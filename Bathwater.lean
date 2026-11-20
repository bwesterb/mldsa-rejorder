import Mathlib

/-!
# Which nonce-reuse optimisations from "Don't throw your nonces out with the bathwater" are exact?

Sprenkels–Westerbaan (ePrint 2020/1158) and Sprenkels' thesis (ch. 8) propose to keep part of the
nonce `y = (y₁, …, y_ℓ)` of ML-DSA/Dilithium across rejected signing attempts. We study these
proposals in the `Trans` hybrid of the security proof (thesis §8.4): every attempt gets a fresh
uniform challenge `c`, independent of everything else, and the adversary sees only the accepted
`(y, c)` (equivalently the signature `(c, z = y + c·s₁)`).

* `Loop`: the semantics of a rejection loop as a sub-stochastic chain. `Loop.tendsto_outUpTo`
  computes the output law of the whole loop from a fixed point `ν = π + ν·B`.
* `ReusePolicy`: on reject, keep the coordinates in a set `K` of `y` and resample the others.
  `exact_of_invariant`: if each reject event depends only on the coordinates that are resampled,
  then in *every* attempt the state is uniform, so the joint law of (number of attempts, output) is
  that of vanilla Dilithium (`outAt_eq_vanilla`).
* `altZ_exact`: the thesis's `alt-z` (Algorithm 8.2: z-check first, polynomial by polynomial; on a
  failure at `i` resample `y₁…y_i`; on an r₀ failure resample everything) is exact.
* `altR0Set_law`: the output law of `alt-r0` with a set `H` of resampled coordinates is
  `(y, c) ↦ κ / (N·|C|·ρ y)` on passing `(y, c)`, where `ρ y` is the r₀ pass probability with the
  `H` part of `y` fresh (nonces with `ρ = 0` are stuck forever: `Loop.tendsto_of_fixed_off`).
  `altR0Set_close`: if `ρ` has relative mean deviation `D` from `μ₀`, this is within statistical
  distance `μ₀D / (P - μ₀D)` of vanilla's uniform law on passing `(y, c)` (`vanilla_law`).
* `Toy`: a Dilithium-shaped instance (`q = 17`, `n = 1`, `ℓ = 2`) with two secret keys that have
  the same public key. For each of
  - `alt-r0` (the ePrint's main proposal, thesis Alg. 8.3: r₀-check first, on failure resample
    only `y₁`),
  - `r0-first, prefix-z` (ePrint Appendix A's partial resampling, but with the r₀-check first as in
    ePrint Algorithm 3),
  - `z-first, then y₁ only on r₀ failure`,
  the probability of some signature differs between the two keys (`toy_altR0_leaks`, …), so no
  simulator that sees only the public key can be perfect. Vanilla gives the same law for both keys
  (`toy_vanilla_same`).
-/

namespace Bathwater
open Finset Filter Topology

/-! ## Loop semantics -/

/-- A rejection loop. In state `s` an attempt accepts with output `x` with probability `A s x`, or
rejects and moves to `s'` with probability `B s s'`. The first attempt starts in law `π`. -/
structure Loop (S X : Type*) where
  π : S → ℚ
  B : S → S → ℚ
  A : S → X → ℚ

namespace Loop
variable {S X : Type*} [Fintype S] (L : Loop S X)

/-- One rejected attempt: push a (sub-)law on states through `B`. -/
def step (μ : S → ℚ) : S → ℚ := fun s' => ∑ s, μ s * L.B s s'

/-- The sub-law of the state at the start of attempt `k` (attempts `0, …, k-1` all rejected). -/
def state (k : ℕ) : S → ℚ := L.step^[k] L.π

/-- Probability that attempt `k` is the accepting one and outputs `x`. -/
def outAt (k : ℕ) (x : X) : ℚ := ∑ s, L.state k s * L.A s x

/-- Probability that the loop accepts within the first `K` attempts and outputs `x`. -/
def outUpTo (K : ℕ) (x : X) : ℚ := ∑ k ∈ range K, L.outAt k x

/-- Probability of `m` consecutive rejections starting from `s`. -/
def survive : ℕ → S → ℚ
  | 0, _ => 1
  | m + 1, s => ∑ s', L.B s s' * survive m s'

lemma step_add (μ μ' : S → ℚ) : L.step (μ + μ') = L.step μ + L.step μ' := by
  funext s'; simp [step, add_mul, sum_add_distrib]

lemma iter_add (k : ℕ) (μ μ' : S → ℚ) :
    L.step^[k] (μ + μ') = L.step^[k] μ + L.step^[k] μ' := by
  induction k generalizing μ μ' with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, step_add, ih]

lemma survive_nonneg (hB : ∀ s s', 0 ≤ L.B s s') : ∀ m s, 0 ≤ L.survive m s
  | 0, _ => zero_le_one
  | m + 1, s => sum_nonneg fun s' _ => mul_nonneg (hB s s') (survive_nonneg hB m s')

lemma norm_iter_le (hB : ∀ s s', 0 ≤ L.B s s') :
    ∀ m (μ : S → ℚ), ∑ s, |L.step^[m] μ s| ≤ ∑ s, |μ s| * L.survive m s
  | 0, μ => by simp [survive]
  | m + 1, μ => by
    rw [Function.iterate_succ_apply]
    refine (norm_iter_le hB m _).trans ?_
    calc ∑ s, |L.step μ s| * L.survive m s
        ≤ ∑ s, (∑ s₀, |μ s₀| * L.B s₀ s) * L.survive m s := by
          refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_right ?_ (L.survive_nonneg hB m s)
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          simp [abs_mul, abs_of_nonneg (hB _ _)]
      _ = ∑ s₀, |μ s₀| * L.survive (m + 1) s₀ := by
          simp only [survive, sum_mul, mul_sum]
          rw [sum_comm]; simp [mul_assoc]

/-- The fixed point equation gives `ν = (attempts 0..K-1) + (what is still running after K)`. -/
lemma fixed_split (ν : S → ℚ) (hν : ∀ s', ν s' = L.π s' + L.step ν s') :
    ∀ K, ν = (fun s => ∑ k ∈ range K, L.state k s) + L.step^[K] ν
  | 0 => by funext s; simp
  | K + 1 => by
    have hν' : ν = L.π + L.step ν := funext hν
    have := fixed_split ν hν K
    conv_lhs => rw [this]
    conv_lhs => rw [hν']
    rw [iter_add]
    funext s
    simp only [Pi.add_apply, sum_range_succ, state]
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    ring

/-- **Loop semantics.** If `ν` solves `ν = π + ν·B`, every row of `B` is sub-stochastic and `m`
consecutive rejections have probability at most `1 - ε`, then the probability that the loop
outputs `x` (within `K` attempts, `K → ∞`) tends to `∑ₛ ν s · A s x`. -/
theorem tendsto_outUpTo (ν : S → ℚ) (hB : ∀ s s', 0 ≤ L.B s s')
    (hA0 : ∀ s x, 0 ≤ L.A s x) (hA1 : ∀ s x, L.A s x ≤ 1)
    (hrow : ∀ s, L.survive 1 s ≤ 1) (m : ℕ) (hm0 : 0 < m) (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : ∀ s, L.survive m s ≤ 1 - ε) (hν : ∀ s', ν s' = L.π s' + L.step ν s') (x : X) :
    Tendsto (fun K => L.outUpTo K x) atTop (𝓝 (∑ s, ν s * L.A s x)) := by
  set N : (S → ℚ) → ℚ := fun μ => ∑ s, |μ s|
  -- one step does not increase the mass, `m` steps shrink it by `1 - ε`
  have h1 : ∀ μ, N (L.step μ) ≤ N μ := fun μ => by
    have := L.norm_iter_le hB 1 μ
    simp only [Function.iterate_one] at this
    refine this.trans (sum_le_sum fun s _ => ?_)
    simpa using mul_le_mul_of_nonneg_left (hrow s) (abs_nonneg (μ s))
  have hmm : ∀ μ, N (L.step^[m] μ) ≤ (1 - ε) * N μ := fun μ => by
    refine (L.norm_iter_le hB m μ).trans ?_
    simp only [N, mul_sum]
    refine sum_le_sum fun s _ => ?_
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hm s) (abs_nonneg _)
  have hr : ∀ r μ, N (L.step^[r] μ) ≤ N μ := fun r => by
    induction r with
    | zero => intro μ; rfl
    | succ r ih => intro μ; rw [Function.iterate_succ_apply]; exact (ih _).trans (h1 μ)
  have hj : ∀ j μ, N (L.step^[m * j] μ) ≤ (1 - ε) ^ j * N μ := fun j => by
    induction j with
    | zero => intro μ; simp
    | succ j ih =>
      intro μ
      rw [Nat.mul_succ, Function.iterate_add_apply]
      refine (ih _).trans ?_
      rw [pow_succ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hmm μ) (pow_nonneg (by linarith) _)
  have hK : ∀ K, N (L.step^[K] ν) ≤ (1 - ε) ^ (K / m) * N ν := fun K => by
    conv_lhs => rw [← Nat.div_add_mod K m, Nat.add_comm, Function.iterate_add_apply]
    exact (hr _ _).trans (hj _ _)
  -- the error after `K` attempts is the output of the still-running mass
  have herr : ∀ K, |L.outUpTo K x - ∑ s, ν s * L.A s x| ≤ (1 - ε) ^ (K / m) * N ν := fun K => by
    have hs := congrFun (L.fixed_split ν hν K)
    have : L.outUpTo K x - ∑ s, ν s * L.A s x = -∑ s, L.step^[K] ν s * L.A s x := by
      simp only [outUpTo, outAt]
      rw [sum_comm]
      simp only [← sum_mul]
      rw [← sum_sub_distrib, ← sum_neg_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [hs s]; simp only [Pi.add_apply]; ring
    rw [this, abs_neg]
    refine ((abs_sum_le_sum_abs _ _).trans ?_).trans (hK K)
    refine sum_le_sum fun s _ => ?_
    rw [abs_mul]
    calc |L.step^[K] ν s| * |L.A s x| ≤ |L.step^[K] ν s| * 1 :=
          mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg (hA0 s x)]; exact hA1 s x)
            (abs_nonneg _)
      _ = |L.step^[K] ν s| := mul_one _
  have hlim : Tendsto (fun K => (1 - ε) ^ (K / m) * N ν) atTop (𝓝 0) := by
    have hp : Tendsto (fun j : ℕ => (1 - ε) ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    have hd : Tendsto (fun K : ℕ => K / m) atTop atTop :=
      Nat.tendsto_div_const_atTop hm0.ne'
    simpa using (hp.comp hd).mul_const (N ν)
  set a := ∑ s, ν s * L.A s x
  have hlo : Tendsto (fun K => a - (1 - ε) ^ (K / m) * N ν) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).sub hlim
  have hhi : Tendsto (fun K => a + (1 - ε) ^ (K / m) * N ν) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).add hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun K => ?_) (fun K => ?_)
  · have := (abs_sub_le_iff.mp (herr K)).2; simp only; linarith
  · have := (abs_sub_le_iff.mp (herr K)).1; simp only; linarith

/-- **Loop semantics without a decay rate.** Rows are exact (every attempt either rejects or
accepts), `π` is a probability, and `ν ≥ 0` solves `ν = π + ν·B`. Then the probability of
outputting `x` within `K` attempts is at most `∑ₛ ν s · A s x`, and short of it by at most
`(∑ ν) / K` in total over all `x`. -/
theorem out_close [Fintype X] (ν : S → ℚ) (hB : ∀ s s', 0 ≤ L.B s s')
    (hA0 : ∀ s x, 0 ≤ L.A s x) (hrow : ∀ s, ∑ s', L.B s s' + ∑ x, L.A s x = 1)
    (hπ0 : ∀ s, 0 ≤ L.π s) (hπ : ∑ s, L.π s = 1) (hν0 : ∀ s, 0 ≤ ν s)
    (hν : ∀ s', ν s' = L.π s' + L.step ν s') (K : ℕ) (hK : 0 < K) :
    (∀ x, L.outUpTo K x ≤ ∑ s, ν s * L.A s x) ∧
    ∑ x, (∑ s, ν s * L.A s x - L.outUpTo K x) ≤ (∑ s, ν s) / K := by
  have step_nonneg : ∀ μ : S → ℚ, (∀ s, 0 ≤ μ s) → ∀ s', 0 ≤ L.step μ s' :=
    fun μ hμ s' => sum_nonneg fun s _ => mul_nonneg (hμ s) (hB s s')
  have iter_nonneg : ∀ k (μ : S → ℚ), (∀ s, 0 ≤ μ s) → ∀ s, 0 ≤ L.step^[k] μ s := by
    intro k; induction k with
    | zero => intro μ h; exact h
    | succ k ih => intro μ h; rw [Function.iterate_succ_apply']; exact step_nonneg _ (ih μ h)
  have hstate0 : ∀ k s, 0 ≤ L.state k s := fun k => iter_nonneg k _ hπ0
  set a : S → ℚ := fun s => ∑ x, L.A s x
  -- mass bookkeeping
  have hmass : ∀ μ : S → ℚ, ∑ s', L.step μ s' = ∑ s, μ s - ∑ s, μ s * a s := by
    intro μ
    simp only [step]
    rw [sum_comm, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← mul_sum]
    have hb : ∑ i, L.B s i = 1 - a s := by have := hrow s; simp only [a]; linarith
    rw [hb]; ring
  set m : ℕ → ℚ := fun k => ∑ s, L.state k s
  have hm_succ : ∀ k, m (k + 1) = m k - ∑ s, L.state k s * a s := by
    intro k; simp only [m, state, Function.iterate_succ_apply']; exact hmass _
  have hout_tot : ∀ k, ∑ x, L.outAt k x = ∑ s, L.state k s * a s := by
    intro k; simp only [outAt, a, mul_sum]; rw [sum_comm]
  have ha0 : ∀ s, 0 ≤ a s := fun s => sum_nonneg fun x _ => hA0 s x
  have hm_anti : ∀ k, m (k + 1) ≤ m k := fun k => by
    rw [hm_succ]; linarith [sum_nonneg fun s (_ : s ∈ univ) => mul_nonneg (hstate0 k s) (ha0 s)]
  have hm_le : ∀ k j, k ≤ j → m j ≤ m k := by
    intro k j hkj; induction hkj with
    | refl => exact le_rfl
    | step _ ih => exact (hm_anti _).trans ih
  -- the part still running
  have hsplit := L.fixed_split ν hν K
  have hrest : ∀ s, ν s - ∑ k ∈ range K, L.state k s = L.step^[K] ν s := by
    intro s; have := congrFun hsplit s; simp only [Pi.add_apply] at this; linarith
  have hgap : ∀ x, ∑ s, ν s * L.A s x - L.outUpTo K x = ∑ s, L.step^[K] ν s * L.A s x := by
    intro x
    simp only [outUpTo, outAt]
    rw [sum_comm, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← sum_mul, ← sub_mul, hrest]
  refine ⟨fun x => ?_, ?_⟩
  · have := hgap x
    have : 0 ≤ ∑ s, L.step^[K] ν s * L.A s x :=
      sum_nonneg fun s _ => mul_nonneg (iter_nonneg K ν hν0 s) (hA0 s x)
    linarith [hgap x]
  · -- total gap = mass still running = m K
    have hνa : ∑ s, ν s * a s = 1 := by
      have h := congrArg (fun f : S → ℚ => ∑ s, f s) (funext hν)
      simp only [sum_add_distrib, hπ] at h
      rw [hmass] at h; linarith
    have htot : ∑ x, (∑ s, ν s * L.A s x - L.outUpTo K x) = m K := by
      have h1 : ∀ K, ∑ x, L.outUpTo K x = 1 - m K := by
        intro K; induction K with
        | zero => simp [outUpTo, m, state, hπ]
        | succ K ih =>
          simp only [outUpTo, sum_range_succ, sum_add_distrib] at ih ⊢
          rw [ih, hout_tot, hm_succ]; ring
      rw [sum_sub_distrib, h1, sum_comm]
      simp only [← mul_sum]
      rw [show ∑ s, ν s * ∑ i, L.A s i = ∑ s, ν s * a s from rfl, hνa]; ring
    rw [htot]
    -- K · m K ≤ ∑_{k<K} m k = mass of V_K ≤ mass of ν
    have hV : ∑ k ∈ range K, m k ≤ ∑ s, ν s := by
      simp only [m]; rw [sum_comm]
      refine sum_le_sum fun s _ => ?_
      linarith [hrest s, iter_nonneg K ν hν0 s]
    have hKm : (K : ℚ) * m K ≤ ∑ k ∈ range K, m k := by
      have : ∑ _k ∈ range K, m K = (K : ℚ) * m K := by simp
      rw [← this]
      exact sum_le_sum fun k hk => hm_le k K (mem_range.mp hk).le
    rw [le_div_iff₀ (by exact_mod_cast hK)]
    linarith

/-- Hence the output law of the loop is `x ↦ ∑ₛ ν s · A s x`. -/
theorem tendsto_of_fixed [Fintype X] (ν : S → ℚ) (hB : ∀ s s', 0 ≤ L.B s s')
    (hA0 : ∀ s x, 0 ≤ L.A s x) (hrow : ∀ s, ∑ s', L.B s s' + ∑ x, L.A s x = 1)
    (hπ0 : ∀ s, 0 ≤ L.π s) (hπ : ∑ s, L.π s = 1) (hν0 : ∀ s, 0 ≤ ν s)
    (hν : ∀ s', ν s' = L.π s' + L.step ν s') (x : X) :
    Tendsto (fun K => L.outUpTo K x) atTop (𝓝 (∑ s, ν s * L.A s x)) := by
  set v := ∑ s, ν s * L.A s x
  have hb : ∀ K, 0 < K → v - (∑ s, ν s) / K ≤ L.outUpTo K x ∧ L.outUpTo K x ≤ v := by
    intro K hK
    obtain ⟨h1, h2⟩ := L.out_close ν hB hA0 hrow hπ0 hπ hν0 hν K hK
    refine ⟨?_, h1 x⟩
    have : v - L.outUpTo K x ≤ ∑ y, (∑ s, ν s * L.A s y - L.outUpTo K y) :=
      single_le_sum (f := fun y => ∑ s, ν s * L.A s y - L.outUpTo K y)
        (fun y _ => sub_nonneg.mpr (h1 y)) (mem_univ x)
    linarith
  have hlo : Tendsto (fun K : ℕ => v - (∑ s, ν s) / K) atTop (𝓝 v) := by
    simpa using (tendsto_const_nhds (x := v)).sub
      ((tendsto_const_div_atTop_nhds_zero_nat (∑ s, ν s)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with K hK using (hb K hK).1
  · filter_upwards [eventually_gt_atTop 0] with K hK using (hb K hK).2


end Loop

/-! ## Partial reuse of the nonce -/

section Reuse
variable {ι V C : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype C] [Nonempty C]

/-- A reuse policy: after drawing `y` and the challenge `c`, either accept (`none`), or reject and
keep the coordinates in `K` of `y` for the next attempt (`some K`); the others are resampled. -/
abbrev ReusePolicy (ι V C : Type*) := (ι → V) → C → Option (Finset ι)

/-- Probability that a reject keeping `K` of `y` leads to `y'`. -/
def keepProb (K : Finset ι) (y y' : ι → V) : ℚ :=
  if ∀ j ∈ K, y' j = y j then 1 / (Fintype.card V : ℚ) ^ (Kᶜ).card else 0

/-- The signing loop of a reuse policy, with state the full nonce at the start of an attempt and
output the accepted `(y, c)`. The challenge is fresh and uniform in every attempt (`Trans`). -/
def ReusePolicy.loop (P : ReusePolicy ι V C) : Loop (ι → V) ((ι → V) × C) where
  π := fun _ => 1 / (Fintype.card (ι → V) : ℚ)
  B := fun y y' => ∑ c, (1 / (Fintype.card C : ℚ)) *
    match P y c with
    | none => 0
    | some K => keepProb K y y'
  A := fun y x => if x.1 = y ∧ P y x.2 = none then 1 / (Fintype.card C : ℚ) else 0

/-- A reject event of `P` depends only on the coordinates that are resampled. -/
def ReusePolicy.Invariant (P : ReusePolicy ι V C) : Prop :=
  ∀ y y' c K, P y c = some K → (∀ j, j ∉ K → y' j = y j) → P y' c = some K

/-- Summing a function that ignores the coordinates in `K` over the nonces that agree with `a`
on `K` gives a `1/|V|^|K|` share of the full sum. -/
lemma sum_agree (K : Finset ι) (g : (ι → V) → ℚ)
    (hg : ∀ y y', (∀ j, j ∉ K → y' j = y j) → g y' = g y) (a : ι → V) :
    ∑ y, (if ∀ j ∈ K, a j = y j then g y else 0) =
      (∑ y, g y) / (Fintype.card V : ℚ) ^ K.card := by
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ K) (fun _ => V)
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  -- `g` only sees the `Kᶜ` part
  set h : ({j // j ∉ K} → V) → ℚ := fun w => g (e.symm (fun j => a j, w))
  have hgu : ∀ u w, g (e.symm (u, w)) = h w := fun u w => by
    apply hg; intro j hj; simp [e, hj]
  have hL : ∑ y, (if ∀ j ∈ K, a j = y j then g y else 0) = ∑ w, h w := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    refine (Fintype.sum_eq_single (fun j : {j // j ∈ K} => a j) ?_).trans ?_
    · intro u hu
      refine sum_eq_zero fun w _ => ?_
      rw [if_neg]
      intro hall; apply hu; funext ⟨j, hj⟩
      have := hall j hj; simp [e, hj] at this; exact this.symm
    · refine sum_congr rfl fun w _ => ?_
      rw [if_pos, hgu]
      intro j hj; simp [e, hj]
  have hR : ∑ y, g y = (Fintype.card V : ℚ) ^ K.card * ∑ w, h w := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [hgu, sum_const, card_univ, Fintype.card_fun, Fintype.card_coe, nsmul_eq_mul]
    push_cast; ring
  rw [hL, hR]; field_simp

/-- Acceptance probability of one fresh attempt. -/
noncomputable def ReusePolicy.pAcc (P : ReusePolicy ι V C) : ℚ :=
  (((univ : Finset ((ι → V) × C)).filter fun x => P x.1 x.2 = none).card : ℚ) /
    ((Fintype.card (ι → V) : ℚ) * Fintype.card C)

/-- **Exactness of invariant policies.** If every reject event depends only on the resampled
coordinates, then at the start of every attempt the nonce is uniform: attempt `k` is reached with
probability `(1 - p)^k` and then `y` is uniform. -/
theorem exact_of_invariant (P : ReusePolicy ι V C) (hP : P.Invariant) (k : ℕ) :
    P.loop.state k = fun _ => (1 - P.pAcc) ^ k / (Fintype.card (ι → V) : ℚ) := by
  classical
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hY : (Fintype.card (ι → V) : ℚ) = (Fintype.card V : ℚ) ^ Fintype.card ι := by
    simp [Fintype.card_fun]
  -- the column sums of `B` are all `1 - p`
  have hcol : ∀ y', ∑ y, P.loop.B y y' = 1 - P.pAcc := by
    intro y'
    have hmatch : ∀ y c, (match P y c with | none => (0 : ℚ) | some K => keepProb K y y') =
        ∑ K : Finset ι, if P y c = some K then keepProb K y y' else 0 := by
      intro y c
      rcases h : P y c with _ | K
      · simp
      · rw [Finset.sum_eq_single K]
        · simp
        · intro K' _ hK'; simp [Ne.symm hK']
        · simp
    have hone : ∀ c (K : Finset ι), ∑ y, (if P y c = some K then keepProb K y y' else 0) =
        (((univ : Finset (ι → V)).filter fun y => P y c = some K).card : ℚ) /
          (Fintype.card (ι → V) : ℚ) := by
      intro c K
      have := sum_agree K (fun y => if P y c = some K then (1 : ℚ) else 0)
        (fun y y' hyy' => by
          by_cases h : P y c = some K
          · simp [h, hP y y' c K h hyy']
          · have : ¬ P y' c = some K := fun h' =>
              h (hP y' y c K h' fun j hj => (hyy' j hj).symm)
            simp [h, this]) y'
      have hcK : (Fintype.card V : ℚ) ^ K.card * (Fintype.card V : ℚ) ^ (Kᶜ).card =
          Fintype.card (ι → V) := by
        rw [hY, ← pow_add, card_add_card_compl]
      calc ∑ y, (if P y c = some K then keepProb K y y' else 0)
          = (∑ y, if ∀ j ∈ K, y' j = y j then (if P y c = some K then (1 : ℚ) else 0) else 0) /
              (Fintype.card V : ℚ) ^ (Kᶜ).card := by
            rw [sum_div]; refine sum_congr rfl fun y _ => ?_
            unfold keepProb
            split_ifs <;> simp
        _ = _ := by
            rw [this, sum_boole, div_div, hcK]
    have hsplit : ∀ c, ∑ K : Finset ι,
        (((univ : Finset (ι → V)).filter fun y => P y c = some K).card : ℚ) =
        (((univ : Finset (ι → V)).filter fun y => P y c ≠ none).card : ℚ) := by
      intro c
      rw [← Nat.cast_sum]; congr 1
      rw [← card_biUnion]
      · congr 1; ext y
        simp only [mem_biUnion, mem_univ, mem_filter, true_and, ne_eq]
        constructor
        · rintro ⟨K, hK⟩; simp [hK]
        · intro h; obtain ⟨K, hK⟩ := Option.ne_none_iff_exists'.mp h; exact ⟨K, hK⟩
      · intro K _ K' _ hKK'
        simp only [Function.onFun]
        rw [disjoint_filter]; intro y _ h1 h2; exact hKK' (Option.some_inj.mp (h1.symm.trans h2))
    have hcard : ∀ c, (((univ : Finset (ι → V)).filter fun y => P y c ≠ none).card : ℚ) =
        Fintype.card (ι → V) - ((univ.filter fun y => P y c = none).card : ℚ) := by
      intro c
      rw [eq_sub_iff_add_eq, ← Nat.cast_add, add_comm]
      congr 1
      exact (card_filter_add_card_filter_not (s := univ) (fun y => P y c = none)).trans card_univ
    have hprod : (((univ : Finset ((ι → V) × C)).filter fun x => P x.1 x.2 = none).card : ℚ) =
        ∑ c, ((univ.filter fun y => P y c = none).card : ℚ) := by
      rw [← Nat.cast_sum]; congr 1
      rw [card_filter, Fintype.sum_prod_type, sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [card_filter]
    have hY0 : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
    calc ∑ y, P.loop.B y y'
        = ∑ c, (1 / (Fintype.card C : ℚ)) * ∑ K : Finset ι, ∑ y,
            (if P y c = some K then keepProb K y y' else 0) := by
          simp only [ReusePolicy.loop]
          rw [sum_comm]
          refine sum_congr rfl fun c _ => ?_
          rw [← mul_sum]; congr 1
          simp only [hmatch]; rw [sum_comm]
      _ = ∑ c, (1 / (Fintype.card C : ℚ)) *
            ((((univ : Finset (ι → V)).filter fun y => P y c ≠ none).card : ℚ) /
              (Fintype.card (ι → V) : ℚ)) := by
          refine sum_congr rfl fun c _ => ?_
          simp only [hone, ← sum_div, hsplit]
      _ = 1 - P.pAcc := by
          unfold ReusePolicy.pAcc
          rw [hprod]
          simp only [hcard, sub_div, mul_sub, sum_sub_distrib, sum_const, card_univ,
            nsmul_eq_mul, ← mul_sum, ← sum_div]
          field_simp
  induction k with
  | zero => funext y; simp [Loop.state, ReusePolicy.loop]
  | succ k ih =>
    funext y'
    simp only [Loop.state, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    simp only [Loop.step, ← mul_sum, ← div_mul_eq_mul_div] at *
    rw [hcol]
    ring

/-- The plain loop: accept iff `pass`, otherwise resample everything. -/
def vanilla (pass : (ι → V) → C → Bool) : ReusePolicy ι V C :=
  fun y c => if pass y c then none else some ∅

lemma vanilla_invariant (pass : (ι → V) → C → Bool) : (vanilla pass).Invariant := by
  intro y y' c K h hyy'
  have hy : y' = y := funext fun j => hyy' j (by
    unfold vanilla at h; split_ifs at h; cases h; simp)
  rw [hy]; exact h

/-- Two invariant policies that accept on the same `(y, c)` have the same joint law of the
accepting attempt and the output. -/
theorem outAt_eq_of_invariant (P Q : ReusePolicy ι V C) (hP : P.Invariant) (hQ : Q.Invariant)
    (hPQ : ∀ y c, P y c = none ↔ Q y c = none) (k : ℕ) (x : (ι → V) × C) :
    P.loop.outAt k x = Q.loop.outAt k x := by
  have hp : P.pAcc = Q.pAcc := by
    unfold ReusePolicy.pAcc; congr 3; ext x; simp [hPQ]
  unfold Loop.outAt
  rw [exact_of_invariant P hP, exact_of_invariant Q hQ, hp]
  refine sum_congr rfl fun y _ => ?_
  simp only [ReusePolicy.loop, hPQ]

end Reuse

section LoopFacts
variable {ι V C : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] [Fintype C]

lemma ReusePolicy.B_nonneg (P : ReusePolicy ι V C) (y y' : ι → V) : 0 ≤ P.loop.B y y' := by
  refine sum_nonneg fun c _ => mul_nonneg (by positivity) ?_
  rcases P y c with _ | K
  · exact le_rfl
  · show 0 ≤ keepProb K y y'
    unfold keepProb; split_ifs <;> positivity

lemma ReusePolicy.A_nonneg (P : ReusePolicy ι V C) (y : ι → V) (x : (ι → V) × C) :
    0 ≤ P.loop.A y x := by
  simp only [ReusePolicy.loop]; split_ifs <;> positivity

lemma ReusePolicy.A_le_one [Nonempty C] (P : ReusePolicy ι V C) (y : ι → V) (x : (ι → V) × C) :
    P.loop.A y x ≤ 1 := by
  simp only [ReusePolicy.loop]
  split_ifs
  · have : (1 : ℚ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos
    exact div_le_one_of_le₀ this (by positivity)
  · exact zero_le_one

end LoopFacts

/-! ## The policies of the paper and the thesis

`zc i v c`: the z-check of polynomial `i`, which depends only on `yᵢ = v` and `c`
(`‖yᵢ + (c·s₁)ᵢ‖∞ < γ₁ - β`). `r0 y c`: the r₀-check `‖LowBits(A·y - c·s₂)‖∞ < γ₂ - β`, which
depends on all of `y`. -/

section Policies
variable {ι V C : Type*} [Fintype ι] [LinearOrder ι] [Fintype V] [DecidableEq V]

/-- All z-checks and the r₀-check pass. -/
def pass (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) (y : ι → V) (c : C) : Bool :=
  r0 y c && decide (∀ i, zc i (y i) c = true)

/-- The first polynomial of `z` that fails its check, if any. -/
def firstFail (zc : ι → V → C → Bool) (y : ι → V) (c : C) : Option ι :=
  ((univ : Finset ι).filter fun i => zc i (y i) c = false).min

/-- `alt-z` (thesis Algorithm 8.2): z-check first; if polynomial `i` is the first to fail, keep
`y_j` for `j > i`; if the z-check passes and the r₀-check fails, resample everything. -/
def altZ (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) : ReusePolicy ι V C := fun y c =>
  match firstFail zc y c with
  | some i => some (univ.filter fun j => i < j)
  | none => if r0 y c then none else some ∅

/-- `alt-r0` (ePrint Algorithm 2, thesis Algorithm 8.3): r₀-check first; on failure keep all of
`y` except `y_h`; on a z failure resample everything. -/
def altR0 (h : ι) (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) : ReusePolicy ι V C :=
  fun y c =>
  if r0 y c then (if decide (∀ i, zc i (y i) c = true) then none else some ∅)
  else some (univ.erase h)

/-- r₀-check first (full resample on failure), then the z-check with prefix resampling as in
ePrint Appendix A / Algorithm 3. -/
def r0FirstPrefixZ (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) : ReusePolicy ι V C :=
  fun y c =>
  if r0 y c then
    match firstFail zc y c with
    | some i => some (univ.filter fun j => i < j)
    | none => none
  else some ∅

/-- z-check first (full resample on failure), then on an r₀ failure keep all but `y_h`. -/
def zFirstThenY1 (h : ι) (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) :
    ReusePolicy ι V C := fun y c =>
  if decide (∀ i, zc i (y i) c = true) then (if r0 y c then none else some (univ.erase h))
  else some ∅

lemma firstFail_eq_none (zc : ι → V → C → Bool) (y : ι → V) (c : C) :
    firstFail zc y c = none ↔ ∀ i, zc i (y i) c = true := by
  unfold firstFail
  change (_ : WithTop ι) = ⊤ ↔ _
  rw [Finset.min_eq_top, filter_eq_empty_iff]
  simp

lemma firstFail_eq_some {zc : ι → V → C → Bool} {y : ι → V} {c : C} {i : ι} :
    firstFail zc y c = some i ↔ zc i (y i) c = false ∧ ∀ j < i, zc j (y j) c = true := by
  unfold firstFail
  set s := (univ : Finset ι).filter fun i => zc i (y i) c = false
  change s.min = (i : WithTop ι) ↔ _
  constructor
  · intro h
    have hi : i ∈ s := mem_of_min h
    refine ⟨(mem_filter.mp hi).2, fun j hj => ?_⟩
    by_contra hne
    have hjs : j ∈ s := mem_filter.mpr ⟨mem_univ _, by simpa using hne⟩
    have := Finset.min_le hjs
    rw [h] at this
    exact absurd (WithTop.coe_le_coe.mp this) (not_le.mpr hj)
  · rintro ⟨hi, hj⟩
    have his : i ∈ s := mem_filter.mpr ⟨mem_univ _, hi⟩
    refine le_antisymm (Finset.min_le his) (Finset.le_min fun j hjs => ?_)
    refine WithTop.coe_le_coe.mpr (not_lt.mp fun hlt => ?_)
    have := hj j hlt
    simp [s, this] at hjs

/-- The first failing index only depends on the coordinates up to it. -/
lemma firstFail_congr {zc : ι → V → C → Bool} {y y' : ι → V} {c : C} {i : ι}
    (h : firstFail zc y c = some i) (hyy' : ∀ j, j ≤ i → y' j = y j) :
    firstFail zc y' c = some i := by
  rw [firstFail_eq_some] at h ⊢
  refine ⟨by rw [hyy' i le_rfl]; exact h.1, fun j hj => ?_⟩
  rw [hyy' j hj.le]; exact h.2 j hj

theorem altZ_invariant (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) :
    (altZ zc r0).Invariant := by
  intro y y' c K h hyy'
  unfold altZ at h ⊢
  rcases hf : firstFail zc y c with _ | i
  · rw [hf] at h
    have hy : y' = y := by
      split_ifs at h with hr
      cases h
      exact funext fun j => hyy' j (by simp)
    rw [hy, hf]; exact h
  · rw [hf] at h
    cases h
    rw [firstFail_congr hf fun j hj => hyy' j (by simpa using hj)]

theorem altZ_accept (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) (y : ι → V) (c : C) :
    altZ zc r0 y c = none ↔ vanilla (pass zc r0) y c = none := by
  unfold altZ vanilla pass
  rcases hf : firstFail zc y c with _ | i
  · have := (firstFail_eq_none zc y c).mp hf
    simp [this]
  · have h1 := (firstFail_eq_some.mp hf).1
    have : ¬ ∀ i, zc i (y i) c = true := fun h => by simp [h i] at h1
    simp [this]

/-- **`alt-z` is exact.** In the `Trans` hybrid, for every attempt number `k` the probability that
attempt `k` accepts with output `(y, c)` is the same as for vanilla signing. So the output law,
the law of the number of attempts, and their joint law, all equal vanilla's: the vanilla
simulator applies unchanged. -/
theorem altZ_exact [DecidableEq ι] [Nonempty V] [Fintype C] [Nonempty C]
    (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) (k : ℕ) (x : (ι → V) × C) :
    (altZ zc r0).loop.outAt k x = (vanilla (pass zc r0)).loop.outAt k x :=
  outAt_eq_of_invariant _ _ (altZ_invariant zc r0) (vanilla_invariant _)
    (altZ_accept zc r0) k x

end Policies

/-! ## `alt-r0` with a set of resampled coordinates: output law and distance to vanilla

On an r₀ failure the policy resamples the coordinates in `H` and keeps the others. Since the r₀
check depends on the kept coordinates, a nonce whose kept part makes r₀ fail for every choice of
the `H` part and of `c` gets stuck: the loop never leaves it. We compute the output law anyway
(`Loop.tendsto_of_fixed_off`: a fixed point that is only required off a closed set of
non-accepting states), and bound its distance to vanilla in terms of how far the r₀ pass
probability `ρ` (with fresh `H` part) is from a constant `μ₀`. -/

namespace Loop
variable {S X : Type*} [Fintype S] (L : Loop S X)

lemma state_succ (k : ℕ) (s' : S) : L.state (k + 1) s' = ∑ s, L.state k s * L.B s s' := by
  simp only [state, Function.iterate_succ_apply']; rfl

/-- `L` with the states in `T` cut off: moving into `T` becomes an extra output `none`. -/
def cut (T : S → Prop) [DecidablePred T] : Loop S (Option X) where
  π := L.π
  B := fun s s' => if T s' then 0 else L.B s s'
  A := fun s o => match o with
    | none => ∑ s', if T s' then L.B s s' else 0
    | some x => L.A s x

lemma cut_state (T : S → Prop) [DecidablePred T] (hT : ∀ s s', T s → ¬ T s' → L.B s s' = 0) :
    ∀ k s, ¬ T s → (L.cut T).state k s = L.state k s
  | 0, _, _ => rfl
  | k + 1, s', hs' => by
    rw [state_succ, state_succ]
    refine sum_congr rfl fun s _ => ?_
    show (L.cut T).state k s * (if T s' then 0 else L.B s s') = _
    rw [if_neg hs']
    by_cases hs : T s
    · rw [hT s s' hs hs', mul_zero, mul_zero]
    · rw [cut_state T hT k s hs]

/-- **Loop semantics with absorbing states.** Let `T` be a set of states that the loop never
leaves and in which it never accepts. If `ν ≥ 0` solves `ν = π + ν·B` off `T`, the output law of
the loop is still `x ↦ ∑ₛ ν s · A s x`. -/
theorem tendsto_of_fixed_off [Fintype X] (T : S → Prop) [DecidablePred T] (ν : S → ℚ)
    (hB : ∀ s s', 0 ≤ L.B s s') (hA0 : ∀ s x, 0 ≤ L.A s x)
    (hrow : ∀ s, ∑ s', L.B s s' + ∑ x, L.A s x = 1) (hπ0 : ∀ s, 0 ≤ L.π s)
    (hπ : ∑ s, L.π s = 1) (hT : ∀ s s', T s → ¬ T s' → L.B s s' = 0)
    (hTA : ∀ s x, T s → L.A s x = 0) (hν0 : ∀ s, 0 ≤ ν s)
    (hν : ∀ s', ¬ T s' → ν s' = L.π s' + L.step ν s') (x : X) :
    Tendsto (fun K => L.outUpTo K x) atTop (𝓝 (∑ s, ν s * L.A s x)) := by
  set ν' : S → ℚ := fun s => if T s then L.π s else ν s with hν'
  have hfix : ∀ s', ν' s' = (L.cut T).π s' + (L.cut T).step ν' s' := by
    intro s'
    by_cases hs' : T s'
    · have : (L.cut T).step ν' s' = 0 := sum_eq_zero fun s _ => by
        show ν' s * (if T s' then 0 else L.B s s') = 0; rw [if_pos hs', mul_zero]
      rw [this, add_zero]; simp only [hν', if_pos hs']; rfl
    · have : (L.cut T).step ν' s' = L.step ν s' := by
        refine sum_congr rfl fun s _ => ?_
        show ν' s * (if T s' then 0 else L.B s s') = ν s * L.B s s'
        rw [if_neg hs']
        by_cases hs : T s
        · rw [hT s s' hs hs', mul_zero, mul_zero]
        · simp only [hν', if_neg hs]
      rw [this]; simp only [hν', if_neg hs']; exact hν s' hs'
  have hrow' : ∀ s, ∑ s', (L.cut T).B s s' + ∑ o, (L.cut T).A s o = 1 := by
    intro s
    rw [Fintype.sum_option]
    show ∑ s', (if T s' then 0 else L.B s s') +
      ((∑ s', if T s' then L.B s s' else 0) + ∑ x, L.A s x) = 1
    rw [← add_assoc, ← sum_add_distrib, ← hrow s]
    congr 1
    refine sum_congr rfl fun s' _ => ?_
    split_ifs <;> simp
  have hlim := (L.cut T).tendsto_of_fixed ν'
    (fun s s' => by
      show 0 ≤ ite _ _ _
      split_ifs
      exacts [le_rfl, hB s s'])
    (fun s o => by
      cases o with
      | none =>
        exact sum_nonneg fun s' _ => by
          show 0 ≤ ite _ _ _
          split_ifs
          exacts [hB s s', le_rfl]
      | some x => exact hA0 s x)
    hrow' hπ0 hπ
    (fun s => by
      rw [hν']
      dsimp only
      split_ifs
      exacts [hπ0 s, hν0 s])
    hfix (some x)
  have hout : ∀ K, (L.cut T).outUpTo K (some x) = L.outUpTo K x := by
    intro K
    refine sum_congr rfl fun k _ => sum_congr rfl fun s _ => ?_
    show (L.cut T).state k s * L.A s x = L.state k s * L.A s x
    by_cases hs : T s
    · rw [hTA s x hs, mul_zero, mul_zero]
    · rw [L.cut_state T hT k s hs]
  have hval : ∑ s, ν' s * (L.cut T).A s (some x) = ∑ s, ν s * L.A s x := by
    refine sum_congr rfl fun s _ => ?_
    show ν' s * L.A s x = _
    by_cases hs : T s
    · rw [hTA s x hs, mul_zero, mul_zero]
    · simp only [hν', if_neg hs]
  rw [hval] at hlim
  exact hlim.congr hout

end Loop

section AltR0Set
variable {ι V C : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype C] [Nonempty C]

lemma keepProb_sum (K : Finset ι) (y : ι → V) : ∑ y', keepProb K y y' = 1 := by
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have e : ∀ y', keepProb K y y' = (if ∀ j ∈ K, y j = y' j then (1 : ℚ) else 0) /
      (Fintype.card V : ℚ) ^ (Kᶜ).card := by
    intro y'; unfold keepProb
    by_cases h : ∀ j ∈ K, y' j = y j
    · rw [if_pos h, if_pos fun j hj => (h j hj).symm]
    · rw [if_neg h, if_neg fun h' => h fun j hj => (h' j hj).symm, zero_div]
  simp only [e, ← sum_div]
  rw [sum_agree K (fun _ => (1 : ℚ)) (fun _ _ _ => rfl) y]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun]
  push_cast
  rw [div_div, ← pow_add, card_add_card_compl, div_self (by positivity)]

/-- Every attempt of a reuse policy either accepts or rejects. -/
lemma ReusePolicy.row (P : ReusePolicy ι V C) (y : ι → V) :
    ∑ y', P.loop.B y y' + ∑ x, P.loop.A y x = 1 := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have h1 : ∑ y', P.loop.B y y' =
      ∑ c, (1 / (Fintype.card C : ℚ)) * (if P y c = none then 0 else 1) := by
    simp only [ReusePolicy.loop]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [← mul_sum]
    congr 1
    rcases h : P y c with _ | K
    · simp
    · simp [keepProb_sum]
  have h2 : ∑ x, P.loop.A y x = ∑ c, if P y c = none then 1 / (Fintype.card C : ℚ) else 0 := by
    simp only [ReusePolicy.loop]
    rw [Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun c _ => ?_
    simp [ite_and]
  rw [h1, h2, ← sum_add_distrib]
  have : ∀ c, (1 / (Fintype.card C : ℚ)) * (if P y c = none then 0 else 1) +
      (if P y c = none then 1 / (Fintype.card C : ℚ) else 0) = 1 / Fintype.card C := by
    intro c; split_ifs <;> ring
  simp only [this, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- `alt-r0` with a set `H` of resampled coordinates: r₀-check first; on an r₀ failure keep `Hᶜ`
(resample `H`); on a z failure resample everything. (`altR0 h` is the case `H = {h}`.) -/
def altR0Set (H : Finset ι) (r0 zok : (ι → V) → C → Bool) : ReusePolicy ι V C := fun y c =>
  if r0 y c then (if zok y c then none else some ∅) else some Hᶜ

namespace AltR0Set
variable (H : Finset ι) (r0 zok pass : (ι → V) → C → Bool)

/-- `Pr_c[pass y c]`. -/
def sacc (y : ι → V) : ℚ := (∑ c, if pass y c then (1 : ℚ) else 0) / Fintype.card C

/-- Acceptance probability of a fresh vanilla attempt. -/
def pacc : ℚ := (∑ y, sacc pass y) / Fintype.card (ι → V)

/-- r₀ pass probability with the `H` part of the nonce fresh; depends only on `y` off `H`. The
nonce `y` is *stuck* if `rho H r0 y = 0`. -/
def rho (y : ι → V) : ℚ :=
  (∑ y', ∑ c, if (∀ j ∉ H, y' j = y j) ∧ r0 y' c then (1 : ℚ) else 0) /
    ((Fintype.card V : ℚ) ^ H.card * Fintype.card C)

/-- `Pr_c[r₀ passes and z fails]`. -/
def zfail (y : ι → V) : ℚ :=
  (∑ c, if r0 y c ∧ ¬ zok y c then (1 : ℚ) else 0) / Fintype.card C

/-- `F = E_y[f y / ρ y; ρ y ≠ 0]` with `f = zfail`; `1 - F > 0` when vanilla can accept
(`one_sub_F_pos`). -/
def F : ℚ :=
  (∑ y ∈ univ.filter (fun y => rho H r0 y ≠ 0), zfail r0 zok y / rho H r0 y) /
    Fintype.card (ι → V)

/-- `κ = 1 / (1 - F)`: normalisation of the `alt-r0` output law. -/
def kappa : ℚ := 1 / (1 - F H r0 zok)

/-- `D = E_y|ρ y - μ₀| / μ₀`: relative mean deviation of `ρ` from `μ₀`. -/
def dev (μ₀ : ℚ) : ℚ := (∑ y, |rho H r0 y - μ₀|) / (Fintype.card (ι → V) * μ₀)

/-- Output law of vanilla signing: `1 / (N·|C|·P)` on passing `(y, c)`. -/
def vanLaw (x : (ι → V) × C) : ℚ :=
  if pass x.1 x.2 then 1 / (Fintype.card (ι → V) * Fintype.card C * pacc pass) else 0

/-- Output law of `altR0Set`: `κ / (N·|C|·ρ y)` on passing `(y, c)`. -/
def altLaw (x : (ι → V) × C) : ℚ :=
  if (r0 x.1 x.2 && zok x.1 x.2) ∧ rho H r0 x.1 ≠ 0 then
    kappa H r0 zok / (Fintype.card (ι → V) * Fintype.card C * rho H r0 x.1) else 0

variable {H r0 zok pass}

lemma card_class (a : ι → V) :
    ∑ y : ι → V, (if ∀ j ∉ H, y j = a j then (1 : ℚ) else 0) = (Fintype.card V : ℚ) ^ H.card := by
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have h := sum_agree Hᶜ (fun _ => (1 : ℚ)) (fun _ _ _ => rfl) a
  have e : ∀ y : ι → V, (∀ j ∈ Hᶜ, a j = y j) ↔ (∀ j ∉ H, y j = a j) := fun y => by
    simp only [mem_compl]
    exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  calc ∑ y : ι → V, (if ∀ j ∉ H, y j = a j then (1 : ℚ) else 0)
      = ∑ y : ι → V, (if ∀ j ∈ Hᶜ, a j = y j then (1 : ℚ) else 0) :=
        sum_congr rfl fun y _ => if_congr (e y).symm rfl rfl
    _ = _ := by
        rw [h]
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun]
        push_cast
        rw [← card_add_card_compl H, pow_add]
        field_simp

/-- Averaging over classes: a class function `φ` against a function `g` or against its class
average give the same sum. -/
lemma sum_class (g φ : (ι → V) → ℚ) (hφ : ∀ y y', (∀ j ∉ H, y' j = y j) → φ y' = φ y) :
    ∑ y, φ y * (∑ y', if ∀ j ∉ H, y' j = y j then g y' else 0) =
      (Fintype.card V : ℚ) ^ H.card * ∑ y, φ y * g y := by
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y' _ => ?_
  rw [← card_class (H := H) y', sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : ∀ j ∉ H, y' j = y j
  · rw [if_pos h, if_pos fun j hj => (h j hj).symm, hφ y y' h]; ring
  · rw [if_neg h, if_neg fun h' => h fun j hj => (h' j hj).symm]; ring

lemma rho_eq (y : ι → V) : rho H r0 y =
    (∑ y', if ∀ j ∉ H, y' j = y j then sacc r0 y' else 0) / (Fintype.card V : ℚ) ^ H.card := by
  have e : ∀ y', (∑ c, if (∀ j ∉ H, y' j = y j) ∧ r0 y' c then (1 : ℚ) else 0) =
      (if ∀ j ∉ H, y' j = y j then ∑ c, (if r0 y' c then (1 : ℚ) else 0) else 0) := by
    intro y'; split_ifs with h
    · exact sum_congr rfl fun c _ => if_congr (and_iff_right h) rfl rfl
    · exact sum_eq_zero fun c _ => if_neg fun h' => h h'.1
  have e2 : ∀ y', (if ∀ j ∉ H, y' j = y j then sacc r0 y' else 0) =
      (if ∀ j ∉ H, y' j = y j then ∑ c, (if r0 y' c then (1 : ℚ) else 0) else 0) /
        Fintype.card C := by
    intro y'; unfold sacc; split_ifs <;> simp
  unfold rho
  simp only [e, e2]
  rw [← sum_div, div_div, mul_comm (Fintype.card C : ℚ)]

lemma rho_congr {y y' : ι → V} (h : ∀ j ∉ H, y' j = y j) : rho H r0 y' = rho H r0 y := by
  unfold rho
  congr 1
  refine sum_congr rfl fun z _ => sum_congr rfl fun c _ => if_congr (and_congr ?_ Iff.rfl) rfl rfl
  exact ⟨fun hz j hj => (hz j hj).trans (h j hj), fun hz j hj => (hz j hj).trans (h j hj).symm⟩

lemma sacc_nonneg (y : ι → V) : 0 ≤ sacc pass y :=
  div_nonneg (sum_nonneg fun c _ => by split_ifs <;> norm_num) (by positivity)

lemma rho_nonneg (y : ι → V) : 0 ≤ rho H r0 y :=
  div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun c _ => by split_ifs <;> norm_num)
    (by positivity)

lemma zfail_nonneg (y : ι → V) : 0 ≤ zfail r0 zok y :=
  div_nonneg (sum_nonneg fun c _ => by split_ifs <;> norm_num) (by positivity)

lemma zfail_add (y : ι → V) :
    zfail r0 zok y + sacc (fun y c => r0 y c && zok y c) y = sacc r0 y := by
  unfold zfail sacc
  rw [← add_div, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun c _ => ?_
  rcases hr : r0 y c <;> rcases hz : zok y c <;> simp [hr, hz]

lemma sacc_le (y : ι → V) : sacc (fun y c => r0 y c && zok y c) y ≤ sacc r0 y := by
  have := zfail_add (r0 := r0) (zok := zok) y
  have := zfail_nonneg (r0 := r0) (zok := zok) y
  linarith

lemma sacc_of_rho {y : ι → V} (h : rho H r0 y = 0) : sacc r0 y = 0 := by
  rw [rho_eq] at h
  have hV : (0 : ℚ) < (Fintype.card V : ℚ) ^ H.card :=
    pow_pos (by exact_mod_cast Fintype.card_pos) _
  have hs : ∑ y', (if ∀ j ∉ H, y' j = y j then sacc r0 y' else 0) = 0 := by
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hV.ne'
  have := (sum_eq_zero_iff_of_nonneg (fun y' _ => by
    split_ifs
    exacts [sacc_nonneg _, le_rfl])).mp hs y (mem_univ _)
  rwa [if_pos fun j _ => rfl] at this

lemma r0_of_rho {y : ι → V} (h : rho H r0 y = 0) (c : C) : r0 y c = false := by
  have h1 := sacc_of_rho h
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  unfold sacc at h1
  have h2 : ∑ c, (if r0 y c then (1 : ℚ) else 0) = 0 := by
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact h
    · exact absurd h hC.ne'
  have := (sum_eq_zero_iff_of_nonneg (fun c _ => by split_ifs <;> norm_num)).mp h2 c (mem_univ _)
  by_contra hc
  rw [Bool.not_eq_false] at hc
  simp [hc] at this

lemma pass_of_rho {y : ι → V} (h : rho H r0 y = 0) :
    sacc (fun y c => r0 y c && zok y c) y = 0 :=
  le_antisymm ((sacc_le y).trans (sacc_of_rho h).le) (sacc_nonneg y)

lemma zfail_of_rho {y : ι → V} (h : rho H r0 y = 0) : zfail r0 zok y = 0 := by
  have := zfail_add (r0 := r0) (zok := zok) y
  have := sacc_nonneg (pass := fun y c => r0 y c && zok y c) y
  have := zfail_nonneg (r0 := r0) (zok := zok) y; have := sacc_of_rho h; linarith

/-- Within a class, the average of `Pr_c[r₀]` is `ρ`. -/
lemma avg (φ : (ι → V) → ℚ) (hφ : ∀ y y', (∀ j ∉ H, y' j = y j) → φ y' = φ y) :
    ∑ y, φ y * sacc r0 y = ∑ y, φ y * rho H r0 y := by
  have hV : (0 : ℚ) < (Fintype.card V : ℚ) ^ H.card :=
    pow_pos (by exact_mod_cast Fintype.card_pos) _
  simp only [rho_eq, mul_div_assoc']
  rw [← sum_div, sum_class _ _ hφ, mul_div_cancel_left₀ _ hV.ne']

lemma F_eq : F H r0 zok = (∑ y, zfail r0 zok y / rho H r0 y) / Fintype.card (ι → V) := by
  unfold F
  rw [sum_filter]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not] at h; rw [h, div_zero]

lemma B_eq (y y' : ι → V) : (altR0Set H r0 zok).loop.B y y' =
    (if ∀ j ∉ H, y j = y' j then (1 - sacc r0 y) / (Fintype.card V : ℚ) ^ H.card else 0) +
      zfail r0 zok y / Fintype.card (ι → V) := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have hk1 : keepProb Hᶜ y y' =
      if ∀ j ∉ H, y j = y' j then 1 / (Fintype.card V : ℚ) ^ H.card else 0 := by
    unfold keepProb; rw [compl_compl]
    exact if_congr ⟨fun h j hj => (h j (mem_compl.mpr hj)).symm,
      fun h j hj => (h j (mem_compl.mp hj)).symm⟩ rfl rfl
  have hk0 : keepProb (∅ : Finset ι) y y' = 1 / Fintype.card (ι → V) := by
    unfold keepProb; rw [if_pos (by simp), compl_empty, card_univ, Fintype.card_fun]; push_cast; rfl
  calc (altR0Set H r0 zok).loop.B y y'
      = ∑ c, (1 / (Fintype.card C : ℚ)) * (keepProb Hᶜ y y' * (1 - if r0 y c then 1 else 0) +
          (if r0 y c ∧ ¬ zok y c then 1 else 0) / Fintype.card (ι → V)) := by
        simp only [ReusePolicy.loop]
        refine sum_congr rfl fun c _ => ?_
        congr 1
        simp only [altR0Set]
        cases r0 y c <;> cases zok y c <;> simp [hk0]
    _ = keepProb Hᶜ y y' * (1 - sacc r0 y) + zfail r0 zok y / Fintype.card (ι → V) := by
        unfold sacc zfail
        rw [← mul_sum]
        simp only [sum_add_distrib, ← sum_div, ← mul_sum, mul_sub, sum_sub_distrib, mul_one,
          sum_const, card_univ, nsmul_eq_mul]
        field_simp
    _ = _ := by
        rw [hk1]; split_ifs <;> ring

/-- The fixed point equation off the stuck nonces. -/
lemma fixed (hE : 1 - F H r0 zok ≠ 0) (y' : ι → V) (hy' : rho H r0 y' ≠ 0) :
    kappa H r0 zok / (Fintype.card (ι → V) * rho H r0 y') = (altR0Set H r0 zok).loop.π y' +
      (altR0Set H r0 zok).loop.step
        (fun y => kappa H r0 zok / (Fintype.card (ι → V) * rho H r0 y)) y' := by
  set κ := kappa H r0 zok with hκ
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have hV : (0 : ℚ) < (Fintype.card V : ℚ) ^ H.card :=
    pow_pos (by exact_mod_cast Fintype.card_pos) _
  have hsum : ∑ y, (if ∀ j ∉ H, y j = y' j then sacc r0 y else 0) =
      (Fintype.card V : ℚ) ^ H.card * rho H r0 y' := by
    rw [rho_eq]; field_simp
  have hstep : (altR0Set H r0 zok).loop.step
      (fun y => κ / ((Fintype.card (ι → V) : ℚ) * rho H r0 y)) y' =
      κ / ((Fintype.card (ι → V) : ℚ) * rho H r0 y') * (1 - rho H r0 y') +
        κ * F H r0 zok / (Fintype.card (ι → V) : ℚ) := by
    show ∑ y, κ / ((Fintype.card (ι → V) : ℚ) * rho H r0 y) * (altR0Set H r0 zok).loop.B y y' = _
    simp only [B_eq, mul_add, sum_add_distrib]
    congr 1
    · have e : ∀ y, κ / ((Fintype.card (ι → V) : ℚ) * rho H r0 y) *
          (if ∀ j ∉ H, y j = y' j then (1 - sacc r0 y) / (Fintype.card V : ℚ) ^ H.card else 0) =
          κ / ((Fintype.card (ι → V) : ℚ) * rho H r0 y') / (Fintype.card V : ℚ) ^ H.card *
            ((if ∀ j ∉ H, y j = y' j then 1 else 0) -
              (if ∀ j ∉ H, y j = y' j then sacc r0 y else 0)) := by
        intro y; split_ifs with hy
        · rw [rho_congr (y := y') (y' := y) hy]; ring
        · simp
      simp only [e, ← mul_sum, sum_sub_distrib, card_class, hsum]
      field_simp
    · have e : ∀ y, κ / ((Fintype.card (ι → V) : ℚ) * rho H r0 y) *
          (zfail r0 zok y / (Fintype.card (ι → V) : ℚ)) =
          κ / (Fintype.card (ι → V) : ℚ) / (Fintype.card (ι → V) : ℚ) *
            (zfail r0 zok y / rho H r0 y) := fun y => by ring
      simp only [e, ← mul_sum]
      rw [F_eq]
      ring
  rw [hstep]
  show κ / ((Fintype.card (ι → V) : ℚ) * rho H r0 y') = 1 / (Fintype.card (ι → V) : ℚ) + _
  rw [hκ, kappa]
  field_simp
  ring

lemma NE_eq : (Fintype.card (ι → V) : ℚ) * (1 - F H r0 zok) =
    (∑ y, if rho H r0 y = 0 then (1 : ℚ) else 0) +
      ∑ y, sacc (fun y c => r0 y c && zok y c) y / rho H r0 y := by
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have h1 : (Fintype.card (ι → V) : ℚ) * F H r0 zok = ∑ y, sacc r0 y / rho H r0 y -
      ∑ y, sacc (fun y c => r0 y c && zok y c) y / rho H r0 y := by
    rw [F_eq, mul_div_cancel₀ _ hN.ne', ← sum_sub_distrib]
    refine sum_congr rfl fun y _ => ?_
    rw [← sub_div, ← zfail_add (r0 := r0) (zok := zok) y]; ring
  have h2 : ∑ y, sacc r0 y / rho H r0 y = ∑ y, if rho H r0 y = 0 then (0 : ℚ) else 1 := by
    have := avg (H := H) (r0 := r0) (fun y => 1 / rho H r0 y) (fun y y' h => by rw [rho_congr h])
    calc ∑ y, sacc r0 y / rho H r0 y = ∑ y, 1 / rho H r0 y * sacc r0 y :=
          sum_congr rfl fun y _ => by ring
      _ = ∑ y, 1 / rho H r0 y * rho H r0 y := this
      _ = _ := sum_congr rfl fun y _ => by
          split_ifs with h
          · simp [h]
          · field_simp
  have h3 : (Fintype.card (ι → V) : ℚ) = ∑ y, ((if rho H r0 y = 0 then (1 : ℚ) else 0) +
      (if rho H r0 y = 0 then 0 else 1)) := by
    simp only [show ∀ y, ((if rho H r0 y = 0 then (1 : ℚ) else 0) +
      (if rho H r0 y = 0 then 0 else 1)) = 1 from fun y => by split_ifs <;> norm_num,
      sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [mul_sub, mul_one, h1, h2, h3, sum_add_distrib]
  ring

lemma one_sub_F_pos (hP : 0 < pacc (fun y c => r0 y c && zok y c)) : 0 < 1 - F H r0 zok := by
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have key := NE_eq (H := H) (r0 := r0) (zok := zok)
  have hSt : 0 ≤ ∑ y, if rho H r0 y = 0 then (1 : ℚ) else 0 :=
    sum_nonneg fun y _ => by split_ifs <;> norm_num
  have hG : 0 < ∑ y, sacc (fun y c => r0 y c && zok y c) y / rho H r0 y := by
    obtain ⟨y, hy⟩ : ∃ y, 0 < sacc (fun y c => r0 y c && zok y c) y := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have : ∑ y, sacc (fun y c => r0 y c && zok y c) y ≤ 0 := sum_nonpos fun y _ => h y
      unfold pacc at hP
      have := (div_pos_iff_of_pos_right hN).mp hP
      linarith
    have hρ : 0 < rho H r0 y := by
      rcases (rho_nonneg (H := H) (r0 := r0) y).lt_or_eq with h | h
      · exact h
      · exfalso; have := pass_of_rho (zok := zok) h.symm; linarith
    exact sum_pos' (fun y _ => div_nonneg (sacc_nonneg _) (rho_nonneg _))
      ⟨y, mem_univ _, div_pos hy hρ⟩
  have : 0 < (Fintype.card (ι → V) : ℚ) * (1 - F H r0 zok) := by rw [key]; linarith
  exact pos_of_mul_pos_right this hN.le

end AltR0Set

open AltR0Set in
/-- **Output law of `alt-r0` with resampled set `H`.** The loop outputs `(y, c)` with probability
`κ / (N·|C|·ρ y)` if `(y, c)` passes (and `0` otherwise), where `ρ y` is the r₀ pass probability
with the `H` part fresh. Stuck nonces (`ρ y = 0`) are never left and never accept. -/
theorem altR0Set_law (H : Finset ι) (r0 zok : (ι → V) → C → Bool)
    (hP : 0 < pacc (fun y c => r0 y c && zok y c)) (x : (ι → V) × C) :
    Tendsto (fun K => (altR0Set H r0 zok).loop.outUpTo K x) atTop (𝓝 (altLaw H r0 zok x)) := by
  have hE := one_sub_F_pos (H := H) hP
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hκ : 0 < kappa H r0 zok := one_div_pos.mpr hE
  set ν : (ι → V) → ℚ := fun y => kappa H r0 zok / (Fintype.card (ι → V) * rho H r0 y) with hν
  have key := Loop.tendsto_of_fixed_off (altR0Set H r0 zok).loop (fun y => rho H r0 y = 0) ν
    (ReusePolicy.B_nonneg _) (ReusePolicy.A_nonneg _) (ReusePolicy.row _)
    (fun _ => by show (0 : ℚ) ≤ 1 / _; positivity)
    (by
      show ∑ _y : ι → V, 1 / (Fintype.card (ι → V) : ℚ) = 1
      rw [sum_const, card_univ, nsmul_eq_mul]; field_simp)
    (fun y y' hy hy' => by
      rw [B_eq, zfail_of_rho hy, zero_div, add_zero, if_neg]
      intro hyy; exact hy' ((rho_congr (r0 := r0) hyy).symm.trans hy))
    (fun y x hy => by
      show (if x.1 = y ∧ altR0Set H r0 zok y x.2 = none then _ else _) = 0
      rw [if_neg]
      rintro ⟨-, h⟩
      simp [altR0Set, r0_of_rho hy] at h)
    (fun y => div_nonneg hκ.le (mul_nonneg hN.le (rho_nonneg _)))
    (fun y' hy' => fixed hE.ne' y' hy') x
  have hval : ∑ y, ν y * (altR0Set H r0 zok).loop.A y x = altLaw H r0 zok x := by
    rw [sum_eq_single x.1]
    · show ν x.1 * (if x.1 = x.1 ∧ altR0Set H r0 zok x.1 x.2 = none then
        1 / (Fintype.card C : ℚ) else 0) = _
      unfold altLaw altR0Set
      rw [hν]
      dsimp only
      cases r0 x.1 x.2 <;> cases zok x.1 x.2 <;> simp
      by_cases hρ : rho H r0 x.1 = 0
      · simp [hρ]
      · simp [hρ]
        field_simp
    · intro y _ hy
      show ν y * (if x.1 = y ∧ _ then _ else _) = 0
      rw [if_neg (fun h => hy h.1.symm), mul_zero]
    · intro h; exact absurd (mem_univ _) h
  rw [hval] at key
  exact key

open AltR0Set in
/-- **Output law of vanilla signing**: uniform on the passing `(y, c)`. (The case `H = univ`,
`zok = true` of `altR0Set_law`.) -/
theorem vanilla_law (pass : (ι → V) → C → Bool) (hP : 0 < pacc pass) (x : (ι → V) × C) :
    Tendsto (fun K => (vanilla pass).loop.outUpTo K x) atTop (𝓝 (vanLaw pass x)) := by
  have hv : vanilla pass = altR0Set univ pass (fun _ _ => true) := by
    funext y c; unfold vanilla altR0Set; cases pass y c <;> simp
  have hP' : 0 < pacc (fun y c => pass y c && (fun _ _ => true : (ι → V) → C → Bool) y c) := by
    simpa using hP
  have hrho : ∀ y, rho univ pass y = pacc pass := by
    intro y
    unfold rho pacc sacc
    simp
    rw [← sum_div, div_div, mul_comm (Fintype.card C : ℚ)]
  have hκ : kappa (univ : Finset ι) pass (fun _ _ => true) = 1 := by
    simp [kappa, F, zfail]
  have hval : altLaw univ pass (fun _ _ => true) x = vanLaw pass x := by
    unfold altLaw vanLaw
    simp only [hrho, hκ, Bool.and_true, ne_eq, hP.ne', not_false_eq_true, and_true]
  rw [hv, ← hval]
  exact altR0Set_law univ pass _ hP' x

namespace AltR0Set

/-- The arithmetic behind `altR0Set_close`. -/
lemma dist_aux {Y : Type*} [Fintype Y] (ρ s : Y → ℚ) (N P E κ μ₀ D : ℚ)
    (hN : 0 < N) (hμ : 0 < μ₀) (hρ0 : ∀ y, 0 ≤ ρ y) (hs0 : ∀ y, 0 ≤ s y)
    (hst : ∀ y, ρ y = 0 → s y = 0)
    (hNE : N * E = (∑ y, if ρ y = 0 then (1 : ℚ) else 0) + ∑ y, s y / ρ y)
    (hsP : ∑ y, s y = N * P)
    (hψ : ∑ y, |μ₀ - ρ y| / ρ y * s y ≤ ∑ y, if ρ y = 0 then 0 else |ρ y - μ₀|)
    (hSg : ∑ y, |ρ y - μ₀| = N * (μ₀ * D)) (hκ : κ = 1 / E) (hD : μ₀ * D < P) :
    (∑ y, s y * |κ / ρ y - 1 / P|) / N ≤ 2 * μ₀ * D / (P - μ₀ * D) ∧
      1 - κ * (∑ y, s y / ρ y) / N ≤ μ₀ * D / (P - μ₀ * D) := by
  have hD0 : 0 ≤ D := by
    have h1 : N * 0 ≤ N * (μ₀ * D) := by
      rw [mul_zero, ← hSg]; exact sum_nonneg fun _ _ => abs_nonneg _
    have h2 : μ₀ * 0 ≤ μ₀ * D := by rw [mul_zero]; exact le_of_mul_le_mul_left h1 hN
    exact le_of_mul_le_mul_left h2 hμ
  have hP : 0 < P := by linarith [mul_nonneg hμ.le hD0]
  -- `|μ₀ (1 - F) - P| ≤ μ₀ D`, scaled by `N`
  have ha : |μ₀ * (N * E) - N * P| ≤ N * (μ₀ * D) := by
    rw [← hSg]
    have e1 : ∑ y, (if ρ y = 0 then μ₀ else 0) = μ₀ * ∑ y, (if ρ y = 0 then (1 : ℚ) else 0) := by
      rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; split_ifs <;> simp
    have e : μ₀ * (N * E) - N * P =
        ∑ y, ((if ρ y = 0 then μ₀ else 0) + (μ₀ * (s y / ρ y) - s y)) := by
      rw [sum_add_distrib, sum_sub_distrib, e1, ← mul_sum, hsP, hNE]; ring
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ y, |(if ρ y = 0 then μ₀ else 0) + (μ₀ * (s y / ρ y) - s y)|
        ≤ ∑ y, ((if ρ y = 0 then μ₀ else 0) + |μ₀ - ρ y| / ρ y * s y) := sum_le_sum fun y _ => by
          by_cases h : ρ y = 0
          · rw [hst y h, if_pos h, h]; simp [abs_of_pos hμ]
          · have hρ : 0 < ρ y := lt_of_le_of_ne (hρ0 y) (Ne.symm h)
            rw [if_neg h, zero_add, zero_add,
              show μ₀ * (s y / ρ y) - s y = (μ₀ - ρ y) / ρ y * s y by field_simp,
              abs_mul, abs_div, abs_of_pos hρ, abs_of_nonneg (hs0 y)]
      _ = ∑ y, (if ρ y = 0 then μ₀ else 0) + ∑ y, |μ₀ - ρ y| / ρ y * s y := sum_add_distrib
      _ ≤ ∑ y, (if ρ y = 0 then μ₀ else 0) + ∑ y, (if ρ y = 0 then 0 else |ρ y - μ₀|) := by
          linarith
      _ = ∑ y, |ρ y - μ₀| := by
          rw [← sum_add_distrib]; refine sum_congr rfl fun y _ => ?_
          split_ifs with h
          · rw [h, zero_sub, abs_neg, abs_of_pos hμ, add_zero]
          · rw [zero_add]
  have hlow : P - μ₀ * D ≤ μ₀ * E := by
    have h1 := (abs_le.mp ha).1
    have : N * (P - μ₀ * D) ≤ N * (μ₀ * E) := by linarith
    exact le_of_mul_le_mul_left this hN
  have hE : 0 < E := pos_of_mul_pos_right (by linarith) hμ.le
  have hgap : 0 < P - μ₀ * D := by linarith
  have hκle : κ ≤ μ₀ / (P - μ₀ * D) := by
    rw [hκ, div_le_div_iff₀ hE hgap]; linarith
  have hκ0 : 0 < κ := by rw [hκ]; exact one_div_pos.mpr hE
  have hκE : κ * E = 1 := by rw [hκ]; field_simp
  constructor
  · have hpt : ∀ y, s y * |κ / ρ y - 1 / P| ≤
        κ / μ₀ * (|μ₀ - ρ y| / ρ y * s y) + s y * |κ / μ₀ - 1 / P| := by
      intro y
      by_cases h : ρ y = 0
      · rw [hst y h]; simp
      · have hρ : 0 < ρ y := lt_of_le_of_ne (hρ0 y) (Ne.symm h)
        have e : κ / ρ y - 1 / P = κ / μ₀ * ((μ₀ - ρ y) / ρ y) + (κ / μ₀ - 1 / P) := by
          field_simp; ring
        rw [e]
        calc s y * |κ / μ₀ * ((μ₀ - ρ y) / ρ y) + (κ / μ₀ - 1 / P)|
            ≤ s y * (|κ / μ₀ * ((μ₀ - ρ y) / ρ y)| + |κ / μ₀ - 1 / P|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) (hs0 y)
          _ = _ := by
              rw [abs_mul, abs_div, abs_div, abs_of_pos hκ0, abs_of_pos hμ, abs_of_pos hρ]; ring
    have hlast : N * P * |κ / μ₀ - 1 / P| ≤ κ / μ₀ * (N * (μ₀ * D)) := by
      have e : N * P * (κ / μ₀ - 1 / P) = κ / μ₀ * (N * P - μ₀ * (N * E)) := by
        rw [hκ]; field_simp
      have h1 : |N * P * (κ / μ₀ - 1 / P)| = N * P * |κ / μ₀ - 1 / P| := by
        rw [abs_mul, abs_of_pos (mul_pos hN hP)]
      rw [← h1, e, abs_mul, abs_of_pos (div_pos hκ0 hμ), abs_sub_comm]
      exact mul_le_mul_of_nonneg_left ha (div_pos hκ0 hμ).le
    have hsum : ∑ y, s y * |κ / ρ y - 1 / P| ≤
        κ / μ₀ * (N * (μ₀ * D)) + κ / μ₀ * (N * (μ₀ * D)) := by
      calc ∑ y, s y * |κ / ρ y - 1 / P|
          ≤ ∑ y, (κ / μ₀ * (|μ₀ - ρ y| / ρ y * s y) + s y * |κ / μ₀ - 1 / P|) :=
            sum_le_sum fun y _ => hpt y
        _ = κ / μ₀ * ∑ y, |μ₀ - ρ y| / ρ y * s y + N * P * |κ / μ₀ - 1 / P| := by
            rw [sum_add_distrib, ← mul_sum, ← sum_mul, hsP]
        _ ≤ _ := by
            have h1 : ∑ y, |μ₀ - ρ y| / ρ y * s y ≤ N * (μ₀ * D) := by
              refine hψ.trans ?_
              rw [← hSg]
              exact sum_le_sum fun y _ => by split_ifs; exacts [abs_nonneg _, le_rfl]
            have := mul_le_mul_of_nonneg_left h1 (div_pos hκ0 hμ).le
            linarith
    calc (∑ y, s y * |κ / ρ y - 1 / P|) / N
        ≤ (κ / μ₀ * (N * (μ₀ * D)) + κ / μ₀ * (N * (μ₀ * D))) / N :=
          (div_le_div_iff_of_pos_right hN).mpr hsum
      _ = 2 * D * κ := by field_simp; ring
      _ ≤ 2 * D * (μ₀ / (P - μ₀ * D)) :=
          mul_le_mul_of_nonneg_left hκle (mul_nonneg (by norm_num) hD0)
      _ = _ := by ring
  · have hSt : μ₀ * ∑ y, (if ρ y = 0 then (1 : ℚ) else 0) ≤ N * (μ₀ * D) := by
      rw [← hSg, mul_sum]
      exact sum_le_sum fun y _ => by
        split_ifs with h
        · rw [h, zero_sub, abs_neg, abs_of_pos hμ, mul_one]
        · rw [mul_zero]; exact abs_nonneg _
    have hSt' : (∑ y, if ρ y = 0 then (1 : ℚ) else 0) ≤ N * D := by
      have : μ₀ * ∑ y, (if ρ y = 0 then (1 : ℚ) else 0) ≤ μ₀ * (N * D) := by linarith
      exact le_of_mul_le_mul_left this hμ
    have hG : ∑ y, s y / ρ y = N * E - ∑ y, (if ρ y = 0 then (1 : ℚ) else 0) := by
      rw [hNE]; ring
    have e : 1 - κ * (∑ y, s y / ρ y) / N = κ * (∑ y, if ρ y = 0 then (1 : ℚ) else 0) / N := by
      rw [hG]
      have : κ * (N * E - ∑ y, (if ρ y = 0 then (1 : ℚ) else 0)) / N =
          κ * E - κ * (∑ y, if ρ y = 0 then (1 : ℚ) else 0) / N := by
        field_simp
      rw [this, hκE]; ring
    rw [e]
    calc κ * (∑ y, if ρ y = 0 then (1 : ℚ) else 0) / N ≤ κ * (N * D) / N :=
          (div_le_div_iff_of_pos_right hN).mpr (mul_le_mul_of_nonneg_left hSt' hκ0.le)
      _ = D * κ := by field_simp
      _ ≤ D * (μ₀ / (P - μ₀ * D)) := mul_le_mul_of_nonneg_left hκle hD0
      _ = _ := by ring

end AltR0Set

open AltR0Set in
/-- **Distance of `alt-r0` to vanilla.** Let `D` be the mean relative deviation of `ρ` from some
`μ₀ > 0`. If `μ₀·D < P` (the vanilla acceptance probability), the statistical distance between
the output laws of `alt-r0` and vanilla is at most `μ₀ D / (P - μ₀ D)` (twice that in `ℓ¹`), and
so is the probability that `alt-r0` never terminates. -/
theorem altR0Set_close (H : Finset ι) (r0 zok : (ι → V) → C → Bool) (μ₀ : ℚ) (hμ : 0 < μ₀)
    (hD : μ₀ * dev H r0 μ₀ < pacc (fun y c => r0 y c && zok y c)) :
    ∑ x, |altLaw H r0 zok x - vanLaw (fun y c => r0 y c && zok y c) x| ≤
        2 * μ₀ * dev H r0 μ₀ / (pacc (fun y c => r0 y c && zok y c) - μ₀ * dev H r0 μ₀) ∧
      1 - ∑ x, altLaw H r0 zok x ≤
        μ₀ * dev H r0 μ₀ / (pacc (fun y c => r0 y c && zok y c) - μ₀ * dev H r0 μ₀) := by
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hsP : ∑ y, sacc (fun y c => r0 y c && zok y c) y =
      Fintype.card (ι → V) * pacc (fun y c => r0 y c && zok y c) := by
    unfold pacc; field_simp
  have hSg : ∑ y, |rho H r0 y - μ₀| = Fintype.card (ι → V) * (μ₀ * dev H r0 μ₀) := by
    unfold dev; field_simp
  have hψ : ∑ y, |μ₀ - rho H r0 y| / rho H r0 y * sacc (fun y c => r0 y c && zok y c) y ≤
      ∑ y, if rho H r0 y = 0 then 0 else |rho H r0 y - μ₀| := by
    calc _ ≤ ∑ y, |μ₀ - rho H r0 y| / rho H r0 y * sacc r0 y :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (sacc_le y)
            (div_nonneg (abs_nonneg _) (rho_nonneg _))
      _ = ∑ y, |μ₀ - rho H r0 y| / rho H r0 y * rho H r0 y :=
          avg _ (fun y y' h => by rw [rho_congr h])
      _ = _ := sum_congr rfl fun y _ => by
          split_ifs with h
          · simp [h]
          · rw [div_mul_cancel₀ _ h, abs_sub_comm]
  obtain ⟨h1, h2⟩ := dist_aux (rho H r0) (sacc (fun y c => r0 y c && zok y c))
    (Fintype.card (ι → V)) (pacc (fun y c => r0 y c && zok y c)) (1 - F H r0 zok)
    (kappa H r0 zok) μ₀ (dev H r0 μ₀) hN hμ rho_nonneg sacc_nonneg (fun _ h => pass_of_rho h)
    NE_eq hsP hψ hSg rfl hD
  have hTV : ∑ x, |altLaw H r0 zok x - vanLaw (fun y c => r0 y c && zok y c) x| =
      (∑ y, sacc (fun y c => r0 y c && zok y c) y *
        |kappa H r0 zok / rho H r0 y - 1 / pacc (fun y c => r0 y c && zok y c)|) /
        Fintype.card (ι → V) := by
    rw [Fintype.sum_prod_type, sum_div]
    refine sum_congr rfl fun y _ => ?_
    have e : ∀ c, |altLaw H r0 zok (y, c) - vanLaw (fun y c => r0 y c && zok y c) (y, c)| =
        (if (r0 y c && zok y c) = true then (1 : ℚ) else 0) *
          (|kappa H r0 zok / rho H r0 y - 1 / pacc (fun y c => r0 y c && zok y c)| /
            (Fintype.card (ι → V) * Fintype.card C)) := by
      intro c
      unfold altLaw vanLaw
      dsimp only
      by_cases hp : (r0 y c && zok y c) = true
      · have hρ : rho H r0 y ≠ 0 := fun h => by simp [r0_of_rho h c] at hp
        rw [if_pos ⟨hp, hρ⟩, if_pos hp, if_pos hp, one_mul,
          show ∀ a b : ℚ, a / (b * rho H r0 y) - 1 / (b * pacc (fun y c => r0 y c && zok y c)) =
            (a / rho H r0 y - 1 / pacc (fun y c => r0 y c && zok y c)) / b from fun a b => by ring,
          abs_div, abs_of_pos (mul_pos hN hC)]
      · rw [if_neg (fun h => hp h.1), if_neg hp, if_neg hp]; simp
    simp only [e, ← sum_mul]
    unfold sacc
    ring
  have hU : ∑ x, altLaw H r0 zok x = kappa H r0 zok *
      (∑ y, sacc (fun y c => r0 y c && zok y c) y / rho H r0 y) / Fintype.card (ι → V) := by
    rw [Fintype.sum_prod_type, mul_sum, sum_div]
    refine sum_congr rfl fun y _ => ?_
    have e : ∀ c, altLaw H r0 zok (y, c) = (if (r0 y c && zok y c) = true then (1 : ℚ) else 0) *
        (kappa H r0 zok / (Fintype.card (ι → V) * Fintype.card C * rho H r0 y)) := by
      intro c
      unfold altLaw
      dsimp only
      by_cases hρ : rho H r0 y = 0
      · simp [hρ]
      · by_cases hp : (r0 y c && zok y c) = true
        · rw [if_pos ⟨hp, hρ⟩, if_pos hp, one_mul]
        · rw [if_neg (fun h => hp h.1), if_neg hp, zero_mul]
    simp only [e, ← sum_mul]
    unfold sacc
    ring
  rw [hTV, hU]
  exact ⟨h1, h2⟩

end AltR0Set

/-! ## A Dilithium-shaped toy

`q = 17`, `n = 1` (so `R_q = ℤ/17`), `γ₂ = 2` (`2γ₂ ∣ q - 1`), `γ₁ = 3`, `η = 1`, `τ = 1` (so
`c = ±1` and `β = 1`), `ℓ = 2`, `k = 1`, `A = (4 7)`. The coefficient `v : Fin 6` of `y` stands for
`v - 2 ∈ (-γ₁, γ₁]`, the challenge `c : Fin 2` for `2c - 1 = ±1`. `lowBits` is FIPS 204's
`Decompose` (including the corner case `r⁺ - r₀ = q - 1`).

The two keys `s₁ = (-1, -1), s₂ = -1` and `s₁ = (1, 0), s₂ = 1` have the same public key
`t = A·s₁ + s₂ = 5`. The signature `(c, z) = (1, (0, 0))` comes from `y = (1, 1)` under the first key
and from `y = (-1, 0)` under the second. Vanilla signing outputs it with probability `1/4` under
both keys; each non-exact policy outputs it with different probabilities under the two keys.

Each limit is computed with `Loop.tendsto_outUpTo` from an explicit solution `ν` of `ν = π + ν·B`
(found with exact linear algebra outside Lean, checked here by the kernel), with `m = 3` and
`ε = 1/200`. -/

namespace Toy

def yv (v : Fin 6) : ℤ := (v : ℤ) - 2
def cv (c : Fin 2) : ℤ := 2 * (c : ℤ) - 1

/-- `r₀` of FIPS 204 `Decompose` for `q = 17`, `γ₂ = 2`. -/
def lowBits (r : ℤ) : ℤ :=
  let rp := r % 17
  let r0 := if 2 < rp % 4 then rp % 4 - 4 else rp % 4
  if rp - r0 = 16 then r0 - 1 else r0

structure Key where
  s1 : Fin 2 → ℤ
  s2 : ℤ

def Arow : Fin 2 → ℤ := ![4, 7]

/-- The public key `t = A·s₁ + s₂ mod q`. -/
def pk (k : Key) : ℤ := (Arow 0 * k.s1 0 + Arow 1 * k.s1 1 + k.s2) % 17

/-- z-check of polynomial `i`: `|yᵢ + c·s₁ᵢ| < γ₁ - β = 2`. -/
def zc (k : Key) (i : Fin 2) (v : Fin 6) (c : Fin 2) : Bool :=
  decide (|yv v + cv c * k.s1 i| < 2)

/-- r₀-check: `|LowBits(A·y - c·s₂)| < γ₂ - β = 1`. -/
def r0 (k : Key) (y : Fin 2 → Fin 6) (c : Fin 2) : Bool :=
  decide (|lowBits (Arow 0 * yv (y 0) + Arow 1 * yv (y 1) - cv c * k.s2)| < 1)

def key1 : Key := ⟨![-1, -1], -1⟩
def key2 : Key := ⟨![1, 0], 1⟩

/-- The nonces giving the signature `(c, z) = (1, (0, 0))` under the two keys. -/
def y1 : Fin 2 → Fin 6 := ![3, 3]
def y2 : Fin 2 → Fin 6 := ![1, 2]

lemma same_pk : pk key1 = pk key2 := by decide

lemma y1_sig : ∀ i, yv (y1 i) + cv 1 * key1.s1 i = 0 := by decide
lemma y2_sig : ∀ i, yv (y2 i) + cv 1 * key2.s1 i = 0 := by decide

def tab (l : List ℚ) (y : Fin 2 → Fin 6) : ℚ := l.getD (6 * (y 0).val + (y 1).val) 0

def nuVan_key1 : List ℚ := [1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2]
def nuVan_key2 : List ℚ := [1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2, 1/2]
def nuAltR0_key1 : List ℚ := [1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3]
def nuAltR0_key2 : List ℚ := [1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3, 1/3, 2/3, 2/3, 1/3, 4/9, 2/3]
def nuR0Pz_key1 : List ℚ := [60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121]
def nuR0Pz_key2 : List ℚ := [60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121, 60/121, 6/11, 5/11, 6/11, 20/33, 60/121]
def nuZY1_key1 : List ℚ := [88/171, 88/171, 11/19, 8/19, 88/171, 22/57, 88/171, 88/171, 11/19, 8/19, 88/171, 22/57, 88/171, 88/171, 11/19, 8/19, 88/171, 22/57, 88/171, 88/171, 11/19, 8/19, 88/171, 22/57, 88/171, 88/171, 11/19, 8/19, 88/171, 22/57, 88/171, 88/171, 11/19, 8/19, 88/171, 22/57]
def nuZY1_key2 : List ℚ := [1/3, 2/3, 1/2, 1/2, 1/3, 1/3, 1/3, 2/3, 1/2, 1/2, 1/3, 1/3, 1/3, 2/3, 1/2, 1/2, 1/3, 1/3, 1/3, 2/3, 1/2, 1/2, 1/3, 1/3, 1/3, 2/3, 1/2, 1/2, 1/3, 1/3, 1/3, 2/3, 1/2, 1/2, 1/3, 1/3]

lemma limit (P : ReusePolicy (Fin 2) (Fin 6) (Fin 2)) (ν : List ℚ) (x : (Fin 2 → Fin 6) × Fin 2)
    (hrow : ∀ y, P.loop.survive 1 y ≤ 1) (hm : ∀ y, P.loop.survive 3 y ≤ 1 - 1 / 200)
    (hν : ∀ y', tab ν y' = P.loop.π y' + P.loop.step (tab ν) y') (v : ℚ)
    (hv : ∑ s, tab ν s * P.loop.A s x = v) :
    Tendsto (fun K => P.loop.outUpTo K x) atTop (𝓝 v) :=
  hv ▸ P.loop.tendsto_outUpTo (tab ν) (P.B_nonneg) (P.A_nonneg) (P.A_le_one) hrow 3
    (by norm_num) (1 / 200) (by norm_num) (by norm_num) hm hν x

set_option maxRecDepth 100000

/-- Vanilla: the signature `(1, (0,0))` has probability `1/4` under both keys. -/
theorem toy_vanilla_same :
    Tendsto (fun K => (vanilla (pass (zc key1) (r0 key1))).loop.outUpTo K (y1, 1)) atTop
      (𝓝 (1 / 4)) ∧
    Tendsto (fun K => (vanilla (pass (zc key2) (r0 key2))).loop.outUpTo K (y2, 1)) atTop
      (𝓝 (1 / 4)) :=
  ⟨limit _ nuVan_key1 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel),
    limit _ nuVan_key2 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel)⟩

/-- **`alt-r0` is not zero-knowledge** (ePrint 2020/1158 Algorithm 2, thesis Algorithm 8.3): two
keys with the same public key output the signature `(1, (0,0))` with probabilities `1/6` and
`1/3`. -/
theorem toy_altR0_leaks :
    Tendsto (fun K => (altR0 0 (zc key1) (r0 key1)).loop.outUpTo K (y1, 1)) atTop
      (𝓝 (1 / 6)) ∧
    Tendsto (fun K => (altR0 0 (zc key2) (r0 key2)).loop.outUpTo K (y2, 1)) atTop
      (𝓝 (1 / 3)) :=
  ⟨limit _ nuAltR0_key1 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel),
    limit _ nuAltR0_key2 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel)⟩

/-- **r₀-check first, then prefix resampling on a z failure** (the partial resampling of ePrint
Appendix A in the check order of its Algorithm 3) is not zero-knowledge: `3/11` against `5/22`. -/
theorem toy_r0FirstPrefixZ_leaks :
    Tendsto (fun K => (r0FirstPrefixZ (zc key1) (r0 key1)).loop.outUpTo K (y1, 1)) atTop
      (𝓝 (3 / 11)) ∧
    Tendsto (fun K => (r0FirstPrefixZ (zc key2) (r0 key2)).loop.outUpTo K (y2, 1)) atTop
      (𝓝 (5 / 22)) :=
  ⟨limit _ nuR0Pz_key1 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel),
    limit _ nuR0Pz_key2 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel)⟩

/-- **z-check first, then keep the tail on an r₀ failure** is not zero-knowledge: `4/19` against
`1/4`. -/
theorem toy_zFirstThenY1_leaks :
    Tendsto (fun K => (zFirstThenY1 0 (zc key1) (r0 key1)).loop.outUpTo K (y1, 1)) atTop
      (𝓝 (4 / 19)) ∧
    Tendsto (fun K => (zFirstThenY1 0 (zc key2) (r0 key2)).loop.outUpTo K (y2, 1)) atTop
      (𝓝 (1 / 4)) :=
  ⟨limit _ nuZY1_key1 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel),
    limit _ nuZY1_key2 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
      (by decide +kernel)⟩

end Toy

end Bathwater
