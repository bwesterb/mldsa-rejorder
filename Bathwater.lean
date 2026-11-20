import Mathlib
import RejOrder

/-!
# Nonce reuse in ML-DSA signing ("Don't throw your nonces out with the bathwater")

This file collects, in order:

* `BathwaterCore`: loop semantics, partial reuse of the nonce, the exactness of alt-z, the output
  law of alt-r0 and its distance to vanilla, and the toy counterexamples.
* `FourierPart`: a Fourier bound on the covariance of indicators of product sets.
* `AltR0Part`: the second moment over `A` of the r₀ pass probability with the tail fixed.
* `AltR0ExcPart`: the probability of exceptional slots.
* `AltR0SharpPart`: the sharper second moment by pairing orthogonal test vectors, and its
  kernel-checked ML-DSA instances.
* `AltR0FinalPart`: alt-r0 for ML-DSA-44/65/87 end to end.
* `MinEntropyPart`: min-entropy of the commitment with a fresh head.

It imports `RejOrder.lean` for the module/NTT machinery and the gap counts.
-/

section BathwaterCore

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

end BathwaterCore

section FourierPart

/-!
# A Fourier bound on the covariance of two indicator functions

Let `q` be prime, `P` a finite additive commutative group and `φ φ' : P →+ (Fin m → ZMod q)`
two additive maps. Let `G = Fintype.piFinset g` be a product of nonempty "good" sets
`g r ⊆ ZMod q`, with density `μ = ∏ r, |g r| / q`, and suppose that in every coordinate the bad
density is at most `β` times the good density: `q - |g r| ≤ β |g r|`.

The theorem `AltR0.cov_le` states that, for `a` uniform on `P`, the covariance of the
indicators `1[φ a ∈ G]` and `1[φ' a ∈ G]` is bounded in absolute value by
`μ² · ∑_{ξ, ξ' ≠ 0, ξ ⬝ φ + ξ' ⬝ φ' ≡ 0} β ^ (wt ξ + wt ξ')`,
where `wt ξ` is the Hamming weight of `ξ`.

The proof is by finite Fourier analysis over `ZMod q` with the standard additive character
`ZMod.stdAddChar`: the Fourier coefficients of `1_G` factor over coordinates, each nonzero
frequency in a coordinate costs a factor `β`, and averaging the characters over `P` keeps
exactly the pairs `(ξ, ξ')` for which `a ↦ ξ ⬝ φ a + ξ' ⬝ φ' a` vanishes identically.
The statement itself lives entirely in `ℚ`.
-/

open Finset

namespace AltR0

section Fourier

variable {q : ℕ} [NeZero q]

local notation "ψ" => (ZMod.stdAddChar : AddChar (ZMod q) ℂ)

/-- One-dimensional character sum. -/
lemma sum_psi_mul (b : ZMod q) :
    ∑ x : ZMod q, ψ (x * b) = if b = 0 then (q : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  split_ifs <;> simp

lemma psi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod q) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- One-dimensional Fourier coefficient of the indicator of `s`. -/
noncomputable def gh (s : Finset (ZMod q)) (x : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ u ∈ s, ψ (-(x * u))

/-- One-dimensional Fourier inversion. -/
lemma gh_inv (s : Finset (ZMod q)) (t : ZMod q) :
    ∑ x : ZMod q, gh s x * ψ (x * t) = if t ∈ s then 1 else 0 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have h1 : ∀ x, gh s x * ψ (x * t) = (q : ℂ)⁻¹ * ∑ u ∈ s, ψ (x * (t - u)) := by
    intro x
    rw [gh, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∑ u ∈ s, ∑ x : ZMod q, ψ (x * (t - u)) = if t ∈ s then (q : ℂ) else 0 := by
    simp_rw [sum_psi_mul, sub_eq_zero]
    exact Finset.sum_ite_eq s t (fun _ => (q : ℂ))
  rw [h2]
  split_ifs
  · exact inv_mul_cancel₀ hq
  · exact mul_zero _

lemma gh_zero (s : Finset (ZMod q)) : gh s 0 = (s.card : ℂ) / q := by
  simp [gh, div_eq_inv_mul]

lemma gh_norm (s : Finset (ZMod q)) (β : ℝ) (hs : (q : ℝ) - s.card ≤ β * s.card)
    (x : ZMod q) : ‖gh s x‖ ≤ (s.card / q : ℝ) * (if x ≠ 0 then β else 1) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  unfold gh
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  split_ifs with hx
  · have htot : ∑ u, ψ (-(x * u)) = 0 := by
      have := sum_psi_mul (q := q) (-x)
      simp only [neg_eq_zero, hx, ↓reduceIte] at this
      rw [← this]
      refine Finset.sum_congr rfl fun u _ => ?_
      congr 1
      ring
    have hs' : ∑ u ∈ s, ψ (-(x * u)) = -∑ u ∈ sᶜ, ψ (-(x * u)) := by
      rw [eq_neg_iff_add_eq_zero, Finset.sum_add_sum_compl, htot]
    have hb : ‖∑ u ∈ s, ψ (-(x * u))‖ ≤ (q : ℝ) - s.card := by
      rw [hs', norm_neg]
      refine (norm_sum_le _ _).trans ?_
      have hle : s.card ≤ q := by simpa [ZMod.card] using s.card_le_univ
      simp only [AddChar.norm_apply, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_compl, ZMod.card]
      rw [Nat.cast_sub hle]
    calc (q : ℝ)⁻¹ * ‖∑ u ∈ s, ψ (-(x * u))‖ ≤ (q : ℝ)⁻¹ * ((q : ℝ) - s.card) := by gcongr
      _ ≤ (q : ℝ)⁻¹ * (β * s.card) := by gcongr
      _ = _ := by ring
  · push Not at hx
    subst hx
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul,
      mul_one, Complex.norm_natCast]
    rw [div_eq_inv_mul]

variable {m : ℕ}

/-- Fourier coefficient of the indicator of `Fintype.piFinset g`. -/
noncomputable def Gh (g : Fin m → Finset (ZMod q)) (ξ : Fin m → ZMod q) : ℂ :=
  ∏ r, gh (g r) (ξ r)

lemma Gh_inv (g : Fin m → Finset (ZMod q)) (w : Fin m → ZMod q) :
    ∑ ξ, Gh g ξ * ψ (ξ ⬝ᵥ w) = if w ∈ Fintype.piFinset g then 1 else 0 := by
  have h1 : ∀ ξ : Fin m → ZMod q, Gh g ξ * ψ (ξ ⬝ᵥ w) = ∏ r, gh (g r) (ξ r) * ψ (ξ r * w r) := by
    intro ξ
    rw [Gh, dotProduct, psi_sum, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun ξ _ => h1 ξ,
    ← Fintype.prod_sum (fun r x => gh (g r) x * ψ (x * w r))]
  simp_rw [gh_inv]
  rw [Fintype.prod_boole]
  simp [Fintype.mem_piFinset]

lemma Gh_zero (g : Fin m → Finset (ZMod q)) : Gh g 0 = ∏ r, ((g r).card : ℂ) / q := by
  simp [Gh, gh_zero]

lemma ind_sub_eq (g : Fin m → Finset (ZMod q)) (w : Fin m → ZMod q) :
    (((if w ∈ Fintype.piFinset g then (1 : ℚ) else 0) - ∏ r, ((g r).card : ℚ) / q : ℚ) : ℂ)
      = ∑ ξ ∈ univ.erase 0, Gh g ξ * ψ (ξ ⬝ᵥ w) := by
  rw [Finset.sum_erase_eq_sub (mem_univ _), Gh_inv, Gh_zero]
  simp only [zero_dotProduct, AddChar.map_zero_eq_one, mul_one]
  split_ifs <;> push_cast <;> ring

lemma Gh_norm (g : Fin m → Finset (ZMod q)) (β : ℝ)
    (hs : ∀ r, (q : ℝ) - (g r).card ≤ β * (g r).card) (ξ : Fin m → ZMod q) :
    ‖Gh g ξ‖ ≤ (∏ r, ((g r).card : ℝ) / q) * β ^ (univ.filter fun r => ξ r ≠ 0).card := by
  rw [Gh, norm_prod]
  calc ∏ r, ‖gh (g r) (ξ r)‖
      ≤ ∏ r, (((g r).card : ℝ) / q * (if ξ r ≠ 0 then β else 1)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun r _ => gh_norm _ β (hs r) _)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
          Finset.prod_const]

/-- Averaging a character composed with an additive map over a finite group. -/
lemma sum_char_hom {P : Type*} [Fintype P] [AddCommGroup P] (χ : P →+ ZMod q) :
    ∑ a, ψ (χ a) = if (∀ a, χ a = 0) then (Fintype.card P : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · push Not at h
    obtain ⟨a0, ha0⟩ := h
    let Ψ : AddChar P ℂ := AddChar.compAddMonoidHom ψ χ
    have hne : Ψ ≠ 0 := by
      intro h0
      apply ha0
      apply ZMod.injective_stdAddChar
      rw [AddChar.map_zero_eq_one]
      have := DFunLike.congr_fun h0 a0
      simpa [Ψ] using this
    simpa [Ψ] using AddChar.sum_eq_zero_iff_ne_zero.2 hne

end Fourier

/-- **Covariance bound.** All quantities are rational. -/
theorem cov_le {q : ℕ} [Fact q.Prime] {m : ℕ} {P : Type*} [Fintype P] [AddCommGroup P]
    (φ φ' : P →+ (Fin m → ZMod q)) (g : Fin m → Finset (ZMod q))
    (_hg : ∀ r, (g r).Nonempty) (β : ℚ) (_hβ : 0 ≤ β)
    (hbad : ∀ r, ((q : ℚ) - (g r).card) ≤ β * (g r).card) :
    |(∑ a : P, ((if φ a ∈ Fintype.piFinset g then (1 : ℚ) else 0) - ∏ r, ((g r).card : ℚ) / q) *
        ((if φ' a ∈ Fintype.piFinset g then (1 : ℚ) else 0) - ∏ r, ((g r).card : ℚ) / q))
        / Fintype.card P|
      ≤ (∏ r, ((g r).card : ℚ) / q) ^ 2 *
        ∑ ξ ∈ univ.erase (0 : Fin m → ZMod q), ∑ ξ' ∈ univ.erase (0 : Fin m → ZMod q),
          if (∀ a, ξ ⬝ᵥ φ a + ξ' ⬝ᵥ φ' a = 0) then
            β ^ ((univ.filter fun r => ξ r ≠ 0).card + (univ.filter fun r => ξ' r ≠ 0).card)
          else 0 := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar with hψ
  set E : Finset (Fin m → ZMod q) := univ.erase 0 with hE
  set μR : ℝ := ∏ r, ((g r).card : ℝ) / q with hμR
  set X : ℚ := (∑ a : P, ((if φ a ∈ Fintype.piFinset g then (1 : ℚ) else 0) -
      ∏ r, ((g r).card : ℚ) / q) * ((if φ' a ∈ Fintype.piFinset g then (1 : ℚ) else 0) -
      ∏ r, ((g r).card : ℚ) / q)) / Fintype.card P with hX
  have hP : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- the additive map whose triviality is tested
  let χ : (Fin m → ZMod q) → (Fin m → ZMod q) → P →+ ZMod q := fun ξ ξ' =>
    AddMonoidHom.mk' (fun a => ξ ⬝ᵥ φ a + ξ' ⬝ᵥ φ' a) (by
      intro a b
      simp only [map_add, dotProduct_add]
      abel)
  -- Fourier expansion of `X`
  have hXC : (X : ℂ) = ∑ ξ ∈ E, ∑ ξ' ∈ E,
      if (∀ a, ξ ⬝ᵥ φ a + ξ' ⬝ᵥ φ' a = 0) then Gh g ξ * Gh g ξ' else 0 := by
    rw [hX, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
    simp_rw [Rat.cast_mul, ind_sub_eq]
    rw [div_eq_iff hP]
    have h1 : ∀ a : P, (∑ ξ ∈ E, Gh g ξ * ψ (ξ ⬝ᵥ φ a)) * (∑ ξ' ∈ E, Gh g ξ' * ψ (ξ' ⬝ᵥ φ' a))
        = ∑ ξ ∈ E, ∑ ξ' ∈ E, Gh g ξ * Gh g ξ' * ψ (χ ξ ξ' a) := by
      intro a
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun ξ' _ => ?_
      change _ = _ * ψ (ξ ⬝ᵥ φ a + ξ' ⬝ᵥ φ' a)
      rw [AddChar.map_add_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ξ' _ => ?_
    rw [← Finset.mul_sum, sum_char_hom (χ ξ ξ')]
    change _ * (if (∀ a, ξ ⬝ᵥ φ a + ξ' ⬝ᵥ φ' a = 0) then _ else _) = _
    split_ifs <;> ring
  -- bound
  have hbadR : ∀ r, (q : ℝ) - (g r).card ≤ (β : ℝ) * (g r).card := by
    intro r
    exact_mod_cast hbad r
  have hnorm : ‖(X : ℂ)‖ ≤ ∑ ξ ∈ E, ∑ ξ' ∈ E,
      if (∀ a, ξ ⬝ᵥ φ a + ξ' ⬝ᵥ φ' a = 0) then
        μR ^ 2 * (β : ℝ) ^ ((univ.filter fun r => ξ r ≠ 0).card +
          (univ.filter fun r => ξ' r ≠ 0).card)
      else 0 := by
    rw [hXC]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ' _ => ?_)
    split_ifs
    · rw [norm_mul, pow_add]
      have h1 := Gh_norm g (β : ℝ) hbadR ξ
      have h2 := Gh_norm g (β : ℝ) hbadR ξ'
      calc ‖Gh g ξ‖ * ‖Gh g ξ'‖
          ≤ (μR * (β : ℝ) ^ (univ.filter fun r => ξ r ≠ 0).card) *
            (μR * (β : ℝ) ^ (univ.filter fun r => ξ' r ≠ 0).card) :=
            mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = _ := by ring
    · simp
  have habs : ((|X| : ℚ) : ℝ) = ‖(X : ℂ)‖ := by
    rw [Rat.cast_abs, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hfinal : ((|X| : ℚ) : ℝ) ≤ (((∏ r, ((g r).card : ℚ) / q) ^ 2 *
        ∑ ξ ∈ E, ∑ ξ' ∈ E,
          if (∀ a, ξ ⬝ᵥ φ a + ξ' ⬝ᵥ φ' a = 0) then
            β ^ ((univ.filter fun r => ξ r ≠ 0).card + (univ.filter fun r => ξ' r ≠ 0).card)
          else 0 : ℚ) : ℝ) := by
    rw [habs]
    refine hnorm.trans (le_of_eq ?_)
    rw [Rat.cast_mul, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ' _ => ?_
    split_ifs
    · push_cast
      rfl
    · simp
  exact_mod_cast hfinal

end AltR0

end FourierPart

section AltR0Part

/-!
# alt-r0: the r₀ pass probability barely depends on the kept tail

In alt-r0 the tail `t = (y_j)_{j ≠ h₀}` of the nonce is kept while only `y_{h₀}` is resampled, so
what matters is `ρ(t) = Pr_{y_{h₀}}[A·y passes the r₀ check]` for each fixed `t`. This file bounds
`E_A E_t (ρ(t) - μ)²`.

* `Slots`: for a pair of nonces sharing the tail, the degenerate NTT slots are those where the head
  difference or the whole tail vanishes (`degS_sub`), and `d` of them occur with probability at most
  `C(n,d) · (1/w + (2γ₁)^{-(L-1)})^d` (`deg_card_prob_tail`).
-/

open Finset

noncomputable section

namespace AltR0
open RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n L : ℕ}

/-! ## Nonces with a fixed tail -/

/-- NTT of a single polynomial. -/
def nttP (ζ : Fin n → ZMod q) (f : Fin n → ZMod q) (k : Fin n) : ZMod q :=
  ∑ s : Fin n, ζ k ^ (s : ℕ) * f s

/-- The head box: coefficient `s` ranges over `[lo s, lo s + w)`. -/
def hbox (lo : Fin n → ℤ) (w : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun s => Finset.Ico (lo s) (lo s + w)

/-- The tail box: the head block is `0`, the other blocks range over the usual box. -/
def tbox (γ₁ : ℕ) (h₀ : Fin L) : Finset (Fin L → Fin n → ℤ) :=
  Fintype.piFinset fun j => if j = h₀ then {0} else box γ₁ n

/-- The nonce with head `y₁` and tail `t`. -/
def join (h₀ : Fin L) (y₁ : Fin n → ℤ) (t : Fin L → Fin n → ℤ) : Fin (L * n) → ℤ :=
  fun c => if (finProdFinEquiv.symm c).1 = h₀ then y₁ (finProdFinEquiv.symm c).2
    else t (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2

lemma blk_join (h₀ : Fin L) (y₁ : Fin n → ℤ) (t : Fin L → Fin n → ℤ) (j : Fin L) :
    blk (zc (q := q) (join h₀ y₁ t)) j
      = if j = h₀ then (fun s => (y₁ s : ZMod q)) else (fun s => (t j s : ZMod q)) := by
  funext s
  simp only [blk, zc, join, Equiv.symm_apply_apply]
  split_ifs <;> rfl

lemma ntt_join (ζ : Fin n → ZMod q) (h₀ : Fin L) (y₁ : Fin n → ℤ) (t : Fin L → Fin n → ℤ)
    (j : Fin L) (k : Fin n) :
    ntt ζ (zc (q := q) (join h₀ y₁ t)) j k
      = if j = h₀ then nttP ζ (fun s => (y₁ s : ZMod q)) k
        else nttP ζ (fun s => (t j s : ZMod q)) k := by
  unfold ntt
  rw [blk_join]
  split_ifs <;> rfl

lemma nttP_sub (ζ : Fin n → ZMod q) (f g : Fin n → ZMod q) (k : Fin n) :
    nttP ζ (f - g) k = nttP ζ f k - nttP ζ g k := by
  simp only [nttP, Pi.sub_apply, mul_sub, sum_sub_distrib]

/-- **Degenerate slots of a pair sharing the tail.** At a degenerate slot either the heads have
the same NTT value, or every tail polynomial vanishes. -/
lemma degS_sub (ζ : Fin n → ZMod q) (h₀ : Fin L) (y₁ y₁' : Fin n → ℤ) (t : Fin L → Fin n → ℤ)
    (k : Fin n) (hk : k ∈ degS ζ (join h₀ y₁ t) (join h₀ y₁' t)) :
    nttP ζ (fun s => ((y₁ s - y₁' s : ℤ) : ZMod q)) k = 0
      ∨ ∀ j, j ≠ h₀ → nttP ζ (fun s => (t j s : ZMod q)) k = 0 := by
  obtain ⟨c, c', hcc, hall⟩ := (Finset.mem_filter.mp hk).2
  by_cases ht : ∀ j, j ≠ h₀ → nttP ζ (fun s => (t j s : ZMod q)) k = 0
  · exact Or.inr ht
  · left
    push_neg at ht
    obtain ⟨j, hj, hne⟩ := ht
    have h1 := hall j
    rw [ntt_join, ntt_join, if_neg hj, if_neg hj, ← add_mul] at h1
    have hcc' : c' = -c := by
      have := (mul_eq_zero.mp h1).resolve_right hne
      linear_combination this
    have hc : c ≠ 0 := by
      rcases hcc with h | h
      · exact h
      · intro h0; exact h (by rw [hcc', h0, neg_zero])
    have h2 := hall h₀
    rw [ntt_join, ntt_join, if_pos rfl, if_pos rfl, hcc'] at h2
    have h3 : c * (nttP ζ (fun s => (y₁ s : ZMod q)) k - nttP ζ (fun s => (y₁' s : ZMod q)) k)
        = 0 := by linear_combination h2
    have h4 := (mul_eq_zero.mp h3).resolve_left hc
    rw [← nttP_sub] at h4
    convert h4 using 2
    funext s; push_cast; rfl

/-! ## Counting vanishing NTT values -/

lemma int_eq_of_cast_Ico {lo : ℤ} {w : ℕ} (hw : w ≤ q) {a b : ℤ}
    (ha : a ∈ Finset.Ico lo (lo + w)) (hb : b ∈ Finset.Ico lo (lo + w))
    (h : (a : ZMod q) = (b : ZMod q)) : a = b := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mp h
  rw [Finset.mem_Ico] at ha hb
  have hq : (w : ℤ) ≤ q := by exact_mod_cast hw
  have h0 : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  omega

/-- Two polynomials in a box of width `w ≤ q` that agree from position `r` on and whose
difference has vanishing NTT at `r` slots are equal. -/
lemma win_inj_P {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw : w ≤ q) (S : Finset (Fin n)) {f g : Fin n → ℤ} (hf : f ∈ hbox lo w)
    (hg : g ∈ hbox lo w) (hout : ∀ s : Fin n, S.card ≤ (s : ℕ) → f s = g s)
    (hntt : ∀ k ∈ S, nttP ζ (fun s => ((f s - g s : ℤ) : ZMod q)) k = 0) : f = g := by
  have hrn : S.card ≤ n := by simpa using Finset.card_le_univ S
  funext s₀
  by_cases hs : (s₀ : ℕ) < S.card
  · set cf : ℕ → ZMod q := fun t => if h : t < n then (((f ⟨t, h⟩ - g ⟨t, h⟩ : ℤ)) : ZMod q)
      else 0 with hcf
    have hw' : ∀ k ∈ S, ∑ t ∈ range S.card, cf t * ζ k ^ t = 0 := by
      intro k hk
      have h1 := hntt k hk
      unfold nttP at h1
      rw [Finset.sum_subset (Finset.range_subset_range.mpr hrn), ← Fin.sum_univ_eq_sum_range
        (fun i => cf i * ζ k ^ i) n, ← h1]
      · refine Finset.sum_congr rfl fun t _ => ?_
        simp only [hcf, dif_pos t.2, Fin.eta]
        ring
      · intro i hi hni
        rw [Finset.mem_range] at hi hni
        simp only [hcf, dif_pos hi]
        rw [hout ⟨i, hi⟩ (by simp; omega), sub_self]; simp
    have h0 := window ζ hζ cf S.card S le_rfl hw' s₀ hs
    simp only [hcf, dif_pos s₀.2, Fin.eta] at h0
    push_cast at h0
    exact int_eq_of_cast_Ico hw (Fintype.mem_piFinset.mp hf s₀) (Fintype.mem_piFinset.mp hg s₀)
      (sub_eq_zero.mp h0)
  · exact hout s₀ (by omega)

lemma card_hbox (lo : Fin n → ℤ) (w : ℕ) : (hbox lo w).card = w ^ n := by
  rw [hbox, Fintype.card_piFinset]
  simp

/-- For fixed `g`, at most `w^(n - |S|)` polynomials `f` in the box have `f - g` with vanishing
NTT on `S`. -/
lemma card_sol_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw : w ≤ q) (S : Finset (Fin n)) (g : Fin n → ℤ) (hg : g ∈ hbox lo w) :
    ((hbox lo w).filter fun f => ∀ k ∈ S, nttP ζ (fun s => ((f s - g s : ℤ) : ZMod q)) k = 0).card
      ≤ w ^ (n - S.card) := by
  set sol := (hbox lo w).filter fun f =>
    ∀ k ∈ S, nttP ζ (fun s => ((f s - g s : ℤ) : ZMod q)) k = 0
  set tgt : Finset ({s : Fin n // S.card ≤ (s : ℕ)} → ℤ) :=
    Fintype.piFinset fun s => Finset.Ico (lo s) (lo s + w)
  have hinj : Set.InjOn (fun f (s : {s : Fin n // S.card ≤ (s : ℕ)}) => f s.1)
      (sol : Set (Fin n → ℤ)) := by
    intro f hf f' hf' he
    have hf1 := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
    have hf2 := Finset.mem_filter.mp (Finset.mem_coe.mp hf')
    refine win_inj_P hζ hw S hf1.1 hf2.1 (fun s hs => congrFun he ⟨s, hs⟩) fun k hk => ?_
    have e1 := hf1.2 k hk
    have e2 := hf2.2 k hk
    have : (fun s => ((f s - f' s : ℤ) : ZMod q))
        = (fun s => ((f s - g s : ℤ) : ZMod q)) - (fun s => ((f' s - g s : ℤ) : ZMod q)) := by
      funext s; simp only [Pi.sub_apply]; push_cast; ring
    rw [this, nttP_sub, e1, e2, sub_zero]
  have hmaps : ∀ f ∈ sol, (fun (s : {s : Fin n // S.card ≤ (s : ℕ)}) => f s.1) ∈ tgt := by
    intro f hf
    exact Fintype.mem_piFinset.mpr fun s =>
      Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 s.1
  refine (Finset.card_le_card_of_injOn _ hmaps hinj).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  simp only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast, prod_const, card_univ]
  congr 1
  rw [Fintype.card_subtype]
  have : (univ.filter fun s : Fin n => S.card ≤ (s : ℕ)) = univ.filter fun s : Fin n =>
      ¬ (s : ℕ) < S.card := by ext s; simp
  rw [this, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), card_univ,
    Fintype.card_fin]
  congr 1
  rw [Fin.card_filter_val_lt]
  have hrn : S.card ≤ n := by simpa using Finset.card_le_univ S
  omega

/-! ## The probability of `d` degenerate slots -/

lemma box_eq_hbox (γ₁ : ℕ) : RejOrder.box γ₁ n = hbox (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁) := by
  unfold RejOrder.box hbox
  congr 1; funext s; ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; push_cast; omega

lemma zero_mem_box {γ₁ : ℕ} (hγ1 : 0 < γ₁) : (0 : Fin n → ℤ) ∈ RejOrder.box γ₁ n := by
  unfold RejOrder.box
  exact Fintype.mem_piFinset.mpr fun _ => by simp; omega

/-- Head pairs whose difference has vanishing NTT on `S`. -/
lemma card_head_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw : w ≤ q) (S : Finset (Fin n)) :
    ((hbox lo w ×ˢ hbox lo w).filter fun ff =>
        ∀ k ∈ S, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0).card
      ≤ w ^ n * w ^ (n - S.card) := by
  rw [Finset.card_filter, Finset.sum_product_right]
  calc ∑ g ∈ hbox lo w, ∑ f ∈ hbox lo w,
        (if ∀ k ∈ S, nttP ζ (fun s => (((f, g).1 s - (f, g).2 s : ℤ) : ZMod q)) k = 0
          then 1 else 0)
      = ∑ g ∈ hbox lo w, ((hbox lo w).filter fun f =>
          ∀ k ∈ S, nttP ζ (fun s => ((f s - g s : ℤ) : ZMod q)) k = 0).card := by
        refine sum_congr rfl fun g _ => ?_
        rw [Finset.card_filter]
    _ ≤ ∑ _g ∈ hbox lo w, w ^ (n - S.card) := sum_le_sum fun g hg => card_sol_le hζ hw S g hg
    _ = w ^ n * w ^ (n - S.card) := by rw [sum_const, card_hbox, smul_eq_mul]

/-- Tails whose polynomials all have vanishing NTT on `E`. -/
lemma card_tail_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {γ₁ : ℕ} (hγ1 : 0 < γ₁)
    (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L) (E : Finset (Fin n)) :
    ((tbox γ₁ h₀).filter fun t => ∀ j, j ≠ h₀ → ∀ k ∈ E, nttP ζ (fun s => (t j s : ZMod q)) k = 0).card
      ≤ ((2 * γ₁) ^ (n - E.card)) ^ (L - 1) := by
  set sol1 := (RejOrder.box γ₁ n).filter fun f => ∀ k ∈ E, nttP ζ (fun s => (f s : ZMod q)) k = 0
  have h1 : sol1.card ≤ (2 * γ₁) ^ (n - E.card) := by
    have := card_sol_le (lo := fun _ => -(γ₁ : ℤ) + 1) hζ hγ E 0
      (by rw [← box_eq_hbox]; exact zero_mem_box hγ1)
    rw [← box_eq_hbox] at this
    convert this using 3
    simp
  have heq : ((tbox γ₁ h₀).filter fun t => ∀ j, j ≠ h₀ → ∀ k ∈ E,
      nttP ζ (fun s => (t j s : ZMod q)) k = 0)
      = Fintype.piFinset fun j => if j = h₀ then {0} else sol1 := by
    ext t
    simp only [tbox, Finset.mem_filter, Fintype.mem_piFinset, sol1]
    constructor
    · rintro ⟨h1, h2⟩ j
      have := h1 j
      split_ifs at this ⊢ with hj
      · exact this
      · exact Finset.mem_filter.mpr ⟨this, h2 j hj⟩
    · intro h
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · have := h j; split_ifs at this ⊢ with hj
        · exact this
        · exact (Finset.mem_filter.mp this).1
      · have := h j; rw [if_neg hj] at this; exact (Finset.mem_filter.mp this).2
  rw [heq, Fintype.card_piFinset]
  calc ∏ j, (if j = h₀ then ({0} : Finset (Fin n → ℤ)) else sol1).card
      ≤ ∏ j : Fin L, (if j = h₀ then 1 else (2 * γ₁) ^ (n - E.card)) := by
        refine Finset.prod_le_prod' fun j _ => ?_
        split_ifs
        · simp
        · exact h1
    _ = ((2 * γ₁) ^ (n - E.card)) ^ (L - 1) := by
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
        congr 1
        rw [Finset.filter_ne' univ h₀, Finset.card_erase_of_mem (Finset.mem_univ _), card_univ,
          Fintype.card_fin]

lemma card_tbox {γ₁ : ℕ} (h₀ : Fin L) : (tbox (n := n) γ₁ h₀).card = ((2 * γ₁) ^ n) ^ (L - 1) := by
  rw [tbox, Fintype.card_piFinset]
  have : ∀ j, (if j = h₀ then ({0} : Finset (Fin n → ℤ)) else RejOrder.box γ₁ n).card
      = if j = h₀ then 1 else (2 * γ₁) ^ n := by
    intro j; split_ifs
    · simp
    · exact card_box_nat γ₁ n
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    Finset.filter_ne' univ h₀, Finset.card_erase_of_mem (Finset.mem_univ _), card_univ,
    Fintype.card_fin]

/-- The triples `(y₁, y₁', t)`: two heads and a common tail. -/
def trip (lo : Fin n → ℤ) (w γ₁ : ℕ) (h₀ : Fin L) :
    Finset (((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ)) :=
  (hbox lo w ×ˢ hbox lo w) ×ˢ tbox γ₁ h₀

/-- **A given set of slots is degenerate** with probability at most `p^|Z|`,
`p = 1/w + (2γ₁)^{-(L-1)}`. -/
lemma prob_Z {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw0 : 0 < w) (hw : w ≤ q) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L)
    (Z : Finset (Fin n)) :
    prob (trip lo w γ₁ h₀) (fun x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2))
      ≤ (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ Z.card := by
  set A : Finset (Fin n) → Finset ((Fin n → ℤ) × (Fin n → ℤ)) := fun D =>
    (hbox lo w ×ˢ hbox lo w).filter fun ff =>
      ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0
  set B : Finset (Fin n) → Finset (Fin L → Fin n → ℤ) := fun E =>
    (tbox γ₁ h₀).filter fun t => ∀ j, j ≠ h₀ → ∀ k ∈ E, nttP ζ (fun s => (t j s : ZMod q)) k = 0
  have hsub : (trip lo w γ₁ h₀).filter (fun x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2))
      ⊆ Z.powerset.biUnion fun D => A D ×ˢ B (Z \ D) := by
    intro x hx
    obtain ⟨hxm, hZ⟩ := Finset.mem_filter.mp hx
    obtain ⟨hff, ht⟩ := Finset.mem_product.mp hxm
    set D := Z.filter fun k => nttP ζ (fun s => ((x.1.1 s - x.1.2 s : ℤ) : ZMod q)) k = 0
    refine Finset.mem_biUnion.mpr ⟨D, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hff, fun k hk =>
      (Finset.mem_filter.mp hk).2⟩, Finset.mem_filter.mpr ⟨ht, fun j hj k hk => ?_⟩⟩
    obtain ⟨hkZ, hkD⟩ := Finset.mem_sdiff.mp hk
    rcases degS_sub ζ h₀ x.1.1 x.1.2 x.2 k (hZ hkZ) with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨hkZ, h⟩) hkD
    · exact h j hj
  have hw' : (0 : ℚ) < w := by exact_mod_cast hw0
  have hg' : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hcard : ((trip lo w γ₁ h₀).card : ℚ)
      = (w : ℚ) ^ n * (w : ℚ) ^ n * (((2 * γ₁ : ℚ)) ^ n) ^ (L - 1) := by
    rw [trip, card_product, card_product, card_hbox, card_tbox]; push_cast; ring
  unfold prob
  rw [div_le_iff₀ (by rw [hcard]; positivity)]
  have hcount := Finset.card_le_card hsub
  refine (Nat.cast_le.mpr (hcount.trans card_biUnion_le)).trans ?_
  push_cast
  have hprod : (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ Z.card
      = ∑ D ∈ Z.powerset, (1 / (w : ℚ)) ^ D.card * (1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ (Z \ D).card := by
    rw [← Finset.prod_const, Finset.prod_add]
    simp only [prod_const]
  rw [hprod, Finset.sum_mul]
  refine Finset.sum_le_sum fun D hD => ?_
  have hDZ : D ⊆ Z := Finset.mem_powerset.mp hD
  have hDn : D.card ≤ n := by simpa using Finset.card_le_univ D
  have hEn : (Z \ D).card ≤ n := by simpa using Finset.card_le_univ (Z \ D)
  rw [card_product]
  push_cast
  have ha : ((A D).card : ℚ) ≤ (w : ℚ) ^ n * (w : ℚ) ^ (n - D.card) := by
    exact_mod_cast card_head_le hζ hw D
  have hb : ((B (Z \ D)).card : ℚ) ≤ (((2 * γ₁ : ℚ)) ^ (n - (Z \ D).card)) ^ (L - 1) := by
    exact_mod_cast card_tail_le hζ hγ1 hγ h₀ (Z \ D)
  refine (mul_le_mul ha hb (by positivity) (by positivity)).trans (le_of_eq ?_)
  rw [hcard, pow_sub₀ _ hw'.ne' hDn, pow_sub₀ _ hg'.ne' hEn]
  have hwne : (w : ℚ) ≠ 0 := hw'.ne'
  have hgne : (2 * γ₁ : ℚ) ≠ 0 := hg'.ne'
  simp only [div_eq_mul_inv, one_mul, inv_pow, mul_pow, ← pow_mul]
  field_simp
  ring

/-- **`d` degenerate slots** occur with probability at most `C(n,d) · p^d`. -/
lemma prob_deg_ge {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw0 : 0 < w) (hw : w ≤ q) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L) (d : ℕ) :
    prob (trip lo w γ₁ h₀) (fun x => d ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card)
      ≤ n.choose d * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ d := by
  refine (prob_le_sum _ ((univ : Finset (Fin n)).powersetCard d) _
    (fun Z x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)) fun x _ hx => ?_).trans ?_
  · obtain ⟨Z, hZ, hc⟩ := Finset.exists_subset_card_eq hx
    exact ⟨Z, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩, hZ⟩
  · refine (Finset.sum_le_sum fun Z hZ => prob_Z hζ hw0 hw hγ1 hγ h₀ Z).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun Z hZ => by rw [(Finset.mem_powersetCard.mp hZ).2], sum_const,
      Finset.card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## Weighted count of test vectors supported on few slots -/

section Weights
variable {K : ℕ}

/-- Coefficient support of a test vector. -/
def supp (ξ : Fin (K * n) → ZMod q) : Finset (Fin (K * n)) := univ.filter fun r => ξ r ≠ 0

/-- All dual coordinates outside the slot set `S` vanish. -/
def DualIn (ζ : Fin n → ZMod q) (S : Finset (Fin n)) (ξ : Fin (K * n) → ZMod q) : Prop :=
  ∀ i k, k ∉ S → dual ζ ξ i k = 0

instance (ζ : Fin n → ZMod q) (S : Finset (Fin n)) : DecidablePred (DualIn (K := K) ζ S) :=
  fun ξ => by unfold DualIn; infer_instance

lemma ext_restrict (ξ : Fin (K * n) → ZMod q) (T : Finset (Fin (K * n))) (h : supp ξ ⊆ T) :
    ext T (fun r : T => ξ r) = ξ := by
  funext r
  unfold RejOrder.ext
  split_ifs with hr
  · rfl
  · by_contra hne
    exact hr (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hne⟩))

/-- Nonzero test vectors with support exactly `T ≠ ∅` and duals in `S` are at most
`|suppIn1 T S| - 1`. -/
lemma card_fiber_le (ζ : Fin n → ZMod q) (S : Finset (Fin n)) (T : Finset (Fin (K * n)))
    (hT : T.Nonempty) :
    ((univ : Finset (Fin (K * n) → ZMod q)).filter fun ξ => supp ξ = T ∧ DualIn ζ S ξ).card + 1
      ≤ (suppIn1 ζ T S).card := by
  set F := (univ : Finset (Fin (K * n) → ZMod q)).filter fun ξ => supp ξ = T ∧ DualIn ζ S ξ
  have hmaps : ∀ ξ ∈ F, (fun r : T => ξ r) ∈ (suppIn1 ζ T S).erase 0 := by
    intro ξ hξ
    obtain ⟨hs, hd⟩ := (Finset.mem_filter.mp hξ).2
    refine Finset.mem_erase.mpr ⟨fun h0 => ?_, (mem_suppIn1 T S _).mpr fun i k hk => ?_⟩
    · obtain ⟨r, hr⟩ := hT
      have := congrFun h0 ⟨r, hr⟩
      rw [← hs] at hr
      exact (Finset.mem_filter.mp hr).2 this
    · rw [ext_restrict ξ T hs.le]; exact hd i k hk
  have hinj : Set.InjOn (fun ξ (r : T) => ξ r) (F : Set (Fin (K * n) → ZMod q)) := by
    intro ξ hξ ξ' hξ' he
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hξ)).2.1
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hξ')).2.1
    rw [← ext_restrict ξ T h1.le, ← ext_restrict ξ' T h2.le]
    exact congrArg (RejOrder.ext T) he
  have h0 : (0 : T → ZMod q) ∈ suppIn1 ζ T S := by
    refine (mem_suppIn1 T S _).mpr fun i k _ => ?_
    have : RejOrder.ext T (0 : T → ZMod q) = 0 := by funext r; simp [RejOrder.ext]
    rw [this]; unfold dual; rw [show blk (0 : Fin (K * n) → ZMod q) i = 0 from rfl,
      Matrix.mulVec_zero]; rfl
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_erase_of_mem h0] at this
  have hpos : 0 < (suppIn1 ζ T S).card := Finset.card_pos.mpr ⟨0, h0⟩
  omega

lemma xg_le (σ : ℕ) (T : Finset (Fin (K * n))) : xg n K σ T ≤ K * σ := by
  unfold xg
  calc ∑ i : Fin K, min (rowT T i).card (σ - cgap n (rowT T i)) ≤ ∑ _i : Fin K, σ :=
        Finset.sum_le_sum fun i _ => (min_le_right _ _).trans (Nat.sub_le _ _)
    _ = K * σ := by simp

/-- **Weighted count.** `∑_{ξ ≠ 0, duals in S} β^wt(ξ) ≤ ∑_T β^|T| (q^xg − 1)`. -/
lemma wsum_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (hζ0 : ∀ k, ζ k ≠ 0)
    {c : ZMod q} (hw : ∀ k, ζ k ^ n = c) (S : Finset (Fin n)) {β : ℚ} (hβ : 0 ≤ β) :
    ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then β ^ (supp ξ).card else 0)
      ≤ ∑ T ∈ (univ : Finset (Fin (K * n))).powerset,
          β ^ T.card * (((q : ℚ) ^ xg n K S.card T) - 1) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := supp) (t := (univ : Finset (Fin (K * n))).powerset)
    (fun ξ _ => Finset.mem_powerset.mpr (Finset.subset_univ _))]
  refine Finset.sum_le_sum fun T _ => ?_
  have hq1 : (1 : ℚ) ≤ (q : ℚ) ^ xg n K S.card T := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  rw [Finset.sum_filter]
  have heq : ∀ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
      (if supp ξ = T then (if DualIn ζ S ξ then β ^ (supp ξ).card else 0) else 0)
        = β ^ T.card * (if supp ξ = T ∧ DualIn ζ S ξ then 1 else 0) := by
    intro ξ _
    by_cases h1 : supp ξ = T <;> by_cases h2 : DualIn ζ S ξ <;> simp [h1, h2]
  rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, Finset.sum_boole]
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- support ∅ means ξ = 0, excluded
    have : ((univ : Finset (Fin (K * n) → ZMod q)).erase 0).filter
        (fun ξ => supp ξ = T ∧ DualIn ζ S ξ) = ∅ := by
      refine Finset.filter_false_of_mem fun ξ hξ h => ?_
      apply (Finset.mem_erase.mp hξ).1
      funext r
      by_contra hne
      have : r ∈ supp ξ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [h.1, hT] at this; exact absurd this (Finset.notMem_empty r)
    rw [this, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact mul_nonneg (pow_nonneg hβ _) (by linarith)
  · refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ _)
    have h1 := card_fiber_le ζ S T hT
    have h2 := card_suppIn1_le_xg hζ hζ0 hw T S
    have h3 : (((univ : Finset (Fin (K * n) → ZMod q)).erase 0).filter
        fun ξ => supp ξ = T ∧ DualIn ζ S ξ).card
        ≤ ((univ : Finset (Fin (K * n) → ZMod q)).filter
          fun ξ => supp ξ = T ∧ DualIn ζ S ξ).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
    have : ((((univ : Finset (Fin (K * n) → ZMod q)).erase 0).filter
        fun ξ => supp ξ = T ∧ DualIn ζ S ξ).card : ℚ) + 1 ≤ (q : ℚ) ^ xg n K S.card T := by
      exact_mod_cast (by omega : _ + 1 ≤ q ^ xg n K S.card T)
    linarith

end Weights

/-! ## The second moment of `ρ(t)` over the matrix -/

section Main
open Matrix
variable {K : ℕ}

/-- Values of one coordinate of `w` that pass the r₀ check. -/
def good (γ₂ β : ℕ) (v : Fin (K * n) → ℤ) (r : Fin (K * n)) : Finset (ZMod q) :=
  univ.filter fun x => ¬ ((γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v r|)

lemma card_good {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ}
    (hv : Bounded β v) (r : Fin (K * n)) :
    (good (q := q) γ₂ β v r).card = mb * (2 * (γ₂ - β) - 1) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod q)))
    (fun x => (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v r|)
  rw [fail_card hp (v r) (hv r), Finset.card_univ, ZMod.card] at h1
  have := pass_le_q hp
  unfold good; omega

/-- `a ↦ A·y` as an additive map. -/
def phiHom {ζ : Fin n → ZMod q} {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    (h : IsNTTMul ζ mulmat) (y : Fin (L * n) → ZMod q) :
    (Fin K → Fin L → Fin n → ZMod q) →+ (Fin (K * n) → ZMod q) where
  toFun a := modMat mulmat a *ᵥ y
  map_zero' := by
    have h0 := modMat_add (K := K) (L := L) mulmat h.add 0 0
    rw [add_zero] at h0
    have : modMat (K := K) (L := L) mulmat 0 = 0 := by
      have := congrArg (· - modMat (K := K) (L := L) mulmat 0) h0
      simpa using this.symm
    rw [this, Matrix.zero_mulVec]
  map_add' a b := by
    rw [modMat_add mulmat h.add, Matrix.add_mulVec]

/-- An orthogonal pair of test vectors has its dual coordinates on the degenerate slots. -/
lemma dualIn_of_orth {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (y y' : Fin (L * n) → ℤ) (ξ ξ' : Fin (K * n) → ZMod q)
    (horth : ∀ a, ξ ⬝ᵥ phiHom h (zc y) a + ξ' ⬝ᵥ phiHom h (zc y') a = 0) :
    DualIn ζ (degS ζ y y') ξ ∧ DualIn ζ (degS ζ y y') ξ' := by
  have hs := slot_of_orth h ξ ξ' (zc y) (zc y') (fun a => by
    have := horth a
    simp only [dotProduct, phiHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact this)
  have key : ∀ i k, k ∉ degS ζ y y' → dual ζ ξ i k = 0 ∧ dual ζ ξ' i k = 0 := by
    intro i k hk
    by_contra hne
    apply hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, dual ζ ξ i k, dual ζ ξ' i k, ?_,
      fun j => hs i j k⟩
    by_contra h2; push Not at h2; exact hne h2
  exact ⟨fun i k hk => (key i k hk).1, fun i k hk => (key i k hk).2⟩

/-- The empty slot set admits no nonzero test vector. -/
lemma dualIn_empty {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (ξ : Fin (K * n) → ZMod q)
    (h : DualIn ζ ∅ ξ) : ξ = 0 :=
  eq_zero_of_dual hζ ξ fun i => funext fun k => h i k (Finset.notMem_empty k)

/-- `(Pr_B[P] - μ)² = E_{b,b'} (1_P b - μ)(1_P b' - μ)`. -/
lemma sq_prob {α : Type*} (B : Finset α) (hB : B.Nonempty) (P : α → Prop) [DecidablePred P]
    (μ : ℚ) :
    (prob B P - μ) ^ 2 = (∑ b ∈ B, ∑ b' ∈ B, ((if P b then (1 : ℚ) else 0) - μ) *
      ((if P b' then (1 : ℚ) else 0) - μ)) / (B.card : ℚ) ^ 2 := by
  have hc : (B.card : ℚ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have : prob B P - μ = (∑ b ∈ B, ((if P b then (1 : ℚ) else 0) - μ)) / B.card := by
    unfold prob
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [this, div_pow, sq, Finset.sum_mul_sum]

/-- Probability over the head that `A·(y₁, t)` passes the r₀ check. -/
def rhoC (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ β : ℕ)
    (v : Fin (K * n) → ℤ) (lo : Fin n → ℤ) (w : ℕ) (h₀ : Fin L)
    (a : Fin K → Fin L → Fin n → ZMod q) (t : Fin L → Fin n → ℤ) : ℚ :=
  prob (hbox lo w) fun y₁ => modMat mulmat a *ᵥ zc (join h₀ y₁ t) ∈ Fintype.piFinset (good γ₂ β v)

/-- **Second moment over the matrix.** For `a` uniform, `t` uniform on the tail box,
`E (ρ_c(t) - μ)²` is at most `μ² ∑_{d ≤ d_m} C(n,d) p^d E_b(d)² + C(n, d_m+1) p^(d_m+1)`, where
`E_b(d)` bounds the β-weighted number of test vectors on `d` slots. -/
theorem var_le {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {γ₁ γ₂ β : ℕ} {v : Fin (K * n) → ℤ} {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) (hwq : w ≤ q)
    (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L)
    (bt : ℚ) (hbt : 0 ≤ bt)
    (hbad : ∀ r, ((q : ℚ) - (good (q := q) γ₂ β v r).card) ≤ bt * (good (q := q) γ₂ β v r).card)
    (dm : ℕ) (Eb : ℕ → ℚ)
    (hEb : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then bt ^ (supp ξ).card else 0) ≤ Eb S.card) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2) / (tbox (n := n) γ₁ h₀).card)
      ≤ (∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2 *
          ∑ d ∈ Icc 1 dm, (n.choose d * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ d)
            * Eb d ^ 2
        + n.choose (dm + 1) * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ (dm + 1) := by
  set μ : ℚ := ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q with hμ
  have hμ0 : 0 ≤ μ := Finset.prod_nonneg fun r _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hμ1 : μ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun r _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      fun r _ => ?_
    have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    rw [div_le_one hq]
    exact_mod_cast (Finset.card_le_univ _).trans (by rw [ZMod.card])
  have hHB : (hbox lo w).Nonempty := by
    rw [← Finset.card_pos, card_hbox]; positivity
  have hTB : (tbox (n := n) γ₁ h₀).Nonempty := by
    rw [← Finset.card_pos, card_tbox]; positivity
  -- the covariance of one triple
  set X : (Fin K → Fin L → Fin n → ZMod q) → (((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ))
      → ℚ := fun a x =>
    ((if phiHom h (zc (join h₀ x.1.1 x.2)) a ∈ Fintype.piFinset (good (q := q) γ₂ β v)
      then (1 : ℚ) else 0) - μ) *
    ((if phiHom h (zc (join h₀ x.1.2 x.2)) a ∈ Fintype.piFinset (good (q := q) γ₂ β v)
      then (1 : ℚ) else 0) - μ) with hX
  set D : (((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ)) → ℕ := fun x =>
    (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
  set Hf : ℕ → ℚ := fun d => ∑ e ∈ Icc 1 dm, (if e ≤ d then μ ^ 2 * Eb e ^ 2 else 0)
    + (if dm + 1 ≤ d then 1 else 0)
  have hgne : ∀ r, (good (q := q) γ₂ β v r).Nonempty := by
    intro r
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have := hbad r
    rw [hne, Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero] at this
    have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    linarith
  have hX1 : ∀ a x, X a x ≤ 1 := by
    intro a x
    simp only [hX]
    have hb : ∀ P : Prop, [Decidable P] → |(if P then (1 : ℚ) else 0) - μ| ≤ 1 := by
      intro P _; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    calc _ ≤ |_ * _| := le_abs_self _
      _ = _ := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hb _) (hb _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hcov : ∀ x, (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ Hf (D x) := by
    intro x
    set Ew : ℚ := ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
      (if DualIn ζ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)) ξ then bt ^ (supp ξ).card
        else 0) with hEw
    have hEw0 : 0 ≤ Ew := Finset.sum_nonneg fun ξ _ => by split_ifs <;> positivity
    have hc := cov_le (phiHom h (zc (join h₀ x.1.1 x.2))) (phiHom h (zc (join h₀ x.1.2 x.2)))
      (good (q := q) γ₂ β v) hgne bt hbt hbad
    have hpair : (∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        ∑ ξ' ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
          if (∀ a, ξ ⬝ᵥ phiHom h (zc (join h₀ x.1.1 x.2)) a
              + ξ' ⬝ᵥ phiHom h (zc (join h₀ x.1.2 x.2)) a = 0) then
            bt ^ ((univ.filter fun r => ξ r ≠ 0).card + (univ.filter fun r => ξ' r ≠ 0).card)
          else 0) ≤ Ew ^ 2 := by
      rw [sq, hEw, Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun ξ _ => Finset.sum_le_sum fun ξ' _ => ?_
      split_ifs with ho h1 h2 h2 h1 h2 h2
      · rw [pow_add]; rfl
      · exact absurd (dualIn_of_orth h _ _ ξ ξ' ho).2 h2
      · exact absurd (dualIn_of_orth h _ _ ξ ξ' ho).1 h1
      · exact absurd (dualIn_of_orth h _ _ ξ ξ' ho).1 h1
      all_goals first | positivity | simp
    have hmain : (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ μ ^ 2 * Ew ^ 2 :=
      (le_abs_self _).trans (hc.trans (mul_le_mul_of_nonneg_left hpair (sq_nonneg _)))
    have hHf0 : ∀ d, 0 ≤ ∑ e ∈ Icc 1 dm, (if e ≤ d then μ ^ 2 * Eb e ^ 2 else 0) :=
      fun d => Finset.sum_nonneg fun e _ => by split_ifs <;> positivity
    rcases Nat.eq_zero_or_pos (D x) with hD | hD
    · -- no degenerate slot: no test vector
      have : Ew = 0 := by
        refine Finset.sum_eq_zero fun ξ hξ => ?_
        rw [if_neg]
        intro hd
        have hS : degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) = ∅ :=
          Finset.card_eq_zero.mp hD
        rw [hS] at hd
        exact (Finset.mem_erase.mp hξ).1 (dualIn_empty h.inj ξ hd)
      rw [this] at hmain
      refine hmain.trans ?_
      simp only [Hf]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero]
      linarith [hHf0 (D x), (show (0:ℚ) ≤ if dm + 1 ≤ D x then 1 else 0 by split_ifs <;> norm_num)]
    · by_cases hdm : D x ≤ dm
      · have hE := hEb _ hD hdm
        refine hmain.trans ?_
        have h1 : μ ^ 2 * Ew ^ 2 ≤ μ ^ 2 * Eb (D x) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hEw0 hE 2) (sq_nonneg _)
        refine h1.trans ?_
        simp only [Hf]
        have hmem : D x ∈ Icc 1 dm := Finset.mem_Icc.mpr ⟨hD, hdm⟩
        have := Finset.single_le_sum (f := fun e => if e ≤ D x then μ ^ 2 * Eb e ^ 2 else 0)
          (fun e _ => by split_ifs <;> positivity) hmem
        simp only [le_refl, if_true] at this
        linarith [(show (0:ℚ) ≤ if dm + 1 ≤ D x then 1 else 0 by split_ifs <;> norm_num)]
      · have hP : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
          exact_mod_cast Fintype.card_pos
        rw [div_le_iff₀ hP]
        calc ∑ a, X a x ≤ ∑ _a : Fin K → Fin L → Fin n → ZMod q, (1 : ℚ) :=
              Finset.sum_le_sum fun a _ => hX1 a x
          _ = 1 * Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by simp
          _ ≤ Hf (D x) * Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
              refine mul_le_mul_of_nonneg_right ?_ hP.le
              simp only [Hf, if_pos (by omega : dm + 1 ≤ D x)]
              linarith [hHf0 (D x)]
  have hHBc : (0 : ℚ) < (hbox lo w).card := by exact_mod_cast hHB.card_pos
  have hTBc : (0 : ℚ) < (tbox (n := n) γ₁ h₀).card := by exact_mod_cast hTB.card_pos
  have htrip : ((trip lo w γ₁ h₀).card : ℚ)
      = (hbox lo w).card * (hbox lo w).card * (tbox (n := n) γ₁ h₀).card := by
    rw [trip, card_product, card_product]; push_cast; ring
  have htripc : (0 : ℚ) < (trip lo w γ₁ h₀).card := by rw [htrip]; positivity
  have hPc : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
    exact_mod_cast Fintype.card_pos
  -- rewrite the inner average as an average over triples
  have hsumtrip : ∀ a, ∑ x ∈ trip lo w γ₁ h₀, X a x
      = ∑ t ∈ tbox γ₁ h₀, ∑ y₁ ∈ hbox lo w, ∑ y₁' ∈ hbox lo w, X a ((y₁, y₁'), t) := by
    intro a
    rw [trip, Finset.sum_product_right]
    simp_rw [Finset.sum_product]
  have step1 : ∀ a, (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2)
      / (tbox (n := n) γ₁ h₀).card = (∑ x ∈ trip lo w γ₁ h₀, X a x) / (trip lo w γ₁ h₀).card := by
    intro a
    have e1 : ∀ t, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2
        = (∑ y₁ ∈ hbox lo w, ∑ y₁' ∈ hbox lo w, X a ((y₁, y₁'), t)) / ((hbox lo w).card : ℚ) ^ 2 :=
      fun t => sq_prob (hbox lo w) hHB _ μ
    simp_rw [e1]
    rw [← Finset.sum_div, hsumtrip, htrip]
    field_simp
  have hprobs : ∀ e, ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card : ℚ))
      / (trip lo w γ₁ h₀).card ≤ n.choose e * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ e :=
    fun e => prob_deg_ge h.inj hw0 hwq hγ1 hγ h₀ e
  have hsplit : ∑ x ∈ trip lo w γ₁ h₀, Hf (D x)
      = ∑ e ∈ Icc 1 dm, μ ^ 2 * Eb e ^ 2 * (((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card : ℚ)
        + (((trip lo w γ₁ h₀).filter fun x => dm + 1 ≤ D x).card : ℚ) := by
    simp only [Hf, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    congr 1
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    · rw [Finset.sum_boole]
  unfold avg
  simp_rw [step1]
  calc (∑ a, (∑ x ∈ trip lo w γ₁ h₀, X a x) / (trip lo w γ₁ h₀).card)
        / Fintype.card (Fin K → Fin L → Fin n → ZMod q)
      = (∑ x ∈ trip lo w γ₁ h₀, (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q))
        / (trip lo w γ₁ h₀).card := by
        rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]; ring
    _ ≤ (∑ x ∈ trip lo w γ₁ h₀, Hf (D x)) / (trip lo w γ₁ h₀).card :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hcov x) htripc.le
    _ = ∑ e ∈ Icc 1 dm, μ ^ 2 * Eb e ^ 2 * ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card
          : ℚ) / (trip lo w γ₁ h₀).card)
        + (((trip lo w γ₁ h₀).filter fun x => dm + 1 ≤ D x).card : ℚ)
          / (trip lo w γ₁ h₀).card := by
        rw [hsplit, add_div, Finset.sum_div]
        congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
    _ ≤ _ := by
        refine add_le_add ?_ (hprobs (dm + 1))
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun e _ => ?_
        rw [show μ ^ 2 * ((n.choose e : ℚ) * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ e
            * Eb e ^ 2) = μ ^ 2 * Eb e ^ 2 * ((n.choose e : ℚ)
            * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ e) by ring]
        exact mul_le_mul_of_nonneg_left (hprobs e) (by positivity)

end Main

/-! ## The numeric bound -/

section Numeric

/-- Integer form of the weighted count on `d` slots, scaled by `D^(K n)` (`β = Bd / D`):
the gap-count coefficients for `|T| ≤ s` and the trivial bound `q^(K d)` above. -/
def EN (e e₂ q n K Bd D d s : ℕ) : ℕ :=
  sumF (fun t => Bd ^ t * D ^ (K * n - t) * (coefK e e₂ q n K 1 d s t - chooseC (K * n) t))
      (s + 1)
    + sumF (fun t => if s < t then Bd ^ t * D ^ (K * n - t) * (chooseC (K * n) t * (q ^ (K * d) - 1))
      else 0) (K * n + 1)

lemma sum_card_split {m : ℕ} (F : Finset (Fin m) → ℚ) :
    ∑ T ∈ (univ : Finset (Fin m)).powerset, F T
      = ∑ t ∈ range (m + 1), ∑ T ∈ (univ : Finset (Fin m)).powersetCard t, F T := by
  rw [← sum_idx_card m F]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  exact ⟨fun _ => by simpa using Finset.card_le_univ T, fun _ => trivial⟩

/-- **The weighted count is at most `EN / D^(K n)`.** -/
lemma wcount_le_EN {n K : ℕ} (hn : 0 < n) (e e₂ q Bd D d s : ℕ) (hq : 1 ≤ q) (hD : 0 < D)
    (hs : s ≤ K * n) :
    ∑ T ∈ (univ : Finset (Fin (K * n))).powerset,
        ((Bd : ℚ) / D) ^ T.card * (((q : ℚ) ^ xg n K d T) - 1)
      ≤ (EN e e₂ q n K Bd D d s : ℚ) / (D : ℚ) ^ (K * n) := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hq' : (1 : ℚ) ≤ q := by exact_mod_cast hq
  set bt : ℚ := (Bd : ℚ) / D
  have hbt : 0 ≤ bt := by positivity
  -- per size `t`
  have hA : ∀ t, ∑ T ∈ (univ : Finset (Fin (K * n))).powersetCard t,
      bt ^ T.card * (((q : ℚ) ^ xg n K d T) - 1)
      = bt ^ t * ((∑ T ∈ (univ : Finset (Fin (K * n))).powersetCard t, q ^ (1 * xg n K d T) : ℕ)
        - (chooseC (K * n) t : ℕ)) := by
    intro t
    rw [Finset.sum_congr rfl fun T hT => by rw [(Finset.mem_powersetCard.mp hT).2], ← Finset.mul_sum,
      Finset.sum_sub_distrib, chooseC_eq]
    push_cast
    simp [Finset.card_powersetCard, one_mul]
  have hscale : ∀ t, t ≤ K * n → ∀ X : ℚ,
      (Bd : ℚ) ^ t * (D : ℚ) ^ (K * n - t) * X / (D : ℚ) ^ (K * n) = bt ^ t * X := by
    intro t ht X
    rw [div_pow, show (D : ℚ) ^ (K * n) = D ^ (K * n - t) * D ^ t by
      rw [← pow_add]; congr 1; omega]
    field_simp
  rw [sum_card_split]
  have hsplit : range (K * n + 1) = range (s + 1) ∪ Finset.Ico (s + 1) (K * n + 1) := by
    ext t; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro t h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega)]
  unfold EN
  rw [Nat.cast_add, add_div, sumF_eq, sumF_eq]
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  refine add_le_add (Finset.sum_le_sum fun t ht => ?_) ?_
  · have ht' : t ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [hA, hscale t (ht'.trans hs)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hbt _)
    exact cast_sub_le_of _ _ _ (sum_T_le_coefK e e₂ q 1 d s t hq hn ht')
  · have hsubI : Finset.Ico (s + 1) (K * n + 1) ⊆ range (K * n + 1) := fun t ht => by
      simp only [Finset.mem_Ico, Finset.mem_range] at ht ⊢; omega
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsubI fun t _ _ => ?_)
    · refine Finset.sum_le_sum fun t ht => ?_
      obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.mp ht
      rw [if_pos (by omega), hA, hscale t (by omega)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hbt _)
      have hle : ∑ T ∈ (univ : Finset (Fin (K * n))).powersetCard t, q ^ (1 * xg n K d T)
          ≤ chooseC (K * n) t * q ^ (K * d) := by
        calc _ ≤ ∑ _T ∈ (univ : Finset (Fin (K * n))).powersetCard t, q ^ (K * d) :=
              Finset.sum_le_sum fun T _ => Nat.pow_le_pow_right (by omega)
                (by rw [one_mul]; exact xg_le d T)
          _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, card_univ, Fintype.card_fin,
              smul_eq_mul, chooseC_eq]
      have : ((∑ T ∈ (univ : Finset (Fin (K * n))).powersetCard t, q ^ (1 * xg n K d T) : ℕ) : ℚ)
          ≤ (chooseC (K * n) t : ℚ) * (q : ℚ) ^ (K * d) := by exact_mod_cast hle
      have hc : (((q ^ (K * d) - 1 : ℕ)) : ℚ) = (q : ℚ) ^ (K * d) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
      rw [hc]
      nlinarith
    · have : (1 : ℚ) ≤ (q : ℚ) ^ (K * d) := one_le_pow₀ hq'
      split_ifs
      · have : (0 : ℚ) ≤ (q : ℚ) ^ (K * d) - 1 := by linarith
        positivity
      · simp

/-- The sum checked by the kernel (scaled to integers). -/
def numL (e e₂ q n K Bd Dc pn pd s dm : ℕ) : ℕ :=
  sumF (fun d => if 1 ≤ d then chooseC n d * pn ^ d * pd ^ (dm + 1 - d)
      * EN e e₂ q n K Bd Dc d s ^ 2 else 0) (dm + 1)
    + chooseC n (dm + 1) * pn ^ (dm + 1) * q ^ (2 * (K * n))

end Numeric

section Final
open Matrix
variable {K : ℕ}

/-- **Relative second moment.** If the integer inequality
`2^k · numL ≤ Dc^(2Kn) · pd^(d_m+1)` holds (checked by the kernel for concrete parameters), then
`E_A E_t (ρ_c(t) − μ)² ≤ μ² / 2^k`. Here `Dc` is the number of r₀-passing values per coordinate,
`p = pn / pd = 1/w + (2γ₁)^{-(L-1)}`. -/
theorem var_rel {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {cz : ZMod q} (hwz : ∀ k, ζ k ^ n = cz) (hn : 0 < n)
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) (hwq : w ≤ q) (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (e e₂ s dm k : ℕ) (hs : s ≤ K * n)
    (hnum : 2 ^ k * numL e e₂ q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        ((2 * γ₁) ^ (L - 1) + w) (w * (2 * γ₁) ^ (L - 1)) s dm
      ≤ (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n)) * (w * (2 * γ₁) ^ (L - 1)) ^ (dm + 1)) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2) / (tbox (n := n) γ₁ h₀).card)
      ≤ (∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2 / 2 ^ k := by
  set Dc := mb * (2 * (γ₂ - β) - 1) with hDc
  set Bd := q - Dc with hBd
  have hDcq : Dc ≤ q := pass_le_q hp
  have hDc0 : 0 < Dc := by
    have h1 := hp.mb_pos; have h2 := hp.β_lt_γ₂
    exact Nat.mul_pos h1 (by omega)
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hDc' : (0 : ℚ) < Dc := by exact_mod_cast hDc0
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq1
  set bt : ℚ := (Bd : ℚ) / Dc
  have hgood : ∀ r, ((good (q := q) γ₂ β v r).card : ℚ) = Dc := fun r => by
    rw [card_good hp hv r]
  have hμ : ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q = ((Dc : ℚ) / q) ^ (K * n) := by
    simp_rw [hgood]; rw [Finset.prod_const, card_univ, Fintype.card_fin]
  have hbad : ∀ r, ((q : ℚ) - (good (q := q) γ₂ β v r).card) ≤ bt * (good (q := q) γ₂ β v r).card := by
    intro r; rw [hgood]
    simp only [bt, hBd]; rw [Nat.cast_sub hDcq]; field_simp; rfl
  have hEb : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then bt ^ (supp ξ).card else 0)
        ≤ (EN e e₂ q n K Bd Dc S.card s : ℚ) / (Dc : ℚ) ^ (K * n) :=
    fun S _ _ => (wsum_le h.inj h.ne0 hwz S (by positivity)).trans
      (wcount_le_EN hn e e₂ q Bd Dc S.card s hq1 hDc0 hs)
  refine (var_le h hw0 hwq hγ1 hγ h₀ bt (by positivity) hbad dm
    (fun d => (EN e e₂ q n K Bd Dc d s : ℚ) / (Dc : ℚ) ^ (K * n)) hEb).trans ?_
  rw [hμ]
  -- pure arithmetic from `hnum`
  set pn : ℕ := (2 * γ₁) ^ (L - 1) + w
  set pd : ℕ := w * (2 * γ₁) ^ (L - 1)
  have hpd : (0 : ℚ) < pd := by positivity
  have hp_eq : 1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1) = (pn : ℚ) / pd := by
    simp only [pn, pd]; push_cast; field_simp
  rw [hp_eq]
  have hnum' : (2 : ℚ) ^ k * ((∑ d ∈ Icc 1 dm, (n.choose d : ℚ) * (pn : ℚ) ^ d
        * (pd : ℚ) ^ (dm + 1 - d) * (EN e e₂ q n K Bd Dc d s : ℚ) ^ 2)
        + (n.choose (dm + 1) : ℚ) * (pn : ℚ) ^ (dm + 1) * (q : ℚ) ^ (2 * (K * n)))
      ≤ (Dc : ℚ) ^ (2 * (K * n)) * (pd : ℚ) ^ (dm + 1) := by
    have := (Nat.cast_le (α := ℚ)).mpr hnum
    unfold numL at this
    rw [sumF_eq] at this
    push_cast at this
    have hr : ∑ x ∈ range (dm + 1), (if 1 ≤ x then (chooseC n x : ℚ) * (pn : ℚ) ^ x
        * (pd : ℚ) ^ (dm + 1 - x) * (EN e e₂ q n K Bd Dc x s : ℚ) ^ 2 else 0)
        = ∑ d ∈ Icc 1 dm, (n.choose d : ℚ) * (pn : ℚ) ^ d
          * (pd : ℚ) ^ (dm + 1 - d) * (EN e e₂ q n K Bd Dc d s : ℚ) ^ 2 := by
      rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext d; simp [Finset.mem_Icc]; omega) fun d _ => by rw [chooseC_eq]
    simp only [chooseC_eq] at this hr
    convert this using 3
    exact hr.symm
  have hDn : (0 : ℚ) < (Dc : ℚ) ^ (K * n) := by positivity
  have hQ : (0 : ℚ) < (q : ℚ) ^ (2 * (K * n)) := by positivity
  have hsum : (((Dc : ℚ) / q) ^ (K * n)) ^ 2 *
      ∑ d ∈ Icc 1 dm, (n.choose d : ℚ) * ((pn : ℚ) / pd) ^ d
        * ((EN e e₂ q n K Bd Dc d s : ℚ) / (Dc : ℚ) ^ (K * n)) ^ 2
      = (∑ d ∈ Icc 1 dm, (n.choose d : ℚ) * (pn : ℚ) ^ d * (pd : ℚ) ^ (dm + 1 - d)
          * (EN e e₂ q n K Bd Dc d s : ℚ) ^ 2) / ((q : ℚ) ^ (2 * (K * n)) * (pd : ℚ) ^ (dm + 1)) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' := (Finset.mem_Icc.mp hd).2
    rw [show (pd : ℚ) ^ (dm + 1) = (pd : ℚ) ^ d * (pd : ℚ) ^ (dm + 1 - d) by
      rw [← pow_add]; congr 1; omega]
    rw [show (q : ℚ) ^ (2 * (K * n)) = ((q : ℚ) ^ (K * n)) ^ 2 by rw [← pow_mul]; ring_nf]
    simp only [div_pow]
    field_simp
  have hlast : (n.choose (dm + 1) : ℚ) * ((pn : ℚ) / pd) ^ (dm + 1)
      = (n.choose (dm + 1) : ℚ) * (pn : ℚ) ^ (dm + 1) * (q : ℚ) ^ (2 * (K * n))
        / ((q : ℚ) ^ (2 * (K * n)) * (pd : ℚ) ^ (dm + 1)) := by
    rw [div_pow]
    field_simp
  rw [hsum, hlast, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [show (((Dc : ℚ) / q) ^ (K * n)) ^ 2 = (Dc : ℚ) ^ (2 * (K * n)) / (q : ℚ) ^ (2 * (K * n)) by
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm (K * n) 2]]
  rw [div_mul_eq_mul_div, le_div_iff₀ hQ]
  have := mul_le_mul_of_nonneg_right hnum' hQ.le
  nlinarith [this]

/-- **First moment.** Under the hypotheses of `var_rel` with `k = 2j`,
`E_A E_t |ρ_c(t) − μ| ≤ μ / 2^j`. -/
theorem dev_rel {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {cz : ZMod q} (hwz : ∀ k, ζ k ^ n = cz) (hn : 0 < n)
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) (hwq : w ≤ q) (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (e e₂ s dm j : ℕ) (hs : s ≤ K * n)
    (hnum : 2 ^ (2 * j) * numL e e₂ q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        ((2 * γ₁) ^ (L - 1) + w) (w * (2 * γ₁) ^ (L - 1)) s dm
      ≤ (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n)) * (w * (2 * γ₁) ^ (L - 1)) ^ (dm + 1)) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, |rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q|) / (tbox (n := n) γ₁ h₀).card)
      ≤ (∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) / 2 ^ j := by
  set μ := ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q with hμ
  have hvar := var_rel (lo := lo) h hwz hn hp hv hw0 hwq hγ1 hγ h₀ e e₂ s dm (2 * j) hs hnum
  rw [← hμ] at hvar
  have hμ0 : 0 < μ := by
    refine Finset.prod_pos fun r _ => div_pos ?_ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))
    rw [card_good hp hv r]
    have h1 := hp.mb_pos; have h2 := hp.β_lt_γ₂
    exact_mod_cast Nat.mul_pos h1 (by omega)
  set η : ℚ := μ / 2 ^ j
  have hη : 0 < η := div_pos hμ0 (pow_pos two_pos j)
  have hpt : ∀ x : ℚ, |x| ≤ (x ^ 2 / η + η) / 2 := by
    intro x
    have : 0 ≤ (|x| - η) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
    rw [sub_sq, sq_abs] at this
    have e1 : (x ^ 2 - 2 * |x| * η + η ^ 2) / η = x ^ 2 / η - 2 * |x| + η := by
      field_simp
    linarith
  have hTB : (0 : ℚ) < (tbox (n := n) γ₁ h₀).card := by
    rw [card_tbox]; have : 0 < 2 * γ₁ := by omega
    positivity
  calc avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, |rhoC mulmat γ₂ β v lo w h₀ a t - μ|) / (tbox (n := n) γ₁ h₀).card)
      ≤ avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        ((∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2)
          / (tbox (n := n) γ₁ h₀).card / η + η) / 2) := by
        refine avg_mono fun a => ?_
        rw [div_le_iff₀ hTB]
        have : ∑ t ∈ tbox γ₁ h₀, |rhoC mulmat γ₂ β v lo w h₀ a t - μ|
            ≤ ∑ t ∈ tbox γ₁ h₀, ((rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2 / η + η) / 2 :=
          Finset.sum_le_sum fun t _ => hpt _
        refine this.trans (le_of_eq ?_)
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
          nsmul_eq_mul]
        field_simp
    _ = (avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
          (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2)
            / (tbox (n := n) γ₁ h₀).card) / η + η) / 2 := by
        unfold avg
        rw [Finset.sum_div, Finset.sum_div]
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, card_univ,
          nsmul_eq_mul]
        have : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
          exact_mod_cast Fintype.card_pos
        field_simp
    _ ≤ (μ ^ 2 / 2 ^ (2 * j) / η + η) / 2 := by
        have := div_le_div_of_nonneg_right hvar hη.le
        linarith
    _ = η := by
        have hμne : μ ≠ 0 := hμ0.ne'
        rw [show η = μ / 2 ^ j from rfl, pow_mul]
        field_simp
        rw [← pow_mul, ← pow_mul, mul_comm j 2]
        ring

end Final


end AltR0

end

end AltR0Part

section AltR0ExcPart

/-!
# alt-r0: degenerate slot sets containing an exceptional slot

An *exceptional* slot is one where the whole tail vanishes and one of the two heads vanishes.
Such a slot is always degenerate (`exc_sub_degS`), and `d` degenerate slots of which at least
one is exceptional occur with probability at most `C(n,d) · ((p + e)^d - p^d)`, where
`p = 1/w + (2γ₁)^{-(L-1)}` and `e = 2 / (w (2γ₁)^(L-1))` (`prob_deg_exc`).
-/

open Finset

noncomputable section

namespace AltR0
open RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n L : ℕ}

/-- Exceptional slots: the whole tail vanishes and one of the two heads vanishes. -/
def exc (ζ : Fin n → ZMod q) (h₀ : Fin L) (y₁ y₁' : Fin n → ℤ) (t : Fin L → Fin n → ℤ) :
    Finset (Fin n) :=
  univ.filter fun k => (∀ j, j ≠ h₀ → nttP ζ (fun s => (t j s : ZMod q)) k = 0) ∧
    (nttP ζ (fun s => (y₁ s : ZMod q)) k = 0 ∨ nttP ζ (fun s => (y₁' s : ZMod q)) k = 0)

/-- Exceptional slots are degenerate. -/
lemma exc_sub_degS (ζ : Fin n → ZMod q) (h₀ : Fin L) (y₁ y₁' : Fin n → ℤ)
    (t : Fin L → Fin n → ℤ) :
    exc ζ h₀ y₁ y₁' t ⊆ degS ζ (join h₀ y₁ t) (join h₀ y₁' t) := by
  intro k hk
  obtain ⟨ht, hy⟩ := (Finset.mem_filter.mp hk).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases hy with h | h
  · refine ⟨1, 0, Or.inl one_ne_zero, fun j => ?_⟩
    rw [zero_mul, add_zero, one_mul, ntt_join]
    split_ifs with hj
    · exact h
    · exact ht j hj
  · refine ⟨0, 1, Or.inr one_ne_zero, fun j => ?_⟩
    rw [zero_mul, zero_add, one_mul, ntt_join]
    split_ifs with hj
    · exact h
    · exact ht j hj

lemma nttP_intsub (ζ : Fin n → ZMod q) (f g : Fin n → ℤ) (k : Fin n) :
    nttP ζ (fun s => ((f s - g s : ℤ) : ZMod q)) k
      = nttP ζ (fun s => (f s : ZMod q)) k - nttP ζ (fun s => (g s : ZMod q)) k := by
  rw [← nttP_sub]; congr 1; funext s; simp

/-- At most `w^(n - |S|)` polynomials in the box have prescribed NTT values on `S`. -/
lemma card_solc_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw : w ≤ q) (S : Finset (Fin n)) (c : Fin n → ZMod q) :
    ((hbox lo w).filter fun f => ∀ k ∈ S, nttP ζ (fun s => (f s : ZMod q)) k = c k).card
      ≤ w ^ (n - S.card) := by
  rcases Finset.eq_empty_or_nonempty ((hbox lo w).filter fun f =>
      ∀ k ∈ S, nttP ζ (fun s => (f s : ZMod q)) k = c k) with h | ⟨g, hg⟩
  · rw [h, Finset.card_empty]; exact Nat.zero_le _
  · obtain ⟨hgb, hgc⟩ := Finset.mem_filter.mp hg
    refine (Finset.card_le_card fun f hf => ?_).trans (card_sol_le hζ hw S g hgb)
    obtain ⟨hfb, hfc⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hfb, fun k hk => by rw [nttP_intsub, hfc k hk, hgc k hk,
      sub_self]⟩

/-- Head pairs with `y₁` vanishing on `X₁`, `y₁'` vanishing on `X₂` and the difference
vanishing on `D`. -/
lemma card_head2_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw : w ≤ q) (X₁ X₂ D : Finset (Fin n)) :
    ((hbox lo w ×ˢ hbox lo w).filter fun ff =>
        (∀ k ∈ X₁, nttP ζ (fun s => (ff.1 s : ZMod q)) k = 0) ∧
        (∀ k ∈ X₂, nttP ζ (fun s => (ff.2 s : ZMod q)) k = 0) ∧
        ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0).card
      ≤ w ^ (n - X₁.card) * w ^ (n - (X₂ ∪ D).card) := by
  set c : (Fin n → ℤ) → Fin n → ZMod q := fun f k =>
    if k ∈ D then nttP ζ (fun s => (f s : ZMod q)) k else 0 with hc
  have hsub : ((hbox lo w ×ˢ hbox lo w).filter fun ff =>
        (∀ k ∈ X₁, nttP ζ (fun s => (ff.1 s : ZMod q)) k = 0) ∧
        (∀ k ∈ X₂, nttP ζ (fun s => (ff.2 s : ZMod q)) k = 0) ∧
        ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0)
      ⊆ ((hbox lo w).filter fun f => ∀ k ∈ X₁, nttP ζ (fun s => (f s : ZMod q)) k
          = (fun _ => (0 : ZMod q)) k).biUnion fun f =>
        ((hbox lo w).filter fun g => ∀ k ∈ X₂ ∪ D, nttP ζ (fun s => (g s : ZMod q)) k
          = c f k).image fun g => (f, g) := by
    rintro ⟨f, g⟩ hx
    obtain ⟨hm, h1, h2, h3⟩ := Finset.mem_filter.mp hx
    obtain ⟨hf, hg⟩ := Finset.mem_product.mp hm
    refine Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, h1⟩,
      Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, fun k hk => ?_⟩, rfl⟩⟩
    simp only [hc]
    split_ifs with hkD
    · have := h3 k hkD
      rw [nttP_intsub] at this
      exact (sub_eq_zero.mp this).symm
    · exact h2 k ((Finset.mem_union.mp hk).resolve_right hkD)
  refine (Finset.card_le_card hsub).trans (card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum fun f _ => card_image_le.trans (card_solc_le hζ hw _ (c f))).trans ?_
  rw [sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_solc_le hζ hw X₁ _)

lemma sum_powerset_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) (x y : ℚ) :
    ∑ t ∈ s.powerset, x ^ t.card * y ^ (s \ t).card = (x + y) ^ s.card := by
  rw [← Finset.prod_const, Finset.prod_add]
  simp only [prod_const]

/-- **A given set of slots is degenerate and contains an exceptional slot** with probability at
most `(p + e)^|Z| - p^|Z|`. -/
lemma prob_Z_exc {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw0 : 0 < w) (hw : w ≤ q) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L)
    (Z : Finset (Fin n)) :
    prob (trip lo w γ₁ h₀) (fun x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) ∧
        (Z ∩ exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty)
      ≤ (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)
          + 2 / ((w : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ Z.card
        - (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ Z.card := by
  set A : Finset (Fin n) → Finset (Fin n) → Finset (Fin n) →
      Finset ((Fin n → ℤ) × (Fin n → ℤ)) := fun X₁ X₂ D =>
    (hbox lo w ×ˢ hbox lo w).filter fun ff =>
        (∀ k ∈ X₁, nttP ζ (fun s => (ff.1 s : ZMod q)) k = 0) ∧
        (∀ k ∈ X₂, nttP ζ (fun s => (ff.2 s : ZMod q)) k = 0) ∧
        ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0 with hA
  set B : Finset (Fin n) → Finset (Fin L → Fin n → ℤ) := fun E =>
    (tbox γ₁ h₀).filter fun t => ∀ j, j ≠ h₀ → ∀ k ∈ E, nttP ζ (fun s => (t j s : ZMod q)) k = 0
    with hB
  have hsub : (trip lo w γ₁ h₀).filter (fun x =>
        Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) ∧
        (Z ∩ exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty)
      ⊆ (Z.powerset.erase ∅).biUnion fun X => X.powerset.biUnion fun X₁ =>
          (Z \ X).powerset.biUnion fun D => A X₁ (X \ X₁) D ×ˢ B (X ∪ ((Z \ X) \ D)) := by
    intro x hx
    obtain ⟨hxm, hZ, hne⟩ := Finset.mem_filter.mp hx
    obtain ⟨hff, ht⟩ := Finset.mem_product.mp hxm
    set X := Z ∩ exc ζ h₀ x.1.1 x.1.2 x.2 with hX
    set X₁ := X.filter fun k => nttP ζ (fun s => (x.1.1 s : ZMod q)) k = 0
    set D := (Z \ X).filter fun k => nttP ζ (fun s => ((x.1.1 s - x.1.2 s : ℤ) : ZMod q)) k = 0
    have hXZ : X ⊆ Z := Finset.inter_subset_left
    have hexc : ∀ k ∈ X, k ∈ exc ζ h₀ x.1.1 x.1.2 x.2 := fun k hk => (Finset.mem_inter.mp hk).2
    refine Finset.mem_biUnion.mpr ⟨X, Finset.mem_erase.mpr ⟨hne.ne_empty,
      Finset.mem_powerset.mpr hXZ⟩, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨X₁, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    refine Finset.mem_biUnion.mpr ⟨D, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hff,
      fun k hk => (Finset.mem_filter.mp hk).2, fun k hk => ?_,
      fun k hk => (Finset.mem_filter.mp hk).2⟩, Finset.mem_filter.mpr ⟨ht, fun j hj k hk => ?_⟩⟩
    · obtain ⟨hkX, hk1⟩ := Finset.mem_sdiff.mp hk
      rcases ((Finset.mem_filter.mp (hexc k hkX)).2).2 with h | h
      · exact absurd (Finset.mem_filter.mpr ⟨hkX, h⟩) hk1
      · exact h
    · rcases Finset.mem_union.mp hk with hkX | hkE
      · exact ((Finset.mem_filter.mp (hexc k hkX)).2).1 j hj
      · obtain ⟨hk2, hkD⟩ := Finset.mem_sdiff.mp hkE
        obtain ⟨hkZ, _⟩ := Finset.mem_sdiff.mp hk2
        rcases degS_sub ζ h₀ x.1.1 x.1.2 x.2 k (hZ hkZ) with h | h
        · exact absurd (Finset.mem_filter.mpr ⟨hk2, h⟩) hkD
        · exact h j hj
  have hw' : (0 : ℚ) < w := by exact_mod_cast hw0
  have hg' : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hcard : ((trip lo w γ₁ h₀).card : ℚ)
      = (w : ℚ) ^ n * (w : ℚ) ^ n * (((2 * γ₁ : ℚ)) ^ n) ^ (L - 1) := by
    rw [trip, card_product, card_product, card_hbox, card_tbox]; push_cast; ring
  set τ : ℚ := 1 / ((2 * γ₁ : ℚ)) ^ (L - 1) with hτ
  set a : ℚ := 1 / ((w : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1)) with ha
  have hterm : ∀ X ∈ Z.powerset.erase ∅, ∀ X₁ ∈ X.powerset, ∀ D ∈ (Z \ X).powerset,
      (((A X₁ (X \ X₁) D ×ˢ B (X ∪ ((Z \ X) \ D))).card : ℕ) : ℚ)
        ≤ (a ^ X₁.card * a ^ (X \ X₁).card) * ((1 / (w : ℚ)) ^ D.card * τ ^ ((Z \ X) \ D).card)
          * (trip lo w γ₁ h₀).card := by
    intro X hX X₁ hX₁ D hD
    have hXZ : X ⊆ Z := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hX)
    have hX₁X : X₁ ⊆ X := Finset.mem_powerset.mp hX₁
    have hDZ : D ⊆ Z \ X := Finset.mem_powerset.mp hD
    have hdisj1 : Disjoint (X \ X₁) D := by
      rw [Finset.disjoint_left]
      intro k hk hkD
      exact (Finset.mem_sdiff.mp (hDZ hkD)).2 (Finset.mem_sdiff.mp hk).1
    have hdisj2 : Disjoint X ((Z \ X) \ D) := by
      rw [Finset.disjoint_left]
      intro k hk hkE
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hkE).1).2 hk
    have hc1 := card_head2_le (lo := lo) hζ hw X₁ (X \ X₁) D
    have hc2 := card_tail_le hζ hγ1 hγ h₀ (X ∪ ((Z \ X) \ D))
    rw [Finset.card_union_of_disjoint hdisj1] at hc1
    rw [Finset.card_union_of_disjoint hdisj2,
      ← Finset.card_sdiff_add_card_eq_card hX₁X] at hc2
    have hn1 : X₁.card ≤ n := by simpa using Finset.card_le_univ X₁
    have hn2 : (X \ X₁).card + D.card ≤ n := by
      rw [← Finset.card_union_of_disjoint hdisj1]; simpa using Finset.card_le_univ ((X \ X₁) ∪ D)
    have hn3 : (X \ X₁).card + X₁.card + ((Z \ X) \ D).card ≤ n := by
      rw [Finset.card_sdiff_add_card_eq_card hX₁X, ← Finset.card_union_of_disjoint hdisj2]
      simpa using Finset.card_le_univ (X ∪ ((Z \ X) \ D))
    rw [card_product]
    push_cast
    have ha' : ((A X₁ (X \ X₁) D).card : ℚ)
        ≤ (w : ℚ) ^ (n - X₁.card) * (w : ℚ) ^ (n - ((X \ X₁).card + D.card)) := by
      exact_mod_cast hc1
    have hb' : ((B (X ∪ ((Z \ X) \ D))).card : ℚ)
        ≤ (((2 * γ₁ : ℚ)) ^ (n - ((X \ X₁).card + X₁.card + ((Z \ X) \ D).card))) ^ (L - 1) := by
      exact_mod_cast hc2
    refine (mul_le_mul ha' hb' (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [hcard, pow_right_comm (2 * (γ₁ : ℚ)) n (L - 1), pow_right_comm (2 * (γ₁ : ℚ)) _ (L - 1)]
    simp only [ha, hτ]
    have hG : (0 : ℚ) < ((2 * γ₁ : ℚ)) ^ (L - 1) := by positivity
    generalize ((2 * γ₁ : ℚ)) ^ (L - 1) = G at hG ⊢
    have hwne : (w : ℚ) ≠ 0 := hw'.ne'
    have hGne : G ≠ 0 := hG.ne'
    rw [pow_sub₀ _ hwne hn1, pow_sub₀ _ hwne hn2, pow_sub₀ _ hGne hn3]
    simp only [one_div, mul_inv, inv_pow, mul_pow, pow_add]
    field_simp
  have hsum : ∑ X ∈ Z.powerset.erase ∅, ∑ X₁ ∈ X.powerset, ∑ D ∈ (Z \ X).powerset,
      (a ^ X₁.card * a ^ (X \ X₁).card) * ((1 / (w : ℚ)) ^ D.card * τ ^ ((Z \ X) \ D).card)
      = (1 / (w : ℚ) + τ + 2 / ((w : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ Z.card
        - (1 / (w : ℚ) + τ) ^ Z.card := by
    have h1 : ∀ X ∈ Z.powerset.erase ∅, ∑ X₁ ∈ X.powerset, ∑ D ∈ (Z \ X).powerset,
        (a ^ X₁.card * a ^ (X \ X₁).card) * ((1 / (w : ℚ)) ^ D.card * τ ^ ((Z \ X) \ D).card)
        = (a + a) ^ X.card * (1 / (w : ℚ) + τ) ^ (Z \ X).card := by
      intro X _
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_powerset_pow]
    rw [Finset.sum_congr rfl h1, Finset.sum_erase_eq_sub (Finset.empty_mem_powerset Z),
      sum_powerset_pow]
    simp only [card_empty, pow_zero, one_mul, sdiff_empty]
    congr 2
    simp only [ha]
    ring
  unfold prob
  rw [div_le_iff₀ (by rw [hcard]; positivity)]
  have hcount := (Finset.card_le_card hsub).trans (card_biUnion_le.trans (Finset.sum_le_sum
    fun X _ => card_biUnion_le.trans (Finset.sum_le_sum fun X₁ _ => card_biUnion_le)))
  refine (Nat.cast_le.mpr hcount).trans ?_
  push_cast
  rw [← hsum, Finset.sum_mul]
  refine Finset.sum_le_sum fun X hX => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun X₁ hX₁ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun D hD => ?_
  exact_mod_cast hterm X hX X₁ hX₁ D hD

/-- **`d` degenerate slots, one of them exceptional,** occur with probability at most
`C(n,d) · ((p + e)^d - p^d)`. -/
theorem prob_deg_exc {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {lo : Fin n → ℤ} {w : ℕ}
    (hw0 : 0 < w) (hw : w ≤ q) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L) (d : ℕ)
    (hd : 1 ≤ d) :
    prob (trip lo w γ₁ h₀) (fun x => d ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card ∧
        (exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty)
      ≤ n.choose d * ((1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)
            + 2 / ((w : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ d
          - (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ d) := by
  refine (prob_le_sum _ ((univ : Finset (Fin n)).powersetCard d) _
    (fun Z x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) ∧
      (Z ∩ exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty) fun x _ hx => ?_).trans ?_
  · obtain ⟨hc, s, hs⟩ := hx
    have hsd := exc_sub_degS ζ h₀ x.1.1 x.1.2 x.2 hs
    obtain ⟨Z, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq (s := {s})
      (Finset.singleton_subset_iff.mpr hsd) (by simpa using hd) hc
    exact ⟨Z, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h3⟩, h2,
      ⟨s, Finset.mem_inter.mpr ⟨h1 (Finset.mem_singleton_self s), hs⟩⟩⟩
  · refine (Finset.sum_le_sum fun Z hZ => prob_Z_exc hζ hw0 hw hγ1 hγ h₀ Z).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun Z hZ => by rw [(Finset.mem_powersetCard.mp hZ).2], sum_const,
      Finset.card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

end AltR0

end

end AltR0ExcPart

section AltR0SharpPart

/-!
# alt-r0: a sharper second moment

For a pair of nonces `y = (y_{h₀}, t)`, `y' = (y'_{h₀}, t)` sharing the tail, an orthogonal pair of
test vectors `(ξ, ξ')` satisfies, at every NTT slot `k`, `ξ̃'(k) = r(k) ξ̃(k)` with `r(k) ≠ 0`,
unless the slot is *exceptional* (the whole tail and one of the heads vanish there): `r = -1` where
the tail does not vanish, `r = -ŷ_{h₀}(k)/ŷ'_{h₀}(k)` where it does. So `ξ' = Φ ξ` for a fixed
bijection `Φ`, and by `b^{wt ξ + wt ξ'} ≤ (b^{2 wt ξ} + b^{2 wt Φξ})/2` the covariance is bounded by
the count with weight `b²` instead of the square of the count with weight `b`.
-/

open Finset Matrix

noncomputable section

namespace AltR0
open RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

/-! ## Test vectors from dual coordinates -/

/-- The test vector with dual coordinates `D`. -/
def ofDual (ζ : Fin n → ZMod q) (D : Fin K → Fin n → ZMod q) : Fin (K * n) → ZMod q :=
  fun r => ∑ k, ζ k ^ ((finProdFinEquiv.symm r).2 : ℕ) * D (finProdFinEquiv.symm r).1 k

lemma dual_ofDual {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (D : Fin K → Fin n → ZMod q)
    (i : Fin K) : dual ζ (ofDual ζ D) i = D i := by
  have hu : IsUnit ((Matrix.vandermonde ζ)ᵀ).det := by
    rw [Matrix.det_transpose]; exact vand_det_unit hζ
  have hb : blk (ofDual ζ D) i = (Matrix.vandermonde ζ)ᵀ *ᵥ D i := by
    funext s
    simp only [blk, ofDual, Equiv.symm_apply_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Matrix.vandermonde_apply]
  unfold dual
  rw [hb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-! ## The pairing map -/

section Pair
variable (ζ : Fin n → ZMod q) (h₀ : Fin L) (y₁ y₁' : Fin n → ℤ) (t : Fin L → Fin n → ℤ)

/-- The tail does not vanish at slot `k`. -/
def TailNZ (k : Fin n) : Prop := ∃ j, j ≠ h₀ ∧ nttP ζ (fun s => (t j s : ZMod q)) k ≠ 0

/-- The slot ratio: `-1` where the tail does not vanish, `-ŷ₁/ŷ₁'` where it vanishes and both
heads are nonzero, `-1` otherwise. -/
def ratio (k : Fin n) : ZMod q := by
  classical
  exact if TailNZ ζ h₀ t k then -1
    else if nttP ζ (fun s => (y₁ s : ZMod q)) k ≠ 0 ∧ nttP ζ (fun s => (y₁' s : ZMod q)) k ≠ 0
    then -(nttP ζ (fun s => (y₁ s : ZMod q)) k / nttP ζ (fun s => (y₁' s : ZMod q)) k) else -1

lemma ratio_ne_zero (k : Fin n) : ratio ζ h₀ y₁ y₁' t k ≠ 0 := by
  classical
  unfold ratio
  split_ifs with h1 h2
  · exact neg_ne_zero.mpr one_ne_zero
  · exact neg_ne_zero.mpr (div_ne_zero h2.1 h2.2)
  · exact neg_ne_zero.mpr one_ne_zero

/-- `Φ ξ`: rescale the dual coordinates of `ξ` slot by slot. -/
def pairMap (ξ : Fin (K * n) → ZMod q) : Fin (K * n) → ZMod q :=
  ofDual ζ fun i k => ratio ζ h₀ y₁ y₁' t k * dual ζ ξ i k

variable {ζ}

lemma dual_pairMap (hζ : Function.Injective ζ) (ξ : Fin (K * n) → ZMod q) (i : Fin K) (k : Fin n) :
    dual ζ (pairMap ζ h₀ y₁ y₁' t ξ) i k = ratio ζ h₀ y₁ y₁' t k * dual ζ ξ i k := by
  unfold pairMap; rw [dual_ofDual hζ]

lemma pairMap_injective (hζ : Function.Injective ζ) :
    Function.Injective (pairMap (K := K) ζ h₀ y₁ y₁' t) := by
  intro ξ ξ' he
  have : ξ - ξ' = 0 := by
    refine eq_zero_of_dual hζ _ fun i => funext fun k => ?_
    have h1 := congrArg (fun v => dual ζ v i k) he
    simp only [dual_pairMap h₀ y₁ y₁' t hζ] at h1
    rw [dual_sub, Pi.sub_apply, Pi.zero_apply,
      mul_left_cancel₀ (ratio_ne_zero ζ h₀ y₁ y₁' t k) h1, sub_self]
  exact sub_eq_zero.mp this

/-- **Orthogonal pairs are graphs of `Φ`** when no degenerate slot is exceptional. -/
lemma orth_eq_pairMap {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    (h : IsNTTMul ζ mulmat)
    (hX : ∀ k ∈ degS ζ (join h₀ y₁ t) (join h₀ y₁' t), TailNZ ζ h₀ t k ∨
      (nttP ζ (fun s => (y₁ s : ZMod q)) k ≠ 0 ∧ nttP ζ (fun s => (y₁' s : ZMod q)) k ≠ 0))
    (ξ ξ' : Fin (K * n) → ZMod q)
    (horth : ∀ a, ξ ⬝ᵥ phiHom h (zc (join h₀ y₁ t)) a
      + ξ' ⬝ᵥ phiHom h (zc (join h₀ y₁' t)) a = 0) :
    ξ' = pairMap ζ h₀ y₁ y₁' t ξ := by
  classical
  have hs := slot_of_orth h ξ ξ' (zc (join h₀ y₁ t)) (zc (join h₀ y₁' t)) (fun a => by
    have := horth a
    simp only [dotProduct, phiHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact this)
  obtain ⟨hd, hd'⟩ := dualIn_of_orth h _ _ ξ ξ' horth
  have key : ∀ i k, dual ζ ξ' i k = ratio ζ h₀ y₁ y₁' t k * dual ζ ξ i k := by
    intro i k
    by_cases hk : k ∈ degS ζ (join h₀ y₁ t) (join h₀ y₁' t)
    · by_cases hT : TailNZ ζ h₀ t k
      · obtain ⟨j, hj, hne⟩ := hT
        have e := hs i j k
        rw [ntt_join, ntt_join, if_neg hj, if_neg hj, ← add_mul] at e
        have e' := (mul_eq_zero.mp e).resolve_right hne
        unfold ratio; rw [if_pos ⟨j, hj, hne⟩]
        linear_combination e'
      · have hH := (hX k hk).resolve_left hT
        have e := hs i h₀ k
        rw [ntt_join, ntt_join, if_pos rfl, if_pos rfl] at e
        unfold ratio; rw [if_neg hT, if_pos hH]
        field_simp [hH.2]
        linear_combination e
    · rw [hd i k hk, hd' i k hk, mul_zero]
  have : ξ' - pairMap ζ h₀ y₁ y₁' t ξ = 0 := by
    refine eq_zero_of_dual h.inj _ fun i => funext fun k => ?_
    rw [dual_sub, Pi.sub_apply, dual_pairMap h₀ y₁ y₁' t h.inj, key, sub_self]; rfl
  exact sub_eq_zero.mp this

/-- **Sharper pair sum.** Without exceptional degenerate slots, the `b`-weighted sum over
orthogonal pairs is at most the `b²`-weighted count of single test vectors. -/
theorem pair_sum_le {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    (h : IsNTTMul ζ mulmat)
    (hX : ∀ k ∈ degS ζ (join h₀ y₁ t) (join h₀ y₁' t), TailNZ ζ h₀ t k ∨
      (nttP ζ (fun s => (y₁ s : ZMod q)) k ≠ 0 ∧ nttP ζ (fun s => (y₁' s : ZMod q)) k ≠ 0))
    {bt : ℚ} (hbt : 0 ≤ bt) :
    (∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
      ∑ ξ' ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        if (∀ a, ξ ⬝ᵥ phiHom h (zc (join h₀ y₁ t)) a + ξ' ⬝ᵥ phiHom h (zc (join h₀ y₁' t)) a = 0)
        then bt ^ ((univ.filter fun r => ξ r ≠ 0).card + (univ.filter fun r => ξ' r ≠ 0).card)
        else 0)
      ≤ ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
          (if DualIn ζ (degS ζ (join h₀ y₁ t) (join h₀ y₁' t)) ξ then (bt ^ 2) ^ (supp ξ).card
            else 0) := by
  classical
  set D := degS ζ (join h₀ y₁ t) (join h₀ y₁' t)
  set Φ := pairMap (K := K) ζ h₀ y₁ y₁' t
  set S := ((univ : Finset (Fin (K * n) → ZMod q)).erase 0).filter (DualIn ζ D)
  have hΦ0 : Φ 0 = 0 := by
    refine eq_zero_of_dual h.inj _ fun i => funext fun k => ?_
    rw [dual_pairMap h₀ y₁ y₁' t h.inj]
    have : dual ζ (0 : Fin (K * n) → ZMod q) i = 0 := by
      unfold dual; rw [show blk (0 : Fin (K * n) → ZMod q) i = 0 from rfl, Matrix.mulVec_zero]
    rw [this]; simp
  have hinj := pairMap_injective (K := K) h₀ y₁ y₁' t h.inj
  have hmaps : ∀ ξ ∈ S, Φ ξ ∈ S := by
    intro ξ hξ
    obtain ⟨hξ0, hξD⟩ := Finset.mem_filter.mp hξ
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h0 => ?_, Finset.mem_univ _⟩,
      fun i k hk => ?_⟩
    · exact (Finset.mem_erase.mp hξ0).1 (hinj (h0.trans hΦ0.symm))
    · rw [dual_pairMap h₀ y₁ y₁' t h.inj, hξD i k hk, mul_zero]
  have himg : S.image Φ = S := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hx; exact hmaps ξ hξ
    · rw [Finset.card_image_of_injective _ hinj]
  -- step a: each inner sum has at most the term `ξ' = Φ ξ`
  have hstep : ∀ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
      (∑ ξ' ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        if (∀ a, ξ ⬝ᵥ phiHom h (zc (join h₀ y₁ t)) a + ξ' ⬝ᵥ phiHom h (zc (join h₀ y₁' t)) a = 0)
        then bt ^ ((univ.filter fun r => ξ r ≠ 0).card + (univ.filter fun r => ξ' r ≠ 0).card)
        else 0)
      ≤ if ξ ∈ S then bt ^ ((supp ξ).card + (supp (Φ ξ)).card) else 0 := by
    intro ξ hξ
    rw [Finset.sum_eq_single (Φ ξ)]
    · split_ifs with ho hS
      · exact le_rfl
      · exact absurd (Finset.mem_filter.mpr ⟨hξ, (dualIn_of_orth h _ _ ξ _ ho).1⟩) hS
      · positivity
      · exact le_rfl
    · intro ξ' _ hne
      rw [if_neg]
      intro ho
      exact hne (orth_eq_pairMap h₀ y₁ y₁' t h hX ξ ξ' ho)
    · intro hn
      exact absurd (Finset.mem_erase.mpr ⟨fun h0 => (Finset.mem_erase.mp hξ).1
        (hinj (h0.trans hΦ0.symm)), Finset.mem_univ _⟩) hn
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_filter]
  -- step b: AM-GM
  have hamgm : ∀ ξ ∈ S, bt ^ ((supp ξ).card + (supp (Φ ξ)).card)
      ≤ ((bt ^ 2) ^ (supp ξ).card + (bt ^ 2) ^ (supp (Φ ξ)).card) / 2 := by
    intro ξ _
    have e1 : (bt ^ 2) ^ (supp ξ).card = (bt ^ (supp ξ).card) ^ 2 := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    have e2 : (bt ^ 2) ^ (supp (Φ ξ)).card = (bt ^ (supp (Φ ξ)).card) ^ 2 := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e1, e2, pow_add]
    nlinarith [sq_nonneg (bt ^ (supp ξ).card - bt ^ (supp (Φ ξ)).card)]
  have hS' : (((univ : Finset (Fin (K * n) → ZMod q)).erase 0).filter fun ξ => ξ ∈ S) = S := by
    ext ξ; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
  rw [hS']
  refine (Finset.sum_le_sum hamgm).trans (le_of_eq ?_)
  -- step c: `Φ` permutes `S`
  have hperm : ∑ ξ ∈ S, (bt ^ 2) ^ (supp (Φ ξ)).card = ∑ ξ ∈ S, (bt ^ 2) ^ (supp ξ).card := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image fun x _ y _ hxy => hinj hxy]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hperm, ← two_mul, mul_div_cancel_left₀ _ two_ne_zero,
    Finset.sum_filter]

end Pair

/-! ## The weighted count by rows

The `b`-weighted sum over coordinate sets factors over the `K` rows, so it is the `K`-th power of
a row sum, which `row_sum_le` bounds by the gap counts `GBk`. No truncation in `|T|` is needed. -/

section Rows

/-- Integer form: `(∑_u Bd^u D^(n-u) GBk_u)^K − (D + Bd)^(K n)`. -/
def ENr (e q n K Bd D d : ℕ) : ℕ :=
  (sumF (fun u => Bd ^ u * D ^ (n - u) * GBk e q n 1 d u) (n + 1)) ^ K - (D + Bd) ^ (K * n)

/-- **The weighted count is at most `ENr / D^(K n)`.** -/
lemma wcount_le_rows {n K : ℕ} (hn : 0 < n) (e q Bd D d : ℕ) (hq : 1 ≤ q) (hD : 0 < D) :
    ∑ T ∈ (univ : Finset (Fin (K * n))).powerset,
        ((Bd : ℚ) / D) ^ T.card * (((q : ℚ) ^ xg n K d T) - 1)
      ≤ (ENr e q n K Bd D d : ℚ) / (D : ℚ) ^ (K * n) := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  set b : ℚ := (Bd : ℚ) / D
  have hb : 0 ≤ b := by positivity
  set g : Finset (Fin n) → ℚ := fun U => b ^ U.card * (q : ℚ) ^ min U.card (d - cgap n U)
  -- the sum over `T` factors over rows
  have hfac : ∑ T ∈ (univ : Finset (Fin (K * n))).powerset, b ^ T.card * (q : ℚ) ^ xg n K d T
      = (∑ U : Finset (Fin n), g U) ^ K := by
    rw [Finset.powerset_univ]
    have hT : ∀ T : Finset (Fin (K * n)), b ^ T.card * (q : ℚ) ^ xg n K d T
        = ∏ i, g (rowT T i) := by
      intro T
      simp only [g, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_rowT, xg]
    simp_rw [hT]
    rw [← Fintype.sum_equiv rowEquiv.symm (fun V => ∏ i, g (V i)) _ (fun V => by
      simp only [rowEquiv, Equiv.coe_fn_symm_mk]
      congr 1; funext i; congr 1
      exact congrFun (rowEquiv.right_inv V) i |>.symm ▸ rfl)]
    rw [show (∑ U, g U) ^ K = ∏ _i : Fin K, ∑ U, g U by simp, Finset.prod_univ_sum,
      Fintype.piFinset_univ]
  have hg0 : ∀ U, 0 ≤ g U := fun U => by positivity
  have hrow : ∑ U : Finset (Fin n), g U
      ≤ ∑ u ∈ range (n + 1), b ^ u * (GBk e q n 1 d u : ℚ) := by
    rw [← Finset.powerset_univ, sum_card_split]
    refine Finset.sum_le_sum fun u _ => ?_
    have h1 : ∑ U ∈ (univ : Finset (Fin n)).powersetCard u, g U
        = b ^ u * ((∑ U ∈ (univ : Finset (Fin n)).powersetCard u,
            q ^ (1 * min u (d - cgap n U)) : ℕ) : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun U hU => ?_
      simp only [g, (Finset.mem_powersetCard.mp hU).2, one_mul]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast row_sum_le e q 1 d u hq hn) (by positivity)
  have hall : ∑ T ∈ (univ : Finset (Fin (K * n))).powerset, b ^ T.card = (b + 1) ^ (K * n) := by
    have := Finset.sum_pow_mul_eq_add_pow b (1 : ℚ) (univ : Finset (Fin (K * n)))
    simpa using this
  have hlhs : ∑ T ∈ (univ : Finset (Fin (K * n))).powerset, b ^ T.card * (((q : ℚ) ^ xg n K d T) - 1)
      = (∑ U : Finset (Fin n), g U) ^ K - (b + 1) ^ (K * n) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hfac, hall]
  have hS : (sumF (fun u => Bd ^ u * D ^ (n - u) * GBk e q n 1 d u) (n + 1) : ℚ)
      = (D : ℚ) ^ n * ∑ u ∈ range (n + 1), b ^ u * (GBk e q n 1 d u : ℚ) := by
    rw [sumF_eq]; push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    rw [show (D : ℚ) ^ n = (D : ℚ) ^ u * (D : ℚ) ^ (n - u) by rw [← pow_add]; congr 1; omega]
    simp only [b, div_pow]; field_simp
  have hE : ((sumF (fun u => Bd ^ u * D ^ (n - u) * GBk e q n 1 d u) (n + 1) : ℕ) : ℚ) ^ K
        - (((D + Bd) ^ (K * n) : ℕ) : ℚ) ≤ (ENr e q n K Bd D d : ℚ) := by
    have := cast_sub_le_of ((sumF (fun u => Bd ^ u * D ^ (n - u) * GBk e q n 1 d u) (n + 1)) ^ K)
      ((D + Bd) ^ (K * n)) _ le_rfl
    push_cast at this ⊢; exact this
  rw [hlhs, le_div_iff₀ (by positivity)]
  refine le_trans ?_ hE
  rw [hS]; push_cast
  have hpow : ((D : ℚ) ^ n * ∑ u ∈ range (n + 1), b ^ u * (GBk e q n 1 d u : ℚ)) ^ K
      = (∑ u ∈ range (n + 1), b ^ u * (GBk e q n 1 d u : ℚ)) ^ K * (D : ℚ) ^ (K * n) := by
    rw [mul_pow, ← pow_mul, mul_comm n K]; ring
  have hDB : ((D : ℚ) + Bd) ^ (K * n) = (b + 1) ^ (K * n) * (D : ℚ) ^ (K * n) := by
    rw [← mul_pow]; congr 1; simp only [b]; field_simp; ring
  rw [hpow, hDB, ← sub_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have := pow_le_pow_left₀ (Finset.sum_nonneg fun U _ => hg0 U) hrow K
  linarith

end Rows

/-! ## The sharper second moment -/

section Sharp
variable {ζ : Fin n → ZMod q}

/-- No degenerate slot of the triple is exceptional. -/
def NX (ζ : Fin n → ZMod q) (h₀ : Fin L) (x : ((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ)) :
    Prop :=
  ∀ k ∈ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2), TailNZ ζ h₀ x.2 k ∨
    (nttP ζ (fun s => (x.1.1 s : ZMod q)) k ≠ 0 ∧ nttP ζ (fun s => (x.1.2 s : ZMod q)) k ≠ 0)

open Classical in
/-- **Sharper second moment.** Triples without exceptional degenerate slots are bounded with the
`b²`-weighted count `E₂`; the others (at most `C(n,d)((p+ε)^d − p^d)` of them with `d` degenerate
slots, hypothesis `hPexc`) with the old bound. -/
theorem var_le_sharp
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {γ₁ γ₂ β : ℕ} {v : Fin (K * n) → ℤ} {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) (hwq : w ≤ q)
    (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L)
    (bt : ℚ) (hbt : 0 ≤ bt)
    (hbad : ∀ r, ((q : ℚ) - (good (q := q) γ₂ β v r).card) ≤ bt * (good (q := q) γ₂ β v r).card)
    (dm₁ dm₂ : ℕ) (Eb₁ Eb₂ : ℕ → ℚ) (hEb₂0 : ∀ d, 0 ≤ Eb₂ d)
    (hEb₁ : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm₂ →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then bt ^ (supp ξ).card else 0) ≤ Eb₁ S.card)
    (hEb₂ : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm₁ →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then (bt ^ 2) ^ (supp ξ).card else 0) ≤ Eb₂ S.card)
    (pe : ℚ)
    (hPexc : ∀ e, 1 ≤ e → prob (trip lo w γ₁ h₀) (fun x =>
        e ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card ∧ ¬ NX ζ h₀ x)
      ≤ n.choose e * (pe ^ e - (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ e)) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2) / (tbox (n := n) γ₁ h₀).card)
      ≤ ((∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2 *
          ∑ d ∈ Icc 1 dm₁, (n.choose d * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ d)
            * Eb₂ d
        + n.choose (dm₁ + 1) * (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ (dm₁ + 1))
      + ((∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2 *
          ∑ d ∈ Icc 1 dm₂, (n.choose d * (pe ^ d - (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ d))
            * Eb₁ d ^ 2
        + n.choose (dm₂ + 1) * (pe ^ (dm₂ + 1)
            - (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ (dm₂ + 1))) := by
  set μ : ℚ := ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q with hμ
  have hμ0 : 0 ≤ μ := Finset.prod_nonneg fun r _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hμ1 : μ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun r _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      fun r _ => ?_
    have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    rw [div_le_one hq]
    exact_mod_cast (Finset.card_le_univ _).trans (by rw [ZMod.card])
  have hHB : (hbox lo w).Nonempty := by
    rw [← Finset.card_pos, card_hbox]; positivity
  have hTB : (tbox (n := n) γ₁ h₀).Nonempty := by
    rw [← Finset.card_pos, card_tbox]; positivity
  -- the covariance of one triple
  set X : (Fin K → Fin L → Fin n → ZMod q) → (((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ))
      → ℚ := fun a x =>
    ((if phiHom h (zc (join h₀ x.1.1 x.2)) a ∈ Fintype.piFinset (good (q := q) γ₂ β v)
      then (1 : ℚ) else 0) - μ) *
    ((if phiHom h (zc (join h₀ x.1.2 x.2)) a ∈ Fintype.piFinset (good (q := q) γ₂ β v)
      then (1 : ℚ) else 0) - μ) with hX
  have hgne : ∀ r, (good (q := q) γ₂ β v r).Nonempty := by
    intro r
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have := hbad r
    rw [hne, Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero] at this
    have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    linarith
  have hX1 : ∀ a x, X a x ≤ 1 := by
    intro a x
    simp only [hX]
    have hb : ∀ P : Prop, [Decidable P] → |(if P then (1 : ℚ) else 0) - μ| ≤ 1 := by
      intro P _; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    calc _ ≤ |_ * _| := le_abs_self _
      _ = _ := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hb _) (hb _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  set D : (((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ)) → ℕ := fun x =>
    (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
  set H₂ : ℕ → ℚ := fun d => ∑ e ∈ Icc 1 dm₁, (if e ≤ d then μ ^ 2 * Eb₂ e else 0)
    + (if dm₁ + 1 ≤ d then 1 else 0)
  set H₁ : ℕ → ℚ := fun d => ∑ e ∈ Icc 1 dm₂, (if e ≤ d then μ ^ 2 * Eb₁ e ^ 2 else 0)
    + (if dm₂ + 1 ≤ d then 1 else 0)
  have hH₂0 : ∀ d, 0 ≤ H₂ d := fun d => add_nonneg
    (Finset.sum_nonneg fun e _ => by split_ifs <;> [exact mul_nonneg (sq_nonneg _) (hEb₂0 e); rfl])
    (by split_ifs <;> norm_num)
  have hH₁0 : ∀ d, 0 ≤ H₁ d := fun d => add_nonneg
    (Finset.sum_nonneg fun e _ => by split_ifs <;> positivity) (by split_ifs <;> norm_num)
  set Hf : (((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ)) → ℚ := fun x =>
    H₂ (D x) + (if NX ζ h₀ x then 0 else H₁ (D x))
  have hP : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
    exact_mod_cast Fintype.card_pos
  -- trivial bound
  have htriv : ∀ x, (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ 1 := by
    intro x
    rw [div_le_iff₀ hP]
    calc ∑ a, X a x ≤ ∑ _a : Fin K → Fin L → Fin n → ZMod q, (1 : ℚ) :=
          Finset.sum_le_sum fun a _ => hX1 a x
      _ = 1 * Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by simp
  -- a generic per-triple step: `cov ≤ μ² E` with `E` bounded by `Eb` up to `dm`, trivial above
  have hstep : ∀ (dm : ℕ) (Eb : ℕ → ℚ) (E : ℚ) (H : ℕ → ℚ),
      (∀ d, H d = ∑ e ∈ Icc 1 dm, (if e ≤ d then μ ^ 2 * Eb e else 0)
        + (if dm + 1 ≤ d then 1 else 0)) → (∀ e, 0 ≤ μ ^ 2 * Eb e) →
      ∀ x, (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ μ ^ 2 * E →
      (D x = 0 → E = 0) → (1 ≤ D x → D x ≤ dm → E ≤ Eb (D x)) →
      (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ H (D x) := by
    intro dm Eb E H hH hEb0' x hmain hz hle
    have hS0 : 0 ≤ ∑ e ∈ Icc 1 dm, (if e ≤ D x then μ ^ 2 * Eb e else 0) :=
      Finset.sum_nonneg fun e _ => by split_ifs <;> [exact hEb0' e; rfl]
    have hI0 : (0 : ℚ) ≤ if dm + 1 ≤ D x then 1 else 0 := by split_ifs <;> norm_num
    rw [hH]
    rcases Nat.eq_zero_or_pos (D x) with hD | hD
    · rw [hz hD, mul_zero] at hmain; linarith
    · by_cases hdm : D x ≤ dm
      · have h1 : μ ^ 2 * E ≤ μ ^ 2 * Eb (D x) :=
          mul_le_mul_of_nonneg_left (hle hD hdm) (sq_nonneg _)
        have := Finset.single_le_sum (f := fun e => if e ≤ D x then μ ^ 2 * Eb e else 0)
          (fun e _ => by split_ifs <;> [exact hEb0' e; rfl]) (Finset.mem_Icc.mpr ⟨hD, hdm⟩)
        simp only [le_refl, if_true] at this
        linarith
      · rw [if_pos (by omega : dm + 1 ≤ D x)]; linarith [htriv x]
  have hcov : ∀ x, (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ Hf x := by
    intro x
    have hc := cov_le (phiHom h (zc (join h₀ x.1.1 x.2))) (phiHom h (zc (join h₀ x.1.2 x.2)))
      (good (q := q) γ₂ β v) hgne bt hbt hbad
    have hzero : ∀ (c : ℚ) (f : ℕ → ℚ), D x = 0 → ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)) ξ then f (supp ξ).card
          else 0) = 0 := by
      intro _ f hD
      refine Finset.sum_eq_zero fun ξ hξ => ?_
      rw [if_neg]
      intro hd
      have hS : degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) = ∅ := Finset.card_eq_zero.mp hD
      rw [hS] at hd
      exact (Finset.mem_erase.mp hξ).1 (dualIn_empty h.inj ξ hd)
    by_cases hnx : NX ζ h₀ x
    · -- sharp branch
      have hpair := pair_sum_le (K := K) h₀ x.1.1 x.1.2 x.2 h hnx hbt
      have hmain := (le_abs_self _).trans (hc.trans (mul_le_mul_of_nonneg_left hpair (sq_nonneg _)))
      have := hstep dm₁ Eb₂ _ H₂ (fun d => rfl) (fun e => mul_nonneg (sq_nonneg _) (hEb₂0 e)) x
        hmain (fun hD => hzero 0 (fun m => (bt ^ 2) ^ m) hD) (fun h1 h2 => hEb₂ _ h1 h2)
      simp only [Hf, if_pos hnx, add_zero]; exact this
    · -- old branch
      set Ew : ℚ := ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)) ξ then bt ^ (supp ξ).card
          else 0) with hEw
      have hEw0 : 0 ≤ Ew := Finset.sum_nonneg fun ξ _ => by split_ifs <;> positivity
      have hpair : (∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
          ∑ ξ' ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
            if (∀ a, ξ ⬝ᵥ phiHom h (zc (join h₀ x.1.1 x.2)) a
                + ξ' ⬝ᵥ phiHom h (zc (join h₀ x.1.2 x.2)) a = 0) then
              bt ^ ((univ.filter fun r => ξ r ≠ 0).card + (univ.filter fun r => ξ' r ≠ 0).card)
            else 0) ≤ Ew ^ 2 := by
        rw [sq, hEw, Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun ξ _ => Finset.sum_le_sum fun ξ' _ => ?_
        split_ifs with ho h1 h2 h2 h1 h2 h2
        · rw [pow_add]; rfl
        · exact absurd (dualIn_of_orth h _ _ ξ ξ' ho).2 h2
        · exact absurd (dualIn_of_orth h _ _ ξ ξ' ho).1 h1
        · exact absurd (dualIn_of_orth h _ _ ξ ξ' ho).1 h1
        all_goals first | positivity | simp
      have hmain := (le_abs_self _).trans (hc.trans (mul_le_mul_of_nonneg_left hpair (sq_nonneg _)))
      have := hstep dm₂ (fun e => Eb₁ e ^ 2) _ H₁ (fun d => rfl) (fun e => by positivity) x hmain
        (fun hD => by rw [hEw, hzero 0 (fun m => bt ^ m) hD]; ring)
        (fun h1 h2 => pow_le_pow_left₀ hEw0 (hEb₁ _ h1 h2) 2)
      simp only [Hf, if_neg hnx]; linarith [hH₂0 (D x)]
  have hHBc : (0 : ℚ) < (hbox lo w).card := by exact_mod_cast hHB.card_pos
  have hTBc : (0 : ℚ) < (tbox (n := n) γ₁ h₀).card := by exact_mod_cast hTB.card_pos
  have htrip : ((trip lo w γ₁ h₀).card : ℚ)
      = (hbox lo w).card * (hbox lo w).card * (tbox (n := n) γ₁ h₀).card := by
    rw [trip, card_product, card_product]; push_cast; ring
  have htripc : (0 : ℚ) < (trip lo w γ₁ h₀).card := by rw [htrip]; positivity
  have hPc : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
    exact_mod_cast Fintype.card_pos
  -- rewrite the inner average as an average over triples
  have hsumtrip : ∀ a, ∑ x ∈ trip lo w γ₁ h₀, X a x
      = ∑ t ∈ tbox γ₁ h₀, ∑ y₁ ∈ hbox lo w, ∑ y₁' ∈ hbox lo w, X a ((y₁, y₁'), t) := by
    intro a
    rw [trip, Finset.sum_product_right]
    simp_rw [Finset.sum_product]
  have step1 : ∀ a, (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2)
      / (tbox (n := n) γ₁ h₀).card = (∑ x ∈ trip lo w γ₁ h₀, X a x) / (trip lo w γ₁ h₀).card := by
    intro a
    have e1 : ∀ t, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2
        = (∑ y₁ ∈ hbox lo w, ∑ y₁' ∈ hbox lo w, X a ((y₁, y₁'), t)) / ((hbox lo w).card : ℚ) ^ 2 :=
      fun t => sq_prob (hbox lo w) hHB _ μ
    simp_rw [e1]
    rw [← Finset.sum_div, hsumtrip, htrip]
    field_simp
  set pp : ℚ := 1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)
  have hprobs : ∀ e, ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card : ℚ))
      / (trip lo w γ₁ h₀).card ≤ n.choose e * pp ^ e :=
    fun e => prob_deg_ge h.inj hw0 hwq hγ1 hγ h₀ e
  have hprobs' : ∀ e, 1 ≤ e → ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x ∧ ¬ NX ζ h₀ x).card
      : ℚ)) / (trip lo w γ₁ h₀).card ≤ n.choose e * (pe ^ e - pp ^ e) :=
    fun e he => hPexc e he
  have hsplit : ∑ x ∈ trip lo w γ₁ h₀, Hf x
      = (∑ e ∈ Icc 1 dm₁, μ ^ 2 * Eb₂ e * (((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card : ℚ)
        + (((trip lo w γ₁ h₀).filter fun x => dm₁ + 1 ≤ D x).card : ℚ))
      + (∑ e ∈ Icc 1 dm₂, μ ^ 2 * Eb₁ e ^ 2
          * (((trip lo w γ₁ h₀).filter fun x => e ≤ D x ∧ ¬ NX ζ h₀ x).card : ℚ)
        + (((trip lo w γ₁ h₀).filter fun x => dm₂ + 1 ≤ D x ∧ ¬ NX ζ h₀ x).card : ℚ)) := by
    simp only [Hf, H₂, H₁, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      congr 1
      · refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      · rw [Finset.sum_boole]
    · have : ∀ x, (if NX ζ h₀ x then (0 : ℚ) else
          ∑ e ∈ Icc 1 dm₂, (if e ≤ D x then μ ^ 2 * Eb₁ e ^ 2 else 0)
            + (if dm₂ + 1 ≤ D x then 1 else 0))
          = ∑ e ∈ Icc 1 dm₂, (if e ≤ D x ∧ ¬ NX ζ h₀ x then μ ^ 2 * Eb₁ e ^ 2 else 0)
            + (if dm₂ + 1 ≤ D x ∧ ¬ NX ζ h₀ x then 1 else 0) := by
        intro x
        by_cases hn : NX ζ h₀ x
        · simp [hn]
        · simp only [hn, if_false, not_false_eq_true, and_true]
      simp_rw [this, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      · refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      · rw [Finset.sum_boole]
  unfold avg
  simp_rw [step1]
  calc (∑ a, (∑ x ∈ trip lo w γ₁ h₀, X a x) / (trip lo w γ₁ h₀).card)
        / Fintype.card (Fin K → Fin L → Fin n → ZMod q)
      = (∑ x ∈ trip lo w γ₁ h₀, (∑ a, X a x) / Fintype.card (Fin K → Fin L → Fin n → ZMod q))
        / (trip lo w γ₁ h₀).card := by
        rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]; ring
    _ ≤ (∑ x ∈ trip lo w γ₁ h₀, Hf x) / (trip lo w γ₁ h₀).card :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hcov x) htripc.le
    _ = (∑ e ∈ Icc 1 dm₁, μ ^ 2 * Eb₂ e * ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card
          : ℚ) / (trip lo w γ₁ h₀).card)
        + (((trip lo w γ₁ h₀).filter fun x => dm₁ + 1 ≤ D x).card : ℚ) / (trip lo w γ₁ h₀).card)
        + (∑ e ∈ Icc 1 dm₂, μ ^ 2 * Eb₁ e ^ 2
          * ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x ∧ ¬ NX ζ h₀ x).card : ℚ)
            / (trip lo w γ₁ h₀).card)
        + (((trip lo w γ₁ h₀).filter fun x => dm₂ + 1 ≤ D x ∧ ¬ NX ζ h₀ x).card : ℚ)
          / (trip lo w γ₁ h₀).card) := by
        rw [hsplit, add_div, add_div, add_div, Finset.sum_div, Finset.sum_div]
        congr 2 <;> refine Finset.sum_congr rfl fun e _ => ?_ <;> ring
    _ ≤ _ := by
        refine add_le_add (add_le_add ?_ (hprobs (dm₁ + 1)))
          (add_le_add ?_ (hprobs' (dm₂ + 1) (by omega)))
        · rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun e _ => ?_
          rw [show μ ^ 2 * ((n.choose e : ℚ) * pp ^ e * Eb₂ e)
              = μ ^ 2 * Eb₂ e * ((n.choose e : ℚ) * pp ^ e) by ring]
          exact mul_le_mul_of_nonneg_left (hprobs e) (mul_nonneg (sq_nonneg _) (hEb₂0 e))
        · rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun e he => ?_
          rw [show μ ^ 2 * ((n.choose e : ℚ) * (pe ^ e - pp ^ e) * Eb₁ e ^ 2)
              = μ ^ 2 * Eb₁ e ^ 2 * ((n.choose e : ℚ) * (pe ^ e - pp ^ e)) by ring]
          exact mul_le_mul_of_nonneg_left (hprobs' e (Finset.mem_Icc.mp he).1) (by positivity)

/-- Exceptional degenerate slots exist exactly when `NX` fails. -/
lemma not_NX_exc {ζ : Fin n → ZMod q} (h₀ : Fin L)
    (x : ((Fin n → ℤ) × (Fin n → ℤ)) × (Fin L → Fin n → ℤ)) (hx : ¬ NX ζ h₀ x) :
    (exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty := by
  unfold NX at hx
  push Not at hx
  obtain ⟨k, -, hT, hH⟩ := hx
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_, ?_⟩⟩
  · by_contra hne; exact hT ⟨j, hj, hne⟩
  · by_contra hne; push Not at hne; exact hne.2 (hH hne.1)

/-- The kernel-checked sum for the sharper bound. -/
def numL2 (e q n K Bd Dc pn pn' pd dm₁ dm₂ M : ℕ) : ℕ :=
  sumF (fun d => if 1 ≤ d then chooseC n d * pn ^ d * pd ^ (M - d)
      * ENr e q n K (Bd ^ 2) (Dc ^ 2) d else 0) (dm₁ + 1)
    + chooseC n (dm₁ + 1) * pn ^ (dm₁ + 1) * pd ^ (M - (dm₁ + 1)) * q ^ (2 * (K * n))
    + sumF (fun d => if 1 ≤ d then chooseC n d * (pn' ^ d - pn ^ d) * pd ^ (M - d)
      * ENr e q n K Bd Dc d ^ 2 else 0) (dm₂ + 1)
    + chooseC n (dm₂ + 1) * (pn' ^ (dm₂ + 1) - pn ^ (dm₂ + 1)) * pd ^ (M - (dm₂ + 1))
      * q ^ (2 * (K * n))

end Sharp


section SharpFinal
variable {ζ : Fin n → ZMod q}

lemma sumF_ite_Icc (dm : ℕ) (f : ℕ → ℚ) :
    ∑ x ∈ range (dm + 1), (if 1 ≤ x then f x else 0) = ∑ d ∈ Icc 1 dm, f d := by
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (by ext d; simp [Finset.mem_Icc]; omega) fun d _ => rfl

open Classical in
/-- **Relative second moment, sharper.** -/
theorem var_rel_sharp
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {cz : ZMod q} (hwz : ∀ k, ζ k ^ n = cz) (hn : 0 < n)
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) (hwq : w ≤ q) (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (e dm₁ dm₂ M k : ℕ)
    (hM₁ : dm₁ + 1 ≤ M) (hM₂ : dm₂ + 1 ≤ M)
    (hnum : 2 ^ k * numL2 e q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        ((2 * γ₁) ^ (L - 1) + w) ((2 * γ₁) ^ (L - 1) + w + 2) (w * (2 * γ₁) ^ (L - 1))
        dm₁ dm₂ M
      ≤ (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n)) * (w * (2 * γ₁) ^ (L - 1)) ^ M) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2) / (tbox (n := n) γ₁ h₀).card)
      ≤ (∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2 / 2 ^ k := by
  set Dc := mb * (2 * (γ₂ - β) - 1) with hDc
  set Bd := q - Dc with hBd
  have hDcq : Dc ≤ q := pass_le_q hp
  have hDc0 : 0 < Dc := by
    have h1 := hp.mb_pos; have h2 := hp.β_lt_γ₂
    exact Nat.mul_pos h1 (by omega)
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hDc' : (0 : ℚ) < Dc := by exact_mod_cast hDc0
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq1
  set bt : ℚ := (Bd : ℚ) / Dc
  have hgood : ∀ r, ((good (q := q) γ₂ β v r).card : ℚ) = Dc := fun r => by
    rw [card_good hp hv r]
  have hμ : ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q = ((Dc : ℚ) / q) ^ (K * n) := by
    simp_rw [hgood]; rw [Finset.prod_const, card_univ, Fintype.card_fin]
  have hbad : ∀ r, ((q : ℚ) - (good (q := q) γ₂ β v r).card) ≤ bt * (good (q := q) γ₂ β v r).card := by
    intro r; rw [hgood]
    simp only [bt, hBd]; rw [Nat.cast_sub hDcq]; field_simp; rfl
  have hEb₁ : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm₂ →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then bt ^ (supp ξ).card else 0)
        ≤ (ENr e q n K Bd Dc S.card : ℚ) / (Dc : ℚ) ^ (K * n) :=
    fun S _ _ => (wsum_le h.inj h.ne0 hwz S (by positivity)).trans
      (wcount_le_rows hn e q Bd Dc S.card hq1 hDc0)
  have hbt2 : bt ^ 2 = ((Bd ^ 2 : ℕ) : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) := by
    simp only [bt]; push_cast; rw [div_pow]
  have hEb₂ : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm₁ →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then (bt ^ 2) ^ (supp ξ).card else 0)
        ≤ (ENr e q n K (Bd ^ 2) (Dc ^ 2) S.card : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) ^ (K * n) := by
    intro S _ _
    rw [hbt2]
    exact (wsum_le h.inj h.ne0 hwz S (by positivity)).trans
      (wcount_le_rows hn e q (Bd ^ 2) (Dc ^ 2) S.card hq1 (by positivity))
  have hPexc : ∀ e', 1 ≤ e' → prob (trip lo w γ₁ h₀) (fun x =>
        e' ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card ∧ ¬ NX ζ h₀ x)
      ≤ n.choose e' * ((1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)
          + 2 / ((w : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ e'
        - (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ e') := by
    intro e' he'
    exact (prob_mono _ fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans
      (prob_deg_exc h.inj hw0 hwq hγ1 hγ h₀ e' he')
  refine (var_le_sharp h hw0 hwq hγ1 hγ h₀ bt (by positivity) hbad dm₁ dm₂
    (fun d => (ENr e q n K Bd Dc d : ℚ) / (Dc : ℚ) ^ (K * n))
    (fun d => (ENr e q n K (Bd ^ 2) (Dc ^ 2) d : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) ^ (K * n))
    (fun d => by positivity) hEb₁ hEb₂ _ hPexc).trans ?_
  rw [hμ]
  -- pure arithmetic from `hnum`
  set pn : ℕ := (2 * γ₁) ^ (L - 1) + w
  set pn' : ℕ := (2 * γ₁) ^ (L - 1) + w + 2
  set pd : ℕ := w * (2 * γ₁) ^ (L - 1)
  have hpd : (0 : ℚ) < pd := by positivity
  have hp_eq : 1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1) = (pn : ℚ) / pd := by
    simp only [pn, pd]; push_cast; field_simp
  have hpe_eq : (pn : ℚ) / pd + 2 / ((w : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1)) = (pn' : ℚ) / pd := by
    simp only [pn, pn', pd]; push_cast; field_simp
  rw [hp_eq, hpe_eq]
  have hQ : (0 : ℚ) < (q : ℚ) ^ (2 * (K * n)) := by positivity
  have hDn : (0 : ℚ) < (Dc : ℚ) ^ (K * n) := by positivity
  set Q : ℚ := (q : ℚ) ^ (2 * (K * n))
  have hμ2 : (((Dc : ℚ) / q) ^ (K * n)) ^ 2 = (Dc : ℚ) ^ (2 * (K * n)) / Q := by
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm (K * n) 2]
  have hsplit : ∀ d, d ≤ M → (pd : ℚ) ^ M = (pd : ℚ) ^ d * (pd : ℚ) ^ (M - d) := fun d hd => by
    rw [← pow_add]; congr 1; omega
  have hle : ∀ d, pn ^ d ≤ pn' ^ d := fun d => Nat.pow_le_pow_left (by omega) d
  -- the four parts of `numL2`, as rationals over `Q · pd^M`
  set A₁ : ℚ := ∑ d ∈ Icc 1 dm₁, (n.choose d : ℚ) * (pn : ℚ) ^ d * (pd : ℚ) ^ (M - d)
    * (ENr e q n K (Bd ^ 2) (Dc ^ 2) d : ℚ)
  set A₂ : ℚ := (n.choose (dm₁ + 1) : ℚ) * (pn : ℚ) ^ (dm₁ + 1) * (pd : ℚ) ^ (M - (dm₁ + 1)) * Q
  set A₃ : ℚ := ∑ d ∈ Icc 1 dm₂, (n.choose d : ℚ) * (((pn' : ℚ) ^ d - (pn : ℚ) ^ d))
    * (pd : ℚ) ^ (M - d) * (ENr e q n K Bd Dc d : ℚ) ^ 2
  set A₄ : ℚ := (n.choose (dm₂ + 1) : ℚ) * ((pn' : ℚ) ^ (dm₂ + 1) - (pn : ℚ) ^ (dm₂ + 1))
    * (pd : ℚ) ^ (M - (dm₂ + 1)) * Q
  have hnumQ : (2 : ℚ) ^ k * (A₁ + A₂ + A₃ + A₄) ≤ (Dc : ℚ) ^ (2 * (K * n)) * (pd : ℚ) ^ M := by
    have := (Nat.cast_le (α := ℚ)).mpr hnum
    unfold numL2 at this
    rw [sumF_eq, sumF_eq] at this
    push_cast at this
    simp only [Nat.cast_ite, Nat.cast_zero, Nat.cast_mul, Nat.cast_pow, chooseC_eq,
      Nat.cast_sub (hle _)] at this
    rw [sumF_ite_Icc, sumF_ite_Icc] at this
    convert this using 3
  have e1 : (Dc : ℚ) ^ (2 * (K * n)) / Q * ∑ d ∈ Icc 1 dm₁,
      ((n.choose d : ℚ) * ((pn : ℚ) / pd) ^ d) *
        ((ENr e q n K (Bd ^ 2) (Dc ^ 2) d : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) ^ (K * n))
      = A₁ / (Q * (pd : ℚ) ^ M) := by
    simp only [A₁]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hsplit d (by have := (Finset.mem_Icc.mp hd).2; omega)]
    push_cast
    rw [← pow_mul, show 2 * (K * n) = (K * n) * 2 by ring, pow_mul]
    simp only [div_pow]
    field_simp
  have e3 : (Dc : ℚ) ^ (2 * (K * n)) / Q * ∑ d ∈ Icc 1 dm₂,
      ((n.choose d : ℚ) * (((pn' : ℚ) / pd) ^ d - ((pn : ℚ) / pd) ^ d)) *
        ((ENr e q n K Bd Dc d : ℚ) / (Dc : ℚ) ^ (K * n)) ^ 2
      = A₃ / (Q * (pd : ℚ) ^ M) := by
    simp only [A₃]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hsplit d (by have := (Finset.mem_Icc.mp hd).2; omega)]
    rw [show 2 * (K * n) = (K * n) * 2 by ring, pow_mul]
    simp only [div_pow]
    field_simp
  have e2 : (n.choose (dm₁ + 1) : ℚ) * ((pn : ℚ) / pd) ^ (dm₁ + 1) = A₂ / (Q * (pd : ℚ) ^ M) := by
    rw [hsplit (dm₁ + 1) hM₁, div_pow]; field_simp; simp only [A₂]; ring
  have e4 : (n.choose (dm₂ + 1) : ℚ) * (((pn' : ℚ) / pd) ^ (dm₂ + 1) - ((pn : ℚ) / pd) ^ (dm₂ + 1))
      = A₄ / (Q * (pd : ℚ) ^ M) := by
    rw [hsplit (dm₂ + 1) hM₂, div_pow, div_pow]; field_simp; simp only [A₄]; ring
  rw [hμ2, e1, e2, e3, e4, ← add_div, ← add_div, ← add_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  rw [show (A₁ + A₂ + (A₃ + A₄)) = A₁ + A₂ + A₃ + A₄ by ring]
  rw [show (Dc : ℚ) ^ (2 * (K * n)) / Q * (Q * (pd : ℚ) ^ M)
      = (Dc : ℚ) ^ (2 * (K * n)) * (pd : ℚ) ^ M by field_simp]
  linarith [hnumQ]

/-- **First moment, sharper.** -/
theorem dev_rel_sharp {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {cz : ZMod q} (hwz : ∀ k, ζ k ^ n = cz) (hn : 0 < n)
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) (hwq : w ≤ q) (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (e dm₁ dm₂ M j : ℕ)
    (hM₁ : dm₁ + 1 ≤ M) (hM₂ : dm₂ + 1 ≤ M)
    (hnum : 2 ^ (2 * j) * numL2 e q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        ((2 * γ₁) ^ (L - 1) + w) ((2 * γ₁) ^ (L - 1) + w + 2) (w * (2 * γ₁) ^ (L - 1))
        dm₁ dm₂ M
      ≤ (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n)) * (w * (2 * γ₁) ^ (L - 1)) ^ M) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, |rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q|) / (tbox (n := n) γ₁ h₀).card)
      ≤ (∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) / 2 ^ j := by
  set μ := ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q with hμ
  have hvar := var_rel_sharp (lo := lo) h hwz hn hp hv hw0 hwq hγ1 hγ h₀ e dm₁ dm₂ M (2 * j)
    hM₁ hM₂ hnum
  rw [← hμ] at hvar
  have hμ0 : 0 < μ := by
    refine Finset.prod_pos fun r _ => div_pos ?_ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))
    rw [card_good hp hv r]
    have h1 := hp.mb_pos; have h2 := hp.β_lt_γ₂
    exact_mod_cast Nat.mul_pos h1 (by omega)
  set η : ℚ := μ / 2 ^ j
  have hη : 0 < η := div_pos hμ0 (pow_pos two_pos j)
  have hpt : ∀ x : ℚ, |x| ≤ (x ^ 2 / η + η) / 2 := by
    intro x
    have : 0 ≤ (|x| - η) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
    rw [sub_sq, sq_abs] at this
    have e1 : (x ^ 2 - 2 * |x| * η + η ^ 2) / η = x ^ 2 / η - 2 * |x| + η := by
      field_simp
    linarith
  have hTB : (0 : ℚ) < (tbox (n := n) γ₁ h₀).card := by
    rw [card_tbox]; have : 0 < 2 * γ₁ := by omega
    positivity
  calc avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, |rhoC mulmat γ₂ β v lo w h₀ a t - μ|) / (tbox (n := n) γ₁ h₀).card)
      ≤ avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        ((∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2)
          / (tbox (n := n) γ₁ h₀).card / η + η) / 2) := by
        refine avg_mono fun a => ?_
        rw [div_le_iff₀ hTB]
        have : ∑ t ∈ tbox γ₁ h₀, |rhoC mulmat γ₂ β v lo w h₀ a t - μ|
            ≤ ∑ t ∈ tbox γ₁ h₀, ((rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2 / η + η) / 2 :=
          Finset.sum_le_sum fun t _ => hpt _
        refine this.trans (le_of_eq ?_)
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
          nsmul_eq_mul]
        field_simp
    _ = (avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
          (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t - μ) ^ 2)
            / (tbox (n := n) γ₁ h₀).card) / η + η) / 2 := by
        unfold avg
        rw [Finset.sum_div, Finset.sum_div]
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, card_univ,
          nsmul_eq_mul]
        have : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
          exact_mod_cast Fintype.card_pos
        field_simp
    _ ≤ (μ ^ 2 / 2 ^ (2 * j) / η + η) / 2 := by
        have := div_le_div_of_nonneg_right hvar hη.le
        linarith
    _ = η := by
        have hμne : μ ≠ 0 := hμ0.ne'
        rw [show η = μ / 2 ^ j from rfl, pow_mul]
        field_simp
        rw [← pow_mul, ← pow_mul, mul_comm j 2]
        ring


end SharpFinal

/-! ## ML-DSA -/

section MLDSASharp
set_option maxRecDepth 100000

/-- The kernel-checked inequality for 44, full head box. -/
theorem num_44_full : 2 ^ (2 * 147) * numL2 330 8380417 256 4 (8380417 - 44 * (2 * (95232 - 78) - 1))
    (44 * (2 * (95232 - 78) - 1)) ((2 * 2 ^ 17) ^ (4 - 1) + (2 * 2 ^ 17)) ((2 * 2 ^ 17) ^ (4 - 1) + (2 * 2 ^ 17) + 2)
    ((2 * 2 ^ 17) * (2 * 2 ^ 17) ^ (4 - 1)) 25 19 26
  ≤ (44 * (2 * (95232 - 78) - 1)) ^ (2 * (4 * 256)) * ((2 * 2 ^ 17) * (2 * 2 ^ 17) ^ (4 - 1)) ^ 26 := by
  decide +kernel

/-- The kernel-checked inequality for 44, z head box. -/
theorem num_44_z : 2 ^ (2 * 147) * numL2 330 8380417 256 4 (8380417 - 44 * (2 * (95232 - 78) - 1))
    (44 * (2 * (95232 - 78) - 1)) ((2 * 2 ^ 17) ^ (4 - 1) + (2 * (2 ^ 17 - 78) - 1)) ((2 * 2 ^ 17) ^ (4 - 1) + (2 * (2 ^ 17 - 78) - 1) + 2)
    ((2 * (2 ^ 17 - 78) - 1) * (2 * 2 ^ 17) ^ (4 - 1)) 25 19 26
  ≤ (44 * (2 * (95232 - 78) - 1)) ^ (2 * (4 * 256)) * ((2 * (2 ^ 17 - 78) - 1) * (2 * 2 ^ 17) ^ (4 - 1)) ^ 26 := by
  decide +kernel

/-- **ML-DSA-44, sharper.** `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^147`. -/
theorem dev_mldsa44_sharp {v : Fin (4 * 256) → ℤ} (hv : Bounded 78 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 17 ∨ w = 2 * (2 ^ 17 - 78) - 1) (h₀ : Fin 4) :
    avg (fun a : Fin 4 → Fin 4 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 17) h₀, |rhoC (negacyclic (q := 8380417) (n := 256)) 95232 78 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417|)
          / (tbox (n := 256) (2 ^ 17) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) / 2 ^ 147 := by
  rcases hw with rfl | rfl
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 25 19 26 147
      (by norm_num) (by norm_num) num_44_full
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 25 19 26 147
      (by norm_num) (by norm_num) num_44_z

/-- The kernel-checked inequality for 65, full head box. -/
theorem num_65_full : 2 ^ (2 * 182) * numL2 330 8380417 256 6 (8380417 - 16 * (2 * (261888 - 196) - 1))
    (16 * (2 * (261888 - 196) - 1)) ((2 * 2 ^ 19) ^ (5 - 1) + (2 * 2 ^ 19)) ((2 * 2 ^ 19) ^ (5 - 1) + (2 * 2 ^ 19) + 2)
    ((2 * 2 ^ 19) * (2 * 2 ^ 19) ^ (5 - 1)) 26 19 27
  ≤ (16 * (2 * (261888 - 196) - 1)) ^ (2 * (6 * 256)) * ((2 * 2 ^ 19) * (2 * 2 ^ 19) ^ (5 - 1)) ^ 27 := by
  decide +kernel

/-- The kernel-checked inequality for 65, z head box. -/
theorem num_65_z : 2 ^ (2 * 182) * numL2 330 8380417 256 6 (8380417 - 16 * (2 * (261888 - 196) - 1))
    (16 * (2 * (261888 - 196) - 1)) ((2 * 2 ^ 19) ^ (5 - 1) + (2 * (2 ^ 19 - 196) - 1)) ((2 * 2 ^ 19) ^ (5 - 1) + (2 * (2 ^ 19 - 196) - 1) + 2)
    ((2 * (2 ^ 19 - 196) - 1) * (2 * 2 ^ 19) ^ (5 - 1)) 26 19 27
  ≤ (16 * (2 * (261888 - 196) - 1)) ^ (2 * (6 * 256)) * ((2 * (2 ^ 19 - 196) - 1) * (2 * 2 ^ 19) ^ (5 - 1)) ^ 27 := by
  decide +kernel

/-- **ML-DSA-65, sharper.** `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^182`. -/
theorem dev_mldsa65_sharp {v : Fin (6 * 256) → ℤ} (hv : Bounded 196 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 196) - 1) (h₀ : Fin 5) :
    avg (fun a : Fin 6 → Fin 5 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, |rhoC (negacyclic (q := 8380417) (n := 256)) 261888 196 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417|)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) / 2 ^ 182 := by
  rcases hw with rfl | rfl
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 26 19 27 182
      (by norm_num) (by norm_num) num_65_full
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 26 19 27 182
      (by norm_num) (by norm_num) num_65_z

/-- The kernel-checked inequality for 87, full head box. -/
theorem num_87_full : 2 ^ (2 * 190) * numL2 330 8380417 256 8 (8380417 - 16 * (2 * (261888 - 120) - 1))
    (16 * (2 * (261888 - 120) - 1)) ((2 * 2 ^ 19) ^ (7 - 1) + (2 * 2 ^ 19)) ((2 * 2 ^ 19) ^ (7 - 1) + (2 * 2 ^ 19) + 2)
    ((2 * 2 ^ 19) * (2 * 2 ^ 19) ^ (7 - 1)) 27 17 28
  ≤ (16 * (2 * (261888 - 120) - 1)) ^ (2 * (8 * 256)) * ((2 * 2 ^ 19) * (2 * 2 ^ 19) ^ (7 - 1)) ^ 28 := by
  decide +kernel

/-- The kernel-checked inequality for 87, z head box. -/
theorem num_87_z : 2 ^ (2 * 190) * numL2 330 8380417 256 8 (8380417 - 16 * (2 * (261888 - 120) - 1))
    (16 * (2 * (261888 - 120) - 1)) ((2 * 2 ^ 19) ^ (7 - 1) + (2 * (2 ^ 19 - 120) - 1)) ((2 * 2 ^ 19) ^ (7 - 1) + (2 * (2 ^ 19 - 120) - 1) + 2)
    ((2 * (2 ^ 19 - 120) - 1) * (2 * 2 ^ 19) ^ (7 - 1)) 27 17 28
  ≤ (16 * (2 * (261888 - 120) - 1)) ^ (2 * (8 * 256)) * ((2 * (2 ^ 19 - 120) - 1) * (2 * 2 ^ 19) ^ (7 - 1)) ^ 28 := by
  decide +kernel

/-- **ML-DSA-87, sharper.** `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^190`. -/
theorem dev_mldsa87_sharp {v : Fin (8 * 256) → ℤ} (hv : Bounded 120 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 120) - 1) (h₀ : Fin 7) :
    avg (fun a : Fin 8 → Fin 7 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, |rhoC (negacyclic (q := 8380417) (n := 256)) 261888 120 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417|)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) / 2 ^ 190 := by
  rcases hw with rfl | rfl
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 17 28 190
      (by norm_num) (by norm_num) num_87_full
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 17 28 190
      (by norm_num) (by norm_num) num_87_z

end MLDSASharp


end AltR0

end

end AltR0SharpPart

section AltR0FinalPart

/-!
# alt-r0 for ML-DSA: end to end

`Bathwater.lean` computes the output law of `alt-r0` with a set `H` of resampled coordinates
(`Bathwater.altR0Set_law`) and bounds its distance to vanilla signing in terms of the relative mean
deviation `dev` of `ρ` (the r₀ pass probability with the `H` part fresh) from a constant `μ₀`
(`Bathwater.altR0Set_close`). `AltR0.lean` bounds `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^j` for ML-DSA, for
every `c·s₂`, every head box and every head index (`AltR0.dev_mldsa44_sharp` etc., in `AltR0Sharp.lean`). This file joins the
two.

## The instance

Nonces are `y : Fin L → V` with `V = box γ₁ n` (polynomials with coefficients in `(-γ₁, γ₁]`), the
challenge ranges over any finite nonempty type `C`, and `u c = c·s₁`, `v c = c·s₂` are bounded by
`β`. `r0 a y c` is the r₀ check `A·y ∈ ∏ good(c·s₂)`, `zok y c` the z check `‖y + c·s₁‖∞ < γ₁ − β`,
`H = {h₀}` (on an r₀ failure only `y_{h₀}` is resampled). `μ = (mb·(2(γ₂−β)−1)/q)^{Kn}` and
`p_z = ((2(γ₁−β)−1)/(2γ₁))^{Ln}`. For a matrix `a`,
* `X a  = E_c E_t |ρ_c(t) − μ|` with the head ranging over the full box, and
* `Xz a = E_c E_t |ρ_c(t) − μ|` with the head ranging over the z-passing box
  `[−(γ₁−β)+1−u, γ₁−β−u)` (shifted by `c·s₁`),
where `t` is uniform on the tail box `AltR0.tbox` and `ρ_c = AltR0.rhoC`.

## The glue

1. `dev_le`: `dev ≤ X / μ`. Bathwater's `ρ y` for `H = {h₀}` is `E_c ρ_c(tail y)` (`rho_eq`), a sum
   over nonces of a function of `(head, tail)` is a sum over `box × tbox` (`sum_split`), and
   `|E_c f − μ| ≤ E_c |f − μ|`.
2. `pacc_ge`: vanilla's acceptance probability is at least `μ p_z − Xz`. For each `c` the z check
   splits into a head and a tail condition (`zok_join`); on z-passing tails the head ranges over
   the shifted z box, where `ρ_c ≥ μ − |ρ_c − μ|`; the z-passing tails number
   `(2(γ₁−β)−1)^{n(L−1)}` (`card_ztail`), which gives exactly `p_z` (`pz_eq`).
3. `close`: plugging 1 and 2 into `altR0Set_close` with `μ₀ = μ` (its bound increases with `dev`
   and decreases with `pacc`): if `D = μ p_z − Xz − X > 0`, alt-r0's output law is within `2X/D` of
   vanilla's in `ℓ¹`, and it fails to terminate with probability at most `X/D`.
4. `avg_X_le`, `avg_Xz_le`: averaging over `a` commutes with averaging over `c`, so
   `dev_mldsa*_sharp` gives `E_a X ≤ μ/2^j` and `E_a Xz ≤ μ/2^j`.
5. `main`: by Markov, at most a `2·2^{-j}/ε` fraction of matrices are `Bad` (`X ≥ με` or
   `Xz ≥ με`); for all others `D ≥ μ(p_z − 2ε)`, so the `ℓ¹` distance is at most
   `2ε/(p_z − 2ε)` and the non-termination probability at most `ε/(p_z − 2ε)`.

## Results

`altR0_mldsa44_eps` (and 65, 87) state `main` for each parameter set with any `ε`;
`altR0_mldsa44` takes `ε = 2^-60` and uses `p_z ≥ 27/50` (`pz_ge_44`, checked by the kernel):

* at most a `2^-62` fraction of matrices are bad, and
* for every other matrix, `∑ |altLaw − vanLaw| ≤ 2^-58` (statistical distance `≤ 2^-59`), and the
  non-termination probability is `≤ 2^-59`.

ML-DSA-65 (`ε = 2^-72`, `p_z ≥ 3/5`): bad fraction `≤ 2^-72`, `ℓ¹ ≤ 2^-70`, non-termination
`≤ 2^-71`. ML-DSA-87 (`ε = 2^-66`, `p_z ≥ 3/5`): bad fraction `≤ 2^-66`, `ℓ¹ ≤ 2^-64`,
non-termination `≤ 2^-65`.

Here `altLaw` is the limit of the output distribution of the alt-r0 loop
(`Bathwater.altR0Set_law`) and `vanLaw` that of vanilla signing (`Bathwater.vanilla_law`), both
in the `Trans` hybrid (fresh uniform challenge in every attempt). The statements hold for every
key (`u`, `v` are arbitrary bounded families), every head index `h₀` and every challenge set.
-/

open Finset Matrix

noncomputable section

namespace AltR0Final
open RejOrder

/-! ## The instance -/

/-- The nonce space of one polynomial: coefficients in `(-γ₁, γ₁]`. -/
abbrev V (γ₁ n : ℕ) := ↥(RejOrder.box γ₁ n)

instance instNonemptyV (γ₁ n : ℕ) [NeZero γ₁] : Nonempty (V γ₁ n) :=
  ⟨⟨0, AltR0.zero_mem_box (Nat.pos_of_ne_zero (NeZero.ne γ₁))⟩⟩

section General

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ} {C : Type*} [Fintype C]

/-- A nonce `y ∈ V^L` as an integer vector of length `L·n`. -/
def flat (γ₁ : ℕ) (y : Fin L → V γ₁ n) : Fin (L * n) → ℤ :=
  fun c' => (y (finProdFinEquiv.symm c').1).1 (finProdFinEquiv.symm c').2

/-- The tail of a nonce: the head block `h₀` is set to `0`. -/
def tailOf (γ₁ : ℕ) (h₀ : Fin L) (y : Fin L → V γ₁ n) : Fin L → Fin n → ℤ :=
  fun j => if j = h₀ then 0 else (y j).1

/-- The r₀ check `‖LowBits(A·y − c·s₂)‖∞ < γ₂ − β`, with `v c = c·s₂`. -/
def r0 (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β : ℕ)
    (v : C → Fin (K * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q) (y : Fin L → V γ₁ n)
    (c : C) : Bool :=
  decide (modMat mulmat a *ᵥ zc (flat γ₁ y) ∈ Fintype.piFinset (AltR0.good γ₂ β (v c)))

/-- The z check `‖y + c·s₁‖∞ < γ₁ − β`, with `u c = c·s₁`. -/
def zok (γ₁ β : ℕ) (u : C → Fin (L * n) → ℤ) (y : Fin L → V γ₁ n) (c : C) : Bool :=
  decide (∀ c', |flat γ₁ y c' + u c c'| < (γ₁ : ℤ) - β)

/-- Lower end of the z-passing window of block `j`, shifted by `u`. -/
def zlo (γ₁ β : ℕ) (j : Fin L) (u : Fin (L * n) → ℤ) : Fin n → ℤ :=
  fun s => -((γ₁ : ℤ) - β) + 1 - u (finProdFinEquiv (j, s))

/-- Width of the z-passing window. -/
def zw (γ₁ β : ℕ) : ℕ := 2 * (γ₁ - β) - 1

/-- `μ`: the r₀ pass probability of a uniform `w`. -/
def mu (q γ₂ β mb K n : ℕ) : ℚ := (((mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ) / q) ^ (K * n)

/-- `p_z`: the z pass probability of a uniform nonce. -/
def pz (γ₁ β L n : ℕ) : ℚ := (((zw γ₁ β : ℕ) : ℚ) / ((2 * γ₁ : ℕ) : ℚ)) ^ (L * n)

/-- Mean deviation of the r₀ pass probability over the tail, full head box, averaged over `c`. -/
def X (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (a : Fin K → Fin L → Fin n → ZMod q) : ℚ :=
  avg fun c : C => (∑ t ∈ AltR0.tbox γ₁ h₀,
    |AltR0.rhoC mulmat γ₂ β (v c) (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁) h₀ a t - mu q γ₂ β mb K n|) /
      (AltR0.tbox (n := n) γ₁ h₀).card

/-- The same with the head ranging over the z-passing box (shifted by `c·s₁`). -/
def Xz (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L)
    (a : Fin K → Fin L → Fin n → ZMod q) : ℚ :=
  avg fun c : C => (∑ t ∈ AltR0.tbox γ₁ h₀,
    |AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β) h₀ a t - mu q γ₂ β mb K n|) /
      (AltR0.tbox (n := n) γ₁ h₀).card

/-! ## Splitting a nonce into head and tail -/

variable {γ₁ : ℕ}

lemma flat_eq (h₀ : Fin L) (y : Fin L → V γ₁ n) :
    flat γ₁ y = AltR0.join h₀ (y h₀).1 (tailOf γ₁ h₀ y) := by
  funext c'
  simp only [flat, AltR0.join, tailOf]
  split_ifs with h
  · rw [h]
  · rfl

lemma mem_tbox_ne {h₀ : Fin L} {t : Fin L → Fin n → ℤ} (ht : t ∈ AltR0.tbox γ₁ h₀) {k : Fin L}
    (hk : k ≠ h₀) : t k ∈ box γ₁ n := by
  have := Fintype.mem_piFinset.mp ht k
  rwa [if_neg hk] at this

lemma mem_tbox_eq {h₀ : Fin L} {t : Fin L → Fin n → ℤ} (ht : t ∈ AltR0.tbox γ₁ h₀) :
    t h₀ = 0 := by
  have := Fintype.mem_piFinset.mp ht h₀
  rw [if_pos rfl] at this
  exact mem_singleton.mp this

lemma tailOf_mem (h₀ : Fin L) (y : Fin L → V γ₁ n) : tailOf γ₁ h₀ y ∈ AltR0.tbox γ₁ h₀ :=
  Fintype.mem_piFinset.mpr fun k => by
    unfold tailOf; split_ifs
    · simp
    · exact (y k).2

/-- Put a head and a tail together. -/
def joinV (h₀ : Fin L) (x : V γ₁ n) (t : Fin L → Fin n → ℤ) (ht : t ∈ AltR0.tbox γ₁ h₀) :
    Fin L → V γ₁ n :=
  fun k => if hk : k = h₀ then x else ⟨t k, mem_tbox_ne ht hk⟩

/-- A sum over nonces of a function of head and tail is a sum over `box × tbox`. -/
lemma sum_split (h₀ : Fin L) (G : (Fin n → ℤ) → (Fin L → Fin n → ℤ) → ℚ) :
    ∑ y : Fin L → V γ₁ n, G (y h₀).1 (tailOf γ₁ h₀ y) =
      ∑ x ∈ box γ₁ n, ∑ t ∈ AltR0.tbox γ₁ h₀, G x t := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij' (fun y _ => ((y h₀).1, tailOf γ₁ h₀ y))
    (fun p hp => joinV h₀ ⟨p.1, (mem_product.mp hp).1⟩ p.2 (mem_product.mp hp).2)
    (fun y _ => mem_product.mpr ⟨(y h₀).2, tailOf_mem h₀ y⟩) (fun _ _ => mem_univ _)
    ?_ ?_ (fun _ _ => rfl)
  · intro y _
    funext k
    unfold joinV
    split_ifs with hk
    · subst hk; rfl
    · apply Subtype.ext; simp [tailOf, hk]
  · intro p hp
    refine Prod.ext (by simp [joinV]) ?_
    funext k
    simp only [tailOf, joinV]
    split_ifs with hk
    · subst hk; exact (mem_tbox_eq (mem_product.mp hp).2).symm
    · rfl

/-- `sum_split` with the summand given pointwise (robust to instance mismatches). -/
lemma sum_split' (h₀ : Fin L) {F : (Fin L → V γ₁ n) → ℚ}
    (G : (Fin n → ℤ) → (Fin L → Fin n → ℤ) → ℚ) (hFG : ∀ y, F y = G (y h₀).1 (tailOf γ₁ h₀ y)) :
    ∑ y, F y = ∑ x ∈ box γ₁ n, ∑ t ∈ AltR0.tbox γ₁ h₀, G x t := by
  rw [← sum_split h₀ G]
  exact sum_congr rfl fun y _ => hFG y

lemma card_Y (h₀ : Fin L) :
    (Fintype.card (Fin L → V γ₁ n) : ℚ) = (box γ₁ n).card * (AltR0.tbox (n := n) γ₁ h₀).card := by
  have := sum_split (γ₁ := γ₁) (n := n) h₀ (fun _ _ => (1 : ℚ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at this
  exact this

lemma tailOf_eq_iff (h₀ : Fin L) (y y' : Fin L → V γ₁ n) :
    tailOf γ₁ h₀ y' = tailOf γ₁ h₀ y ↔ ∀ j ∉ ({h₀} : Finset (Fin L)), y' j = y j := by
  constructor
  · intro h j hj
    have := congrFun h j
    rw [mem_singleton] at hj
    simp only [tailOf, if_neg hj] at this
    exact Subtype.ext this
  · intro h
    funext j
    simp only [tailOf]
    split_ifs with hj
    · rfl
    · rw [h j (by simpa using hj)]


/-! ## The deviation of `ρ` -/

/-- `rhoC` as a normalised count. -/
lemma rhoC_eq (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ β : ℕ)
    (v : Fin (K * n) → ℤ) (lo : Fin n → ℤ) (w : ℕ) (h₀ : Fin L)
    (a : Fin K → Fin L → Fin n → ZMod q) (t : Fin L → Fin n → ℤ) :
    AltR0.rhoC mulmat γ₂ β v lo w h₀ a t =
      (∑ x ∈ AltR0.hbox lo w, if modMat mulmat a *ᵥ zc (AltR0.join h₀ x t) ∈
        Fintype.piFinset (AltR0.good γ₂ β v) then (1 : ℚ) else 0) / (AltR0.hbox lo w).card := by
  unfold AltR0.rhoC RejOrder.prob
  rw [sum_boole]

set_option linter.unusedSectionVars false

/-- Bathwater's `ρ` with `H = {h₀}` is the average over `c` of `rhoC` at the tail. -/
lemma rho_eq [Nonempty (V γ₁ n)] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    (γ₂ β : ℕ) (v : C → Fin (K * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q) (h₀ : Fin L)
    (y : Fin L → V γ₁ n) :
    Bathwater.AltR0Set.rho {h₀} (r0 mulmat γ₁ γ₂ β v a) y =
      (∑ c, AltR0.rhoC mulmat γ₂ β (v c) (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁) h₀ a
        (tailOf γ₁ h₀ y)) / Fintype.card C := by
  unfold Bathwater.AltR0Set.rho
  set T := tailOf γ₁ h₀ y
  rw [sum_split' h₀ (fun x t => ∑ c, if t = T ∧
        modMat mulmat a *ᵥ zc (AltR0.join h₀ x t) ∈ Fintype.piFinset (AltR0.good γ₂ β (v c))
        then (1 : ℚ) else 0)]
  swap
  · intro y'
    refine sum_congr rfl fun c _ => ?_
    congr 1
    simp only [r0, decide_eq_true_eq, flat_eq h₀ y', T, tailOf_eq_iff]
  have e2 : ∀ x ∈ box γ₁ n, (∑ t ∈ AltR0.tbox γ₁ h₀, ∑ c, if t = T ∧
        modMat mulmat a *ᵥ zc (AltR0.join h₀ x t) ∈ Fintype.piFinset (AltR0.good γ₂ β (v c))
        then (1 : ℚ) else 0) = ∑ c, if modMat mulmat a *ᵥ zc (AltR0.join h₀ x T) ∈
          Fintype.piFinset (AltR0.good γ₂ β (v c)) then (1 : ℚ) else 0 := by
    intro x _
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    simp only [ite_and]
    rw [sum_ite_eq' _ T, if_pos (tailOf_mem h₀ y)]
  rw [sum_congr rfl e2, sum_comm]
  simp only [rhoC_eq, ← AltR0.box_eq_hbox, card_singleton, pow_one, Fintype.card_coe]
  rw [← sum_div, div_div]

lemma abs_avg_sub_le (f : C → ℚ) (μ : ℚ) [Nonempty C] :
    |(∑ c, f c) / Fintype.card C - μ| ≤ (∑ c, |f c - μ|) / Fintype.card C := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have : (∑ c, f c) / Fintype.card C - μ = (∑ c, (f c - μ)) / Fintype.card C := by
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]; field_simp
  rw [this, abs_div, abs_of_pos hC]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hC.le

lemma mu_pos {γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) : 0 < mu q γ₂ β mb K n := by
  unfold mu
  have h1 := hp.mb_pos; have h2 := hp.β_lt_γ₂
  have : 0 < mb * (2 * (γ₂ - β) - 1) := Nat.mul_pos h1 (by omega)
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  positivity

lemma mu_eq {γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v) :
    ∏ r, ((AltR0.good (q := q) γ₂ β v r).card : ℚ) / q = mu q γ₂ β mb K n := by
  simp only [AltR0.card_good hp hv, prod_const, card_univ, Fintype.card_fin, mu]

lemma X_nonneg (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ β mb : ℕ)
    (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (a : Fin K → Fin L → Fin n → ZMod q) :
    0 ≤ X mulmat γ₁ γ₂ β mb v h₀ a :=
  avg_nonneg fun _ => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg _)

lemma Xz_nonneg (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L)
    (a : Fin K → Fin L → Fin n → ZMod q) :
    0 ≤ Xz mulmat γ₁ γ₂ β mb u v h₀ a :=
  avg_nonneg fun _ => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg _)

/-- **Step 1.** The relative mean deviation of Bathwater's `ρ` from `μ` is at most `X / μ`. -/
theorem dev_le [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ β mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (v : C → Fin (K * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q)
    (h₀ : Fin L) :
    Bathwater.AltR0Set.dev {h₀} (r0 mulmat γ₁ γ₂ β v a) (mu q γ₂ β mb K n) ≤
      X mulmat γ₁ γ₂ β mb v h₀ a / mu q γ₂ β mb K n := by
  set μ := mu q γ₂ β mb K n
  have hμ : 0 < μ := mu_pos hp
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℚ) < (box γ₁ n).card := by
    have : (box γ₁ n).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty (V γ₁ n)); exact ⟨x.1, x.2⟩
    exact_mod_cast this.card_pos
  have hT : (0 : ℚ) < (AltR0.tbox (n := n) γ₁ h₀).card := by
    have : (AltR0.tbox (n := n) γ₁ h₀).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty (V γ₁ n))
      exact ⟨_, tailOf_mem h₀ (fun _ => x)⟩
    exact_mod_cast this.card_pos
  set R : (Fin L → Fin n → ℤ) → ℚ := fun t => (∑ c, AltR0.rhoC mulmat γ₂ β (v c)
    (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁) h₀ a t) / Fintype.card C
  have hsum : ∑ y : Fin L → V γ₁ n, |Bathwater.AltR0Set.rho {h₀} (r0 mulmat γ₁ γ₂ β v a) y - μ| =
      (box γ₁ n).card * ∑ t ∈ AltR0.tbox γ₁ h₀, |R t - μ| := by
    simp only [rho_eq]
    rw [sum_split h₀ (fun _ t => |R t - μ|), sum_const, nsmul_eq_mul]
  unfold Bathwater.AltR0Set.dev
  rw [hsum, card_Y h₀, le_div_iff₀ hμ]
  have hR : ∑ t ∈ AltR0.tbox γ₁ h₀, |R t - μ| ≤ (AltR0.tbox (n := n) γ₁ h₀).card *
      X mulmat γ₁ γ₂ β mb v h₀ a := by
    calc ∑ t ∈ AltR0.tbox γ₁ h₀, |R t - μ|
        ≤ ∑ t ∈ AltR0.tbox γ₁ h₀, (∑ c, |AltR0.rhoC mulmat γ₂ β (v c)
            (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁) h₀ a t - μ|) / Fintype.card C :=
          sum_le_sum fun t _ => abs_avg_sub_le _ _
      _ = _ := by
          unfold X avg
          rw [← sum_div, sum_comm, mul_div_assoc', mul_sum]
          congr 1
          refine sum_congr rfl fun c _ => ?_
          field_simp
          rfl
  calc ((box γ₁ n).card * ∑ t ∈ AltR0.tbox γ₁ h₀, |R t - μ|) /
        ((box γ₁ n).card * (AltR0.tbox (n := n) γ₁ h₀).card * μ) * μ
      = (∑ t ∈ AltR0.tbox γ₁ h₀, |R t - μ|) / (AltR0.tbox (n := n) γ₁ h₀).card := by
        field_simp
    _ ≤ _ := by rw [div_le_iff₀ hT]; linarith

/-! ## The acceptance probability -/

variable {β : ℕ}

lemma z_coord (hβ : β < γ₁) (z u : ℤ) :
    |z + u| < (γ₁ : ℤ) - β ↔
      z ∈ Ico (-((γ₁ : ℤ) - β) + 1 - u) (-((γ₁ : ℤ) - β) + 1 - u + ((zw γ₁ β : ℕ) : ℤ)) := by
  rw [abs_lt, mem_Ico]; unfold zw; omega

lemma zbox_sub (hβ : β < γ₁) (j : Fin L) {u : Fin (L * n) → ℤ} (hu : Bounded β u) :
    AltR0.hbox (zlo γ₁ β j u) (zw γ₁ β) ⊆ box γ₁ n := by
  intro x hx
  unfold AltR0.hbox at hx
  unfold RejOrder.box
  rw [Fintype.mem_piFinset] at hx ⊢
  intro s
  have h1 := hx s
  have h2 := abs_le.mp (hu (finProdFinEquiv (j, s)))
  rw [mem_Ico] at h1; rw [mem_Ioc]; unfold zlo zw at h1; omega

/-- The z check of `join h₀ x t` splits into a head and a tail condition. -/
lemma zok_join (hβ : β < γ₁) (h₀ : Fin L) (u : Fin (L * n) → ℤ) (x : Fin n → ℤ)
    (t : Fin L → Fin n → ℤ) :
    (∀ c', |AltR0.join h₀ x t c' + u c'| < (γ₁ : ℤ) - β) ↔
      x ∈ AltR0.hbox (zlo γ₁ β h₀ u) (zw γ₁ β) ∧
        ∀ j, j ≠ h₀ → t j ∈ AltR0.hbox (zlo γ₁ β j u) (zw γ₁ β) := by
  have key : (∀ c', |AltR0.join h₀ x t c' + u c'| < (γ₁ : ℤ) - β) ↔
      ∀ j s, |(if j = h₀ then x s else t j s) + u (finProdFinEquiv (j, s))| < (γ₁ : ℤ) - β := by
    constructor
    · intro h j s
      have := h (finProdFinEquiv (j, s))
      simpa [AltR0.join] using this
    · intro h c'
      have := h (finProdFinEquiv.symm c').1 (finProdFinEquiv.symm c').2
      rw [Prod.mk.eta, Equiv.apply_symm_apply] at this
      simpa [AltR0.join] using this
  rw [key]
  simp only [AltR0.hbox, Fintype.mem_piFinset, z_coord hβ, zlo]
  constructor
  · intro h
    refine ⟨fun s => ?_, fun j hj s => ?_⟩
    · simpa using h h₀ s
    · simpa [hj] using h j s
  · rintro ⟨h1, h2⟩ j s
    by_cases hj : j = h₀
    · subst hj; simpa using h1 s
    · simpa [hj] using h2 j hj s

/-- The tail passes the z check. -/
def ztail (γ₁ β : ℕ) (h₀ : Fin L) (u : Fin (L * n) → ℤ) (t : Fin L → Fin n → ℤ) : Prop :=
  ∀ j, j ≠ h₀ → t j ∈ AltR0.hbox (zlo γ₁ β j u) (zw γ₁ β)

instance (γ₁ β : ℕ) (h₀ : Fin L) (u : Fin (L * n) → ℤ) : DecidablePred (ztail γ₁ β h₀ u) :=
  fun _ => by unfold ztail; infer_instance

lemma card_ztail (hβ : β < γ₁) (h₀ : Fin L) {u : Fin (L * n) → ℤ} (hu : Bounded β u) :
    ((AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ u)).card = ((zw γ₁ β) ^ n) ^ (L - 1) := by
  have e : (AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ u) = Fintype.piFinset fun j =>
      if j = h₀ then ({0} : Finset (Fin n → ℤ)) else AltR0.hbox (zlo γ₁ β j u) (zw γ₁ β) := by
    ext t
    simp only [mem_filter, AltR0.tbox, Fintype.mem_piFinset, ztail]
    constructor
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = h₀
      · subst hj; simpa using h1 j
      · rw [if_neg hj]; exact h2 j hj
    · intro h
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · by_cases hj : j = h₀
        · subst hj; simpa using h j
        · rw [if_neg hj]; have := h j; rw [if_neg hj] at this; exact zbox_sub hβ j hu this
      · have := h j; rwa [if_neg hj] at this
  rw [e, Fintype.card_piFinset]
  have : ∀ j, (if j = h₀ then ({0} : Finset (Fin n → ℤ))
      else AltR0.hbox (zlo γ₁ β j u) (zw γ₁ β)).card = if j = h₀ then 1 else (zw γ₁ β) ^ n := by
    intro j; split_ifs
    · simp
    · exact AltR0.card_hbox _ _
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    Finset.filter_ne' univ h₀, Finset.card_erase_of_mem (Finset.mem_univ _), card_univ,
    Fintype.card_fin]

lemma pz_eq (hL : 0 < L) :
    ((((zw γ₁ β) ^ n : ℕ) : ℚ) * ((((zw γ₁ β) ^ n) ^ (L - 1) : ℕ) : ℚ)) /
      ((((2 * γ₁) ^ n : ℕ) : ℚ) * ((((2 * γ₁) ^ n) ^ (L - 1) : ℕ) : ℚ)) = pz γ₁ β L n := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  unfold pz
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [div_pow]
  ring

/-- For a fixed challenge: the probability that a uniform nonce passes both checks is at least
`μ p_z − E_t |ρ_z(t) − μ|`. -/
lemma count_ge [Nonempty (V γ₁ n)] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    {γ₂ mb : ℕ} (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (a : Fin K → Fin L → Fin n → ZMod q) (h₀ : Fin L) (c : C) (hu : Bounded β (u c)) :
    mu q γ₂ β mb K n * pz γ₁ β L n - (∑ t ∈ AltR0.tbox γ₁ h₀,
      |AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β) h₀ a t - mu q γ₂ β mb K n|) /
        (AltR0.tbox (n := n) γ₁ h₀).card ≤
      (∑ y : Fin L → V γ₁ n, if (r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) = true
        then (1 : ℚ) else 0) / Fintype.card (Fin L → V γ₁ n) := by
  have hβ : β < γ₁ := hp.β_lt_γ₁
  set μ := mu q γ₂ β mb K n
  have hμ : 0 < μ := mu_pos hp
  set Z := AltR0.hbox (zlo γ₁ β h₀ (u c)) (zw γ₁ β)
  set P : (Fin n → ℤ) → (Fin L → Fin n → ℤ) → Prop := fun x t =>
    modMat mulmat a *ᵥ zc (AltR0.join h₀ x t) ∈ Fintype.piFinset (AltR0.good γ₂ β (v c))
  set ρ : (Fin L → Fin n → ℤ) → ℚ := fun t =>
    AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β) h₀ a t
  have hZpos : (0 : ℚ) < Z.card := by
    rw [AltR0.card_hbox]; unfold zw
    have : 0 < 2 * (γ₁ - β) - 1 := by omega
    positivity
  have hZB : (Z.card : ℚ) ≤ (box γ₁ n).card := by exact_mod_cast card_le_card (zbox_sub hβ h₀ hu)
  have hB : (0 : ℚ) < (box γ₁ n).card := lt_of_lt_of_le hZpos hZB
  have hT : (0 : ℚ) < (AltR0.tbox (n := n) γ₁ h₀).card := by
    have : (AltR0.tbox (n := n) γ₁ h₀).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty (V γ₁ n))
      exact ⟨_, tailOf_mem h₀ (fun _ => x)⟩
    exact_mod_cast this.card_pos
  -- the count
  have hcount : (∑ y : Fin L → V γ₁ n, if (r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) = true
      then (1 : ℚ) else 0) =
      ∑ t ∈ (AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c)), Z.card * ρ t := by
    rw [sum_split' h₀ (fun x t => if P x t ∧ x ∈ Z ∧ ztail γ₁ β h₀ (u c) t then (1 : ℚ) else 0)]
    swap
    · intro y
      congr 1
      simp only [r0, zok, Bool.and_eq_true, decide_eq_true_eq, flat_eq h₀ y, P, Z, ztail]
      rw [zok_join hβ]
    rw [sum_comm, sum_filter]
    refine sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · simp only [ρ, rhoC_eq, ht, and_true]
      rw [mul_div_cancel₀ _ hZpos.ne', ← sum_filter, ← sum_filter]
      congr 1
      ext x
      simp only [mem_filter, Z, P]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨zbox_sub hβ h₀ hu h2, h1, h2⟩
    · simp [ht]
  have hρ : ∀ t, ρ t ≥ μ - |ρ t - μ| := fun t => by
    have := neg_abs_le (ρ t - μ); linarith
  have hlow : (Z.card : ℚ) * μ * ((AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c))).card -
      Z.card * ∑ t ∈ AltR0.tbox γ₁ h₀, |ρ t - μ| ≤
      ∑ t ∈ (AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c)), Z.card * ρ t := by
    have h1 : ∑ t ∈ (AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c)), |ρ t - μ| ≤
        ∑ t ∈ AltR0.tbox γ₁ h₀, |ρ t - μ| :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => abs_nonneg _
    have h2 : ∑ t ∈ (AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c)), Z.card * (μ - |ρ t - μ|) ≤
        ∑ t ∈ (AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c)), Z.card * ρ t :=
      sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hρ t) hZpos.le
    rw [← mul_sum] at h2
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at h2
    nlinarith [mul_le_mul_of_nonneg_left h1 hZpos.le]
  have hpz : (Z.card : ℚ) * ((AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c))).card /
      ((box γ₁ n).card * (AltR0.tbox (n := n) γ₁ h₀).card) = pz γ₁ β L n := by
    rw [card_ztail hβ h₀ hu, AltR0.card_hbox, card_box_nat, AltR0.card_tbox]
    exact pz_eq (Nat.pos_of_ne_zero fun h => (h ▸ h₀).elim0)
  rw [hcount, card_Y h₀]
  have hS : 0 ≤ ∑ t ∈ AltR0.tbox γ₁ h₀, |ρ t - μ| := sum_nonneg fun _ _ => abs_nonneg _
  rw [le_div_iff₀ (mul_pos hB hT)]
  refine le_trans ?_ hlow
  have e1 : μ * pz γ₁ β L n * ((box γ₁ n).card * (AltR0.tbox (n := n) γ₁ h₀).card) =
      Z.card * μ * ((AltR0.tbox γ₁ h₀).filter (ztail γ₁ β h₀ (u c))).card := by
    rw [← hpz]; field_simp
  have e2 : (∑ t ∈ AltR0.tbox γ₁ h₀, |ρ t - μ|) / (AltR0.tbox (n := n) γ₁ h₀).card *
      ((box γ₁ n).card * (AltR0.tbox (n := n) γ₁ h₀).card) =
      (box γ₁ n).card * ∑ t ∈ AltR0.tbox γ₁ h₀, |ρ t - μ| := by
    field_simp
  rw [sub_mul, e1, e2]
  nlinarith [mul_le_mul_of_nonneg_right hZB hS]

/-- **Step 2.** Vanilla's acceptance probability is at least `μ p_z − X_z`. -/
theorem pacc_ge [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (hu : ∀ c, Bounded β (u c)) (a : Fin K → Fin L → Fin n → ZMod q) (h₀ : Fin L) :
    mu q γ₂ β mb K n * pz γ₁ β L n - Xz mulmat γ₁ γ₂ β mb u v h₀ a ≤
      Bathwater.AltR0Set.pacc (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hY : (0 : ℚ) < Fintype.card (Fin L → V γ₁ n) := by exact_mod_cast Fintype.card_pos
  have e : Bathwater.AltR0Set.pacc (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) =
      (∑ c, (∑ y : Fin L → V γ₁ n, if (r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) = true
        then (1 : ℚ) else 0) / Fintype.card (Fin L → V γ₁ n)) / Fintype.card C := by
    unfold Bathwater.AltR0Set.pacc Bathwater.AltR0Set.sacc
    rw [← sum_div, ← sum_div, sum_comm, div_div, div_div, mul_comm (Fintype.card C : ℚ)]
  rw [e]
  unfold Xz avg
  rw [le_div_iff₀ hC, sub_mul, div_mul_cancel₀ _ hC.ne']
  have := sum_le_sum fun c (_ : c ∈ univ) => count_ge mulmat hp u v a h₀ c (hu c)
  rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at this
  linarith

/-! ## Closeness for one matrix -/

/-- **Step 3.** For a fixed matrix `a`, if `D = μ p_z − X_z − X > 0` then the output law of
alt-r0 (resampling `y_{h₀}` on an r₀ failure) is within `2X/D` of vanilla's in `ℓ¹`, and the
probability that alt-r0 never terminates is at most `X/D`. -/
theorem close [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (hu : ∀ c, Bounded β (u c)) (a : Fin K → Fin L → Fin n → ZMod q) (h₀ : Fin L)
    (hD : 0 < mu q γ₂ β mb K n * pz γ₁ β L n - Xz mulmat γ₁ γ₂ β mb u v h₀ a -
      X mulmat γ₁ γ₂ β mb v h₀ a) :
    ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u) x -
        Bathwater.AltR0Set.vanLaw
          (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) x| ≤
      2 * X mulmat γ₁ γ₂ β mb v h₀ a / (mu q γ₂ β mb K n * pz γ₁ β L n -
        Xz mulmat γ₁ γ₂ β mb u v h₀ a - X mulmat γ₁ γ₂ β mb v h₀ a) ∧
    1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u) x ≤
      X mulmat γ₁ γ₂ β mb v h₀ a / (mu q γ₂ β mb K n * pz γ₁ β L n -
        Xz mulmat γ₁ γ₂ β mb u v h₀ a - X mulmat γ₁ γ₂ β mb v h₀ a) := by
  set μ := mu q γ₂ β mb K n
  set Xa := X mulmat γ₁ γ₂ β mb v h₀ a
  set Za := Xz mulmat γ₁ γ₂ β mb u v h₀ a
  set dv := Bathwater.AltR0Set.dev {h₀} (r0 mulmat γ₁ γ₂ β v a) μ
  set P := Bathwater.AltR0Set.pacc (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c)
  have hμ : 0 < μ := mu_pos hp
  have hdev : μ * dv ≤ Xa := by
    have := dev_le mulmat hp v a h₀
    rwa [le_div_iff₀ hμ, mul_comm] at this
  have hdv0 : 0 ≤ dv := by
    unfold dv Bathwater.AltR0Set.dev
    exact div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
  have hP : μ * pz γ₁ β L n - Za ≤ P := pacc_ge mulmat hp u v hu a h₀
  have hX0 : 0 ≤ Xa := X_nonneg mulmat γ₂ β mb v h₀ a
  have hgap : μ * pz γ₁ β L n - Za - Xa ≤ P - μ * dv := by linarith
  obtain ⟨h1, h2⟩ := Bathwater.altR0Set_close {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u) μ hμ
    (by linarith)
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · rw [mul_assoc]
    exact div_le_div₀ (by linarith) (by linarith) hD hgap
  · exact div_le_div₀ hX0 hdev hD hgap

/-! ## Averaging over the matrix -/

lemma avg_comm {A : Type*} [Fintype A] (f : A → C → ℚ) :
    avg (fun a => avg (fun c => f a c)) = avg (fun c => avg (fun a => f a c)) := by
  unfold avg
  rw [← sum_div, ← sum_div, sum_comm, div_div, div_div, mul_comm (Fintype.card C : ℚ)]

/-- **Step 4 (full head box).** -/
lemma avg_X_le [Nonempty C] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    {γ₂ mb : ℕ} (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) {δ : ℚ}
    (hdev : ∀ c, avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      (∑ t ∈ AltR0.tbox γ₁ h₀, |AltR0.rhoC mulmat γ₂ β (v c) (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁)
        h₀ a t - mu q γ₂ β mb K n|) / (AltR0.tbox (n := n) γ₁ h₀).card) ≤ mu q γ₂ β mb K n * δ) :
    avg (fun a => X mulmat γ₁ γ₂ β mb v h₀ a) ≤ mu q γ₂ β mb K n * δ := by
  unfold X
  rw [avg_comm]
  exact (avg_mono hdev).trans (avg_const _).le

/-- **Step 4 (z-passing head box).** -/
lemma avg_Xz_le [Nonempty C] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    {γ₂ mb : ℕ} (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) {δ : ℚ}
    (hdev : ∀ c, avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      (∑ t ∈ AltR0.tbox γ₁ h₀, |AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β)
        h₀ a t - mu q γ₂ β mb K n|) / (AltR0.tbox (n := n) γ₁ h₀).card) ≤ mu q γ₂ β mb K n * δ) :
    avg (fun a => Xz mulmat γ₁ γ₂ β mb u v h₀ a) ≤ mu q γ₂ β mb K n * δ := by
  unfold Xz
  rw [avg_comm]
  exact (avg_mono hdev).trans (avg_const _).le

/-! ## Few bad matrices -/

/-- A matrix is *bad* (at level `ε`) if one of the two deviations is at least `μ ε`. -/
def Bad (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (ε : ℚ)
    (a : Fin K → Fin L → Fin n → ZMod q) : Prop :=
  mu q γ₂ β mb K n * ε ≤ X mulmat γ₁ γ₂ β mb v h₀ a ∨
    mu q γ₂ β mb K n * ε ≤ Xz mulmat γ₁ γ₂ β mb u v h₀ a

instance (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (ε : ℚ) :
    DecidablePred (Bad mulmat γ₁ γ₂ β mb u v h₀ ε) :=
  fun _ => by unfold Bad; infer_instance

/-- **Main theorem, general form.** Suppose that, for every challenge, the mean deviations
(over the matrix and the tail) of the r₀ pass probability from `μ` are at most `μ δ`, both for the
full head box and for the z-passing head box. Then for every `ε > 0`, at most a `2δ/ε` fraction of
matrices are bad, and for every other matrix (if `2ε < p_z`) the output law of alt-r0 is within
`2ε / (p_z − 2ε)` of vanilla's in `ℓ¹`, and alt-r0 fails to terminate with probability at most
`ε / (p_z − 2ε)`. -/
theorem main [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (hu : ∀ c, Bounded β (u c)) (h₀ : Fin L) {δ ε : ℚ} (hε : 0 < ε)
    (hX : avg (fun a => X mulmat γ₁ γ₂ β mb v h₀ a) ≤ mu q γ₂ β mb K n * δ)
    (hZ : avg (fun a => Xz mulmat γ₁ γ₂ β mb u v h₀ a) ≤ mu q γ₂ β mb K n * δ) :
    ((univ.filter (Bad mulmat γ₁ γ₂ β mb u v h₀ ε)).card : ℚ) /
        Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ 2 * δ / ε ∧
      ∀ a, ¬ Bad mulmat γ₁ γ₂ β mb u v h₀ ε a → 2 * ε < pz γ₁ β L n →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u) x -
            Bathwater.AltR0Set.vanLaw
              (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) x| ≤
          2 * ε / (pz γ₁ β L n - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u) x ≤
          ε / (pz γ₁ β L n - 2 * ε) := by
  set μ := mu q γ₂ β mb K n
  have hμ : 0 < μ := mu_pos hp
  have hη : 0 < μ * ε := mul_pos hμ hε
  have hr : μ * δ / (μ * ε) = δ / ε := mul_div_mul_left _ _ hμ.ne'
  refine ⟨?_, ?_⟩
  · have h1 := markov (fun a => X_nonneg mulmat γ₂ β mb v h₀ a) hη hX
    have h2 := markov (fun a => Xz_nonneg mulmat γ₂ β mb u v h₀ a) hη hZ
    rw [hr] at h1 h2
    have hc : ((univ.filter (Bad mulmat γ₁ γ₂ β mb u v h₀ ε)).card : ℚ) ≤
        ((univ.filter fun a => μ * ε ≤ X mulmat γ₁ γ₂ β mb v h₀ a).card : ℚ) +
          ((univ.filter fun a => μ * ε ≤ Xz mulmat γ₁ γ₂ β mb u v h₀ a).card : ℚ) := by
      rw [← Nat.cast_add]
      refine Nat.cast_le.mpr (le_trans (card_le_card ?_) (card_union_le _ _))
      intro a ha
      simp only [mem_filter, mem_univ, true_and, Bad, mem_union] at ha ⊢
      exact ha
    have hA : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
      exact_mod_cast Fintype.card_pos
    calc ((univ.filter (Bad mulmat γ₁ γ₂ β mb u v h₀ ε)).card : ℚ) /
          Fintype.card (Fin K → Fin L → Fin n → ZMod q)
        ≤ (((univ.filter fun a => μ * ε ≤ X mulmat γ₁ γ₂ β mb v h₀ a).card : ℚ) +
            ((univ.filter fun a => μ * ε ≤ Xz mulmat γ₁ γ₂ β mb u v h₀ a).card : ℚ)) /
            Fintype.card (Fin K → Fin L → Fin n → ZMod q) :=
          div_le_div_of_nonneg_right hc hA.le
      _ ≤ δ / ε + δ / ε := by rw [add_div]; exact add_le_add h1 h2
      _ = 2 * δ / ε := by ring
  · intro a ha hpz
    simp only [Bad, not_or, not_le] at ha
    obtain ⟨hXa, hZa⟩ := ha
    have hX0 := X_nonneg (γ₁ := γ₁) mulmat γ₂ β mb v h₀ a
    have hgap : 0 < μ * (pz γ₁ β L n - 2 * ε) := mul_pos hμ (by linarith)
    have hle : μ * (pz γ₁ β L n - 2 * ε) ≤ μ * pz γ₁ β L n - Xz mulmat γ₁ γ₂ β mb u v h₀ a -
        X mulmat γ₁ γ₂ β mb v h₀ a := by linarith
    obtain ⟨h1, h2⟩ := close mulmat hp u v hu a h₀ (lt_of_lt_of_le hgap hle)
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · calc 2 * X mulmat γ₁ γ₂ β mb v h₀ a / (μ * pz γ₁ β L n -
            Xz mulmat γ₁ γ₂ β mb u v h₀ a - X mulmat γ₁ γ₂ β mb v h₀ a)
          ≤ 2 * (μ * ε) / (μ * (pz γ₁ β L n - 2 * ε)) :=
            div_le_div₀ (by positivity) (by linarith) hgap hle
        _ = 2 * ε / (pz γ₁ β L n - 2 * ε) := by
            rw [mul_left_comm, mul_div_mul_left _ _ hμ.ne']
    · calc X mulmat γ₁ γ₂ β mb v h₀ a / (μ * pz γ₁ β L n -
            Xz mulmat γ₁ γ₂ β mb u v h₀ a - X mulmat γ₁ γ₂ β mb v h₀ a)
          ≤ (μ * ε) / (μ * (pz γ₁ β L n - 2 * ε)) :=
            div_le_div₀ hη.le hXa.le hgap hle
        _ = ε / (pz γ₁ β L n - 2 * ε) := mul_div_mul_left _ _ hμ.ne'

end General

/-! ## ML-DSA-44 -/

section MLDSA44

lemma mu_eq_44 {v : Fin (4 * 256) → ℤ} (hv : Bounded 78 v) :
    ∏ r, ((AltR0.good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417 =
      mu 8380417 95232 78 44 4 256 :=
  mu_eq params_mldsa44 hv

lemma avg_X_44 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (4 * 256) → ℤ)
    (hv : ∀ c, Bounded 78 (v c)) (h₀ : Fin 4) :
    avg (fun a => X (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 v h₀ a) ≤
      mu 8380417 95232 78 44 4 256 * (1 / 2 ^ 147) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa44_sharp (hv c) (lo := fun _ => -((2 ^ 17 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 17) (Or.inl rfl) h₀
  rw [mu_eq_44 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hv : ∀ c, Bounded 78 (v c)) (h₀ : Fin 4) :
    avg (fun a => Xz (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀ a) ≤
      mu 8380417 95232 78 44 4 256 * (1 / 2 ^ 147) := by
  apply avg_Xz_le
  intro c
  have := AltR0.dev_mldsa44_sharp (hv c) (lo := zlo (2 ^ 17) 78 h₀ (u c)) (w := zw (2 ^ 17) 78)
    (Or.inr rfl) h₀
  rw [mu_eq_44 (hv c)] at this
  rw [mul_one_div]; exact this

/-- `p_z ≥ 27 / 50` for ML-DSA-44. -/
lemma pz_ge_44 : (27 / 50 : ℚ) ≤ pz (2 ^ 17) 78 4 256 := by
  have h : 27 * (2 * 2 ^ 17) ^ (4 * 256) ≤ zw (2 ^ 17) 78 ^ (4 * 256) * 50 := by
    decide +kernel
  unfold pz
  rw [div_pow, ← Nat.cast_pow, ← Nat.cast_pow, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ (by norm_num)]
  exact_mod_cast h

/-- **ML-DSA-44, any level `ε`.** At most a `2^-146 / ε` fraction of matrices `A` are bad; for
every other `A` with `2ε < p_z`, alt-r0's output law is within `2ε / (p_z − 2ε)` of vanilla's in
`ℓ¹`, and it fails to terminate with probability at most `ε / (p_z − 2ε)`. -/
theorem altR0_mldsa44_eps {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hu : ∀ c, Bounded 78 (u c)) (hv : ∀ c, Bounded 78 (v c))
    (h₀ : Fin 4) {ε : ℚ} (hε : 0 < ε) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀ ε)).card
        : ℚ) / Fintype.card (Fin 4 → Fin 4 → Fin 256 → ZMod 8380417) ≤ 2 * (1 / 2 ^ 147) / ε ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀ ε a →
        2 * ε < pz (2 ^ 17) 78 4 256 →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 17) 95232 78 v a)
              (zok (2 ^ 17) 78 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 17) 95232 78 v a y c &&
              zok (2 ^ 17) 78 u y c) x| ≤
          2 * ε / (pz (2 ^ 17) 78 4 256 - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 17) 95232 78 v a)
              (zok (2 ^ 17) 78 u) x ≤
          ε / (pz (2 ^ 17) 78 4 256 - 2 * ε) :=
  main negacyclic params_mldsa44 u v hu h₀ hε (avg_X_44 v hv h₀) (avg_Xz_44 u v hv h₀)

/-- **ML-DSA-44, headline.** Take `ε = 2^-73`. For at least a `1 − 2^-73` fraction of
matrices `A`, alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law within
`2^-71` of vanilla's in `ℓ¹` (statistical distance `≤ 2^-72`), and fails to terminate with
probability at most `2^-72`. -/
theorem altR0_mldsa44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hu : ∀ c, Bounded 78 (u c)) (hv : ∀ c, Bounded 78 (v c))
    (h₀ : Fin 4) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀
        (1 / 2 ^ 73))).card : ℚ) / Fintype.card (Fin 4 → Fin 4 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 73 ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀
          (1 / 2 ^ 73) a →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 17) 95232 78 v a)
              (zok (2 ^ 17) 78 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 17) 95232 78 v a y c &&
              zok (2 ^ 17) 78 u y c) x| ≤ 1 / 2 ^ 71 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 17) 95232 78 v a)
              (zok (2 ^ 17) 78 u) x ≤ 1 / 2 ^ 72 := by
  obtain ⟨h1, h2⟩ := altR0_mldsa44_eps u v hu hv h₀ (ε := 1 / 2 ^ 73) (by norm_num)
  refine ⟨h1.trans (le_of_eq (by norm_num)), fun a ha => ?_⟩
  have hpz := pz_ge_44
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 17) 78 4 256 - 2 * (1 / 2 ^ 73) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 73) ≤ 27 / 50 := by norm_num
    linarith
  obtain ⟨d1, d2⟩ := h2 a ha (by linarith)
  refine ⟨d1.trans ?_, d2.trans ?_⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))

end MLDSA44

/-! ## ML-DSA-65 -/

section MLDSA65

lemma mu_eq_65 {v : Fin (6 * 256) → ℤ} (hv : Bounded 196 v) :
    ∏ r, ((AltR0.good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417 =
      mu 8380417 261888 196 16 6 256 :=
  mu_eq params_mldsa65 hv

lemma avg_X_65 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (6 * 256) → ℤ)
    (hv : ∀ c, Bounded 196 (v c)) (h₀ : Fin 5) :
    avg (fun a => X (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 v h₀ a) ≤
      mu 8380417 261888 196 16 6 256 * (1 / 2 ^ 182) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa65_sharp (hv c) (lo := fun _ => -((2 ^ 19 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 19) (Or.inl rfl) h₀
  rw [mu_eq_65 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hv : ∀ c, Bounded 196 (v c)) (h₀ : Fin 5) :
    avg (fun a => Xz (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀ a) ≤
      mu 8380417 261888 196 16 6 256 * (1 / 2 ^ 182) := by
  apply avg_Xz_le
  intro c
  have := AltR0.dev_mldsa65_sharp (hv c) (lo := zlo (2 ^ 19) 196 h₀ (u c)) (w := zw (2 ^ 19) 196)
    (Or.inr rfl) h₀
  rw [mu_eq_65 (hv c)] at this
  rw [mul_one_div]; exact this

/-- `p_z ≥ 3 / 5` for ML-DSA-65. -/
lemma pz_ge_65 : (3 / 5 : ℚ) ≤ pz (2 ^ 19) 196 5 256 := by
  have h : 3 * (2 * 2 ^ 19) ^ (5 * 256) ≤ zw (2 ^ 19) 196 ^ (5 * 256) * 5 := by
    decide +kernel
  unfold pz
  rw [div_pow, ← Nat.cast_pow, ← Nat.cast_pow, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ (by norm_num)]
  exact_mod_cast h

/-- **ML-DSA-65, any level `ε`.** At most a `2^-181 / ε` fraction of matrices `A` are bad; for
every other `A` with `2ε < p_z`, alt-r0's output law is within `2ε / (p_z − 2ε)` of vanilla's in
`ℓ¹`, and it fails to terminate with probability at most `ε / (p_z − 2ε)`. -/
theorem altR0_mldsa65_eps {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hu : ∀ c, Bounded 196 (u c)) (hv : ∀ c, Bounded 196 (v c))
    (h₀ : Fin 5) {ε : ℚ} (hε : 0 < ε) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀ ε)).card
        : ℚ) / Fintype.card (Fin 6 → Fin 5 → Fin 256 → ZMod 8380417) ≤ 2 * (1 / 2 ^ 182) / ε ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀ ε a →
        2 * ε < pz (2 ^ 19) 196 5 256 →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 196 v a)
              (zok (2 ^ 19) 196 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 19) 261888 196 v a y c &&
              zok (2 ^ 19) 196 u y c) x| ≤
          2 * ε / (pz (2 ^ 19) 196 5 256 - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 196 v a)
              (zok (2 ^ 19) 196 u) x ≤
          ε / (pz (2 ^ 19) 196 5 256 - 2 * ε) :=
  main negacyclic params_mldsa65 u v hu h₀ hε (avg_X_65 v hv h₀) (avg_Xz_65 u v hv h₀)

/-- **ML-DSA-65, headline.** Take `ε = 2^-91`. For at least a `1 − 2^-90` fraction of
matrices `A`, alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law within
`2^-89` of vanilla's in `ℓ¹` (statistical distance `≤ 2^-90`), and fails to terminate with
probability at most `2^-90`. -/
theorem altR0_mldsa65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hu : ∀ c, Bounded 196 (u c)) (hv : ∀ c, Bounded 196 (v c))
    (h₀ : Fin 5) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀
        (1 / 2 ^ 91))).card : ℚ) / Fintype.card (Fin 6 → Fin 5 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 90 ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀
          (1 / 2 ^ 91) a →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 196 v a)
              (zok (2 ^ 19) 196 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 19) 261888 196 v a y c &&
              zok (2 ^ 19) 196 u y c) x| ≤ 1 / 2 ^ 89 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 196 v a)
              (zok (2 ^ 19) 196 u) x ≤ 1 / 2 ^ 90 := by
  obtain ⟨h1, h2⟩ := altR0_mldsa65_eps u v hu hv h₀ (ε := 1 / 2 ^ 91) (by norm_num)
  refine ⟨h1.trans (le_of_eq (by norm_num)), fun a ha => ?_⟩
  have hpz := pz_ge_65
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 196 5 256 - 2 * (1 / 2 ^ 91) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 91) ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2⟩ := h2 a ha (by linarith)
  refine ⟨d1.trans ?_, d2.trans ?_⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))

end MLDSA65

/-! ## ML-DSA-87 -/

section MLDSA87

lemma mu_eq_87 {v : Fin (8 * 256) → ℤ} (hv : Bounded 120 v) :
    ∏ r, ((AltR0.good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417 =
      mu 8380417 261888 120 16 8 256 :=
  mu_eq params_mldsa87 hv

lemma avg_X_87 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (8 * 256) → ℤ)
    (hv : ∀ c, Bounded 120 (v c)) (h₀ : Fin 7) :
    avg (fun a => X (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 v h₀ a) ≤
      mu 8380417 261888 120 16 8 256 * (1 / 2 ^ 190) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa87_sharp (hv c) (lo := fun _ => -((2 ^ 19 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 19) (Or.inl rfl) h₀
  rw [mu_eq_87 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hv : ∀ c, Bounded 120 (v c)) (h₀ : Fin 7) :
    avg (fun a => Xz (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀ a) ≤
      mu 8380417 261888 120 16 8 256 * (1 / 2 ^ 190) := by
  apply avg_Xz_le
  intro c
  have := AltR0.dev_mldsa87_sharp (hv c) (lo := zlo (2 ^ 19) 120 h₀ (u c)) (w := zw (2 ^ 19) 120)
    (Or.inr rfl) h₀
  rw [mu_eq_87 (hv c)] at this
  rw [mul_one_div]; exact this

/-- `p_z ≥ 3 / 5` for ML-DSA-87. -/
lemma pz_ge_87 : (3 / 5 : ℚ) ≤ pz (2 ^ 19) 120 7 256 := by
  have h : 3 * (2 * 2 ^ 19) ^ (7 * 256) ≤ zw (2 ^ 19) 120 ^ (7 * 256) * 5 := by
    decide +kernel
  unfold pz
  rw [div_pow, ← Nat.cast_pow, ← Nat.cast_pow, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ (by norm_num)]
  exact_mod_cast h

/-- **ML-DSA-87, any level `ε`.** At most a `2^-189 / ε` fraction of matrices `A` are bad; for
every other `A` with `2ε < p_z`, alt-r0's output law is within `2ε / (p_z − 2ε)` of vanilla's in
`ℓ¹`, and it fails to terminate with probability at most `ε / (p_z − 2ε)`. -/
theorem altR0_mldsa87_eps {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hu : ∀ c, Bounded 120 (u c)) (hv : ∀ c, Bounded 120 (v c))
    (h₀ : Fin 7) {ε : ℚ} (hε : 0 < ε) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀ ε)).card
        : ℚ) / Fintype.card (Fin 8 → Fin 7 → Fin 256 → ZMod 8380417) ≤ 2 * (1 / 2 ^ 190) / ε ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀ ε a →
        2 * ε < pz (2 ^ 19) 120 7 256 →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 120 v a)
              (zok (2 ^ 19) 120 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 19) 261888 120 v a y c &&
              zok (2 ^ 19) 120 u y c) x| ≤
          2 * ε / (pz (2 ^ 19) 120 7 256 - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 120 v a)
              (zok (2 ^ 19) 120 u) x ≤
          ε / (pz (2 ^ 19) 120 7 256 - 2 * ε) :=
  main negacyclic params_mldsa87 u v hu h₀ hε (avg_X_87 v hv h₀) (avg_Xz_87 u v hv h₀)

/-- **ML-DSA-87, headline.** Take `ε = 2^-95`. For at least a `1 − 2^-94` fraction of
matrices `A`, alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law within
`2^-93` of vanilla's in `ℓ¹` (statistical distance `≤ 2^-94`), and fails to terminate with
probability at most `2^-94`. -/
theorem altR0_mldsa87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hu : ∀ c, Bounded 120 (u c)) (hv : ∀ c, Bounded 120 (v c))
    (h₀ : Fin 7) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀
        (1 / 2 ^ 95))).card : ℚ) / Fintype.card (Fin 8 → Fin 7 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 94 ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀
          (1 / 2 ^ 95) a →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 120 v a)
              (zok (2 ^ 19) 120 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 19) 261888 120 v a y c &&
              zok (2 ^ 19) 120 u y c) x| ≤ 1 / 2 ^ 93 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 120 v a)
              (zok (2 ^ 19) 120 u) x ≤ 1 / 2 ^ 94 := by
  obtain ⟨h1, h2⟩ := altR0_mldsa87_eps u v hu hv h₀ (ε := 1 / 2 ^ 95) (by norm_num)
  refine ⟨h1.trans (le_of_eq (by norm_num)), fun a ha => ?_⟩
  have hpz := pz_ge_87
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 120 7 256 - 2 * (1 / 2 ^ 95) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 95) ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2⟩ := h2 a ha (by linarith)
  refine ⟨d1.trans ?_, d2.trans ?_⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))

end MLDSA87

end AltR0Final

end

end AltR0FinalPart

section MinEntropyPart

/-!
# Min-entropy of the commitment when part of the nonce is reused

The step from real signing to the `Trans` hybrid (fresh challenges) needs, in every attempt, a
bound `ε` on the probability of guessing the commitment `w₁ = HighBits(A·y)` given everything
else (Barbosa et al., CRYPTO 2023; adapted to nonce reuse in Sprenkels' thesis §8.4). With alt-r0
or alt-z the tail of `y` may be reused, but the head `y_{h₀}` is always fresh. Hence it suffices
to bound, for every fixed tail `t` and target `W`,
`Pr_{y_{h₀}}[HighBits(A·(y_{h₀}, t)) = W]`.

* `guess_le`: if the entry `A_{i,h₀}` has `z` zero NTT slots, then for every tail and target the
  number of heads hitting `W` in row `i` is at most `(2γ₂+1)^n · (2γ₁)^z`. (The thesis's argument
  is the case `z = 0`, `A_{i,h₀}` invertible.)
* `card_bad_le`: the matrices whose column `h₀` has at least `d` zero slots in *every* row are a
  fraction at most `(C(n,d) / q^d)^K`.
* `minEntropy`: outside that set, every attempt's commitment has guessing probability at most
  `((2γ₂+1)/(2γ₁))^n · (2γ₁)^(d-1)`.
* `minEntropy_mldsa44` etc.: with `d = 2`, `ε ≤ 2^-99` outside a `2^-124` fraction for ML-DSA-44
  (`2^-236`, `2^-186` for ML-DSA-65; `2^-236`, `2^-248` for ML-DSA-87).
-/

open Finset Matrix

noncomputable section

namespace MinEntropy
open RejOrder AltR0

variable {q γ₁ γ₂ β mb : ℕ} [NeZero q]

/-! ## HighBits -/

open Classical in
/-- `HighBits` of FIPS 204: the `r₁` of the unique decomposition `w = 2γ₂·r₁ + r₀`
(`highBits_enc`). -/
def highBits (q γ₂ mb : ℕ) (w : ZMod q) : ℕ :=
  if h : ∃ p ∈ decSet γ₂ mb, enc q γ₂ p = w then (Classical.choose h).1 else 0

lemma highBits_spec (hp : Params q γ₁ γ₂ β mb) (w : ZMod q) :
    ∃ p ∈ decSet γ₂ mb, enc q γ₂ p = w ∧ p.1 = highBits q γ₂ mb w := by
  have h := exists_enc hp w
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
  unfold highBits; rw [dif_pos h]

/-- `highBits` is the `r₁` of the decomposition. -/
lemma highBits_enc (hp : Params q γ₁ γ₂ β mb) {p : ℕ × ℤ} (h : p ∈ decSet γ₂ mb) :
    highBits q γ₂ mb (enc q γ₂ p) = p.1 := by
  obtain ⟨p', hp', he, h1⟩ := highBits_spec hp (enc q γ₂ p)
  rw [← h1, enc_injOn hp hp' h he]

/-- `w` is determined by its high and low bits. -/
lemma eq_of_bits (hp : Params q γ₁ γ₂ β mb) {w w' : ZMod q}
    (h1 : highBits q γ₂ mb w = highBits q γ₂ mb w') (h2 : lowBits q γ₂ w = lowBits q γ₂ w') :
    w = w' := by
  obtain ⟨p, hp1, he, hh⟩ := highBits_spec hp w
  obtain ⟨p', hp1', he', hh'⟩ := highBits_spec hp w'
  have l1 := lowBits_enc_of_mem hp hp1
  have l2 := lowBits_enc_of_mem hp hp1'
  rw [he] at l1; rw [he'] at l2
  have : p = p' := Prod.ext (by rw [hh, hh', h1]) (by rw [← l1, ← l2, h2])
  rw [← he, ← he', this]

lemma lowBits_mem (hp : Params q γ₁ γ₂ β mb) (w : ZMod q) :
    lowBits q γ₂ w ∈ Finset.Icc (-(γ₂ : ℤ)) γ₂ := by
  obtain ⟨p, hp1, he, -⟩ := highBits_spec hp w
  have l1 := lowBits_enc_of_mem hp hp1
  rw [he] at l1
  rw [l1, Finset.mem_Icc]
  rcases (mem_decSet hp p).mp hp1 with ⟨-, h | h⟩ <;> omega

/-! ## Guessing the commitment row -/

section Guess
variable {n : ℕ} [Fact q.Prime]

/-- NTT slots where `a` vanishes. -/
def zeroSlots (ζ : Fin n → ZMod q) (a : Fin n → ZMod q) : Finset (Fin n) :=
  univ.filter fun k => nttP ζ a k = 0

lemma nttP_mul {ζ : Fin n → ZMod q} {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    (h : IsNTTMul ζ mulmat) (a c : Fin n → ZMod q) (k : Fin n) :
    nttP ζ (mulmat a *ᵥ c) k = nttP ζ a k * nttP ζ c k := h.mul a c k

/-- **Guessing one row of the commitment.** For any offset `b` (the contribution of the reused
tail) and target `W`, at most `(2γ₂+1)^n · (2γ₁)^z` heads `y` in the box give
`HighBits(a·y + b) = W`, where `z` is the number of zero NTT slots of `a`. -/
theorem guess_le (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) (a b : Fin n → ZMod q) (W : Fin n → ℕ) :
    ((RejOrder.box γ₁ n).filter fun y =>
        ∀ s, highBits q γ₂ mb ((mulmat a *ᵥ (fun s => (y s : ZMod q)) + b) s) = W s).card
      ≤ (2 * γ₂ + 1) ^ n * (2 * γ₁) ^ (zeroSlots ζ a).card := by
  set F := (RejOrder.box γ₁ n).filter fun y =>
    ∀ s, highBits q γ₂ mb ((mulmat a *ᵥ (fun s => (y s : ZMod q)) + b) s) = W s
  set g : (Fin n → ℤ) → (Fin n → ℤ) := fun y s =>
    lowBits q γ₂ ((mulmat a *ᵥ (fun s => (y s : ZMod q)) + b) s)
  have himg : F.image g ⊆ Fintype.piFinset fun _ => Finset.Icc (-(γ₂ : ℤ)) γ₂ := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact Fintype.mem_piFinset.mpr fun s => lowBits_mem hp _
  have hcard_img : (F.image g).card ≤ (2 * γ₂ + 1) ^ n := by
    refine (Finset.card_le_card himg).trans (le_of_eq ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Int.card_Icc, card_univ, Fintype.card_fin]
    congr 1; omega
  have hfib : ∀ x ∈ F.image g, (F.filter fun y => g y = x).card ≤ (2 * γ₁) ^ (zeroSlots ζ a).card := by
    intro x hx
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hx
    have hy₀F := Finset.mem_filter.mp hy₀
    set S := (zeroSlots ζ a)ᶜ
    have hsub : (F.filter fun y => g y = g y₀) ⊆
        (hbox (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁)).filter fun y =>
          ∀ k ∈ S, nttP ζ (fun s => ((y s - y₀ s : ℤ) : ZMod q)) k = 0 := by
      intro y hy
      obtain ⟨hyF, hg⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyB, hW⟩ := Finset.mem_filter.mp hyF
      refine Finset.mem_filter.mpr ⟨by rw [← box_eq_hbox]; exact hyB, fun k hk => ?_⟩
      have heq : mulmat a *ᵥ (fun s => (y s : ZMod q)) = mulmat a *ᵥ (fun s => (y₀ s : ZMod q)) := by
        funext s
        have e := eq_of_bits hp ((hW s).trans (hy₀F.2 s).symm) (congrFun hg s)
        simpa using e
      have hz : nttP ζ a k * nttP ζ (fun s => ((y s - y₀ s : ℤ) : ZMod q)) k = 0 := by
        rw [← nttP_mul h]
        have : (fun s => ((y s - y₀ s : ℤ) : ZMod q))
            = (fun s => (y s : ZMod q)) - (fun s => (y₀ s : ZMod q)) := by
          funext s; simp
        rw [this, Matrix.mulVec_sub, heq, sub_self]
        simp [nttP]
      have hk' : nttP ζ a k ≠ 0 := by
        intro h0; exact (Finset.mem_compl.mp hk) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
      exact (mul_eq_zero.mp hz).resolve_left hk'
    refine (Finset.card_le_card hsub).trans ?_
    have := card_sol_le (lo := fun _ => -(γ₁ : ℤ) + 1) h.inj hγ S y₀
      (by rw [← box_eq_hbox]; exact hy₀F.1)
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [Finset.card_compl, Fintype.card_fin]
    have : (zeroSlots ζ a).card ≤ n := by simpa using Finset.card_le_univ (zeroSlots ζ a)
    omega
  have := Finset.card_le_mul_card_image F _ hfib
  calc F.card ≤ (2 * γ₁) ^ (zeroSlots ζ a).card * (F.image g).card := this
    _ ≤ (2 * γ₁) ^ (zeroSlots ζ a).card * (2 * γ₂ + 1) ^ n := Nat.mul_le_mul_left _ hcard_img
    _ = _ := Nat.mul_comm _ _

end Guess

/-! ## How many matrices are bad -/

section Count
variable {n : ℕ} [Fact q.Prime]

/-- Polynomials whose NTT vanishes on a set `Z` of slots: at most `q^(n - |Z|)`. -/
lemma card_vanish_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (Z : Finset (Fin n)) :
    ((univ : Finset (Fin n → ZMod q)).filter fun a => ∀ k ∈ Z, nttP ζ a k = 0).card
      ≤ q ^ (n - Z.card) := by
  have hZn : Z.card ≤ n := by simpa using Finset.card_le_univ Z
  set F := (univ : Finset (Fin n → ZMod q)).filter fun a => ∀ k ∈ Z, nttP ζ a k = 0
  have hinj : Set.InjOn (fun a (s : {s : Fin n // Z.card ≤ (s : ℕ)}) => a s.1)
      (F : Set (Fin n → ZMod q)) := by
    intro a ha a' ha' he
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp ha')).2
    funext s₀
    by_cases hs : (s₀ : ℕ) < Z.card
    · set cf : ℕ → ZMod q := fun t => if h : t < n then a ⟨t, h⟩ - a' ⟨t, h⟩ else 0 with hcf
      have hw : ∀ k ∈ Z, ∑ t ∈ range Z.card, cf t * ζ k ^ t = 0 := by
        intro k hk
        have e : nttP ζ a k - nttP ζ a' k = 0 := by rw [h1 k hk, h2 k hk, sub_self]
        unfold nttP at e
        rw [← Finset.sum_sub_distrib] at e
        rw [Finset.sum_subset (Finset.range_subset_range.mpr hZn), ← Fin.sum_univ_eq_sum_range
          (fun i => cf i * ζ k ^ i) n, ← e]
        · refine Finset.sum_congr rfl fun t _ => ?_
          simp only [hcf, dif_pos t.2, Fin.eta]; ring
        · intro i hi hni
          rw [Finset.mem_range] at hi hni
          simp only [hcf, dif_pos hi]
          have := congrFun he ⟨⟨i, hi⟩, by simp; omega⟩
          simp only at this
          rw [this, sub_self, zero_mul]
      have h0 := window ζ hζ cf Z.card Z le_rfl hw s₀ hs
      simp only [hcf, dif_pos s₀.2, Fin.eta] at h0
      exact sub_eq_zero.mp h0
    · exact congrFun he ⟨s₀, by omega⟩
  refine (Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    hinj).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_subtype]
  congr 1
  have : (univ.filter fun s : Fin n => Z.card ≤ (s : ℕ)) = univ.filter fun s : Fin n =>
      ¬ (s : ℕ) < Z.card := by ext s; simp
  rw [this, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), card_univ,
    Fintype.card_fin, Fin.card_filter_val_lt]
  omega

/-- Polynomials with at least `d` zero NTT slots: at most `C(n,d) · q^(n-d)`. -/
lemma card_zero_ge {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (d : ℕ) :
    ((univ : Finset (Fin n → ZMod q)).filter fun a => d ≤ (zeroSlots ζ a).card).card
      ≤ n.choose d * q ^ (n - d) := by
  have hsub : ((univ : Finset (Fin n → ZMod q)).filter fun a => d ≤ (zeroSlots ζ a).card)
      ⊆ ((univ : Finset (Fin n)).powersetCard d).biUnion fun Z =>
        (univ : Finset (Fin n → ZMod q)).filter fun a => ∀ k ∈ Z, nttP ζ a k = 0 := by
    intro a ha
    obtain ⟨Z, hZ, hc⟩ := Finset.exists_subset_card_eq (Finset.mem_filter.mp ha).2
    refine Finset.mem_biUnion.mpr ⟨Z, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => ?_⟩⟩
    exact (Finset.mem_filter.mp (hZ hk)).2
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum fun Z hZ => card_vanish_le hζ Z).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun Z hZ => by rw [(Finset.mem_powersetCard.mp hZ).2], Finset.sum_const,
    Finset.card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]

variable {K L : ℕ}

/-- Matrices whose column `h₀` has at least `d` zero NTT slots in every row. -/
def BadM (ζ : Fin n → ZMod q) (h₀ : Fin L) (d : ℕ) (A : Fin K → Fin L → Fin n → ZMod q) : Prop :=
  ∀ i, d ≤ (zeroSlots ζ (A i h₀)).card

instance (ζ : Fin n → ZMod q) (h₀ : Fin L) (d : ℕ) :
    DecidablePred (BadM (K := K) ζ h₀ d) := fun A => by unfold BadM; infer_instance

/-- **The bad matrices are rare**: a fraction at most `(C(n,d) / q^d)^K`. -/
theorem card_bad_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (h₀ : Fin L) (d : ℕ)
    (hd : d ≤ n) :
    (((univ : Finset (Fin K → Fin L → Fin n → ZMod q)).filter (BadM ζ h₀ d)).card : ℚ)
        / Fintype.card (Fin K → Fin L → Fin n → ZMod q)
      ≤ ((n.choose d : ℚ) / (q : ℚ) ^ d) ^ K := by
  classical
  set BP := (univ : Finset (Fin n → ZMod q)).filter fun a => d ≤ (zeroSlots ζ a).card
  have heq : (univ : Finset (Fin K → Fin L → Fin n → ZMod q)).filter (BadM ζ h₀ d)
      = Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun j : Fin L =>
          if j = h₀ then BP else univ := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, BadM]
    constructor
    · intro h i j; split_ifs with hj
      · subst hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i⟩
      · exact Finset.mem_univ _
    · intro h i; have := h i h₀; rw [if_pos rfl] at this; exact (Finset.mem_filter.mp this).2
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [heq, Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  rw [Fintype.card_piFinset]
  have hrow : ∏ j : Fin L, (if j = h₀ then BP else (univ : Finset (Fin n → ZMod q))).card
      = BP.card * (q ^ n) ^ (L - 1) := by
    simp_rw [apply_ite Finset.card, card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_eq' univ h₀,
      Finset.filter_ne' univ h₀, if_pos (Finset.mem_univ _), Finset.card_singleton, pow_one,
      Finset.card_erase_of_mem (Finset.mem_univ _), card_univ, Fintype.card_fin]
  rw [hrow]
  have hBP : (BP.card : ℚ) ≤ n.choose d * (q : ℚ) ^ (n - d) := by exact_mod_cast card_zero_ge hζ d
  have hL : 0 < L := Fin.pos h₀
  push_cast
  rw [div_le_iff₀ (by positivity)]
  calc ((BP.card : ℚ) * ((q : ℚ) ^ n) ^ (L - 1)) ^ K
      ≤ ((n.choose d : ℚ) * (q : ℚ) ^ (n - d) * ((q : ℚ) ^ n) ^ (L - 1)) ^ K := by
        gcongr
    _ = ((n.choose d : ℚ) / (q : ℚ) ^ d) ^ K * (((q : ℚ) ^ n) ^ L) ^ K := by
        rw [← mul_pow]; congr 1
        rw [show ((q : ℚ) ^ n) ^ L = (q : ℚ) ^ n * ((q : ℚ) ^ n) ^ (L - 1) by
          rw [← pow_succ']; congr 1; omega]
        rw [show (q : ℚ) ^ n = (q : ℚ) ^ d * (q : ℚ) ^ (n - d) by rw [← pow_add]; congr 1; omega]
        field_simp

end Count

/-! ## The min-entropy of a commitment with a fresh head -/

section Main
variable {n K L : ℕ} [Fact q.Prime]

/-- **Min-entropy.** If some row `i` of column `h₀` of `A` has fewer than `d` zero NTT slots, then
for every tail `t` (fixed, or correlated with anything outside `y_{h₀}`) and every target `W`, a
fresh head `y_{h₀}` makes `HighBits(A·y) = W` with probability at most
`(2γ₂+1)^n (2γ₁)^(d-1) / (2γ₁)^n`. -/
theorem minEntropy (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) (h₀ : Fin L) (d : ℕ) (A : Fin K → Fin L → Fin n → ZMod q)
    (hA : ¬ BadM ζ h₀ d A) (t : Fin L → Fin n → ℤ) (W : Fin K → Fin n → ℕ) :
    prob (RejOrder.box γ₁ n) (fun y₁ => ∀ i s,
        highBits q γ₂ mb ((modMat mulmat A *ᵥ zc (join h₀ y₁ t)) (finProdFinEquiv (i, s)))
          = W i s)
      ≤ ((2 * γ₂ + 1) ^ n * (2 * γ₁) ^ (d - 1) : ℕ) / ((2 * γ₁ : ℕ) : ℚ) ^ n := by
  unfold BadM at hA
  push Not at hA
  obtain ⟨i, hi⟩ := hA
  set b : Fin n → ZMod q := ∑ j ∈ univ.erase h₀, mulmat (A i j) *ᵥ (fun s => (t j s : ZMod q))
  have hrow : ∀ y₁ s, (modMat mulmat A *ᵥ zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))
      = (mulmat (A i h₀) *ᵥ (fun s => (y₁ s : ZMod q)) + b) s := by
    intro y₁ s
    rw [modMat_mulVec, ← Finset.add_sum_erase _ _ (Finset.mem_univ h₀)]
    simp only [blk_join, if_pos rfl, Pi.add_apply, b, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  have hsub : (RejOrder.box γ₁ n).filter (fun y₁ => ∀ i s,
      highBits q γ₂ mb ((modMat mulmat A *ᵥ zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))) = W i s)
      ⊆ (RejOrder.box γ₁ n).filter fun y =>
        ∀ s, highBits q γ₂ mb ((mulmat (A i h₀) *ᵥ (fun s => (y s : ZMod q)) + b) s) = W i s := by
    intro y hy
    obtain ⟨hyB, hW⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hyB, fun s => by rw [← hrow]; exact hW i s⟩
  have hc := (Finset.card_le_card hsub).trans (guess_le hp h hγ (A i h₀) b (W i))
  have hc' : (2 * γ₂ + 1) ^ n * (2 * γ₁) ^ (zeroSlots ζ (A i h₀)).card
      ≤ (2 * γ₂ + 1) ^ n * (2 * γ₁) ^ (d - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by have := hp.β_lt_γ₁; omega) (by omega))
  unfold prob
  rw [card_box_nat]
  push_cast
  gcongr
  exact_mod_cast hc.trans hc'

end Main

/-! ## ML-DSA -/

section MLDSA

/-- **ML-DSA-44.** Outside a `2^-124` fraction of matrices, every attempt's commitment has
guessing probability at most `2^-99` (with `d = 2`). With `d = 1` (some entry of column `h₀`
invertible, as in the thesis) it is `2^-117` outside a `2^-59` fraction. -/
theorem minEntropy_mldsa44 (h₀ : Fin 4) :
    (((univ : Finset (Fin 4 → Fin 4 → Fin 256 → ZMod 8380417)).filter
        (BadM zetaMLDSA h₀ 2)).card : ℚ) / Fintype.card (Fin 4 → Fin 4 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 124 ∧
      ∀ A, ¬ BadM zetaMLDSA h₀ 2 A → ∀ (t : Fin 4 → Fin 256 → ℤ) (W : Fin 4 → Fin 256 → ℕ),
        prob (RejOrder.box (2 ^ 17) 256) (fun y₁ => ∀ i s,
          highBits 8380417 95232 44 ((modMat (negacyclic (q := 8380417) (n := 256)) A *ᵥ
            zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))) = W i s) ≤ 1 / 2 ^ 99 := by
  refine ⟨(card_bad_le zetaMLDSA_inj h₀ 2 (by norm_num)).trans (by rw [Nat.choose_two_right]; norm_num), fun A hA t W => ?_⟩
  refine (minEntropy params_mldsa44 isNTTMul_mldsa (by norm_num) h₀ 2 A hA t W).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

/-- **ML-DSA-65.** Outside a `2^-186` fraction of matrices, every attempt's commitment has
guessing probability at most `2^-236` (with `d = 2`). -/
theorem minEntropy_mldsa65 (h₀ : Fin 5) :
    (((univ : Finset (Fin 6 → Fin 5 → Fin 256 → ZMod 8380417)).filter
        (BadM zetaMLDSA h₀ 2)).card : ℚ) / Fintype.card (Fin 6 → Fin 5 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 186 ∧
      ∀ A, ¬ BadM zetaMLDSA h₀ 2 A → ∀ (t : Fin 5 → Fin 256 → ℤ) (W : Fin 6 → Fin 256 → ℕ),
        prob (RejOrder.box (2 ^ 19) 256) (fun y₁ => ∀ i s,
          highBits 8380417 261888 16 ((modMat (negacyclic (q := 8380417) (n := 256)) A *ᵥ
            zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))) = W i s) ≤ 1 / 2 ^ 236 := by
  refine ⟨(card_bad_le zetaMLDSA_inj h₀ 2 (by norm_num)).trans (by rw [Nat.choose_two_right]; norm_num),
    fun A hA t W => ?_⟩
  refine (minEntropy params_mldsa65 isNTTMul_mldsa (by norm_num) h₀ 2 A hA t W).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

/-- **ML-DSA-87.** Outside a `2^-248` fraction of matrices, every attempt's commitment has
guessing probability at most `2^-236` (with `d = 2`). -/
theorem minEntropy_mldsa87 (h₀ : Fin 7) :
    (((univ : Finset (Fin 8 → Fin 7 → Fin 256 → ZMod 8380417)).filter
        (BadM zetaMLDSA h₀ 2)).card : ℚ) / Fintype.card (Fin 8 → Fin 7 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 248 ∧
      ∀ A, ¬ BadM zetaMLDSA h₀ 2 A → ∀ (t : Fin 7 → Fin 256 → ℤ) (W : Fin 8 → Fin 256 → ℕ),
        prob (RejOrder.box (2 ^ 19) 256) (fun y₁ => ∀ i s,
          highBits 8380417 261888 16 ((modMat (negacyclic (q := 8380417) (n := 256)) A *ᵥ
            zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))) = W i s) ≤ 1 / 2 ^ 236 := by
  refine ⟨(card_bad_le zetaMLDSA_inj h₀ 2 (by norm_num)).trans (by rw [Nat.choose_two_right]; norm_num),
    fun A hA t W => ?_⟩
  refine (minEntropy params_mldsa87 isNTTMul_mldsa (by norm_num) h₀ 2 A hA t W).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

end MLDSA

end MinEntropy

end

end MinEntropyPart
