import Mathlib
import RejOrder

/-!
# Nonce reuse in ML-DSA signing ("Don't throw your nonces out with the bathwater")

This file collects, in order:

* `BathwaterCore`: loop semantics, partial reuse of the nonce, the exactness of alt-z, the output
  law of alt-r0 and its distance to vanilla, approximate invariance (`ReusePolicy.defect`,
  `outUpTo_close`), and the toy counterexamples.
* `AltR0Part`: the second moment over `A` of the r₀ pass probability with the tail fixed.
* `PackingPart`, `NcInvPart`: a slot condition costs `1/q` (packing argument; invertibility in
  `ℚ[X]/(X^256+1)`).
* `AltR0ExcPart`: the probability of exceptional slots.
* `AltR0QPart`: the degenerate-slot probabilities with `1/q` per head condition.
* `AltR0SharpPart`: the sharper second moment by pairing orthogonal test vectors, and its
  kernel-checked ML-DSA instances.
* `AltR0GenPart`: the sharper second moment with general slot probabilities (`var_rel_gen`) and
  its `1/q` ML-DSA instances (`var_mldsa44_q` etc.).
* `RingFormPart`: the same instances stated over `R_q = ℤ_q[X]/(X^256 + 1)` itself
  (`moment_mldsa44` etc.); the headlines use them in this form.
* `AltR0FinalPart`: alt-r0 for ML-DSA-44/65/87 end to end.
* `MinEntropyPart`: min-entropy of the commitment with a fresh head.
* `AltR0JointPart`: alt-r0 per attempt (joint law of attempt number and output, survival), via
  the defect bound (`altR0_joint_mldsa44` etc.).
* `Alg3Part`: ePrint Algorithm 3 (r₀ first, resample the head on an r₀ failure and a prefix on a
  z failure) is close to vanilla for ML-DSA (`alg3_defect_le`, `alg3_mldsa44` etc.).

It imports `RejOrder.lean` for the module/NTT machinery, the gap counts, the covariance bound
`cov_le` and the weighted counts of test vectors.
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

/-! ## Approximate invariance (for ePrint Algorithm 3) -/

section Approx
variable {ι V C : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype C] [Nonempty C]

/-- **Defect** of a reuse policy: how far one rejected attempt from a uniform nonce is from
leaving a uniform nonce, `‖π B − (1 − p) π‖₁`. Invariant policies have defect `0`. -/
noncomputable def ReusePolicy.defect (P : ReusePolicy ι V C) : ℚ :=
  ∑ y', |(∑ y, P.loop.B y y') / Fintype.card (ι → V) - (1 - P.pAcc) / Fintype.card (ι → V)|

lemma ReusePolicy.pAcc_nonneg (P : ReusePolicy ι V C) : 0 ≤ P.pAcc := by
  unfold ReusePolicy.pAcc; positivity

lemma ReusePolicy.pAcc_le_one (P : ReusePolicy ι V C) : P.pAcc ≤ 1 := by
  unfold ReusePolicy.pAcc
  rw [div_le_one (by positivity)]
  have := card_le_univ ((univ : Finset ((ι → V) × C)).filter fun x => P x.1 x.2 = none)
  rw [Fintype.card_prod] at this
  exact_mod_cast this

/-- One rejected attempt does not increase the `ℓ¹` norm. -/
lemma ReusePolicy.step_norm_le (P : ReusePolicy ι V C) (e : (ι → V) → ℚ) :
    ∑ y', |P.loop.step e y'| ≤ ∑ y, |e y| := by
  have h := P.loop.norm_iter_le (P.B_nonneg) 1 e
  simp only [Function.iterate_one] at h
  refine h.trans (sum_le_sum fun y _ => ?_)
  have hs : P.loop.survive 1 y ≤ 1 := by
    have hrow := P.row y
    have hA : 0 ≤ ∑ x, P.loop.A y x := sum_nonneg fun x _ => P.A_nonneg y x
    simp only [Loop.survive, mul_one]; linarith
  calc |e y| * P.loop.survive 1 y ≤ |e y| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = |e y| := mul_one _

/-- **Approximate invariance gives approximate exactness.** The sub-law of the nonce at the start
of attempt `k` is within `defect · ∑_{j<k} (1−p)^j` of the exact `(1−p)^k · uniform`. -/
theorem ReusePolicy.state_close (P : ReusePolicy ι V C) (k : ℕ) :
    ∑ y, |P.loop.state k y - (1 - P.pAcc) ^ k / Fintype.card (ι → V)|
      ≤ P.defect * ∑ j ∈ range k, (1 - P.pAcc) ^ j := by
  have hp1 : 0 ≤ 1 - P.pAcc := by linarith [P.pAcc_le_one]
  induction k with
  | zero =>
    simp [Loop.state, ReusePolicy.loop]
  | succ k ih =>
    set e : (ι → V) → ℚ := fun y => P.loop.state k y - (1 - P.pAcc) ^ k / (Fintype.card (ι → V) : ℚ)
    have hst : ∀ y', P.loop.state (k + 1) y' - (1 - P.pAcc) ^ (k + 1) / (Fintype.card (ι → V) : ℚ)
        = P.loop.step e y' + (1 - P.pAcc) ^ k *
          ((∑ y, P.loop.B y y') / (Fintype.card (ι → V) : ℚ) - (1 - P.pAcc) / (Fintype.card (ι → V) : ℚ)) := by
      intro y'
      simp only [Loop.state, Function.iterate_succ_apply', Loop.step, e]
      simp only [sub_mul, sum_sub_distrib, ← mul_sum]
      ring
    calc ∑ y', |P.loop.state (k + 1) y' - (1 - P.pAcc) ^ (k + 1) / (Fintype.card (ι → V) : ℚ)|
        ≤ ∑ y', (|P.loop.step e y'| + (1 - P.pAcc) ^ k *
            |(∑ y, P.loop.B y y') / (Fintype.card (ι → V) : ℚ) - (1 - P.pAcc) / (Fintype.card (ι → V) : ℚ)|) := by
          refine sum_le_sum fun y' _ => ?_
          rw [hst]
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_nonneg (pow_nonneg hp1 k)]
      _ = ∑ y', |P.loop.step e y'| + (1 - P.pAcc) ^ k * P.defect := by
          rw [sum_add_distrib, ← mul_sum, ReusePolicy.defect]
      _ ≤ P.defect * ∑ j ∈ range k, (1 - P.pAcc) ^ j + (1 - P.pAcc) ^ k * P.defect :=
          by have h1 := P.step_norm_le e
             have h2 : ∑ y, |e y| ≤ P.defect * ∑ j ∈ range k, (1 - P.pAcc) ^ j := ih
             linarith
      _ = P.defect * ∑ j ∈ range (k + 1), (1 - P.pAcc) ^ j := by
          rw [sum_range_succ]; ring

omit [Nonempty V] [Nonempty C] in
lemma ReusePolicy.defect_nonneg (P : ReusePolicy ι V C) : 0 ≤ P.defect :=
  sum_nonneg fun _ _ => abs_nonneg _

lemma geom_le_inv {p : ℚ} (hp : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    ∑ j ∈ range k, (1 - p) ^ j ≤ 1 / p := by
  have h : ∑ j ∈ range k, (1 - p) ^ j * p = 1 - (1 - p) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih, pow_succ]; ring
  rw [le_div_iff₀ hp, sum_mul, h]
  linarith [pow_nonneg (by linarith : (0 : ℚ) ≤ 1 - p) k]

/-- Corollary: `≤ defect / p`. -/
theorem ReusePolicy.state_close' (P : ReusePolicy ι V C) (hp : 0 < P.pAcc) (k : ℕ) :
    ∑ y, |P.loop.state k y - (1 - P.pAcc) ^ k / Fintype.card (ι → V)| ≤ P.defect / P.pAcc :=
  (P.state_close k).trans (by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (geom_le_inv hp P.pAcc_le_one k) P.defect_nonneg)

/-- **Joint law of attempt number and output.** If `Q` is invariant and accepts on the same
`(y, c)` as `P`, then in every attempt the two output laws are within `defect(P) / p` in `ℓ¹`. -/
theorem ReusePolicy.outAt_close (P Q : ReusePolicy ι V C) (hQ : Q.Invariant)
    (hPQ : ∀ y c, P y c = none ↔ Q y c = none) (hp : 0 < P.pAcc) (k : ℕ) :
    ∑ x, |P.loop.outAt k x - Q.loop.outAt k x| ≤ P.defect / P.pAcc := by
  have hpq : P.pAcc = Q.pAcc := by
    unfold ReusePolicy.pAcc; congr 3; ext x; simp [hPQ]
  have hA : ∀ y x, P.loop.A y x = Q.loop.A y x := fun y x => by
    simp only [ReusePolicy.loop, hPQ]
  set N : ℚ := (Fintype.card (ι → V) : ℚ)
  set e : (ι → V) → ℚ := fun y => P.loop.state k y - (1 - P.pAcc) ^ k / N
  have hdiff : ∀ x, P.loop.outAt k x - Q.loop.outAt k x = ∑ y, e y * P.loop.A y x := by
    intro x
    simp only [Loop.outAt, exact_of_invariant Q hQ k, e, sub_mul, sum_sub_distrib, hA, hpq]
    rfl
  calc ∑ x, |P.loop.outAt k x - Q.loop.outAt k x|
      ≤ ∑ x, ∑ y, |e y| * P.loop.A y x := by
        refine sum_le_sum fun x _ => ?_
        rw [hdiff]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine sum_congr rfl fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (P.A_nonneg y x)]
    _ = ∑ y, |e y| * ∑ x, P.loop.A y x := by
        rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ y, |e y| := by
        refine sum_le_sum fun y _ => ?_
        have hrow := P.row y
        have hB : 0 ≤ ∑ y', P.loop.B y y' := sum_nonneg fun y' _ => P.B_nonneg y y'
        calc |e y| * ∑ x, P.loop.A y x ≤ |e y| * 1 :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = |e y| := mul_one _
    _ ≤ _ := P.state_close' hp k

/-- Within the first `K` attempts: `≤ K · defect / p`. -/
theorem ReusePolicy.outUpTo_close (P Q : ReusePolicy ι V C) (hQ : Q.Invariant)
    (hPQ : ∀ y c, P y c = none ↔ Q y c = none) (hp : 0 < P.pAcc) (K : ℕ) :
    ∑ x, |P.loop.outUpTo K x - Q.loop.outUpTo K x| ≤ K * (P.defect / P.pAcc) := by
  calc ∑ x, |P.loop.outUpTo K x - Q.loop.outUpTo K x|
      ≤ ∑ x, ∑ k ∈ range K, |P.loop.outAt k x - Q.loop.outAt k x| := by
        refine sum_le_sum fun x _ => ?_
        simp only [Loop.outUpTo, ← sum_sub_distrib]
        exact abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ range K, ∑ x, |P.loop.outAt k x - Q.loop.outAt k x| := sum_comm
    _ ≤ ∑ _k ∈ range K, P.defect / P.pAcc :=
        sum_le_sum fun k _ => P.outAt_close Q hQ hPQ hp k
    _ = K * (P.defect / P.pAcc) := by simp

/-- **Still running after `K` attempts**: probability at most `(1 − p)^K + defect / p`. -/
theorem ReusePolicy.survive_close (P : ReusePolicy ι V C) (hp : 0 < P.pAcc) (K : ℕ) :
    ∑ y, P.loop.state K y ≤ (1 - P.pAcc) ^ K + P.defect / P.pAcc := by
  set N : ℚ := (Fintype.card (ι → V) : ℚ)
  have hN : (0 : ℚ) < N := Nat.cast_pos.mpr Fintype.card_pos
  have h := P.state_close' hp K
  have : ∑ y, P.loop.state K y ≤ ∑ y, ((1 - P.pAcc) ^ K / N
      + |P.loop.state K y - (1 - P.pAcc) ^ K / N|) :=
    sum_le_sum fun y _ => by linarith [le_abs_self (P.loop.state K y - (1 - P.pAcc) ^ K / N)]
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at this
  rw [show (Fintype.card (ι → V) : ℚ) * ((1 - P.pAcc) ^ K / N) = (1 - P.pAcc) ^ K by
    field_simp [hN.ne']; exact mul_comm _ _] at this
  linarith

/-- Sanity check: invariant policies have defect `0`. -/
theorem ReusePolicy.defect_of_invariant (P : ReusePolicy ι V C) (hP : P.Invariant) :
    P.defect = 0 := by
  have h1 := exact_of_invariant P hP 1
  refine sum_eq_zero fun y' _ => ?_
  have := congrFun h1 y'
  simp only [Loop.state, Function.iterate_one, Loop.step, ReusePolicy.loop, pow_one] at this
  rw [abs_eq_zero, sub_eq_zero, ← this, sum_div]
  refine sum_congr rfl fun y _ => ?_
  simp only [ReusePolicy.loop]; ring

end Approx

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


/-! ## The second moment of `ρ(t)` over the matrix -/

section Main
open Matrix
variable {K : ℕ}

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

section PackingPart

/-!
# Packing bound for NTT cosets in a box

If `(B+1)^n > q^|S|`, a short nonzero vector `v` with vanishing NTT on `S` exists; reducing modulo
the ideal it generates gives `q^|S|` short vectors with distinct NTT values on `S`, and their
translates by the solutions in the box are disjoint. Hence
`#{f ∈ box | f^ = τ on S} · q^|S| ≤ (w + 2nB)^n`.
-/

open Finset Matrix RejOrder AltR0

noncomputable section

namespace Packing

lemma negacyclic_map {R S : Type*} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) (a : Fin n → R) :
    (negacyclic a).map f = negacyclic (f ∘ a) := by
  ext s t
  simp only [Matrix.map_apply, negacyclic, Function.comp]
  split_ifs <;> simp

lemma cast_mulVec {R : Type*} [Ring R] {n : ℕ} (a t : Fin n → ℤ) (s : Fin n) :
    (((negacyclic a *ᵥ t) s : ℤ) : R) = (negacyclic (fun i => (a i : R)) *ᵥ fun i => (t i : R)) s := by
  have := RingHom.map_mulVec (Int.castRingHom R) (negacyclic a) t s
  rw [negacyclic_map] at this
  simpa [Function.comp_def] using this

set_option linter.unusedSectionVars false

variable {q n : ℕ} [NeZero q] [Fact q.Prime]

/-- NTT value of an integer vector. -/
abbrev N (ζ : Fin n → ZMod q) (x : Fin n → ℤ) (k : Fin n) : ZMod q :=
  nttP ζ (fun s => (x s : ZMod q)) k

lemma N_add (ζ : Fin n → ZMod q) (x y : Fin n → ℤ) (k : Fin n) :
    N ζ (x + y) k = N ζ x k + N ζ y k := by
  simp only [N, nttP, Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib]

lemma N_sub (ζ : Fin n → ZMod q) (x y : Fin n → ℤ) (k : Fin n) :
    N ζ (x - y) k = N ζ x k - N ζ y k := by
  simp only [N, nttP, Pi.sub_apply, Int.cast_sub, mul_sub, sum_sub_distrib]

lemma N_ideal {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (v t : Fin n → ℤ) (k : Fin n) : N ζ (negacyclic v *ᵥ t) k = N ζ v k * N ζ t k := by
  have e : (fun s => (((negacyclic v *ᵥ t) s : ℤ) : ZMod q))
      = negacyclic (fun i => (v i : ZMod q)) *ᵥ fun i => (t i : ZMod q) := by
    funext s; rw [cast_mulVec]
  simp only [N]
  rw [e]
  exact h.mul _ _ _

/-- Rows of `negacyclic` applied to a vector with entries in `[0,1)` are bounded by `n·B`. -/
lemma abs_mulVec_le {n : ℕ} (v : Fin n → ℤ) (B : ℕ) (hv : ∀ i, |v i| ≤ B) (u : Fin n → ℚ)
    (hu0 : ∀ j, 0 ≤ u j) (hu1 : ∀ j, u j < 1) (i : Fin n) :
    |(negacyclic (fun i => (v i : ℚ)) *ᵥ u) i| ≤ n * B := by
  simp only [Matrix.mulVec, dotProduct]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ j ∈ (univ : Finset (Fin n)),
      |negacyclic (fun i => (v i : ℚ)) i j * u j| ≤ (B : ℚ) := by
    intro j _
    rw [abs_mul, abs_of_nonneg (hu0 j)]
    have hm : |negacyclic (fun i => (v i : ℚ)) i j| ≤ B := by
      have hb : |(v (i - j) : ℚ)| ≤ B := by exact_mod_cast hv (i - j)
      simp only [negacyclic]; split_ifs <;> simpa using hb
    calc |negacyclic (fun i => (v i : ℚ)) i j| * u j ≤ B * 1 :=
          mul_le_mul hm (hu1 j).le (hu0 j) (by positivity)
      _ = B := mul_one _
  refine (sum_le_sum this).trans (le_of_eq ?_)
  simp

theorem card_coset_le {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (S : Finset (Fin n)) (τ : Fin n → ZMod q) (B : ℕ)
    (hB : q ^ S.card < (B + 1) ^ n) :
    ((hbox lo w).filter fun f => ∀ k ∈ S, nttP ζ (fun s => (f s : ZMod q)) k = τ k).card
        * q ^ S.card ≤ (w + 2 * (n * B)) ^ n := by
  classical
  -- Step 1: a short nonzero vector with vanishing NTT on `S`.
  obtain ⟨v, hv0, hvB, hvS⟩ : ∃ v : Fin n → ℤ, v ≠ 0 ∧ (∀ i, |v i| ≤ B) ∧
      ∀ k ∈ S, N ζ v k = 0 := by
    have hc : (univ : Finset (S → ZMod q)).card
        < (Fintype.piFinset fun _ : Fin n => Finset.Icc (0 : ℤ) B).card := by
      rw [Fintype.card_piFinset, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe]
      simpa using hB
    obtain ⟨x, hx, y, hy, hxy, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
      (f := fun x (k : S) => N ζ x k) (fun _ _ => by simp)
    refine ⟨x - y, sub_ne_zero.mpr hxy, fun i => ?_, fun k hk => ?_⟩
    · have h1 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx i)
      have h2 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hy i)
      simp only [Pi.sub_apply, abs_le]; constructor <;> omega
    · rw [N_sub, sub_eq_zero]
      exact congrFun he ⟨k, hk⟩
  -- Step 3: reduction.
  set M := negacyclic (fun i => (v i : ℚ)) with hM
  have hdet : IsUnit M.det := (hinv v hv0).isUnit
  let fl : (Fin n → ℤ) → Fin n → ℤ := fun x j => ⌊(M⁻¹ *ᵥ fun i => (x i : ℚ)) j⌋
  let red : (Fin n → ℤ) → Fin n → ℤ := fun x => x - negacyclic v *ᵥ fl x
  have hredN : ∀ x, ∀ k ∈ S, N ζ (red x) k = N ζ x k := by
    intro x k hk
    simp only [red]
    rw [N_sub, N_ideal h, hvS k hk, zero_mul, sub_zero]
  have hredB : ∀ x i, |red x i| ≤ (n * B : ℕ) := by
    intro x i
    set t := M⁻¹ *ᵥ fun i => (x i : ℚ)
    have hcast : ((red x i : ℤ) : ℚ) = (M *ᵥ fun j => Int.fract (t j)) i := by
      have hMt : M *ᵥ t = fun i => (x i : ℚ) := by
        simp only [t, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]
      have : (fun j => Int.fract (t j)) = t - fun j => ((fl x j : ℤ) : ℚ) := by
        funext j; rfl
      rw [this, Matrix.mulVec_sub, hMt]
      simp only [red, Pi.sub_apply, Int.cast_sub, cast_mulVec, hM]
    have := abs_mulVec_le v B hvB (fun j => Int.fract (t j)) (fun j => Int.fract_nonneg _)
      (fun j => Int.fract_lt_one _) i
    rw [← hM, ← hcast] at this
    exact_mod_cast this
  -- Step 4: representatives.
  set r := S.card
  set R : Finset (Fin n → ℤ) :=
    Fintype.piFinset fun s => if (s : ℕ) < r then Finset.Ico (0 : ℤ) q else {0}
  have hRcard : R.card = q ^ r := by
    rw [Fintype.card_piFinset]
    have : ∀ s : Fin n, ((if (s : ℕ) < r then Finset.Ico (0 : ℤ) q else {0}).card)
        = if (s : ℕ) < r then q else 1 := by
      intro s; split_ifs <;> simp
    simp_rw [this]
    rw [← Finset.prod_filter, prod_const, Fin.card_filter_val_lt]
    have : r ≤ n := by simpa using Finset.card_le_univ S
    rw [min_eq_right this]
  have hRinj : ∀ x ∈ R, ∀ y ∈ R, (∀ k ∈ S, N ζ x k = N ζ y k) → x = y := by
    intro x hx y hy he
    have hq : 0 < (q : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have mem : ∀ z ∈ R, z ∈ hbox (fun _ => 0) q := by
      intro z hz
      refine Fintype.mem_piFinset.mpr fun s => ?_
      have := Fintype.mem_piFinset.mp hz s
      split_ifs at this
      · simpa using this
      · simp at this; rw [this, Finset.mem_Ico]; exact ⟨le_rfl, by simpa using hq⟩
    refine win_inj_P h.inj le_rfl S (mem x hx) (mem y hy) (fun s hs => ?_) fun k hk => ?_
    · have h1 := Fintype.mem_piFinset.mp hx s
      have h2 := Fintype.mem_piFinset.mp hy s
      simp only [show ¬ ((s : ℕ) < r) from by omega, ↓reduceIte, Finset.mem_singleton] at h1 h2
      rw [h1, h2]
    · exact (N_sub ζ x y k).trans (by rw [he k hk, sub_self])
  -- Step 5: packing.
  set F := (hbox lo w).filter fun f => ∀ k ∈ S, nttP ζ (fun s => (f s : ZMod q)) k = τ k
  have hmaps : ∀ p ∈ F ×ˢ R, (p.1 + red p.2) ∈ hbox (fun s => lo s - (n * B : ℕ)) (w + 2 * (n * B)) := by
    intro p hp
    obtain ⟨hf, -⟩ := Finset.mem_product.mp hp
    refine Fintype.mem_piFinset.mpr fun s => ?_
    have h1 := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 s)
    have h2 := abs_le.mp (hredB p.2 s)
    rw [Finset.mem_Ico, Pi.add_apply]
    push_cast at h2 ⊢
    constructor <;> linarith [h2.1, h2.2]
  have hinj : Set.InjOn (fun p : (Fin n → ℤ) × (Fin n → ℤ) => p.1 + red p.2)
      ((F ×ˢ R : Finset _) : Set _) := by
    rintro ⟨f, x⟩ hp ⟨f', x'⟩ hp' he
    obtain ⟨hf, hx⟩ := Finset.mem_product.mp hp
    obtain ⟨hf', hx'⟩ := Finset.mem_product.mp hp'
    simp only at he hf hx hf' hx'
    have hxx : x = x' := by
      refine hRinj x hx x' hx' fun k hk => ?_
      have e := congrArg (fun z => N ζ z k) he
      simp only [N_add] at e
      have t1 := (Finset.mem_filter.mp hf).2 k hk
      have t2 := (Finset.mem_filter.mp hf').2 k hk
      rw [← hredN x k hk, ← hredN x' k hk]
      simp only [N] at e ⊢
      rw [t1, t2] at e
      exact add_left_cancel e
    subst hxx
    simp only [Prod.mk.injEq, and_true]
    exact add_right_cancel he
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, hRcard, card_hbox] at this
  exact this

end Packing

end

end PackingPart

section NcInvPart

open Polynomial Matrix RejOrder

namespace Packing


/-- Column `t` of `negacyclic a`, read in the powers of `r` with `r ^ n = -1`, is `A * r ^ t`. -/
lemma negacyclic_col_sum {L : Type*} [CommRing L] {n : ℕ} [NeZero n] (r : L) (hr : r ^ n = -1)
    (a : Fin n → L) (t : Fin n) :
    ∑ s, negacyclic a s t * r ^ (s : ℕ) = (∑ k, a k * r ^ (k : ℕ)) * r ^ (t : ℕ) := by
  calc ∑ s, negacyclic a s t * r ^ (s : ℕ) = ∑ s : Fin n, r ^ (s : ℕ) * negacyclic a s t :=
        Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = _ := by
        rw [negacyclic_col r hr, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by rw [pow_add, mul_assoc]

/-- General criterion: if `r ^ n = -1` in a domain and `1, r, …, r^(n-1)` are independent,
then `negacyclic a` is nonsingular for every nonzero `a`. -/
theorem negacyclic_det_ne_zero_of {K L : Type*} [Field K] [CommRing L] [IsDomain L] [Algebra K L]
    {n : ℕ} [NeZero n] (r : L) (hr : r ^ n = -1)
    (hli : LinearIndependent K (fun i : Fin n => r ^ (i : ℕ)))
    (a : Fin n → K) (ha : a ≠ 0) : (negacyclic a).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hA : (∑ k, a k • r ^ (k : ℕ)) ≠ 0 := by
    intro h
    exact ha (funext fun i => Fintype.linearIndependent_iff.mp hli a h i)
  have hX : (∑ t, x t • r ^ (t : ℕ)) ≠ 0 := by
    intro h
    exact hx0 (funext fun i => Fintype.linearIndependent_iff.mp hli x h i)
  apply mul_ne_zero hA hX
  have key : ∀ t : Fin n, ∑ s, algebraMap K L (negacyclic a s t) * r ^ (s : ℕ)
      = (∑ k, a k • r ^ (k : ℕ)) * r ^ (t : ℕ) := by
    intro t
    have := negacyclic_col_sum r hr (fun i => algebraMap K L (a i)) t
    simp only [Algebra.smul_def]
    rw [← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [negacyclic]; split_ifs <;> simp
  calc (∑ k, a k • r ^ (k : ℕ)) * ∑ t, x t • r ^ (t : ℕ)
      = ∑ t, x t • ∑ s, algebraMap K L (negacyclic a s t) * r ^ (s : ℕ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [key, mul_smul_comm]
    _ = ∑ s, (negacyclic a *ᵥ x) s • r ^ (s : ℕ) := by
        simp only [Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        simp only [Algebra.smul_def, map_mul]; ring
    _ = 0 := by simp [hx]

lemma X_pow_two_pow_add_one_eq_cyclotomic (k : ℕ) :
    (X ^ (2 ^ k) + 1 : ℚ[X]) = cyclotomic (2 ^ (k + 1)) ℚ := by
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ, add_comm]

/-- For `n = 2 ^ k`, `negacyclic a` over ℚ is nonsingular for every nonzero `a`. -/
theorem negacyclic_det_ne_zero_two_pow (k : ℕ) (a : Fin (2 ^ k) → ℚ) (ha : a ≠ 0) :
    (negacyclic a).det ≠ 0 := by
  obtain ⟨f, hf⟩ : ∃ f : ℚ[X], f = X ^ (2 ^ k) + 1 := ⟨_, rfl⟩
  have hirr : Irreducible f := by
    rw [hf, X_pow_two_pow_add_one_eq_cyclotomic]
    exact cyclotomic.irreducible_rat (by positivity)
  have hmon : f.Monic := by
    rw [hf, ← C_1]; exact monic_X_pow_add_C _ (by positivity)
  have hdeg : f.natDegree = 2 ^ k := by rw [hf, ← C_1]; exact natDegree_X_pow_add_C
  have hmin : minpoly ℚ (AdjoinRoot.root f) = f := by
    have := AdjoinRoot.minpoly_root hirr.ne_zero
    rw [hmon.leadingCoeff] at this; simpa using this
  have hli := linearIndependent_pow (K := ℚ) (AdjoinRoot.root f)
  have hr : AdjoinRoot.root f ^ (2 ^ k) = -1 := by
    have h0 : AdjoinRoot.mk f (X ^ (2 ^ k) + 1) = 0 := by rw [← hf]; exact AdjoinRoot.mk_self
    rw [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  revert hli
  generalize hm : (minpoly ℚ (AdjoinRoot.root f)).natDegree = m
  rw [hmin, hdeg] at hm
  subst hm
  intro hli
  have : Fact (Irreducible f) := ⟨hirr⟩
  exact negacyclic_det_ne_zero_of (AdjoinRoot.root f) hr hli a ha

theorem negacyclic_det_ne_zero (v : Fin 256 → ℤ) (hv : v ≠ 0) :
    (negacyclic (fun i => (v i : ℚ))).det ≠ 0 := by
  have h := negacyclic_det_ne_zero_two_pow 8 (fun i => (v i : ℚ)) (by
    intro h; apply hv; funext i; simpa using congrFun h i)
  exact h

end Packing

end NcInvPart

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

section AltR0QPart

/-!
# alt-r0 degenerate-slot probabilities with `1/q` in place of `1/w`

Versions of `prob_Z`, `prob_deg_ge`, `prob_Z_exc`, `prob_deg_exc` in which the head counts are
bounded by the packing bound `Packing.card_coset_le`, at the cost of the constant
`cst = (w + 2nB)^n / w^n`.
-/

open Finset

noncomputable section

namespace AltR0
open RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n L : ℕ}

omit [Fact q.Prime] in
lemma qpow_lt_of_le {B a b : ℕ} (hab : a ≤ b) (hb : q ^ b < (B + 1) ^ n) :
    q ^ a < (B + 1) ^ n :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne q)) hab) hb

/-- Rational form of `Packing.card_coset_le`. -/
lemma card_coset_q {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (S : Finset (Fin n)) (τ : Fin n → ZMod q) (B : ℕ)
    (hB : q ^ S.card < (B + 1) ^ n) :
    (((hbox lo w).filter fun f => ∀ k ∈ S, nttP ζ (fun s => (f s : ZMod q)) k = τ k).card : ℚ)
      ≤ ((w : ℚ) + 2 * (n * B)) ^ n / (q : ℚ) ^ S.card := by
  have hc := Packing.card_coset_le (lo := lo) (w := w) h hinv S τ B hB
  have hq : (0 : ℚ) < (q : ℚ) ^ S.card := by
    have : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    positivity
  rw [le_div_iff₀ hq]
  exact_mod_cast hc

/-- Head pairs whose difference has vanishing NTT on `D`, packing version. -/
lemma card_head_q {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (D : Finset (Fin n)) (B : ℕ) (hB : q ^ D.card < (B + 1) ^ n) :
    (((hbox lo w ×ˢ hbox lo w).filter fun ff =>
        ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0).card : ℚ)
      ≤ (w : ℚ) ^ n * (((w : ℚ) + 2 * (n * B)) ^ n / (q : ℚ) ^ D.card) := by
  have e : ((hbox lo w ×ˢ hbox lo w).filter fun ff =>
        ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0).card
      = ∑ g ∈ hbox lo w, ((hbox lo w).filter fun f => ∀ k ∈ D,
          nttP ζ (fun s => (f s : ZMod q)) k = nttP ζ (fun s => (g s : ZMod q)) k).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine sum_congr rfl fun g _ => ?_
    rw [Finset.card_filter]
    refine sum_congr rfl fun f _ => ?_
    simp only [nttP_intsub, sub_eq_zero]
  rw [e]
  push_cast
  calc ∑ g ∈ hbox lo w, (((hbox lo w).filter fun f => ∀ k ∈ D,
          nttP ζ (fun s => (f s : ZMod q)) k = nttP ζ (fun s => (g s : ZMod q)) k).card : ℚ)
      ≤ ∑ _g ∈ hbox lo w, ((w : ℚ) + 2 * (n * B)) ^ n / (q : ℚ) ^ D.card :=
        sum_le_sum fun g _ => card_coset_q h hinv D _ B hB
    _ = _ := by rw [sum_const, card_hbox, nsmul_eq_mul]; push_cast; ring

/-- Head pairs with `y₁` vanishing on `X₁`, `y₁'` vanishing on `X₂` and the difference
vanishing on `D`, packing version. -/
lemma card_head2_q {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (X₁ X₂ D : Finset (Fin n)) (B : ℕ)
    (hB1 : q ^ X₁.card < (B + 1) ^ n) (hB2 : q ^ (X₂ ∪ D).card < (B + 1) ^ n) :
    (((hbox lo w ×ˢ hbox lo w).filter fun ff =>
        (∀ k ∈ X₁, nttP ζ (fun s => (ff.1 s : ZMod q)) k = 0) ∧
        (∀ k ∈ X₂, nttP ζ (fun s => (ff.2 s : ZMod q)) k = 0) ∧
        ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0).card : ℚ)
      ≤ (((w : ℚ) + 2 * (n * B)) ^ n / (q : ℚ) ^ X₁.card)
        * (((w : ℚ) + 2 * (n * B)) ^ n / (q : ℚ) ^ (X₂ ∪ D).card) := by
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
  refine (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans card_biUnion_le)).trans ?_
  push_cast
  refine (Finset.sum_le_sum fun f _ => (Nat.cast_le.mpr card_image_le).trans
    (card_coset_q h hinv _ (c f) B hB2)).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_coset_q h hinv X₁ _ B hB1) (by positivity)

/-- **A given set of slots is degenerate** with probability at most `cst · p^|Z|`,
`p = 1/q + (2γ₁)^{-(L-1)}`, `cst = (w + 2nB)^n / w^n`. -/
lemma prob_Z_q {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (B : ℕ) (Z : Finset (Fin n)) (hZ : q ^ Z.card < (B + 1) ^ n) :
    prob (trip lo w γ₁ h₀) (fun x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2))
      ≤ ((w : ℚ) + 2 * (n * B)) ^ n / (w : ℚ) ^ n
        * (1 / (q : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ Z.card := by
  set A : Finset (Fin n) → Finset ((Fin n → ℤ) × (Fin n → ℤ)) := fun D =>
    (hbox lo w ×ˢ hbox lo w).filter fun ff =>
      ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0
  set Bt : Finset (Fin n) → Finset (Fin L → Fin n → ℤ) := fun E =>
    (tbox γ₁ h₀).filter fun t => ∀ j, j ≠ h₀ → ∀ k ∈ E, nttP ζ (fun s => (t j s : ZMod q)) k = 0
  have hsub : (trip lo w γ₁ h₀).filter (fun x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2))
      ⊆ Z.powerset.biUnion fun D => A D ×ˢ Bt (Z \ D) := by
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
  have hq' : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hcard : ((trip lo w γ₁ h₀).card : ℚ)
      = (w : ℚ) ^ n * (w : ℚ) ^ n * (((2 * γ₁ : ℚ)) ^ n) ^ (L - 1) := by
    rw [trip, card_product, card_product, card_hbox, card_tbox]; push_cast; ring
  unfold prob
  rw [div_le_iff₀ (by rw [hcard]; positivity)]
  have hcount := Finset.card_le_card hsub
  refine (Nat.cast_le.mpr (hcount.trans card_biUnion_le)).trans ?_
  push_cast
  have hprod : (1 / (q : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ Z.card
      = ∑ D ∈ Z.powerset, (1 / (q : ℚ)) ^ D.card * (1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ (Z \ D).card := by
    rw [← Finset.prod_const, Finset.prod_add]
    simp only [prod_const]
  rw [hprod, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun D hD => ?_
  have hDZ : D ⊆ Z := Finset.mem_powerset.mp hD
  have hEn : (Z \ D).card ≤ n := by simpa using Finset.card_le_univ (Z \ D)
  rw [card_product]
  push_cast
  have ha : ((A D).card : ℚ)
      ≤ (w : ℚ) ^ n * (((w : ℚ) + 2 * (n * B)) ^ n / (q : ℚ) ^ D.card) :=
    card_head_q h hinv D B (qpow_lt_of_le (Finset.card_le_card hDZ) hZ)
  have hb : ((Bt (Z \ D)).card : ℚ) ≤ (((2 * γ₁ : ℚ)) ^ (n - (Z \ D).card)) ^ (L - 1) := by
    exact_mod_cast card_tail_le h.inj hγ1 hγ h₀ (Z \ D)
  refine (mul_le_mul ha hb (by positivity) (by positivity)).trans (le_of_eq ?_)
  rw [hcard, pow_sub₀ _ hg'.ne' hEn]
  have hwne : (w : ℚ) ≠ 0 := hw'.ne'
  have hgne : (2 * γ₁ : ℚ) ≠ 0 := hg'.ne'
  have hqne : (q : ℚ) ≠ 0 := hq'.ne'
  simp only [div_eq_mul_inv, one_mul, inv_pow, mul_pow, ← pow_mul]
  field_simp
  ring

/-- **`d` degenerate slots** occur with probability at most `cst · C(n,d) · p^d`. -/
lemma prob_deg_ge_q {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (B : ℕ) (d : ℕ) (hd : q ^ d < (B + 1) ^ n) :
    prob (trip lo w γ₁ h₀) (fun x => d ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card)
      ≤ ((w : ℚ) + 2 * (n * B)) ^ n / (w : ℚ) ^ n
        * (n.choose d * (1 / (q : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ d) := by
  refine (prob_le_sum _ ((univ : Finset (Fin n)).powersetCard d) _
    (fun Z x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)) fun x _ hx => ?_).trans ?_
  · obtain ⟨Z, hZ, hc⟩ := Finset.exists_subset_card_eq hx
    exact ⟨Z, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩, hZ⟩
  · refine (Finset.sum_le_sum fun Z hZ => prob_Z_q h hinv hw0 hγ1 hγ h₀ B Z
      (by rw [(Finset.mem_powersetCard.mp hZ).2]; exact hd)).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun Z hZ => by rw [(Finset.mem_powersetCard.mp hZ).2], sum_const,
      Finset.card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- **A given set of slots is degenerate and contains an exceptional slot** with probability at
most `cst² · ((p + e)^|Z| - p^|Z|)`, `p = 1/q + (2γ₁)^{-(L-1)}`, `e = 2 / (q (2γ₁)^(L-1))`. -/
lemma prob_Z_exc_q {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (B : ℕ) (Z : Finset (Fin n)) (hZ : q ^ Z.card < (B + 1) ^ n) :
    prob (trip lo w γ₁ h₀) (fun x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) ∧
        (Z ∩ exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty)
      ≤ (((w : ℚ) + 2 * (n * B)) ^ n / (w : ℚ) ^ n) ^ 2
        * ((1 / (q : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)
          + 2 / ((q : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ Z.card
        - (1 / (q : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ Z.card) := by
  set A : Finset (Fin n) → Finset (Fin n) → Finset (Fin n) →
      Finset ((Fin n → ℤ) × (Fin n → ℤ)) := fun X₁ X₂ D =>
    (hbox lo w ×ˢ hbox lo w).filter fun ff =>
        (∀ k ∈ X₁, nttP ζ (fun s => (ff.1 s : ZMod q)) k = 0) ∧
        (∀ k ∈ X₂, nttP ζ (fun s => (ff.2 s : ZMod q)) k = 0) ∧
        ∀ k ∈ D, nttP ζ (fun s => ((ff.1 s - ff.2 s : ℤ) : ZMod q)) k = 0 with hA
  set Bt : Finset (Fin n) → Finset (Fin L → Fin n → ℤ) := fun E =>
    (tbox γ₁ h₀).filter fun t => ∀ j, j ≠ h₀ → ∀ k ∈ E, nttP ζ (fun s => (t j s : ZMod q)) k = 0
    with hBt
  have hsub : (trip lo w γ₁ h₀).filter (fun x =>
        Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) ∧
        (Z ∩ exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty)
      ⊆ (Z.powerset.erase ∅).biUnion fun X => X.powerset.biUnion fun X₁ =>
          (Z \ X).powerset.biUnion fun D => A X₁ (X \ X₁) D ×ˢ Bt (X ∪ ((Z \ X) \ D)) := by
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
  have hq' : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hcard : ((trip lo w γ₁ h₀).card : ℚ)
      = (w : ℚ) ^ n * (w : ℚ) ^ n * (((2 * γ₁ : ℚ)) ^ n) ^ (L - 1) := by
    rw [trip, card_product, card_product, card_hbox, card_tbox]; push_cast; ring
  set cst : ℚ := ((w : ℚ) + 2 * (n * B)) ^ n / (w : ℚ) ^ n with hcst
  set τ : ℚ := 1 / ((2 * γ₁ : ℚ)) ^ (L - 1) with hτ
  set a : ℚ := 1 / ((q : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1)) with ha
  have hterm : ∀ X ∈ Z.powerset.erase ∅, ∀ X₁ ∈ X.powerset, ∀ D ∈ (Z \ X).powerset,
      (((A X₁ (X \ X₁) D ×ˢ Bt (X ∪ ((Z \ X) \ D))).card : ℕ) : ℚ)
        ≤ cst ^ 2 * ((a ^ X₁.card * a ^ (X \ X₁).card)
          * ((1 / (q : ℚ)) ^ D.card * τ ^ ((Z \ X) \ D).card))
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
    have hB1 : q ^ X₁.card < (B + 1) ^ n :=
      qpow_lt_of_le (Finset.card_le_card (hX₁X.trans hXZ)) hZ
    have hB2 : q ^ ((X \ X₁) ∪ D).card < (B + 1) ^ n := by
      refine qpow_lt_of_le (Finset.card_le_card ?_) hZ
      refine Finset.union_subset ((Finset.sdiff_subset).trans hXZ) (hDZ.trans Finset.sdiff_subset)
    have hc1 := card_head2_q (lo := lo) (w := w) h hinv X₁ (X \ X₁) D B hB1 hB2
    have hc2 := card_tail_le h.inj hγ1 hγ h₀ (X ∪ ((Z \ X) \ D))
    rw [Finset.card_union_of_disjoint hdisj1] at hc1
    rw [Finset.card_union_of_disjoint hdisj2,
      ← Finset.card_sdiff_add_card_eq_card hX₁X] at hc2
    have hn3 : (X \ X₁).card + X₁.card + ((Z \ X) \ D).card ≤ n := by
      rw [Finset.card_sdiff_add_card_eq_card hX₁X, ← Finset.card_union_of_disjoint hdisj2]
      simpa using Finset.card_le_univ (X ∪ ((Z \ X) \ D))
    rw [card_product]
    push_cast
    have hb' : ((Bt (X ∪ ((Z \ X) \ D))).card : ℚ)
        ≤ (((2 * γ₁ : ℚ)) ^ (n - ((X \ X₁).card + X₁.card + ((Z \ X) \ D).card))) ^ (L - 1) := by
      exact_mod_cast hc2
    refine (mul_le_mul hc1 hb' (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [hcard, pow_right_comm (2 * (γ₁ : ℚ)) n (L - 1), pow_right_comm (2 * (γ₁ : ℚ)) _ (L - 1)]
    simp only [ha, hτ, hcst]
    have hG : (0 : ℚ) < ((2 * γ₁ : ℚ)) ^ (L - 1) := by positivity
    generalize ((2 * γ₁ : ℚ)) ^ (L - 1) = G at hG ⊢
    have hwne : (w : ℚ) ≠ 0 := hw'.ne'
    have hqne : (q : ℚ) ≠ 0 := hq'.ne'
    have hGne : G ≠ 0 := hG.ne'
    rw [pow_sub₀ _ hGne hn3]
    simp only [one_div, mul_inv, inv_pow, mul_pow, pow_add, div_pow]
    field_simp
  have hsum : ∑ X ∈ Z.powerset.erase ∅, ∑ X₁ ∈ X.powerset, ∑ D ∈ (Z \ X).powerset,
      (a ^ X₁.card * a ^ (X \ X₁).card) * ((1 / (q : ℚ)) ^ D.card * τ ^ ((Z \ X) \ D).card)
      = (1 / (q : ℚ) + τ + 2 / ((q : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ Z.card
        - (1 / (q : ℚ) + τ) ^ Z.card := by
    have h1 : ∀ X ∈ Z.powerset.erase ∅, ∑ X₁ ∈ X.powerset, ∑ D ∈ (Z \ X).powerset,
        (a ^ X₁.card * a ^ (X \ X₁).card) * ((1 / (q : ℚ)) ^ D.card * τ ^ ((Z \ X) \ D).card)
        = (a + a) ^ X.card * (1 / (q : ℚ) + τ) ^ (Z \ X).card := by
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
  rw [← hsum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun X hX => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun X₁ hX₁ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun D hD => ?_
  exact_mod_cast hterm X hX X₁ hX₁ D hD

/-- **`d` degenerate slots, one of them exceptional,** occur with probability at most
`cst² · C(n,d) · ((p + e)^d - p^d)`. -/
theorem prob_deg_exc_q {ζ : Fin n → ZMod q} (h : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)))
    (hinv : ∀ v : Fin n → ℤ, v ≠ 0 → (negacyclic (fun i => (v i : ℚ))).det ≠ 0)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (B : ℕ) (d : ℕ) (hd1 : 1 ≤ d) (hd : q ^ d < (B + 1) ^ n) :
    prob (trip lo w γ₁ h₀) (fun x => d ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card ∧
        (exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty)
      ≤ (((w : ℚ) + 2 * (n * B)) ^ n / (w : ℚ) ^ n) ^ 2
        * (n.choose d * ((1 / (q : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)
            + 2 / ((q : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ d
          - (1 / (q : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ d)) := by
  refine (prob_le_sum _ ((univ : Finset (Fin n)).powersetCard d) _
    (fun Z x => Z ⊆ degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2) ∧
      (Z ∩ exc ζ h₀ x.1.1 x.1.2 x.2).Nonempty) fun x _ hx => ?_).trans ?_
  · obtain ⟨hc, s, hs⟩ := hx
    have hsd := exc_sub_degS ζ h₀ x.1.1 x.1.2 x.2 hs
    obtain ⟨Z, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq (s := {s})
      (Finset.singleton_subset_iff.mpr hsd) (by simpa using hd1) hc
    exact ⟨Z, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h3⟩, h2,
      ⟨s, Finset.mem_inter.mpr ⟨h1 (Finset.mem_singleton_self s), hs⟩⟩⟩
  · refine (Finset.sum_le_sum fun Z hZ => prob_Z_exc_q h hinv hw0 hγ1 hγ h₀ B Z
      (by rw [(Finset.mem_powersetCard.mp hZ).2]; exact hd)).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun Z hZ => by rw [(Finset.mem_powersetCard.mp hZ).2], sum_const,
      Finset.card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

end AltR0

end

end AltR0QPart

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

open Classical in
/-- **Sharper second moment, general probabilities.** As `var_le_sharp`, but the slot
probabilities are hypotheses: `c_m C(n,e) p_m^e` for `e` degenerate slots, and
`c_e C(n,e) (p_e^e − p_m^e)` for those with an exceptional one. -/
theorem var_le_gen
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
    (pm pe cm ce : ℚ)
    (hPm : ∀ e, e ≤ dm₁ + 1 → prob (trip lo w γ₁ h₀) (fun x =>
        e ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card) ≤ cm * (n.choose e * pm ^ e))
    (hPexc : ∀ e, 1 ≤ e → e ≤ dm₂ + 1 → prob (trip lo w γ₁ h₀) (fun x =>
        e ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card ∧ ¬ NX ζ h₀ x)
      ≤ ce * (n.choose e * (pe ^ e - pm ^ e))) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, (rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2) / (tbox (n := n) γ₁ h₀).card)
      ≤ cm * ((∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2 *
          ∑ d ∈ Icc 1 dm₁, (n.choose d * pm ^ d) * Eb₂ d
        + n.choose (dm₁ + 1) * pm ^ (dm₁ + 1))
      + ce * ((∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) ^ 2 *
          ∑ d ∈ Icc 1 dm₂, (n.choose d * (pe ^ d - pm ^ d)) * Eb₁ d ^ 2
        + n.choose (dm₂ + 1) * (pe ^ (dm₂ + 1) - pm ^ (dm₂ + 1))) := by
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
  have hprobs : ∀ e, e ≤ dm₁ + 1 → ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card : ℚ))
      / (trip lo w γ₁ h₀).card ≤ cm * (n.choose e * pm ^ e) := fun e he => hPm e he
  have hprobs' : ∀ e, 1 ≤ e → e ≤ dm₂ + 1 → ((((trip lo w γ₁ h₀).filter fun x =>
      e ≤ D x ∧ ¬ NX ζ h₀ x).card : ℚ)) / (trip lo w γ₁ h₀).card
      ≤ ce * (n.choose e * (pe ^ e - pm ^ e)) := fun e he he' => hPexc e he he'
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
        rw [mul_add, mul_add]
        refine add_le_add (add_le_add ?_ (hprobs (dm₁ + 1) le_rfl))
          (add_le_add ?_ (hprobs' (dm₂ + 1) (by omega) le_rfl))
        · rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_le_sum fun e he => ?_
          have := hprobs e (by have := (Finset.mem_Icc.mp he).2; omega)
          calc μ ^ 2 * Eb₂ e * ((((trip lo w γ₁ h₀).filter fun x => e ≤ D x).card : ℚ)
                / (trip lo w γ₁ h₀).card)
              ≤ μ ^ 2 * Eb₂ e * (cm * (n.choose e * pm ^ e)) :=
                mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg _) (hEb₂0 e))
            _ = _ := by ring
        · rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_le_sum fun e he => ?_
          have := hprobs' e (Finset.mem_Icc.mp he).1 (by have := (Finset.mem_Icc.mp he).2; omega)
          calc μ ^ 2 * Eb₁ e ^ 2 * ((((trip lo w γ₁ h₀).filter fun x =>
                e ≤ D x ∧ ¬ NX ζ h₀ x).card : ℚ) / (trip lo w γ₁ h₀).card)
              ≤ μ ^ 2 * Eb₁ e ^ 2 * (ce * (n.choose e * (pe ^ e - pm ^ e))) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring

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
        (∑ t ∈ tbox (2 ^ 17) h₀, |rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 95232 78 v lo w h₀ a t
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
        (∑ t ∈ tbox (2 ^ 19) h₀, |rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 196 v lo w h₀ a t
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
        (∑ t ∈ tbox (2 ^ 19) h₀, |rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 120 v lo w h₀ a t
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

/-- **ML-DSA-44, second moment.** `E_A E_t (ρ_c(t) − μ)² ≤ μ² / 2^294`. -/
theorem var_mldsa44_sharp {v : Fin (4 * 256) → ℤ} (hv : Bounded 78 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 17 ∨ w = 2 * (2 ^ 17 - 78) - 1) (h₀ : Fin 4) :
    avg (fun a : Fin 4 → Fin 4 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 17) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 95232 78 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 17) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ (2 * 147) := by
  rcases hw with rfl | rfl
  · exact var_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 25 19 26 (2 * 147)
      (by norm_num) (by norm_num) num_44_full
  · exact var_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 25 19 26 (2 * 147)
      (by norm_num) (by norm_num) num_44_z

/-- **ML-DSA-65, second moment.** `E_A E_t (ρ_c(t) − μ)² ≤ μ² / 2^364`. -/
theorem var_mldsa65_sharp {v : Fin (6 * 256) → ℤ} (hv : Bounded 196 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 196) - 1) (h₀ : Fin 5) :
    avg (fun a : Fin 6 → Fin 5 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 196 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ (2 * 182) := by
  rcases hw with rfl | rfl
  · exact var_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 26 19 27 (2 * 182)
      (by norm_num) (by norm_num) num_65_full
  · exact var_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 26 19 27 (2 * 182)
      (by norm_num) (by norm_num) num_65_z

/-- **ML-DSA-87, second moment.** `E_A E_t (ρ_c(t) − μ)² ≤ μ² / 2^380`. -/
theorem var_mldsa87_sharp {v : Fin (8 * 256) → ℤ} (hv : Bounded 120 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 120) - 1) (h₀ : Fin 7) :
    avg (fun a : Fin 8 → Fin 7 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 120 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ (2 * 190) := by
  rcases hw with rfl | rfl
  · exact var_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 17 28 (2 * 190)
      (by norm_num) (by norm_num) num_87_full
  · exact var_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 17 28 (2 * 190)
      (by norm_num) (by norm_num) num_87_z

end MLDSASharp


end AltR0

end

end AltR0SharpPart

section AltR0GenPart

open Finset Matrix

noncomputable section

namespace AltR0
open RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

/-- Main part of the kernel-checked sum (`b²`-weighted counts). -/
def numM (e q n K Bd Dc pn pd dm₁ M : ℕ) : ℕ :=
  sumF (fun d => if 1 ≤ d then chooseC n d * pn ^ d * pd ^ (M - d)
      * ENr e q n K (Bd ^ 2) (Dc ^ 2) d else 0) (dm₁ + 1)
    + chooseC n (dm₁ + 1) * pn ^ (dm₁ + 1) * pd ^ (M - (dm₁ + 1)) * q ^ (2 * (K * n))

/-- Exceptional part of the kernel-checked sum (crude counts). -/
def numE (e q n K Bd Dc pn pn' pd dm₂ M : ℕ) : ℕ :=
  sumF (fun d => if 1 ≤ d then chooseC n d * (pn' ^ d - pn ^ d) * pd ^ (M - d)
      * ENr e q n K Bd Dc d ^ 2 else 0) (dm₂ + 1)
    + chooseC n (dm₂ + 1) * (pn' ^ (dm₂ + 1) - pn ^ (dm₂ + 1)) * pd ^ (M - (dm₂ + 1))
      * q ^ (2 * (K * n))

variable {ζ : Fin n → ZMod q}

open Classical in
/-- **Relative second moment, general slot probabilities.** With `p_m = pn/pd`, `p_e = pn'/pd`,
constants `c_m = cn/wn` and `c_e = c_m²`, the integer inequality
`2^k (cn·wn·numM + cn²·numE) ≤ Dc^(2Kn) pd^M wn²` gives `E_A E_t (ρ − μ)² ≤ μ²/2^k`. -/
theorem var_rel_gen
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {cz : ZMod q} (hwz : ∀ k, ζ k ^ n = cz) (hn : 0 < n)
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v)
    {lo : Fin n → ℤ} {w : ℕ} (hw0 : 0 < w) (hwq : w ≤ q) (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (h₀ : Fin L) (e dm₁ dm₂ M k : ℕ)
    (hM₁ : dm₁ + 1 ≤ M) (hM₂ : dm₂ + 1 ≤ M)
    (cn wn pn pn' pd : ℕ) (hwn : 0 < wn) (hpd : 0 < pd) (hpp : pn ≤ pn')
    (hPm : ∀ e', e' ≤ dm₁ + 1 → prob (trip lo w γ₁ h₀) (fun x =>
        e' ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card)
      ≤ (cn : ℚ) / wn * (n.choose e' * ((pn : ℚ) / pd) ^ e'))
    (hPexc : ∀ e', 1 ≤ e' → e' ≤ dm₂ + 1 → prob (trip lo w γ₁ h₀) (fun x =>
        e' ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card ∧ ¬ NX ζ h₀ x)
      ≤ ((cn : ℚ) / wn) ^ 2 * (n.choose e' * (((pn' : ℚ) / pd) ^ e' - ((pn : ℚ) / pd) ^ e')))
    (hnum : 2 ^ k * (cn * wn * numM e q n K (q - mb * (2 * (γ₂ - β) - 1))
          (mb * (2 * (γ₂ - β) - 1)) pn pd dm₁ M
        + cn ^ 2 * numE e q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
          pn pn' pd dm₂ M)
      ≤ (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n)) * pd ^ M * wn ^ 2) :
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
  refine (var_le_gen h hw0 hwq hγ1 hγ h₀ bt (by positivity) hbad dm₁ dm₂
    (fun d => (ENr e q n K Bd Dc d : ℚ) / (Dc : ℚ) ^ (K * n))
    (fun d => (ENr e q n K (Bd ^ 2) (Dc ^ 2) d : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) ^ (K * n))
    (fun d => by positivity) hEb₁ hEb₂ _ _ _ _ hPm hPexc).trans ?_
  rw [hμ]
  have hpd' : (0 : ℚ) < pd := by exact_mod_cast hpd
  have hQ : (0 : ℚ) < (q : ℚ) ^ (2 * (K * n)) := by positivity
  have hDn : (0 : ℚ) < (Dc : ℚ) ^ (K * n) := by positivity
  set Q : ℚ := (q : ℚ) ^ (2 * (K * n))
  have hμ2 : (((Dc : ℚ) / q) ^ (K * n)) ^ 2 = (Dc : ℚ) ^ (2 * (K * n)) / Q := by
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm (K * n) 2]
  have hsplit : ∀ d, d ≤ M → (pd : ℚ) ^ M = (pd : ℚ) ^ d * (pd : ℚ) ^ (M - d) := fun d hd => by
    rw [← pow_add]; congr 1; omega
  have hle : ∀ d, pn ^ d ≤ pn' ^ d := fun d => Nat.pow_le_pow_left hpp d
  -- the four parts of `numL2`, as rationals over `Q · pd^M`
  set A₁ : ℚ := ∑ d ∈ Icc 1 dm₁, (n.choose d : ℚ) * (pn : ℚ) ^ d * (pd : ℚ) ^ (M - d)
    * (ENr e q n K (Bd ^ 2) (Dc ^ 2) d : ℚ)
  set A₂ : ℚ := (n.choose (dm₁ + 1) : ℚ) * (pn : ℚ) ^ (dm₁ + 1) * (pd : ℚ) ^ (M - (dm₁ + 1)) * Q
  set A₃ : ℚ := ∑ d ∈ Icc 1 dm₂, (n.choose d : ℚ) * (((pn' : ℚ) ^ d - (pn : ℚ) ^ d))
    * (pd : ℚ) ^ (M - d) * (ENr e q n K Bd Dc d : ℚ) ^ 2
  set A₄ : ℚ := (n.choose (dm₂ + 1) : ℚ) * ((pn' : ℚ) ^ (dm₂ + 1) - (pn : ℚ) ^ (dm₂ + 1))
    * (pd : ℚ) ^ (M - (dm₂ + 1)) * Q
  have hnumQ : (2 : ℚ) ^ k * ((cn : ℚ) * wn * (A₁ + A₂) + (cn : ℚ) ^ 2 * (A₃ + A₄))
      ≤ (Dc : ℚ) ^ (2 * (K * n)) * (pd : ℚ) ^ M * (wn : ℚ) ^ 2 := by
    have := (Nat.cast_le (α := ℚ)).mpr hnum
    unfold numM numE at this
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
  have hwn' : (0 : ℚ) < wn := by exact_mod_cast hwn
  rw [hμ2, e1, e2, e3, e4]
  rw [show (cn : ℚ) / wn * (A₁ / (Q * (pd : ℚ) ^ M) + A₂ / (Q * (pd : ℚ) ^ M))
      + ((cn : ℚ) / wn) ^ 2 * (A₃ / (Q * (pd : ℚ) ^ M) + A₄ / (Q * (pd : ℚ) ^ M))
      = ((cn : ℚ) * wn * (A₁ + A₂) + (cn : ℚ) ^ 2 * (A₃ + A₄)) / ((wn : ℚ) ^ 2 * (Q * (pd : ℚ) ^ M))
      by field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [show (Dc : ℚ) ^ (2 * (K * n)) / Q * ((wn : ℚ) ^ 2 * (Q * (pd : ℚ) ^ M))
      = (Dc : ℚ) ^ (2 * (K * n)) * (pd : ℚ) ^ M * (wn : ℚ) ^ 2 by field_simp]
  linarith [hnumQ]

section MLDSAQ

set_option maxRecDepth 100000

/-- Kernel-checked inequality for the `1/q` slot bound. -/
theorem numQ_44_full : 2 ^ 382 * (((2 * 2 ^ 17) + 2 * (256 * 5)) ^ 256 * (2 * 2 ^ 17) ^ 256 *
      numM 330 8380417 256 4 (8380417 - 44 * (2 * (95232 - 78) - 1)) (44 * (2 * (95232 - 78) - 1))
        ((2 * 2 ^ 17) ^ (4 - 1) + 8380417) (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) 27 28
    + (((2 * 2 ^ 17) + 2 * (256 * 5)) ^ 256) ^ 2 *
      numE 330 8380417 256 4 (8380417 - 44 * (2 * (95232 - 78) - 1)) (44 * (2 * (95232 - 78) - 1))
        ((2 * 2 ^ 17) ^ (4 - 1) + 8380417) ((2 * 2 ^ 17) ^ (4 - 1) + 8380417 + 2) (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) 19 28)
  ≤ (44 * (2 * (95232 - 78) - 1)) ^ (2 * (4 * 256)) * (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) ^ 28 * ((2 * 2 ^ 17) ^ 256) ^ 2 := by
  decide +kernel

/-- Kernel-checked inequality for the `1/q` slot bound. -/
theorem numQ_44_z : 2 ^ 382 * (((2 * (2 ^ 17 - 78) - 1) + 2 * (256 * 5)) ^ 256 * (2 * (2 ^ 17 - 78) - 1) ^ 256 *
      numM 330 8380417 256 4 (8380417 - 44 * (2 * (95232 - 78) - 1)) (44 * (2 * (95232 - 78) - 1))
        ((2 * 2 ^ 17) ^ (4 - 1) + 8380417) (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) 27 28
    + (((2 * (2 ^ 17 - 78) - 1) + 2 * (256 * 5)) ^ 256) ^ 2 *
      numE 330 8380417 256 4 (8380417 - 44 * (2 * (95232 - 78) - 1)) (44 * (2 * (95232 - 78) - 1))
        ((2 * 2 ^ 17) ^ (4 - 1) + 8380417) ((2 * 2 ^ 17) ^ (4 - 1) + 8380417 + 2) (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) 19 28)
  ≤ (44 * (2 * (95232 - 78) - 1)) ^ (2 * (4 * 256)) * (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) ^ 28 * ((2 * (2 ^ 17 - 78) - 1) ^ 256) ^ 2 := by
  decide +kernel

/-- Kernel-checked inequality for the `1/q` slot bound. -/
theorem numQ_65_full : 2 ^ 420 * (((2 * 2 ^ 19) + 2 * (256 * 5)) ^ 256 * (2 * 2 ^ 19) ^ 256 *
      numM 330 8380417 256 6 (8380417 - 16 * (2 * (261888 - 196) - 1)) (16 * (2 * (261888 - 196) - 1))
        ((2 * 2 ^ 19) ^ (5 - 1) + 8380417) (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) 27 28
    + (((2 * 2 ^ 19) + 2 * (256 * 5)) ^ 256) ^ 2 *
      numE 330 8380417 256 6 (8380417 - 16 * (2 * (261888 - 196) - 1)) (16 * (2 * (261888 - 196) - 1))
        ((2 * 2 ^ 19) ^ (5 - 1) + 8380417) ((2 * 2 ^ 19) ^ (5 - 1) + 8380417 + 2) (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) 19 28)
  ≤ (16 * (2 * (261888 - 196) - 1)) ^ (2 * (6 * 256)) * (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) ^ 28 * ((2 * 2 ^ 19) ^ 256) ^ 2 := by
  decide +kernel

/-- Kernel-checked inequality for the `1/q` slot bound. -/
theorem numQ_65_z : 2 ^ 420 * (((2 * (2 ^ 19 - 196) - 1) + 2 * (256 * 5)) ^ 256 * (2 * (2 ^ 19 - 196) - 1) ^ 256 *
      numM 330 8380417 256 6 (8380417 - 16 * (2 * (261888 - 196) - 1)) (16 * (2 * (261888 - 196) - 1))
        ((2 * 2 ^ 19) ^ (5 - 1) + 8380417) (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) 27 28
    + (((2 * (2 ^ 19 - 196) - 1) + 2 * (256 * 5)) ^ 256) ^ 2 *
      numE 330 8380417 256 6 (8380417 - 16 * (2 * (261888 - 196) - 1)) (16 * (2 * (261888 - 196) - 1))
        ((2 * 2 ^ 19) ^ (5 - 1) + 8380417) ((2 * 2 ^ 19) ^ (5 - 1) + 8380417 + 2) (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) 19 28)
  ≤ (16 * (2 * (261888 - 196) - 1)) ^ (2 * (6 * 256)) * (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) ^ 28 * ((2 * (2 ^ 19 - 196) - 1) ^ 256) ^ 2 := by
  decide +kernel

/-- Kernel-checked inequality for the `1/q` slot bound. -/
theorem numQ_87_full : 2 ^ 472 * (((2 * 2 ^ 19) + 2 * (256 * 5)) ^ 256 * (2 * 2 ^ 19) ^ 256 *
      numM 330 8380417 256 8 (8380417 - 16 * (2 * (261888 - 120) - 1)) (16 * (2 * (261888 - 120) - 1))
        ((2 * 2 ^ 19) ^ (7 - 1) + 8380417) (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) 27 28
    + (((2 * 2 ^ 19) + 2 * (256 * 5)) ^ 256) ^ 2 *
      numE 330 8380417 256 8 (8380417 - 16 * (2 * (261888 - 120) - 1)) (16 * (2 * (261888 - 120) - 1))
        ((2 * 2 ^ 19) ^ (7 - 1) + 8380417) ((2 * 2 ^ 19) ^ (7 - 1) + 8380417 + 2) (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) 19 28)
  ≤ (16 * (2 * (261888 - 120) - 1)) ^ (2 * (8 * 256)) * (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) ^ 28 * ((2 * 2 ^ 19) ^ 256) ^ 2 := by
  decide +kernel

/-- Kernel-checked inequality for the `1/q` slot bound. -/
theorem numQ_87_z : 2 ^ 472 * (((2 * (2 ^ 19 - 120) - 1) + 2 * (256 * 5)) ^ 256 * (2 * (2 ^ 19 - 120) - 1) ^ 256 *
      numM 330 8380417 256 8 (8380417 - 16 * (2 * (261888 - 120) - 1)) (16 * (2 * (261888 - 120) - 1))
        ((2 * 2 ^ 19) ^ (7 - 1) + 8380417) (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) 27 28
    + (((2 * (2 ^ 19 - 120) - 1) + 2 * (256 * 5)) ^ 256) ^ 2 *
      numE 330 8380417 256 8 (8380417 - 16 * (2 * (261888 - 120) - 1)) (16 * (2 * (261888 - 120) - 1))
        ((2 * 2 ^ 19) ^ (7 - 1) + 8380417) ((2 * 2 ^ 19) ^ (7 - 1) + 8380417 + 2) (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) 19 28)
  ≤ (16 * (2 * (261888 - 120) - 1)) ^ (2 * (8 * 256)) * (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) ^ 28 * ((2 * (2 ^ 19 - 120) - 1) ^ 256) ^ 2 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
open Classical in
/-- **ML-DSA-44, second moment with the `1/q` slot bound.** -/
theorem var_mldsa44_q {v : Fin (4 * 256) → ℤ} (hv : Bounded 78 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 17 ∨ w = 2 * (2 ^ 17 - 78) - 1) (h₀ : Fin 4) :
    avg (fun a : Fin 4 → Fin 4 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 17) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 95232 78 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 17) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ 382 := by
  have hq : ∀ e' : ℕ, e' ≤ 28 → 8380417 ^ e' < (5 + 1) ^ 256 := fun e' he' =>
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) he') (by norm_num)
  have hp : ((((2 * 2 ^ 17) ^ (4 - 1) + 8380417 : ℕ)) : ℚ) / (((8380417 * (2 * 2 ^ 17) ^ (4 - 1) : ℕ)) : ℚ)
      = 1 / ((8380417 : ℕ) : ℚ) + 1 / ((2 * ((2 ^ 17 : ℕ) : ℚ))) ^ (4 - 1) := by
    push_cast; field_simp; norm_num
  have hpe : ((((2 * 2 ^ 17) ^ (4 - 1) + 8380417 + 2 : ℕ)) : ℚ) / (((8380417 * (2 * 2 ^ 17) ^ (4 - 1) : ℕ)) : ℚ)
      = 1 / ((8380417 : ℕ) : ℚ) + 1 / ((2 * ((2 ^ 17 : ℕ) : ℚ))) ^ (4 - 1)
        + 2 / (((8380417 : ℕ) : ℚ) * ((2 * ((2 ^ 17 : ℕ) : ℚ))) ^ (4 - 1)) := by
    push_cast; field_simp; norm_num
  rcases hw with rfl | rfl
  · refine var_rel_gen isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 19 28 382 (by norm_num) (by norm_num)
      ((2 * 2 ^ 17 + 2 * (256 * 5)) ^ 256) ((2 * 2 ^ 17) ^ 256) ((2 * 2 ^ 17) ^ (4 - 1) + 8380417) ((2 * 2 ^ 17) ^ (4 - 1) + 8380417 + 2)
      (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) (pow_pos (by norm_num) _) (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
      (Nat.le_add_right _ _) ?_ ?_ numQ_44_full
    · intro e' he'
      have := prob_deg_ge_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 17) (w := 2 * 2 ^ 17)
        (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' (hq e' (by omega))
      rw [hp]; convert this using 2; push_cast; norm_num
    · intro e' he1 he'
      have := prob_deg_exc_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 17) (w := 2 * 2 ^ 17)
        (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' he1 (hq e' (by omega))
      have h2 := (prob_mono (trip lo _ _ h₀)
        (P := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ ¬ NX zetaMLDSA h₀ x)
        (Q := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ (exc zetaMLDSA h₀ x.1.1 x.1.2 x.2).Nonempty)
        fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans this
      rw [hp, hpe]; convert h2 using 2; push_cast; norm_num
  · refine var_rel_gen isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 19 28 382 (by norm_num) (by norm_num)
      ((2 * (2 ^ 17 - 78) - 1 + 2 * (256 * 5)) ^ 256) ((2 * (2 ^ 17 - 78) - 1) ^ 256)
      ((2 * 2 ^ 17) ^ (4 - 1) + 8380417) ((2 * 2 ^ 17) ^ (4 - 1) + 8380417 + 2)
      (8380417 * (2 * 2 ^ 17) ^ (4 - 1)) (pow_pos (by norm_num) _) (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
      (Nat.le_add_right _ _) ?_ ?_ numQ_44_z
    · intro e' he'
      have := prob_deg_ge_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 17)
        (w := 2 * (2 ^ 17 - 78) - 1) (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' (hq e' (by omega))
      rw [hp]; convert this using 2; push_cast; norm_num
    · intro e' he1 he'
      have := prob_deg_exc_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 17)
        (w := 2 * (2 ^ 17 - 78) - 1) (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' he1
        (hq e' (by omega))
      have h2 := (prob_mono (trip lo _ _ h₀)
        (P := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ ¬ NX zetaMLDSA h₀ x)
        (Q := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ (exc zetaMLDSA h₀ x.1.1 x.1.2 x.2).Nonempty)
        fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans this
      rw [hp, hpe]; convert h2 using 2; push_cast; norm_num


set_option maxHeartbeats 2000000 in
open Classical in
/-- **ML-DSA-65, second moment with the `1/q` slot bound.** -/
theorem var_mldsa65_q {v : Fin (6 * 256) → ℤ} (hv : Bounded 196 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 196) - 1) (h₀ : Fin 5) :
    avg (fun a : Fin 6 → Fin 5 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 196 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ 420 := by
  have hq : ∀ e' : ℕ, e' ≤ 28 → 8380417 ^ e' < (5 + 1) ^ 256 := fun e' he' =>
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) he') (by norm_num)
  have hp : ((((2 * 2 ^ 19) ^ (5 - 1) + 8380417 : ℕ)) : ℚ) / (((8380417 * (2 * 2 ^ 19) ^ (5 - 1) : ℕ)) : ℚ)
      = 1 / ((8380417 : ℕ) : ℚ) + 1 / ((2 * ((2 ^ 19 : ℕ) : ℚ))) ^ (5 - 1) := by
    push_cast; field_simp; norm_num
  have hpe : ((((2 * 2 ^ 19) ^ (5 - 1) + 8380417 + 2 : ℕ)) : ℚ) / (((8380417 * (2 * 2 ^ 19) ^ (5 - 1) : ℕ)) : ℚ)
      = 1 / ((8380417 : ℕ) : ℚ) + 1 / ((2 * ((2 ^ 19 : ℕ) : ℚ))) ^ (5 - 1)
        + 2 / (((8380417 : ℕ) : ℚ) * ((2 * ((2 ^ 19 : ℕ) : ℚ))) ^ (5 - 1)) := by
    push_cast; field_simp; norm_num
  rcases hw with rfl | rfl
  · refine var_rel_gen isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 19 28 420 (by norm_num) (by norm_num)
      ((2 * 2 ^ 19 + 2 * (256 * 5)) ^ 256) ((2 * 2 ^ 19) ^ 256) ((2 * 2 ^ 19) ^ (5 - 1) + 8380417) ((2 * 2 ^ 19) ^ (5 - 1) + 8380417 + 2)
      (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) (pow_pos (by norm_num) _) (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
      (Nat.le_add_right _ _) ?_ ?_ numQ_65_full
    · intro e' he'
      have := prob_deg_ge_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19) (w := 2 * 2 ^ 19)
        (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' (hq e' (by omega))
      rw [hp]; convert this using 2; push_cast; norm_num
    · intro e' he1 he'
      have := prob_deg_exc_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19) (w := 2 * 2 ^ 19)
        (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' he1 (hq e' (by omega))
      have h2 := (prob_mono (trip lo _ _ h₀)
        (P := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ ¬ NX zetaMLDSA h₀ x)
        (Q := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ (exc zetaMLDSA h₀ x.1.1 x.1.2 x.2).Nonempty)
        fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans this
      rw [hp, hpe]; convert h2 using 2; push_cast; norm_num
  · refine var_rel_gen isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 19 28 420 (by norm_num) (by norm_num)
      ((2 * (2 ^ 19 - 196) - 1 + 2 * (256 * 5)) ^ 256) ((2 * (2 ^ 19 - 196) - 1) ^ 256)
      ((2 * 2 ^ 19) ^ (5 - 1) + 8380417) ((2 * 2 ^ 19) ^ (5 - 1) + 8380417 + 2)
      (8380417 * (2 * 2 ^ 19) ^ (5 - 1)) (pow_pos (by norm_num) _) (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
      (Nat.le_add_right _ _) ?_ ?_ numQ_65_z
    · intro e' he'
      have := prob_deg_ge_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19)
        (w := 2 * (2 ^ 19 - 196) - 1) (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' (hq e' (by omega))
      rw [hp]; convert this using 2; push_cast; norm_num
    · intro e' he1 he'
      have := prob_deg_exc_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19)
        (w := 2 * (2 ^ 19 - 196) - 1) (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' he1
        (hq e' (by omega))
      have h2 := (prob_mono (trip lo _ _ h₀)
        (P := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ ¬ NX zetaMLDSA h₀ x)
        (Q := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ (exc zetaMLDSA h₀ x.1.1 x.1.2 x.2).Nonempty)
        fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans this
      rw [hp, hpe]; convert h2 using 2; push_cast; norm_num


set_option maxHeartbeats 2000000 in
open Classical in
/-- **ML-DSA-87, second moment with the `1/q` slot bound.** -/
theorem var_mldsa87_q {v : Fin (8 * 256) → ℤ} (hv : Bounded 120 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 120) - 1) (h₀ : Fin 7) :
    avg (fun a : Fin 8 → Fin 7 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 120 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ 472 := by
  have hq : ∀ e' : ℕ, e' ≤ 28 → 8380417 ^ e' < (5 + 1) ^ 256 := fun e' he' =>
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) he') (by norm_num)
  have hp : ((((2 * 2 ^ 19) ^ (7 - 1) + 8380417 : ℕ)) : ℚ) / (((8380417 * (2 * 2 ^ 19) ^ (7 - 1) : ℕ)) : ℚ)
      = 1 / ((8380417 : ℕ) : ℚ) + 1 / ((2 * ((2 ^ 19 : ℕ) : ℚ))) ^ (7 - 1) := by
    push_cast; field_simp; norm_num
  have hpe : ((((2 * 2 ^ 19) ^ (7 - 1) + 8380417 + 2 : ℕ)) : ℚ) / (((8380417 * (2 * 2 ^ 19) ^ (7 - 1) : ℕ)) : ℚ)
      = 1 / ((8380417 : ℕ) : ℚ) + 1 / ((2 * ((2 ^ 19 : ℕ) : ℚ))) ^ (7 - 1)
        + 2 / (((8380417 : ℕ) : ℚ) * ((2 * ((2 ^ 19 : ℕ) : ℚ))) ^ (7 - 1)) := by
    push_cast; field_simp; norm_num
  rcases hw with rfl | rfl
  · refine var_rel_gen isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 19 28 472 (by norm_num) (by norm_num)
      ((2 * 2 ^ 19 + 2 * (256 * 5)) ^ 256) ((2 * 2 ^ 19) ^ 256) ((2 * 2 ^ 19) ^ (7 - 1) + 8380417) ((2 * 2 ^ 19) ^ (7 - 1) + 8380417 + 2)
      (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) (pow_pos (by norm_num) _) (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
      (Nat.le_add_right _ _) ?_ ?_ numQ_87_full
    · intro e' he'
      have := prob_deg_ge_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19) (w := 2 * 2 ^ 19)
        (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' (hq e' (by omega))
      rw [hp]; convert this using 2; push_cast; norm_num
    · intro e' he1 he'
      have := prob_deg_exc_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19) (w := 2 * 2 ^ 19)
        (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' he1 (hq e' (by omega))
      have h2 := (prob_mono (trip lo _ _ h₀)
        (P := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ ¬ NX zetaMLDSA h₀ x)
        (Q := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ (exc zetaMLDSA h₀ x.1.1 x.1.2 x.2).Nonempty)
        fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans this
      rw [hp, hpe]; convert h2 using 2; push_cast; norm_num
  · refine var_rel_gen isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 27 19 28 472 (by norm_num) (by norm_num)
      ((2 * (2 ^ 19 - 120) - 1 + 2 * (256 * 5)) ^ 256) ((2 * (2 ^ 19 - 120) - 1) ^ 256)
      ((2 * 2 ^ 19) ^ (7 - 1) + 8380417) ((2 * 2 ^ 19) ^ (7 - 1) + 8380417 + 2)
      (8380417 * (2 * 2 ^ 19) ^ (7 - 1)) (pow_pos (by norm_num) _) (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
      (Nat.le_add_right _ _) ?_ ?_ numQ_87_z
    · intro e' he'
      have := prob_deg_ge_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19)
        (w := 2 * (2 ^ 19 - 120) - 1) (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' (hq e' (by omega))
      rw [hp]; convert this using 2; push_cast; norm_num
    · intro e' he1 he'
      have := prob_deg_exc_q (lo := lo) isNTTMul_mldsa Packing.negacyclic_det_ne_zero (γ₁ := 2 ^ 19)
        (w := 2 * (2 ^ 19 - 120) - 1) (by norm_num) (by norm_num) (by norm_num) h₀ 5 e' he1
        (hq e' (by omega))
      have h2 := (prob_mono (trip lo _ _ h₀)
        (P := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ ¬ NX zetaMLDSA h₀ x)
        (Q := fun x => e' ≤ (degS zetaMLDSA (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card
          ∧ (exc zetaMLDSA h₀ x.1.1 x.1.2 x.2).Nonempty)
        fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans this
      rw [hp, hpe]; convert h2 using 2; push_cast; norm_num


end MLDSAQ

end AltR0

end

end AltR0GenPart

section RingFormPart

/-!
# The second moment as a statement about `R_q = ℤ_q[X]/(X^256 + 1)`

`var_mldsa44_q` etc. are stated with flattened coefficient vectors and negacyclic matrices. Here
they are restated over `RejOrder.Rq`, Mathlib's `AdjoinRoot (X^256 + 1)`: `A` is uniform in
`R_q^{k×ℓ}`, the products `A · y` are ring products, and the r₀ check reads the coefficients of the
reduced representative. The bridge (section `RingForm` of `RejOrder.lean`) is `coeffs_mul`
(multiplication in `R_q` is the negacyclic matrix, checked by evaluating at the 256 roots of
`X^256 + 1`) and `avg_matrix` (a uniform `A` has uniform coefficients); both are equalities,
so nothing is lost in the restatement. The headlines go through `moment_mldsa44` etc. (via
`var_mldsa44_ring`), so these ring statements are their only ML-DSA-specific computational
input.
-/

open Finset Polynomial Matrix

noncomputable section

set_option maxRecDepth 10000

namespace Bathwater.RingForm
open RejOrder AltR0

/-! ## The quantity bounded -/

/-- The r₀ check on `w ∈ R_q^K` with shift `v`: every coefficient has
`|LowBits − v| < γ₂ − β`. -/
def Pass {K : ℕ} (γ₂ β : ℕ) (v : Fin K → Fin 256 → ℤ) (w : Fin K → Rq) : Prop :=
  ∀ i s, |lowBits 8380417 γ₂ (coeffs (w i) s) - v i s| < (γ₂ : ℤ) - β

noncomputable instance {K : ℕ} (γ₂ β : ℕ) (v : Fin K → Fin 256 → ℤ) :
    DecidablePred (Pass γ₂ β v) := fun _ => Classical.dec _

/-- `ρ(A, t)`: probability over the head `y₀` (uniform on `hbox lo w`) that
`A · y` passes the r₀ check, where `y` is `y₀` at position `h₀` and `t` elsewhere. -/
noncomputable def rho {K L : ℕ} (γ₂ β : ℕ) (v : Fin K → Fin 256 → ℤ) (lo : Fin 256 → ℤ) (w : ℕ)
    (h₀ : Fin L) (A : Matrix (Fin K) (Fin L) Rq) (t : Fin L → Fin 256 → ℤ) : ℚ :=
  prob (hbox lo w) fun y₀ => Pass γ₂ β v (A *ᵥ fun j => ofInt (if j = h₀ then y₀ else t j))

/-- Flattening of `v`. -/
def flatV {K : ℕ} (v : Fin K → Fin 256 → ℤ) : Fin (K * 256) → ℤ :=
  fun r => v (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2

lemma rhoC_eq {K L : ℕ} (γ₂ β : ℕ) (v : Fin K → Fin 256 → ℤ) (lo : Fin 256 → ℤ) (w : ℕ)
    (h₀ : Fin L) (a : Fin K → Fin L → Fin 256 → ZMod 8380417) (t : Fin L → Fin 256 → ℤ) :
    rhoC negacyclic γ₂ β (flatV v) lo w h₀ a t
      = rho γ₂ β v lo w h₀ (Matrix.of fun i j => ofCoeffs (a i j)) t := by
  unfold rhoC rho
  refine prob_congr _ fun y₀ _ => ?_
  have hblk : (fun j => ofCoeffs (blk (zc (q := 8380417) (join h₀ y₀ t)) j))
      = fun j => ofInt (if j = h₀ then y₀ else t j) := by
    funext j; rw [blk_join]; unfold ofInt; split_ifs <;> rfl
  simp only [Fintype.mem_piFinset, good, Finset.mem_filter, Finset.mem_univ, true_and, not_le,
    Pass]
  rw [← hblk, ← finProdFinEquiv.forall_congr_right]
  simp only [Prod.forall, modMat_mulVec_eq, flatV, Equiv.symm_apply_apply]

/-! ## ML-DSA -/

/-- **ML-DSA-44: the second moment, a statement about `R_q` alone.** Let `A` be uniform in
`R_q^{4×4}`, `t` uniform on the tail box (polynomial `h₀` zero, the others with coefficients in
`(-2^17, 2^17]`), and `y₀` uniform on a head box of width `w` (the full box or the z-passing box).
For every shift `v` with `‖v‖∞ ≤ 78`, the probability `ρ(A, t)` over `y₀` that `A · y` passes the
r₀ check satisfies `E_A E_t (ρ − μ)² ≤ μ² / 2^382`, with `μ` the pass probability of a uniform
`w ∈ R_q^4`. -/
theorem moment_mldsa44 (v : Fin 4 → Fin 256 → ℤ) (hv : ∀ i s, |v i s| ≤ 78)
    {lo : Fin 256 → ℤ} {w : ℕ} (hw : w = 2 * 2 ^ 17 ∨ w = 2 * (2 ^ 17 - 78) - 1) (h₀ : Fin 4) :
    avg (fun A : Matrix (Fin 4) (Fin 4) Rq =>
        (∑ t ∈ tbox (2 ^ 17) h₀, (rho 95232 78 v lo w h₀ A t
          - (44 * (2 * (95232 - 78) - 1) / 8380417 : ℚ) ^ (4 * 256)) ^ 2)
          / (tbox (n := 256) (2 ^ 17) h₀).card)
      ≤ ((44 * (2 * (95232 - 78) - 1) / 8380417 : ℚ) ^ (4 * 256)) ^ 2 / 2 ^ 382 := by
  have hvf : Bounded 78 (flatV v) := fun r => hv _ _
  have hμ : ∏ r, ((good (q := 8380417) 95232 78 (flatV v) r).card : ℚ) / 8380417
      = (44 * (2 * (95232 - 78) - 1) / 8380417 : ℚ) ^ (4 * 256) := by
    simp only [card_good params_mldsa44 hvf, prod_const, card_univ, Fintype.card_fin]; norm_num
  rw [avg_matrix]
  simp only [← rhoC_eq, ← hμ]
  exact var_mldsa44_q hvf hw h₀

/-- **ML-DSA-65: the second moment, a statement about `R_q` alone.** Let `A` be uniform in
`R_q^{6×5}`, `t` uniform on the tail box (polynomial `h₀` zero, the others with coefficients in
`(-2^19, 2^19]`), and `y₀` uniform on a head box of width `w` (the full box or the z-passing box).
For every shift `v` with `‖v‖∞ ≤ 196`, the probability `ρ(A, t)` over `y₀` that `A · y` passes the
r₀ check satisfies `E_A E_t (ρ − μ)² ≤ μ² / 2^420`, with `μ` the pass probability of a uniform
`w ∈ R_q^6`. -/
theorem moment_mldsa65 (v : Fin 6 → Fin 256 → ℤ) (hv : ∀ i s, |v i s| ≤ 196)
    {lo : Fin 256 → ℤ} {w : ℕ} (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 196) - 1) (h₀ : Fin 5) :
    avg (fun A : Matrix (Fin 6) (Fin 5) Rq =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rho 261888 196 v lo w h₀ A t
          - (16 * (2 * (261888 - 196) - 1) / 8380417 : ℚ) ^ (6 * 256)) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ ((16 * (2 * (261888 - 196) - 1) / 8380417 : ℚ) ^ (6 * 256)) ^ 2 / 2 ^ 420 := by
  have hvf : Bounded 196 (flatV v) := fun r => hv _ _
  have hμ : ∏ r, ((good (q := 8380417) 261888 196 (flatV v) r).card : ℚ) / 8380417
      = (16 * (2 * (261888 - 196) - 1) / 8380417 : ℚ) ^ (6 * 256) := by
    simp only [card_good params_mldsa65 hvf, prod_const, card_univ, Fintype.card_fin]; norm_num
  rw [avg_matrix]
  simp only [← rhoC_eq, ← hμ]
  exact var_mldsa65_q hvf hw h₀

/-- **ML-DSA-87: the second moment, a statement about `R_q` alone.** Let `A` be uniform in
`R_q^{8×7}`, `t` uniform on the tail box (polynomial `h₀` zero, the others with coefficients in
`(-2^19, 2^19]`), and `y₀` uniform on a head box of width `w` (the full box or the z-passing box).
For every shift `v` with `‖v‖∞ ≤ 120`, the probability `ρ(A, t)` over `y₀` that `A · y` passes the
r₀ check satisfies `E_A E_t (ρ − μ)² ≤ μ² / 2^472`, with `μ` the pass probability of a uniform
`w ∈ R_q^8`. -/
theorem moment_mldsa87 (v : Fin 8 → Fin 256 → ℤ) (hv : ∀ i s, |v i s| ≤ 120)
    {lo : Fin 256 → ℤ} {w : ℕ} (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 120) - 1) (h₀ : Fin 7) :
    avg (fun A : Matrix (Fin 8) (Fin 7) Rq =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rho 261888 120 v lo w h₀ A t
          - (16 * (2 * (261888 - 120) - 1) / 8380417 : ℚ) ^ (8 * 256)) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ ((16 * (2 * (261888 - 120) - 1) / 8380417 : ℚ) ^ (8 * 256)) ^ 2 / 2 ^ 472 := by
  have hvf : Bounded 120 (flatV v) := fun r => hv _ _
  have hμ : ∏ r, ((good (q := 8380417) 261888 120 (flatV v) r).card : ℚ) / 8380417
      = (16 * (2 * (261888 - 120) - 1) / 8380417 : ℚ) ^ (8 * 256) := by
    simp only [card_good params_mldsa87 hvf, prod_const, card_univ, Fintype.card_fin]; norm_num
  rw [avg_matrix]
  simp only [← rhoC_eq, ← hμ]
  exact var_mldsa87_q hvf hw h₀

set_option maxHeartbeats 1000000 in
/-- `var_mldsa44_q` recovered from the ring statement `moment_mldsa44`; the headlines use this
one, so the ring statement is their only ML-DSA-specific input. -/
theorem var_mldsa44_ring {v : Fin (4 * 256) → ℤ} (hv : Bounded 78 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 17 ∨ w = 2 * (2 ^ 17 - 78) - 1) (h₀ : Fin 4) :
    avg (fun a : Fin 4 → Fin 4 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 17) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 95232 78 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 17) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ 382 := by
  set v' : Fin 4 → Fin 256 → ℤ := fun i s => v (finProdFinEquiv (i, s))
  have hflat : flatV v' = v := funext fun r => by simp [flatV, v']
  have h := moment_mldsa44 v' (fun i s => hv _) (lo := lo) hw h₀
  rw [avg_matrix] at h
  simp only [← rhoC_eq, hflat] at h
  have hμ : ∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417
      = (44 * (2 * (95232 - 78) - 1) / 8380417 : ℚ) ^ (4 * 256) := by
    simp only [card_good params_mldsa44 hv, prod_const, card_univ, Fintype.card_fin]; norm_num
  rw [hμ]; exact h

set_option maxHeartbeats 1000000 in
/-- `var_mldsa65_q` recovered from the ring statement `moment_mldsa65`; the headlines use this
one, so the ring statement is their only ML-DSA-specific input. -/
theorem var_mldsa65_ring {v : Fin (6 * 256) → ℤ} (hv : Bounded 196 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 196) - 1) (h₀ : Fin 5) :
    avg (fun a : Fin 6 → Fin 5 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 196 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ 420 := by
  set v' : Fin 6 → Fin 256 → ℤ := fun i s => v (finProdFinEquiv (i, s))
  have hflat : flatV v' = v := funext fun r => by simp [flatV, v']
  have h := moment_mldsa65 v' (fun i s => hv _) (lo := lo) hw h₀
  rw [avg_matrix] at h
  simp only [← rhoC_eq, hflat] at h
  have hμ : ∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417
      = (16 * (2 * (261888 - 196) - 1) / 8380417 : ℚ) ^ (6 * 256) := by
    simp only [card_good params_mldsa65 hv, prod_const, card_univ, Fintype.card_fin]; norm_num
  rw [hμ]; exact h

set_option maxHeartbeats 1000000 in
/-- `var_mldsa87_q` recovered from the ring statement `moment_mldsa87`; the headlines use this
one, so the ring statement is their only ML-DSA-specific input. -/
theorem var_mldsa87_ring {v : Fin (8 * 256) → ℤ} (hv : Bounded 120 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 120) - 1) (h₀ : Fin 7) :
    avg (fun a : Fin 8 → Fin 7 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, (rhoC (negacyclic (R := ZMod 8380417) (n := 256)) 261888 120 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) ^ 2)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) ^ 2 / 2 ^ 472 := by
  set v' : Fin 8 → Fin 256 → ℤ := fun i s => v (finProdFinEquiv (i, s))
  have hflat : flatV v' = v := funext fun r => by simp [flatV, v']
  have h := moment_mldsa87 v' (fun i s => hv _) (lo := lo) hw h₀
  rw [avg_matrix] at h
  simp only [← rhoC_eq, hflat] at h
  have hμ : ∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417
      = (16 * (2 * (261888 - 120) - 1) / 8380417 : ℚ) ^ (8 * 256) := by
    simp only [card_good params_mldsa87 hv, prod_const, card_univ, Fintype.card_fin]; norm_num
  rw [hμ]; exact h

end Bathwater.RingForm

end

end RingFormPart

section AltR0FinalPart

/-!
# alt-r0 for ML-DSA: end to end

Section `BathwaterCore` computes the output law of `alt-r0` with a set `H` of resampled coordinates
(`Bathwater.altR0Set_law`) and bounds its distance to vanilla signing in terms of the relative mean
deviation `dev` of `ρ` (the r₀ pass probability with the `H` part fresh) from a constant `μ₀`
(`Bathwater.altR0Set_close`). Section `AltR0SharpPart` bounds, for ML-DSA, every `c·s₂`, every head
box and every head index, the second moment `E_A E_t (ρ_c(t) − μ)² ≤ μ² / 2^{2j}`
(`AltR0.var_mldsa44_sharp` etc.) and the first moment `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^j`
(`AltR0.dev_mldsa44_sharp` etc.). This section joins the two.

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
5. `main`: by Markov on these first moments, at most a `2·2^{-j}/ε` fraction of matrices are `Bad`
   (`X ≥ με` or `Xz ≥ με`); for all others `D ≥ μ(p_z − 2ε)`, so the `ℓ¹` distance is at most
   `2ε/(p_z − 2ε)` and the non-termination probability at most `ε/(p_z − 2ε)`.
6. `main2`: better, apply Markov to the second moments `X2`, `Xz2` (`E_a X2 ≤ μ²/2^{2j}`, from
   `var_mldsa*_sharp`): at most a `2·2^{-2j}/ε²` fraction of matrices are `Bad2`
   (`X2 ≥ (με)²` or `Xz2 ≥ (με)²`), and for the others `X, Xz < με` by Cauchy–Schwarz over
   `(c, t)` (`X_lt_of_X2`), with the same conclusions as `main`.

## Results

`altR0_mldsa44_eps` (and 65, 87) state `main` for any `ε`. The headlines `altR0_mldsa44/65/87`
use `main2`:

* ML-DSA-44 (`ε = 2^-98`, `p_z ≥ 27/50`): bad fraction `≤ 2^-97`; for every other matrix
  `∑ |altLaw − vanLaw| ≤ 2^-96` and non-termination `≤ 2^-97`.
* ML-DSA-65 (`ε = 2^-121`, `p_z ≥ 3/5`): bad fraction `≤ 2^-121`, `ℓ¹ ≤ 2^-119`, non-termination
  `≤ 2^-120`.
* ML-DSA-87 (`ε = 2^-126`, `p_z ≥ 3/5`): bad fraction `≤ 2^-127`, `ℓ¹ ≤ 2^-124`, non-termination
  `≤ 2^-125`.

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
  decide (modMat mulmat a *ᵥ zc (flat γ₁ y) ∈ Fintype.piFinset (RejOrder.good γ₂ β (v c)))

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
        Fintype.piFinset (RejOrder.good γ₂ β v) then (1 : ℚ) else 0) / (AltR0.hbox lo w).card := by
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
        modMat mulmat a *ᵥ zc (AltR0.join h₀ x t) ∈ Fintype.piFinset (RejOrder.good γ₂ β (v c))
        then (1 : ℚ) else 0)]
  swap
  · intro y'
    refine sum_congr rfl fun c _ => ?_
    congr 1
    simp only [r0, decide_eq_true_eq, flat_eq h₀ y', T, tailOf_eq_iff]
  have e2 : ∀ x ∈ box γ₁ n, (∑ t ∈ AltR0.tbox γ₁ h₀, ∑ c, if t = T ∧
        modMat mulmat a *ᵥ zc (AltR0.join h₀ x t) ∈ Fintype.piFinset (RejOrder.good γ₂ β (v c))
        then (1 : ℚ) else 0) = ∑ c, if modMat mulmat a *ᵥ zc (AltR0.join h₀ x T) ∈
          Fintype.piFinset (RejOrder.good γ₂ β (v c)) then (1 : ℚ) else 0 := by
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
    ∏ r, ((RejOrder.good (q := q) γ₂ β v r).card : ℚ) / q = mu q γ₂ β mb K n := by
  simp only [RejOrder.card_good hp hv, prod_const, card_univ, Fintype.card_fin, mu]

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
    modMat mulmat a *ᵥ zc (AltR0.join h₀ x t) ∈ Fintype.piFinset (RejOrder.good γ₂ β (v c))
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


/-! ## Markov on the second moment -/

/-- Mean squared deviation of the r₀ pass probability over the tail, full head box, averaged over
`c`. -/
def X2 (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (a : Fin K → Fin L → Fin n → ZMod q) : ℚ :=
  avg fun c : C => (∑ t ∈ AltR0.tbox γ₁ h₀,
    (AltR0.rhoC mulmat γ₂ β (v c) (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁) h₀ a t - mu q γ₂ β mb K n) ^ 2) /
      (AltR0.tbox (n := n) γ₁ h₀).card

/-- The same with the z-passing head box. -/
def Xz2 (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L)
    (a : Fin K → Fin L → Fin n → ZMod q) : ℚ :=
  avg fun c : C => (∑ t ∈ AltR0.tbox γ₁ h₀,
    (AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β) h₀ a t - mu q γ₂ β mb K n) ^ 2) /
      (AltR0.tbox (n := n) γ₁ h₀).card

/-- `E|d| ≤ (E d² / η + η) / 2`, averaged over `c` and a finite set of `t`. -/
lemma avg_abs_le [Nonempty C] {ι : Type*} (s : Finset ι) (d : C → ι → ℚ) {η : ℚ} (hη : 0 < η) :
    avg (fun c => (∑ t ∈ s, |d c t|) / s.card)
      ≤ (avg (fun c => (∑ t ∈ s, d c t ^ 2) / s.card) / η + η) / 2 := by
  have hpt : ∀ x : ℚ, |x| ≤ (x ^ 2 / η + η) / 2 := by
    intro x
    have : 0 ≤ (|x| - η) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
    rw [sub_sq, sq_abs] at this
    have e1 : (x ^ 2 - 2 * |x| * η + η ^ 2) / η = x ^ 2 / η - 2 * |x| + η := by field_simp
    linarith
  have hc : ∀ c, (∑ t ∈ s, |d c t|) / s.card
      ≤ ((∑ t ∈ s, d c t ^ 2) / s.card / η + η) / 2 := by
    intro c
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0, Nat.cast_zero, div_zero, div_zero, zero_div, zero_add]; positivity
    · have hs : (0 : ℚ) < s.card := by exact_mod_cast hpos
      rw [div_le_iff₀ hs]
      refine (Finset.sum_le_sum fun t _ => hpt (d c t)).trans (le_of_eq ?_)
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
      field_simp
  refine (avg_mono hc).trans (le_of_eq ?_)
  unfold avg
  rw [Finset.sum_div, Finset.sum_div]
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, card_univ,
    nsmul_eq_mul]
  have : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  field_simp

lemma X_lt_of_X2 [Nonempty C] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    {γ₂ mb : ℕ} (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (a : Fin K → Fin L → Fin n → ZMod q)
    {η : ℚ} (hη : 0 < η) (h : X2 mulmat γ₁ γ₂ β mb v h₀ a < η ^ 2) :
    X mulmat γ₁ γ₂ β mb v h₀ a < η := by
  have := avg_abs_le (C := C) (AltR0.tbox (n := n) γ₁ h₀) (fun c t =>
    AltR0.rhoC mulmat γ₂ β (v c) (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁) h₀ a t - mu q γ₂ β mb K n) hη
  have h2 : X2 mulmat γ₁ γ₂ β mb v h₀ a / η < η := by rw [div_lt_iff₀ hη]; nlinarith
  unfold X; unfold X2 at h2
  linarith

lemma Xz_lt_of_Xz2 [Nonempty C] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    {γ₂ mb : ℕ} (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L)
    (a : Fin K → Fin L → Fin n → ZMod q)
    {η : ℚ} (hη : 0 < η) (h : Xz2 mulmat γ₁ γ₂ β mb u v h₀ a < η ^ 2) :
    Xz mulmat γ₁ γ₂ β mb u v h₀ a < η := by
  have := avg_abs_le (C := C) (AltR0.tbox (n := n) γ₁ h₀) (fun c t =>
    AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β) h₀ a t - mu q γ₂ β mb K n) hη
  have h2 : Xz2 mulmat γ₁ γ₂ β mb u v h₀ a / η < η := by rw [div_lt_iff₀ hη]; nlinarith
  unfold Xz; unfold Xz2 at h2
  linarith

lemma X2_nonneg (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ β mb : ℕ)
    (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (a : Fin K → Fin L → Fin n → ZMod q) :
    0 ≤ X2 mulmat γ₁ γ₂ β mb v h₀ a :=
  avg_nonneg fun c => div_nonneg (Finset.sum_nonneg fun t _ => sq_nonneg _) (Nat.cast_nonneg _)

lemma Xz2_nonneg (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L)
    (a : Fin K → Fin L → Fin n → ZMod q) : 0 ≤ Xz2 mulmat γ₁ γ₂ β mb u v h₀ a :=
  avg_nonneg fun c => div_nonneg (Finset.sum_nonneg fun t _ => sq_nonneg _) (Nat.cast_nonneg _)

lemma avg_X2_le [Nonempty C] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    {γ₂ mb : ℕ} (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) {δ : ℚ}
    (hvar : ∀ c, avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      (∑ t ∈ AltR0.tbox γ₁ h₀, (AltR0.rhoC mulmat γ₂ β (v c) (fun _ => -(γ₁ : ℤ) + 1) (2 * γ₁)
        h₀ a t - mu q γ₂ β mb K n) ^ 2) / (AltR0.tbox (n := n) γ₁ h₀).card)
        ≤ mu q γ₂ β mb K n ^ 2 * δ) :
    avg (fun a => X2 mulmat γ₁ γ₂ β mb v h₀ a) ≤ mu q γ₂ β mb K n ^ 2 * δ := by
  unfold X2
  rw [avg_comm]
  exact (avg_mono hvar).trans (avg_const _).le

lemma avg_Xz2_le [Nonempty C] (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    {γ₂ mb : ℕ} (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) {δ : ℚ}
    (hvar : ∀ c, avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      (∑ t ∈ AltR0.tbox γ₁ h₀, (AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β)
        h₀ a t - mu q γ₂ β mb K n) ^ 2) / (AltR0.tbox (n := n) γ₁ h₀).card)
        ≤ mu q γ₂ β mb K n ^ 2 * δ) :
    avg (fun a => Xz2 mulmat γ₁ γ₂ β mb u v h₀ a) ≤ mu q γ₂ β mb K n ^ 2 * δ := by
  unfold Xz2
  rw [avg_comm]
  exact (avg_mono hvar).trans (avg_const _).le

/-- A matrix is *bad in mean square* (at level `ε`) if one of the two mean squared deviations is
at least `(μ ε)²`. -/
def Bad2 (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (ε : ℚ)
    (a : Fin K → Fin L → Fin n → ZMod q) : Prop :=
  (mu q γ₂ β mb K n * ε) ^ 2 ≤ X2 mulmat γ₁ γ₂ β mb v h₀ a ∨
    (mu q γ₂ β mb K n * ε) ^ 2 ≤ Xz2 mulmat γ₁ γ₂ β mb u v h₀ a

instance (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β mb : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (h₀ : Fin L) (ε : ℚ) :
    DecidablePred (Bad2 mulmat γ₁ γ₂ β mb u v h₀ ε) :=
  fun _ => by unfold Bad2; infer_instance

/-- **Main theorem, second-moment form.** If the mean squared deviations are at most `μ² δ` on
average over the matrix, then at most a `2δ/ε²` fraction of matrices are bad in mean square, and
every other matrix has the conclusions of `main`. Markov is applied to the second moment, and
Cauchy–Schwarz only per matrix. -/
theorem main2 [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (hu : ∀ c, Bounded β (u c)) (h₀ : Fin L) {δ ε : ℚ} (hε : 0 < ε)
    (hX : avg (fun a => X2 mulmat γ₁ γ₂ β mb v h₀ a) ≤ mu q γ₂ β mb K n ^ 2 * δ)
    (hZ : avg (fun a => Xz2 mulmat γ₁ γ₂ β mb u v h₀ a) ≤ mu q γ₂ β mb K n ^ 2 * δ) :
    ((univ.filter (Bad2 mulmat γ₁ γ₂ β mb u v h₀ ε)).card : ℚ) /
        Fintype.card (Fin K → Fin L → Fin n → ZMod q) ≤ 2 * δ / ε ^ 2 ∧
      ∀ a, ¬ Bad2 mulmat γ₁ γ₂ β mb u v h₀ ε a → 2 * ε < pz γ₁ β L n →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u) x -
            Bathwater.AltR0Set.vanLaw
              (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) x| ≤
          2 * ε / (pz γ₁ β L n - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u) x ≤
          ε / (pz γ₁ β L n - 2 * ε) := by
  set μ := mu q γ₂ β mb K n
  have hμ : 0 < μ := mu_pos hp
  have hη : 0 < μ * ε := mul_pos hμ hε
  have hη2 : 0 < (μ * ε) ^ 2 := by positivity
  have hr : μ ^ 2 * δ / (μ * ε) ^ 2 = δ / ε ^ 2 := by
    rw [mul_pow]; exact mul_div_mul_left _ _ (pow_ne_zero 2 hμ.ne')
  refine ⟨?_, ?_⟩
  · have h1 := markov (fun a => X2_nonneg mulmat γ₂ β mb v h₀ a) hη2 hX
    have h2 := markov (fun a => Xz2_nonneg mulmat γ₂ β mb u v h₀ a) hη2 hZ
    rw [hr] at h1 h2
    have hc : ((univ.filter (Bad2 mulmat γ₁ γ₂ β mb u v h₀ ε)).card : ℚ) ≤
        ((univ.filter fun a => (μ * ε) ^ 2 ≤ X2 mulmat γ₁ γ₂ β mb v h₀ a).card : ℚ) +
          ((univ.filter fun a => (μ * ε) ^ 2 ≤ Xz2 mulmat γ₁ γ₂ β mb u v h₀ a).card : ℚ) := by
      rw [← Nat.cast_add]
      refine Nat.cast_le.mpr (le_trans (card_le_card ?_) (card_union_le _ _))
      intro a ha
      simp only [mem_filter, mem_univ, true_and, Bad2, mem_union] at ha ⊢
      exact ha
    have hA : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
      exact_mod_cast Fintype.card_pos
    calc ((univ.filter (Bad2 mulmat γ₁ γ₂ β mb u v h₀ ε)).card : ℚ) /
          Fintype.card (Fin K → Fin L → Fin n → ZMod q)
        ≤ (((univ.filter fun a => (μ * ε) ^ 2 ≤ X2 mulmat γ₁ γ₂ β mb v h₀ a).card : ℚ) +
            ((univ.filter fun a => (μ * ε) ^ 2 ≤ Xz2 mulmat γ₁ γ₂ β mb u v h₀ a).card : ℚ)) /
            Fintype.card (Fin K → Fin L → Fin n → ZMod q) :=
          div_le_div_of_nonneg_right hc hA.le
      _ ≤ δ / ε ^ 2 + δ / ε ^ 2 := by rw [add_div]; exact add_le_add h1 h2
      _ = 2 * δ / ε ^ 2 := by ring
  · intro a ha hpz
    simp only [Bad2, not_or, not_le] at ha
    obtain ⟨hXa2, hZa2⟩ := ha
    have hXa := X_lt_of_X2 mulmat v h₀ a hη hXa2
    have hZa := Xz_lt_of_Xz2 mulmat u v h₀ a hη hZa2
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

/-! ## The r₀ check over `R_q` -/

/-- The r₀ check for `A ∈ R_q^{K×L}`: `‖LowBits(A·y − c·s₂)‖∞ < γ₂ − β`, with `v c = c·s₂` and
`ringMat A` the matrix of `y ↦ A·y` on coefficient vectors. The headlines are stated with it. -/
def r0R {C : Type*} {K L : ℕ} (γ₁ γ₂ β : ℕ) (v : C → Fin (K * 256) → ℤ)
    (A : Matrix (Fin K) (Fin L) Rq) (y : Fin L → V γ₁ 256) (c : C) : Bool :=
  decide (ringMat A *ᵥ zc (flat γ₁ y) ∈ Fintype.piFinset (RejOrder.good γ₂ β (v c)))

lemma r0_coeffsOf {C : Type*} {K L : ℕ} (γ₁ γ₂ β : ℕ) (v : C → Fin (K * 256) → ℤ)
    (A : Matrix (Fin K) (Fin L) Rq) :
    r0 negacyclic γ₁ γ₂ β v (coeffsOf A) = r0R γ₁ γ₂ β v A := by
  funext y c
  simp only [r0, r0R, modMat_coeffsOf]

/-- The bad matrices over `R_q` (mean deviation form): `Bad` for the coefficients of `A`. -/
abbrev BadR {C : Type*} [Fintype C] {K L : ℕ} (γ₁ γ₂ β mb : ℕ) (u : C → Fin (L * 256) → ℤ)
    (v : C → Fin (K * 256) → ℤ) (h₀ : Fin L) (ε : ℚ) (A : Matrix (Fin K) (Fin L) Rq) : Prop :=
  Bad negacyclic γ₁ γ₂ β mb u v h₀ ε (coeffsOf A)

/-- The bad matrices over `R_q` (mean square form): those for which the mean squared deviation
of the r₀ pass probability from `μ`, over the tail and the challenge, is at least `(μ ε)²`, for
the full head box or the z-passing one. This is `Bad2` for the coefficients of `A`. -/
abbrev Bad2R {C : Type*} [Fintype C] {K L : ℕ} (γ₁ γ₂ β mb : ℕ) (u : C → Fin (L * 256) → ℤ)
    (v : C → Fin (K * 256) → ℤ) (h₀ : Fin L) (ε : ℚ) (A : Matrix (Fin K) (Fin L) Rq) : Prop :=
  Bad2 negacyclic γ₁ γ₂ β mb u v h₀ ε (coeffsOf A)

/-! ## ML-DSA-44 -/

section MLDSA44

lemma mu_eq_44 {v : Fin (4 * 256) → ℤ} (hv : Bounded 78 v) :
    ∏ r, ((RejOrder.good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417 =
      mu 8380417 95232 78 44 4 256 :=
  mu_eq params_mldsa44 hv

lemma avg_X_44 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (4 * 256) → ℤ)
    (hv : ∀ c, Bounded 78 (v c)) (h₀ : Fin 4) :
    avg (fun a => X (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 17) 95232 78 44 v h₀ a) ≤
      mu 8380417 95232 78 44 4 256 * (1 / 2 ^ 147) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa44_sharp (hv c) (lo := fun _ => -((2 ^ 17 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 17) (Or.inl rfl) h₀
  rw [mu_eq_44 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hv : ∀ c, Bounded 78 (v c)) (h₀ : Fin 4) :
    avg (fun a => Xz (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀ a) ≤
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
    ((univ.filter fun A : Matrix (Fin 4) (Fin 4) Rq =>
        BadR (2 ^ 17) 95232 78 44 u v h₀ ε A).card : ℚ) / Fintype.card (Matrix (Fin 4) (Fin 4) Rq) ≤ 2 * (1 / 2 ^ 147) / ε ∧
      ∀ A, ¬ BadR (2 ^ 17) 95232 78 44 u v h₀ ε A →
        2 * ε < pz (2 ^ 17) 78 4 256 →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 17) 95232 78 v A)
              (zok (2 ^ 17) 78 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0R (2 ^ 17) 95232 78 v A y c &&
              zok (2 ^ 17) 78 u y c) x| ≤
          2 * ε / (pz (2 ^ 17) 78 4 256 - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 17) 95232 78 v A)
              (zok (2 ^ 17) 78 u) x ≤
          ε / (pz (2 ^ 17) 78 4 256 - 2 * ε) := by
  obtain ⟨h1, h2⟩ := main negacyclic params_mldsa44 u v hu h₀ hε (avg_X_44 v hv h₀) (avg_Xz_44 u v hv h₀)
  refine ⟨(frac_ring _).trans_le h1, fun A => ?_⟩
  simp only [← r0_coeffsOf]
  exact h2 (coeffsOf A)

lemma avg_X2_44 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (4 * 256) → ℤ)
    (hv : ∀ c, Bounded 78 (v c)) (h₀ : Fin 4) :
    avg (fun a => X2 (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 17) 95232 78 44 v h₀ a) ≤
      mu 8380417 95232 78 44 4 256 ^ 2 * (1 / 2 ^ 382) := by
  apply avg_X2_le
  intro c
  have := Bathwater.RingForm.var_mldsa44_ring (hv c) (lo := fun _ => -(((2 ^ 17) : ℕ) : ℤ) + 1)
    (w := 2 * (2 ^ 17)) (Or.inl rfl) h₀
  rw [mu_eq_44 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz2_44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hv : ∀ c, Bounded 78 (v c)) (h₀ : Fin 4) :
    avg (fun a => Xz2 (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀ a) ≤
      mu 8380417 95232 78 44 4 256 ^ 2 * (1 / 2 ^ 382) := by
  apply avg_Xz2_le
  intro c
  have := Bathwater.RingForm.var_mldsa44_ring (hv c) (lo := zlo (2 ^ 17) 78 h₀ (u c)) (w := zw (2 ^ 17) 78)
    (Or.inr rfl) h₀
  rw [mu_eq_44 (hv c)] at this
  rw [mul_one_div]; exact this

/-- **ML-DSA-44, headline.** Take `ε = 2^-127`. For at least a `1 − 2^-127` fraction of
matrices `A` (Markov on the second moment over `A`, which is `≤ μ²·2^-382` with the `1/q`
slot bound), alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law
within `2^-125` of vanilla's in `ℓ¹`, and fails to terminate with probability at most `2^-126`. -/
theorem altR0_mldsa44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hu : ∀ c, Bounded 78 (u c)) (hv : ∀ c, Bounded 78 (v c))
    (h₀ : Fin 4) :
    ((univ.filter fun A : Matrix (Fin 4) (Fin 4) Rq =>
        Bad2R (2 ^ 17) 95232 78 44 u v h₀ (1 / 2 ^ 127) A).card : ℚ) / Fintype.card (Matrix (Fin 4) (Fin 4) Rq)
        ≤ 1 / 2 ^ 127 ∧
      ∀ A, ¬ Bad2R (2 ^ 17) 95232 78 44 u v h₀ (1 / 2 ^ 127) A →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 17) 95232 78 v A)
              (zok (2 ^ 17) 78 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0R (2 ^ 17) 95232 78 v A y c &&
              zok (2 ^ 17) 78 u y c) x| ≤ 1 / 2 ^ 125 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 17) 95232 78 v A)
              (zok (2 ^ 17) 78 u) x ≤ 1 / 2 ^ 126 := by
  obtain ⟨h1, h2⟩ := main2 negacyclic params_mldsa44 u v hu h₀ (ε := 1 / 2 ^ 127) (by norm_num)
    (avg_X2_44 v hv h₀) (avg_Xz2_44 u v hv h₀)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha
  have hpz := pz_ge_44
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 17) 78 4 256 - 2 * (1 / 2 ^ 127) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 127) ≤ 27 / 50 := by norm_num
    linarith
  obtain ⟨d1, d2⟩ := h2 a ha (by linarith)
  refine ⟨d1.trans ?_, d2.trans ?_⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))

end MLDSA44

/-! ## ML-DSA-65 -/

section MLDSA65

lemma mu_eq_65 {v : Fin (6 * 256) → ℤ} (hv : Bounded 196 v) :
    ∏ r, ((RejOrder.good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417 =
      mu 8380417 261888 196 16 6 256 :=
  mu_eq params_mldsa65 hv

lemma avg_X_65 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (6 * 256) → ℤ)
    (hv : ∀ c, Bounded 196 (v c)) (h₀ : Fin 5) :
    avg (fun a => X (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 196 16 v h₀ a) ≤
      mu 8380417 261888 196 16 6 256 * (1 / 2 ^ 182) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa65_sharp (hv c) (lo := fun _ => -((2 ^ 19 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 19) (Or.inl rfl) h₀
  rw [mu_eq_65 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hv : ∀ c, Bounded 196 (v c)) (h₀ : Fin 5) :
    avg (fun a => Xz (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀ a) ≤
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
    ((univ.filter fun A : Matrix (Fin 6) (Fin 5) Rq =>
        BadR (2 ^ 19) 261888 196 16 u v h₀ ε A).card : ℚ) / Fintype.card (Matrix (Fin 6) (Fin 5) Rq) ≤ 2 * (1 / 2 ^ 182) / ε ∧
      ∀ A, ¬ BadR (2 ^ 19) 261888 196 16 u v h₀ ε A →
        2 * ε < pz (2 ^ 19) 196 5 256 →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 196 v A)
              (zok (2 ^ 19) 196 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0R (2 ^ 19) 261888 196 v A y c &&
              zok (2 ^ 19) 196 u y c) x| ≤
          2 * ε / (pz (2 ^ 19) 196 5 256 - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 196 v A)
              (zok (2 ^ 19) 196 u) x ≤
          ε / (pz (2 ^ 19) 196 5 256 - 2 * ε) := by
  obtain ⟨h1, h2⟩ := main negacyclic params_mldsa65 u v hu h₀ hε (avg_X_65 v hv h₀) (avg_Xz_65 u v hv h₀)
  refine ⟨(frac_ring _).trans_le h1, fun A => ?_⟩
  simp only [← r0_coeffsOf]
  exact h2 (coeffsOf A)

lemma avg_X2_65 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (6 * 256) → ℤ)
    (hv : ∀ c, Bounded 196 (v c)) (h₀ : Fin 5) :
    avg (fun a => X2 (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 196 16 v h₀ a) ≤
      mu 8380417 261888 196 16 6 256 ^ 2 * (1 / 2 ^ 420) := by
  apply avg_X2_le
  intro c
  have := Bathwater.RingForm.var_mldsa65_ring (hv c) (lo := fun _ => -(((2 ^ 19) : ℕ) : ℤ) + 1)
    (w := 2 * (2 ^ 19)) (Or.inl rfl) h₀
  rw [mu_eq_65 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz2_65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hv : ∀ c, Bounded 196 (v c)) (h₀ : Fin 5) :
    avg (fun a => Xz2 (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀ a) ≤
      mu 8380417 261888 196 16 6 256 ^ 2 * (1 / 2 ^ 420) := by
  apply avg_Xz2_le
  intro c
  have := Bathwater.RingForm.var_mldsa65_ring (hv c) (lo := zlo (2 ^ 19) 196 h₀ (u c)) (w := zw (2 ^ 19) 196)
    (Or.inr rfl) h₀
  rw [mu_eq_65 (hv c)] at this
  rw [mul_one_div]; exact this

/-- **ML-DSA-65, headline.** Take `ε = 2^-140`. For at least a `1 − 2^-139` fraction of
matrices `A` (Markov on the second moment over `A`, which is `≤ μ²·2^-420` with the `1/q`
slot bound), alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law
within `2^-138` of vanilla's in `ℓ¹`, and fails to terminate with probability at most `2^-139`. -/
theorem altR0_mldsa65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hu : ∀ c, Bounded 196 (u c)) (hv : ∀ c, Bounded 196 (v c))
    (h₀ : Fin 5) :
    ((univ.filter fun A : Matrix (Fin 6) (Fin 5) Rq =>
        Bad2R (2 ^ 19) 261888 196 16 u v h₀ (1 / 2 ^ 140) A).card : ℚ) / Fintype.card (Matrix (Fin 6) (Fin 5) Rq)
        ≤ 1 / 2 ^ 139 ∧
      ∀ A, ¬ Bad2R (2 ^ 19) 261888 196 16 u v h₀ (1 / 2 ^ 140) A →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 196 v A)
              (zok (2 ^ 19) 196 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0R (2 ^ 19) 261888 196 v A y c &&
              zok (2 ^ 19) 196 u y c) x| ≤ 1 / 2 ^ 138 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 196 v A)
              (zok (2 ^ 19) 196 u) x ≤ 1 / 2 ^ 139 := by
  obtain ⟨h1, h2⟩ := main2 negacyclic params_mldsa65 u v hu h₀ (ε := 1 / 2 ^ 140) (by norm_num)
    (avg_X2_65 v hv h₀) (avg_Xz2_65 u v hv h₀)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha
  have hpz := pz_ge_65
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 196 5 256 - 2 * (1 / 2 ^ 140) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 140) ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2⟩ := h2 a ha (by linarith)
  refine ⟨d1.trans ?_, d2.trans ?_⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))

end MLDSA65

/-! ## ML-DSA-87 -/

section MLDSA87

lemma mu_eq_87 {v : Fin (8 * 256) → ℤ} (hv : Bounded 120 v) :
    ∏ r, ((RejOrder.good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417 =
      mu 8380417 261888 120 16 8 256 :=
  mu_eq params_mldsa87 hv

lemma avg_X_87 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (8 * 256) → ℤ)
    (hv : ∀ c, Bounded 120 (v c)) (h₀ : Fin 7) :
    avg (fun a => X (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 120 16 v h₀ a) ≤
      mu 8380417 261888 120 16 8 256 * (1 / 2 ^ 190) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa87_sharp (hv c) (lo := fun _ => -((2 ^ 19 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 19) (Or.inl rfl) h₀
  rw [mu_eq_87 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hv : ∀ c, Bounded 120 (v c)) (h₀ : Fin 7) :
    avg (fun a => Xz (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀ a) ≤
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
    ((univ.filter fun A : Matrix (Fin 8) (Fin 7) Rq =>
        BadR (2 ^ 19) 261888 120 16 u v h₀ ε A).card : ℚ) / Fintype.card (Matrix (Fin 8) (Fin 7) Rq) ≤ 2 * (1 / 2 ^ 190) / ε ∧
      ∀ A, ¬ BadR (2 ^ 19) 261888 120 16 u v h₀ ε A →
        2 * ε < pz (2 ^ 19) 120 7 256 →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 120 v A)
              (zok (2 ^ 19) 120 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0R (2 ^ 19) 261888 120 v A y c &&
              zok (2 ^ 19) 120 u y c) x| ≤
          2 * ε / (pz (2 ^ 19) 120 7 256 - 2 * ε) ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 120 v A)
              (zok (2 ^ 19) 120 u) x ≤
          ε / (pz (2 ^ 19) 120 7 256 - 2 * ε) := by
  obtain ⟨h1, h2⟩ := main negacyclic params_mldsa87 u v hu h₀ hε (avg_X_87 v hv h₀) (avg_Xz_87 u v hv h₀)
  refine ⟨(frac_ring _).trans_le h1, fun A => ?_⟩
  simp only [← r0_coeffsOf]
  exact h2 (coeffsOf A)

lemma avg_X2_87 {C : Type*} [Fintype C] [Nonempty C] (v : C → Fin (8 * 256) → ℤ)
    (hv : ∀ c, Bounded 120 (v c)) (h₀ : Fin 7) :
    avg (fun a => X2 (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 120 16 v h₀ a) ≤
      mu 8380417 261888 120 16 8 256 ^ 2 * (1 / 2 ^ 472) := by
  apply avg_X2_le
  intro c
  have := Bathwater.RingForm.var_mldsa87_ring (hv c) (lo := fun _ => -(((2 ^ 19) : ℕ) : ℤ) + 1)
    (w := 2 * (2 ^ 19)) (Or.inl rfl) h₀
  rw [mu_eq_87 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz2_87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hv : ∀ c, Bounded 120 (v c)) (h₀ : Fin 7) :
    avg (fun a => Xz2 (negacyclic (R := ZMod 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀ a) ≤
      mu 8380417 261888 120 16 8 256 ^ 2 * (1 / 2 ^ 472) := by
  apply avg_Xz2_le
  intro c
  have := Bathwater.RingForm.var_mldsa87_ring (hv c) (lo := zlo (2 ^ 19) 120 h₀ (u c)) (w := zw (2 ^ 19) 120)
    (Or.inr rfl) h₀
  rw [mu_eq_87 (hv c)] at this
  rw [mul_one_div]; exact this

/-- **ML-DSA-87, headline.** Take `ε = 2^-157`. For at least a `1 − 2^-157` fraction of
matrices `A` (Markov on the second moment over `A`, which is `≤ μ²·2^-472` with the `1/q`
slot bound), alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law
within `2^-155` of vanilla's in `ℓ¹`, and fails to terminate with probability at most `2^-156`. -/
theorem altR0_mldsa87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hu : ∀ c, Bounded 120 (u c)) (hv : ∀ c, Bounded 120 (v c))
    (h₀ : Fin 7) :
    ((univ.filter fun A : Matrix (Fin 8) (Fin 7) Rq =>
        Bad2R (2 ^ 19) 261888 120 16 u v h₀ (1 / 2 ^ 157) A).card : ℚ) / Fintype.card (Matrix (Fin 8) (Fin 7) Rq)
        ≤ 1 / 2 ^ 157 ∧
      ∀ A, ¬ Bad2R (2 ^ 19) 261888 120 16 u v h₀ (1 / 2 ^ 157) A →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 120 v A)
              (zok (2 ^ 19) 120 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0R (2 ^ 19) 261888 120 v A y c &&
              zok (2 ^ 19) 120 u y c) x| ≤ 1 / 2 ^ 155 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0R (2 ^ 19) 261888 120 v A)
              (zok (2 ^ 19) 120 u) x ≤ 1 / 2 ^ 156 := by
  obtain ⟨h1, h2⟩ := main2 negacyclic params_mldsa87 u v hu h₀ (ε := 1 / 2 ^ 157) (by norm_num)
    (avg_X2_87 v hv h₀) (avg_Xz2_87 u v hv h₀)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha
  have hpz := pz_ge_87
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 120 7 256 - 2 * (1 / 2 ^ 157) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 157) ≤ 3 / 5 := by norm_num
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

/-- The bad matrices over `R_q`: every entry of column `h₀` vanishes at `d` or more of the
`256` roots of `X^256 + 1`. -/
abbrev BadMR {K L : ℕ} (h₀ : Fin L) (d : ℕ) (A : Matrix (Fin K) (Fin L) Rq) : Prop :=
  BadM zetaMLDSA h₀ d (coeffsOf A)

/-- **ML-DSA-44.** Outside a `2^-124` fraction of matrices, every attempt's commitment has
guessing probability at most `2^-99` (with `d = 2`). With `d = 1` (some entry of column `h₀`
invertible, as in the thesis) it is `2^-117` outside a `2^-59` fraction. -/
theorem minEntropy_mldsa44 (h₀ : Fin 4) :
    ((univ.filter fun A : Matrix (Fin 4) (Fin 4) Rq =>
        BadMR h₀ 2 A).card : ℚ) / Fintype.card (Matrix (Fin 4) (Fin 4) Rq)
        ≤ 1 / 2 ^ 124 ∧
      ∀ A, ¬ BadMR h₀ 2 A → ∀ (t : Fin 4 → Fin 256 → ℤ) (W : Fin 4 → Fin 256 → ℕ),
        prob (RejOrder.box (2 ^ 17) 256) (fun y₁ => ∀ i s,
          highBits 8380417 95232 44 ((ringMat A *ᵥ
            zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))) = W i s) ≤ 1 / 2 ^ 99 := by
  refine ⟨(frac_ring _).trans_le ((card_bad_le zetaMLDSA_inj h₀ 2 (by norm_num)).trans (by rw [Nat.choose_two_right]; norm_num)), fun A hA t W => ?_⟩
  rw [← modMat_coeffsOf]
  refine (minEntropy params_mldsa44 isNTTMul_mldsa (by norm_num) h₀ 2 (coeffsOf A) hA t W).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

/-- **ML-DSA-65.** Outside a `2^-186` fraction of matrices, every attempt's commitment has
guessing probability at most `2^-236` (with `d = 2`). -/
theorem minEntropy_mldsa65 (h₀ : Fin 5) :
    ((univ.filter fun A : Matrix (Fin 6) (Fin 5) Rq =>
        BadMR h₀ 2 A).card : ℚ) / Fintype.card (Matrix (Fin 6) (Fin 5) Rq)
        ≤ 1 / 2 ^ 186 ∧
      ∀ A, ¬ BadMR h₀ 2 A → ∀ (t : Fin 5 → Fin 256 → ℤ) (W : Fin 6 → Fin 256 → ℕ),
        prob (RejOrder.box (2 ^ 19) 256) (fun y₁ => ∀ i s,
          highBits 8380417 261888 16 ((ringMat A *ᵥ
            zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))) = W i s) ≤ 1 / 2 ^ 236 := by
  refine ⟨(frac_ring _).trans_le ((card_bad_le zetaMLDSA_inj h₀ 2 (by norm_num)).trans (by rw [Nat.choose_two_right]; norm_num)),
    fun A hA t W => ?_⟩
  rw [← modMat_coeffsOf]
  refine (minEntropy params_mldsa65 isNTTMul_mldsa (by norm_num) h₀ 2 (coeffsOf A) hA t W).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

/-- **ML-DSA-87.** Outside a `2^-248` fraction of matrices, every attempt's commitment has
guessing probability at most `2^-236` (with `d = 2`). -/
theorem minEntropy_mldsa87 (h₀ : Fin 7) :
    ((univ.filter fun A : Matrix (Fin 8) (Fin 7) Rq =>
        BadMR h₀ 2 A).card : ℚ) / Fintype.card (Matrix (Fin 8) (Fin 7) Rq)
        ≤ 1 / 2 ^ 248 ∧
      ∀ A, ¬ BadMR h₀ 2 A → ∀ (t : Fin 7 → Fin 256 → ℤ) (W : Fin 8 → Fin 256 → ℕ),
        prob (RejOrder.box (2 ^ 19) 256) (fun y₁ => ∀ i s,
          highBits 8380417 261888 16 ((ringMat A *ᵥ
            zc (join h₀ y₁ t)) (finProdFinEquiv (i, s))) = W i s) ≤ 1 / 2 ^ 236 := by
  refine ⟨(frac_ring _).trans_le ((card_bad_le zetaMLDSA_inj h₀ 2 (by norm_num)).trans (by rw [Nat.choose_two_right]; norm_num)),
    fun A hA t W => ?_⟩
  rw [← modMat_coeffsOf]
  refine (minEntropy params_mldsa87 isNTTMul_mldsa (by norm_num) h₀ 2 (coeffsOf A) hA t W).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

end MLDSA

end MinEntropy

end

end MinEntropyPart


section Alg3Part

open Finset

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Bathwater

/-! ## Part B. ePrint Algorithm 3 -/

section Alg3Policy
variable {ι V C : Type*} [Fintype ι] [LinearOrder ι] [Fintype V] [DecidableEq V]

/-- ePrint Algorithm 3: r₀-check first; on an r₀ failure keep everything except the head `h₀`;
if r₀ passes and polynomial `i` is the first to fail its z-check, keep `y_j` for `j > i`. -/
def alg3 (h₀ : ι) (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) : ReusePolicy ι V C :=
  fun y c =>
  if r0 y c then
    match firstFail zc y c with
    | some i => some (univ.filter fun j => i < j)
    | none => none
  else some (univ.erase h₀)

theorem alg3_accept (h₀ : ι) (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) (y : ι → V)
    (c : C) : alg3 h₀ zc r0 y c = none ↔ pass zc r0 y c = true := by
  unfold alg3 pass
  rcases hf : firstFail zc y c with _ | i
  · have := (firstFail_eq_none zc y c).mp hf
    cases hr : r0 y c <;> simp [this]
  · have h1 := (firstFail_eq_some.mp hf).1
    have : ¬ ∀ i, zc i (y i) c = true := fun h => by simp [h i] at h1
    cases hr : r0 y c <;> simp [this]

end Alg3Policy

/-! ## Part C (generic). The defect of Algorithm 3 -/

section Alg3Defect
variable {ι V C : Type*} [Fintype ι] [LinearOrder ι] [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype C] [Nonempty C]

/-- Total mass of the column sums of `B`: `N (1 − p)`. -/
lemma ReusePolicy.col_total (P : ReusePolicy ι V C) :
    ∑ y', ∑ y, P.loop.B y y' = Fintype.card (ι → V) * (1 - P.pAcc) := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have hA : ∑ y, ∑ x, P.loop.A y x =
      (((univ : Finset ((ι → V) × C)).filter fun x => P x.1 x.2 = none).card : ℚ) /
        Fintype.card C := by
    rw [sum_comm, card_filter]; push_cast; rw [sum_div]
    refine sum_congr rfl fun x _ => ?_
    simp only [ReusePolicy.loop]
    rw [Finset.sum_eq_single x.1]
    · split_ifs <;> simp_all
    · intro y _ hy; rw [if_neg]; rintro ⟨h, _⟩; exact hy h.symm
    · simp
  rw [sum_comm]
  have hrow : ∀ y, ∑ y', P.loop.B y y' = 1 - ∑ x, P.loop.A y x := fun y => by
    have := P.row y; linarith
  rw [sum_congr rfl fun y _ => hrow y, sum_sub_distrib, hA]
  unfold ReusePolicy.pAcc
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  field_simp

/-- Centring: if `∑ f = N a`, then for any constant `m`,
`∑ |f/N − a/N| ≤ 2 ∑ |f/N − m/N|`. -/
lemma centre_le {Y : Type*} [Fintype Y] (f : Y → ℚ) (N a m : ℚ) (hN : 0 < N)
    (hcard : (Fintype.card Y : ℚ) = N) (hf : ∑ y, f y = N * a) :
    ∑ y, |f y / N - a / N| ≤ 2 * ∑ y, |f y / N - m / N| := by
  set g := fun y => f y / N - m / N with hg_def
  have hg : ∑ y, g y = a - m := by
    simp only [g, sum_sub_distrib, ← sum_div, hf, sum_const, card_univ, nsmul_eq_mul, hcard]
    field_simp
  have h1 : ∀ y, |f y / N - a / N| ≤ |g y| + |a - m| / N := fun y => by
    have : f y / N - a / N = g y + (m - a) / N := by simp only [g]; ring
    rw [this]; refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hN, abs_sub_comm m a]
  calc ∑ y, |f y / N - a / N| ≤ ∑ y, (|g y| + |a - m| / N) := sum_le_sum fun y _ => h1 y
    _ = ∑ y, |g y| + |a - m| := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hcard]; field_simp
    _ ≤ ∑ y, |g y| + ∑ y, |g y| := by
        rw [← hg]; linarith [abs_sum_le_sum_abs g (univ : Finset Y)]
    _ = 2 * ∑ y, |f y / N - m / N| := by ring

/-- Averaging a function of the resampled coordinates over a reject that keeps `K` gives its mean. -/
lemma keepProb_const (K : Finset ι) (g : (ι → V) → ℚ)
    (hg : ∀ y y', (∀ j, j ∉ K → y' j = y j) → g y' = g y) (y' : ι → V) :
    ∑ y, keepProb K y y' * g y = (∑ y, g y) / Fintype.card (ι → V) := by
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hY : (Fintype.card (ι → V) : ℚ) =
      (Fintype.card V : ℚ) ^ K.card * (Fintype.card V : ℚ) ^ (Kᶜ).card := by
    rw [← pow_add, card_add_card_compl]; simp [Fintype.card_fun]
  have := sum_agree K g hg y'
  rw [hY, ← div_div, ← this, sum_div]
  refine sum_congr rfl fun y _ => ?_
  unfold keepProb; split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- Tower property for the head: against a weight that ignores `h₀`, a function and its head
average give the same sum. -/
lemma head_tower (h₀ : ι) (φ h : (ι → V) → ℚ)
    (hφ : ∀ y y', (∀ j, j ≠ h₀ → y' j = y j) → φ y' = φ y) :
    ∑ y, φ y * h y = ∑ y, φ y * ∑ y'', keepProb (univ.erase h₀) y'' y * h y'' := by
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hc : (univ.erase h₀)ᶜ = {h₀} := by ext; simp
  have e : ∀ y, ∑ y'', keepProb (univ.erase h₀) y'' y * h y'' =
      (∑ y'', if ∀ j ∉ ({h₀} : Finset ι), y'' j = y j then h y'' else 0) /
        (Fintype.card V : ℚ) ^ ({h₀} : Finset ι).card := by
    intro y; rw [sum_div]; refine sum_congr rfl fun y'' _ => ?_
    unfold keepProb; rw [hc]
    by_cases hh : ∀ j ∉ ({h₀} : Finset ι), y'' j = y j
    · rw [if_pos hh, if_pos (fun j hj => (hh j (by simpa using (mem_erase.mp hj).1)).symm)]; ring
    · rw [if_neg hh, if_neg]
      · simp
      intro h'; apply hh; intro j hj
      exact (h' j (mem_erase.mpr ⟨by simpa using hj, mem_univ _⟩)).symm
  simp only [e, mul_div_assoc']
  rw [← sum_div, AltR0Set.sum_class (H := {h₀}) h φ
    (fun y y' hyy' => hφ y y' (fun j hj => hyy' j (by simpa using hj)))]
  field_simp


/-- `0/1` value of a Boolean. -/
def bq (b : Bool) : ℚ := if b then 1 else 0

lemma bq_nonneg (b : Bool) : 0 ≤ bq b := by unfold bq; split_ifs <;> norm_num
lemma bq_le_one (b : Bool) : bq b ≤ 1 := by unfold bq; split_ifs <;> norm_num

variable (h₀ : ι) (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) (μ : ℚ)

/-- One step of the Markov kernel of `alg3` for challenge `c`, from `y` to `y'`. -/
def Mfun (c : C) (y y' : ι → V) : ℚ :=
  match alg3 h₀ zc r0 y c with
  | none => 0
  | some K => keepProb K y y'

/-- Indicator that `i` is the first z failure. -/
def Ff (c : C) (i : ι) (y : ι → V) : ℚ := if firstFail zc y c = some i then 1 else 0

/-- Indicator that `i` is the first z failure among the non-head polynomials. -/
def Gf (c : C) (i : ι) (y : ι → V) : ℚ :=
  if zc i (y i) c = false ∧ ∀ j, j < i → j ≠ h₀ → zc j (y j) c = true then 1 else 0

/-- The head average of `1[head passes z] · (1[r₀] − μ)`, as a function of the kept part. -/
def headDev (c : C) (y' : ι → V) : ℚ :=
  ∑ y, keepProb (univ.erase h₀) y y' * (bq (zc h₀ (y h₀) c) * (bq (r0 y c) - μ))

/-- `W = E_c E_y |headDev|`. -/
def alg3W : ℚ :=
  (∑ c, ∑ y, |headDev h₀ zc r0 μ c y|) / (Fintype.card C * Fintype.card (ι → V))

/-- The constant part of the column sum for challenge `c`. -/
def mC (c : C) : ℚ :=
  (∑ y : ι → V, (1 - μ * bq (zc h₀ (y h₀) c))) / Fintype.card (ι → V) +
    ∑ i ∈ univ.erase h₀, μ * (∑ y, Ff zc c i y) / Fintype.card (ι → V)

variable {h₀}

lemma M_eq (hmin : ∀ j, h₀ ≤ j) (c : C) (y y' : ι → V) :
    Mfun h₀ zc r0 c y y' =
      keepProb (univ.erase h₀) y y' * (1 - bq (zc h₀ (y h₀) c) * bq (r0 y c)) +
      ∑ i ∈ univ.erase h₀, keepProb (univ.filter fun j => i < j) y y' *
        (bq (r0 y c) * Ff zc c i y) := by
  unfold Mfun alg3
  cases hr : r0 y c
  · simp [bq]
  · rcases hf : firstFail zc y c with _ | i
    · have := (firstFail_eq_none zc y c).mp hf
      simp [bq, Ff, hf, this]
    · obtain ⟨hi, hlt⟩ := firstFail_eq_some.mp hf
      by_cases hih : i = h₀
      · subst hih
        have hK : (univ.filter fun j => i < j) = univ.erase i := by
          ext j; simp [lt_iff_le_and_ne, hmin j, eq_comm]
        have h0 : ∀ j ∈ univ.erase i, Ff zc c j y = 0 := by
          intro j hj; simp only [Ff, hf, Option.some.injEq]
          rw [if_neg (fun h => (mem_erase.mp hj).1 h.symm)]
        rw [sum_eq_zero (fun j hj => by rw [h0 j hj, mul_zero, mul_zero])]
        simp only [if_true]
        rw [hK]
        simp [bq, hi]
      · have hz : zc h₀ (y h₀) c = true := hlt h₀ (lt_of_le_of_ne (hmin i) (Ne.symm hih))
        rw [sum_eq_single i]
        · simp [bq, Ff, hf, hz]
        · intro j _ hj; simp [Ff, hf, Ne.symm hj]
        · intro h; exact absurd (mem_erase.mpr ⟨hih, mem_univ _⟩) h

lemma kp_nonneg (K : Finset ι) (y y' : ι → V) : 0 ≤ keepProb K y y' := by
  unfold keepProb; split_ifs <;> positivity

lemma Gf_nonneg (c : C) (i : ι) (y : ι → V) : 0 ≤ Gf h₀ zc c i y := by
  unfold Gf; split_ifs <;> norm_num

lemma Gf_le_one (c : C) (i : ι) (y : ι → V) : Gf h₀ zc c i y ≤ 1 := by
  unfold Gf; split_ifs <;> norm_num

lemma Ff_eq (hmin : ∀ j, h₀ ≤ j) (c : C) {i : ι} (hi : i ≠ h₀) (y : ι → V) :
    Ff zc c i y = bq (zc h₀ (y h₀) c) * Gf h₀ zc c i y := by
  have hlt : h₀ < i := lt_of_le_of_ne (hmin i) (Ne.symm hi)
  have key : firstFail zc y c = some i ↔ zc h₀ (y h₀) c = true ∧
      (zc i (y i) c = false ∧ ∀ j, j < i → j ≠ h₀ → zc j (y j) c = true) := by
    rw [firstFail_eq_some]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2 h₀ hlt, h1, fun j hj _ => h2 j hj⟩
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      by_cases hjh : j = h₀
      · subst hjh; exact h0
      · exact h2 j hj hjh
  unfold Ff Gf bq
  by_cases hz : zc h₀ (y h₀) c = true
  · simp only [key, hz, true_and, if_true, one_mul]
  · simp [key, hz]

/-- **Column sums of Algorithm 3**, for a fixed challenge: a constant, minus the head deviation at
`y'`, plus for each non-head `i` an average of the head deviation over a reject at `i`. -/
lemma col_eq (hmin : ∀ j, h₀ ≤ j) (c : C) (y' : ι → V) :
    ∑ y, Mfun h₀ zc r0 c y y' = mC h₀ zc μ c - headDev h₀ zc r0 μ c y' +
      ∑ i ∈ univ.erase h₀, ∑ y, keepProb (univ.filter fun j => i < j) y y' * Gf h₀ zc c i y *
        headDev h₀ zc r0 μ c y := by
  simp only [M_eq zc r0 hmin c, sum_add_distrib]
  rw [sum_comm (s := (univ : Finset (ι → V))) (t := univ.erase h₀)]
  have hA : ∑ y, keepProb (univ.erase h₀) y y' * (1 - bq (zc h₀ (y h₀) c) * bq (r0 y c)) =
      (∑ y : ι → V, (1 - μ * bq (zc h₀ (y h₀) c))) / Fintype.card (ι → V) - headDev h₀ zc r0 μ c y' := by
    have e : ∀ y, keepProb (univ.erase h₀) y y' * (1 - bq (zc h₀ (y h₀) c) * bq (r0 y c)) =
        keepProb (univ.erase h₀) y y' * (1 - μ * bq (zc h₀ (y h₀) c)) -
          keepProb (univ.erase h₀) y y' * (bq (zc h₀ (y h₀) c) * (bq (r0 y c) - μ)) :=
      fun y => by ring
    rw [sum_congr rfl fun y _ => e y, sum_sub_distrib, keepProb_const]
    · rfl
    · intro y y'' h
      rw [h h₀ (by simp)]
  have hB : ∀ i ∈ univ.erase h₀, ∑ y, keepProb (univ.filter fun j => i < j) y y' *
      (bq (r0 y c) * Ff zc c i y) = μ * (∑ y, Ff zc c i y) / Fintype.card (ι → V) +
      ∑ y, keepProb (univ.filter fun j => i < j) y y' * Gf h₀ zc c i y *
        headDev h₀ zc r0 μ c y := by
    intro i hi
    have hih : i ≠ h₀ := (mem_erase.mp hi).1
    have e : ∀ y, keepProb (univ.filter fun j => i < j) y y' * (bq (r0 y c) * Ff zc c i y) =
        keepProb (univ.filter fun j => i < j) y y' * (μ * Ff zc c i y) +
          (keepProb (univ.filter fun j => i < j) y y' * Gf h₀ zc c i y) *
            (bq (zc h₀ (y h₀) c) * (bq (r0 y c) - μ)) := by
      intro y; rw [Ff_eq zc hmin c hih]; ring
    rw [sum_congr rfl fun y _ => e y, sum_add_distrib, keepProb_const, ← mul_sum, mul_div_assoc,
      head_tower h₀]
    · rfl
    · intro y y'' h
      have hK : ∀ j ∈ (univ.filter fun j => i < j), j ≠ h₀ := by
        intro j hj; rw [mem_filter] at hj
        exact ne_of_gt (lt_of_le_of_lt (hmin i) hj.2)
      have h1 : keepProb (univ.filter fun j => i < j) y'' y' =
          keepProb (univ.filter fun j => i < j) y y' := by
        unfold keepProb
        exact if_congr ⟨fun H j hj => (H j hj).trans (h j (hK j hj)),
          fun H j hj => (H j hj).trans (h j (hK j hj)).symm⟩ rfl rfl
      have h2 : Gf h₀ zc c i y'' = Gf h₀ zc c i y := by
        unfold Gf
        refine if_congr ?_ rfl rfl
        rw [h i hih]
        exact and_congr Iff.rfl ⟨fun H j hj hjh => (h j hjh) ▸ H j hj hjh,
          fun H j hj hjh => (h j hjh).symm ▸ H j hj hjh⟩
      rw [h1, h2]
    · intro y y'' h
      have h' : ∀ j, j ≤ i → y'' j = y j := fun j hj => h j (by simpa using hj)
      unfold Ff
      by_cases hf : firstFail zc y c = some i
      · rw [if_pos hf, if_pos (firstFail_congr hf h')]
      · rw [if_neg hf, if_neg (fun hf' => hf (firstFail_congr hf' fun j hj => (h' j hj).symm))]
  rw [hA, sum_congr rfl hB, sum_add_distrib]
  unfold mC
  ring

/-- For a fixed challenge, the column sums are within `|ι| · ∑ |headDev|` of a constant in `ℓ¹`. -/
lemma col_bound (hmin : ∀ j, h₀ ≤ j) (c : C) :
    ∑ y', |∑ y, Mfun h₀ zc r0 c y y' - mC h₀ zc μ c| ≤
      Fintype.card ι * ∑ y, |headDev h₀ zc r0 μ c y| := by
  set hd := headDev h₀ zc r0 μ c
  have hpt : ∀ y', |∑ y, Mfun h₀ zc r0 c y y' - mC h₀ zc μ c| ≤
      |hd y'| + ∑ i ∈ univ.erase h₀, ∑ y, keepProb (univ.filter fun j => i < j) y y' * |hd y| := by
    intro y'
    rw [col_eq zc r0 μ hmin c y']
    have : mC h₀ zc μ c - hd y' + ∑ i ∈ univ.erase h₀, ∑ y,
        keepProb (univ.filter fun j => i < j) y y' * Gf h₀ zc c i y * hd y - mC h₀ zc μ c =
        -hd y' + ∑ i ∈ univ.erase h₀, ∑ y,
          keepProb (univ.filter fun j => i < j) y y' * Gf h₀ zc c i y * hd y := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    refine add_le_add le_rfl ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_))
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (kp_nonneg _ _ _), abs_of_nonneg (Gf_nonneg zc c i y)]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (kp_nonneg _ _ _)
    have := Gf_le_one (h₀ := h₀) zc c i y
    have := abs_nonneg (hd y)
    nlinarith
  calc ∑ y', |∑ y, Mfun h₀ zc r0 c y y' - mC h₀ zc μ c|
      ≤ ∑ y', (|hd y'| + ∑ i ∈ univ.erase h₀, ∑ y,
          keepProb (univ.filter fun j => i < j) y y' * |hd y|) := sum_le_sum fun y' _ => hpt y'
    _ = ∑ y, |hd y| + ∑ _i ∈ univ.erase h₀, ∑ y, |hd y| := by
        rw [sum_add_distrib]; congr 1
        rw [sum_comm]; refine sum_congr rfl fun i _ => ?_
        rw [sum_comm]; refine sum_congr rfl fun y _ => ?_
        rw [← sum_mul, keepProb_sum, one_mul]
    _ = Fintype.card ι * ∑ y, |hd y| := by
        rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul]
        have : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨h₀⟩
        rw [Nat.cast_sub this]; push_cast; ring

lemma col_sum (y' : ι → V) : ∑ y, (alg3 h₀ zc r0).loop.B y y' =
    (∑ c, ∑ y, Mfun h₀ zc r0 c y y') / Fintype.card C := by
  simp only [ReusePolicy.loop, Mfun]
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [← mul_sum, one_div, inv_mul_eq_div]; try rfl

/-- **Part C, generic.** If the head `h₀` is the least index, the defect of Algorithm 3 is at most
`2 |ι| W`, where `W = E_c E_y |headDev|` measures how far the head-averaged r₀ pass indicator,
restricted to heads that pass their z-check, is from `μ`. (Any constant `μ`.) -/
theorem alg3_defect (hmin : ∀ j, h₀ ≤ j) :
    (alg3 h₀ zc r0).defect ≤ 2 * Fintype.card ι * alg3W h₀ zc r0 μ := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  set N : ℚ := (Fintype.card (ι → V) : ℚ) with hN_def
  set mbar : ℚ := (∑ c, mC h₀ zc μ c) / Fintype.card C
  have hcent := centre_le (fun y' => ∑ y, (alg3 h₀ zc r0).loop.B y y') N
    (1 - (alg3 h₀ zc r0).pAcc) mbar hN rfl ((alg3 h₀ zc r0).col_total)
  unfold ReusePolicy.defect
  refine hcent.trans ?_
  have hpt : ∀ y', |(∑ y, (alg3 h₀ zc r0).loop.B y y') / N - mbar / N| ≤
      (∑ c, |∑ y, Mfun h₀ zc r0 c y y' - mC h₀ zc μ c|) / (Fintype.card C * N) := by
    intro y'
    have e : (∑ y, (alg3 h₀ zc r0).loop.B y y') / N - mbar / N =
        (∑ c, (∑ y, Mfun h₀ zc r0 c y y' - mC h₀ zc μ c)) / (Fintype.card C * N) := by
      rw [col_sum, sum_sub_distrib]; field_simp; simp only [mbar]; field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hC hN)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (mul_pos hC hN).le
  calc 2 * ∑ y', |(∑ y, (alg3 h₀ zc r0).loop.B y y') / N - mbar / N|
      ≤ 2 * ∑ y', (∑ c, |∑ y, Mfun h₀ zc r0 c y y' - mC h₀ zc μ c|) / (Fintype.card C * N) := by
        gcongr with y' _; exact hpt y'
    _ = 2 * (∑ c, ∑ y', |∑ y, Mfun h₀ zc r0 c y y' - mC h₀ zc μ c|) / (Fintype.card C * N) := by
        rw [← sum_div, sum_comm]; ring
    _ ≤ 2 * (∑ c, Fintype.card ι * ∑ y, |headDev h₀ zc r0 μ c y|) / (Fintype.card C * N) := by
        gcongr with c _; exact col_bound zc r0 μ hmin c
    _ = 2 * Fintype.card ι * alg3W h₀ zc r0 μ := by
        unfold alg3W; rw [← mul_sum]; ring

/-- The acceptance probability of Algorithm 3 is vanilla's. -/
lemma alg3_pAcc : (alg3 h₀ zc r0).pAcc = AltR0Set.pacc (pass zc r0) := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  unfold ReusePolicy.pAcc AltR0Set.pacc AltR0Set.sacc
  rw [← sum_div, div_div, mul_comm (Fintype.card C : ℚ)]
  congr 1
  rw [card_filter, Fintype.sum_prod_type]; push_cast
  refine sum_congr rfl fun y _ => sum_congr rfl fun c _ => ?_
  simp only [alg3_accept]

end Alg3Defect

end Bathwater

/-! ## The ML-DSA instance -/

namespace AltR0Final
open RejOrder Matrix

section Alg3Inst

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ} {C : Type*} [Fintype C] {γ₁ β : ℕ}

/-- The per-block z-check `‖y_j + (c·s₁)_j‖∞ < γ₁ − β`, with `u c = c·s₁`. -/
def zcB (γ₁ β : ℕ) (u : C → Fin (L * n) → ℤ) (j : Fin L) (x : V γ₁ n) (c : C) : Bool :=
  decide (∀ s, |x.1 s + u c (finProdFinEquiv (j, s))| < (γ₁ : ℤ) - β)

lemma zok_eq (u : C → Fin (L * n) → ℤ) (y : Fin L → V γ₁ n) (c : C) :
    zok γ₁ β u y c = decide (∀ j, zcB γ₁ β u j (y j) c = true) := by
  unfold zok zcB
  simp only [decide_eq_true_eq]
  congr 1
  apply propext
  constructor
  · intro h j s
    have := h (finProdFinEquiv (j, s))
    simpa [flat] using this
  · intro h c'
    have := h (finProdFinEquiv.symm c').1 (finProdFinEquiv.symm c').2
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at this
    simpa [flat] using this

lemma pass_eq (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q) :
    Bathwater.pass (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a) =
      fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c := by
  funext y c; unfold Bathwater.pass; rw [zok_eq]; congr 1; exact decide_eq_decide.mpr Iff.rfl

lemma zcB_iff (hβ : β < γ₁) (u : C → Fin (L * n) → ℤ) (j : Fin L) (x : V γ₁ n) (c : C) :
    zcB γ₁ β u j x c = true ↔ x.1 ∈ AltR0.hbox (zlo γ₁ β j (u c)) (zw γ₁ β) := by
  unfold zcB AltR0.hbox
  simp only [decide_eq_true_eq, Fintype.mem_piFinset, z_coord hβ, zlo]

/-- The head deviation of Algorithm 3 for ML-DSA: `|Z|/|box| · (ρ_z(tail) − μ)`. -/
lemma headDev_eq [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ : ℕ) (hβ : β < γ₁)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q)
    (h₀ : Fin L) (μ : ℚ) (c : C) (hu : Bounded β (u c)) (y' : Fin L → V γ₁ n) :
    Bathwater.headDev h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a) μ c y' =
      ((AltR0.hbox (zlo γ₁ β h₀ (u c)) (zw γ₁ β)).card / (box γ₁ n).card : ℚ) *
        (AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β) h₀ a (tailOf γ₁ h₀ y') - μ) := by
  set T := tailOf γ₁ h₀ y'
  set Z := AltR0.hbox (zlo γ₁ β h₀ (u c)) (zw γ₁ β)
  set P : (Fin n → ℤ) → (Fin L → Fin n → ℤ) → Prop := fun x t =>
    modMat mulmat a *ᵥ RejOrder.zc (AltR0.join h₀ x t) ∈ Fintype.piFinset (RejOrder.good γ₂ β (v c))
  have hZpos : (0 : ℚ) < Z.card := by
    rw [AltR0.card_hbox]; unfold zw
    have : 0 < 2 * (γ₁ - β) - 1 := by omega
    positivity
  have hZB : Z ⊆ box γ₁ n := zbox_sub hβ h₀ hu
  have hB : (0 : ℚ) < (box γ₁ n).card :=
    lt_of_lt_of_le hZpos (by exact_mod_cast card_le_card hZB)
  unfold Bathwater.headDev
  rw [sum_split' h₀ (fun x t => if t = T then
    (if x ∈ Z then ((if P x t then (1 : ℚ) else 0) - μ) else 0) / (box γ₁ n).card else 0)]
  swap
  · intro y
    have hc : (univ.erase h₀)ᶜ = {h₀} := by ext; simp
    have e1 : (∀ j ∈ univ.erase h₀, y' j = y j) ↔ tailOf γ₁ h₀ y = T := by
      rw [tailOf_eq_iff]
      constructor
      · intro h j hj; exact (h j (by simpa using hj)).symm
      · intro h j hj; exact (h j (by simpa using hj)).symm
    have e2 := zcB_iff hβ u h₀ (y h₀) c
    have e3 : r0 mulmat γ₁ γ₂ β v a y c = true ↔ P (y h₀).1 (tailOf γ₁ h₀ y) := by
      simp only [r0, decide_eq_true_eq, flat_eq h₀ y, P]
    unfold Bathwater.keepProb Bathwater.bq
    rw [hc, card_singleton, pow_one, Fintype.card_coe]
    by_cases h1 : tailOf γ₁ h₀ y = T
    · rw [if_pos (e1.mpr h1), if_pos h1]
      by_cases h2 : (y h₀).1 ∈ Z
      · rw [if_pos (e2.mpr h2), if_pos h2]
        by_cases h3 : P (y h₀).1 (tailOf γ₁ h₀ y)
        · rw [if_pos (e3.mpr h3), if_pos h3]; ring
        · rw [if_neg (fun h => h3 (e3.mp h)), if_neg h3]; ring
      · rw [if_neg (fun h => h2 (e2.mp h)), if_neg h2]; ring
    · rw [if_neg (fun h => h1 (e1.mp h)), if_neg h1, zero_mul]
  have hT : T ∈ AltR0.tbox γ₁ h₀ := tailOf_mem h₀ y'
  have e4 : ∀ x ∈ box γ₁ n, (∑ t ∈ AltR0.tbox γ₁ h₀, if t = T then
      (if x ∈ Z then ((if P x t then (1 : ℚ) else 0) - μ) else 0) / (box γ₁ n).card else 0) =
      (if x ∈ Z then ((if P x T then (1 : ℚ) else 0) - μ) else 0) / (box γ₁ n).card := by
    intro x _
    rw [sum_ite_eq' _ T, if_pos hT]
  rw [sum_congr rfl e4, ← sum_div, sum_ite_mem, inter_eq_right.mpr hZB, sum_sub_distrib,
    sum_const, nsmul_eq_mul, rhoC_eq]
  show _ = (Z.card : ℚ) / _ * ((∑ x ∈ Z, if P x T then (1 : ℚ) else 0) / Z.card - μ)
  field_simp

/-- `W ≤ X_z`: the head deviation of Algorithm 3 is controlled by the z-box deviation of `alt-r0`. -/
lemma alg3W_le [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ} (hβ : β < γ₁)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (hu : ∀ c, Bounded β (u c))
    (a : Fin K → Fin L → Fin n → ZMod q) (h₀ : Fin L) :
    Bathwater.alg3W h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a) (mu q γ₂ β mb K n) ≤
      Xz mulmat γ₁ γ₂ β mb u v h₀ a := by
  set μ := mu q γ₂ β mb K n
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
  set ρ : C → (Fin L → Fin n → ℤ) → ℚ := fun c t =>
    AltR0.rhoC mulmat γ₂ β (v c) (zlo γ₁ β h₀ (u c)) (zw γ₁ β) h₀ a t
  have hc : ∀ c, ∑ y, |Bathwater.headDev h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a) μ c y| ≤
      (box γ₁ n).card * ∑ t ∈ AltR0.tbox γ₁ h₀, |ρ c t - μ| := by
    intro c
    have hZB := zbox_sub hβ h₀ (hu c)
    have hq0 : (0 : ℚ) ≤ ((AltR0.hbox (zlo γ₁ β h₀ (u c)) (zw γ₁ β)).card / (box γ₁ n).card : ℚ) :=
      by positivity
    have hq1 : ((AltR0.hbox (zlo γ₁ β h₀ (u c)) (zw γ₁ β)).card / (box γ₁ n).card : ℚ) ≤ 1 :=
      (div_le_one hB).mpr (by exact_mod_cast card_le_card hZB)
    calc ∑ y, |Bathwater.headDev h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a) μ c y|
        ≤ ∑ y : Fin L → V γ₁ n, |ρ c (tailOf γ₁ h₀ y) - μ| := by
          refine sum_le_sum fun y _ => ?_
          rw [headDev_eq mulmat γ₂ hβ u v a h₀ μ c (hu c), abs_mul, abs_of_nonneg hq0]
          exact mul_le_of_le_one_left (abs_nonneg _) hq1
      _ = (box γ₁ n).card * ∑ t ∈ AltR0.tbox γ₁ h₀, |ρ c t - μ| := by
          rw [sum_split h₀ (fun _ t => |ρ c t - μ|), sum_const, nsmul_eq_mul]
  unfold Bathwater.alg3W Xz avg
  rw [card_Y h₀, div_le_div_iff₀ (by positivity) hC]
  calc (∑ c, ∑ y, |Bathwater.headDev h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a) μ c y|) *
        Fintype.card C
      ≤ (∑ c, (box γ₁ n).card * ∑ t ∈ AltR0.tbox γ₁ h₀, |ρ c t - μ|) * Fintype.card C := by
        gcongr with c _; exact hc c
    _ = _ := by
        rw [← mul_sum, ← sum_div]
        field_simp
        rfl

/-- **Part C, ML-DSA instance.** With the head `h₀` least in the order of `Fin L`, the defect of
Algorithm 3 is at most `2 L X_z`. -/
theorem alg3_defect_le [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ} (hβ : β < γ₁)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (hu : ∀ c, Bounded β (u c))
    (a : Fin K → Fin L → Fin n → ZMod q) (h₀ : Fin L) (hmin : ∀ j, h₀ ≤ j) :
    (Bathwater.alg3 h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a)).defect ≤
      2 * L * Xz mulmat γ₁ γ₂ β mb u v h₀ a := by
  have h := Bathwater.alg3_defect (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a) (mu q γ₂ β mb K n) hmin
  rw [Fintype.card_fin] at h
  refine h.trans ?_
  have := alg3W_le (γ₂ := γ₂) (mb := mb) mulmat hβ u v hu a h₀
  have hL : (0 : ℚ) ≤ 2 * L := by positivity
  exact mul_le_mul_of_nonneg_left this hL

/-- **Part D, step 1.** Algorithm 3 accepts with vanilla's probability. -/
lemma alg3_pAcc_eq [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q)
    (h₀ : Fin L) :
    (Bathwater.alg3 h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a)).pAcc =
      Bathwater.AltR0Set.pacc (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) := by
  rw [Bathwater.alg3_pAcc, pass_eq]

/-- **Part D, general form.** For a matrix that is not `Bad2` at level `ε < p_z`, in every
attempt window `k`, Algorithm 3's joint law of (attempt number, output) over the first `k`
attempts is within `k · 2Lε/(p_z − ε)` of vanilla's in `ℓ¹`, and it is still running after `k`
attempts with probability at most `(1 − μ(p_z − ε))^k + 2Lε/(p_z − ε)`. -/
theorem alg3_main [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (hu : ∀ c, Bounded β (u c)) (h₀ : Fin L) (hmin : ∀ j, h₀ ≤ j) {ε : ℚ} (hε : 0 < ε)
    (a : Fin K → Fin L → Fin n → ZMod q) (ha : ¬ Bad2 mulmat γ₁ γ₂ β mb u v h₀ ε a)
    (hpz : ε < pz γ₁ β L n) (k : ℕ) :
    ∑ x, |(Bathwater.alg3 h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a)).loop.outUpTo k x -
        (Bathwater.vanilla (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c)).loop.outUpTo
          k x| ≤ k * (2 * L * ε / (pz γ₁ β L n - ε)) ∧
      ∑ y, (Bathwater.alg3 h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a)).loop.state k y ≤
        (1 - mu q γ₂ β mb K n * (pz γ₁ β L n - ε)) ^ k + 2 * L * ε / (pz γ₁ β L n - ε) ∧
      mu q γ₂ β mb K n * (pz γ₁ β L n - ε) ≤
        (Bathwater.alg3 h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a)).pAcc := by
  set μ := mu q γ₂ β mb K n
  set P := Bathwater.alg3 h₀ (zcB γ₁ β u) (r0 mulmat γ₁ γ₂ β v a)
  have hμ : 0 < μ := mu_pos hp
  have hη : 0 < μ * ε := mul_pos hμ hε
  simp only [Bad2, not_or, not_le] at ha
  have hZa := Xz_lt_of_Xz2 mulmat u v h₀ a hη ha.2
  have hdef : P.defect ≤ 2 * L * (μ * ε) :=
    (alg3_defect_le mulmat hp.β_lt_γ₁ u v hu a h₀ hmin).trans
      (mul_le_mul_of_nonneg_left hZa.le (by positivity))
  have hpacc : μ * (pz γ₁ β L n - ε) ≤ P.pAcc := by
    rw [alg3_pAcc_eq]
    have := pacc_ge mulmat hp u v hu a h₀
    linarith
  have hgap : 0 < μ * (pz γ₁ β L n - ε) := mul_pos hμ (by linarith)
  have hp0 : 0 < P.pAcc := lt_of_lt_of_le hgap hpacc
  have hratio : P.defect / P.pAcc ≤ 2 * L * ε / (pz γ₁ β L n - ε) := by
    calc P.defect / P.pAcc ≤ 2 * L * (μ * ε) / (μ * (pz γ₁ β L n - ε)) :=
          div_le_div₀ (by positivity) hdef hgap hpacc
      _ = 2 * L * ε / (pz γ₁ β L n - ε) := by
          rw [mul_left_comm, mul_div_mul_left _ _ hμ.ne']
  have hPQ : ∀ y c, P y c = none ↔
      Bathwater.vanilla (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) y c = none := by
    intro y c
    rw [Bathwater.alg3_accept, pass_eq]
    unfold Bathwater.vanilla
    split_ifs with h <;> simp [h]
  refine ⟨?_, ?_, hpacc⟩
  · refine (P.outUpTo_close _ (Bathwater.vanilla_invariant _) hPQ hp0 k).trans ?_
    exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
  · refine (P.survive_close hp0 k).trans (add_le_add ?_ hratio)
    exact pow_le_pow_left₀ (by linarith [P.pAcc_le_one]) (by linarith) k

end Alg3Inst

/-! ## Headlines -/

/-- Shared tail of the three headlines. -/
lemma headline_aux {L : ℕ} {μ pz pAcc ε B : ℚ} (k : ℕ) (hμ : 0 < μ) (hgap : 1 / 2 ≤ pz - ε)
    (hB : 2 * L * ε / (1 / 2) ≤ B) (hε : 0 ≤ ε) (hp1 : pAcc ≤ 1) (hpacc : μ * (pz - ε) ≤ pAcc)
    {d s : ℚ} (hd : d ≤ k * (2 * L * ε / (pz - ε)))
    (hs : s ≤ (1 - μ * (pz - ε)) ^ k + 2 * L * ε / (pz - ε)) :
    d ≤ k * B ∧ s ≤ (1 - μ / 2) ^ k + B := by
  have hb : 2 * L * ε / (pz - ε) ≤ B :=
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) hgap).trans hB
  refine ⟨hd.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)), hs.trans (add_le_add ?_ hb)⟩
  refine pow_le_pow_left₀ (by linarith) ?_ k
  nlinarith

/-- **ML-DSA-44, Algorithm 3.** Take `ε = 2^-127` and the head `y₀`. For at least a `1 − 2^-127`
fraction of matrices `A` (the same bad set as `altR0_mldsa44`), for every `k`: over the first `k`
attempts the joint law of (attempt number, output) of Algorithm 3 is within `k · 2^-123` of
vanilla's in `ℓ¹`, and Algorithm 3 is still running after `k` attempts with probability at most
`(1 − μ/2)^k + 2^-123`. -/
theorem alg3_mldsa44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hu : ∀ c, Bounded 78 (u c)) (hv : ∀ c, Bounded 78 (v c)) :
    ((univ.filter fun A : Matrix (Fin 4) (Fin 4) Rq =>
        Bad2R (2 ^ 17) 95232 78 44 u v 0 (1 / 2 ^ 127) A).card : ℚ) / Fintype.card (Matrix (Fin 4) (Fin 4) Rq)
        ≤ 1 / 2 ^ 127 ∧
      ∀ A, ¬ Bad2R (2 ^ 17) 95232 78 44 u v 0 (1 / 2 ^ 127) A → ∀ k : ℕ,
        ∑ x, |(Bathwater.alg3 0 (zcB (2 ^ 17) 78 u)
              (r0R (2 ^ 17) 95232 78 v A)).loop.outUpTo k x -
            (Bathwater.vanilla (fun y c => r0R (2 ^ 17) 95232 78 v A y c &&
              zok (2 ^ 17) 78 u y c)).loop.outUpTo k x| ≤ k * (1 / 2 ^ 123) ∧
        ∑ y, (Bathwater.alg3 0 (zcB (2 ^ 17) 78 u)
              (r0R (2 ^ 17) 95232 78 v A)).loop.state k y ≤
          (1 - mu 8380417 95232 78 44 4 256 / 2) ^ k + 1 / 2 ^ 123 := by
  obtain ⟨h1, -⟩ := main2 negacyclic params_mldsa44 u v hu 0 (ε := 1 / 2 ^ 127) (by norm_num)
    (avg_X2_44 v hv 0) (avg_Xz2_44 u v hv 0)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha k
  have hpz := pz_ge_44
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 17) 78 4 256 - 1 / 2 ^ 127 := by
    have : (1 / 2 : ℚ) + 1 / 2 ^ 127 ≤ 27 / 50 := by norm_num
    linarith
  obtain ⟨d1, d2, d3⟩ := alg3_main negacyclic params_mldsa44 u v hu 0 (fun j => Fin.zero_le j)
    (by norm_num) a ha (by linarith) k
  exact headline_aux k (mu_pos params_mldsa44) hgap (by norm_num) (by norm_num)
    (Bathwater.ReusePolicy.pAcc_le_one _) d3 d1 d2

/-- **ML-DSA-65, Algorithm 3.** `ε = 2^-140`: bad fraction `≤ 2^-139`; for every other `A` and
every `k`, `ℓ¹ ≤ k · 2^-135` and still running after `k` attempts `≤ (1 − μ/2)^k + 2^-135`. -/
theorem alg3_mldsa65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hu : ∀ c, Bounded 196 (u c)) (hv : ∀ c, Bounded 196 (v c)) :
    ((univ.filter fun A : Matrix (Fin 6) (Fin 5) Rq =>
        Bad2R (2 ^ 19) 261888 196 16 u v 0 (1 / 2 ^ 140) A).card : ℚ) / Fintype.card (Matrix (Fin 6) (Fin 5) Rq)
        ≤ 1 / 2 ^ 139 ∧
      ∀ A, ¬ Bad2R (2 ^ 19) 261888 196 16 u v 0 (1 / 2 ^ 140) A → ∀ k : ℕ,
        ∑ x, |(Bathwater.alg3 0 (zcB (2 ^ 19) 196 u)
              (r0R (2 ^ 19) 261888 196 v A)).loop.outUpTo k x -
            (Bathwater.vanilla (fun y c => r0R (2 ^ 19) 261888 196 v A y c &&
              zok (2 ^ 19) 196 u y c)).loop.outUpTo k x| ≤ k * (1 / 2 ^ 135) ∧
        ∑ y, (Bathwater.alg3 0 (zcB (2 ^ 19) 196 u)
              (r0R (2 ^ 19) 261888 196 v A)).loop.state k y ≤
          (1 - mu 8380417 261888 196 16 6 256 / 2) ^ k + 1 / 2 ^ 135 := by
  obtain ⟨h1, -⟩ := main2 negacyclic params_mldsa65 u v hu 0 (ε := 1 / 2 ^ 140) (by norm_num)
    (avg_X2_65 v hv 0) (avg_Xz2_65 u v hv 0)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha k
  have hpz := pz_ge_65
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 196 5 256 - 1 / 2 ^ 140 := by
    have : (1 / 2 : ℚ) + 1 / 2 ^ 140 ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2, d3⟩ := alg3_main negacyclic params_mldsa65 u v hu 0 (fun j => Fin.zero_le j)
    (by norm_num) a ha (by linarith) k
  exact headline_aux k (mu_pos params_mldsa65) hgap (by norm_num) (by norm_num)
    (Bathwater.ReusePolicy.pAcc_le_one _) d3 d1 d2

/-- **ML-DSA-87, Algorithm 3.** `ε = 2^-157`: bad fraction `≤ 2^-157`; for every other `A` and
every `k`, `ℓ¹ ≤ k · 2^-152` and still running after `k` attempts `≤ (1 − μ/2)^k + 2^-152`. -/
theorem alg3_mldsa87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hu : ∀ c, Bounded 120 (u c)) (hv : ∀ c, Bounded 120 (v c)) :
    ((univ.filter fun A : Matrix (Fin 8) (Fin 7) Rq =>
        Bad2R (2 ^ 19) 261888 120 16 u v 0 (1 / 2 ^ 157) A).card : ℚ) / Fintype.card (Matrix (Fin 8) (Fin 7) Rq)
        ≤ 1 / 2 ^ 157 ∧
      ∀ A, ¬ Bad2R (2 ^ 19) 261888 120 16 u v 0 (1 / 2 ^ 157) A → ∀ k : ℕ,
        ∑ x, |(Bathwater.alg3 0 (zcB (2 ^ 19) 120 u)
              (r0R (2 ^ 19) 261888 120 v A)).loop.outUpTo k x -
            (Bathwater.vanilla (fun y c => r0R (2 ^ 19) 261888 120 v A y c &&
              zok (2 ^ 19) 120 u y c)).loop.outUpTo k x| ≤ k * (1 / 2 ^ 152) ∧
        ∑ y, (Bathwater.alg3 0 (zcB (2 ^ 19) 120 u)
              (r0R (2 ^ 19) 261888 120 v A)).loop.state k y ≤
          (1 - mu 8380417 261888 120 16 8 256 / 2) ^ k + 1 / 2 ^ 152 := by
  obtain ⟨h1, -⟩ := main2 negacyclic params_mldsa87 u v hu 0 (ε := 1 / 2 ^ 157) (by norm_num)
    (avg_X2_87 v hv 0) (avg_Xz2_87 u v hv 0)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha k
  have hpz := pz_ge_87
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 120 7 256 - 1 / 2 ^ 157 := by
    have : (1 / 2 : ℚ) + 1 / 2 ^ 157 ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2, d3⟩ := alg3_main negacyclic params_mldsa87 u v hu 0 (fun j => Fin.zero_le j)
    (by norm_num) a ha (by linarith) k
  exact headline_aux k (mu_pos params_mldsa87) hgap (by norm_num) (by norm_num)
    (Bathwater.ReusePolicy.pAcc_le_one _) d3 d1 d2

end AltR0Final

end

end Alg3Part

section AltR0JointPart

/-!
# alt-r0 per attempt: joint law of (attempt number, output) close to vanilla's

`alt-r0` (`Bathwater.altR0Set {h₀} r0 zok`): on an r₀ failure resample only the head `h₀`; on a
z failure resample everything; accept if both pass. Its defect is at most `2 E_y|ρ(y) − μ|`
for any constant `μ` (`altR0Set_defect_le`), which for ML-DSA is `≤ 2 X` (`altR0Set_defect_le_X`).
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Bathwater.AltR0Joint

section Generic
variable {ι V C : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype C] [Nonempty C]

/-- Total mass of the column sums of `B`: `N (1 − p)`. (As `ReusePolicy.col_total`, without the order on `ι`.) -/
lemma col_total (P : ReusePolicy ι V C) :
    ∑ y', ∑ y, P.loop.B y y' = Fintype.card (ι → V) * (1 - P.pAcc) := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  have hA : ∑ y, ∑ x, P.loop.A y x =
      (((univ : Finset ((ι → V) × C)).filter fun x => P x.1 x.2 = none).card : ℚ) /
        Fintype.card C := by
    rw [sum_comm, card_filter]; push_cast; rw [sum_div]
    refine sum_congr rfl fun x _ => ?_
    simp only [ReusePolicy.loop]
    rw [Finset.sum_eq_single x.1]
    · split_ifs <;> simp_all
    · intro y _ hy; rw [if_neg]; rintro ⟨h, _⟩; exact hy h.symm
    · simp
  rw [sum_comm]
  have hrow : ∀ y, ∑ y', P.loop.B y y' = 1 - ∑ x, P.loop.A y x := fun y => by
    have := P.row y; linarith
  rw [sum_congr rfl fun y _ => hrow y, sum_sub_distrib, hA]
  unfold ReusePolicy.pAcc
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  field_simp

/-- Centring (as `Bathwater.centre_le`, restated here outside the ordered section). -/
lemma centre_le {Y : Type*} [Fintype Y] (f : Y → ℚ) (N a m : ℚ) (hN : 0 < N)
    (hcard : (Fintype.card Y : ℚ) = N) (hf : ∑ y, f y = N * a) :
    ∑ y, |f y / N - a / N| ≤ 2 * ∑ y, |f y / N - m / N| := by
  set g := fun y => f y / N - m / N with hg_def
  have hg : ∑ y, g y = a - m := by
    simp only [g, sum_sub_distrib, ← sum_div, hf, sum_const, card_univ, nsmul_eq_mul, hcard]
    field_simp
  have h1 : ∀ y, |f y / N - a / N| ≤ |g y| + |a - m| / N := fun y => by
    have : f y / N - a / N = g y + (m - a) / N := by simp only [g]; ring
    rw [this]; refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hN, abs_sub_comm m a]
  calc ∑ y, |f y / N - a / N| ≤ ∑ y, (|g y| + |a - m| / N) := sum_le_sum fun y _ => h1 y
    _ = ∑ y, |g y| + |a - m| := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hcard]; field_simp
    _ ≤ ∑ y, |g y| + ∑ y, |g y| := by
        rw [← hg]; linarith [abs_sum_le_sum_abs g (univ : Finset Y)]
    _ = 2 * ∑ y, |f y / N - m / N| := by ring

/-- **Column sums of alt-r0**: `1 − ρ(y') + E_y[Pr_c(r₀ pass ∧ z fail)]`. Only `ρ` varies. -/
lemma col_eq (H : Finset ι) (r0 zok : (ι → V) → C → Bool) (y' : ι → V) :
    ∑ y, (altR0Set H r0 zok).loop.B y y' =
      1 - AltR0Set.rho H r0 y' + (∑ y, AltR0Set.zfail r0 zok y) / Fintype.card (ι → V) := by
  have hW : (0 : ℚ) < (Fintype.card V : ℚ) ^ H.card :=
    pow_pos (by exact_mod_cast Fintype.card_pos) _
  simp only [AltR0Set.B_eq, sum_add_distrib, ← sum_div]
  have e : ∀ y : ι → V, (if ∀ j ∉ H, y j = y' j then (1 - AltR0Set.sacc r0 y) /
      (Fintype.card V : ℚ) ^ H.card else 0) =
      ((if ∀ j ∉ H, y j = y' j then (1 : ℚ) else 0) -
        (if ∀ j ∉ H, y j = y' j then AltR0Set.sacc r0 y else 0)) /
        (Fintype.card V : ℚ) ^ H.card := fun y => by split_ifs <;> simp [sub_div]
  rw [sum_congr rfl fun y _ => e y, ← sum_div, sum_sub_distrib, AltR0Set.card_class,
    AltR0Set.rho_eq, sub_div, div_self hW.ne']

/-- **Defect of alt-r0** with resampled set `H`: for any constant `μ`, at most twice the mean
deviation `E_y |ρ(y) − μ|`. -/
theorem altR0Set_defect_le (H : Finset ι) (r0 zok : (ι → V) → C → Bool) (μ : ℚ) :
    (altR0Set H r0 zok).defect ≤
      2 * ((∑ y, |AltR0Set.rho H r0 y - μ|) / Fintype.card (ι → V)) := by
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  set N : ℚ := (Fintype.card (ι → V) : ℚ) with hN_def
  set Z : ℚ := (∑ y, AltR0Set.zfail r0 zok y) / N
  have hcent := centre_le (fun y' => ∑ y, (altR0Set H r0 zok).loop.B y y') N
    (1 - (altR0Set H r0 zok).pAcc) (1 - μ + Z) hN rfl (col_total _)
  unfold ReusePolicy.defect
  refine hcent.trans (le_of_eq ?_)
  congr 1
  rw [sum_div]
  refine sum_congr rfl fun y' _ => ?_
  simp only [col_eq]
  rw [show (1 - AltR0Set.rho H r0 y' + Z) / N - (1 - μ + Z) / N =
      -((AltR0Set.rho H r0 y' - μ) / N) by ring, abs_neg, abs_div, abs_of_pos hN]

/-- alt-r0 accepts exactly when both checks pass. -/
lemma altR0Set_accept (H : Finset ι) (r0 zok : (ι → V) → C → Bool) (y : ι → V) (c : C) :
    altR0Set H r0 zok y c = none ↔ (r0 y c && zok y c) = true := by
  unfold altR0Set; cases r0 y c <;> cases zok y c <;> simp

/-- The acceptance probability of alt-r0 is vanilla's. -/
lemma altR0Set_pAcc (H : Finset ι) (r0 zok : (ι → V) → C → Bool) :
    (altR0Set H r0 zok).pAcc = AltR0Set.pacc (fun y c => r0 y c && zok y c) := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < Fintype.card (ι → V) := by exact_mod_cast Fintype.card_pos
  unfold ReusePolicy.pAcc AltR0Set.pacc AltR0Set.sacc
  rw [← sum_div, div_div, mul_comm (Fintype.card C : ℚ)]
  congr 1
  rw [card_filter, Fintype.sum_prod_type]; push_cast
  refine sum_congr rfl fun y _ => sum_congr rfl fun c _ => ?_
  simp only [altR0Set_accept]

end Generic

end Bathwater.AltR0Joint

/-! ## The ML-DSA instance -/

namespace AltR0Final
open RejOrder Matrix

section AltR0JointInst

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ} {C : Type*} [Fintype C] {γ₁ β : ℕ}

/-- **Defect of alt-r0 for ML-DSA** (any head `h₀`): at most `2 X`. -/
theorem altR0Set_defect_le [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (a : Fin K → Fin L → Fin n → ZMod q) (h₀ : Fin L) :
    (Bathwater.altR0Set {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u)).defect ≤
      2 * X mulmat γ₁ γ₂ β mb v h₀ a := by
  set μ := mu q γ₂ β mb K n
  have hμ : 0 < μ := mu_pos hp
  have hN : (0 : ℚ) < Fintype.card (Fin L → V γ₁ n) := by exact_mod_cast Fintype.card_pos
  refine (Bathwater.AltR0Joint.altR0Set_defect_le {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u)
    μ).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hd := dev_le mulmat hp v a h₀
  unfold Bathwater.AltR0Set.dev at hd
  set S := ∑ y, |Bathwater.AltR0Set.rho {h₀} (r0 mulmat γ₁ γ₂ β v a) y - μ|
  calc S / Fintype.card (Fin L → V γ₁ n)
      = S / (Fintype.card (Fin L → V γ₁ n) * μ) * μ := by field_simp
    _ ≤ X mulmat γ₁ γ₂ β mb v h₀ a / μ * μ := mul_le_mul_of_nonneg_right hd hμ.le
    _ = X mulmat γ₁ γ₂ β mb v h₀ a := by field_simp

/-- alt-r0 accepts with vanilla's probability. -/
lemma altR0Set_pAcc_eq [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₂ : ℕ)
    (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q)
    (h₀ : Fin L) :
    (Bathwater.altR0Set {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u)).pAcc =
      Bathwater.AltR0Set.pacc (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) :=
  Bathwater.AltR0Joint.altR0Set_pAcc _ _ _

/-- **Per-attempt closeness of alt-r0, general form.** For a matrix that is not `Bad2` at level
`ε < p_z`, in every attempt window `k`, alt-r0's joint law of (attempt number, output) over the
first `k` attempts is within `k · 2ε/(p_z − ε)` of vanilla's in `ℓ¹`, and it is still running after
`k` attempts with probability at most `(1 − μ(p_z − ε))^k + 2ε/(p_z − ε)`. -/
theorem altR0_joint_main [Nonempty C] [Nonempty (V γ₁ n)]
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) {γ₂ mb : ℕ}
    (hp : Params q γ₁ γ₂ β mb) (u : C → Fin (L * n) → ℤ) (v : C → Fin (K * n) → ℤ)
    (hu : ∀ c, Bounded β (u c)) (h₀ : Fin L) {ε : ℚ} (hε : 0 < ε)
    (a : Fin K → Fin L → Fin n → ZMod q) (ha : ¬ Bad2 mulmat γ₁ γ₂ β mb u v h₀ ε a)
    (hpz : ε < pz γ₁ β L n) (k : ℕ) :
    ∑ x, |(Bathwater.altR0Set {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u)).loop.outUpTo k x -
        (Bathwater.vanilla (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c)).loop.outUpTo
          k x| ≤ k * (2 * ε / (pz γ₁ β L n - ε)) ∧
      ∑ y, (Bathwater.altR0Set {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u)).loop.state k y ≤
        (1 - mu q γ₂ β mb K n * (pz γ₁ β L n - ε)) ^ k + 2 * ε / (pz γ₁ β L n - ε) ∧
      mu q γ₂ β mb K n * (pz γ₁ β L n - ε) ≤
        (Bathwater.altR0Set {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u)).pAcc := by
  set μ := mu q γ₂ β mb K n
  set P := Bathwater.altR0Set {h₀} (r0 mulmat γ₁ γ₂ β v a) (zok γ₁ β u)
  have hμ : 0 < μ := mu_pos hp
  have hη : 0 < μ * ε := mul_pos hμ hε
  simp only [Bad2, not_or, not_le] at ha
  have hXa := X_lt_of_X2 mulmat v h₀ a hη ha.1
  have hZa := Xz_lt_of_Xz2 mulmat u v h₀ a hη ha.2
  have hdef : P.defect ≤ 2 * (μ * ε) :=
    (altR0Set_defect_le mulmat hp u v a h₀).trans (by linarith)
  have hpacc : μ * (pz γ₁ β L n - ε) ≤ P.pAcc := by
    rw [altR0Set_pAcc_eq]
    have := pacc_ge mulmat hp u v hu a h₀
    linarith
  have hgap : 0 < μ * (pz γ₁ β L n - ε) := mul_pos hμ (by linarith)
  have hp0 : 0 < P.pAcc := lt_of_lt_of_le hgap hpacc
  have hratio : P.defect / P.pAcc ≤ 2 * ε / (pz γ₁ β L n - ε) := by
    calc P.defect / P.pAcc ≤ 2 * (μ * ε) / (μ * (pz γ₁ β L n - ε)) :=
          div_le_div₀ (by positivity) hdef hgap hpacc
      _ = 2 * ε / (pz γ₁ β L n - ε) := by
          rw [mul_left_comm, mul_div_mul_left _ _ hμ.ne']
  have hPQ : ∀ y c, P y c = none ↔
      Bathwater.vanilla (fun y c => r0 mulmat γ₁ γ₂ β v a y c && zok γ₁ β u y c) y c = none := by
    intro y c
    rw [Bathwater.AltR0Joint.altR0Set_accept]
    unfold Bathwater.vanilla
    split_ifs with h <;> simp [h]
  refine ⟨?_, ?_, hpacc⟩
  · refine (P.outUpTo_close _ (Bathwater.vanilla_invariant _) hPQ hp0 k).trans ?_
    exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
  · refine (P.survive_close hp0 k).trans (add_le_add ?_ hratio)
    exact pow_le_pow_left₀ (by linarith [P.pAcc_le_one]) (by linarith) k

end AltR0JointInst

/-! ## Headlines -/

/-- Shared tail of the three headlines. -/
lemma joint_headline_aux {μ pz pAcc ε B : ℚ} (k : ℕ) (hμ : 0 < μ) (hgap : 1 / 2 ≤ pz - ε)
    (hB : 2 * ε / (1 / 2) ≤ B) (hε : 0 ≤ ε) (hp1 : pAcc ≤ 1) (hpacc : μ * (pz - ε) ≤ pAcc)
    {d s : ℚ} (hd : d ≤ k * (2 * ε / (pz - ε)))
    (hs : s ≤ (1 - μ * (pz - ε)) ^ k + 2 * ε / (pz - ε)) :
    d ≤ k * B ∧ s ≤ (1 - μ / 2) ^ k + B := by
  have hb : 2 * ε / (pz - ε) ≤ B :=
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) hgap).trans hB
  refine ⟨hd.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)), hs.trans (add_le_add ?_ hb)⟩
  refine pow_le_pow_left₀ (by linarith) ?_ k
  nlinarith

/-- **ML-DSA-44, alt-r0, per attempt.** `ε = 2^-127`, any head `h₀`. Bad fraction `≤ 1 / 2 ^ 127` (the
same bad set as `altR0_mldsa44`); for every other `A` and every `k`, over the first `k` attempts
the joint law of (attempt number, output) of alt-r0 is within `k · 2^-125` of vanilla's in `ℓ¹`,
and alt-r0 is still running after `k` attempts with probability `≤ (1 − μ/2)^k + 2^-125`. -/
theorem altR0_joint_mldsa44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hu : ∀ c, Bounded 78 (u c)) (hv : ∀ c, Bounded 78 (v c))
    (h₀ : Fin 4) :
    ((univ.filter fun A : Matrix (Fin 4) (Fin 4) Rq =>
        Bad2R (2 ^ 17) 95232 78 44 u v h₀ (1 / 2 ^ 127) A).card : ℚ) / Fintype.card (Matrix (Fin 4) (Fin 4) Rq)
        ≤ 1 / 2 ^ 127 ∧
      ∀ A, ¬ Bad2R (2 ^ 17) 95232 78 44 u v h₀ (1 / 2 ^ 127) A → ∀ k : ℕ,
        ∑ x, |(Bathwater.altR0Set {h₀} (r0R (2 ^ 17) 95232 78 v A)
              (zok (2 ^ 17) 78 u)).loop.outUpTo k x -
            (Bathwater.vanilla (fun y c => r0R (2 ^ 17) 95232 78 v A y c &&
              zok (2 ^ 17) 78 u y c)).loop.outUpTo k x| ≤ k * (1 / 2 ^ 125) ∧
        ∑ y, (Bathwater.altR0Set {h₀} (r0R (2 ^ 17) 95232 78 v A)
              (zok (2 ^ 17) 78 u)).loop.state k y ≤
          (1 - mu 8380417 95232 78 44 4 256 / 2) ^ k + 1 / 2 ^ 125 := by
  obtain ⟨h1, -⟩ := main2 negacyclic params_mldsa44 u v hu h₀ (ε := 1 / 2 ^ 127) (by norm_num)
    (avg_X2_44 v hv h₀) (avg_Xz2_44 u v hv h₀)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha k
  have hpz := pz_ge_44
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 17) 78 4 256 - 1 / 2 ^ 127 := by
    have : (1 / 2 : ℚ) + 1 / 2 ^ 127 ≤ 27 / 50 := by norm_num
    linarith
  obtain ⟨d1, d2, d3⟩ := altR0_joint_main negacyclic params_mldsa44 u v hu h₀
    (by norm_num) a ha (by linarith) k
  exact joint_headline_aux k (mu_pos params_mldsa44) hgap (by norm_num) (by norm_num)
    (Bathwater.ReusePolicy.pAcc_le_one _) d3 d1 d2

/-- **ML-DSA-65, alt-r0, per attempt.** `ε = 2^-140`, any head `h₀`. Bad fraction `≤ 1 / 2 ^ 139` (the
same bad set as `altR0_mldsa65`); for every other `A` and every `k`, over the first `k` attempts
the joint law of (attempt number, output) of alt-r0 is within `k · 2^-138` of vanilla's in `ℓ¹`,
and alt-r0 is still running after `k` attempts with probability `≤ (1 − μ/2)^k + 2^-138`. -/
theorem altR0_joint_mldsa65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hu : ∀ c, Bounded 196 (u c)) (hv : ∀ c, Bounded 196 (v c))
    (h₀ : Fin 5) :
    ((univ.filter fun A : Matrix (Fin 6) (Fin 5) Rq =>
        Bad2R (2 ^ 19) 261888 196 16 u v h₀ (1 / 2 ^ 140) A).card : ℚ) / Fintype.card (Matrix (Fin 6) (Fin 5) Rq)
        ≤ 1 / 2 ^ 139 ∧
      ∀ A, ¬ Bad2R (2 ^ 19) 261888 196 16 u v h₀ (1 / 2 ^ 140) A → ∀ k : ℕ,
        ∑ x, |(Bathwater.altR0Set {h₀} (r0R (2 ^ 19) 261888 196 v A)
              (zok (2 ^ 19) 196 u)).loop.outUpTo k x -
            (Bathwater.vanilla (fun y c => r0R (2 ^ 19) 261888 196 v A y c &&
              zok (2 ^ 19) 196 u y c)).loop.outUpTo k x| ≤ k * (1 / 2 ^ 138) ∧
        ∑ y, (Bathwater.altR0Set {h₀} (r0R (2 ^ 19) 261888 196 v A)
              (zok (2 ^ 19) 196 u)).loop.state k y ≤
          (1 - mu 8380417 261888 196 16 6 256 / 2) ^ k + 1 / 2 ^ 138 := by
  obtain ⟨h1, -⟩ := main2 negacyclic params_mldsa65 u v hu h₀ (ε := 1 / 2 ^ 140) (by norm_num)
    (avg_X2_65 v hv h₀) (avg_Xz2_65 u v hv h₀)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha k
  have hpz := pz_ge_65
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 196 5 256 - 1 / 2 ^ 140 := by
    have : (1 / 2 : ℚ) + 1 / 2 ^ 140 ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2, d3⟩ := altR0_joint_main negacyclic params_mldsa65 u v hu h₀
    (by norm_num) a ha (by linarith) k
  exact joint_headline_aux k (mu_pos params_mldsa65) hgap (by norm_num) (by norm_num)
    (Bathwater.ReusePolicy.pAcc_le_one _) d3 d1 d2

/-- **ML-DSA-87, alt-r0, per attempt.** `ε = 2^-157`, any head `h₀`. Bad fraction `≤ 1 / 2 ^ 157` (the
same bad set as `altR0_mldsa87`); for every other `A` and every `k`, over the first `k` attempts
the joint law of (attempt number, output) of alt-r0 is within `k · 2^-155` of vanilla's in `ℓ¹`,
and alt-r0 is still running after `k` attempts with probability `≤ (1 − μ/2)^k + 2^-155`. -/
theorem altR0_joint_mldsa87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hu : ∀ c, Bounded 120 (u c)) (hv : ∀ c, Bounded 120 (v c))
    (h₀ : Fin 7) :
    ((univ.filter fun A : Matrix (Fin 8) (Fin 7) Rq =>
        Bad2R (2 ^ 19) 261888 120 16 u v h₀ (1 / 2 ^ 157) A).card : ℚ) / Fintype.card (Matrix (Fin 8) (Fin 7) Rq)
        ≤ 1 / 2 ^ 157 ∧
      ∀ A, ¬ Bad2R (2 ^ 19) 261888 120 16 u v h₀ (1 / 2 ^ 157) A → ∀ k : ℕ,
        ∑ x, |(Bathwater.altR0Set {h₀} (r0R (2 ^ 19) 261888 120 v A)
              (zok (2 ^ 19) 120 u)).loop.outUpTo k x -
            (Bathwater.vanilla (fun y c => r0R (2 ^ 19) 261888 120 v A y c &&
              zok (2 ^ 19) 120 u y c)).loop.outUpTo k x| ≤ k * (1 / 2 ^ 155) ∧
        ∑ y, (Bathwater.altR0Set {h₀} (r0R (2 ^ 19) 261888 120 v A)
              (zok (2 ^ 19) 120 u)).loop.state k y ≤
          (1 - mu 8380417 261888 120 16 8 256 / 2) ^ k + 1 / 2 ^ 155 := by
  obtain ⟨h1, -⟩ := main2 negacyclic params_mldsa87 u v hu h₀ (ε := 1 / 2 ^ 157) (by norm_num)
    (avg_X2_87 v hv h₀) (avg_Xz2_87 u v hv h₀)
  refine ⟨(frac_ring _).trans_le (h1.trans (le_of_eq (by field_simp))), fun A => ?_⟩
  simp only [← r0_coeffsOf, Bad2R]
  generalize coeffsOf A = a
  intro ha k
  have hpz := pz_ge_87
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 120 7 256 - 1 / 2 ^ 157 := by
    have : (1 / 2 : ℚ) + 1 / 2 ^ 157 ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2, d3⟩ := altR0_joint_main negacyclic params_mldsa87 u v hu h₀
    (by norm_num) a ha (by linarith) k
  exact joint_headline_aux k (mu_pos params_mldsa87) hgap (by norm_num) (by norm_num)
    (Bathwater.ReusePolicy.pAcc_le_one _) d3 d1 d2

end AltR0Final

end

end AltR0JointPart
