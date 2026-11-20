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
