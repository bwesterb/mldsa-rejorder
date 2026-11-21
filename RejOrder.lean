import Mathlib

/-!
# The order of rejection checks in circl's ML-DSA leaks nothing through timing

One signing attempt, with the challenge fixed. `leak M u v` is the total distance between the
probabilities of the rejection views and reference values that do not depend on the secret
shifts `u = c·s₁`, `v = c·s₂`.

* `indist`: for any matrix, two secrets with the same public value cannot be told apart from the
  timing view with advantage more than the sum of their leaks.
* `leak_mldsa44`, `leak_mldsa65`, `leak_mldsa87`: for `A` uniform in `R_q^{K×L}`
  (`R_q = AdjoinRoot (X^256 + 1)` over `ZMod 8380417`), the leak is at most `2^-405`, `2^-547`,
  `2^-729` on average over `A`.
* `bad_frac_mldsa44` etc.: over many attempts, few matrices are bad.

The proof: every view is a difference of prefix-pass product sets (`leak_le_Dev`); the second
moment over `A` of each deviation is a sum of covariances of product-set indicators, bounded by
Fourier analysis (`cov_le`) by a weighted count of test vectors orthogonal to the image; those
live on the degenerate NTT slots of the pair of nonces (`dualIn_of_orth`, `deg_card_prob`), and
are counted row by row with the free-run (gap) counts (`wcount_le_rows`).

Sections, in order: `Defs` (the model), `Layer0` (exact counting), `Layer1` (accepted attempts),
`Leak`, `Uncertainty`, `Module`, `ModuleProb`, `ModuleCount`, `Profile`, `Negacyclic`, `RingForm`,
`Numeric`, `GapCount`, `GapComb`, `GapEval`, `GapSum`, `GapNumeric`, `Covariance`,
`TestVectors`, `FourierLeak`, `MLDSA`, `Headline`.
-/

section Defs
/-!
# Definitions

These follow the Lean brief "ML-DSA rejection-check order in circl" verbatim,
except that `firstIdx` is implemented (the brief left it as `sorry`).
-/

open Finset

noncomputable section

namespace RejOrder

/-- Probability of `P` under the uniform distribution on the finset `B`. -/
def prob {α : Type*} (B : Finset α) (P : α → Prop) [DecidablePred P] : ℚ :=
  ((B.filter P).card : ℚ) / B.card

/-- Side conditions on the parameters. -/
structure Params (q γ₁ γ₂ β mb : ℕ) : Prop where
  q_eq    : q = 2 * γ₂ * mb + 1
  β_lt_γ₁ : β < γ₁
  β_lt_γ₂ : β < γ₂
  mb_pos  : 0 < mb

variable (q γ₁ γ₂ β mb : ℕ) [NeZero q] {l m : ℕ}

/-- The box y is drawn from: every coordinate in (-γ₁, γ₁]. -/
def box (l : ℕ) : Finset (Fin l → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ioc (-(γ₁ : ℤ)) γ₁

/-- Low part of FIPS 204 Decompose with α = 2γ₂. Lies in [-γ₂, γ₂]. -/
def lowBits (w : ZMod q) : ℤ :=
  let r  : ℤ := (ZMod.val w : ℤ)
  let r' : ℤ := r % (2 * γ₂)
  let r0 : ℤ := if r' ≤ γ₂ then r' else r' - 2 * γ₂
  if r - r0 = (q : ℤ) - 1 then r0 - 1 else r0

def Bounded {ι : Type*} (u : ι → ℤ) : Prop := ∀ k, |u k| ≤ (β : ℤ)

/-- w = M · (y mod q). -/
def wOf (M : Matrix (Fin m) (Fin l) (ZMod q)) (y : Fin l → ℤ) : Fin m → ZMod q :=
  M.mulVec fun k => (y k : ZMod q)

def zFails (u y : Fin l → ℤ) (k : Fin l) : Prop :=
  (γ₁ : ℤ) - β ≤ |y k + u k|

def rFails (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ)
    (y : Fin l → ℤ) (i : Fin m) : Prop :=
  (γ₂ : ℤ) - β ≤ |lowBits q γ₂ (wOf q M y i) - v i|

instance (u y : Fin l → ℤ) : DecidablePred (zFails γ₁ β u y) :=
  fun _ => by unfold zFails; infer_instance

instance (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (y : Fin l → ℤ) :
    DecidablePred (rFails q γ₂ β M v y) :=
  fun _ => by unfold rFails; infer_instance

/-- Least index satisfying `P`, if any. -/
def firstIdx {n : ℕ} (P : Fin n → Prop) [DecidablePred P] : Option (Fin n) :=
  if h : (univ.filter P).Nonempty then some ((univ.filter P).min' h) else none

def J (u y : Fin l → ℤ) : Option (Fin l) := firstIdx (zFails γ₁ β u y)

def I (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (y : Fin l → ℤ) :
    Option (Fin m) := firstIdx (rFails q γ₂ β M v y)

/-- What a timing attacker sees of one attempt, plus z when it is accepted. -/
inductive View (l m : ℕ)
  | rFail (i : Fin m)
  | zFail (j : Fin l)
  | pass  (z : Fin l → ℤ)
  deriving DecidableEq

/-- circl's order: r₀ check first, then z check. -/
def view (M : Matrix (Fin m) (Fin l) (ZMod q)) (u : Fin l → ℤ) (v : Fin m → ℤ)
    (y : Fin l → ℤ) : View l m :=
  match I q γ₂ β M v y with
  | some i => .rFail i
  | none =>
    match J γ₁ β u y with
    | some j => .zFail j
    | none   => .pass (y + u)

def pR : ℚ := 1 - (mb * (2 * ((γ₂ : ℚ) - β) - 1)) / q
def pZ : ℚ := (2 * (β : ℚ) + 1) / (2 * γ₁)

/-- First failure among `n` independent trials with failure probability `p`. -/
def geom (p : ℚ) (n : ℕ) : Option (Fin n) → ℚ
  | some i => (1 - p) ^ (i : ℕ) * p
  | none   => (1 - p) ^ n

/-- The y for which the z check first fails at `j`. -/
def Bset (u : Fin l → ℤ) (j : Fin l) : Finset (Fin l → ℤ) :=
  (box γ₁ l).filter fun y => J γ₁ β u y = some j

end RejOrder

end
end Defs

section Layer0
/-!
# Layer 0: exact counting
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## Generic facts about `prob` and `firstIdx` -/

section Generic

variable {α : Type*}

lemma prob_congr (B : Finset α) {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ y ∈ B, P y ↔ Q y) : prob B P = prob B Q := by
  unfold prob; rw [Finset.filter_congr h]

lemma prob_true (B : Finset α) (hB : B.Nonempty) : prob B (fun _ => True) = 1 := by
  unfold prob
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
  have : (B.card : ℚ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  field_simp

lemma prob_not (B : Finset α) (hB : B.Nonempty) (P : α → Prop) [DecidablePred P] :
    prob B (fun y => ¬ P y) = 1 - prob B P := by
  unfold prob
  have h := Finset.card_filter_add_card_filter_not (s := B) P
  have : (B.card : ℚ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq this]
  exact_mod_cast (by omega : (B.filter (fun y => ¬ P y)).card + (B.filter P).card = B.card)

/-- Probability of a product event on a product set is the product of the probabilities. -/
lemma prob_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    (S : ∀ i, Finset (β i)) (P : ∀ i, β i → Prop) [∀ i, DecidablePred (P i)]
    (Q : (∀ i, β i) → Prop) [DecidablePred Q]
    (hQ : ∀ y ∈ Fintype.piFinset S, Q y ↔ ∀ i, P i (y i)) :
    prob (Fintype.piFinset S) Q = ∏ i, prob (S i) (P i) := by
  unfold prob
  have : (Fintype.piFinset S).filter Q = Fintype.piFinset (fun i => (S i).filter (P i)) := by
    ext y; simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact ⟨h1 i, ((hQ y (Fintype.mem_piFinset.mpr h1)).mp h2) i⟩
    · intro h
      have h1 : ∀ i, y i ∈ S i := fun i => (h i).1
      exact ⟨h1, (hQ y (Fintype.mem_piFinset.mpr h1)).mpr fun i => (h i).2⟩
  rw [this, Fintype.card_piFinset, Fintype.card_piFinset]
  push_cast
  rw [Finset.prod_div_distrib]

lemma firstIdx_eq_some {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (i : Fin n) :
    firstIdx P = some i ↔ P i ∧ ∀ j < i, ¬ P j := by
  unfold firstIdx
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      refine ⟨(Finset.mem_filter.mp (Finset.min'_mem _ h)).2, fun j hj hPj => ?_⟩
      exact absurd (Finset.min'_le _ j (by simp [hPj])) (not_le.mpr hj)
    · rintro ⟨hPi, hlt⟩
      apply le_antisymm
      · exact Finset.min'_le _ i (by simp [hPi])
      · apply Finset.le_min'
        intro j hj
        by_contra hji
        exact hlt j (not_le.mp hji) (Finset.mem_filter.mp hj).2
  · simp only [false_iff, not_and, not_forall, not_not]
    intro hPi
    exact absurd ⟨i, by simp [hPi]⟩ h

lemma firstIdx_eq_none {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    firstIdx P = none ↔ ∀ i, ¬ P i := by
  unfold firstIdx
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨i, hi⟩ := h
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · simp only [true_iff]
    intro i hPi
    exact h ⟨i, by simp [hPi]⟩

/-- `∏ₖ (a if k < j, b if k = j, 1 otherwise) = a ^ j * b`. -/
lemma prod_geom_some {n : ℕ} (j : Fin n) (a b : ℚ) :
    ∏ k : Fin n, (if k < j then a else if k = j then b else 1) = a ^ (j : ℕ) * b := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_ite_eq']
  have h1 : (Finset.univ.filter fun k : Fin n => k < j) = Finset.Iio j := by
    ext k; simp
  rw [h1, Fin.card_Iio]
  simp

end Generic

/-! ## Interval counting -/

/-- Shifting by `u` with `|u| ≤ b` does not change how many points of `(-g, g]` land in the
open interval `(-(g-b), g-b)`. -/
lemma Ioc_pass_card (g b : ℕ) (u : ℤ) (hb : b < g) (hu : |u| ≤ b) :
    ((Finset.Ioc (-(g : ℤ)) g).filter fun y => |y + u| < (g : ℤ) - b).card
      = 2 * (g - b) - 1 := by
  have : ((Finset.Ioc (-(g : ℤ)) g).filter fun y => |y + u| < (g : ℤ) - b)
      = Finset.Icc (-((g : ℤ) - b - 1) - u) ((g : ℤ) - b - 1 - u) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, abs_lt]
    rw [abs_le] at hu
    omega
  rw [this, Int.card_Icc]
  omega

/-! ## The decomposition behind `lowBits` -/

section Decompose

variable {q γ₁ γ₂ β mb : ℕ} [NeZero q]

private lemma emod_decomp (a t s : ℤ) (h0 : 0 ≤ s) (h1 : s < a) : (s + a * t) % a = s := by
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

/-- `lowBits` recovers `x` from `2γ₂·k + x` whenever `(k, x)` is a valid decomposition: either
`k < mb` and `x ∈ (-γ₂, γ₂]`, or the one corner point `k = 0`, `x = -γ₂`. -/
lemma lowBits_enc (hp : Params q γ₁ γ₂ β mb) (k : ℕ) (x : ℤ) (hk : k < mb)
    (hx : (-(γ₂ : ℤ) < x ∧ x ≤ γ₂) ∨ (x = -γ₂ ∧ k = 0)) :
    lowBits q γ₂ (((2 * γ₂ * k : ℤ) + x : ℤ) : ZMod q) = x := by
  have hγ : 0 < γ₂ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₂
  have hq : (q : ℤ) = 2 * γ₂ * mb + 1 := by exact_mod_cast hp.q_eq
  -- products as linear facts for omega
  have hkm : (2 * γ₂ * k : ℤ) + 2 * γ₂ ≤ 2 * γ₂ * mb := by
    have : (k : ℤ) + 1 ≤ mb := by exact_mod_cast hk
    nlinarith
  have hk0 : (0 : ℤ) ≤ 2 * γ₂ * k := by positivity
  have hk1 : k ≠ 0 → (2 * γ₂ : ℤ) ≤ 2 * γ₂ * k := by
    intro h
    have : (1 : ℤ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    nlinarith
  unfold lowBits
  simp only
  rw [ZMod.val_intCast]
  set a : ℤ := 2 * γ₂ with ha
  have ha0 : 0 < a := by omega
  by_cases hx0 : 0 ≤ x
  · -- ordinary case, nonnegative low part
    have hr : (a * k + x) % q = x + a * k := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; ring
    rw [hr, emod_decomp a k x hx0 (by omega)]
    split_ifs <;> omega
  · by_cases hkz : k = 0
    · -- k = 0 and x < 0: the reduction mod q wraps around
      subst hkz
      have hx' : -(γ₂ : ℤ) ≤ x := by omega
      have hr : (a * ((0 : ℕ) : ℤ) + x) % q = x + q := by
        rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]; push_cast; ring
      rw [hr]
      by_cases hx1 : x = -1
      · subst hx1
        have : (-1 + (q : ℤ)) = 0 + a * mb := by rw [hq]; ring
        rw [this, emod_decomp a mb 0 le_rfl ha0]
        split_ifs <;> omega
      · have : x + (q : ℤ) = (x + 1 + a) + a * (mb - 1) := by rw [hq]; ring
        have hm : a * ((mb : ℤ) - 1) = a * mb - a := by ring
        rw [this, emod_decomp a (mb - 1) (x + 1 + a) (by omega) (by omega)]
        split_ifs <;> omega
    · -- k ≥ 1 and x < 0
      have hkk := hk1 hkz
      have hr : (a * k + x) % q = a * k + x := Int.emod_eq_of_lt (by omega) (by omega)
      have : a * k + x = (x + a) + a * (k - 1) := by ring
      have hm : a * ((k : ℤ) - 1) = a * k - a := by ring
      rw [hr, this, emod_decomp a (k - 1) (x + a) (by omega) (by omega)]
      split_ifs <;> omega

variable (q γ₂ mb) in
/-- Valid decompositions `(r₁, r₀)` of an element of `ZMod q`. -/
def decSet : Finset (ℕ × ℤ) :=
  (Finset.range mb ×ˢ Finset.Ioc (-(γ₂ : ℤ)) γ₂) ∪ {(0, -(γ₂ : ℤ))}

variable (q γ₂) in
/-- Reassemble `r₁·2γ₂ + r₀` in `ZMod q`. -/
def enc (p : ℕ × ℤ) : ZMod q := (((2 * γ₂ * p.1 : ℤ) + p.2 : ℤ) : ZMod q)

lemma mem_decSet (hp : Params q γ₁ γ₂ β mb) (p : ℕ × ℤ) :
    p ∈ decSet γ₂ mb ↔
      p.1 < mb ∧ ((-(γ₂ : ℤ) < p.2 ∧ p.2 ≤ γ₂) ∨ (p.2 = -γ₂ ∧ p.1 = 0)) := by
  have := hp.mb_pos
  obtain ⟨k, x⟩ := p
  simp only [decSet, Finset.mem_union, Finset.mem_product, Finset.mem_range, Finset.mem_Ioc,
    Finset.mem_singleton, Prod.mk.injEq]
  omega

lemma lowBits_enc_of_mem (hp : Params q γ₁ γ₂ β mb) {p : ℕ × ℤ} (h : p ∈ decSet γ₂ mb) :
    lowBits q γ₂ (enc q γ₂ p) = p.2 := by
  rw [mem_decSet hp] at h
  exact lowBits_enc hp p.1 p.2 h.1 h.2

lemma enc_injOn (hp : Params q γ₁ γ₂ β mb) : Set.InjOn (enc q γ₂) (decSet γ₂ mb) := by
  intro p hp1 p' hp2 he
  have h2 : p.2 = p'.2 := by
    rw [← lowBits_enc_of_mem hp hp1, ← lowBits_enc_of_mem hp hp2, he]
  have hγ : 0 < γ₂ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₂
  have hm1 := ((mem_decSet hp p).mp hp1).1
  have hm2 := ((mem_decSet hp p').mp hp2).1
  have he' : ((2 * γ₂ * p.1 : ℕ) : ZMod q) = ((2 * γ₂ * p'.1 : ℕ) : ZMod q) := by
    unfold enc at he
    rw [h2] at he
    push_cast at he
    have := add_right_cancel he
    exact_mod_cast this
  rw [ZMod.natCast_eq_natCast_iff' _ _ q] at he'
  have hlt : ∀ k, k < mb → 2 * γ₂ * k < q := by
    intro k hk
    rw [hp.q_eq]
    have := Nat.mul_lt_mul_of_pos_left hk (by omega : 0 < 2 * γ₂)
    omega
  rw [Nat.mod_eq_of_lt (hlt _ hm1), Nat.mod_eq_of_lt (hlt _ hm2)] at he'
  have h1 : p.1 = p'.1 := Nat.eq_of_mul_eq_mul_left (by omega) he'
  exact Prod.ext h1 h2

lemma card_decSet (hp : Params q γ₁ γ₂ β mb) : (decSet γ₂ mb).card = q := by
  unfold decSet
  rw [Finset.card_union_of_disjoint, Finset.card_product, Finset.card_range, Int.card_Ioc,
    Finset.card_singleton]
  · rw [hp.q_eq]
    have : ((γ₂ : ℤ) - -(γ₂ : ℤ)).toNat = 2 * γ₂ := by omega
    rw [this]; ring
  · rw [Finset.disjoint_singleton_right]
    simp

lemma image_enc (hp : Params q γ₁ γ₂ β mb) :
    (decSet γ₂ mb).image (enc q γ₂) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn (enc_injOn hp), card_decSet hp, ZMod.card]

lemma exists_enc (hp : Params q γ₁ γ₂ β mb) (w : ZMod q) :
    ∃ p ∈ decSet γ₂ mb, enc q γ₂ p = w := by
  have : w ∈ (decSet γ₂ mb).image (enc q γ₂) := by rw [image_enc hp]; exact Finset.mem_univ _
  simpa using this

end Decompose

/-! ## The Layer 0 theorems -/

variable {q γ₁ γ₂ β mb : ℕ} [NeZero q] {l m : ℕ}

/-- z check: the number of passing y does not depend on the shift. -/
theorem z_pass_count (hp : Params q γ₁ γ₂ β mb) (u : ℤ) (hu : |u| ≤ β) :
    ((Finset.Ioc (-(γ₁ : ℤ)) γ₁).filter fun y => |y + u| < (γ₁ : ℤ) - β).card
      = 2 * (γ₁ - β) - 1 :=
  Ioc_pass_card γ₁ β u hp.β_lt_γ₁ hu

/-- r₀ check: the number of passing w in ZMod q does not depend on the shift. -/
theorem r_pass_count (hp : Params q γ₁ γ₂ β mb) (v : ℤ) (hv : |v| ≤ β) :
    ((Finset.univ : Finset (ZMod q)).filter
        fun w => |lowBits q γ₂ w - v| < (γ₂ : ℤ) - β).card
      = mb * (2 * (γ₂ - β) - 1) := by
  rw [← image_enc hp, Finset.filter_image,
    Finset.card_image_of_injOn ((enc_injOn hp).mono (Finset.filter_subset _ _))]
  rw [Finset.filter_congr (q := fun p : ℕ × ℤ => |p.2 - v| < (γ₂ : ℤ) - β)
    (fun p hp' => by rw [lowBits_enc_of_mem hp hp'])]
  unfold decSet
  have hprod : (Finset.range mb ×ˢ Finset.Ioc (-(γ₂ : ℤ)) γ₂).filter
      (fun p : ℕ × ℤ => |p.2 - v| < (γ₂ : ℤ) - β)
      = Finset.range mb ×ˢ (Finset.Ioc (-(γ₂ : ℤ)) γ₂).filter (fun x => |x - v| < (γ₂ : ℤ) - β) := by
    ext ⟨k, x⟩; simp only [Finset.mem_filter, Finset.mem_product]; tauto
  rw [Finset.filter_union, hprod, Finset.filter_singleton, if_neg,
    Finset.union_empty, Finset.card_product, Finset.card_range]
  · congr 1
    have h := Ioc_pass_card γ₂ β (-v) hp.β_lt_γ₂ (by rwa [abs_neg])
    simpa [sub_eq_add_neg] using h
  · rw [abs_le] at hv
    simp only [not_lt, abs_sub_comm]
    rw [le_abs]
    left; omega

/-- Lemma 3 of the Dilithium spec, in the form circl relies on. -/
theorem lowBits_shift (hp : Params q γ₁ γ₂ β mb) (w : ZMod q) (v : ℤ) (hv : |v| ≤ β) :
    |lowBits q γ₂ w - v| < (γ₂ : ℤ) - β ↔
    |lowBits q γ₂ (w - (v : ZMod q))| < (γ₂ : ℤ) - β := by
  rw [abs_le] at hv
  constructor
  · intro h
    obtain ⟨⟨k, x⟩, hmem, rfl⟩ := exists_enc hp w
    rw [lowBits_enc_of_mem hp hmem] at h
    have hk := ((mem_decSet hp _).mp hmem).1
    have he : enc q γ₂ (k, x) - (v : ZMod q) = enc q γ₂ (k, x - v) := by
      unfold enc; push_cast; ring
    rw [he, lowBits_enc_of_mem hp ((mem_decSet hp (k, x - v)).mpr ⟨hk, Or.inl (by
      simp only; rw [abs_lt] at h; omega)⟩)]
    exact h
  · intro h
    obtain ⟨⟨k, y⟩, hmem, he⟩ := exists_enc hp (w - (v : ZMod q))
    rw [← he, lowBits_enc_of_mem hp hmem] at h
    have hk := ((mem_decSet hp _).mp hmem).1
    have hw : w = enc q γ₂ (k, y + v) := by
      have : w = enc q γ₂ (k, y) + (v : ZMod q) := by rw [he]; ring
      rw [this]; unfold enc; push_cast; ring
    rw [hw, lowBits_enc_of_mem hp ((mem_decSet hp (k, y + v)).mpr ⟨hk, Or.inl (by
      simp only; rw [abs_lt] at h; omega)⟩)]
    simpa using h

lemma card_Ioc_γ₁ (hp : Params q γ₁ γ₂ β mb) :
    (Finset.Ioc (-(γ₁ : ℤ)) γ₁).card = 2 * γ₁ := by
  rw [Int.card_Ioc]; omega

lemma Ioc_γ₁_nonempty (hp : Params q γ₁ γ₂ β mb) : (Finset.Ioc (-(γ₁ : ℤ)) γ₁).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_Ioc_γ₁ hp]
  have := hp.β_lt_γ₁
  omega

/-- Per-coordinate z-check pass probability. -/
lemma prob_z_pass (hp : Params q γ₁ γ₂ β mb) (u : ℤ) (hu : |u| ≤ β) :
    prob (Finset.Ioc (-(γ₁ : ℤ)) γ₁) (fun t => ¬ ((γ₁ : ℤ) - β ≤ |t + u|)) = 1 - pZ γ₁ β := by
  have hβ := hp.β_lt_γ₁
  unfold prob pZ
  simp only [not_le]
  rw [z_pass_count hp u hu, card_Ioc_γ₁ hp]
  have : (γ₁ : ℚ) ≠ 0 := by exact_mod_cast (by omega : γ₁ ≠ 0)
  push_cast [show 1 ≤ 2 * (γ₁ - β) by omega, Nat.cast_sub hβ.le]
  field_simp
  ring

/-- Per-coordinate z-check failure probability. -/
lemma prob_z_fail (hp : Params q γ₁ γ₂ β mb) (u : ℤ) (hu : |u| ≤ β) :
    prob (Finset.Ioc (-(γ₁ : ℤ)) γ₁) (fun t => (γ₁ : ℤ) - β ≤ |t + u|) = pZ γ₁ β := by
  have h := prob_not _ (Ioc_γ₁_nonempty hp) (fun t => (γ₁ : ℤ) - β ≤ |t + u|)
  rw [prob_z_pass hp u hu] at h
  linarith

/-- The z check alone is exactly geometric, for every shift. -/
theorem J_dist (hp : Params q γ₁ γ₂ β mb) (u : Fin l → ℤ) (hu : Bounded β u)
    (o : Option (Fin l)) :
    prob (box γ₁ l) (fun y => J γ₁ β u y = o) = geom (pZ γ₁ β) l o := by
  unfold box
  cases o with
  | none =>
    rw [prob_pi _ (fun k t => ¬ ((γ₁ : ℤ) - β ≤ |t + u k|)) _ (fun y _ => by
      unfold J; rw [firstIdx_eq_none]; rfl)]
    simp_rw [prob_z_pass hp _ (hu _)]
    simp [geom]
  | some j =>
    rw [prob_pi _ (fun k t => (k < j → ¬ ((γ₁ : ℤ) - β ≤ |t + u k|)) ∧
        (k = j → (γ₁ : ℤ) - β ≤ |t + u k|)) _ (fun y _ => by
      unfold J; rw [firstIdx_eq_some]; unfold zFails
      constructor
      · rintro ⟨hj, hlt⟩ k
        exact ⟨hlt k, fun hk => hk ▸ hj⟩
      · intro h
        exact ⟨(h j).2 rfl, fun k hk => (h k).1 hk⟩)]
    have : ∀ k : Fin l, prob (Finset.Ioc (-(γ₁ : ℤ)) γ₁) (fun t =>
        (k < j → ¬ ((γ₁ : ℤ) - β ≤ |t + u k|)) ∧ (k = j → (γ₁ : ℤ) - β ≤ |t + u k|))
        = if k < j then 1 - pZ γ₁ β else if k = j then pZ γ₁ β else 1 := by
      intro k
      split_ifs with h1 h2
      · rw [← prob_z_pass hp (u k) (hu k)]
        exact prob_congr _ fun t _ => by simp [h1, ne_of_lt h1]
      · rw [← prob_z_fail hp (u k) (hu k)]
        exact prob_congr _ fun t _ => by simp [h2]
      · rw [← prob_true _ (Ioc_γ₁_nonempty hp)]
        exact prob_congr _ fun t _ => by simp [h1, h2]
    simp_rw [this]
    rw [prod_geom_some]
    rfl

end RejOrder

end
end Layer0

section Layer1
/-!
# Layer 1: the view, and the exact probability of an accepted attempt
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q γ₁ γ₂ β mb : ℕ} [NeZero q] {l m : ℕ}

/-! ## Helpers -/

section Views

variable (M : Matrix (Fin m) (Fin l) (ZMod q)) (u : Fin l → ℤ) (v : Fin m → ℤ) (y : Fin l → ℤ)

lemma view_eq_rFail (i : Fin m) :
    view q γ₁ γ₂ β M u v y = .rFail i ↔ I q γ₂ β M v y = some i := by
  unfold view
  rcases I q γ₂ β M v y with _ | i'
  · rcases J γ₁ β u y with _ | j <;> simp
  · simp

lemma view_eq_zFail (j : Fin l) :
    view q γ₁ γ₂ β M u v y = .zFail j ↔ I q γ₂ β M v y = none ∧ J γ₁ β u y = some j := by
  unfold view
  rcases I q γ₂ β M v y with _ | i'
  · rcases J γ₁ β u y with _ | j' <;> simp
  · simp

lemma view_eq_pass (z : Fin l → ℤ) :
    view q γ₁ γ₂ β M u v y = .pass z ↔
      I q γ₂ β M v y = none ∧ J γ₁ β u y = none ∧ y + u = z := by
  unfold view
  rcases I q γ₂ β M v y with _ | i'
  · rcases J γ₁ β u y with _ | j' <;> simp
  · simp

end Views

lemma wOf_sub (M : Matrix (Fin m) (Fin l) (ZMod q)) (z u : Fin l → ℤ) :
    wOf q M (z - u) = wOf q M z - wOf q M u := by
  unfold wOf
  rw [← Matrix.mulVec_sub]
  congr 1
  ext k
  simp

lemma card_box (hp : Params q γ₁ γ₂ β mb) : ((box γ₁ l).card : ℚ) = (2 * γ₁ : ℚ) ^ l := by
  unfold box
  rw [Fintype.card_piFinset, Finset.prod_const, card_Ioc_γ₁ hp, Finset.card_univ,
    Fintype.card_fin]
  push_cast; ring

/-! ## The main theorem -/

/-- Both pass: exact, and a function of z and the public value M·u + v only. -/
theorem view_pass (hp : Params q γ₁ γ₂ β mb) (M : Matrix (Fin m) (Fin l) (ZMod q))
    {u : Fin l → ℤ} {v : Fin m → ℤ} (hu : Bounded β u) (hv : Bounded β v) (z : Fin l → ℤ) :
    prob (box γ₁ l) (fun y => view q γ₁ γ₂ β M u v y = .pass z)
      = if (∀ k, |z k| < (γ₁ : ℤ) - β) ∧
           (∀ i, |lowBits q γ₂ (wOf q M z i - (wOf q M u i + (v i : ZMod q)))|
                   < (γ₂ : ℤ) - β)
        then 1 / ((2 * γ₁ : ℚ) ^ l) else 0 := by
  set C : Prop := (∀ k, |z k| < (γ₁ : ℤ) - β) ∧
           (∀ i, |lowBits q γ₂ (wOf q M z i - (wOf q M u i + (v i : ZMod q)))|
                   < (γ₂ : ℤ) - β) with hC
  have key : ∀ y, view q γ₁ γ₂ β M u v y = .pass z ↔ y = z - u ∧ C := by
    intro y
    rw [view_eq_pass]
    unfold I J
    rw [firstIdx_eq_none, firstIdx_eq_none]
    unfold rFails zFails
    simp only [not_le]
    have hlow : ∀ i, |lowBits q γ₂ (wOf q M (z - u) i) - v i| < (γ₂ : ℤ) - β ↔
        |lowBits q γ₂ (wOf q M z i - (wOf q M u i + (v i : ZMod q)))| < (γ₂ : ℤ) - β := by
      intro i
      rw [lowBits_shift hp _ (v i) (hv i), wOf_sub]
      simp only [Pi.sub_apply, sub_sub]
    constructor
    · rintro ⟨hI, hJ, rfl⟩
      simp only [add_sub_cancel_right, true_and]
      refine ⟨fun k => by simpa using hJ k, fun i => ?_⟩
      rw [← hlow, add_sub_cancel_right]
      exact hI i
    · rintro ⟨rfl, hz, hr⟩
      refine ⟨fun i => (hlow i).mpr (hr i), fun k => by simpa using hz k, by simp⟩
  rw [prob_congr _ (fun y _ => key y)]
  unfold prob
  rw [card_box hp]
  split_ifs with hc
  · have hmem : z - u ∈ box γ₁ l := by
      unfold box
      rw [Fintype.mem_piFinset]
      intro k
      have h1 := hc.1 k
      have h2 := hu k
      rw [abs_lt] at h1; rw [abs_le] at h2
      simp only [Pi.sub_apply, Finset.mem_Ioc]
      omega
    have : (box γ₁ l).filter (fun y => y = z - u ∧ C) = {z - u} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h, _⟩; exact h
      · rintro rfl; exact ⟨hmem, rfl, hc⟩
    rw [this, Finset.card_singleton]
    push_cast; ring
  · have : (box γ₁ l).filter (fun y => y = z - u ∧ C) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ _ h; exact hc h
    rw [this]; simp

end RejOrder

end
end Layer1

section Leak
/-!
# The leak of one attempt

`leak M u v` is the total distance between the probabilities of the rejection views and reference
values that do not depend on the secret shifts `u`, `v`. It bounds what any distinguisher can
learn (`indist`).
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## Averages -/

section Avg

variable {P : Type*} [Fintype P]

/-- Expectation of `f a` for `a` uniform on `P`. -/
def avg (f : P → ℚ) : ℚ := (∑ a, f a) / Fintype.card P

lemma avg_mono {f g : P → ℚ} (h : ∀ a, f a ≤ g a) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

lemma avg_nonneg {f : P → ℚ} (h : ∀ a, 0 ≤ f a) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

lemma avg_add (f g : P → ℚ) : avg (fun a => f a + g a) = avg f + avg g := by
  unfold avg; rw [Finset.sum_add_distrib, add_div]

lemma avg_mul_left (c : ℚ) (f : P → ℚ) : avg (fun a => c * f a) = c * avg f := by
  unfold avg; rw [← Finset.mul_sum, mul_div_assoc]

lemma avg_const [Nonempty P] (c : ℚ) : avg (fun _ : P => c) = c := by
  unfold avg
  have : (Fintype.card P : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma avg_finset_sum {ι : Type*} (S : Finset ι) (f : ι → P → ℚ) :
    avg (fun a => ∑ i ∈ S, f i a) = ∑ i ∈ S, avg (f i) := by
  unfold avg; rw [Finset.sum_comm, Finset.sum_div]

/-- Markov's inequality: the fraction of `a` with `f a ≥ η` is at most `avg f / η`. -/
theorem markov {f : P → ℚ} (hf : ∀ a, 0 ≤ f a) {ε η : ℚ} (hη : 0 < η) (h : avg f ≤ ε) :
    ((univ.filter fun a => η ≤ f a).card : ℚ) / Fintype.card P ≤ ε / η := by
  rw [le_div_iff₀ hη]
  refine le_trans ?_ h
  unfold avg
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc ((univ.filter fun a => η ≤ f a).card : ℚ) * η
      = ∑ a ∈ univ.filter (fun a => η ≤ f a), η := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ univ.filter (fun a => η ≤ f a), f a :=
        Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
    _ ≤ ∑ a, f a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ => hf a

end Avg

variable {q γ₁ γ₂ β mb : ℕ} [NeZero q] {l m : ℕ} {P : Type*} [Fintype P]

/-! ## The leak, and what it means -/

variable (q γ₁ γ₂ β mb) in
/-- Total deviation of the rejection views from secret-independent reference values:
the r₀ check first fails at `i` with probability `(1-p_R)^i p_R`, and the r₀ check passes and the
z check first fails at `j` with probability `(1-p_R)^m (1-p_Z)^j p_Z`. -/
def leak (M : Matrix (Fin m) (Fin l) (ZMod q)) (u : Fin l → ℤ) (v : Fin m → ℤ) : ℚ :=
  ∑ i : Fin m, |prob (box γ₁ l) (fun y => view q γ₁ γ₂ β M u v y = .rFail i)
      - geom (pR q γ₂ β mb) m (some i)|
  + ∑ j : Fin l, |prob (box γ₁ l) (fun y => view q γ₁ γ₂ β M u v y = .zFail j)
      - geom (pZ γ₁ β) l (some j) * geom (pR q γ₂ β mb) m none|

lemma prob_fiber {α β' : Type*} [DecidableEq β'] (B : Finset α) (f : α → β') (D : β' → Prop)
    [DecidablePred D] (X : Finset β') (hX : ∀ y ∈ B, f y ∈ X) :
    prob B (fun y => D (f y)) = ∑ x ∈ X, if D x then prob B (fun y => f y = x) else 0 := by
  unfold prob
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := B.filter fun y => D (f y)) (t := X)
    (fun y hy => hX y (Finset.mem_filter.mp hy).1)]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hD
  · have : (B.filter fun y => D (f y)).filter (fun y => f y = x) = B.filter fun y => f y = x := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hB, _⟩, hx⟩; exact ⟨hB, hx⟩
      · rintro ⟨hB, hx⟩; exact ⟨⟨hB, hx ▸ hD⟩, hx⟩
    rw [this]
  · have : (B.filter fun y => D (f y)).filter (fun y => f y = x) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, hDy⟩, hx⟩
      exact hD (hx ▸ hDy)
    rw [this]; simp

/-- **Indistinguishability.** For a fixed matrix, two secrets with the same public value
`M·u + v` cannot be told apart from the timing view of one attempt, by any test `D`, with
advantage more than the sum of their leaks. -/
theorem indist (hp : Params q γ₁ γ₂ β mb) (M : Matrix (Fin m) (Fin l) (ZMod q))
    {u u' : Fin l → ℤ} {v v' : Fin m → ℤ} (hu : Bounded β u) (hv : Bounded β v)
    (hu' : Bounded β u') (hv' : Bounded β v')
    (hpub : ∀ i, wOf q M u i + (v i : ZMod q) = wOf q M u' i + (v' i : ZMod q))
    (D : View l m → Prop) [DecidablePred D] :
    |prob (box γ₁ l) (fun y => D (view q γ₁ γ₂ β M u v y))
      - prob (box γ₁ l) (fun y => D (view q γ₁ γ₂ β M u' v' y))|
      ≤ leak q γ₁ γ₂ β mb M u v + leak q γ₁ γ₂ β mb M u' v' := by
  classical
  set Pr : View l m → ℚ := fun x => prob (box γ₁ l) (fun y => view q γ₁ γ₂ β M u v y = x)
  set Pr' : View l m → ℚ := fun x => prob (box γ₁ l) (fun y => view q γ₁ γ₂ β M u' v' y = x)
  set X : Finset (View l m) := (box γ₁ l).image (view q γ₁ γ₂ β M u v)
    ∪ (box γ₁ l).image (view q γ₁ γ₂ β M u' v') with hX
  rw [prob_fiber _ _ D X (fun y hy => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)),
    prob_fiber _ _ D X (fun y hy => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)),
    ← Finset.sum_sub_distrib]
  -- per-view bound
  set h : View l m → ℚ := fun x => match x with
    | .rFail i => |Pr (.rFail i) - geom (pR q γ₂ β mb) m (some i)|
        + |Pr' (.rFail i) - geom (pR q γ₂ β mb) m (some i)|
    | .zFail j => |Pr (.zFail j) - geom (pZ γ₁ β) l (some j) * geom (pR q γ₂ β mb) m none|
        + |Pr' (.zFail j) - geom (pZ γ₁ β) l (some j) * geom (pR q γ₂ β mb) m none|
    | .pass _ => 0 with hh
  have hh0 : ∀ x, 0 ≤ h x := by
    intro x; cases x <;> simp only [hh] <;> positivity
  have hterm : ∀ x, |Pr x - Pr' x| ≤ h x := by
    intro x
    cases x with
    | rFail i => simp only [hh]; rw [abs_sub_comm (Pr' _)]; exact abs_sub_le _ _ _
    | zFail j => simp only [hh]; rw [abs_sub_comm (Pr' _)]; exact abs_sub_le _ _ _
    | pass z =>
      have e : Pr (.pass z) = Pr' (.pass z) := by
        simp only [Pr, Pr']
        rw [view_pass hp M hu hv z, view_pass hp M hu' hv' z]
        simp_rw [hpub]
      simp only [hh, e, sub_self, abs_zero, le_refl]
  set Y : Finset (View l m) := (univ.image View.rFail) ∪ (univ.image View.zFail) with hY
  have hXY : ∑ x ∈ X, h x ≤ ∑ x ∈ Y, h x := by
    rw [← Finset.sum_filter_add_sum_filter_not X (· ∈ Y)]
    have z0 : ∑ x ∈ X.filter (fun x => ¬ x ∈ Y), h x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxY := (Finset.mem_filter.mp hx).2
      cases x with
      | rFail i => exact absurd (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) hxY
      | zFail j => exact absurd (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))) hxY
      | pass z => rfl
    rw [z0, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
      fun x _ _ => hh0 x
  have hYsum : ∑ x ∈ Y, h x = ∑ i : Fin m, h (.rFail i) + ∑ j : Fin l, h (.zFail j) := by
    rw [hY, Finset.sum_union, Finset.sum_image (fun a _ b _ hab => View.rFail.inj hab),
      Finset.sum_image (fun a _ b _ hab => View.zFail.inj hab)]
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx'
    cases hj
  calc |∑ x ∈ X, ((if D x then Pr x else 0) - (if D x then Pr' x else 0))|
      ≤ ∑ x ∈ X, |(if D x then Pr x else 0) - (if D x then Pr' x else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ X, h x := Finset.sum_le_sum fun x _ => by
        split_ifs
        · exact hterm x
        · simp only [sub_self, abs_zero]; exact hh0 x
    _ ≤ ∑ x ∈ Y, h x := hXY
    _ = _ := by
        rw [hYsum]
        simp only [hh, leak, Finset.sum_add_distrib]
        ring

/-! ## Reducing the leak to sparse tests -/

end RejOrder

end
end Leak

section Uncertainty
/-!
# Two Vandermonde facts

For distinct evaluation points `ζ k`:

* `window`: a polynomial of degree `< r` that vanishes at `r` of the points is zero.
* `dual_vanish`: the uncertainty principle. If `μ` is supported on at most `r` points and the
  power sums `∑ k, μ k * ζ k ^ t` vanish for `r` consecutive exponents `t`, then `μ = 0`.

`exists_free_run` supplies the consecutive exponents: a set `T` of exponents below `n` misses a
run of length `n / (|T| + 1)`.
-/

open Finset Polynomial

namespace RejOrder

variable {F : Type*} [Field F] {n : ℕ} (ζ : Fin n → F)

lemma window (hζ : Function.Injective ζ) (c : ℕ → F) (r : ℕ) (S : Finset (Fin n))
    (hr : r ≤ S.card) (h : ∀ k ∈ S, ∑ t ∈ range r, c t * ζ k ^ t = 0) :
    ∀ t < r, c t = 0 := by
  classical
  intro t ht
  set p : F[X] := ∑ t ∈ range r, C (c t) * X ^ t with hp
  have hp0 : p = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (S.image ζ)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      simp only [hp, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
      exact h k hk
    · rw [Finset.card_image_of_injective _ hζ]
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := r - 1) _ _ ?_) (by omega)
      intro t' ht'
      exact (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp ht'; omega)
  have hc : p.coeff t = c t := by
    simp only [hp, finset_sum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [ht]
  rw [← hc, hp0, coeff_zero]

lemma dual_vanish (hζ : Function.Injective ζ) (hζ0 : ∀ k, ζ k ≠ 0) (μ : Fin n → F)
    (S₀ : Finset (Fin n)) (hsupp : ∀ k, k ∉ S₀ → μ k = 0) (t₀ r : ℕ) (hr : S₀.card ≤ r)
    (h : ∀ a < r, ∑ k, μ k * ζ k ^ (t₀ + a) = 0) : μ = 0 := by
  classical
  funext k₀
  by_cases hk : k₀ ∈ S₀
  · set Lp : F[X] := Lagrange.nodal (S₀.erase k₀) ζ with hLp
    have hdeg : Lp.natDegree < r := by
      rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem hk]
      have := Finset.card_pos.mpr ⟨k₀, hk⟩
      omega
    have key : ∑ a ∈ range r, Lp.coeff a * ∑ k, μ k * ζ k ^ (t₀ + a)
        = μ k₀ * ζ k₀ ^ t₀ * Lp.eval (ζ k₀) := by
      calc ∑ a ∈ range r, Lp.coeff a * ∑ k, μ k * ζ k ^ (t₀ + a)
          = ∑ k, μ k * ζ k ^ t₀ * ∑ a ∈ range r, Lp.coeff a * ζ k ^ a := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
        _ = ∑ k, μ k * ζ k ^ t₀ * Lp.eval (ζ k) := by simp_rw [← eval_eq_sum_range' hdeg]
        _ = μ k₀ * ζ k₀ ^ t₀ * Lp.eval (ζ k₀) := by
            apply Finset.sum_eq_single k₀
            · intro k _ hne
              by_cases hkS : k ∈ S₀
              · rw [Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hne, hkS⟩), mul_zero]
              · rw [hsupp k hkS]; ring
            · intro h; exact absurd (Finset.mem_univ _) h
    have hz : ∑ a ∈ range r, Lp.coeff a * ∑ k, μ k * ζ k ^ (t₀ + a) = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [h a (Finset.mem_range.mp ha), mul_zero]
    rw [hz] at key
    have hne : Lp.eval (ζ k₀) ≠ 0 :=
      Lagrange.eval_nodal_not_at_node fun i hi he => (Finset.mem_erase.mp hi).1 (hζ he).symm
    rcases mul_eq_zero.mp key.symm with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 (pow_ne_zero _ (hζ0 k₀))
    · exact absurd h1 hne
  · exact hsupp k₀ hk

end RejOrder
end Uncertainty

section Module
/-!
# The module-structured matrix

`A ∈ R_q^{K×L}` is modelled as a block matrix whose `(i, j)` block is the matrix of
multiplication by `a i j`. The only property of the ring that is used is that multiplication is
diagonalised by evaluation at `n` distinct nonzero points `ζ k` (the NTT).
-/

open Finset Matrix

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

/-- Multiplication in the ring is diagonalised by evaluation at the points `ζ k`. -/
structure IsNTTMul (ζ : Fin n → ZMod q)
    (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) : Prop where
  inj : Function.Injective ζ
  ne0 : ∀ k, ζ k ≠ 0
  add : ∀ a b, mulmat (a + b) = mulmat a + mulmat b
  mul : ∀ a c k, ∑ s : Fin n, ζ k ^ (s : ℕ) * (mulmat a *ᵥ c) s
      = (∑ s : Fin n, ζ k ^ (s : ℕ) * a s) * ∑ s : Fin n, ζ k ^ (s : ℕ) * c s

/-- The `K·n × L·n` matrix of `a ∈ R_q^{K×L}`. -/
def modMat (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    (a : Fin K → Fin L → Fin n → ZMod q) : Matrix (Fin (K * n)) (Fin (L * n)) (ZMod q) :=
  fun r c => mulmat (a (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm c).1)
    (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm c).2

/-- The `j`-th polynomial of a vector. -/
def blk (y : Fin (L * n) → ZMod q) (j : Fin L) : Fin n → ZMod q :=
  fun t => y (finProdFinEquiv (j, t))

/-- NTT of the `j`-th polynomial of a vector. -/
def ntt (ζ : Fin n → ZMod q) (y : Fin (L * n) → ZMod q) (j : Fin L) (k : Fin n) : ZMod q :=
  ∑ t : Fin n, ζ k ^ (t : ℕ) * blk y j t

lemma sum_blocks {M : Type*} [AddCommMonoid M] (f : Fin (L * n) → M) :
    ∑ c, f c = ∑ j : Fin L, ∑ t : Fin n, f (finProdFinEquiv (j, t)) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]

lemma modMat_mulVec (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    (a : Fin K → Fin L → Fin n → ZMod q) (y : Fin (L * n) → ZMod q) (i : Fin K) (s : Fin n) :
    (modMat mulmat a *ᵥ y) (finProdFinEquiv (i, s)) = ∑ j, (mulmat (a i j) *ᵥ blk y j) s := by
  simp only [Matrix.mulVec, dotProduct, modMat, blk]
  rw [sum_blocks]
  simp only [Equiv.symm_apply_apply]

lemma modMat_add (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    (hadd : ∀ a b, mulmat (a + b) = mulmat a + mulmat b)
    (a b : Fin K → Fin L → Fin n → ZMod q) :
    modMat (K := K) (L := L) mulmat (a + b) = modMat mulmat a + modMat mulmat b := by
  ext r c
  simp only [modMat, Pi.add_apply, hadd, Matrix.add_apply]

/-! ## Dual coordinates of a test vector -/

/-- `Λ̃ i`, defined by `Λ (i, s) = ∑ k, ζ k ^ s * Λ̃ i k`. -/
def dual (ζ : Fin n → ZMod q) (Λ : Fin (K * n) → ZMod q) (i : Fin K) : Fin n → ZMod q :=
  ((Matrix.vandermonde ζ)ᵀ)⁻¹ *ᵥ blk Λ i

lemma vand_det_unit {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) :
    IsUnit (Matrix.vandermonde ζ).det :=
  isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hζ)

lemma dual_spec {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (Λ : Fin (K * n) → ZMod q)
    (i : Fin K) (s : Fin n) :
    ∑ k, ζ k ^ (s : ℕ) * dual ζ Λ i k = Λ (finProdFinEquiv (i, s)) := by
  have hu : IsUnit ((Matrix.vandermonde ζ)ᵀ).det := by
    rw [Matrix.det_transpose]; exact vand_det_unit hζ
  have h := congrFun (Matrix.mulVec_mulVec (blk Λ i) (Matrix.vandermonde ζ)ᵀ
    ((Matrix.vandermonde ζ)ᵀ)⁻¹) s
  rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h
  rw [← show blk Λ i s = Λ (finProdFinEquiv (i, s)) from rfl, ← h]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply, dual]

lemma dual_sub (ζ : Fin n → ZMod q) (Λ Λ' : Fin (K * n) → ZMod q) (i : Fin K) :
    dual ζ (Λ - Λ') i = dual ζ Λ i - dual ζ Λ' i := by
  unfold dual
  rw [← Matrix.mulVec_sub]; rfl

/-- A test vector with vanishing dual coordinates is zero. -/
lemma eq_zero_of_dual {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ)
    (Λ : Fin (K * n) → ZMod q) (h : ∀ i, dual ζ Λ i = 0) : Λ = 0 := by
  funext r
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective r
  rw [← dual_spec hζ Λ i s, h i]; simp

/-! ## An orthogonal test vector forces per-slot conditions -/

lemma pairing {ζ : Fin n → ZMod q} {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    (h : IsNTTMul ζ mulmat) (Λ : Fin (K * n) → ZMod q) (y : Fin (L * n) → ZMod q)
    (a : Fin K → Fin L → Fin n → ZMod q) :
    ∑ r, Λ r * (modMat mulmat a *ᵥ y) r
      = ∑ i, ∑ j, ∑ k, dual ζ Λ i k * (∑ s : Fin n, ζ k ^ (s : ℕ) * a i j s) * ntt ζ y j k := by
  rw [sum_blocks]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ s, Λ (finProdFinEquiv (i, s)) * (modMat mulmat a *ᵥ y) (finProdFinEquiv (i, s))
      = ∑ s : Fin n, ∑ j, ∑ k, dual ζ Λ i k * (ζ k ^ (s : ℕ) * (mulmat (a i j) *ᵥ blk y j) s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [modMat_mulVec, ← dual_spec h.inj Λ i s, Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, ∑ k, dual ζ Λ i k * ∑ s : Fin n, ζ k ^ (s : ℕ) * (mulmat (a i j) *ᵥ blk y j) s := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [h.mul, mul_assoc]; rfl

lemma slot_of_orth {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    (h : IsNTTMul ζ mulmat) (Λ Λ' : Fin (K * n) → ZMod q) (y y' : Fin (L * n) → ZMod q)
    (horth : ∀ a : Fin K → Fin L → Fin n → ZMod q,
      ∑ r, Λ r * (modMat mulmat a *ᵥ y) r + ∑ r, Λ' r * (modMat mulmat a *ᵥ y') r = 0)
    (i : Fin K) (j : Fin L) (k : Fin n) :
    dual ζ Λ i k * ntt ζ y j k + dual ζ Λ' i k * ntt ζ y' j k = 0 := by
  set a₀ : Fin K → Fin L → Fin n → ZMod q := fun i' j' =>
    if i' = i then (if j' = j then (Matrix.vandermonde ζ)⁻¹ *ᵥ Pi.single k 1 else 0) else 0
    with ha₀
  have hc : ∀ i' j' k', ∑ s : Fin n, ζ k' ^ (s : ℕ) * a₀ i' j' s
      = if i' = i then (if j' = j then (if k' = k then 1 else 0) else 0) else 0 := by
    intro i' j' k'
    simp only [ha₀]
    have e : ∀ w : Fin n → ZMod q, ∑ s : Fin n, ζ k' ^ (s : ℕ) * ((Matrix.vandermonde ζ)⁻¹ *ᵥ w) s
        = w k' := by
      intro w
      have hv := congrFun (Matrix.mulVec_mulVec w (Matrix.vandermonde ζ)
        (Matrix.vandermonde ζ)⁻¹) k'
      rw [Matrix.mul_nonsing_inv _ (vand_det_unit h.inj), Matrix.one_mulVec] at hv
      rw [← hv]
      simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    split_ifs with h1 h2 h3
    · rw [e, h3]; simp
    · rw [e]; simp [h3]
    · simp
    · simp
  have := horth a₀
  rw [pairing h, pairing h] at this
  simp only [hc, mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero] at this
  exact this

end RejOrder

end
end Module

section ModuleProb
/-!
# Probability of the per-slot conditions

For `y, y'` uniform on the box, `σ` independent slot conditions on each of the `L` polynomials
hold with probability at most `(2γ₁)^(-L·σ)`. A union bound over one representative per
projective line then bounds the probability of many degenerate slots (`deg_prob`). This is the window argument: once the coefficients
outside a window of the right size are fixed, at most one choice of the window satisfies the
conditions.
-/

open Finset Matrix

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

/-- Reduce an integer vector mod `q`. -/
def zc (y : Fin (L * n) → ℤ) : Fin (L * n) → ZMod q := fun c => (y c : ZMod q)

lemma int_eq_of_cast {γ₁ : ℕ} (hγ : 2 * γ₁ ≤ q) {a b : ℤ}
    (ha : a ∈ Finset.Ioc (-(γ₁ : ℤ)) γ₁) (hb : b ∈ Finset.Ioc (-(γ₁ : ℤ)) γ₁)
    (h : (a : ZMod q) = (b : ZMod q)) : a = b := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mp h
  rw [Finset.mem_Ioc] at ha hb
  have hq : (2 * γ₁ : ℤ) ≤ q := by exact_mod_cast hγ
  have h0 : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  omega

lemma win_inj {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {γ₁ : ℕ} (hγ : 2 * γ₁ ≤ q)
    (r : ℕ) (S : Finset (Fin n)) (hr : r ≤ S.card)
    {y z : Fin (L * n) → ℤ} (hy : y ∈ box γ₁ (L * n)) (hz : z ∈ box γ₁ (L * n))
    (hout : ∀ c, ¬ ((finProdFinEquiv.symm c).2 : ℕ) < r → y c = z c)
    (hntt : ∀ j, ∀ k ∈ S, ntt ζ (zc (q := q) y) j k = ntt ζ (zc z) j k) : y = z := by
  have hrn : r ≤ n := hr.trans (by simpa using Finset.card_le_univ S)
  funext c
  by_cases hc : ((finProdFinEquiv.symm c).2 : ℕ) < r
  · obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective c
    simp only [Equiv.symm_apply_apply] at hc
    set cf : ℕ → ZMod q := fun t' => if h : t' < n then
      (zc y (finProdFinEquiv (j, ⟨t', h⟩)) - zc z (finProdFinEquiv (j, ⟨t', h⟩))) else 0 with hcf
    have hcf_out : ∀ i ∈ range n, i ∉ range r → cf i * 0 = 0 ∧ cf i = 0 := by
      intro i hi hni
      rw [Finset.mem_range] at hi hni
      refine ⟨mul_zero _, ?_⟩
      simp only [hcf, dif_pos hi, zc]
      rw [hout (finProdFinEquiv (j, ⟨i, hi⟩)) (by simpa using hni), sub_self]
    have hw : ∀ k ∈ S, ∑ t' ∈ range r, cf t' * ζ k ^ t' = 0 := by
      intro k hk
      have h1 := hntt j k hk
      unfold ntt blk at h1
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
      rw [Finset.sum_subset (Finset.range_subset_range.mpr hrn)
        (fun i hi hni => by rw [(hcf_out i hi hni).2, zero_mul]),
        ← Fin.sum_univ_eq_sum_range (fun i => cf i * ζ k ^ i) n, ← h1]
      refine Finset.sum_congr rfl fun t' _ => ?_
      simp only [hcf, dif_pos t'.2, Fin.eta]
      ring
    have h0 := window ζ hζ cf r S hr hw t hc
    simp only [hcf, dif_pos t.2, Fin.eta, sub_eq_zero, zc] at h0
    exact int_eq_of_cast hγ (Fintype.mem_piFinset.mp hy _) (Fintype.mem_piFinset.mp hz _) h0
  · exact hout c hc

/-- The box with the first `r` coefficients of every polynomial forced to zero. -/
def maskSet (γ₁ r : ℕ) : Finset (Fin (L * n) → ℤ) :=
  Fintype.piFinset fun c => if ((finProdFinEquiv.symm c).2 : ℕ) < r then ({0} : Finset ℤ)
    else Finset.Ioc (-(γ₁ : ℤ)) γ₁

def mask (r : ℕ) (y : Fin (L * n) → ℤ) : Fin (L * n) → ℤ :=
  fun c => if ((finProdFinEquiv.symm c).2 : ℕ) < r then 0 else y c

lemma mask_mem {γ₁ : ℕ} (r : ℕ) {y : Fin (L * n) → ℤ} (hy : y ∈ box γ₁ (L * n)) :
    mask r y ∈ maskSet (L := L) (n := n) γ₁ r := by
  rw [maskSet, Fintype.mem_piFinset]
  intro c
  unfold mask
  split_ifs
  · simp
  · exact Fintype.mem_piFinset.mp hy c

lemma prod_range_ite (r n b : ℕ) (hr : r ≤ n) :
    ∏ i ∈ range n, (if i < r then 1 else b) = b ^ (n - r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Finset.prod_range_add, Finset.prod_congr rfl (g := fun _ => 1)
    (fun i hi => if_pos (Finset.mem_range.mp hi)), Finset.prod_const_one, one_mul,
    Finset.prod_congr rfl (g := fun _ => b) (fun i _ => if_neg (by omega)), Finset.prod_const,
    Finset.card_range]
  congr 1; omega

lemma card_maskSet (γ₁ r : ℕ) (hr : r ≤ n) :
    (maskSet (L := L) (n := n) γ₁ r).card = (2 * γ₁) ^ (L * (n - r)) := by
  have hI : (Finset.Ioc (-(γ₁ : ℤ)) γ₁).card = 2 * γ₁ := by rw [Int.card_Ioc]; omega
  rw [maskSet, Fintype.card_piFinset]
  simp_rw [apply_ite Finset.card, Finset.card_singleton, hI]
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun i => if i < r then 1 else 2 * γ₁) n, prod_range_ite _ _ _ hr,
    ← pow_mul, Nat.mul_comm (n - r) L]

lemma card_box_nat (γ₁ l : ℕ) : (box γ₁ l).card = (2 * γ₁) ^ l := by
  have hI : (Finset.Ioc (-(γ₁ : ℤ)) γ₁).card = 2 * γ₁ := by rw [Int.card_Ioc]; omega
  rw [box, Fintype.card_piFinset, Finset.prod_const, hI, Finset.card_univ, Fintype.card_fin]

/-- Counting form of the probability bound. -/
lemma slot_count {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {γ₁ : ℕ} (hγ : 2 * γ₁ ≤ q)
    (c c' : Fin n → ZMod q) (S : Finset (Fin n)) (hS : ∀ k ∈ S, c k ≠ 0 ∨ c' k ≠ 0) :
    ((box γ₁ (L * n) ×ˢ box γ₁ (L * n)).filter (fun yy => ∀ j, ∀ k ∈ S,
        c k * ntt ζ (zc (q := q) yy.1) j k + c' k * ntt ζ (zc yy.2) j k = 0)).card
      * (2 * γ₁) ^ (L * S.card) ≤ (2 * γ₁) ^ (2 * (L * n)) := by
  set S₂ := S.filter (fun k => c k = 0) with hS₂
  set S₁ := S.filter (fun k => ¬ c k = 0) with hS₁
  have hcard : S₂.card + S₁.card = S.card := Finset.card_filter_add_card_filter_not _
  have h1n : S₁.card ≤ n := by simpa using Finset.card_le_univ S₁
  have h2n : S₂.card ≤ n := by simpa using Finset.card_le_univ S₂
  set sol := (box γ₁ (L * n) ×ˢ box γ₁ (L * n)).filter (fun yy => ∀ j, ∀ k ∈ S,
        c k * ntt ζ (zc (q := q) yy.1) j k + c' k * ntt ζ (zc yy.2) j k = 0) with hsol
  have hle : sol.card ≤ (maskSet (L := L) (n := n) γ₁ S₁.card ×ˢ
      maskSet (L := L) (n := n) γ₁ S₂.card).card := by
    apply Finset.card_le_card_of_injOn (fun yy => (mask S₁.card yy.1, mask S₂.card yy.2))
    · intro yy hyy
      have hb := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hyy)).1
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨mask_mem _ hb.1, mask_mem _ hb.2⟩)
    · intro yy hyy zz hzz he
      have hy := Finset.mem_filter.mp (Finset.mem_coe.mp hyy)
      have hz := Finset.mem_filter.mp (Finset.mem_coe.mp hzz)
      have hyb := Finset.mem_product.mp hy.1
      have hzb := Finset.mem_product.mp hz.1
      simp only [Prod.mk.injEq] at he
      have hout : ∀ (r : ℕ) (y z : Fin (L * n) → ℤ), mask r y = mask r z →
          ∀ c, ¬ ((finProdFinEquiv.symm c).2 : ℕ) < r → y c = z c := by
        intro r y z hm c hc
        have := congrFun hm c
        simpa only [mask, if_neg hc] using this
      have e2 : yy.2 = zz.2 := by
        refine win_inj hζ hγ S₂.card S₂ le_rfl hyb.2 hzb.2 (hout _ _ _ he.2) ?_
        intro j k hk
        have hkS := (Finset.mem_filter.mp hk).1
        have hck : c k = 0 := (Finset.mem_filter.mp hk).2
        have hck' : c' k ≠ 0 := (hS k hkS).resolve_left (not_not.mpr hck)
        have a1 := hy.2 j k hkS
        have a2 := hz.2 j k hkS
        rw [hck, zero_mul, zero_add] at a1 a2
        rw [(mul_eq_zero.mp a1).resolve_left hck', (mul_eq_zero.mp a2).resolve_left hck']
      have e1 : yy.1 = zz.1 := by
        refine win_inj hζ hγ S₁.card S₁ le_rfl hyb.1 hzb.1 (hout _ _ _ he.1) ?_
        intro j k hk
        have hkS := (Finset.mem_filter.mp hk).1
        have hck : c k ≠ 0 := (Finset.mem_filter.mp hk).2
        have a1 := hy.2 j k hkS
        have a2 := hz.2 j k hkS
        rw [e2] at a1
        exact mul_left_cancel₀ hck (add_right_cancel (a1.trans a2.symm))
      exact Prod.ext e1 e2
  rw [Finset.card_product, card_maskSet _ _ h1n, card_maskSet _ _ h2n] at hle
  calc sol.card * (2 * γ₁) ^ (L * S.card)
      ≤ ((2 * γ₁) ^ (L * (n - S₁.card)) * (2 * γ₁) ^ (L * (n - S₂.card)))
          * (2 * γ₁) ^ (L * S.card) := Nat.mul_le_mul_right _ hle
    _ = (2 * γ₁) ^ (2 * (L * n)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have a1 : L * (n - S₁.card) + L * S₁.card = L * n := by
          rw [← Nat.mul_add, Nat.sub_add_cancel h1n]
        have a2 : L * (n - S₂.card) + L * S₂.card = L * n := by
          rw [← Nat.mul_add, Nat.sub_add_cancel h2n]
        rw [← hcard, Nat.mul_add]
        omega

/-- For `y, y'` uniform on the box, `|S|` slot conditions on each polynomial hold with
probability at most `(2γ₁)^(-L·|S|)`. -/
lemma slot_prob {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {γ₁ : ℕ} (hγ1 : 0 < γ₁)
    (hγ : 2 * γ₁ ≤ q) (c c' : Fin n → ZMod q) (S : Finset (Fin n))
    (hS : ∀ k ∈ S, c k ≠ 0 ∨ c' k ≠ 0) :
    prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n)) (fun yy => ∀ j, ∀ k ∈ S,
        c k * ntt ζ (zc (q := q) yy.1) j k + c' k * ntt ζ (zc yy.2) j k = 0)
      ≤ 1 / ((2 * γ₁ : ℚ)) ^ (L * S.card) := by
  have h := slot_count (L := L) hζ hγ c c' S hS
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  unfold prob
  rw [Finset.card_product, card_box_nat, div_le_div_iff₀ (by push_cast; positivity) (by positivity),
    one_mul]
  have h' : ((_ * (2 * γ₁) ^ (L * S.card) : ℕ) : ℚ) ≤ (((2 * γ₁) ^ (2 * (L * n)) : ℕ) : ℚ) :=
    Nat.cast_le.mpr h
  push_cast at h' ⊢
  rw [← pow_add, ← two_mul]
  exact h'

/-! ## Degenerate slots -/

/-- Union bound. -/
lemma prob_le_sum {α ι : Type*} (B : Finset α) (I : Finset ι) (P : α → Prop) (Q : ι → α → Prop)
    [DecidablePred P] [∀ i, DecidablePred (Q i)] (h : ∀ y ∈ B, P y → ∃ i ∈ I, Q i y) : prob B P ≤ ∑ i ∈ I, prob B (Q i) := by
  unfold prob
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : B.filter P ⊆ I.biUnion fun i => B.filter (Q i) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨i, hi, hq⟩ := h y hy.1 hy.2
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hy.1, hq⟩⟩
  exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- Slots where the NTT vectors of `y` and `y'` are linearly dependent: some nonzero `(c, c')`
annihilates `(ŷ_j(k), ŷ'_j(k))` for every polynomial `j`. -/
def degS (ζ : Fin n → ZMod q) (y y' : Fin (L * n) → ℤ) : Finset (Fin n) :=
  univ.filter fun k => ∃ c c' : ZMod q, (c ≠ 0 ∨ c' ≠ 0) ∧
    ∀ j, c * ntt ζ (zc (q := q) y) j k + c' * ntt ζ (zc y') j k = 0

/-- One representative `(c, c')` per projective line: `(0, 1)` and `(1, x)`. -/
def rep : Option (ZMod q) → ZMod q × ZMod q
  | none => (0, 1)
  | some x => (1, x)

lemma rep_ne (o : Option (ZMod q)) : (rep o).1 ≠ 0 ∨ (rep o).2 ≠ 0 := by
  cases o
  · exact Or.inr one_ne_zero
  · exact Or.inl one_ne_zero

lemma rep_spec {c c' : ZMod q} (hc : c ≠ 0 ∨ c' ≠ 0) {a b : Fin L → ZMod q}
    (h : ∀ j, c * a j + c' * b j = 0) : ∃ o, ∀ j, (rep o).1 * a j + (rep o).2 * b j = 0 := by
  by_cases c0 : c = 0
  · refine ⟨none, fun j => ?_⟩
    have hj := h j
    rw [c0, zero_mul, zero_add] at hj
    simp only [rep, zero_mul, one_mul, zero_add]
    exact (mul_eq_zero.mp hj).resolve_left (hc.resolve_left (not_not.mpr c0))
  · refine ⟨some (c' / c), fun j => ?_⟩
    have hj := h j
    simp only [rep, one_mul]
    have e : a j = c⁻¹ * (c * a j) := by rw [← mul_assoc, inv_mul_cancel₀ c0, one_mul]
    rw [e, eq_neg_of_add_eq_zero_left hj]
    ring

/-- Slot conditions on `S₀`, and at least `r` further degenerate slots, hold with probability at
most `C(n - |S₀|, r) · (q + 1)^r · (2γ₁)^(-L·(|S₀| + r))`: a union bound over the `r` slots and
over one representative per projective line at each of them. -/
lemma deg_prob {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {γ₁ : ℕ} (hγ1 : 0 < γ₁)
    (hγ : 2 * γ₁ ≤ q) (c₀ c₀' : Fin n → ZMod q) (S₀ : Finset (Fin n))
    (hS₀ : ∀ k ∈ S₀, c₀ k ≠ 0 ∨ c₀' k ≠ 0) (r : ℕ) :
    prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n)) (fun yy =>
        (∀ j, ∀ k ∈ S₀, c₀ k * ntt ζ (zc (q := q) yy.1) j k + c₀' k * ntt ζ (zc yy.2) j k = 0)
        ∧ r ≤ (degS ζ yy.1 yy.2 \ S₀).card)
      ≤ ((n - S₀.card).choose r * ((q : ℚ) + 1) ^ r : ℚ) / (2 * γ₁ : ℚ) ^ (L * (S₀.card + r)) := by
  set BB := box γ₁ (L * n) ×ˢ box γ₁ (L * n) with hBB
  set 𝒰 := Finset.powersetCard r (univ \ S₀) with h𝒰
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  -- the coefficients for a set `U` of extra slots and a choice of line at each
  set cU : (U : Finset (Fin n)) → (U → Option (ZMod q)) → Fin n → ZMod q := fun U φ k =>
    if k ∈ S₀ then c₀ k else if h : k ∈ U then (rep (φ ⟨k, h⟩)).1 else 0 with hcU
  set cU' : (U : Finset (Fin n)) → (U → Option (ZMod q)) → Fin n → ZMod q := fun U φ k =>
    if k ∈ S₀ then c₀' k else if h : k ∈ U then (rep (φ ⟨k, h⟩)).2 else 0 with hcU'
  have step1 : prob BB (fun yy =>
        (∀ j, ∀ k ∈ S₀, c₀ k * ntt ζ (zc (q := q) yy.1) j k + c₀' k * ntt ζ (zc yy.2) j k = 0)
        ∧ r ≤ (degS ζ yy.1 yy.2 \ S₀).card)
      ≤ ∑ U ∈ 𝒰, ∑ φ : U → Option (ZMod q), prob BB (fun yy => ∀ j, ∀ k ∈ S₀ ∪ U,
          cU U φ k * ntt ζ (zc (q := q) yy.1) j k + cU' U φ k * ntt ζ (zc yy.2) j k = 0) := by
    refine (prob_le_sum BB 𝒰 _ (fun U yy =>
        (∀ j, ∀ k ∈ S₀, c₀ k * ntt ζ (zc (q := q) yy.1) j k + c₀' k * ntt ζ (zc yy.2) j k = 0)
        ∧ ∀ k ∈ U, k ∈ degS ζ yy.1 yy.2) ?_).trans (Finset.sum_le_sum fun U hU => ?_)
    · rintro yy - ⟨h0, hr⟩
      obtain ⟨U, hUsub, hUc⟩ := Finset.exists_subset_card_eq hr
      refine ⟨U, Finset.mem_powersetCard.mpr ⟨fun k hk => ?_, hUc⟩, h0,
        fun k hk => (Finset.mem_sdiff.mp (hUsub hk)).1⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp (hUsub hk)).2⟩
    · refine prob_le_sum BB _ _ _ ?_
      rintro yy - ⟨h0, hd⟩
      have hex : ∀ k : U, ∃ o : Option (ZMod q), ∀ j,
          (rep o).1 * ntt ζ (zc (q := q) yy.1) j k + (rep o).2 * ntt ζ (zc yy.2) j k = 0 := by
        intro k
        obtain ⟨c, c', hc, hcc⟩ := (Finset.mem_filter.mp (hd k k.2)).2
        exact rep_spec hc hcc
      choose φ hφ using hex
      refine ⟨φ, Finset.mem_univ _, fun j k hk => ?_⟩
      by_cases hk0 : k ∈ S₀
      · simp only [hcU, hcU', if_pos hk0]
        exact h0 j k hk0
      · have hkU : k ∈ U := (Finset.mem_union.mp hk).resolve_left hk0
        simp only [hcU, hcU', if_neg hk0, dif_pos hkU]
        exact hφ ⟨k, hkU⟩ j
  refine step1.trans ?_
  have step2 : ∀ U ∈ 𝒰, ∀ φ : U → Option (ZMod q), prob BB (fun yy => ∀ j, ∀ k ∈ S₀ ∪ U,
      cU U φ k * ntt ζ (zc (q := q) yy.1) j k + cU' U φ k * ntt ζ (zc yy.2) j k = 0)
      ≤ 1 / (2 * γ₁ : ℚ) ^ (L * (S₀.card + r)) := by
    intro U hU φ
    have hU' := Finset.mem_powersetCard.mp hU
    have hdisj : Disjoint S₀ U := by
      rw [Finset.disjoint_left]
      intro k hk hkU
      exact (Finset.mem_sdiff.mp (hU'.1 hkU)).2 hk
    have hc : (S₀ ∪ U).card = S₀.card + r := by
      rw [Finset.card_union_of_disjoint hdisj, hU'.2]
    rw [← hc]
    refine slot_prob hζ hγ1 hγ (cU U φ) (cU' U φ) (S₀ ∪ U) fun k hk => ?_
    by_cases hk0 : k ∈ S₀
    · simp only [hcU, hcU', if_pos hk0]; exact hS₀ k hk0
    · have hkU : k ∈ U := (Finset.mem_union.mp hk).resolve_left hk0
      simp only [hcU, hcU', if_neg hk0, dif_pos hkU]
      exact rep_ne _
  refine (Finset.sum_le_sum fun U hU => Finset.sum_le_sum fun φ _ => step2 U hU φ).trans
    (le_of_eq ?_)
  have hcardφ : ∀ U ∈ 𝒰, (Fintype.card (U → Option (ZMod q)) : ℚ) = ((q : ℚ) + 1) ^ r := by
    intro U hU
    rw [Fintype.card_fun, Fintype.card_option, ZMod.card, Fintype.card_coe,
      (Finset.mem_powersetCard.mp hU).2]
    push_cast; ring
  rw [Finset.sum_congr rfl fun U hU => by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardφ U hU]]
  rw [Finset.sum_const, nsmul_eq_mul, h𝒰, Finset.card_powersetCard, Finset.card_univ_sdiff,
    Fintype.card_fin]
  ring

end RejOrder

end
end ModuleProb

section ModuleCount
/-!
# Test vectors on a coordinate set, and degenerate slots of independent nonces

Test vectors supported on a coordinate set `T` (`ext`, `rowT`, `suppIn1`), and the probability
that two independent uniform nonces have `d` given degenerate slots (`deg_card_prob`).
-/

open Finset Matrix

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

lemma prob_mono {α : Type*} (B : Finset α) {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ y ∈ B, P y → Q y) : prob B P ≤ prob B Q := by
  unfold prob
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun y hy => by
    rw [Finset.mem_filter] at hy ⊢; exact ⟨hy.1, h y hy.1 hy.2⟩

/-! ## Extending a function on `T` by zero -/

/-- Extend by zero. -/
def ext (T : Finset (Fin (K * n))) (g : T → ZMod q) : Fin (K * n) → ZMod q :=
  fun r => if h : r ∈ T then g ⟨r, h⟩ else 0

lemma ext_out (T : Finset (Fin (K * n))) (g : T → ZMod q) {r : Fin (K * n)} (hr : r ∉ T) :
    ext T g r = 0 := by simp [ext, hr]

lemma ext_coe (T : Finset (Fin (K * n))) (g : T → ZMod q) (r : T) : ext T g r = g r := by
  simp [ext, r.2]

lemma ext_sub (T : Finset (Fin (K * n))) (g g' : T → ZMod q) :
    ext T (g - g') = ext T g - ext T g' := by
  funext r; simp only [ext, Pi.sub_apply]; split_ifs <;> simp

/-- The two halves of a test vector. -/
def lam (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) : Fin (K * n) → ZMod q :=
  ext T fun r => ℓ (Sum.inl r)

def lam' (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) : Fin (K * n) → ZMod q :=
  ext T fun r => ℓ (Sum.inr r)

/-! ## Joint support and the per-vector probability bound -/

/-- NTT slots where some dual coordinate of the test vector is nonzero. -/
def jsupp (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) :
    Finset (Fin n) :=
  univ.filter fun k => ∃ i, dual ζ (lam T ℓ) i k ≠ 0 ∨ dual ζ (lam' T ℓ) i k ≠ 0

/-- At least `σ*` degenerate slots occur with probability at most
`C(n, σ*) · (q + 1)^σ* · (2γ₁)^(-L·σ*)`. -/
lemma deg_card_prob {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) {γ₁ : ℕ} (hγ1 : 0 < γ₁)
    (hγ : 2 * γ₁ ≤ q) (σs : ℕ) :
    prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n)) (fun yy => σs ≤ (degS ζ yy.1 yy.2).card)
      ≤ (n.choose σs * ((q : ℚ) + 1) ^ σs : ℚ) / (2 * γ₁ : ℚ) ^ (L * σs) := by
  have := deg_prob (L := L) hζ hγ1 hγ 0 0 ∅ (fun k hk => absurd hk (Finset.notMem_empty k)) σs
  simp only [Finset.card_empty, Nat.sub_zero, zero_add, Finset.sdiff_empty] at this
  refine le_trans (prob_mono _ fun yy _ hy => ⟨fun j k hk => absurd hk (Finset.notMem_empty k),
    hy⟩) this

/-! ## Counting -/

/-- The coefficient positions of row `i` that lie in `T`. -/
def rowT (T : Finset (Fin (K * n))) (i : Fin K) : Finset (Fin n) :=
  univ.filter fun s => finProdFinEquiv (i, s) ∈ T

/-! ## Test vectors on one side -/

/-- Test vectors `(κ, 0)` whose support lies in `S`. -/
def suppIn1 (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    Finset (T → ZMod q) :=
  univ.filter fun κ => jsupp ζ T (Sum.elim κ 0) ⊆ S

end RejOrder

end
end ModuleCount

section Profile
/-!
# Rows of a coordinate set
-/

open Finset Matrix

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

lemma sum_rowT (T : Finset (Fin (K * n))) : ∑ i, (rowT T i).card = T.card := by
  have h1 : T.card = ∑ c : Fin (K * n), if c ∈ T then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]; simp
  rw [h1, sum_blocks]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowT, Finset.card_filter]

end RejOrder

end
end Profile

section Negacyclic
/-!
# The ring `Z_q[X]/(X^n + 1)`

Multiplication by `a` as a matrix, and the proof that it is diagonalised by evaluation at the
roots of `X^n + 1`. For ML-DSA, `q = 8380417`, `n = 256`, and the roots are the odd powers of
`1753`.
-/

open Finset Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n : ℕ} [NeZero n]

/-- Matrix of multiplication by `a` in `R[X]/(X^n + 1)`, over any ring `R`: column `t` holds the
coefficients of `a · X^t`. Used over `ℤ_q`, and over `ℤ` and `ℚ` in `Bathwater.lean`. -/
def negacyclic {R : Type*} [Ring R] {n : ℕ} (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun s t => if t ≤ s then a (s - t) else -a (s - t)

lemma negacyclic_col {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (ζ : R) (hζ : ζ ^ n = -1)
    (a : Fin n → R) (t : Fin n) :
    ∑ s : Fin n, ζ ^ (s : ℕ) * negacyclic a s t = ∑ u : Fin n, a u * ζ ^ ((u : ℕ) + (t : ℕ)) := by
  rw [← Equiv.sum_comp (Equiv.addRight t)]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Equiv.coe_addRight, negacyclic, add_sub_cancel_right]
  have hval : ((u + t : Fin n) : ℕ) = ((u : ℕ) + (t : ℕ)) % n := Fin.val_add u t
  by_cases hlt : (u : ℕ) + (t : ℕ) < n
  · have hle : t ≤ u + t := by
      rw [Fin.le_def, hval, Nat.mod_eq_of_lt hlt]; omega
    rw [if_pos hle, hval, Nat.mod_eq_of_lt hlt, mul_comm]
  · have hu := u.2
    have ht := t.2
    have hmod : ((u : ℕ) + (t : ℕ)) % n = (u : ℕ) + (t : ℕ) - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hle : ¬ t ≤ u + t := by
      rw [Fin.le_def, hval, hmod]; omega
    rw [if_neg hle, hval, hmod]
    have : ζ ^ ((u : ℕ) + (t : ℕ)) = ζ ^ ((u : ℕ) + (t : ℕ) - n) * ζ ^ n := by
      rw [← pow_add]; congr 1; omega
    rw [this, hζ]; ring

/-- `Z_q[X]/(X^n + 1)` with `n` distinct roots of `X^n + 1` satisfies the NTT interface. -/
theorem isNTTMul_negacyclic (ζ : Fin n → ZMod q) (hinj : Function.Injective ζ)
    (hroot : ∀ k, ζ k ^ n = -1) : IsNTTMul ζ (negacyclic (R := ZMod q) (n := n)) where
  inj := hinj
  ne0 k := by
    intro h0
    have := hroot k
    rw [h0, zero_pow (NeZero.ne n)] at this
    have h1 : (1 : ZMod q) = 0 := by linear_combination this
    exact one_ne_zero h1
  add a b := by
    ext s t
    simp only [negacyclic, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> ring
  mul a c k := by
    calc ∑ s : Fin n, ζ k ^ (s : ℕ) * (negacyclic a *ᵥ c) s
        = ∑ t : Fin n, c t * ∑ s : Fin n, ζ k ^ (s : ℕ) * negacyclic a s t := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
      _ = ∑ t : Fin n, c t * ∑ u : Fin n, a u * ζ k ^ ((u : ℕ) + (t : ℕ)) := by
          simp_rw [negacyclic_col (ζ k) (hroot k)]
      _ = _ := by
          rw [Finset.sum_mul_sum, Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring

/-! ## ML-DSA: `q = 8380417`, `n = 256` -/

instance : Fact (Nat.Prime 8380417) := ⟨by norm_num⟩

/-- The roots of `X^256 + 1` mod `q`: the odd powers of `1753`. -/
def zetaMLDSA (k : Fin 256) : ZMod 8380417 := (1753 : ZMod 8380417) ^ (2 * (k : ℕ) + 1)

lemma sq_step (a b : ℕ) (h : a * a % 8380417 = b % 8380417) :
    ((a : ℕ) : ZMod 8380417) ^ 2 = ((b : ℕ) : ZMod 8380417) := by
  rw [sq, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']; exact h

lemma pow_1753 : (1753 : ZMod 8380417) ^ 256 = -1 := by
  have h0 : (1753 : ZMod 8380417) = ((1753 : ℕ) : ZMod 8380417) := by norm_cast
  have e : (256 : ℕ) = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 := by norm_num
  rw [h0, e]
  simp only [pow_mul]
  rw [sq_step 1753 3073009 (by norm_num), sq_step 3073009 3602218 (by norm_num), sq_step 3602218 5010068 (by norm_num), sq_step 5010068 7778734 (by norm_num), sq_step 7778734 5178923 (by norm_num), sq_step 5178923 3765607 (by norm_num), sq_step 3765607 4808194 (by norm_num), sq_step 4808194 8380416 (by norm_num)]
  rw [eq_neg_iff_add_eq_zero]
  have : ((8380417 : ℕ) : ZMod 8380417) = 0 := ZMod.natCast_self _
  exact_mod_cast this

lemma zetaMLDSA_root (k : Fin 256) : zetaMLDSA k ^ 256 = -1 := by
  unfold zetaMLDSA
  rw [← pow_mul, mul_comm, pow_mul, pow_1753]
  exact Odd.neg_one_pow ⟨k, rfl⟩

lemma zetaMLDSA_inj : Function.Injective zetaMLDSA := by
  have hne : (-1 : ZMod 8380417) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod 8380417) = 0 := by
      have : (2 : ZMod 8380417) = 0 := by linear_combination -h
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    omega
  have hord : orderOf (1753 : ZMod 8380417) = 2 ^ (8 + 1) := by
    apply orderOf_eq_prime_pow
    · rw [show (2 : ℕ) ^ 8 = 256 by norm_num, pow_1753]; exact hne
    · rw [show (2 : ℕ) ^ (8 + 1) = 256 * 2 by norm_num, pow_mul, pow_1753]; norm_num
  intro k k' h
  have hinj := pow_injOn_Iio_orderOf (x := (1753 : ZMod 8380417))
  rw [hord] at hinj
  have hk := k.2
  have hk' := k'.2
  have := hinj (by simp only [Set.mem_Iio]; omega : 2 * (k : ℕ) + 1 ∈ Set.Iio (2 ^ (8 + 1)))
    (by simp only [Set.mem_Iio]; omega : 2 * (k' : ℕ) + 1 ∈ Set.Iio (2 ^ (8 + 1))) h
  exact Fin.ext (by omega)

/-- The ML-DSA ring satisfies the NTT interface. -/
theorem isNTTMul_mldsa : IsNTTMul zetaMLDSA (negacyclic (R := ZMod 8380417) (n := 256)) :=
  isNTTMul_negacyclic zetaMLDSA zetaMLDSA_inj zetaMLDSA_root

end RejOrder

end
end Negacyclic

section RingForm
/-!
# The ring `R_q = ℤ_q[X]/(X^256 + 1)`

Mathlib's `AdjoinRoot (X^256 + 1)` over `ℤ_q`, its coefficients, and the bridge to the
negacyclic matrices used above: a product in `R_q` has the coefficients of the negacyclic matrix
product (`coeffs_mul`, by evaluating at the 256 roots of `X^256 + 1`), `ringMat A` is the matrix
of `y ↦ A · y` on coefficient vectors (`ringMat_mulVec`), and averaging over `A ∈ R_q^{K×L}` is
averaging over its coefficients (`avg_matrix`, `avg_ringMat`). The headlines are stated over
`R_q` with these.
-/

open Finset Polynomial Matrix

noncomputable section

set_option maxRecDepth 10000

namespace RejOrder

/-- `X^256 + 1` over `ℤ_q`, `q = 8380417`. -/
noncomputable abbrev polyR : (ZMod 8380417)[X] := X ^ 256 + 1

lemma polyR_monic : polyR.Monic := by
  simpa using monic_X_pow_add_C (1 : ZMod 8380417) (n := 256) (by norm_num)

lemma polyR_natDegree : polyR.natDegree = 256 := by
  simpa only [map_one] using natDegree_X_pow_add_C (n := 256) (r := (1 : ZMod 8380417))

lemma polyR_ne_one : polyR ≠ 1 := fun h => by
  have := polyR_natDegree; rw [h, natDegree_one] at this; norm_num at this

/-- **The ring** `R_q = ℤ_q[X]/(X^256 + 1)` of ML-DSA (Mathlib's `AdjoinRoot`). -/
abbrev Rq := AdjoinRoot polyR

/-- Coefficient `s` of `w ∈ R_q`: that of its representative of degree `< 256`. -/
noncomputable def coeffs (w : Rq) (s : Fin 256) : ZMod 8380417 :=
  (AdjoinRoot.modByMonicHom polyR_monic w).coeff s

/-- The element `∑ a_s X^s` of `R_q`. -/
noncomputable def ofCoeffs (a : Fin 256 → ZMod 8380417) : Rq :=
  AdjoinRoot.mk polyR (∑ s : Fin 256, C (a s) * X ^ (s : ℕ))

/-- The element `∑ y_s X^s` of `R_q`, for integer `y`. -/
noncomputable def ofInt (y : Fin 256 → ℤ) : Rq := ofCoeffs fun s => (y s : ZMod 8380417)

lemma coeffs_ofCoeffs (a : Fin 256 → ZMod 8380417) : coeffs (ofCoeffs a) = a := by
  funext s
  have hdeg : (∑ s : Fin 256, C (a s) * X ^ (s : ℕ)).degree < polyR.degree := by
    rw [degree_eq_natDegree polyR_monic.ne_zero, polyR_natDegree]
    exact degree_sum_fin_lt a
  simp only [coeffs, ofCoeffs, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff polyR_monic).mpr hdeg, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single s (fun b _ hb => if_neg (fun h => hb (Fin.ext h).symm))
    (fun h => absurd (mem_univ s) h), if_pos rfl]

lemma natDegree_rep (w : Rq) : (AdjoinRoot.modByMonicHom polyR_monic w).natDegree < 256 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective w
  rw [AdjoinRoot.modByMonicHom_mk, ← polyR_natDegree]
  exact natDegree_modByMonic_lt _ polyR_monic polyR_ne_one

lemma ofCoeffs_coeffs (w : Rq) : ofCoeffs (coeffs w) = w := by
  have h := as_sum_range' _ 256 (natDegree_rep w)
  rw [Finset.sum_range (fun i => monomial i ((AdjoinRoot.modByMonicHom polyR_monic w).coeff i))] at h
  simp only [← C_mul_X_pow_eq_monomial] at h
  conv_rhs => rw [← AdjoinRoot.mk_leftInverse polyR_monic w, h]
  rfl

/-- Coefficients identify `R_q` with `ℤ_q^256`. -/
noncomputable def coeffsEquiv : Rq ≃ (Fin 256 → ZMod 8380417) where
  toFun := coeffs
  invFun := ofCoeffs
  left_inv := ofCoeffs_coeffs
  right_inv := coeffs_ofCoeffs

noncomputable instance : Fintype Rq := Fintype.ofEquiv _ coeffsEquiv.symm

lemma coeffs_sum {ι : Type*} (S : Finset ι) (f : ι → Rq) (s : Fin 256) :
    coeffs (∑ j ∈ S, f j) s = ∑ j ∈ S, coeffs (f j) s := by
  simp only [coeffs, map_sum, finsetSum_coeff]

/-! ## Multiplication is negacyclic convolution -/

/-- Evaluation at the `k`-th root of `X^256 + 1`. -/
noncomputable def ev (k : Fin 256) : Rq →+* ZMod 8380417 :=
  AdjoinRoot.lift (RingHom.id _) (zetaMLDSA k) (by simp [zetaMLDSA_root])

lemma ev_ofCoeffs (k : Fin 256) (a : Fin 256 → ZMod 8380417) :
    ev k (ofCoeffs a) = ∑ s : Fin 256, zetaMLDSA k ^ (s : ℕ) * a s := by
  simp only [ev, ofCoeffs, AdjoinRoot.lift_mk, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X_pow,
    RingHom.id_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma eq_of_ntt {u u' : Fin 256 → ZMod 8380417}
    (h : ∀ k, ∑ s : Fin 256, zetaMLDSA k ^ (s : ℕ) * u s
      = ∑ s : Fin 256, zetaMLDSA k ^ (s : ℕ) * u' s) : u = u' := by
  rw [← sub_eq_zero]
  refine Matrix.eq_zero_of_mulVec_eq_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr zetaMLDSA_inj) (funext fun k => ?_)
  simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, h k, sub_self, Pi.zero_apply]

/-- Coefficients of a product in `R_q` are given by the negacyclic matrix. -/
lemma coeffs_mul (a c : Fin 256 → ZMod 8380417) :
    coeffs (ofCoeffs a * ofCoeffs c) = negacyclic a *ᵥ c := by
  refine eq_of_ntt fun k => ?_
  rw [isNTTMul_mldsa.mul, ← ev_ofCoeffs, ← ev_ofCoeffs, ← ev_ofCoeffs, ofCoeffs_coeffs, map_mul]

/-- `A · y` in `R_q^K`, coefficient by coefficient, is the flattened `modMat` product. -/
lemma modMat_mulVec_eq {K L : ℕ} (a : Fin K → Fin L → Fin 256 → ZMod 8380417)
    (y : Fin (L * 256) → ZMod 8380417) (i : Fin K) (s : Fin 256) :
    (modMat negacyclic a *ᵥ y) (finProdFinEquiv (i, s))
      = coeffs (((Matrix.of fun i j => ofCoeffs (a i j)) *ᵥ fun j => ofCoeffs (blk y j)) i) s := by
  rw [modMat_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, coeffs_sum, coeffs_mul]

/-- Averaging over `A ∈ R_q^{K×L}` is averaging over its coefficients. -/
lemma avg_matrix {K L : ℕ} (F : Matrix (Fin K) (Fin L) Rq → ℚ) :
    avg F = avg (fun a : Fin K → Fin L → Fin 256 → ZMod 8380417 =>
      F (Matrix.of fun i j => ofCoeffs (a i j))) := by
  let e : (Fin K → Fin L → Fin 256 → ZMod 8380417) ≃ Matrix (Fin K) (Fin L) Rq :=
    (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => coeffsEquiv.symm).trans
      Matrix.of
  unfold avg
  rw [Fintype.card_congr e, ← Equiv.sum_comp e]
  rfl

/-- The matrix over `ℤ_q` of `y ↦ A · y` on coefficient vectors: entry `((i, s), (j, t))` is
coefficient `s` of `A_ij · X^t` (`ringMat_mulVec`). -/
noncomputable def ringMat {K L : ℕ} (A : Matrix (Fin K) (Fin L) Rq) :
    Matrix (Fin (K * 256)) (Fin (L * 256)) (ZMod 8380417) :=
  fun r c => coeffs (A (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm c).1
    * AdjoinRoot.root polyR ^ ((finProdFinEquiv.symm c).2 : ℕ)) (finProdFinEquiv.symm r).2

lemma ofCoeffs_single (t : Fin 256) :
    ofCoeffs (Pi.single t 1) = AdjoinRoot.root polyR ^ (t : ℕ) := by
  rw [ofCoeffs, Finset.sum_eq_single t (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp [AdjoinRoot.mk_X]

lemma ringMat_of {K L : ℕ} (a : Fin K → Fin L → Fin 256 → ZMod 8380417) :
    ringMat (Matrix.of fun i j => ofCoeffs (a i j)) = modMat negacyclic a := by
  ext r c
  simp only [ringMat, modMat, Matrix.of_apply, ← ofCoeffs_single, coeffs_mul,
    Matrix.mulVec_single_one]
  rfl

/-- `ringMat A` computes `A · y`: entry `(i, s)` of `ringMat A · y` is coefficient `s` of
`(A · y)_i`, where `y_j ∈ R_q` has the coefficients of block `j`. -/
lemma ringMat_mulVec {K L : ℕ} (A : Matrix (Fin K) (Fin L) Rq)
    (y : Fin (L * 256) → ZMod 8380417) (i : Fin K) (s : Fin 256) :
    (ringMat A *ᵥ y) (finProdFinEquiv (i, s))
      = coeffs ((A *ᵥ fun j => ofCoeffs (blk y j)) i) s := by
  have hA : A = Matrix.of fun i j => ofCoeffs (coeffs (A i j)) := by
    ext i j; simp [ofCoeffs_coeffs]
  conv_lhs => rw [hA]
  rw [ringMat_of, modMat_mulVec_eq, ← hA]

/-- Averaging over `A ∈ R_q^{K×L}` through `ringMat` is averaging over the coefficient form. -/
lemma avg_ringMat {K L : ℕ} (F : Matrix (Fin (K * 256)) (Fin (L * 256)) (ZMod 8380417) → ℚ) :
    avg (fun A : Matrix (Fin K) (Fin L) Rq => F (ringMat A))
      = avg (fun a : Fin K → Fin L → Fin 256 → ZMod 8380417 => F (modMat negacyclic a)) := by
  rw [avg_matrix]; simp only [ringMat_of]

/-- The coefficient arrays of a matrix over `R_q`. -/
noncomputable def coeffsOf {K L : ℕ} (A : Matrix (Fin K) (Fin L) Rq) :
    Fin K → Fin L → Fin 256 → ZMod 8380417 := fun i j => coeffs (A i j)

/-- The coefficient form of `A` gives the same matrix as `ringMat A`. -/
lemma modMat_coeffsOf {K L : ℕ} (A : Matrix (Fin K) (Fin L) Rq) :
    modMat negacyclic (coeffsOf A) = ringMat A := by
  rw [← ringMat_of]
  congr 1
  ext i j
  simp [coeffsOf, ofCoeffs_coeffs]

/-- A fraction of matrices over `R_q` is the same fraction of coefficient arrays. -/
lemma frac_ring {K L : ℕ} (P : (Fin K → Fin L → Fin 256 → ZMod 8380417) → Prop)
    [DecidablePred P] :
    ((univ.filter fun A : Matrix (Fin K) (Fin L) Rq => P (coeffsOf A)).card : ℚ)
        / Fintype.card (Matrix (Fin K) (Fin L) Rq)
      = ((univ.filter P).card : ℚ) / Fintype.card (Fin K → Fin L → Fin 256 → ZMod 8380417) := by
  let e : Matrix (Fin K) (Fin L) Rq ≃ (Fin K → Fin L → Fin 256 → ZMod 8380417) :=
    Matrix.of.symm.trans (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => coeffsEquiv)
  have he : ∀ A, e A = coeffsOf A := fun A => rfl
  rw [Fintype.card_congr e, Finset.card_equiv e (t := univ.filter P) (fun A => by simp [he])]

end RejOrder

end
end RingForm

section Numeric
/-!
# Binomial coefficients for kernel evaluation

`chooseC` computes `Nat.choose` by a formula the kernel evaluates quickly.
-/

open Finset Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## Computable sums -/

def chooseC (m t : ℕ) : ℕ := m.descFactorial t / t.factorial

lemma chooseC_eq (m t : ℕ) : chooseC m t = m.choose t :=
  (Nat.choose_eq_descFactorial_div_factorial m t).symm

/-! ## From rationals to naturals -/

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ} {γ₁ γ₂ β mb : ℕ}

/-! ## The capped route in naturals -/

end RejOrder

end
end Numeric

section GapCount
/-!
# Counting test vectors by the actual free runs of each row

A test vector on `T` whose duals lie on a slot set `S` is constrained row by row: each row
uses its longest *cyclic* run of free positions, `cgap`. Runs may wrap around: since `ζ k ^ n` is the same for every slot (`-1` for the
negacyclic ring), power sums that vanish across the wrap still vanish at consecutive exponents
(`dual_row_zero`). Each row also keeps the trivial bound `q^(t_i)`, so a row contributes
`q^min(t_i, |S| - cgap)` (`card_suppIn1_le_gap`).
-/

open Finset Matrix

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## The longest cyclic free run -/

/-- `U` misses the `ρ` cyclically consecutive positions `t₀, t₀ + 1, …` (mod `n`). -/
def CFree (n : ℕ) (U : Finset (Fin n)) (t₀ ρ : ℕ) : Prop :=
  ∀ a < ρ, ∀ s ∈ U, (s : ℕ) ≠ (t₀ + a) % n

/-- The length of the longest cyclic run of positions not in `U` (at most `n`). -/
def cgap (n : ℕ) (U : Finset (Fin n)) : ℕ :=
  ((range n ×ˢ range (n + 1)).filter fun p => CFree n U p.1 p.2).sup Prod.snd

lemma le_cgap {n : ℕ} {U : Finset (Fin n)} {t₀ ρ : ℕ} (ht : t₀ < n) (hρ : ρ ≤ n)
    (h : CFree n U t₀ ρ) : ρ ≤ cgap n U := by
  unfold cgap
  exact Finset.le_sup (f := Prod.snd) (b := (t₀, ρ)) (Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ht, Finset.mem_range.mpr (Nat.lt_succ_of_le hρ)⟩, h⟩)

lemma exists_cfree {n : ℕ} (hn : 0 < n) (U : Finset (Fin n)) :
    ∃ t₀ < n, cgap n U ≤ n ∧ CFree n U t₀ (cgap n U) := by
  have hne : ((range n ×ˢ range (n + 1)).filter fun p => CFree n U p.1 p.2).Nonempty :=
    ⟨(0, 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hn,
      Finset.mem_range.mpr (by omega)⟩, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup _ hne Prod.snd
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp1
  refine ⟨p.1, Finset.mem_range.mp h1, ?_, ?_⟩
  · rw [cgap, hpe]; have := Finset.mem_range.mp h2; omega
  · rw [cgap, hpe]; exact hp2

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

/-! ## The uncertainty principle across the wrap -/

/-- If row `i` of `Λ` vanishes outside `U`, and its dual coordinates vanish outside a set `S₀`
no larger than the longest cyclic free run of `U`, then they vanish everywhere. -/
lemma dual_row_zero {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (hζ0 : ∀ k, ζ k ≠ 0)
    {c : ZMod q} (hw : ∀ k, ζ k ^ n = c) (Λ : Fin (K * n) → ZMod q) (i : Fin K)
    (U S₀ : Finset (Fin n)) (hU : ∀ s, s ∉ U → Λ (finProdFinEquiv (i, s)) = 0)
    (hS₀ : S₀.card ≤ cgap n U) (hd : ∀ k, k ∉ S₀ → dual ζ Λ i k = 0) : dual ζ Λ i = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext k; exact k.elim0
  obtain ⟨t₀, ht₀, -, hfree⟩ := exists_cfree hn U
  apply dual_vanish ζ hζ hζ0 _ S₀ hd t₀ _ hS₀
  intro a ha
  set m := (t₀ + a) % n with hm
  have hmn : m < n := Nat.mod_lt _ hn
  have hnot : (⟨m, hmn⟩ : Fin n) ∉ U := fun hin => hfree a ha _ hin rfl
  have hsp := dual_spec hζ Λ i ⟨m, hmn⟩
  rw [hU _ hnot] at hsp
  have hpow : ∀ k, ζ k ^ (t₀ + a) = c ^ ((t₀ + a) / n) * ζ k ^ m := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod (t₀ + a) n]
    rw [pow_add, pow_mul, hw k]
  calc ∑ k, dual ζ Λ i k * ζ k ^ (t₀ + a)
      = c ^ ((t₀ + a) / n) * ∑ k, ζ k ^ m * dual ζ Λ i k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [hpow k]; ring
    _ = 0 := by rw [hsp, mul_zero]

/-! ## Restriction to one row -/

/-- The values of `κ` on the coordinates of `T` in row `i`. -/
def rowRes (T : Finset (Fin (K * n))) (i : Fin K) (κ : T → ZMod q) : rowT T i → ZMod q :=
  fun s => κ ⟨finProdFinEquiv (i, s.1), (Finset.mem_filter.mp s.2).2⟩

/-- Row `i` of the extension by zero, from the row values alone. -/
def rowVec (T : Finset (Fin (K * n))) (i : Fin K) (h : rowT T i → ZMod q) : Fin n → ZMod q :=
  fun s => if hs : s ∈ rowT T i then h ⟨s, hs⟩ else 0

lemma rowVec_res (T : Finset (Fin (K * n))) (i : Fin K) (κ : T → ZMod q) :
    rowVec T i (rowRes T i κ) = blk (ext T κ) i := by
  funext s
  simp only [rowVec, rowRes, blk, ext]
  by_cases hs : s ∈ rowT T i
  · simp [hs, (Finset.mem_filter.mp hs).2]
  · have : finProdFinEquiv (i, s) ∉ T := fun h => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp [hs, this]

lemma mem_suppIn1 {ζ : Fin n → ZMod q} (T : Finset (Fin (K * n))) (S : Finset (Fin n))
    (κ : T → ZMod q) :
    κ ∈ suppIn1 ζ T S ↔ ∀ i k, k ∉ S → dual ζ (ext T κ) i k = 0 := by
  have e2 : ext T (fun _ => (0 : ZMod q)) = 0 := by funext r; simp [ext]
  have d0 : ∀ i, dual ζ (0 : Fin (K * n) → ZMod q) i = 0 := by
    intro i; unfold dual; rw [show blk (0 : Fin (K * n) → ZMod q) i = 0 from rfl,
      Matrix.mulVec_zero]
  simp only [suppIn1, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i k hk
    by_contra hne
    exact hk (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, Or.inl hne⟩))
  · intro h k hk
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hk).2
    by_contra hkS
    rcases hi with hi | hi
    · exact hi (h i k hkS)
    · apply hi
      change dual ζ (ext T fun r => (Sum.elim κ 0 : T ⊕ T → ZMod q) (Sum.inr r)) i k = 0
      simp only [Sum.elim_inr, Pi.zero_apply]
      rw [e2, d0]; rfl

/-- **Uncertainty count with the actual free runs.** Each row contributes at most
`q^min(t_i, |S| - cgap)` one-sided test vectors supported on `S`. -/
lemma card_suppIn1_le_gap {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ)
    (hζ0 : ∀ k, ζ k ≠ 0) {c : ZMod q} (hw : ∀ k, ζ k ^ n = c) (T : Finset (Fin (K * n)))
    (S : Finset (Fin n)) :
    (suppIn1 ζ T S).card
      ≤ ∏ i : Fin K, q ^ min (rowT T i).card (S.card - cgap n (rowT T i)) := by
  set A := suppIn1 ζ T S with hA
  set R : ∀ i : Fin K, Finset (rowT T i → ZMod q) := fun i => A.image (rowRes T i) with hR
  -- the rows determine the function
  have hinj : Set.InjOn (fun κ (i : Fin K) => rowRes T i κ) (A : Set (T → ZMod q)) := by
    intro κ₁ _ κ₂ _ he
    funext r
    obtain ⟨⟨i, s⟩, hrs⟩ := finProdFinEquiv.surjective r.1
    have hs : s ∈ rowT T i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hrs]; exact r.2⟩
    have := congrFun (congrFun he i) ⟨s, hs⟩
    simp only [rowRes] at this
    have hr : (⟨finProdFinEquiv (i, s), (Finset.mem_filter.mp hs).2⟩ : T) = r :=
      Subtype.ext hrs
    rwa [hr] at this
  have hmaps : ∀ κ ∈ A, (fun κ (i : Fin K) => rowRes T i κ) κ ∈ Fintype.piFinset R :=
    fun κ hκ => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hκ
  refine (Finset.card_le_card_of_injOn _ hmaps hinj).trans ?_
  rw [Fintype.card_piFinset]
  refine Finset.prod_le_prod fun i _ => ?_
  have b1 : (R i).card ≤ q ^ (rowT T i).card := by
    refine (Finset.card_le_univ _).trans (le_of_eq ?_)
    rw [Fintype.card_fun, ZMod.card, Fintype.card_coe]
  have b2 : (R i).card ≤ q ^ (S.card - cgap n (rowT T i)) := by
    obtain ⟨S₀, hsub, hcard⟩ := Finset.exists_subset_card_eq
      (min_le_left S.card (cgap n (rowT T i)))
    set code : (rowT T i → ZMod q) → (↥(S \ S₀) → ZMod q) :=
      fun h k => (((Matrix.vandermonde ζ)ᵀ)⁻¹ *ᵥ rowVec T i h) k with hcode
    have hcd : ∀ κ : T → ZMod q, ∀ k, (((Matrix.vandermonde ζ)ᵀ)⁻¹ *ᵥ
        rowVec T i (rowRes T i κ)) k = dual ζ (ext T κ) i k := by
      intro κ k; rw [rowVec_res]; rfl
    have hinj2 : Set.InjOn code (R i : Set (rowT T i → ZMod q)) := by
      intro h₁ h₁m h₂ h₂m he
      obtain ⟨κ₁, hκ₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₁m)
      obtain ⟨κ₂, hκ₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₂m)
      have z₁ := (mem_suppIn1 T S κ₁).mp hκ₁
      have z₂ := (mem_suppIn1 T S κ₂).mp hκ₂
      have hd : ∀ k, k ∉ S₀ → dual ζ (ext T (κ₁ - κ₂)) i k = 0 := by
        intro k hk
        rw [ext_sub, dual_sub, Pi.sub_apply, sub_eq_zero]
        by_cases hkS : k ∈ S
        · have := congrFun he ⟨k, Finset.mem_sdiff.mpr ⟨hkS, hk⟩⟩
          simp only [hcode, hcd] at this
          exact this
        · rw [z₁ i k hkS, z₂ i k hkS]
      have hU : ∀ s, s ∉ rowT T i → ext T (κ₁ - κ₂) (finProdFinEquiv (i, s)) = 0 :=
        fun s hs => ext_out T _ fun h => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have h0 := dual_row_zero hζ hζ0 hw (ext T (κ₁ - κ₂)) i (rowT T i) S₀ hU
        (by rw [hcard]; exact min_le_right _ _) hd
      funext s
      have hsp := dual_spec hζ (ext T (κ₁ - κ₂)) i s.1
      rw [h0] at hsp
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hsp
      have hc := ext_coe T (κ₁ - κ₂) ⟨finProdFinEquiv (i, s.1), (Finset.mem_filter.mp s.2).2⟩
      rw [← hsp] at hc
      simp only [rowRes]
      exact (sub_eq_zero.mp (by rw [← Pi.sub_apply]; exact hc.symm))
    refine (Finset.card_le_card_of_injOn code (fun _ _ => Finset.mem_coe.mpr
      (Finset.mem_univ _)) hinj2).trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe,
      Finset.card_sdiff_of_subset hsub, hcard]
    congr 1; omega
  rcases le_total (rowT T i).card (S.card - cgap n (rowT T i)) with hle | hle
  · rw [min_eq_left hle]; exact b1
  · rw [min_eq_right hle]; exact b2

variable (n K) in
/-- The exponent of the count: `∑ i, min(t_i, σ - cgap_i)`. -/
def xg (σ : ℕ) (T : Finset (Fin (K * n))) : ℕ :=
  ∑ i : Fin K, min (rowT T i).card (σ - cgap n (rowT T i))

lemma card_suppIn1_le_xg {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ)
    (hζ0 : ∀ k, ζ k ≠ 0) {c : ZMod q} (hw : ∀ k, ζ k ^ n = c) (T : Finset (Fin (K * n)))
    (S : Finset (Fin n)) : (suppIn1 ζ T S).card ≤ q ^ xg n K S.card T := by
  rw [xg, ← Finset.prod_pow_eq_pow_sum]
  exact card_suppIn1_le_gap hζ hζ0 hw T S

end RejOrder

end
end GapCount

section GapComb
/-!
# How many rows have only short free runs

A row of size `u` all of whose cyclic free runs have length at most `g` is rare. Cutting the
cycle just after one of its `u` elements leaves `u - 1` points on a path of `n - 1` positions
with no free run longer than `g` (`card_shortSet`, a double count over the `u` cut points), and
such sets are counted by compositions: the coefficient of `X^(N-v)` in `(1 + X + ⋯ + X^g)^(v+1)`
(`card_linSet`, by removing the first point).
-/

open Finset Polynomial

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

/-- `1 + X + ⋯ + X^g`. -/
def runPoly (g : ℕ) : ℕ[X] := ∑ z ∈ range (g + 1), X ^ z

lemma coeff_runPoly (g a : ℕ) : (runPoly g).coeff a = if a < g + 1 then 1 else 0 := by
  simp only [runPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- Subsets of `{0, …, N-1}` of size `v` that meet every window of `g + 1` consecutive
positions. -/
def linSet (N g v : ℕ) : Finset (Finset ℕ) :=
  ((range N).powersetCard v).filter fun W => ∀ t, t + g + 1 ≤ N → ∃ a ≤ g, t + a ∈ W

/-- The composition count: `v + 1` free runs of length at most `g` adding up to `N - v`. -/
def linB (N g v : ℕ) : ℕ := if v ≤ N then ((runPoly g) ^ (v + 1)).coeff (N - v) else 0

/-- Removing the first point. -/
lemma linSet_cover (N g v : ℕ) :
    linSet N g (v + 1) ⊆ ((range (g + 1)).filter (· < N)).biUnion
      (fun z => (linSet (N - z - 1) g v).image (fun W => insert z (W.image (· + (z + 1))))) := by
  intro V hV
  obtain ⟨hVp, hwin⟩ := Finset.mem_filter.mp hV
  obtain ⟨hVsub, hVcard⟩ := Finset.mem_powersetCard.mp hVp
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  set z := V.min' hne with hz
  have hzV : z ∈ V := Finset.min'_mem V hne
  have hzN : z < N := Finset.mem_range.mp (hVsub hzV)
  have hzg : z ≤ g := by
    by_cases hN : g + 1 ≤ N
    · obtain ⟨a, ha, haV⟩ := hwin 0 (by omega)
      have := Finset.min'_le V _ haV
      omega
    · omega
  have hgt : ∀ x ∈ V.erase z, z < x := fun x hx =>
    lt_of_le_of_ne (Finset.min'_le V x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx).symm
  refine Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hzN⟩, ?_⟩
  refine Finset.mem_image.mpr ⟨(V.erase z).image (· - (z + 1)), ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      have h1 := hgt x hx
      have h2 := Finset.mem_range.mp (hVsub (Finset.mem_of_mem_erase hx))
      exact Finset.mem_range.mpr (by omega)
    · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem hzV, hVcard, Nat.add_sub_cancel]
      intro x hx y hy hxy
      have := hgt x hx; have := hgt y hy
      simp only at hxy
      omega
    · intro t ht
      obtain ⟨a, ha, haV⟩ := hwin (t + z + 1) (by omega)
      exact ⟨a, ha, Finset.mem_image.mpr ⟨t + z + 1 + a,
        Finset.mem_erase.mpr ⟨by omega, haV⟩, by omega⟩⟩
  · ext x
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨w, ⟨y, ⟨hyz, hyV⟩, rfl⟩, rfl⟩)
      · exact hzV
      · have := hgt y (Finset.mem_erase.mpr ⟨hyz, hyV⟩)
        rwa [show y - (z + 1) + (z + 1) = y by omega]
    · intro hx
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        have := hgt x (Finset.mem_erase.mpr ⟨hxz, hx⟩)
        exact ⟨x - (z + 1), ⟨x, ⟨hxz, hx⟩, rfl⟩, by omega⟩

lemma linB_step (N g v : ℕ) :
    ∑ z ∈ (range (g + 1)).filter (· < N), linB (N - z - 1) g v ≤ linB N g (v + 1) := by
  by_cases hv : v + 1 ≤ N
  · set M := N - (v + 1) with hM
    set f : ℕ → ℕ := fun b => ((runPoly g) ^ (v + 1)).coeff b with hf
    have hR : linB N g (v + 1) = ∑ a ∈ (range (M + 1)).filter (· < g + 1), f (M - a) := by
      rw [linB, ite_eq_left hv, pow_succ', Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [coeff_runPoly]
      split_ifs <;> simp [hf, hM]
    have hL : ∑ z ∈ (range (g + 1)).filter (· < N), linB (N - z - 1) g v
        = ∑ z ∈ (range (g + 1)).filter (· ≤ M), f (M - z) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      unfold linB
      by_cases hz : z ≤ M
      · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hz, show N - z - 1 - v = M - z by omega]
      · rw [ite_eq_right hz]
        split_ifs with h1 h2 <;> first | rfl | omega
    rw [hL, hR]
    apply le_of_eq
    apply Finset.sum_congr _ fun _ _ => rfl
    ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
  · rw [linB, ite_eq_right hv]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro z hz
    have := (Finset.mem_filter.mp hz).2
    rw [linB, ite_eq_right (by omega)]

lemma card_linSet (g : ℕ) : ∀ v N, (linSet N g v).card ≤ linB N g v := by
  intro v
  induction v with
  | zero =>
    intro N
    by_cases hN : N < g + 1
    · rw [linB, ite_eq_left (Nat.zero_le _), zero_add, pow_one, coeff_runPoly, ite_eq_left (by omega)]
      refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
      rw [Finset.card_powersetCard, Nat.choose_zero_right]
    · apply le_of_eq_of_le (b := 0) _ (Nat.zero_le _)
      rw [Finset.card_eq_zero, linSet, Finset.filter_eq_empty_iff]
      intro W hW hwin
      rw [Finset.mem_powersetCard, Finset.card_eq_zero] at hW
      obtain ⟨a, _, ha⟩ := hwin 0 (by omega)
      rw [hW.2] at ha
      exact Finset.notMem_empty _ ha
  | succ v ih =>
    intro N
    refine (Finset.card_le_card (linSet_cover N g v)).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun z _ => Finset.card_image_le.trans (ih (N - z - 1))).trans ?_
    exact linB_step N g v

/-! ## Cutting the cycle -/

lemma mod_two_cases (a n : ℕ) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

variable {n : ℕ}

/-- Rows of size `u` whose longest cyclic free run is at most `g`. -/
def shortSet (n u g : ℕ) : Finset (Finset (Fin n)) :=
  (univ.powersetCard u).filter fun U => cgap n U ≤ g

/-- Double count over the `u` points at which the cycle can be cut. -/
lemma card_shortSet (hn : 0 < n) (u g : ℕ) :
    u * (shortSet n u g).card ≤ n * (linSet (n - 1) g (u - 1)).card := by
  set rot : Fin n → ℕ → Fin n := fun e w => ⟨(w + e + 1) % n, Nat.mod_lt _ hn⟩ with hrot
  set rel : Fin n → Fin n → ℕ := fun e x => ((x : ℕ) + (n - 1 - e)) % n with hrel
  have hrel_eq : ∀ e x : Fin n, rel e x
      = if (e : ℕ) < (x : ℕ) then (x : ℕ) - (e : ℕ) - 1 else (x : ℕ) + (n - 1 - (e : ℕ)) := by
    intro e x
    have := e.2; have := x.2
    rw [hrel]; dsimp only
    rw [mod_two_cases _ _ (by omega)]
    split_ifs <;> omega
  have hrot_rel : ∀ e x : Fin n, rot e (rel e x) = x := by
    intro e x
    apply Fin.ext
    have := e.2; have := x.2
    rw [hrot]; dsimp only
    rw [hrel_eq, mod_two_cases _ _ (by split_ifs <;> omega)]
    split_ifs <;> omega
  set P := (shortSet n u g).sigma (fun U => U) with hP
  have hPcard : P.card = u * (shortSet n u g).card := by
    rw [hP, Finset.card_sigma, Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const,
      smul_eq_mul, mul_comm]
    intro U hU
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).2
  have hcover : P ⊆ (univ : Finset (Fin n)).biUnion (fun e => (linSet (n - 1) g (u - 1)).image
      (fun W => (⟨insert e (W.image (rot e)), e⟩ : Σ _ : Finset (Fin n), Fin n))) := by
    rintro ⟨U, e⟩ hUe
    obtain ⟨hU, he⟩ := Finset.mem_sigma.mp hUe
    obtain ⟨hUp, hUg⟩ := Finset.mem_filter.mp hU
    have hUc := (Finset.mem_powersetCard.mp hUp).2
    refine Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨(U.erase e).image (rel e), ?_, ?_⟩⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
      · intro w hw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
        have hxe : x ≠ e := Finset.ne_of_mem_erase hx
        have hxe' : (x : ℕ) ≠ e := fun h => hxe (Fin.ext h)
        have := e.2; have := x.2
        rw [Finset.mem_range, hrel_eq]
        split_ifs <;> omega
      · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem he, hUc]
        intro x _ y _ hxy
        have := e.2; have := x.2; have := y.2
        simp only [hrel_eq] at hxy
        apply Fin.ext
        split_ifs at hxy <;> omega
      · intro t ht
        by_contra hcon
        push Not at hcon
        have hfree : CFree n U ((e + 1 + t) % n) (g + 1) := by
          intro a ha s hs hse
          have := e.2; have := s.2
          rw [Nat.mod_add_mod, mod_two_cases _ _ (by omega)] at hse
          have hse' : (s : ℕ) ≠ e := by split_ifs at hse <;> omega
          apply hcon a (by omega)
          refine Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨fun h => hse' (by rw [h]), hs⟩, ?_⟩
          rw [hrel_eq]
          split_ifs at hse ⊢ <;> omega
        have h1 := le_cgap (Nat.mod_lt _ hn) (by omega) hfree
        have h2 : cgap n U ≤ g := hUg
        omega
    · have hR : insert e (((U.erase e).image (rel e)).image (rot e)) = U := by
        rw [Finset.image_image]
        ext s
        simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Function.comp,
          hrot_rel]
        constructor
        · rintro (rfl | ⟨x, ⟨_, hx⟩, rfl⟩)
          · exact he
          · exact hx
        · intro hs
          by_cases hse : s = e
          · exact Or.inl hse
          · exact Or.inr ⟨s, ⟨hse, hs⟩, rfl⟩
      rw [hR]
  calc u * (shortSet n u g).card = P.card := hPcard.symm
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ e : Fin n, ((linSet (n - 1) g (u - 1)).image _).card := Finset.card_biUnion_le
    _ ≤ ∑ _e : Fin n, (linSet (n - 1) g (u - 1)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = n * (linSet (n - 1) g (u - 1)).card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end RejOrder

end
end GapComb

section GapEval
/-!
# Evaluating the gap counts

The per-row counts are coefficients of polynomials with natural coefficients. They are evaluated
by Kronecker substitution: a polynomial `p` whose coefficients are below `2^e` is stored as the
number `p(2^e)`, products of polynomials become products of numbers, and the coefficient of
`X^t` is read off as the `t`-th block of `e` bits (`digit_eval`). When a coefficient bound
fails, the definitions fall back to the sum of all coefficients, which is still an upper bound,
so the definitions below are upper bounds unconditionally (`compK_ge`, `coefK_ge`).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## Computable definitions -/

/-- `∑ i < k, f i`, by `Nat.rec` (cheaper in the kernel than `sumR`). -/
def sumF (f : ℕ → ℕ) (k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc + f i) k

/-- The `t`-th block of `e` bits of `N`. -/
def digit (e N t : ℕ) : ℕ := (N >>> (e * t)) &&& (2 ^ e - 1)

/-- `(1 + X + ⋯ + X^g)` at `X = 2^e`. -/
def geomK (e g : ℕ) : ℕ := sumF (fun z => 1 <<< (e * z)) (g + 1)

/-- Upper bound on the coefficient of `X^d` in `(1 + X + ⋯ + X^g)^u`. -/
def compK (e g u d : ℕ) : ℕ := if (g + 1) ^ u < 2 ^ e then digit e (geomK e g ^ u) d else (g + 1) ^ u

/-- Upper bound on the number of rows of size `u` with no cyclic free run longer than `g`. -/
def NBk (e n u g : ℕ) : ℕ := min (chooseC n u) (n * compK e g u (n - u) / u)

/-- Upper bound on `∑_{|U| = u} q^(c·min(u, σ - cgap U))`. -/
def GBk (e q n c σ u : ℕ) : ℕ :=
  chooseC n u + (q ^ c - 1) *
    sumF (fun g => if σ < g + 1 + u then q ^ (c * (σ - 1 - g)) * NBk e n u g else 0) σ

def sumGB (e q n c σ s : ℕ) : ℕ := sumF (fun u => GBk e q n c σ u) (s + 1)

def packGB (e e₂ q n c σ s : ℕ) : ℕ := sumF (fun u => GBk e q n c σ u <<< (e₂ * u)) (s + 1)

/-- Upper bound on the coefficient of `X^t` in the `K`-th power of `∑_{u ≤ s} GBk u · X^u`. -/
def coefK (e e₂ q n K c σ s t : ℕ) : ℕ :=
  if sumGB e q n c σ s ^ K < 2 ^ e₂ then digit e₂ (packGB e e₂ q n c σ s ^ K) t
  else sumGB e q n c σ s ^ K

lemma sumF_eq (f : ℕ → ℕ) (k : ℕ) : sumF f k = ∑ i ∈ range k, f i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-! ## Kronecker substitution -/

lemma digit_sum_aux {B : ℕ} (hB : 0 < B) :
    ∀ (t D : ℕ) (c : ℕ → ℕ), (∀ i, c i < B) → t < D →
      (∑ i ∈ range D, c i * B ^ i) / B ^ t % B = c t := by
  intro t
  induction t with
  | zero =>
    intro D c hc hD
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    rw [Finset.sum_range_succ', pow_zero, Nat.div_one, mul_one]
    have : ∑ i ∈ range D, c (i + 1) * B ^ (i + 1) = B * ∑ i ∈ range D, c (i + 1) * B ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (hc 0)]
  | succ t ih =>
    intro D c hc hD
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    rw [Finset.sum_range_succ', pow_zero, mul_one]
    have : ∑ i ∈ range D, c (i + 1) * B ^ (i + 1) = B * ∑ i ∈ range D, c (i + 1) * B ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, pow_succ', ← Nat.div_div_eq_div_mul, add_comm, Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt (hc 0), zero_add]
    exact ih D (fun i => c (i + 1)) (fun i => hc (i + 1)) (by omega)

lemma digit_eq (e N t : ℕ) : digit e N t = N / (2 ^ e) ^ t % 2 ^ e := by
  rw [digit, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, ← pow_mul]

lemma digit_eval (e : ℕ) (p : ℕ[X]) (hp : ∀ i, p.coeff i < 2 ^ e) (t : ℕ) :
    digit e (p.eval (2 ^ e)) t = p.coeff t := by
  rw [digit_eq, eval_eq_sum_range' (n := max (p.natDegree + 1) (t + 1)) (by omega)]
  exact digit_sum_aux (by positivity) t _ _ hp (by omega)

lemma coeff_le_eval_one (p : ℕ[X]) (i : ℕ) : p.coeff i ≤ p.eval 1 := by
  rw [eval_eq_sum_range' (n := p.natDegree + 1) (by omega)]
  simp only [one_pow, mul_one]
  by_cases hi : i < p.natDegree + 1
  · exact Finset.single_le_sum (f := fun j => p.coeff j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact Nat.zero_le _

/-- A coefficient read off by Kronecker substitution, or the fallback bound. -/
lemma coeff_le_kron (e K t : ℕ) (p : ℕ[X]) :
    (p ^ K).coeff t ≤ if p.eval 1 ^ K < 2 ^ e then digit e (p.eval (2 ^ e) ^ K) t
      else p.eval 1 ^ K := by
  have hb : ∀ i, (p ^ K).coeff i ≤ p.eval 1 ^ K := fun i => by
    have := coeff_le_eval_one (p ^ K) i; rwa [eval_pow] at this
  split_ifs with h
  · rw [← eval_pow, digit_eval e _ (fun i => lt_of_le_of_lt (hb i) h)]
  · exact hb t

lemma runPoly_eval (e g : ℕ) : (runPoly g).eval (2 ^ e) = geomK e g := by
  rw [geomK, sumF_eq, runPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [eval_pow, eval_X, Nat.shiftLeft_eq, one_mul, pow_mul]

lemma runPoly_eval_one (g : ℕ) : (runPoly g).eval 1 = g + 1 := by
  simp [runPoly, eval_finsetSum]

lemma compK_ge (e g u d : ℕ) : ((runPoly g) ^ u).coeff d ≤ compK e g u d := by
  have := coeff_le_kron e u d (runPoly g)
  rwa [runPoly_eval, runPoly_eval_one] at this

/-- The polynomial `∑_{u ≤ s} GBk u · X^u`. -/
noncomputable def gbPoly (e q n c σ s : ℕ) : ℕ[X] :=
  ∑ u ∈ range (s + 1), C (GBk e q n c σ u) * X ^ u

lemma coeff_gbPoly (e q n c σ s u : ℕ) (hu : u ≤ s) :
    (gbPoly e q n c σ s).coeff u = GBk e q n c σ u := by
  rw [gbPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, ite_eq_left_iff, not_lt]
  intro h; omega

lemma coefK_ge (e e₂ q n K c σ s t : ℕ) :
    ((gbPoly e q n c σ s) ^ K).coeff t ≤ coefK e e₂ q n K c σ s t := by
  have h1 : (gbPoly e q n c σ s).eval 1 = sumGB e q n c σ s := by
    simp [gbPoly, eval_finsetSum, sumGB, sumF_eq]
  have h2 : (gbPoly e q n c σ s).eval (2 ^ e₂) = packGB e e₂ q n c σ s := by
    simp only [gbPoly, eval_finsetSum, packGB, sumF_eq, eval_mul, eval_C, eval_pow, eval_X,
      Nat.shiftLeft_eq, pow_mul]
  have := coeff_le_kron e₂ K t (gbPoly e q n c σ s)
  rwa [h1, h2] at this

/-- Coefficients of powers are monotone in the coefficients up to the degree considered. -/
lemma coeff_pow_mono (p p' : ℕ[X]) (t : ℕ) (h : ∀ i ≤ t, p.coeff i ≤ p'.coeff i) :
    ∀ K, ∀ j ≤ t, (p ^ K).coeff j ≤ (p' ^ K).coeff j := by
  intro K
  induction K with
  | zero => intro j _; simp
  | succ K ih =>
    intro j hj
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_le_sum fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    exact Nat.mul_le_mul (ih _ (by omega)) (h _ (by omega))

end RejOrder

end GapEval

section GapSum
/-!
# Summing the gap counts over coordinate sets

The coordinate sets `T` correspond to their `K` rows, so a sum over `T` of a product over rows is
a coefficient of a `K`-th power (`sum_T_prod`). With the per-row bound `row_sum_le` this bounds
`∑_{|T| = t} q^(c·xg σ T)` by `coefK` (`sum_T_le_coefK`).
-/

open Finset Polynomial

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

variable {n K : ℕ}

/-- `q^(c·m) = 1 + (q^c - 1) · ∑_{j < m} q^(c·j)`. -/
lemma pow_geom (q c m : ℕ) (hq : 1 ≤ q) :
    q ^ (c * m) = 1 + (q ^ c - 1) * ∑ j ∈ range m, q ^ (c * j) := by
  have h1 : 1 ≤ q ^ c := Nat.one_le_pow _ _ hq
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show q ^ (c * (m + 1)) = q ^ c * q ^ (c * m) by rw [mul_add, mul_one, pow_add, mul_comm],
      Finset.sum_range_succ, mul_add, ← add_assoc, ← ih, Nat.sub_mul, one_mul]
    have : q ^ (c * m) ≤ q ^ c * q ^ (c * m) := Nat.le_mul_of_pos_left _ (by omega)
    omega

lemma sum_min_reflect (q c u σ ρ : ℕ) :
    ∑ j ∈ range (min u (σ - ρ)), q ^ (c * j)
      = ∑ g ∈ range σ, if σ < g + 1 + u ∧ ρ ≤ g then q ^ (c * (σ - 1 - g)) else 0 := by
  conv_rhs => rw [← Finset.sum_range_reflect]
  have e : ∀ j ∈ range σ, (if σ < σ - 1 - j + 1 + u ∧ ρ ≤ σ - 1 - j
      then q ^ (c * (σ - 1 - (σ - 1 - j))) else 0)
      = if j < min u (σ - ρ) then q ^ (c * j) else 0 := by
    intro j hj
    have := Finset.mem_range.mp hj
    by_cases h : j < min u (σ - ρ)
    · rw [ite_eq_left (by omega), ite_eq_left h, show σ - 1 - (σ - 1 - j) = j by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
  congr 1
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma card_shortSet_le (e : ℕ) (hn : 0 < n) {u g : ℕ} (hu : 1 ≤ u) :
    (shortSet n u g).card ≤ NBk e n u g := by
  refine le_min ?_ ?_
  · rw [chooseC_eq]
    refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    refine (card_shortSet hn u g).trans (Nat.mul_le_mul_left _ ?_)
    refine (card_linSet g (u - 1) (n - 1)).trans ?_
    rw [linB]
    split_ifs with h
    · rw [show u - 1 + 1 = u by omega, show n - 1 - (u - 1) = n - u by omega]
      exact compK_ge e g u (n - u)
    · exact Nat.zero_le _

/-- **Per-row bound.** -/
lemma row_sum_le (e q c σ u : ℕ) (hq : 1 ≤ q) (hn : 0 < n) :
    ∑ U ∈ (univ : Finset (Fin n)).powersetCard u, q ^ (c * min u (σ - cgap n U))
      ≤ GBk e q n c σ u := by
  rw [GBk, sumF_eq]
  have hsplit : ∀ U ∈ (univ : Finset (Fin n)).powersetCard u,
      q ^ (c * min u (σ - cgap n U)) = 1 + (q ^ c - 1) *
        ∑ g ∈ range σ, if σ < g + 1 + u ∧ cgap n U ≤ g then q ^ (c * (σ - 1 - g)) else 0 := by
    intro U _
    rw [pow_geom q c _ hq, sum_min_reflect]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← chooseC_eq, ← Finset.mul_sum]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun g hg => ?_
  have hgσ := Finset.mem_range.mp hg
  by_cases h : σ < g + 1 + u
  · rw [ite_eq_left h]
    have : ∀ U ∈ (univ : Finset (Fin n)).powersetCard u,
        (if σ < g + 1 + u ∧ cgap n U ≤ g then q ^ (c * (σ - 1 - g)) else 0)
          = if cgap n U ≤ g then q ^ (c * (σ - 1 - g)) else 0 :=
      fun U _ => by simp only [h, true_and]
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_left _ (card_shortSet_le e hn (by omega))
  · rw [ite_eq_right h]
    apply le_of_eq
    exact Finset.sum_eq_zero fun U _ => by rw [ite_eq_right (fun h' => h h'.1)]

/-- Coordinate sets are the same as their rows. -/
def rowEquiv : Finset (Fin (K * n)) ≃ (Fin K → Finset (Fin n)) where
  toFun T i := rowT T i
  invFun V := univ.filter fun r => (finProdFinEquiv.symm r).2 ∈ V (finProdFinEquiv.symm r).1
  left_inv T := by
    ext r
    simp only [rowT, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv V := by
    funext i; ext s
    simp only [rowT, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Equiv.symm_apply_apply]

lemma sum_T_prod (f : Finset (Fin n) → ℕ) (t : ℕ) :
    ∑ T ∈ (univ : Finset (Fin (K * n))).powersetCard t, ∏ i, f (rowT T i)
      = ((∑ U : Finset (Fin n), C (f U) * X ^ U.card) ^ K).coeff t := by
  have hpow : (∑ U : Finset (Fin n), C (f U) * X ^ U.card) ^ K
      = ∏ _i : Fin K, ∑ U : Finset (Fin n), C (f U) * X ^ U.card := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, Finset.prod_univ_sum, Fintype.piFinset_univ, finsetSum_coeff]
  have hterm : ∀ V : Fin K → Finset (Fin n),
      (∏ i, C (f (V i)) * X ^ (V i).card).coeff t
        = if ∑ i, (V i).card = t then ∏ i, f (V i) else 0 := by
    intro V
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, coeff_C_mul_X_pow]
    simp only [eq_comm]
  simp_rw [hterm]
  rw [Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter]
  refine Fintype.sum_equiv rowEquiv _ _ fun T => ?_
  simp only [rowEquiv, Equiv.coe_fn_mk, sum_rowT]

/-- **The sum over coordinate sets of a given size.** -/
lemma sum_T_le_coefK (e e₂ q c σ s t : ℕ) (hq : 1 ≤ q) (hn : 0 < n) (ht : t ≤ s) :
    ∑ T ∈ (univ : Finset (Fin (K * n))).powersetCard t, q ^ (c * xg n K σ T)
      ≤ coefK e e₂ q n K c σ s t := by
  set f : Finset (Fin n) → ℕ := fun U => q ^ (c * min U.card (σ - cgap n U)) with hf
  have e1 : ∀ T : Finset (Fin (K * n)), q ^ (c * xg n K σ T) = ∏ i, f (rowT T i) := by
    intro T
    rw [hf, Finset.prod_pow_eq_pow_sum, xg, Finset.mul_sum]
  simp_rw [e1]
  rw [sum_T_prod f t]
  refine le_trans ?_ (coefK_ge e e₂ q n K c σ s t)
  refine coeff_pow_mono _ _ s (fun u hu => ?_) K t ht
  rw [coeff_gbPoly e q n c σ s u hu, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  have : (univ : Finset (Finset (Fin n))).filter (fun U => u = U.card)
      = (univ : Finset (Fin n)).powersetCard u := by
    ext U; simp [Finset.mem_powersetCard, eq_comm]
  rw [this]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun U hU => ?_)) (row_sum_le e q c σ u hq hn)
  simp only [hf, (Finset.mem_powersetCard.mp hU).2]

end RejOrder

end
end GapSum

section GapNumeric
/-!
# Two helpers for the kernel-checked sums
-/

open Finset Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## Computable sums -/

/-! ## From rationals to naturals -/

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ} {γ₁ γ₂ β mb : ℕ}

lemma cast_sub_le_of (A C X : ℕ) (hA : A ≤ X) : (A : ℚ) - C ≤ ((X - C : ℕ) : ℚ) := by
  by_cases h : C ≤ X
  · rw [Nat.cast_sub h]
    have := (Nat.cast_le (α := ℚ)).mpr hA
    linarith
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    have : (A : ℚ) ≤ C := by exact_mod_cast (by omega : A ≤ C)
    push_cast; linarith

lemma sum_idx_card {m : ℕ} (s : ℕ) (F : Finset (Fin m) → ℚ) :
    ∑ T ∈ (univ : Finset (Fin m)).powerset with T.card ≤ s, F T
      = ∑ t ∈ range (s + 1), ∑ T ∈ (univ : Finset (Fin m)).powersetCard t, F T := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (s + 1))
    (fun T hT => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hT).2))]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by omega, h⟩

end RejOrder

end
end GapNumeric

section Covariance

/-!
# A Fourier bound on the covariance of two indicator functions

Let `q` be prime, `P` a finite additive commutative group and `φ φ' : P →+ (Fin m → ZMod q)`
two additive maps. Let `G = Fintype.piFinset g` be a product of nonempty "good" sets
`g r ⊆ ZMod q`, with density `μ = ∏ r, |g r| / q`, and suppose that in every coordinate the bad
density is at most `β` times the good density: `q - |g r| ≤ β |g r|`.

The theorem `cov_le` states that, for `a` uniform on `P`, the covariance of the
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

namespace RejOrder

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

end RejOrder

end Covariance

section TestVectors
/-!
# Test vectors on degenerate slots

The `β`-weighted number of test vectors whose dual coordinates lie on a slot set (`wsum_le`),
bounded by rows with the gap counts (`wcount_le_rows`); the r₀-passing sets `good` and the
additive map `a ↦ A·y`; orthogonal pairs of test vectors live on the degenerate slots
(`dualIn_of_orth`).
-/

open Finset

noncomputable section

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n L : ℕ}

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

section Single
variable {γ₁ γ₂ β mb : ℕ}

/-! ### Single-coordinate facts about the r₀ check under uniform `w` -/

lemma fail_card (hp : Params q γ₁ γ₂ β mb) (c : ℤ) (hc : |c| ≤ β) :
    ((univ : Finset (ZMod q)).filter fun x => (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - c|).card
      = q - mb * (2 * (γ₂ - β) - 1) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod q)))
    (fun x => (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - c|)
  rw [Finset.card_univ, ZMod.card] at h1
  have h2 := r_pass_count hp c hc
  simp only [not_le] at h1
  omega

lemma pass_le_q (hp : Params q γ₁ γ₂ β mb) : mb * (2 * (γ₂ - β) - 1) ≤ q := by
  rw [hp.q_eq]
  have : 2 * (γ₂ - β) - 1 ≤ 2 * γ₂ := by omega
  have := Nat.mul_le_mul_left mb this
  nlinarith

end Single

lemma sum_card_split {m : ℕ} (F : Finset (Fin m) → ℚ) :
    ∑ T ∈ (univ : Finset (Fin m)).powerset, F T
      = ∑ t ∈ range (m + 1), ∑ T ∈ (univ : Finset (Fin m)).powersetCard t, F T := by
  rw [← sum_idx_card m F]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  exact ⟨fun _ => by simpa using Finset.card_le_univ T, fun _ => trivial⟩

section Pass
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

end Pass

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

lemma sumF_ite_Icc (dm : ℕ) (f : ℕ → ℚ) :
    ∑ x ∈ range (dm + 1), (if 1 ≤ x then f x else 0) = ∑ d ∈ Icc 1 dm, f d := by
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (by ext d; simp [Finset.mem_Icc]; omega) fun d _ => rfl

end RejOrder

end

end TestVectors

section FourierLeak

/-!
# The leak via the product-Fourier bound

`leak` (the per-attempt leak of circl's check order) bounded on average over `A`. Every view
of an attempt is a difference of prefix-pass product sets `P_i = ∏_{r<i} good_r × ∏_{r≥i} univ`
(`leak_le_Dev`), so `cov_le` applies to each; pairs of nonces are independent, so a degenerate
slot has probability `(q+1)/(2γ₁)^L` (`deg_card_prob`), and the weighted counts are bounded by
rows (`wcount_le_rows`). Result (`leak_avg_fourier`, instantiated in `leak_mldsa44` etc.):
`E_A leak ≤ 2^-405, 2^-547, 2^-729` for ML-DSA-44/65/87.
-/

open Finset Matrix

noncomputable section

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

/-- Coordinates before `i` must pass the r₀ check, the others are free. -/
def gset (γ₂ β : ℕ) (v : Fin (K * n) → ℤ) (i : ℕ) (r : Fin (K * n)) : Finset (ZMod q) :=
  if (r : ℕ) < i then good γ₂ β v r else univ

/-- The prefix-pass set: the first `i` coordinates of `w` pass the r₀ check. -/
def Pset (γ₂ β : ℕ) (v : Fin (K * n) → ℤ) (i : ℕ) : Finset (Fin (K * n) → ZMod q) :=
  Fintype.piFinset (gset (q := q) γ₂ β v i)

/-- Density of the prefix-pass set. -/
def muP (γ₂ β : ℕ) (v : Fin (K * n) → ℤ) (i : ℕ) : ℚ :=
  ∏ r, ((gset (q := q) γ₂ β v i r).card : ℚ) / q

/-- Deviation of `Pr[y ∈ B' ∧ A·y ∈ P_i]` from `Pr[B'] · |P_i|/q^m`, `y` uniform on the box. -/
def Dev (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)) (γ₁ γ₂ β : ℕ)
    (v : Fin (K * n) → ℤ) (i : ℕ) (B' : Finset (Fin (L * n) → ℤ))
    (a : Fin K → Fin L → Fin n → ZMod q) : ℚ :=
  |((B'.filter fun y => modMat mulmat a *ᵥ zc y ∈ Pset (q := q) γ₂ β v i).card : ℚ)
      / (box γ₁ (L * n)).card
    - (B'.card : ℚ) / (box γ₁ (L * n)).card * muP (q := q) γ₂ β v i|

lemma muP_nonneg (γ₂ β : ℕ) (v : Fin (K * n) → ℤ) (i : ℕ) : 0 ≤ muP (q := q) γ₂ β v i :=
  Finset.prod_nonneg fun r _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma muP_le_one (γ₂ β : ℕ) (v : Fin (K * n) → ℤ) (i : ℕ) : muP (q := q) γ₂ β v i ≤ 1 := by
  refine Finset.prod_le_one₀ (fun r _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    fun r _ => ?_
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [div_le_one hq]
  exact_mod_cast (Finset.card_le_univ _).trans (by rw [ZMod.card])

/-- **Second moment of `Dev`.** For any sub-event `B'` of the box and any `i`,
`E_A Dev² ≤ ∑_{d ≤ d_m} C(n,d) ρ^d E_b(d)² + C(n, d_m+1) ρ^(d_m+1)`,
`ρ = (q+1)/(2γ₁)^L` the probability of a degenerate slot for independent `y, y'`. -/
theorem Dsq_le {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {γ₁ γ₂ β : ℕ} {v : Fin (K * n) → ℤ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q)
    (B' : Finset (Fin (L * n) → ℤ)) (hB' : B' ⊆ box γ₁ (L * n)) (i : ℕ)
    (bt : ℚ) (hbt : 0 ≤ bt)
    (hbad : ∀ r, ((q : ℚ) - (good (q := q) γ₂ β v r).card) ≤ bt * (good (q := q) γ₂ β v r).card)
    (dm : ℕ) (Eb : ℕ → ℚ)
    (hEb : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then bt ^ (supp ξ).card else 0) ≤ Eb S.card) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q => Dev mulmat γ₁ γ₂ β v i B' a ^ 2)
      ≤ ∑ d ∈ Icc 1 dm, (n.choose d * (((q : ℚ) + 1) / (2 * γ₁ : ℚ) ^ L) ^ d) * Eb d ^ 2
        + n.choose (dm + 1) * (((q : ℚ) + 1) / (2 * γ₁ : ℚ) ^ L) ^ (dm + 1) := by
  set μ := muP (q := q) γ₂ β v i with hμdef
  have hμ0 : 0 ≤ μ := muP_nonneg γ₂ β v i
  have hμ1 : μ ≤ 1 := muP_le_one γ₂ β v i
  set Bx := box γ₁ (L * n)
  have hBx : (0 : ℚ) < Bx.card := by
    rw [card_box_nat]; have : 0 < 2 * γ₁ := by omega
    positivity
  have hgset : ∀ r, ((q : ℚ) - (gset (q := q) γ₂ β v i r).card)
      ≤ bt * (gset (q := q) γ₂ β v i r).card := by
    intro r; unfold gset
    split_ifs
    · exact hbad r
    · rw [card_univ, ZMod.card, sub_self]; positivity
  have hgne : ∀ r, (gset (q := q) γ₂ β v i r).Nonempty := by
    intro r
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have := hgset r
    rw [hne, Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero] at this
    have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    linarith
  -- the centred indicator
  set X : (Fin K → Fin L → Fin n → ZMod q) → (Fin (L * n) → ℤ) → ℚ := fun a y =>
    (if phiHom h (zc y) a ∈ Fintype.piFinset (gset (q := q) γ₂ β v i) then (1 : ℚ) else 0) - μ
    with hX
  have hDev : ∀ a, Dev mulmat γ₁ γ₂ β v i B' a ^ 2
      = (∑ y ∈ B', ∑ y' ∈ B', X a y * X a y') / (Bx.card : ℚ) ^ 2 := by
    intro a
    have e : ((B'.filter fun y => modMat mulmat a *ᵥ zc y ∈ Pset (q := q) γ₂ β v i).card : ℚ)
        / Bx.card - (B'.card : ℚ) / Bx.card * μ = (∑ y ∈ B', X a y) / Bx.card := by
      simp only [hX]
      rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
      rw [sub_div]
      congr 1
      ring
    unfold Dev
    rw [← hμdef, e, sq_abs, div_pow, sq, Finset.sum_mul_sum]
  -- per-pair bound
  set D : (Fin (L * n) → ℤ) × (Fin (L * n) → ℤ) → ℕ := fun yy => (degS ζ yy.1 yy.2).card
  set Hf : ℕ → ℚ := fun d => ∑ e ∈ Icc 1 dm, (if e ≤ d then Eb e ^ 2 else 0)
    + (if dm + 1 ≤ d then 1 else 0)
  have hHf0 : ∀ d, 0 ≤ ∑ e ∈ Icc 1 dm, (if e ≤ d then Eb e ^ 2 else 0) :=
    fun d => Finset.sum_nonneg fun e _ => by split_ifs <;> positivity
  have hP : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
    exact_mod_cast Fintype.card_pos
  have hX1 : ∀ a y y', X a y * X a y' ≤ 1 := by
    intro a y y'
    simp only [hX]
    have hb : ∀ P : Prop, [Decidable P] → |(if P then (1 : ℚ) else 0) - μ| ≤ 1 := by
      intro P _; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    calc _ ≤ |_ * _| := le_abs_self _
      _ = _ := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hb _) (hb _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hcov : ∀ yy : (Fin (L * n) → ℤ) × (Fin (L * n) → ℤ),
      |(∑ a, X a yy.1 * X a yy.2) / Fintype.card (Fin K → Fin L → Fin n → ZMod q)|
        ≤ Hf (D yy) := by
    intro yy
    set Ew : ℚ := ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
      (if DualIn ζ (degS ζ yy.1 yy.2) ξ then bt ^ (supp ξ).card else 0) with hEw
    have hEw0 : 0 ≤ Ew := Finset.sum_nonneg fun ξ _ => by split_ifs <;> positivity
    have hc := cov_le (phiHom h (zc yy.1)) (phiHom h (zc yy.2)) (gset (q := q) γ₂ β v i) hgne
      bt hbt hgset
    have hpair : (∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        ∑ ξ' ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
          if (∀ a, ξ ⬝ᵥ phiHom h (zc yy.1) a + ξ' ⬝ᵥ phiHom h (zc yy.2) a = 0) then
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
    have hmain : |(∑ a, X a yy.1 * X a yy.2) / Fintype.card (Fin K → Fin L → Fin n → ZMod q)|
        ≤ Ew ^ 2 := by
      refine hc.trans ?_
      calc μ ^ 2 * _ ≤ 1 * Ew ^ 2 := by
            refine mul_le_mul (by nlinarith) hpair (Finset.sum_nonneg fun _ _ =>
              Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity) zero_le_one
        _ = Ew ^ 2 := one_mul _
    have htriv : |(∑ a, X a yy.1 * X a yy.2) / Fintype.card (Fin K → Fin L → Fin n → ZMod q)|
        ≤ 1 := by
      rw [abs_div, abs_of_pos hP, div_le_iff₀ hP, one_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ a, |X a yy.1 * X a yy.2| ≤ ∑ _a : Fin K → Fin L → Fin n → ZMod q, (1 : ℚ) := by
            refine Finset.sum_le_sum fun a _ => ?_
            simp only [hX]
            rw [abs_mul]
            have hb : ∀ P : Prop, [Decidable P] → |(if P then (1 : ℚ) else 0) - μ| ≤ 1 := by
              intro P _; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
            calc _ ≤ 1 * 1 := mul_le_mul (hb _) (hb _) (abs_nonneg _) zero_le_one
              _ = 1 := one_mul 1
        _ = _ := by simp
    rcases Nat.eq_zero_or_pos (D yy) with hD | hD
    · have : Ew = 0 := by
        refine Finset.sum_eq_zero fun ξ hξ => ?_
        rw [if_neg]
        intro hd
        have hS : degS ζ yy.1 yy.2 = ∅ := Finset.card_eq_zero.mp hD
        rw [hS] at hd
        exact (Finset.mem_erase.mp hξ).1 (dualIn_empty h.inj ξ hd)
      rw [this] at hmain
      refine hmain.trans ?_
      simp only [Hf]
      linarith [hHf0 (D yy), (show (0:ℚ) ≤ if dm + 1 ≤ D yy then 1 else 0 by
        split_ifs <;> norm_num), (show (0:ℚ) ^ 2 = 0 by norm_num)]
    · by_cases hdm : D yy ≤ dm
      · have hE := hEb _ hD hdm
        refine hmain.trans ?_
        have h1 : Ew ^ 2 ≤ Eb (D yy) ^ 2 := pow_le_pow_left₀ hEw0 hE 2
        refine h1.trans ?_
        simp only [Hf]
        have := Finset.single_le_sum (f := fun e => if e ≤ D yy then Eb e ^ 2 else 0)
          (fun e _ => by split_ifs <;> positivity) (Finset.mem_Icc.mpr ⟨hD, hdm⟩)
        simp only [le_refl, if_true] at this
        linarith [(show (0:ℚ) ≤ if dm + 1 ≤ D yy then 1 else 0 by split_ifs <;> norm_num)]
      · refine htriv.trans ?_
        simp only [Hf, if_pos (by omega : dm + 1 ≤ D yy)]
        linarith [hHf0 (D yy)]
  -- average over `a`, then over pairs
  have hprobs : ∀ e, (((Bx ×ˢ Bx).filter fun yy => e ≤ D yy).card : ℚ) / (Bx ×ˢ Bx).card
      ≤ n.choose e * (((q : ℚ) + 1) / (2 * γ₁ : ℚ) ^ L) ^ e := by
    intro e
    have := deg_card_prob (L := L) h.inj hγ1 hγ e
    unfold prob at this
    refine this.trans (le_of_eq ?_)
    rw [div_pow, ← pow_mul, mul_comm L e]; ring
  have hBB : ((Bx ×ˢ Bx).card : ℚ) = (Bx.card : ℚ) ^ 2 := by rw [card_product]; push_cast; ring
  have hsplit : ∑ yy ∈ Bx ×ˢ Bx, Hf (D yy)
      = ∑ e ∈ Icc 1 dm, Eb e ^ 2 * (((Bx ×ˢ Bx).filter fun yy => e ≤ D yy).card : ℚ)
        + (((Bx ×ˢ Bx).filter fun yy => dm + 1 ≤ D yy).card : ℚ) := by
    simp only [Hf, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    congr 1
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    · rw [Finset.sum_boole]
  have hBsub : B' ×ˢ B' ⊆ Bx ×ˢ Bx := Finset.product_subset_product hB' hB'
  calc avg (fun a : Fin K → Fin L → Fin n → ZMod q => Dev mulmat γ₁ γ₂ β v i B' a ^ 2)
      = (∑ yy ∈ B' ×ˢ B', (∑ a, X a yy.1 * X a yy.2)
          / Fintype.card (Fin K → Fin L → Fin n → ZMod q)) / (Bx.card : ℚ) ^ 2 := by
        unfold avg
        simp_rw [hDev]
        have e1 : ∑ a : Fin K → Fin L → Fin n → ZMod q,
            (∑ y ∈ B', ∑ y' ∈ B', X a y * X a y') / (Bx.card : ℚ) ^ 2
            = (∑ y ∈ B', ∑ y' ∈ B', ∑ a, X a y * X a y') / (Bx.card : ℚ) ^ 2 := by
          rw [← Finset.sum_div]; congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
        have e2 : ∑ yy ∈ B' ×ˢ B', (∑ a, X a yy.1 * X a yy.2)
            / (Fintype.card (Fin K → Fin L → Fin n → ZMod q) : ℚ)
            = (∑ y ∈ B', ∑ y' ∈ B', ∑ a, X a y * X a y')
              / (Fintype.card (Fin K → Fin L → Fin n → ZMod q) : ℚ) := by
          rw [Finset.sum_product, Finset.sum_div]
          exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_div]
        rw [e1, e2]; ring
    _ ≤ (∑ yy ∈ Bx ×ˢ Bx, Hf (D yy)) / (Bx.card : ℚ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc _ ≤ ∑ yy ∈ B' ×ˢ B', |(∑ a, X a yy.1 * X a yy.2)
                / Fintype.card (Fin K → Fin L → Fin n → ZMod q)| :=
              Finset.sum_le_sum fun yy _ => le_abs_self _
          _ ≤ ∑ yy ∈ Bx ×ˢ Bx, |(∑ a, X a yy.1 * X a yy.2)
                / Fintype.card (Fin K → Fin L → Fin n → ZMod q)| :=
              Finset.sum_le_sum_of_subset_of_nonneg hBsub fun _ _ _ => abs_nonneg _
          _ ≤ _ := Finset.sum_le_sum fun yy _ => hcov yy
    _ = ∑ e ∈ Icc 1 dm, Eb e ^ 2 * ((((Bx ×ˢ Bx).filter fun yy => e ≤ D yy).card : ℚ)
          / (Bx ×ˢ Bx).card)
        + (((Bx ×ˢ Bx).filter fun yy => dm + 1 ≤ D yy).card : ℚ) / (Bx ×ˢ Bx).card := by
        rw [hsplit, hBB, add_div, Finset.sum_div]
        congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
    _ ≤ _ := by
        refine add_le_add (Finset.sum_le_sum fun e _ => ?_) (hprobs (dm + 1))
        rw [show ((n.choose e : ℚ) * (((q : ℚ) + 1) / (2 * γ₁ : ℚ) ^ L) ^ e) * Eb e ^ 2
            = Eb e ^ 2 * ((n.choose e : ℚ) * (((q : ℚ) + 1) / (2 * γ₁ : ℚ) ^ L) ^ e) by ring]
        exact mul_le_mul_of_nonneg_left (hprobs e) (sq_nonneg _)

/-! ## The leak in terms of `Dev` -/

lemma one_sub_pR {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) :
    1 - pR q γ₂ β mb = ((mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ) / q := by
  have h1 := hp.β_lt_γ₂
  unfold pR
  rw [sub_sub_cancel]
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (γ₂ - β)), Nat.cast_sub h1.le]
  ring

lemma muP_eq {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ}
    (hv : Bounded β v) (i : ℕ) (hi : i ≤ K * n) :
    muP (q := q) γ₂ β v i = (1 - pR q γ₂ β mb) ^ i := by
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold muP gset
  have : ∀ r : Fin (K * n), ((if (r : ℕ) < i then good (q := q) γ₂ β v r else univ).card : ℚ) / q
      = if (r : ℕ) < i then 1 - pR q γ₂ β mb else 1 := by
    intro r
    split_ifs
    · rw [card_good hp hv r, one_sub_pR hp]
    · rw [card_univ, ZMod.card, div_self hq]
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [Fin.card_filter_val_lt]
  omega

variable {m l : ℕ}

lemma Pset_iff {γ₂ β : ℕ} (M : Matrix (Fin (K * n)) (Fin l) (ZMod q)) (v : Fin (K * n) → ℤ)
    (y : Fin l → ℤ) (i : ℕ) :
    M *ᵥ (fun k => (y k : ZMod q)) ∈ Pset (q := q) γ₂ β v i
      ↔ ∀ r : Fin (K * n), (r : ℕ) < i → ¬ rFails q γ₂ β M v y r := by
  simp only [Pset, gset, Fintype.mem_piFinset]
  refine forall_congr' fun r => ?_
  split_ifs with hr
  · simp [good, rFails, wOf, hr]
  · simp [hr]

/-- **The leak is a sum of prefix deviations.** `rFail i` is "pass on the first `i`, not on the
first `i+1`", and `zFail j` is "`y ∈ Bset j` and pass everywhere". -/
theorem leak_le_Dev {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {u : Fin (L * n) → ℤ} {v : Fin (K * n) → ℤ}
    (hu : Bounded β u) (hv : Bounded β v) (a : Fin K → Fin L → Fin n → ZMod q) :
    leak q γ₁ γ₂ β mb (modMat mulmat a) u v
      ≤ ∑ i : Fin (K * n), (Dev mulmat γ₁ γ₂ β v i (box γ₁ (L * n)) a
          + Dev mulmat γ₁ γ₂ β v (i + 1) (box γ₁ (L * n)) a)
        + ∑ j : Fin (L * n), Dev mulmat γ₁ γ₂ β v (K * n) (Bset γ₁ β u j) a := by
  set M := modMat (K := K) (L := L) mulmat a
  set Bx := box γ₁ (L * n)
  set F : ℕ → Finset (Fin (L * n) → ℤ) := fun k =>
    Bx.filter fun y => M *ᵥ zc y ∈ Pset (q := q) γ₂ β v k
  have hBx : (0 : ℚ) < Bx.card := by
    have := hp.β_lt_γ₁
    rw [card_box_nat]; have : 0 < 2 * γ₁ := by omega
    positivity
  have hDevBx : ∀ k, Dev mulmat γ₁ γ₂ β v k Bx a
      = |((F k).card : ℚ) / Bx.card - muP (q := q) γ₂ β v k| := by
    intro k; unfold Dev; rw [div_self hBx.ne', one_mul]
  unfold leak
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun j _ => ?_)
  · -- `rFail i`
    have hsub : F (i + 1) ⊆ F i := by
      intro y hy
      obtain ⟨hyB, hy'⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨hyB, ?_⟩
      rw [show zc y = fun k => (y k : ZMod q) from rfl, Pset_iff] at hy' ⊢
      exact fun r hr => hy' r (by omega)
    have hev : (Bx.filter fun y => view q γ₁ γ₂ β M u v y = .rFail i) = F i \ F (i + 1) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_sdiff, F]
      rw [view_eq_rFail, I, firstIdx_eq_some]
      rw [show zc y = fun k => (y k : ZMod q) from rfl, Pset_iff, Pset_iff]
      constructor
      · rintro ⟨hy, hfi, hlt⟩
        refine ⟨⟨hy, fun r hr => hlt r (Fin.lt_def.mpr hr)⟩, fun h => ?_⟩
        exact (h.2 i (by omega)) hfi
      · rintro ⟨⟨hy, hpre⟩, hnot⟩
        refine ⟨hy, ?_, fun r hr => hpre r (Fin.lt_def.mp hr)⟩
        by_contra hfi
        apply hnot ⟨hy, fun r hr => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h1 | h1
        · exact hpre r h1
        · have : r = i := Fin.ext h1
          rw [this]; exact hfi
    have hprob : prob Bx (fun y => view q γ₁ γ₂ β M u v y = .rFail i)
        = ((F i).card : ℚ) / Bx.card - ((F (i + 1)).card : ℚ) / Bx.card := by
      unfold prob
      rw [hev, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), sub_div]
    have hgeom : geom (pR q γ₂ β mb) (K * n) (some i)
        = muP (q := q) γ₂ β v i - muP (q := q) γ₂ β v (i + 1) := by
      rw [muP_eq hp hv i (by omega), muP_eq hp hv (i + 1) (by omega)]
      simp only [geom]; ring
    rw [hprob, hgeom, hDevBx, hDevBx]
    calc |((F i).card : ℚ) / Bx.card - ((F (i + 1)).card : ℚ) / Bx.card
          - (muP (q := q) γ₂ β v i - muP (q := q) γ₂ β v (i + 1))|
        = |(((F i).card : ℚ) / Bx.card - muP (q := q) γ₂ β v i)
          - (((F (i + 1)).card : ℚ) / Bx.card - muP (q := q) γ₂ β v (i + 1))| := by ring_nf
      _ ≤ _ := abs_sub _ _
  · -- `zFail j`
    have hev : (Bx.filter fun y => view q γ₁ γ₂ β M u v y = .zFail j)
        = (Bset γ₁ β u j).filter fun y => M *ᵥ zc y ∈ Pset (q := q) γ₂ β v (K * n) := by
      ext y
      simp only [Finset.mem_filter, Bset]
      rw [view_eq_zFail, I, firstIdx_eq_none]
      rw [show zc y = fun k => (y k : ZMod q) from rfl, Pset_iff]
      constructor
      · rintro ⟨hy, hI, hJ⟩; exact ⟨⟨hy, hJ⟩, fun r _ => hI r⟩
      · rintro ⟨⟨hy, hJ⟩, hP⟩; exact ⟨hy, fun r => hP r r.2, hJ⟩
    have hJ := J_dist hp u hu (some j)
    have href : geom (pZ γ₁ β) (L * n) (some j) * geom (pR q γ₂ β mb) (K * n) none
        = ((Bset γ₁ β u j).card : ℚ) / Bx.card * muP (q := q) γ₂ β v (K * n) := by
      rw [← hJ, muP_eq hp hv (K * n) le_rfl]
      simp only [geom]
      unfold prob; rfl
    unfold prob
    rw [hev, href]
    unfold Dev
    exact le_rfl

/-! ## Averaging over the matrix -/

/-- The integer inequality checked by the kernel: `ρ = rn/rd`, `E_b(d) = ENr / Dc^(Kn)`. -/
def numR (e q n K Bd Dc rn rd dm : ℕ) : ℕ :=
  sumF (fun d => if 1 ≤ d then chooseC n d * rn ^ d * rd ^ (dm + 1 - d)
      * ENr e q n K Bd Dc d ^ 2 else 0) (dm + 1)
    + chooseC n (dm + 1) * rn ^ (dm + 1) * Dc ^ (2 * (K * n))

/-- **Expected deviation.** If the kernel inequality holds with `2^(2j)`, then for every prefix
length `i` and every sub-event `B'` of the box, `E_A Dev ≤ 2^-j`. -/
theorem avg_Dev_le {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {cz : ZMod q} (hwz : ∀ k, ζ k ^ n = cz) (hn : 0 < n)
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v)
    (hγ : 2 * γ₁ ≤ q) (e dm j : ℕ)
    (hnum : 2 ^ (2 * j) * numR e q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        (q + 1) ((2 * γ₁) ^ L) dm
      ≤ ((2 * γ₁) ^ L) ^ (dm + 1) * (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n)))
    (i : ℕ) (B' : Finset (Fin (L * n) → ℤ)) (hB' : B' ⊆ box γ₁ (L * n)) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q => Dev mulmat γ₁ γ₂ β v i B' a) ≤ 1 / 2 ^ j := by
  set Dc := mb * (2 * (γ₂ - β) - 1) with hDc
  set Bd := q - Dc with hBd
  have hDcq : Dc ≤ q := pass_le_q hp
  have hDc0 : 0 < Dc := by
    have h1 := hp.mb_pos; have h2 := hp.β_lt_γ₂
    exact Nat.mul_pos h1 (by omega)
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hγ1 : 0 < γ₁ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  have hDc' : (0 : ℚ) < Dc := by exact_mod_cast hDc0
  set bt : ℚ := (Bd : ℚ) / Dc
  have hgood : ∀ r, ((good (q := q) γ₂ β v r).card : ℚ) = Dc := fun r => by
    rw [card_good hp hv r]
  have hbad : ∀ r, ((q : ℚ) - (good (q := q) γ₂ β v r).card) ≤ bt * (good (q := q) γ₂ β v r).card := by
    intro r; rw [hgood]
    simp only [bt, hBd]; rw [Nat.cast_sub hDcq]; field_simp; rfl
  have hEb : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then bt ^ (supp ξ).card else 0)
        ≤ (ENr e q n K Bd Dc S.card : ℚ) / (Dc : ℚ) ^ (K * n) :=
    fun S _ _ => (wsum_le h.inj h.ne0 hwz S (by positivity)).trans
      (wcount_le_rows hn e q Bd Dc S.card hq1 hDc0)
  have hsq := Dsq_le (K := K) h (v := v) hγ1 hγ B' hB' i bt (by positivity) hbad dm
    (fun d => (ENr e q n K Bd Dc d : ℚ) / (Dc : ℚ) ^ (K * n)) hEb
  -- the numeric side
  set rd : ℕ := (2 * γ₁) ^ L
  have hrd : (0 : ℚ) < rd := by positivity
  have hρ : ((q : ℚ) + 1) / (2 * γ₁ : ℚ) ^ L = ((q + 1 : ℕ) : ℚ) / rd := by
    simp only [rd]; push_cast; ring
  rw [hρ] at hsq
  set η : ℚ := 1 / 2 ^ j
  have hη : 0 < η := by positivity
  have hS : ∑ d ∈ Icc 1 dm, ((n.choose d : ℚ) * (((q + 1 : ℕ) : ℚ) / rd) ^ d)
        * ((ENr e q n K Bd Dc d : ℚ) / (Dc : ℚ) ^ (K * n)) ^ 2
      + n.choose (dm + 1) * (((q + 1 : ℕ) : ℚ) / rd) ^ (dm + 1) ≤ η ^ 2 := by
    have hnumQ := (Nat.cast_le (α := ℚ)).mpr hnum
    unfold numR at hnumQ
    rw [sumF_eq] at hnumQ
    push_cast at hnumQ
    simp only [Nat.cast_ite, Nat.cast_zero, chooseC_eq] at hnumQ
    rw [sumF_ite_Icc] at hnumQ
    have hDn : (0 : ℚ) < (Dc : ℚ) ^ (K * n) := by positivity
    have hsplit : ∀ d, d ≤ dm + 1 → (rd : ℚ) ^ (dm + 1) = (rd : ℚ) ^ d * (rd : ℚ) ^ (dm + 1 - d) :=
      fun d hd => by rw [← pow_add]; congr 1; omega
    have hlhs : ∑ d ∈ Icc 1 dm, ((n.choose d : ℚ) * (((q + 1 : ℕ) : ℚ) / rd) ^ d)
          * ((ENr e q n K Bd Dc d : ℚ) / (Dc : ℚ) ^ (K * n)) ^ 2
        + n.choose (dm + 1) * (((q + 1 : ℕ) : ℚ) / rd) ^ (dm + 1)
        = (∑ d ∈ Icc 1 dm, (n.choose d : ℚ) * ((q : ℚ) + 1) ^ d * (rd : ℚ) ^ (dm + 1 - d)
            * (ENr e q n K Bd Dc d : ℚ) ^ 2
          + (n.choose (dm + 1) : ℚ) * ((q : ℚ) + 1) ^ (dm + 1) * (Dc : ℚ) ^ (2 * (K * n)))
          / ((rd : ℚ) ^ (dm + 1) * (Dc : ℚ) ^ (2 * (K * n))) := by
      rw [add_div, Finset.sum_div]
      congr 1
      · refine Finset.sum_congr rfl fun d hd => ?_
        rw [hsplit d (by have := (Finset.mem_Icc.mp hd).2; omega)]
        rw [show 2 * (K * n) = (K * n) * 2 by ring, pow_mul]
        push_cast
        simp only [div_pow]
        field_simp
        ring
      · push_cast; rw [div_pow]; field_simp
    rw [hlhs, div_le_iff₀ (by positivity)]
    simp only [η, one_div, inv_pow]
    rw [← pow_mul, mul_comm j 2]
    rw [show ((2 : ℚ) ^ (2 * j))⁻¹ * ((rd : ℚ) ^ (dm + 1) * (Dc : ℚ) ^ (2 * (K * n)))
        = ((rd : ℚ) ^ (dm + 1) * (Dc : ℚ) ^ (2 * (K * n))) / 2 ^ (2 * j) by ring]
    rw [le_div_iff₀ (by positivity)]
    simp only [rd] at hnumQ ⊢
    push_cast at hnumQ ⊢
    linarith
  have hsq' := hsq.trans hS
  -- AM-GM pointwise
  have hpt : ∀ x : ℚ, |x| ≤ (x ^ 2 / η + η) / 2 := by
    intro x
    have : 0 ≤ (|x| - η) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
    rw [sub_sq, sq_abs] at this
    have e1 : (x ^ 2 - 2 * |x| * η + η ^ 2) / η = x ^ 2 / η - 2 * |x| + η := by field_simp
    linarith
  calc avg (fun a : Fin K → Fin L → Fin n → ZMod q => Dev mulmat γ₁ γ₂ β v i B' a)
      ≤ avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
          (Dev mulmat γ₁ γ₂ β v i B' a ^ 2 / η + η) / 2) := by
        refine avg_mono fun a => ?_
        exact (le_abs_self _).trans (hpt (Dev mulmat γ₁ γ₂ β v i B' a))
    _ = (avg (fun a : Fin K → Fin L → Fin n → ZMod q => Dev mulmat γ₁ γ₂ β v i B' a ^ 2) / η
          + η) / 2 := by
        unfold avg
        rw [Finset.sum_div]
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, card_univ,
          nsmul_eq_mul]
        have : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
          exact_mod_cast Fintype.card_pos
        field_simp
    _ ≤ (η ^ 2 / η + η) / 2 := by
        have := div_le_div_of_nonneg_right hsq' hη.le
        linarith
    _ = η := by field_simp; ring

/-- **The leak on average over the matrix**, by the product-Fourier bound:
`E_A leak ≤ (2·K n + L n) / 2^j` whenever the kernel inequality holds with `2^(2j)`. -/
theorem leak_avg_fourier {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {cz : ZMod q} (hwz : ∀ k, ζ k ^ n = cz) (hn : 0 < n)
    {γ₁ γ₂ β mb : ℕ} (hp : Params q γ₁ γ₂ β mb) {u : Fin (L * n) → ℤ} {v : Fin (K * n) → ℤ}
    (hu : Bounded β u) (hv : Bounded β v) (hγ : 2 * γ₁ ≤ q) (e dm j : ℕ)
    (hnum : 2 ^ (2 * j) * numR e q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        (q + 1) ((2 * γ₁) ^ L) dm
      ≤ ((2 * γ₁) ^ L) ^ (dm + 1) * (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n))) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q => leak q γ₁ γ₂ β mb (modMat mulmat a) u v)
      ≤ (2 * (K * n) + L * n : ℕ) / 2 ^ j := by
  have hD : ∀ i (B' : Finset (Fin (L * n) → ℤ)), B' ⊆ box γ₁ (L * n) →
      avg (fun a : Fin K → Fin L → Fin n → ZMod q => Dev mulmat γ₁ γ₂ β v i B' a) ≤ 1 / 2 ^ j :=
    fun i B' hB' => avg_Dev_le h hwz hn hp hv hγ e dm j hnum i B' hB'
  refine (avg_mono fun a => leak_le_Dev hp hu hv a).trans ?_
  rw [avg_add, avg_finset_sum, avg_finset_sum]
  have h1 : ∑ i : Fin (K * n), avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      Dev mulmat γ₁ γ₂ β v i (box γ₁ (L * n)) a + Dev mulmat γ₁ γ₂ β v (i + 1) (box γ₁ (L * n)) a)
      ≤ ∑ _i : Fin (K * n), 2 * (1 / 2 ^ j : ℚ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [avg_add]
    linarith [hD i _ subset_rfl, hD (i + 1) _ subset_rfl]
  have h2 : ∑ jj : Fin (L * n), avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      Dev mulmat γ₁ γ₂ β v (K * n) (Bset γ₁ β u jj) a) ≤ ∑ _jj : Fin (L * n), (1 / 2 ^ j : ℚ) :=
    Finset.sum_le_sum fun jj _ => hD _ _ (Finset.filter_subset _ _)
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

end RejOrder

end

end FourierLeak

section MLDSA
/-!
# The three ML-DSA parameter sets

For `A` uniform in `R_q^{K×L}` with `R_q = Z_q[X]/(X^256 + 1)`, the leak of one signing attempt is
negligible on average over `A`. The numerical inequalities are checked by kernel evaluation.
-/

open Finset Matrix

noncomputable section

namespace RejOrder

/-- ML-DSA-44: q = 8380417, γ₁ = 2^17, γ₂ = 95232, β = 78, mb = 44. -/
theorem params_mldsa44 : Params 8380417 (2 ^ 17) 95232 78 44 := by constructor <;> norm_num
/-- ML-DSA-65: q = 8380417, γ₁ = 2^19, γ₂ = 261888, β = 196, mb = 16. -/
theorem params_mldsa65 : Params 8380417 (2 ^ 19) 261888 196 16 := by constructor <;> norm_num
/-- ML-DSA-87: q = 8380417, γ₁ = 2^19, γ₂ = 261888, β = 120, mb = 16. -/
theorem params_mldsa87 : Params 8380417 (2 ^ 19) 261888 120 16 := by constructor <;> norm_num

set_option maxRecDepth 100000

/-- The kernel-checked inequality for ML-DSA-44. -/
theorem numR_44 : 2 ^ (2 * 417) * numR 330 8380417 256 4 (8380417 - 44 * (2 * (95232 - 78) - 1))
    (44 * (2 * (95232 - 78) - 1)) (8380417 + 1) ((2 * 2 ^ 17) ^ 4) 19
  ≤ ((2 * 2 ^ 17) ^ 4) ^ (19 + 1) * (44 * (2 * (95232 - 78) - 1)) ^ (2 * (4 * 256)) := by
  decide +kernel

/-- **ML-DSA-44** -/
theorem leak_mldsa44 {u : Fin (4 * 256) → ℤ} {v : Fin (4 * 256) → ℤ}
    (hu : Bounded 78 u) (hv : Bounded 78 v) :
    avg (fun A : Matrix (Fin 4) (Fin 4) Rq => leak 8380417 (2 ^ 17) 95232 78 44 (ringMat A) u v)
      ≤ 1 / 2 ^ 405 := by
  refine (avg_ringMat fun M => leak 8380417 (2 ^ 17) 95232 78 44 M u v).trans_le ?_
  refine (leak_avg_fourier isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hu hv
    (by norm_num) 330 19 417 numR_44).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    show 417 = 12 + 405 from rfl, pow_add]
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- The kernel-checked inequality for ML-DSA-65. -/
theorem numR_65 : 2 ^ (2 * 560) * numR 330 8380417 256 6 (8380417 - 16 * (2 * (261888 - 196) - 1))
    (16 * (2 * (261888 - 196) - 1)) (8380417 + 1) ((2 * 2 ^ 19) ^ 5) 20
  ≤ ((2 * 2 ^ 19) ^ 5) ^ (20 + 1) * (16 * (2 * (261888 - 196) - 1)) ^ (2 * (6 * 256)) := by
  decide +kernel

/-- **ML-DSA-65** -/
theorem leak_mldsa65 {u : Fin (5 * 256) → ℤ} {v : Fin (6 * 256) → ℤ}
    (hu : Bounded 196 u) (hv : Bounded 196 v) :
    avg (fun A : Matrix (Fin 6) (Fin 5) Rq => leak 8380417 (2 ^ 19) 261888 196 16 (ringMat A) u v)
      ≤ 1 / 2 ^ 547 := by
  refine (avg_ringMat fun M => leak 8380417 (2 ^ 19) 261888 196 16 M u v).trans_le ?_
  refine (leak_avg_fourier isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hu hv
    (by norm_num) 330 20 560 numR_65).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    show 560 = 13 + 547 from rfl, pow_add]
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- The kernel-checked inequality for ML-DSA-87. -/
theorem numR_87 : 2 ^ (2 * 742) * numR 330 8380417 256 8 (8380417 - 16 * (2 * (261888 - 120) - 1))
    (16 * (2 * (261888 - 120) - 1)) (8380417 + 1) ((2 * 2 ^ 19) ^ 7) 23
  ≤ ((2 * 2 ^ 19) ^ 7) ^ (23 + 1) * (16 * (2 * (261888 - 120) - 1)) ^ (2 * (8 * 256)) := by
  decide +kernel

/-- **ML-DSA-87** -/
theorem leak_mldsa87 {u : Fin (7 * 256) → ℤ} {v : Fin (8 * 256) → ℤ}
    (hu : Bounded 120 u) (hv : Bounded 120 v) :
    avg (fun A : Matrix (Fin 8) (Fin 7) Rq => leak 8380417 (2 ^ 19) 261888 120 16 (ringMat A) u v)
      ≤ 1 / 2 ^ 729 := by
  refine (avg_ringMat fun M => leak 8380417 (2 ^ 19) 261888 120 16 M u v).trans_le ?_
  refine (leak_avg_fourier isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hu hv
    (by norm_num) 330 23 742 numR_87).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    show 742 = 13 + 729 from rfl, pow_add]
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end RejOrder

end
end MLDSA

section Headline
/-!
# Many attempts, and how many matrices are bad

An attacker who watches many signing attempts sees one view per attempt. For fixed shifts, the
statistical distance of the combined view from a secret-independent reference is at most the sum
of the per-attempt leaks (a hybrid argument, not formalised here). With random challenges the
shifts are random too, which is covered by giving the attempts weights. The theorems below bound
the fraction of matrices for which this weighted sum of leaks is large.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q γ₁ γ₂ β mb : ℕ} [NeZero q] {l m : ℕ} {P : Type*} [Fintype P]

lemma leak_nonneg (M : Matrix (Fin m) (Fin l) (ZMod q)) (u : Fin l → ℤ) (v : Fin m → ℤ) :
    0 ≤ leak q γ₁ γ₂ β mb M u v := by
  unfold leak; positivity

/-- **Few bad matrices.** Suppose the leak of one attempt is at most `ε` on average over the
matrix, for every pair of bounded shifts. Take any finite family of bounded shifts `(u i, v i)`
with nonnegative weights `w i` of total weight `W` (for instance `Q` attempts, each with a
challenge drawn from a finite set). Then the fraction of matrices for which the weighted sum of
leaks is at least `η` is at most `W·ε/η`. -/
theorem bad_frac {mat : P → Matrix (Fin m) (Fin l) (ZMod q)} {ε : ℚ}
    (hε : ∀ u v, Bounded β u → Bounded β v →
      avg (fun a => leak q γ₁ γ₂ β mb (mat a) u v) ≤ ε)
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (us : ι → Fin l → ℤ) (vs : ι → Fin m → ℤ)
    (hus : ∀ i, Bounded β (us i)) (hvs : ∀ i, Bounded β (vs i)) {η : ℚ} (hη : 0 < η) :
    ((univ.filter fun a => η ≤ ∑ i, w i * leak q γ₁ γ₂ β mb (mat a) (us i) (vs i)).card : ℚ)
        / Fintype.card P
      ≤ (∑ i, w i) * ε / η := by
  apply markov (fun a => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (leak_nonneg _ _ _)) hη
  rw [avg_finset_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [avg_mul_left]
  exact mul_le_mul_of_nonneg_left (hε _ _ (hus i) (hvs i)) (hw i)

/-- **ML-DSA-44, many attempts.** -/
theorem bad_frac_mldsa44 {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (us : ι → Fin (4 * 256) → ℤ) (vs : ι → Fin (4 * 256) → ℤ)
    (hus : ∀ i, Bounded 78 (us i)) (hvs : ∀ i, Bounded 78 (vs i)) {η : ℚ} (hη : 0 < η) :
    ((univ.filter fun A : Matrix (Fin 4) (Fin 4) Rq => η ≤ ∑ i, w i *
        leak 8380417 (2 ^ 17) 95232 78 44 (ringMat A) (us i) (vs i)).card : ℚ)
        / Fintype.card (Matrix (Fin 4) (Fin 4) Rq)
      ≤ (∑ i, w i) * (1 / 2 ^ 405) / η :=
  bad_frac (fun _ _ hu hv => leak_mldsa44 hu hv) w hw us vs hus hvs hη

/-- **ML-DSA-65, many attempts.** -/
theorem bad_frac_mldsa65 {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (us : ι → Fin (5 * 256) → ℤ) (vs : ι → Fin (6 * 256) → ℤ)
    (hus : ∀ i, Bounded 196 (us i)) (hvs : ∀ i, Bounded 196 (vs i)) {η : ℚ} (hη : 0 < η) :
    ((univ.filter fun A : Matrix (Fin 6) (Fin 5) Rq => η ≤ ∑ i, w i *
        leak 8380417 (2 ^ 19) 261888 196 16 (ringMat A) (us i) (vs i)).card : ℚ)
        / Fintype.card (Matrix (Fin 6) (Fin 5) Rq)
      ≤ (∑ i, w i) * (1 / 2 ^ 547) / η :=
  bad_frac (fun _ _ hu hv => leak_mldsa65 hu hv) w hw us vs hus hvs hη

/-- **ML-DSA-87, many attempts.** -/
theorem bad_frac_mldsa87 {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (us : ι → Fin (7 * 256) → ℤ) (vs : ι → Fin (8 * 256) → ℤ)
    (hus : ∀ i, Bounded 120 (us i)) (hvs : ∀ i, Bounded 120 (vs i)) {η : ℚ} (hη : 0 < η) :
    ((univ.filter fun A : Matrix (Fin 8) (Fin 7) Rq => η ≤ ∑ i, w i *
        leak 8380417 (2 ^ 19) 261888 120 16 (ringMat A) (us i) (vs i)).card : ℚ)
        / Fintype.card (Matrix (Fin 8) (Fin 7) Rq)
      ≤ (∑ i, w i) * (1 / 2 ^ 729) / η :=
  bad_frac (fun _ _ hu hv => leak_mldsa87 hu hv) w hw us vs hus hvs hη

end RejOrder

end
end Headline

#print axioms RejOrder.indist
#print axioms RejOrder.leak_mldsa44
#print axioms RejOrder.leak_mldsa65
#print axioms RejOrder.leak_mldsa87
#print axioms RejOrder.bad_frac_mldsa44
#print axioms RejOrder.bad_frac_mldsa65
#print axioms RejOrder.bad_frac_mldsa87
