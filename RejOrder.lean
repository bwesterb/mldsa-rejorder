import Mathlib

/-!
# The order of rejection checks in circl's ML-DSA leaks nothing through timing

One signing attempt, with the challenge fixed. `leak M u v` is the total distance between the
probabilities of the rejection views and reference values that do not depend on the secret
shifts `u = c·s₁`, `v = c·s₂`.

* `indist`: for any matrix, two secrets with the same public value cannot be told apart from the
  timing view with advantage more than the sum of their leaks.
* `leak_mldsa44`, `leak_mldsa65`, `leak_mldsa87`: for `A` uniform in `R_q^{K×L}`, the leak is at
  most `2^-239`, `2^-291`, `2^-380` on average over `A`. The first two use the capped second
  moment (`second_moment_cap`, `leak_avg_module_cap`), which splits the pairs `(y, y')` on the
  number of NTT slots where they are linearly dependent; the third uses `leak_avg_module`.

Sections, in order: `Defs` (the model), `Layer0` (exact counting), `Layer1` (accepted attempts),
`Layer2` (Bonferroni), `Leak`, `SecondMoment`, `Uncertainty`, `Module`, `ModuleProb`,
`ModuleCount`, `Profile`, `ModuleMain`, `Negacyclic`, `Numeric`, `MLDSA`.
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

lemma prob_nonneg (B : Finset α) (P : α → Prop) [DecidablePred P] : 0 ≤ prob B P := by
  unfold prob; positivity

lemma prob_le_one (B : Finset α) (P : α → Prop) [DecidablePred P] : prob B P ≤ 1 := by
  unfold prob
  rcases Nat.eq_zero_or_pos B.card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_filter_le _ _

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

lemma prob_and {α : Type*} (B : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    prob B (fun y => P y ∧ Q y) = prob B Q * prob (B.filter Q) P := by
  unfold prob
  rw [Finset.filter_filter]
  have hc : (B.filter fun y => P y ∧ Q y) = (B.filter fun y => Q y ∧ P y) :=
    Finset.filter_congr fun _ _ => and_comm
  rw [hc]
  by_cases h : ((B.filter Q).card : ℚ) = 0
  · have h0 : (B.filter Q).card = 0 := by exact_mod_cast h
    have : (B.filter fun y => Q y ∧ P y).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← h0]
      apply Finset.card_le_card
      intro y; simp only [Finset.mem_filter]; tauto
    simp [this, h]
  · field_simp

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

section Layer2
/-!
# Layer 2: Bonferroni truncation

The first-failure index of the r₀ check is compared with its distribution under uniform `w` by a
Bonferroni truncation of inclusion–exclusion, run for `y` uniform on a set `B` and for `w` uniform
on `(ZMod q)^m`. The kept terms are "every coordinate in `T` fails" events with `|T| ≤ s`; their
deviations `dev T` are the only input about the matrix.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## Truncated alternating binomial sums -/

/-- `∑_{k ≤ t} (-1)^k C(N, k)`. -/
def alt (N t : ℕ) : ℚ := ∑ k ∈ range (t + 1), (-1 : ℚ) ^ k * (N.choose k)

lemma alt_zero (t : ℕ) : alt 0 t = 1 := by
  unfold alt
  rw [Finset.sum_range_succ']
  simp

lemma alt_succ (n t : ℕ) : alt (n + 1) t = (-1) ^ t * (n.choose t) := by
  induction t with
  | zero => simp [alt]
  | succ t ih =>
    unfold alt at *
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    push_cast; ring

/-- The Bonferroni inequality, in numbers. -/
lemma bonf_num (N t : ℕ) : |(if N = 0 then 1 else 0 : ℚ) - alt N t| ≤ N.choose (t + 1) := by
  rcases N with _ | n
  · simp [alt_zero]
  · rw [alt_succ, if_neg (Nat.succ_ne_zero n), zero_sub, abs_neg, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, one_mul, Nat.abs_cast, Nat.choose_succ_succ]
    push_cast
    linarith [(Nat.cast_nonneg (n.choose (t + 1)) : (0 : ℚ) ≤ _)]

lemma sum_range_choose_ind (N t : ℕ) :
    ∑ k ∈ range (N + 1), (N.choose k) • (if k ≤ t then (-1 : ℚ) ^ k else 0) = alt N t := by
  set h : ℕ → ℚ := fun k => if k ≤ t then (-1 : ℚ) ^ k * N.choose k else 0 with hh
  have e1 : ∑ k ∈ range (N + 1), (N.choose k) • (if k ≤ t then (-1 : ℚ) ^ k else 0)
      = ∑ k ∈ range (N + 1), h k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hh, nsmul_eq_mul]
    split_ifs <;> ring
  have e2 : ∑ k ∈ range (N + 1), h k = ∑ k ∈ range (N + t + 1), h k := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp only [hh, Nat.choose_eq_zero_of_lt (by omega : N < k)]
    simp
  have e3 : alt N t = ∑ k ∈ range (N + t + 1), h k := by
    unfold alt
    rw [Finset.sum_congr rfl (g := h) (fun k hk => by
      simp only [Finset.mem_range] at hk; simp [hh, (by omega : k ≤ t)])]
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp only [if_neg (by omega : ¬ k ≤ t)]
  rw [e1, e2, e3]

lemma powerset_alt {ι : Type*} [DecidableEq ι] (S : Finset ι) (t : ℕ) :
    ∑ T ∈ S.powerset with T.card ≤ t, (-1 : ℚ) ^ T.card = alt S.card t := by
  rw [Finset.sum_filter]
  have := Finset.sum_powerset_apply_card (fun k => if k ≤ t then (-1 : ℚ) ^ k else 0) (x := S)
  rw [this, sum_range_choose_ind]

/-! ## Abstract Bonferroni truncation -/

section Abstract

variable {α ι : Type*} [DecidableEq ι] (f : ι → α → Prop) [∀ j, DecidablePred (f j)]

lemma bonf_point (A Xs : Finset ι) (t : ℕ) (y : α) :
    |(if (∀ j ∈ A, ¬ f j y) ∧ (∀ j ∈ Xs, f j y) then 1 else 0 : ℚ)
      - ∑ T ∈ A.powerset with T.card ≤ t,
          (-1 : ℚ) ^ T.card * (if (∀ j ∈ T, f j y) ∧ (∀ j ∈ Xs, f j y) then 1 else 0)|
    ≤ ∑ T ∈ A.powersetCard (t + 1), (if ∀ j ∈ T, f j y then 1 else 0 : ℚ) := by
  set S := A.filter (fun j => f j y) with hS
  have hR : ∑ T ∈ A.powersetCard (t + 1), (if ∀ j ∈ T, f j y then 1 else 0 : ℚ)
      = (S.card.choose (t + 1) : ℚ) := by
    rw [Finset.sum_boole, ← Finset.card_powersetCard]
    congr 2
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard, hS, Finset.subset_iff]
    constructor
    · rintro ⟨⟨hA, hc⟩, hf⟩; exact ⟨fun j hj => ⟨hA hj, hf j hj⟩, hc⟩
    · rintro ⟨h, hc⟩; exact ⟨⟨fun j hj => (h hj).1, hc⟩, fun j hj => (h hj).2⟩
  rw [hR]
  by_cases hX : ∀ j ∈ Xs, f j y
  · simp only [eq_true hX, and_true]
    have hK : ∑ T ∈ A.powerset with T.card ≤ t,
        (-1 : ℚ) ^ T.card * (if ∀ j ∈ T, f j y then 1 else 0) = alt S.card t := by
      rw [← powerset_alt]
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_filter]
      congr 1
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, hS, Finset.subset_iff]
      constructor
      · rintro ⟨hA, hc, hf⟩; exact ⟨fun j hj => ⟨hA hj, hf j hj⟩, hc⟩
      · rintro ⟨h, hc⟩; exact ⟨fun j hj => (h hj).1, hc, fun j hj => (h hj).2⟩
    rw [hK]
    have hG : (∀ j ∈ A, ¬ f j y) ↔ S.card = 0 := by
      rw [Finset.card_eq_zero, hS, Finset.filter_eq_empty_iff]
    have : (if ∀ j ∈ A, ¬ f j y then 1 else 0 : ℚ) = if S.card = 0 then 1 else 0 := by
      simp only [hG]
    rw [this]
    exact bonf_num S.card t
  · simp only [eq_false hX, and_false, if_false, mul_zero, Finset.sum_const_zero, sub_zero, abs_zero]
    positivity

lemma prob_eq_sum (Ω : Finset α) (P : α → Prop) [DecidablePred P] :
    prob Ω P = (∑ y ∈ Ω, if P y then (1 : ℚ) else 0) / Ω.card := by
  unfold prob; rw [Finset.sum_boole]

/-- Bonferroni truncation of inclusion–exclusion for the uniform distribution on `Ω`. -/
lemma bonf (Ω : Finset α) (A Xs : Finset ι) (t : ℕ) :
    |prob Ω (fun y => (∀ j ∈ A, ¬ f j y) ∧ (∀ j ∈ Xs, f j y))
      - ∑ T ∈ A.powerset with T.card ≤ t,
          (-1 : ℚ) ^ T.card * prob Ω (fun y => (∀ j ∈ T, f j y) ∧ (∀ j ∈ Xs, f j y))|
    ≤ ∑ T ∈ A.powersetCard (t + 1), prob Ω (fun y => ∀ j ∈ T, f j y) := by
  have hn : (0 : ℚ) ≤ Ω.card := Nat.cast_nonneg _
  simp only [prob_eq_sum]
  rw [← Finset.sum_div]
  simp only [mul_div_assoc', ← Finset.sum_div]
  rw [← sub_div, abs_div, abs_of_nonneg hn]
  apply div_le_div_of_nonneg_right _ hn
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := A.powerset.filter _), ← Finset.sum_sub_distrib,
    Finset.sum_comm (s := A.powersetCard _)]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun y _ => bonf_point f A Xs t y)

end Abstract

variable {q γ₁ γ₂ β mb : ℕ} [NeZero q] {l m : ℕ}

/-! ### Single-coordinate facts about the r₀ check under uniform w -/

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

lemma pR_eq (hp : Params q γ₁ γ₂ β mb) :
    (((q - mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ)) / q = pR q γ₂ β mb := by
  have hβ := hp.β_lt_γ₂
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold pR
  rw [Nat.cast_sub (pass_le_q hp)]
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (γ₂ - β)), Nat.cast_sub hβ.le]
  field_simp

lemma pR_nonneg (hp : Params q γ₁ γ₂ β mb) : 0 ≤ pR q γ₂ β mb := by
  rw [← pR_eq hp]; positivity

lemma prob_fail_univ (hp : Params q γ₁ γ₂ β mb) (c : ℤ) (hc : |c| ≤ β) :
    prob (univ : Finset (ZMod q)) (fun x => (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - c|)
      = pR q γ₂ β mb := by
  unfold prob
  rw [fail_card hp c hc, Finset.card_univ, ZMod.card, pR_eq hp]

lemma prob_pass_univ (hp : Params q γ₁ γ₂ β mb) (c : ℤ) (hc : |c| ≤ β) :
    prob (univ : Finset (ZMod q)) (fun x => ¬ ((γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - c|))
      = 1 - pR q γ₂ β mb := by
  rw [prob_not _ (Finset.univ_nonempty (α := ZMod q)), prob_fail_univ hp c hc]

/-! ### The two families of coordinate events -/

variable (q γ₂ β) in
/-- Failure of coordinate `j` for `w` itself (the uniform side). -/
def fU (v : Fin m → ℤ) (j : Fin m) (w : Fin m → ZMod q) : Prop :=
  (γ₂ : ℤ) - β ≤ |lowBits q γ₂ (w j) - v j|

instance (v : Fin m → ℤ) (j : Fin m) : DecidablePred (fU q γ₂ β v j) :=
  fun _ => by unfold fU; infer_instance

variable (q γ₂ β) in
/-- Failure of coordinate `j` for `w = M·y` (the real side). -/
def fR (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (j : Fin m) (y : Fin l → ℤ) :
    Prop :=
  rFails q γ₂ β M v y j

instance (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (j : Fin m) :
    DecidablePred (fR q γ₂ β M v j) :=
  fun _ => by unfold fR; infer_instance

lemma prob_univ_allF (hp : Params q γ₁ γ₂ β mb) {v : Fin m → ℤ} (hv : Bounded β v)
    (U : Finset (Fin m)) :
    prob (univ : Finset (Fin m → ZMod q)) (fun w => ∀ j ∈ U, fU q γ₂ β v j w)
      = pR q γ₂ β mb ^ U.card := by
  rw [← Fintype.piFinset_univ]
  rw [prob_pi _ (fun j x => j ∈ U → (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v j|) _
    (fun w _ => by unfold fU; exact ⟨fun h j hj => h j hj, fun h j hj => h j hj⟩)]
  have : ∀ j : Fin m, prob (univ : Finset (ZMod q))
      (fun x => j ∈ U → (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v j|)
      = if j ∈ U then pR q γ₂ β mb else 1 := by
    intro j
    split_ifs with hj
    · rw [← prob_fail_univ hp (v j) (hv j)]
      exact prob_congr _ fun x _ => by simp [hj]
    · rw [← prob_true _ (Finset.univ_nonempty (α := ZMod q))]
      exact prob_congr _ fun x _ => by simp [hj]
  simp_rw [this]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-! ### The first-failure event in terms of coordinate events -/

/-- Indices that must pass for `I = o`. -/
def passSet : Option (Fin m) → Finset (Fin m)
  | some i => univ.filter (· < i)
  | none => univ

/-- Indices that must fail for `I = o`. -/
def failSet : Option (Fin m) → Finset (Fin m)
  | some i => {i}
  | none => ∅

lemma failSet_card (o : Option (Fin m)) : (failSet o).card ≤ 1 := by
  cases o <;> simp [failSet]

/-- `I = o` in terms of coordinate events, for any family of coordinate events. -/
lemma firstIdx_eq_iff {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (o : Option (Fin n)) :
    firstIdx P = o ↔ (∀ j ∈ passSet o, ¬ P j) ∧ (∀ j ∈ failSet o, P j) := by
  cases o with
  | none => simp [passSet, failSet, firstIdx_eq_none]
  | some i =>
    rw [firstIdx_eq_some]
    simp only [passSet, failSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, forall_eq]
    exact and_comm

lemma prob_univ_geom (hp : Params q γ₁ γ₂ β mb) {v : Fin m → ℤ} (hv : Bounded β v)
    (o : Option (Fin m)) :
    prob (univ : Finset (Fin m → ZMod q))
        (fun w => (∀ j ∈ passSet o, ¬ fU q γ₂ β v j w) ∧ (∀ j ∈ failSet o, fU q γ₂ β v j w))
      = geom (pR q γ₂ β mb) m o := by
  rw [← Fintype.piFinset_univ]
  cases o with
  | none =>
    rw [prob_pi _ (fun j x => ¬ ((γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v j|)) _
      (fun w _ => by simp [passSet, failSet, fU])]
    simp_rw [prob_pass_univ hp _ (hv _)]
    simp [geom]
  | some i =>
    rw [prob_pi _ (fun j x => (j < i → ¬ ((γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v j|)) ∧
        (j = i → (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v j|)) _ (fun w _ => by
      simp only [passSet, failSet, fU, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, forall_eq]
      constructor
      · rintro ⟨h1, h2⟩ j; exact ⟨h1 j, fun hj => hj ▸ h2⟩
      · intro h; exact ⟨fun j => (h j).1, (h i).2 rfl⟩)]
    have : ∀ j : Fin m, prob (univ : Finset (ZMod q)) (fun x =>
        (j < i → ¬ ((γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v j|)) ∧
        (j = i → (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v j|))
        = if j < i then 1 - pR q γ₂ β mb else if j = i then pR q γ₂ β mb else 1 := by
      intro j
      split_ifs with h1 h2
      · rw [← prob_pass_univ hp (v j) (hv j)]
        exact prob_congr _ fun t _ => by simp [h1, ne_of_lt h1]
      · rw [← prob_fail_univ hp (v j) (hv j)]
        exact prob_congr _ fun t _ => by simp [h2]
      · rw [← prob_true _ (Finset.univ_nonempty (α := ZMod q))]
        exact prob_congr _ fun t _ => by simp [h1, h2]
    simp_rw [this]
    rw [prod_geom_some]
    rfl

/-! ## Bonferroni with a deviation per coordinate set -/

variable (q γ₂ β mb) in
/-- How far "every coordinate in `T` fails the r₀ check" is from its probability `p_R^|T|` under
uniform `w`, for `y` uniform on `B`. -/
def dev (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (B : Finset (Fin l → ℤ))
    (T : Finset (Fin m)) : ℚ :=
  |prob B (fun y => ∀ j ∈ T, fR q γ₂ β M v j y) - pR q γ₂ β mb ^ T.card|

variable (q γ₂ β mb) in
/-- Total deviation over all coordinate sets of size at most `s`. -/
def devSum (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (B : Finset (Fin l → ℤ))
    (s : ℕ) : ℚ :=
  ∑ T ∈ (univ : Finset (Fin m)).powerset with T.card ≤ s, dev q γ₂ β mb M v B T

lemma dev_nonneg (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (B : Finset (Fin l → ℤ))
    (T : Finset (Fin m)) : 0 ≤ dev q γ₂ β mb M v B T := abs_nonneg _

lemma core_dev (hp : Params q γ₁ γ₂ β mb) {M : Matrix (Fin m) (Fin l) (ZMod q)}
    {v : Fin m → ℤ} (hv : Bounded β v) {s : ℕ} (hs : 1 ≤ s)
    (B : Finset (Fin l → ℤ)) (A Xs : Finset (Fin m)) (hXs : Xs.card ≤ 1) (hd : Disjoint A Xs) :
    |prob B (fun y => (∀ j ∈ A, ¬ fR q γ₂ β M v j y) ∧ (∀ j ∈ Xs, fR q γ₂ β M v j y))
      - prob (univ : Finset (Fin m → ZMod q))
          (fun w => (∀ j ∈ A, ¬ fU q γ₂ β v j w) ∧ (∀ j ∈ Xs, fU q γ₂ β v j w))|
    ≤ 2 * (m.choose s) * (pR q γ₂ β mb) ^ s + 2 * devSum q γ₂ β mb M v B s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hpR := pR_nonneg hp
  set D := devSum q γ₂ β mb M v B (t + 1) with hD
  set p := pR q γ₂ β mb with hpdef
  set K := A.powerset.filter fun T => T.card ≤ t with hKdef
  have hbr : |prob B (fun y => (∀ j ∈ A, ¬ fR q γ₂ β M v j y) ∧ (∀ j ∈ Xs, fR q γ₂ β M v j y))
      - ∑ T ∈ K, (-1 : ℚ) ^ T.card *
          prob B (fun y => (∀ j ∈ T, fR q γ₂ β M v j y) ∧ (∀ j ∈ Xs, fR q γ₂ β M v j y))|
      ≤ ∑ T ∈ A.powersetCard (t + 1), prob B (fun y => ∀ j ∈ T, fR q γ₂ β M v j y) := by
    convert bonf (fR q γ₂ β M v) B A Xs t
  have hbu : |prob (univ : Finset (Fin m → ZMod q))
        (fun w => (∀ j ∈ A, ¬ fU q γ₂ β v j w) ∧ (∀ j ∈ Xs, fU q γ₂ β v j w))
      - ∑ T ∈ K, (-1 : ℚ) ^ T.card * prob (univ : Finset (Fin m → ZMod q))
          (fun w => (∀ j ∈ T, fU q γ₂ β v j w) ∧ (∀ j ∈ Xs, fU q γ₂ β v j w))|
      ≤ ∑ T ∈ A.powersetCard (t + 1), prob (univ : Finset (Fin m → ZMod q))
          (fun w => ∀ j ∈ T, fU q γ₂ β v j w) := by
    convert bonf (fU q γ₂ β v) (univ : Finset (Fin m → ZMod q)) A Xs t
  have hRu : ∑ T ∈ A.powersetCard (t + 1), prob (univ : Finset (Fin m → ZMod q))
        (fun w => ∀ j ∈ T, fU q γ₂ β v j w)
      = (A.card.choose (t + 1) : ℚ) * p ^ (t + 1) := by
    rw [← Finset.card_powersetCard, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [prob_univ_allF hp hv, (Finset.mem_powersetCard.mp hT).2]
  -- kept terms
  have hkept : ∀ T ∈ K,
      |prob B (fun y => (∀ j ∈ T, fR q γ₂ β M v j y) ∧ (∀ j ∈ Xs, fR q γ₂ β M v j y))
        - prob (univ : Finset (Fin m → ZMod q))
            (fun w => (∀ j ∈ T, fU q γ₂ β v j w) ∧ (∀ j ∈ Xs, fU q γ₂ β v j w))|
        ≤ dev q γ₂ β mb M v B (T ∪ Xs) := by
    intro T hT
    rw [prob_congr (Q := fun y => ∀ j ∈ T ∪ Xs, fR q γ₂ β M v j y) _
        (fun y _ => by simp only [Finset.mem_union]; constructor
                       · rintro ⟨h1, h2⟩ j (hj | hj); exacts [h1 j hj, h2 j hj]
                       · intro h; exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩),
      prob_congr (Q := fun w => ∀ j ∈ T ∪ Xs, fU q γ₂ β v j w) _
        (fun w _ => by simp only [Finset.mem_union]; constructor
                       · rintro ⟨h1, h2⟩ j (hj | hj); exacts [h1 j hj, h2 j hj]
                       · intro h; exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩),
      prob_univ_allF hp hv]
    exact le_of_eq rfl
  have hsub : ∀ T ∈ K, T ∪ Xs ∈ (univ : Finset (Fin m)).powerset.filter (fun U => U.card ≤ t + 1) := by
    intro T hT
    have hTc : T.card ≤ t := (Finset.mem_filter.mp hT).2
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact (Finset.card_union_le _ _).trans (by omega)
  have hinj : Set.InjOn (fun T => T ∪ Xs) (K : Set (Finset (Fin m))) := by
    intro T₁ h₁ T₂ h₂ he
    have d₁ : Disjoint T₁ Xs :=
      hd.mono_left (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).1)
    have d₂ : Disjoint T₂ Xs :=
      hd.mono_left (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).1)
    simp only at he
    rw [← Finset.union_sdiff_cancel_right d₁, he, Finset.union_sdiff_cancel_right d₂]
  have hKD : ∑ T ∈ K, dev q γ₂ β mb M v B (T ∪ Xs) ≤ D := by
    rw [← Finset.sum_image (f := fun U => dev q γ₂ β mb M v B U) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro U hU
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hU
      exact hsub T hT
    · intro U _ _; exact dev_nonneg _ _ _ _
  have hK : |∑ T ∈ K, (-1 : ℚ) ^ T.card *
        prob B (fun y => (∀ j ∈ T, fR q γ₂ β M v j y) ∧ (∀ j ∈ Xs, fR q γ₂ β M v j y))
      - ∑ T ∈ K, (-1 : ℚ) ^ T.card * prob (univ : Finset (Fin m → ZMod q))
          (fun w => (∀ j ∈ T, fU q γ₂ β v j w) ∧ (∀ j ∈ Xs, fU q γ₂ β v j w))|
      ≤ D := by
    rw [← Finset.sum_sub_distrib]
    refine ((Finset.abs_sum_le_sum_abs _ _).trans ?_).trans hKD
    refine Finset.sum_le_sum fun T hT => ?_
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hkept T hT
  -- remainder on the real side
  have hRr : ∑ T ∈ A.powersetCard (t + 1), prob B (fun y => ∀ j ∈ T, fR q γ₂ β M v j y)
      ≤ (A.card.choose (t + 1) : ℚ) * p ^ (t + 1) + D := by
    have h1 : ∀ T ∈ A.powersetCard (t + 1), prob B (fun y => ∀ j ∈ T, fR q γ₂ β M v j y)
        ≤ p ^ (t + 1) + dev q γ₂ β mb M v B T := by
      intro T hT
      have hc := (Finset.mem_powersetCard.mp hT).2
      have : prob B (fun y => ∀ j ∈ T, fR q γ₂ β M v j y) - p ^ T.card
          ≤ dev q γ₂ β mb M v B T := le_abs_self _
      rw [hc] at this
      linarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    have : ∑ T ∈ A.powersetCard (t + 1), dev q γ₂ β mb M v B T ≤ D := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro U hU
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
        exact (Finset.mem_powersetCard.mp hU).2.le
      · intro U _ _; exact dev_nonneg _ _ _ _
    linarith
  have hA : A.card ≤ m := by simpa using Finset.card_le_univ A
  have hch : (A.card.choose (t + 1) : ℚ) ≤ m.choose (t + 1) := by
    exact_mod_cast Nat.choose_le_choose _ hA
  have e2 : (A.card.choose (t + 1) : ℚ) * p ^ (t + 1) ≤ (m.choose (t + 1) : ℚ) * p ^ (t + 1) :=
    mul_le_mul_of_nonneg_right hch (by positivity)
  rw [hRu] at hbu
  rw [abs_le] at hbr hbu hK ⊢
  constructor <;> linarith

lemma disjoint_passSet_failSet (o : Option (Fin m)) : Disjoint (passSet o) (failSet o) := by
  cases o with
  | none => simp [failSet]
  | some i => simp [passSet, failSet]

/-- Layer 2 with per-set deviations: the first-failure index of the r₀ check is close to
geometric, with error the Bonferroni remainder plus twice the total deviation. -/
lemma real_close_dev (hp : Params q γ₁ γ₂ β mb) (M : Matrix (Fin m) (Fin l) (ZMod q))
    {v : Fin m → ℤ} (hv : Bounded β v) {s : ℕ} (hs : 1 ≤ s)
    (B : Finset (Fin l → ℤ)) (o : Option (Fin m)) :
    |prob B (fun y => I q γ₂ β M v y = o) - geom (pR q γ₂ β mb) m o|
      ≤ 2 * (m.choose s) * (pR q γ₂ β mb) ^ s + 2 * devSum q γ₂ β mb M v B s := by
  rw [← prob_univ_geom hp hv o,
    prob_congr (P := fun y => I q γ₂ β M v y = o) (Q := fun y =>
      (∀ j ∈ passSet o, ¬ fR q γ₂ β M v j y) ∧
      (∀ j ∈ failSet o, fR q γ₂ β M v j y)) _ (fun y _ => firstIdx_eq_iff _ o)]
  exact core_dev hp hv hs B _ _ (failSet_card o) (disjoint_passSet_failSet o)

end RejOrder

end
end Layer2

section Leak
/-!
# The leak of one attempt

`leak M u v` is the total distance between the probabilities of the rejection views and reference
values that do not depend on the secret shifts `u`, `v`. It bounds what any distinguisher can
learn (`indist`), and it is small on average over the matrix whenever the "all of `T` fail" events
are close to uniform on average (`leak_avg`).
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

variable (q γ₂ β mb) in
/-- Joint form of `dev`: `y` is uniform on `B`, and the event is "`y ∈ B'` and every coordinate
in `T` fails". -/
def jdev (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (B B' : Finset (Fin l → ℤ))
    (T : Finset (Fin m)) : ℚ :=
  |((B'.filter fun y => ∀ j ∈ T, fR q γ₂ β M v j y).card : ℚ) / B.card
    - (B'.card : ℚ) / B.card * pR q γ₂ β mb ^ T.card|

variable (q γ₂ β mb) in
def jdevSum (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (B B' : Finset (Fin l → ℤ))
    (s : ℕ) : ℚ :=
  ∑ T ∈ (univ : Finset (Fin m)).powerset with T.card ≤ s, jdev q γ₂ β mb M v B B' T

lemma jdev_eq (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ) (B B' : Finset (Fin l → ℤ))
    (T : Finset (Fin m)) :
    (B'.card : ℚ) / B.card * dev q γ₂ β mb M v B' T = jdev q γ₂ β mb M v B B' T := by
  unfold dev jdev prob
  have h0 : (0 : ℚ) ≤ (B'.card : ℚ) / B.card := by positivity
  conv_lhs => rw [← abs_of_nonneg h0]
  rw [← abs_mul]
  congr 1
  by_cases hc : (B'.card : ℚ) = 0
  · have hc' : B'.card = 0 := by exact_mod_cast hc
    have : (B'.filter fun y => ∀ j ∈ T, fR q γ₂ β M v j y).card = 0 :=
      Nat.eq_zero_of_le_zero (hc' ▸ Finset.card_filter_le _ _)
    simp [hc', this]
  · by_cases hB : (B.card : ℚ) = 0
    · simp [hB]
    · field_simp

lemma jdevSum_eq (M : Matrix (Fin m) (Fin l) (ZMod q)) (v : Fin m → ℤ)
    (B B' : Finset (Fin l → ℤ)) (s : ℕ) :
    (B'.card : ℚ) / B.card * devSum q γ₂ β mb M v B' s = jdevSum q γ₂ β mb M v B B' s := by
  unfold devSum jdevSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => jdev_eq M v B B' T

variable (q γ₁ γ₂ β mb) in
/-- Sparse-test near-uniformity on average over the matrix: for every sub-event `B'` of the box,
the "all of `T` fail" events, summed over all `T` of size at most `s`, deviate by at most `δ`
in total. -/
def SparseFailAvg (mat : P → Matrix (Fin m) (Fin l) (ZMod q)) (s : ℕ) (δ : ℚ) : Prop :=
  ∀ v, Bounded β v → ∀ B' ⊆ box γ₁ l,
    avg (fun a => jdevSum q γ₂ β mb (mat a) v (box γ₁ l) B' s) ≤ δ

lemma box_card_pos (hp : Params q γ₁ γ₂ β mb) : (0 : ℚ) < ((box γ₁ l).card : ℚ) := by
  rw [card_box hp]
  have : (0 : ℚ) < γ₁ := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  positivity

lemma rFail_close (hp : Params q γ₁ γ₂ β mb) (M : Matrix (Fin m) (Fin l) (ZMod q))
    (u : Fin l → ℤ) {v : Fin m → ℤ} (hv : Bounded β v) {s : ℕ} (hs : 1 ≤ s) (i : Fin m) :
    |prob (box γ₁ l) (fun y => view q γ₁ γ₂ β M u v y = .rFail i)
        - geom (pR q γ₂ β mb) m (some i)|
      ≤ 2 * (m.choose s) * (pR q γ₂ β mb) ^ s
        + 2 * jdevSum q γ₂ β mb M v (box γ₁ l) (box γ₁ l) s := by
  have hb := box_card_pos (l := l) hp
  rw [prob_congr _ (fun y _ => view_eq_rFail M u v y i),
    ← jdevSum_eq M v (box γ₁ l) (box γ₁ l) s, div_self hb.ne', one_mul]
  exact real_close_dev hp M hv hs _ (some i)

lemma zFail_close (hp : Params q γ₁ γ₂ β mb) (M : Matrix (Fin m) (Fin l) (ZMod q))
    {u : Fin l → ℤ} {v : Fin m → ℤ} (hu : Bounded β u) (hv : Bounded β v) {s : ℕ} (hs : 1 ≤ s)
    (j : Fin l) :
    |prob (box γ₁ l) (fun y => view q γ₁ γ₂ β M u v y = .zFail j)
        - geom (pZ γ₁ β) l (some j) * geom (pR q γ₂ β mb) m none|
      ≤ 2 * (m.choose s) * (pR q γ₂ β mb) ^ s
        + 2 * jdevSum q γ₂ β mb M v (box γ₁ l) (Bset γ₁ β u j) s := by
  have hpR := pR_nonneg hp
  rw [prob_congr _ (fun y _ => view_eq_zFail M u v y j), prob_and]
  have hB : (box γ₁ l).filter (fun y => J γ₁ β u y = some j) = Bset γ₁ β u j := rfl
  rw [hB, ← J_dist hp u hu (some j)]
  set g := prob (box γ₁ l) (fun y => J γ₁ β u y = some j) with hg
  have hg0 : 0 ≤ g := prob_nonneg _ _
  have hg1 : g ≤ 1 := prob_le_one _ _
  have hgc : g = ((Bset γ₁ β u j).card : ℚ) / (box γ₁ l).card := rfl
  rw [← mul_sub, abs_mul, abs_of_nonneg hg0,
    ← jdevSum_eq M v (box γ₁ l) (Bset γ₁ β u j) s, ← hgc]
  have hc := real_close_dev hp M hv hs (Bset γ₁ β u j) none
  have hD : 0 ≤ devSum q γ₂ β mb M v (Bset γ₁ β u j) s :=
    Finset.sum_nonneg fun T _ => dev_nonneg _ _ _ _
  have hC : (0 : ℚ) ≤ 2 * (m.choose s) * (pR q γ₂ β mb) ^ s := by positivity
  calc g * |prob (Bset γ₁ β u j) (fun y => I q γ₂ β M v y = none)
          - geom (pR q γ₂ β mb) m none|
      ≤ g * (2 * (m.choose s) * (pR q γ₂ β mb) ^ s
          + 2 * devSum q γ₂ β mb M v (Bset γ₁ β u j) s) :=
        mul_le_mul_of_nonneg_left hc hg0
    _ ≤ _ := by nlinarith

/-- If the sparse tests deviate by at most `δ` on average over the matrix, the leak is at most
`(m + l)·(2·C(m,s)·p_R^s + 2δ)` on average. -/
theorem leak_avg [Nonempty P] (hp : Params q γ₁ γ₂ β mb)
    {mat : P → Matrix (Fin m) (Fin l) (ZMod q)} {s : ℕ} (hs : 1 ≤ s) {δ : ℚ}
    (h : SparseFailAvg q γ₁ γ₂ β mb mat s δ) {u : Fin l → ℤ} {v : Fin m → ℤ}
    (hu : Bounded β u) (hv : Bounded β v) :
    avg (fun a => leak q γ₁ γ₂ β mb (mat a) u v)
      ≤ ((m : ℚ) + l) * (2 * (m.choose s) * (pR q γ₂ β mb) ^ s + 2 * δ) := by
  set c : ℚ := 2 * (m.choose s) * (pR q γ₂ β mb) ^ s with hc
  have hr : avg (fun a : P => c + 2 * jdevSum q γ₂ β mb (mat a) v (box γ₁ l) (box γ₁ l) s)
      ≤ c + 2 * δ := by
    rw [avg_add, avg_const, avg_mul_left]
    linarith [h v hv _ (Finset.Subset.refl _)]
  have hz : ∀ j, avg (fun a : P =>
      c + 2 * jdevSum q γ₂ β mb (mat a) v (box γ₁ l) (Bset γ₁ β u j) s) ≤ c + 2 * δ := by
    intro j
    have hsub : Bset γ₁ β u j ⊆ box γ₁ l := Finset.filter_subset _ _
    rw [avg_add, avg_const, avg_mul_left]
    linarith [h v hv _ hsub]
  refine le_trans (avg_mono (g := fun a =>
      ∑ _i : Fin m, (c + 2 * jdevSum q γ₂ β mb (mat a) v (box γ₁ l) (box γ₁ l) s)
      + ∑ j : Fin l, (c + 2 * jdevSum q γ₂ β mb (mat a) v (box γ₁ l) (Bset γ₁ β u j) s))
    fun a => ?_) ?_
  · exact add_le_add (Finset.sum_le_sum fun i _ => rFail_close hp (mat a) u hv hs i)
      (Finset.sum_le_sum fun j _ => zFail_close hp (mat a) hu hv hs j)
  · rw [avg_add, avg_finset_sum, avg_finset_sum]
    have h1 : ∑ _i : Fin m, avg (fun a : P =>
        c + 2 * jdevSum q γ₂ β mb (mat a) v (box γ₁ l) (box γ₁ l) s) ≤ m * (c + 2 * δ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
    have h2 : ∑ j : Fin l, avg (fun a : P =>
        c + 2 * jdevSum q γ₂ β mb (mat a) v (box γ₁ l) (Bset γ₁ β u j) s) ≤ l * (c + 2 * δ) := by
      refine (Finset.sum_le_sum fun j _ => hz j).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith

end RejOrder

end
end Leak

section SecondMoment
/-!
# Second moment over a random linear map

`a` is uniform on a finite abelian group `P`, and `Φ a` is additive in `a`. A value of `Φ a` is
hit at most `N / q^dim` of the time, where `N` counts the test vectors orthogonal to the whole
image, and exactly `1 / q^dim` of the time when `N = 1`. This gives a second-moment bound for
events on `Φ a`, with no leftover-hash-lemma loss for sparse product events. For pairs with many
orthogonal test vectors, the cross term is instead capped by `Pr[Φ y ∈ E]`, which is controlled
by the test vectors orthogonal to `Φ y` alone (`second_moment_cap`).
-/

open Finset

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

section Char

variable {q : ℕ} [NeZero q] {P : Type*} [Fintype P] [AddCommGroup P] {ι : Type*} [Fintype ι]

local notation "χ" => (ZMod.stdAddChar (N := q))

lemma chi_sum (S : Finset ι) (f : ι → ZMod q) : (χ (∑ i ∈ S, f i) : ℂ) = ∏ i ∈ S, χ (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

lemma char_sum (h : P → ZMod q) (hadd : ∀ a b, h (a + b) = h a + h b) :
    ∑ a, (χ (h a) : ℂ) = if ∀ a, h a = 0 then (Fintype.card P : ℂ) else 0 := by
  split_ifs with hall
  · simp [hall]
  · obtain ⟨a₀, ha₀⟩ := not_forall.mp hall
    have hne : (χ (h a₀) : ℂ) ≠ 1 := by
      rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q))]
      exact fun he => ha₀ (ZMod.injective_stdAddChar he)
    have hS : ∑ a, (χ (h a) : ℂ) = χ (h a₀) * ∑ a, (χ (h a) : ℂ) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight a₀)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Equiv.coe_addRight, hadd, AddChar.map_add_eq_mul, mul_comm]
    have h0 : (1 - (χ (h a₀) : ℂ)) * ∑ a, (χ (h a) : ℂ) = 0 := by
      rw [sub_mul, one_mul]; exact sub_eq_zero.mpr hS
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne.symm)

lemma delta_char (b : ZMod q) :
    ∑ c : ZMod q, (χ (c * b) : ℂ) = if b = 0 then (q : ℂ) else 0 := by
  have h := AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar q)
  rw [ZMod.card] at h
  rw [h]; split_ifs <;> simp

/-- The orthogonality count: test vectors that vanish on the whole image of `Φ`. -/
def orth (Φ : P → ι → ZMod q) : Finset (ι → ZMod q) :=
  univ.filter fun ℓ => ∀ a, ℓ ⬝ᵥ Φ a = 0

lemma fiber_char (Φ : P → ι → ZMod q) (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b)
    (x : ι → ZMod q) :
    ((univ.filter fun a => Φ a = x).card : ℂ) * (q : ℂ) ^ Fintype.card ι
      = Fintype.card P * ∑ ℓ ∈ orth Φ, (χ (-(ℓ ⬝ᵥ x)) : ℂ) := by
  have h1 : ∀ a, (if Φ a = x then (q : ℂ) ^ Fintype.card ι else 0)
      = ∑ ℓ : ι → ZMod q, (χ (ℓ ⬝ᵥ Φ a) : ℂ) * χ (-(ℓ ⬝ᵥ x)) := by
    intro a
    have h2 : ∀ ℓ : ι → ZMod q, (χ (ℓ ⬝ᵥ Φ a) : ℂ) * χ (-(ℓ ⬝ᵥ x))
        = ∏ i, (χ (ℓ i * (Φ a i - x i)) : ℂ) := by
      intro ℓ
      rw [← AddChar.map_add_eq_mul, ← chi_sum]
      congr 1
      simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]; ring
    simp_rw [h2]
    have h3 := Finset.prod_univ_sum (fun _ : ι => (univ : Finset (ZMod q)))
      (fun i c => (χ (c * (Φ a i - x i)) : ℂ))
    rw [Fintype.piFinset_univ] at h3
    rw [← h3]
    simp_rw [delta_char]
    rw [Finset.prod_ite_zero]
    simp only [sub_eq_zero, Finset.prod_const, Finset.card_univ]
    congr 1
    exact propext ⟨fun h i _ => congrFun h i, fun h => funext fun i => h i (Finset.mem_univ i)⟩
  have hadd' : ∀ ℓ : ι → ZMod q, ∀ a b, ℓ ⬝ᵥ Φ (a + b) = ℓ ⬝ᵥ Φ a + ℓ ⬝ᵥ Φ b := by
    intro ℓ a b; rw [hadd, dotProduct_add]
  calc ((univ.filter fun a => Φ a = x).card : ℂ) * (q : ℂ) ^ Fintype.card ι
      = ∑ a, (if Φ a = x then (q : ℂ) ^ Fintype.card ι else 0) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ a, ∑ ℓ : ι → ZMod q, (χ (ℓ ⬝ᵥ Φ a) : ℂ) * χ (-(ℓ ⬝ᵥ x)) :=
        Finset.sum_congr rfl fun a _ => h1 a
    _ = ∑ ℓ : ι → ZMod q, (χ (-(ℓ ⬝ᵥ x)) : ℂ) * ∑ a, (χ (ℓ ⬝ᵥ Φ a) : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = ∑ ℓ : ι → ZMod q, (χ (-(ℓ ⬝ᵥ x)) : ℂ) *
          (if ∀ a, ℓ ⬝ᵥ Φ a = 0 then (Fintype.card P : ℂ) else 0) :=
        Finset.sum_congr rfl fun ℓ _ => by rw [char_sum _ (hadd' ℓ)]
    _ = _ := by
        unfold orth
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        split_ifs <;> ring

lemma zero_mem_orth (Φ : P → ι → ZMod q) : (0 : ι → ZMod q) ∈ orth Φ := by
  simp [orth]

lemma orth_card_pos (Φ : P → ι → ZMod q) : 1 ≤ (orth Φ).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_orth Φ⟩

/-- Every value is hit at most `N / q^dim` of the time. -/
lemma fiber_le (Φ : P → ι → ZMod q) (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b) (x : ι → ZMod q) :
    (univ.filter fun a => Φ a = x).card * q ^ Fintype.card ι
      ≤ Fintype.card P * (orth Φ).card := by
  have h := congrArg norm (fiber_char Φ hadd x)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast,
    Complex.norm_natCast] at h
  have h2 : ‖∑ ℓ ∈ orth Φ, (χ (-(ℓ ⬝ᵥ x)) : ℂ)‖ ≤ (orth Φ).card := by
    refine (norm_sum_le _ _).trans ?_
    simp
  have h3 : (((univ.filter fun a => Φ a = x).card * q ^ Fintype.card ι : ℕ) : ℝ)
      ≤ ((Fintype.card P * (orth Φ).card : ℕ) : ℝ) := by
    push_cast
    rw [h]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  exact_mod_cast h3

/-- If only the zero test vector is orthogonal to the image, `Φ a` is exactly uniform. -/
lemma fiber_eq (Φ : P → ι → ZMod q) (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b) (x : ι → ZMod q)
    (h1 : (orth Φ).card = 1) :
    (univ.filter fun a => Φ a = x).card * q ^ Fintype.card ι = Fintype.card P := by
  have h := fiber_char Φ hadd x
  obtain ⟨ℓ₀, hℓ⟩ := Finset.card_eq_one.mp h1
  have : ℓ₀ = 0 := by
    have := zero_mem_orth Φ
    rw [hℓ, Finset.mem_singleton] at this
    exact this.symm
  rw [hℓ, this, Finset.sum_singleton] at h
  simp only [zero_dotProduct, neg_zero, AddChar.map_zero_eq_one, mul_one] at h
  exact_mod_cast h

end Char

/-! ## Pairs -/

section Pair

variable {q : ℕ} [NeZero q] {P : Type*} [Fintype P] [AddCommGroup P] {τ : Type*} [Fintype τ]
  [DecidableEq τ]

/-- Two maps side by side. Test vectors on `τ ⊕ τ` are pairs `(λ, λ')`. -/
def pairΦ (Φ₁ Φ₂ : P → τ → ZMod q) (a : P) : τ ⊕ τ → ZMod q := Sum.elim (Φ₁ a) (Φ₂ a)

lemma pairΦ_add {Φ₁ Φ₂ : P → τ → ZMod q} (h₁ : ∀ a b, Φ₁ (a + b) = Φ₁ a + Φ₁ b)
    (h₂ : ∀ a b, Φ₂ (a + b) = Φ₂ a + Φ₂ b) (a b : P) :
    pairΦ Φ₁ Φ₂ (a + b) = pairΦ Φ₁ Φ₂ a + pairΦ Φ₁ Φ₂ b := by
  funext i; cases i <;> simp [pairΦ, h₁, h₂]

lemma pair_fiber (Φ₁ Φ₂ : P → τ → ZMod q) (x₁ x₂ : τ → ZMod q) :
    (univ.filter fun a => Φ₁ a = x₁ ∧ Φ₂ a = x₂)
      = univ.filter fun a => pairΦ Φ₁ Φ₂ a = Sum.elim x₁ x₂ := by
  ext a
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; unfold pairΦ; rw [h1, h2]
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩

lemma cnt_sum (Φ₁ Φ₂ : P → τ → ZMod q) (E₁ E₂ : Finset (τ → ZMod q)) :
    (univ.filter fun a => Φ₁ a ∈ E₁ ∧ Φ₂ a ∈ E₂).card
      = ∑ x ∈ E₁ ×ˢ E₂, (univ.filter fun a => Φ₁ a = x.1 ∧ Φ₂ a = x.2).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => (Φ₁ a, Φ₂ a)) (t := E₁ ×ˢ E₂)
    (fun a ha => Finset.mem_product.mpr (Finset.mem_filter.mp ha).2)]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  ext a
  simp only [Finset.mem_product] at hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1 ▸ hx.1, h2 ▸ hx.2⟩, h1, h2⟩

lemma card_sum_self : Fintype.card (τ ⊕ τ) = 2 * Fintype.card τ := by
  rw [Fintype.card_sum]; ring

lemma cnt_le (Φ₁ Φ₂ : P → τ → ZMod q) (h₁ : ∀ a b, Φ₁ (a + b) = Φ₁ a + Φ₁ b)
    (h₂ : ∀ a b, Φ₂ (a + b) = Φ₂ a + Φ₂ b) (E₁ E₂ : Finset (τ → ZMod q)) :
    (univ.filter fun a => Φ₁ a ∈ E₁ ∧ Φ₂ a ∈ E₂).card * q ^ (2 * Fintype.card τ)
      ≤ E₁.card * E₂.card * (Fintype.card P * (orth (pairΦ Φ₁ Φ₂)).card) := by
  rw [cnt_sum, Finset.sum_mul, ← Finset.card_product, ← smul_eq_mul (a := (E₁ ×ˢ E₂).card),
    ← Finset.sum_const]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [pair_fiber, ← card_sum_self]
  exact fiber_le _ (pairΦ_add h₁ h₂) _

lemma cnt_eq (Φ₁ Φ₂ : P → τ → ZMod q) (h₁ : ∀ a b, Φ₁ (a + b) = Φ₁ a + Φ₁ b)
    (h₂ : ∀ a b, Φ₂ (a + b) = Φ₂ a + Φ₂ b) (E₁ E₂ : Finset (τ → ZMod q))
    (hN : (orth (pairΦ Φ₁ Φ₂)).card = 1) :
    (univ.filter fun a => Φ₁ a ∈ E₁ ∧ Φ₂ a ∈ E₂).card * q ^ (2 * Fintype.card τ)
      = E₁.card * E₂.card * Fintype.card P := by
  rw [cnt_sum, Finset.sum_mul, ← Finset.card_product, ← smul_eq_mul (a := (E₁ ×ˢ E₂).card),
    ← Finset.sum_const]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pair_fiber, ← card_sum_self]
  exact fiber_eq _ (pairΦ_add h₁ h₂) _ hN

/-- The cross term of the second moment for one pair of maps. -/
lemma cross_le (Φ₁ Φ₂ : P → τ → ZMod q) (h₁ : ∀ a b, Φ₁ (a + b) = Φ₁ a + Φ₁ b)
    (h₂ : ∀ a b, Φ₂ (a + b) = Φ₂ a + Φ₂ b) (E : Finset (τ → ZMod q)) :
    ∑ a, ((if Φ₁ a ∈ E then (1 : ℚ) else 0) - E.card / (q : ℚ) ^ Fintype.card τ) *
         ((if Φ₂ a ∈ E then (1 : ℚ) else 0) - E.card / (q : ℚ) ^ Fintype.card τ)
      ≤ Fintype.card P * (3 * (E.card / (q : ℚ) ^ Fintype.card τ) ^ 2 *
          (((orth (pairΦ Φ₁ Φ₂)).card : ℚ) - 1)) := by
  set N := (orth (pairΦ Φ₁ Φ₂)).card with hNdef
  set Q : ℚ := (q : ℚ) ^ Fintype.card τ with hQ
  have hq0 : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hQ0 : 0 < Q := by positivity
  set μ : ℚ := E.card / Q with hμ
  have hμ0 : 0 ≤ μ := by positivity
  set c₁₂ := (univ.filter fun a => Φ₁ a ∈ E ∧ Φ₂ a ∈ E).card with hc12
  set c₁ := (univ.filter fun a => Φ₁ a ∈ E ∧ Φ₂ a ∈ (univ : Finset (τ → ZMod q))).card with hc1
  set c₂ := (univ.filter fun a => Φ₁ a ∈ (univ : Finset (τ → ZMod q)) ∧ Φ₂ a ∈ E).card with hc2
  set p := Fintype.card P with hp
  have hexp : ∑ a, ((if Φ₁ a ∈ E then (1 : ℚ) else 0) - μ) * ((if Φ₂ a ∈ E then (1 : ℚ) else 0) - μ)
      = c₁₂ - μ * c₁ - μ * c₂ + μ ^ 2 * p := by
    have e : ∀ a, ((if Φ₁ a ∈ E then (1 : ℚ) else 0) - μ) * ((if Φ₂ a ∈ E then (1 : ℚ) else 0) - μ)
        = (if Φ₁ a ∈ E ∧ Φ₂ a ∈ E then (1 : ℚ) else 0)
          - μ * (if Φ₁ a ∈ E ∧ Φ₂ a ∈ (univ : Finset (τ → ZMod q)) then (1 : ℚ) else 0)
          - μ * (if Φ₁ a ∈ (univ : Finset (τ → ZMod q)) ∧ Φ₂ a ∈ E then (1 : ℚ) else 0)
          + μ ^ 2 := by
      intro a
      by_cases ha : Φ₁ a ∈ E <;> by_cases hb : Φ₂ a ∈ E <;> simp [ha, hb] <;> ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hexp]
  have hcardU : ((univ : Finset (τ → ZMod q)).card : ℚ) = Q := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card]; push_cast; rfl
  have hQ2 : ((q ^ (2 * Fintype.card τ) : ℕ) : ℚ) = Q ^ 2 := by
    push_cast; rw [hQ, ← pow_mul, mul_comm]
  have hN1 : 1 ≤ N := orth_card_pos _
  have hpc : (0 : ℚ) ≤ p := Nat.cast_nonneg _
  by_cases hN : N = 1
  · have e12 : (c₁₂ : ℚ) * Q ^ 2 = E.card * E.card * p := by
      rw [← hQ2]; exact_mod_cast cnt_eq Φ₁ Φ₂ h₁ h₂ E E hN
    have e1 : (c₁ : ℚ) * Q ^ 2 = E.card * Q * p := by
      rw [← hQ2, ← hcardU]; exact_mod_cast cnt_eq Φ₁ Φ₂ h₁ h₂ E univ hN
    have e2 : (c₂ : ℚ) * Q ^ 2 = Q * E.card * p := by
      rw [← hQ2, ← hcardU]; exact_mod_cast cnt_eq Φ₁ Φ₂ h₁ h₂ univ E hN
    have hQ2' : Q ^ 2 ≠ 0 := by positivity
    have f12 : (c₁₂ : ℚ) = μ ^ 2 * p := by
      rw [eq_div_of_mul_eq hQ2' e12, hμ]; ring
    have f1 : (c₁ : ℚ) = μ * p := by
      rw [eq_div_of_mul_eq hQ2' e1, hμ]; field_simp
    have f2 : (c₂ : ℚ) = μ * p := by
      rw [eq_div_of_mul_eq hQ2' e2, hμ]; field_simp
    rw [f12, f1, f2, hN]
    simp only [Nat.cast_one, sub_self, mul_zero]
    nlinarith
  · have hN2 : (2 : ℚ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    have e12 : (c₁₂ : ℚ) * Q ^ 2 ≤ E.card * E.card * (p * N) := by
      rw [← hQ2]; exact_mod_cast cnt_le Φ₁ Φ₂ h₁ h₂ E E
    have f12 : (c₁₂ : ℚ) ≤ μ ^ 2 * (p * N) := by
      have : μ ^ 2 * (p * N) = E.card * E.card * (p * N) / Q ^ 2 := by rw [hμ]; ring
      rw [this, le_div_iff₀ (by positivity)]
      exact e12
    have g1 : 0 ≤ μ * (c₁ : ℚ) := by positivity
    have g2 : 0 ≤ μ * (c₂ : ℚ) := by positivity
    have g3 : 0 ≤ μ ^ 2 * p := by positivity
    nlinarith

end Pair

/-! ## A cap on the cross term -/

section Cap

variable {q : ℕ} [NeZero q] {P : Type*} [Fintype P] [AddCommGroup P] {τ : Type*} [Fintype τ]
  [DecidableEq τ]

/-- An event `E` is hit at most `|E| · N / q^dim` of the time, where `N` counts the test vectors
orthogonal to the image of `Φ` alone. -/
lemma cnt1_le (Φ : P → τ → ZMod q) (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b)
    (E : Finset (τ → ZMod q)) :
    (univ.filter fun a => Φ a ∈ E).card * q ^ Fintype.card τ
      ≤ E.card * (Fintype.card P * (orth Φ).card) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Φ) (s := univ.filter fun a => Φ a ∈ E) (t := E)
    (fun a ha => (Finset.mem_filter.mp ha).2), Finset.sum_mul,
    ← smul_eq_mul (a := E.card), ← Finset.sum_const]
  refine Finset.sum_le_sum fun x hx => ?_
  have e : ((univ.filter fun a => Φ a ∈ E).filter fun a => Φ a = x)
      = univ.filter fun a => Φ a = x := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hx, h⟩⟩
  rw [e]
  exact fiber_le Φ hadd x

/-- The cross term is also at most `Pr[Φ₁ ∈ E] + μ²`, which the previous lemma bounds by the
orthogonality count of `Φ₁` alone. -/
lemma cross_cap (Φ₁ Φ₂ : P → τ → ZMod q) (h₁ : ∀ a b, Φ₁ (a + b) = Φ₁ a + Φ₁ b)
    (E : Finset (τ → ZMod q)) :
    ∑ a, ((if Φ₁ a ∈ E then (1 : ℚ) else 0) - E.card / (q : ℚ) ^ Fintype.card τ) *
         ((if Φ₂ a ∈ E then (1 : ℚ) else 0) - E.card / (q : ℚ) ^ Fintype.card τ)
      ≤ Fintype.card P * (E.card / (q : ℚ) ^ Fintype.card τ * (1 + E.card / (q : ℚ) ^ Fintype.card τ)
          + E.card / (q : ℚ) ^ Fintype.card τ * (((orth Φ₁).card : ℚ) - 1)) := by
  set Q : ℚ := (q : ℚ) ^ Fintype.card τ with hQ
  have hq0 : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hQ0 : 0 < Q := by positivity
  set μ : ℚ := E.card / Q with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hpt : ∀ a, ((if Φ₁ a ∈ E then (1 : ℚ) else 0) - μ) * ((if Φ₂ a ∈ E then (1 : ℚ) else 0) - μ)
      ≤ (if Φ₁ a ∈ E then (1 : ℚ) else 0) + μ ^ 2 := by
    intro a
    by_cases ha : Φ₁ a ∈ E <;> by_cases hb : Φ₂ a ∈ E <;> simp [ha, hb] <;> nlinarith
  refine (Finset.sum_le_sum fun a _ => hpt a).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : ((univ.filter fun a => Φ₁ a ∈ E).card : ℚ) * Q
      ≤ E.card * (Fintype.card P * (orth Φ₁).card) := by
    have := Nat.cast_le (α := ℚ).mpr (cnt1_le Φ₁ h₁ E)
    push_cast at this
    exact this
  have hc' : ((univ.filter fun a => Φ₁ a ∈ E).card : ℚ)
      ≤ μ * (Fintype.card P * (orth Φ₁).card) := by
    rw [hμ, div_mul_eq_mul_div, le_div_iff₀ hQ0]; exact hc
  nlinarith

end Cap

/-! ## The second-moment bound for a family of maps -/

section Family

variable {q : ℕ} [NeZero q] {P : Type*} [Fintype P] [AddCommGroup P] {τ : Type*} [Fintype τ]
  [DecidableEq τ] {Y : Type*}

/-- `y` is uniform on `B`, and `Φ y a` is additive in `a`. For any sub-event `B'` of `B`, the
probability of "`y ∈ B'` and `Φ y a ∈ E`" deviates from `Pr[B'] · |E| / q^dim` by a second moment
that is controlled by the pairs `(y, y')` with a non-trivial orthogonal test vector. -/
theorem second_moment (Φ : Y → P → τ → ZMod q) (hadd : ∀ y a b, Φ y (a + b) = Φ y a + Φ y b)
    (E : Finset (τ → ZMod q)) (B B' : Finset Y) (hB : B.Nonempty) (hsub : B' ⊆ B) :
    avg (fun a : P => (((B'.filter fun y => Φ y a ∈ E).card : ℚ) / B.card
        - (B'.card : ℚ) / B.card * (E.card / (q : ℚ) ^ Fintype.card τ)) ^ 2)
      ≤ 3 * (E.card / (q : ℚ) ^ Fintype.card τ) ^ 2 *
          ∑ ℓ ∈ (univ : Finset (τ ⊕ τ → ZMod q)).erase 0,
            prob (B ×ˢ B) (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0) := by
  set μ : ℚ := E.card / (q : ℚ) ^ Fintype.card τ with hμ
  have hBc : (0 : ℚ) < B.card := by exact_mod_cast hB.card_pos
  have hPc : (0 : ℚ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  set X : Y → P → ℚ := fun y a => (if Φ y a ∈ E then (1 : ℚ) else 0) - μ with hX
  have h1 : ∀ a : P, ((B'.filter fun y => Φ y a ∈ E).card : ℚ) / B.card
      - (B'.card : ℚ) / B.card * μ = (∑ y ∈ B', X y a) / B.card := by
    intro a
    simp only [hX]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
    ring
  have h2 : ∀ a : P, (∑ y ∈ B', X y a) ^ 2 = ∑ yy ∈ B' ×ˢ B', X yy.1 a * X yy.2 a := by
    intro a; rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  -- per-pair bound
  set W : Y × Y → ℚ := fun yy => ((orth (pairΦ (Φ yy.1) (Φ yy.2))).card : ℚ) - 1 with hW
  have hW0 : ∀ yy, 0 ≤ W yy := fun yy => by
    simp only [hW, sub_nonneg]; exact_mod_cast orth_card_pos _
  have h3 : ∀ yy : Y × Y, ∑ a, X yy.1 a * X yy.2 a ≤ Fintype.card P * (3 * μ ^ 2 * W yy) :=
    fun yy => cross_le (Φ yy.1) (Φ yy.2) (hadd yy.1) (hadd yy.2) E
  have h4 : ∑ a : P, (∑ y ∈ B', X y a) ^ 2
      ≤ Fintype.card P * (3 * μ ^ 2 * ∑ yy ∈ B ×ˢ B, W yy) := by
    simp_rw [h2]
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun yy _ => h3 yy).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hPc.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.product_subset_product hsub hsub)
      fun yy _ _ => hW0 yy
  -- count the orthogonal test vectors the other way round
  have h5 : ∑ yy ∈ B ×ˢ B, W yy = (B.card : ℚ) ^ 2 *
      ∑ ℓ ∈ (univ : Finset (τ ⊕ τ → ZMod q)).erase 0,
        prob (B ×ˢ B) (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0) := by
    have hW' : ∀ yy : Y × Y, W yy = ∑ ℓ ∈ (univ : Finset (τ ⊕ τ → ZMod q)).erase 0,
        (if ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0 then (1 : ℚ) else 0) := by
      intro yy
      rw [Finset.sum_boole]
      have : ((univ : Finset (τ ⊕ τ → ZMod q)).erase 0).filter
          (fun ℓ => ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0)
          = (orth (pairΦ (Φ yy.1) (Φ yy.2))).erase 0 := by
        ext ℓ; simp only [orth, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
          and_assoc]
      rw [this, Finset.card_erase_of_mem (zero_mem_orth _)]
      simp only [hW]
      rw [Nat.cast_sub (orth_card_pos _)]; simp
    simp_rw [hW']
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    unfold prob
    rw [Finset.sum_boole, Finset.card_product]
    push_cast
    field_simp
  unfold avg
  simp_rw [h1, div_pow]
  rw [← Finset.sum_div, div_div, div_le_iff₀ (by positivity)]
  refine h4.trans (le_of_eq ?_)
  rw [h5]; ring

lemma sum_ind {α : Type*} (S : Finset α) (R : α → Prop) [DecidablePred R] :
    ∑ x ∈ S, (if R x then (1 : ℚ) else 0) = S.card * prob S R := by
  rw [Finset.sum_boole]
  unfold prob
  by_cases h : (S.card : ℚ) = 0
  · have h' : S = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast h)
    simp [h']
  · field_simp

/-- **Capped second moment.** As `second_moment`, but the pairs `(y, y')` are split by a
predicate `Bad`. Off `Bad`, every orthogonal test vector satisfies `Sm`, and only those are
counted. On `Bad`, the cross term is capped by the orthogonality count of `Φ y` alone, which
costs one factor `μ` instead of two. -/
theorem second_moment_cap (Φ : Y → P → τ → ZMod q) (hadd : ∀ y a b, Φ y (a + b) = Φ y a + Φ y b)
    (E : Finset (τ → ZMod q)) (B B' : Finset Y) (hB : B.Nonempty) (hsub : B' ⊆ B)
    (Bad : Y × Y → Prop) (Sm : (τ ⊕ τ → ZMod q) → Prop) [DecidablePred Bad] [DecidablePred Sm]
    (hSm : ∀ yy, ¬ Bad yy → ∀ ℓ, (∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0) → Sm ℓ) :
    avg (fun a : P => (((B'.filter fun y => Φ y a ∈ E).card : ℚ) / B.card
        - (B'.card : ℚ) / B.card * (E.card / (q : ℚ) ^ Fintype.card τ)) ^ 2)
      ≤ 3 * (E.card / (q : ℚ) ^ Fintype.card τ) ^ 2 *
          ∑ ℓ ∈ ((univ : Finset (τ ⊕ τ → ZMod q)).erase 0).filter Sm,
            prob (B ×ˢ B) (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0)
        + E.card / (q : ℚ) ^ Fintype.card τ * (1 + E.card / (q : ℚ) ^ Fintype.card τ) *
            prob (B ×ˢ B) Bad
        + E.card / (q : ℚ) ^ Fintype.card τ *
          ∑ ℓ ∈ (univ : Finset (τ → ZMod q)).erase 0,
            prob (B ×ˢ B) (fun yy => (∀ a, ℓ ⬝ᵥ Φ yy.1 a = 0) ∧ Bad yy) := by
  set μ : ℚ := E.card / (q : ℚ) ^ Fintype.card τ with hμ
  have hq0 : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hμ0 : 0 ≤ μ := by positivity
  have hBc : (0 : ℚ) < B.card := by exact_mod_cast hB.card_pos
  have hPc : (0 : ℚ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  set X : Y → P → ℚ := fun y a => (if Φ y a ∈ E then (1 : ℚ) else 0) - μ with hX
  have h1 : ∀ a : P, ((B'.filter fun y => Φ y a ∈ E).card : ℚ) / B.card
      - (B'.card : ℚ) / B.card * μ = (∑ y ∈ B', X y a) / B.card := by
    intro a
    simp only [hX]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
    ring
  have h2 : ∀ a : P, (∑ y ∈ B', X y a) ^ 2 = ∑ yy ∈ B' ×ˢ B', X yy.1 a * X yy.2 a := by
    intro a; rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  set L₂ := ((univ : Finset (τ ⊕ τ → ZMod q)).erase 0).filter Sm with hL₂
  set L₁ := (univ : Finset (τ → ZMod q)).erase 0 with hL₁
  -- per-pair bound
  set W : Y × Y → ℚ := fun yy =>
    3 * μ ^ 2 * ∑ ℓ ∈ L₂, (if ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0 then (1 : ℚ) else 0)
    + μ * (1 + μ) * (if Bad yy then (1 : ℚ) else 0)
    + μ * ∑ ℓ ∈ L₁, (if (∀ a, ℓ ⬝ᵥ Φ yy.1 a = 0) ∧ Bad yy then (1 : ℚ) else 0) with hW
  have hW0 : ∀ yy, 0 ≤ W yy := fun yy => by
    simp only [hW]
    have a1 : 0 ≤ ∑ ℓ ∈ L₂, (if ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0 then (1 : ℚ) else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have a2 : 0 ≤ ∑ ℓ ∈ L₁, (if (∀ a, ℓ ⬝ᵥ Φ yy.1 a = 0) ∧ Bad yy then (1 : ℚ) else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have a3 : (0 : ℚ) ≤ (if Bad yy then (1 : ℚ) else 0) := by split_ifs <;> norm_num
    positivity
  -- the orthogonality counts as sums of indicators
  have hcnt : ∀ (ι : Type _) [Fintype ι] [DecidableEq ι] (Ψ : P → ι → ZMod q),
      ((orth Ψ).card : ℚ) - 1 = ∑ ℓ ∈ (univ : Finset (ι → ZMod q)).erase 0,
        (if ∀ a, ℓ ⬝ᵥ Ψ a = 0 then (1 : ℚ) else 0) := by
    intro ι _ _ Ψ
    rw [Finset.sum_boole]
    have : ((univ : Finset (ι → ZMod q)).erase 0).filter (fun ℓ => ∀ a, ℓ ⬝ᵥ Ψ a = 0)
        = (orth Ψ).erase 0 := by
      ext ℓ; simp only [orth, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
        and_true]
    rw [this, Finset.card_erase_of_mem (zero_mem_orth _), Nat.cast_sub (orth_card_pos _)]
    simp
  have h3 : ∀ yy : Y × Y, ∑ a, X yy.1 a * X yy.2 a ≤ Fintype.card P * W yy := by
    intro yy
    have i2 : 0 ≤ ∑ ℓ ∈ L₂, (if ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0 then (1 : ℚ) else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have i1 : 0 ≤ ∑ ℓ ∈ L₁, (if (∀ a, ℓ ⬝ᵥ Φ yy.1 a = 0) ∧ Bad yy then (1 : ℚ) else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    by_cases hb : Bad yy
    · have hc := cross_cap (Φ yy.1) (Φ yy.2) (hadd yy.1) E
      rw [hcnt] at hc
      refine hc.trans (mul_le_mul_of_nonneg_left ?_ hPc.le)
      simp only [hW, hb, and_true, ite_true, mul_one]
      have : 0 ≤ 3 * μ ^ 2 *
          ∑ ℓ ∈ L₂, (if ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0 then (1 : ℚ) else 0) := by
        positivity
      linarith
    · have hc := cross_le (Φ yy.1) (Φ yy.2) (hadd yy.1) (hadd yy.2) E
      rw [hcnt] at hc
      refine hc.trans (mul_le_mul_of_nonneg_left ?_ hPc.le)
      simp only [hW, hb, and_false, ite_false, mul_zero, add_zero, Finset.sum_const_zero]
      apply le_of_eq
      congr 1
      rw [hL₂, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      by_cases ho : ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0
      · simp only [ho, hSm yy hb ℓ ho, forall_const, ite_true]
      · simp only [ho, ite_false, ite_self]
  have h4 : ∑ a : P, (∑ y ∈ B', X y a) ^ 2 ≤ Fintype.card P * ∑ yy ∈ B ×ˢ B, W yy := by
    simp_rw [h2]
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun yy _ => h3 yy).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hPc.le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.product_subset_product hsub hsub)
      fun yy _ _ => hW0 yy
  -- count the other way round
  have h5 : ∑ yy ∈ B ×ˢ B, W yy = (B.card : ℚ) ^ 2 *
      (3 * μ ^ 2 * ∑ ℓ ∈ L₂, prob (B ×ˢ B) (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (Φ yy.1) (Φ yy.2) a = 0)
        + μ * (1 + μ) * prob (B ×ˢ B) Bad
        + μ * ∑ ℓ ∈ L₁, prob (B ×ˢ B) (fun yy => (∀ a, ℓ ⬝ᵥ Φ yy.1 a = 0) ∧ Bad yy)) := by
    simp only [hW]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_comm (s := B ×ˢ B) (t := L₂),
      Finset.sum_comm (s := B ×ˢ B) (t := L₁)]
    simp only [sum_ind]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.card_product]
    push_cast
    ring
  unfold avg
  simp_rw [h1, div_pow]
  rw [← Finset.sum_div, div_div, div_le_iff₀ (by positivity)]
  refine h4.trans (le_of_eq ?_)
  rw [h5]; ring

end Family

end RejOrder

end
end SecondMoment

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

omit [Field F] in
lemma exists_free_run (T : Finset (Fin n)) (ρ : ℕ) (hρ : ρ * (T.card + 1) ≤ n) :
    ∃ t₀, t₀ + ρ ≤ n ∧ ∀ a < ρ, ∀ s ∈ T, (s : ℕ) ≠ t₀ + a := by
  classical
  rcases Nat.eq_zero_or_pos ρ with rfl | hpos
  · exact ⟨0, by omega, fun a ha => absurd ha (by omega)⟩
  · have hcard : (T.image fun s : Fin n => (s : ℕ) / ρ).card < (range (T.card + 1)).card := by
      rw [Finset.card_range]
      exact lt_of_le_of_lt Finset.card_image_le (Nat.lt_succ_self _)
    obtain ⟨b, hb, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    rw [Finset.mem_range] at hb
    refine ⟨b * ρ, ?_, ?_⟩
    · calc b * ρ + ρ = ρ * (b + 1) := by ring
        _ ≤ ρ * (T.card + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ n := hρ
    · intro a ha s hs he
      apply hnot
      rw [Finset.mem_image]
      refine ⟨s, hs, ?_⟩
      rw [he, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt ha, Nat.zero_add]

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
# Counting test vectors by their NTT support

A test vector on a coordinate set `T` is a pair `(λ, λ')` of functions on `T`. Its joint support
is the set of NTT slots where some dual coordinate is nonzero. The probability that it is
orthogonal to the image decays with the size of the support, and by the uncertainty principle
few test vectors have small support. One-sided test vectors `(κ, 0)` are counted the same way,
with half the exponent (`card_suppIn1_le_prod`).
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

lemma sum_ext (T : Finset (Fin (K * n))) (g : T → ZMod q) (f : Fin (K * n) → ZMod q) :
    ∑ r : T, g r * f r = ∑ r, ext T g r * f r := by
  rw [← Finset.sum_subset (Finset.subset_univ T)
    (fun r _ hr => by rw [ext_out T g hr, zero_mul]),
    ← Finset.sum_coe_sort T (fun r => ext T g r * f r)]
  exact Finset.sum_congr rfl fun r _ => by rw [ext_coe]

/-- The two halves of a test vector. -/
def lam (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) : Fin (K * n) → ZMod q :=
  ext T fun r => ℓ (Sum.inl r)

def lam' (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) : Fin (K * n) → ZMod q :=
  ext T fun r => ℓ (Sum.inr r)

/-- The coordinates in `T` of `A·y`, as a function of the matrix parameter. -/
def PhiT (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    (T : Finset (Fin (K * n))) (y : Fin (L * n) → ℤ) (a : Fin K → Fin L → Fin n → ZMod q) :
    T → ZMod q :=
  fun r => (modMat mulmat a *ᵥ zc y) r

lemma PhiT_add {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)}
    (hadd : ∀ a b, mulmat (a + b) = mulmat a + mulmat b) (T : Finset (Fin (K * n)))
    (y : Fin (L * n) → ℤ) (a b : Fin K → Fin L → Fin n → ZMod q) :
    PhiT mulmat T y (a + b) = PhiT mulmat T y a + PhiT mulmat T y b := by
  funext r
  simp only [PhiT, Pi.add_apply, modMat_add mulmat hadd, Matrix.add_mulVec]

lemma dot_pair (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) (y y' : Fin (L * n) → ℤ)
    (a : Fin K → Fin L → Fin n → ZMod q) :
    ℓ ⬝ᵥ pairΦ (PhiT mulmat T y) (PhiT mulmat T y') a
      = ∑ r, lam T ℓ r * (modMat mulmat a *ᵥ zc y) r
        + ∑ r, lam' T ℓ r * (modMat mulmat a *ᵥ zc y') r := by
  simp only [dotProduct, pairΦ, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, PhiT]
  rw [lam, lam', ← sum_ext, ← sum_ext]

/-! ## Joint support and the per-vector probability bound -/

/-- NTT slots where some dual coordinate of the test vector is nonzero. -/
def jsupp (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) :
    Finset (Fin n) :=
  univ.filter fun k => ∃ i, dual ζ (lam T ℓ) i k ≠ 0 ∨ dual ζ (lam' T ℓ) i k ≠ 0

/-- For each slot in the support, the dual coordinates of one row that witnesses it. -/
def cOf (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) (k : Fin n) :
    ZMod q :=
  if hk : ∃ i, dual ζ (lam T ℓ) i k ≠ 0 ∨ dual ζ (lam' T ℓ) i k ≠ 0
  then dual ζ (lam T ℓ) (Classical.choose hk) k else 0

def cOf' (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) (k : Fin n) :
    ZMod q :=
  if hk : ∃ i, dual ζ (lam T ℓ) i k ≠ 0 ∨ dual ζ (lam' T ℓ) i k ≠ 0
  then dual ζ (lam' T ℓ) (Classical.choose hk) k else 0

lemma cOf_spec (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) (k : Fin n)
    (hk : ∃ i, dual ζ (lam T ℓ) i k ≠ 0 ∨ dual ζ (lam' T ℓ) i k ≠ 0) :
    cOf ζ T ℓ k = dual ζ (lam T ℓ) (Classical.choose hk) k ∧
    cOf' ζ T ℓ k = dual ζ (lam' T ℓ) (Classical.choose hk) k :=
  ⟨dif_pos hk, dif_pos hk⟩

lemma orth_prob {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (T : Finset (Fin (K * n)))
    (ℓ : T ⊕ T → ZMod q) :
    prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
        (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0)
      ≤ 1 / (2 * γ₁ : ℚ) ^ (L * (jsupp ζ T ℓ).card) := by
  have hS : ∀ k ∈ jsupp ζ T ℓ, cOf ζ T ℓ k ≠ 0 ∨ cOf' ζ T ℓ k ≠ 0 := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [(cOf_spec ζ T ℓ k hk').1, (cOf_spec ζ T ℓ k hk').2]
    exact Classical.choose_spec hk'
  have hmono : ∀ yy ∈ box γ₁ (L * n) ×ˢ box γ₁ (L * n),
      (∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0) →
      ∀ j, ∀ k ∈ jsupp ζ T ℓ, cOf ζ T ℓ k * ntt ζ (zc (q := q) yy.1) j k
        + cOf' ζ T ℓ k * ntt ζ (zc yy.2) j k = 0 := by
    intro yy _ horth j k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [(cOf_spec ζ T ℓ k hk').1, (cOf_spec ζ T ℓ k hk').2]
    exact slot_of_orth h (lam T ℓ) (lam' T ℓ) (zc yy.1) (zc yy.2)
      (fun a => by rw [← dot_pair]; exact horth a) _ j k
  exact le_trans (prob_mono _ hmono)
    (slot_prob h.inj hγ1 hγ (cOf ζ T ℓ) (cOf' ζ T ℓ) _ hS)

/-- An orthogonal test vector is supported on degenerate slots. -/
lemma jsupp_sub_degS {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) (y y' : Fin (L * n) → ℤ)
    (horth : ∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T y) (PhiT mulmat T y') a = 0) :
    jsupp ζ T ℓ ⊆ degS ζ y y' := by
  intro k hk
  have hk' := (Finset.mem_filter.mp hk).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, cOf ζ T ℓ k, cOf' ζ T ℓ k, ?_, fun j => ?_⟩
  · rw [(cOf_spec ζ T ℓ k hk').1, (cOf_spec ζ T ℓ k hk').2]
    exact Classical.choose_spec hk'
  · rw [(cOf_spec ζ T ℓ k hk').1, (cOf_spec ζ T ℓ k hk').2]
    exact slot_of_orth h (lam T ℓ) (lam' T ℓ) (zc y) (zc y')
      (fun a => by rw [← dot_pair]; exact horth a) _ j k

/-- A test vector with support of size `σ` is orthogonal, and there are at least `σ*`
degenerate slots, with probability at most the smaller of `(2γ₁)^(-L·σ)` and
`C(n - σ, σ* - σ) · (q + 1)^(σ* - σ) · (2γ₁)^(-L·max(σ, σ*))`. -/
lemma orth_deg_prob {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    {γ₁ : ℕ} (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (T : Finset (Fin (K * n)))
    (ℓ : T ⊕ T → ZMod q) (σs : ℕ) :
    prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
        (fun yy => (∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0)
          ∧ σs ≤ (degS ζ yy.1 yy.2).card)
      ≤ min (1 / (2 * γ₁ : ℚ) ^ (L * (jsupp ζ T ℓ).card))
          (((n - (jsupp ζ T ℓ).card).choose (σs - (jsupp ζ T ℓ).card)
            * ((q : ℚ) + 1) ^ (σs - (jsupp ζ T ℓ).card) : ℚ)
            / (2 * γ₁ : ℚ) ^ (L * ((jsupp ζ T ℓ).card + (σs - (jsupp ζ T ℓ).card)))) := by
  refine le_min ((prob_mono _ fun yy _ hy => hy.1).trans (orth_prob h hγ1 hγ T ℓ)) ?_
  have hS : ∀ k ∈ jsupp ζ T ℓ, cOf ζ T ℓ k ≠ 0 ∨ cOf' ζ T ℓ k ≠ 0 := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [(cOf_spec ζ T ℓ k hk').1, (cOf_spec ζ T ℓ k hk').2]
    exact Classical.choose_spec hk'
  refine le_trans (prob_mono _ fun yy _ hy => ⟨fun j k hk => ?_, ?_⟩)
    (deg_prob h.inj hγ1 hγ (cOf ζ T ℓ) (cOf' ζ T ℓ) (jsupp ζ T ℓ) hS (σs - (jsupp ζ T ℓ).card))
  · have hk' := (Finset.mem_filter.mp hk).2
    rw [(cOf_spec ζ T ℓ k hk').1, (cOf_spec ζ T ℓ k hk').2]
    exact slot_of_orth h (lam T ℓ) (lam' T ℓ) (zc yy.1) (zc yy.2)
      (fun a => by rw [← dot_pair]; exact hy.1 a) _ j k
  · have hsub := jsupp_sub_degS h T ℓ yy.1 yy.2 hy.1
    rw [Finset.card_sdiff_of_subset hsub]
    have := hy.2
    omega

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

/-- Two functions on `T` whose dual coordinates agree outside sets `S₀ i` that are no larger
than a run of exponents missing from row `i` of `T` are equal. -/
lemma eq_of_dual_eq {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (hζ0 : ∀ k, ζ k ≠ 0)
    (T : Finset (Fin (K * n))) (g₁ g₂ : T → ZMod q) (S₀ : Fin K → Finset (Fin n))
    (hS₀ : ∀ i, (S₀ i).card ≤ n / ((rowT T i).card + 1))
    (hd : ∀ i k, k ∉ S₀ i → dual ζ (ext T g₁) i k = dual ζ (ext T g₂) i k) : g₁ = g₂ := by
  have hΔ : ext T (g₁ - g₂) = 0 := by
    apply eq_zero_of_dual hζ
    intro i
    obtain ⟨t₀, ht₀, hfree⟩ := exists_free_run (rowT T i) (n / ((rowT T i).card + 1))
      (Nat.div_mul_le_self _ _)
    apply dual_vanish ζ hζ hζ0 _ (S₀ i) _ t₀ _ (hS₀ i)
    · intro a ha
      have hlt : t₀ + a < n := by omega
      have hnot : finProdFinEquiv (i, (⟨t₀ + a, hlt⟩ : Fin n)) ∉ T := by
        intro hin
        exact hfree a ha ⟨t₀ + a, hlt⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩) rfl
      have := dual_spec hζ (ext T (g₁ - g₂)) i ⟨t₀ + a, hlt⟩
      rw [ext_out T _ hnot] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · intro k hk
      rw [ext_sub, dual_sub, Pi.sub_apply, hd i k hk, sub_self]
  funext r
  have := congrFun hΔ r
  rw [ext_coe] at this
  exact sub_eq_zero.mp this

lemma eq_zero_of_jsupp {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (hζ0 : ∀ k, ζ k ≠ 0)
    (T : Finset (Fin (K * n))) (ℓ : T ⊕ T → ZMod q) (h : jsupp ζ T ℓ = ∅) : ℓ = 0 := by
  have hz : ∀ i k, dual ζ (lam T ℓ) i k = 0 ∧ dual ζ (lam' T ℓ) i k = 0 := by
    intro i k
    by_contra hne
    have : k ∈ jsupp ζ T ℓ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, by tauto⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty _)
  have h1 := eq_zero_of_dual hζ (lam T ℓ) fun i => funext fun k => (hz i k).1
  have h2 := eq_zero_of_dual hζ (lam' T ℓ) fun i => funext fun k => (hz i k).2
  funext x
  rcases x with r | r
  · have := congrFun h1 r; rwa [lam, ext_coe] at this
  · have := congrFun h2 r; rwa [lam', ext_coe] at this

lemma jsupp_zero (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) :
    jsupp ζ T (0 : T ⊕ T → ZMod q) = ∅ := by
  have e1 : lam T (0 : T ⊕ T → ZMod q) = 0 := by funext r; simp [lam, ext]
  have e2 : lam' T (0 : T ⊕ T → ZMod q) = 0 := by funext r; simp [lam', ext]
  have d0 : ∀ i, dual ζ (0 : Fin (K * n) → ZMod q) i = 0 := by
    intro i; unfold dual; rw [show blk (0 : Fin (K * n) → ZMod q) i = 0 from rfl,
      Matrix.mulVec_zero]
  ext k
  simp [jsupp, e1, e2, d0]

/-- Test vectors whose joint support lies in `S`. -/
def suppIn (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    Finset (T ⊕ T → ZMod q) :=
  univ.filter fun ℓ => jsupp ζ T ℓ ⊆ S

lemma card_suppIn_le_all (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    (suppIn ζ T S).card ≤ q ^ (2 * T.card) := by
  refine (Finset.card_le_univ _).trans (le_of_eq ?_)
  rw [Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_coe, two_mul]

/-- The uncertainty principle as a count: each row with `t_i` coefficients in `T` contributes
at most `q^(2·(|S| − n/(t_i+1)))` test vectors supported on `S`. -/
lemma card_suppIn_le_prod {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ)
    (hζ0 : ∀ k, ζ k ≠ 0) (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    (suppIn ζ T S).card
      ≤ ∏ i : Fin K, q ^ (2 * (S.card - n / ((rowT T i).card + 1))) := by
  have hex : ∀ i : Fin K, ∃ S₀ ⊆ S, S₀.card = min S.card (n / ((rowT T i).card + 1)) :=
    fun i => Finset.exists_subset_card_eq (min_le_left _ _)
  choose S₀ hsub hcard using hex
  set f : (T ⊕ T → ZMod q) →
      (∀ i : Fin K, (↥(S \ S₀ i) → ZMod q) × (↥(S \ S₀ i) → ZMod q)) :=
    fun ℓ i => (fun k => dual ζ (lam T ℓ) i k, fun k => dual ζ (lam' T ℓ) i k) with hf
  have hinj : Set.InjOn f (suppIn ζ T S : Set (T ⊕ T → ZMod q)) := by
    intro ℓ₁ h₁ ℓ₂ h₂ he
    have hs₁ : jsupp ζ T ℓ₁ ⊆ S := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    have hs₂ : jsupp ζ T ℓ₂ ⊆ S := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    have hout : ∀ (ℓ : T ⊕ T → ZMod q), jsupp ζ T ℓ ⊆ S → ∀ i k, k ∉ S →
        dual ζ (lam T ℓ) i k = 0 ∧ dual ζ (lam' T ℓ) i k = 0 := by
      intro ℓ hs i k hk
      by_contra hne
      exact hk (hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, by tauto⟩))
    have hagree : ∀ i k, k ∉ S₀ i →
        dual ζ (lam T ℓ₁) i k = dual ζ (lam T ℓ₂) i k ∧
        dual ζ (lam' T ℓ₁) i k = dual ζ (lam' T ℓ₂) i k := by
      intro i k hk
      by_cases hkS : k ∈ S
      · have hmem : k ∈ S \ S₀ i := Finset.mem_sdiff.mpr ⟨hkS, hk⟩
        have e := congrFun he i
        simp only [hf, Prod.mk.injEq] at e
        exact ⟨congrFun e.1 ⟨k, hmem⟩, congrFun e.2 ⟨k, hmem⟩⟩
      · rw [(hout ℓ₁ hs₁ i k hkS).1, (hout ℓ₂ hs₂ i k hkS).1, (hout ℓ₁ hs₁ i k hkS).2,
          (hout ℓ₂ hs₂ i k hkS).2]
        exact ⟨rfl, rfl⟩
    have hle : ∀ i, (S₀ i).card ≤ n / ((rowT T i).card + 1) :=
      fun i => (hcard i).le.trans (min_le_right _ _)
    have e1 := eq_of_dual_eq hζ hζ0 T (fun r => ℓ₁ (Sum.inl r)) (fun r => ℓ₂ (Sum.inl r)) S₀ hle
      (fun i k hk => (hagree i k hk).1)
    have e2 := eq_of_dual_eq hζ hζ0 T (fun r => ℓ₁ (Sum.inr r)) (fun r => ℓ₂ (Sum.inr r)) S₀ hle
      (fun i k hk => (hagree i k hk).2)
    funext x
    rcases x with r | r
    · exact congrFun e1 r
    · exact congrFun e2 r
  refine (Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    hinj).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_coe,
    Finset.card_sdiff_of_subset (hsub i), hcard i, ← pow_add, two_mul]
  congr 2 <;> omega

/-! ## Test vectors on one side -/

lemma dot_inl {P τ : Type*} [Fintype τ] (Φ₁ Φ₂ : P → τ → ZMod q) (κ : τ → ZMod q) (a : P) :
    (Sum.elim κ 0 : τ ⊕ τ → ZMod q) ⬝ᵥ pairΦ Φ₁ Φ₂ a = κ ⬝ᵥ Φ₁ a := by
  simp [dotProduct, pairΦ, Fintype.sum_sum_type]

/-- Test vectors `(κ, 0)` whose support lies in `S`. -/
def suppIn1 (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    Finset (T → ZMod q) :=
  univ.filter fun κ => jsupp ζ T (Sum.elim κ 0) ⊆ S

lemma card_suppIn1_le_all (ζ : Fin n → ZMod q) (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    (suppIn1 ζ T S).card ≤ q ^ T.card := by
  refine (Finset.card_le_univ _).trans (le_of_eq ?_)
  rw [Fintype.card_fun, ZMod.card, Fintype.card_coe]

/-- One-sided form of `card_suppIn_le_prod`: each row contributes at most
`q^(|S| − n/(t_i+1))`. -/
lemma card_suppIn1_le_prod {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ)
    (hζ0 : ∀ k, ζ k ≠ 0) (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    (suppIn1 ζ T S).card
      ≤ ∏ i : Fin K, q ^ (S.card - n / ((rowT T i).card + 1)) := by
  have hex : ∀ i : Fin K, ∃ S₀ ⊆ S, S₀.card = min S.card (n / ((rowT T i).card + 1)) :=
    fun i => Finset.exists_subset_card_eq (min_le_left _ _)
  choose S₀ hsub hcard using hex
  set f : (T → ZMod q) → (∀ i : Fin K, ↥(S \ S₀ i) → ZMod q) :=
    fun κ i k => dual ζ (ext T κ) i k with hf
  have hinj : Set.InjOn f (suppIn1 ζ T S : Set (T → ZMod q)) := by
    intro κ₁ h₁ κ₂ h₂ he
    have hs₁ : jsupp ζ T (Sum.elim κ₁ 0) ⊆ S := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    have hs₂ : jsupp ζ T (Sum.elim κ₂ 0) ⊆ S := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    have hout : ∀ (κ : T → ZMod q), jsupp ζ T (Sum.elim κ 0) ⊆ S → ∀ i k, k ∉ S →
        dual ζ (ext T κ) i k = 0 := by
      intro κ hs i k hk
      by_contra hne
      exact hk (hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, Or.inl hne⟩))
    have hagree : ∀ i k, k ∉ S₀ i → dual ζ (ext T κ₁) i k = dual ζ (ext T κ₂) i k := by
      intro i k hk
      by_cases hkS : k ∈ S
      · have hmem : k ∈ S \ S₀ i := Finset.mem_sdiff.mpr ⟨hkS, hk⟩
        exact congrFun (congrFun he i) ⟨k, hmem⟩
      · rw [hout κ₁ hs₁ i k hkS, hout κ₂ hs₂ i k hkS]
    have hle : ∀ i, (S₀ i).card ≤ n / ((rowT T i).card + 1) :=
      fun i => (hcard i).le.trans (min_le_right _ _)
    exact eq_of_dual_eq hζ hζ0 T κ₁ κ₂ S₀ hle hagree
  refine (Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    hinj).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.card_fun, ZMod.card, Fintype.card_coe,
    Finset.card_sdiff_of_subset (hsub i), hcard i]
  congr 1; omega

end RejOrder

end
end ModuleCount

section Profile
/-!
# From coordinate sets to a closed-form sum

How many test vectors have NTT support in `S` depends on how the coordinates of `T` are spread
over the `K` rows. This file bounds the count by a function of `|T|` and `|S|` alone (a
Jensen-type inequality over the rows).
-/

open Finset Matrix

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

/-- Bound on `∑ i, (σ - n / (t_i + 1))` over all ways to split `t` coordinates over `K` rows. -/
def eB (n K t σ : ℕ) : ℕ :=
  (Finset.Icc 1 K).sup fun r => (r * (σ + 1) * (t + r) - (n + 1) * r * r) / (t + r)

lemma profile_le (n K σ : ℕ) (tt : Fin K → ℕ) :
    ∑ i, (σ - n / (tt i + 1)) ≤ eB n K (∑ i, tt i) σ := by
  set t := ∑ i, tt i with ht
  set R := (univ : Finset (Fin K)).filter (fun i => n / (tt i + 1) < σ) with hR
  have hsum : ∑ i, (σ - n / (tt i + 1)) = ∑ i ∈ R, (σ - n / (tt i + 1)) := by
    rw [hR, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · omega
  rw [hsum]
  rcases Nat.eq_zero_or_pos R.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; exact Nat.zero_le _
  set r := R.card with hr
  have hrK : r ≤ K := by simpa using Finset.card_le_univ R
  refine le_trans ?_ (Finset.le_sup (f := fun r => (r * (σ + 1) * (t + r) - (n + 1) * r * r) / (t + r))
    (Finset.mem_Icc.mpr ⟨hpos, hrK⟩))
  have htr : 0 < t + r := by omega
  rw [Nat.le_div_iff_mul_le htr]
  apply Nat.le_sub_of_add_le
  -- work in ℚ
  have hrq : (0 : ℚ) < r := by exact_mod_cast hpos
  have htrq : (0 : ℚ) < (t : ℚ) + r := by exact_mod_cast htr
  have h1 : ∀ i ∈ R, ((σ - n / (tt i + 1) : ℕ) : ℚ) ≤ (σ : ℚ) + 1 - ((n : ℚ) + 1) / ((tt i : ℚ) + 1) := by
    intro i hi
    have hlt : n / (tt i + 1) < σ := (Finset.mem_filter.mp hi).2
    rw [Nat.cast_sub hlt.le]
    have hd : (0 : ℚ) < (tt i : ℚ) + 1 := by positivity
    have hk : n < (tt i + 1) * (n / (tt i + 1) + 1) := Nat.lt_mul_div_succ n (by omega)
    have hk' : ((n : ℚ) + 1) ≤ ((tt i : ℚ) + 1) * (((n / (tt i + 1) : ℕ) : ℚ) + 1) := by
      exact_mod_cast hk
    have : ((n : ℚ) + 1) / ((tt i : ℚ) + 1) ≤ ((n / (tt i + 1) : ℕ) : ℚ) + 1 := by
      rw [div_le_iff₀ hd]; linarith
    linarith
  have h2 : (r : ℚ) ^ 2 / ((t : ℚ) + r) ≤ ∑ i ∈ R, (1 : ℚ) / ((tt i : ℚ) + 1) := by
    have hs := Finset.sq_sum_div_le_sum_sq_div R (fun _ => (1 : ℚ))
      (g := fun i => (tt i : ℚ) + 1) (fun i _ => by positivity)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_pow] at hs
    refine le_trans ?_ hs
    have hden : ∑ i ∈ R, ((tt i : ℚ) + 1) ≤ (t : ℚ) + r := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      have : ∑ i ∈ R, (tt i : ℚ) ≤ (t : ℚ) := by
        rw [ht]; push_cast
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => Nat.cast_nonneg _
      linarith
    have hden0 : (0 : ℚ) < ∑ i ∈ R, ((tt i : ℚ) + 1) :=
      Finset.sum_pos (fun i _ => by positivity) (Finset.card_pos.mp hpos)
    exact div_le_div_of_nonneg_left (by positivity) hden0 hden
  have h3 : ((∑ i ∈ R, (σ - n / (tt i + 1)) : ℕ) : ℚ)
      ≤ (r : ℚ) * ((σ : ℚ) + 1) - ((n : ℚ) + 1) * ((r : ℚ) ^ 2 / ((t : ℚ) + r)) := by
    push_cast
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have : ∑ i ∈ R, ((n : ℚ) + 1) / ((tt i : ℚ) + 1)
        = ((n : ℚ) + 1) * ∑ i ∈ R, (1 : ℚ) / ((tt i : ℚ) + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have hn : (0 : ℚ) ≤ (n : ℚ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hn]
  have h4 : ((∑ i ∈ R, (σ - n / (tt i + 1)) : ℕ) : ℚ) * ((t : ℚ) + r) + ((n : ℚ) + 1) * r * r
      ≤ (r : ℚ) * ((σ : ℚ) + 1) * ((t : ℚ) + r) := by
    have := mul_le_mul_of_nonneg_right h3 htrq.le
    have e : ((r : ℚ) * ((σ : ℚ) + 1) - ((n : ℚ) + 1) * ((r : ℚ) ^ 2 / ((t : ℚ) + r))) * ((t : ℚ) + r)
        = (r : ℚ) * ((σ : ℚ) + 1) * ((t : ℚ) + r) - ((n : ℚ) + 1) * r * r := by
      field_simp
    rw [e] at this
    linarith
  exact_mod_cast h4

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ}

lemma sum_rowT (T : Finset (Fin (K * n))) : ∑ i, (rowT T i).card = T.card := by
  have h1 : T.card = ∑ c : Fin (K * n), if c ∈ T then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]; simp
  rw [h1, sum_blocks]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowT, Finset.card_filter]

variable (q n K L) in
/-- Bound on the expected number of nontrivial orthogonal test vectors on a coordinate set of
size `t`, with the NTT supports grouped by size `σ`. -/
def QBt (γ₁ t : ℕ) : ℚ :=
  ∑ σ ∈ range (n + 1), (n.choose σ : ℚ) *
    ((((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) - 1) / (2 * γ₁ : ℚ) ^ (L * σ))

/-- The uncertainty-principle count, in terms of `|T|` and `|S|` only. -/
lemma card_suppIn_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (hζ0 : ∀ k, ζ k ≠ 0)
    (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    (suppIn ζ T S).card ≤ q ^ (2 * min T.card (eB n K T.card S.card)) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  rcases le_total T.card (eB n K T.card S.card) with hle | hle
  · rw [min_eq_left hle]; exact card_suppIn_le_all ζ T S
  · rw [min_eq_right hle]
    refine (card_suppIn_le_prod hζ hζ0 T S).trans ?_
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
    apply Nat.pow_le_pow_right hq1
    apply Nat.mul_le_mul_left
    have := profile_le n K S.card (fun i => (rowT T i).card)
    rwa [sum_rowT] at this

/-- One-sided form of `card_suppIn_le`: the exponent is not doubled. -/
lemma card_suppIn1_le {ζ : Fin n → ZMod q} (hζ : Function.Injective ζ) (hζ0 : ∀ k, ζ k ≠ 0)
    (T : Finset (Fin (K * n))) (S : Finset (Fin n)) :
    (suppIn1 ζ T S).card ≤ q ^ (min T.card (eB n K T.card S.card)) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  rcases le_total T.card (eB n K T.card S.card) with hle | hle
  · rw [min_eq_left hle]; exact card_suppIn1_le_all ζ T S
  · rw [min_eq_right hle]
    refine (card_suppIn1_le_prod hζ hζ0 T S).trans ?_
    rw [Finset.prod_pow_eq_pow_sum]
    apply Nat.pow_le_pow_right hq1
    have := profile_le n K S.card (fun i => (rowT T i).card)
    rwa [sum_rowT] at this

variable (q n K L) in
/-- As `QBt`, but only for supports of size below `σ*`. -/
def QBs (γ₁ σs t : ℕ) : ℚ :=
  ∑ σ ∈ range σs, (n.choose σ : ℚ) *
    ((((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) - 1) / (2 * γ₁ : ℚ) ^ (L * σ))

variable (q n L) in
/-- Bound on the probability of at least `σ*` degenerate slots. -/
def PDq (γ₁ σs : ℕ) : ℚ :=
  (n.choose σs * ((q : ℚ) + 1) ^ σs : ℚ) / (2 * γ₁ : ℚ) ^ (L * σs)

variable (q n L) in
/-- Bound on the probability that a one-sided test vector with support of size `σ` is orthogonal
and there are at least `σ*` degenerate slots. -/
def hBq (γ₁ σs σ : ℕ) : ℚ :=
  min (1 / (2 * γ₁ : ℚ) ^ (L * σ))
    (((n - σ).choose (σs - σ) * ((q : ℚ) + 1) ^ (σs - σ) : ℚ)
      / (2 * γ₁ : ℚ) ^ (L * (σ + (σs - σ))))

variable (q n K L) in
/-- Bound on the expected number of nontrivial one-sided orthogonal test vectors on a coordinate
set of size `t`, on the event of at least `σ*` degenerate slots. -/
def RBt (γ₁ σs t : ℕ) : ℚ :=
  ∑ σ ∈ range (n + 1), (n.choose σ : ℚ) *
    ((((q ^ (min t (eB n K t σ)) : ℕ) : ℚ) - 1) * hBq q n L γ₁ σs σ)

/-- Regroup a sum over coordinate sets of size at most `s` by cardinality. -/
lemma sum_idx {m : ℕ} (s : ℕ) (F : ℕ → ℚ) :
    ∑ T ∈ (univ : Finset (Fin m)).powerset with T.card ≤ s, F T.card
      = ∑ t ∈ range (m + 1), (m.choose t : ℚ) * (if t ≤ s then F t else 0) := by
  rw [Finset.sum_filter, Finset.sum_powerset_apply_card (fun t => if t ≤ s then F t else 0),
    Finset.card_univ, Fintype.card_fin]
  exact Finset.sum_congr rfl fun t _ => by rw [nsmul_eq_mul]

end RejOrder

end
end Profile

section ModuleMain
/-!
# Sparse-test near-uniformity for a module-structured matrix

The restated hypothesis 4 (`SparseFailAvg`) holds for `A` uniform in `R_q^{K×L}`, with an explicit
error. Two routes: `sparseFailAvg_module` bounds every pair `(y, y')` by its pair test vectors;
`sparseFailAvg_module_cap` does so only when fewer than `σ*` slots are degenerate, and otherwise
caps the pair by the one-sided test vectors of `y`.
-/

open Finset Matrix

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace RejOrder

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ} {γ₁ γ₂ β mb : ℕ}

lemma Q_le {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (T : Finset (Fin (K * n))) :
    ∑ ℓ ∈ (univ : Finset (T ⊕ T → ZMod q)).erase 0,
        prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
          (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0)
      ≤ QBt q n K L γ₁ T.card := by
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  set g : Finset (Fin n) → ℚ := fun S => 1 / (2 * γ₁ : ℚ) ^ (L * S.card) with hg
  set G : ℕ → ℚ := fun σ => (((q ^ (2 * min T.card (eB n K T.card σ)) : ℕ) : ℚ) - 1)
    / (2 * γ₁ : ℚ) ^ (L * σ) with hGdef
  have hG0 : ∀ σ, 0 ≤ G σ := fun σ => div_nonneg (by
    have : (1 : ℚ) ≤ ((q ^ (2 * min T.card (eB n K T.card σ)) : ℕ) : ℚ) := by
      exact_mod_cast Nat.one_le_pow _ _ hq1
    linarith) (by positivity)
  have hmaps : ∀ ℓ ∈ (univ : Finset (T ⊕ T → ZMod q)).erase 0,
      jsupp ζ T ℓ ∈ (univ : Finset (Finset (Fin n))).erase ∅ := by
    intro ℓ hℓ
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    exact (Finset.mem_erase.mp hℓ).1 (eq_zero_of_jsupp h.inj h.ne0 T ℓ he)
  calc ∑ ℓ ∈ (univ : Finset (T ⊕ T → ZMod q)).erase 0,
        prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
          (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0)
      ≤ ∑ ℓ ∈ (univ : Finset (T ⊕ T → ZMod q)).erase 0, g (jsupp ζ T ℓ) :=
        Finset.sum_le_sum fun ℓ _ => orth_prob h hγ1 hγ T ℓ
    _ = ∑ S ∈ (univ : Finset (Finset (Fin n))).erase ∅,
          ∑ ℓ ∈ (univ : Finset (T ⊕ T → ZMod q)).erase 0 with jsupp ζ T ℓ = S, g S :=
        (Finset.sum_fiberwise_of_maps_to' hmaps g).symm
    _ ≤ ∑ S ∈ (univ : Finset (Finset (Fin n))).erase ∅, G S.card := by
        refine Finset.sum_le_sum fun S _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, hg, mul_one_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hsub : ((univ : Finset (T ⊕ T → ZMod q)).erase 0).filter
            (fun ℓ => jsupp ζ T ℓ = S) ⊆ (suppIn ζ T S).erase 0 := by
          intro ℓ hℓ
          rw [Finset.mem_filter] at hℓ
          refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hℓ.1).1, ?_⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ.2.le⟩
        have h0 : (0 : T ⊕ T → ZMod q) ∈ suppIn ζ T S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [jsupp_zero]; exact Finset.empty_subset _⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem h0] at hc
        replace hc := hc.trans (Nat.sub_le_sub_right (card_suppIn_le h.inj h.ne0 T S) 1)
        have := Nat.cast_le (α := ℚ).mpr hc
        rwa [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_one] at this
    _ ≤ ∑ S ∈ (univ : Finset (Finset (Fin n))), G S.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun S _ _ => hG0 _
    _ = QBt q n K L γ₁ T.card := by
        rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ,
          Fintype.card_fin]
        unfold QBt
        exact Finset.sum_congr rfl fun σ _ => by rw [nsmul_eq_mul]

/-! ## The event "all of `T` fail" as a product set -/

variable (q γ₂ β) in
/-- Values of `w` restricted to `T` for which every coordinate fails the r₀ check. -/
def failE (v : Fin (K * n) → ℤ) (T : Finset (Fin (K * n))) : Finset (T → ZMod q) :=
  Fintype.piFinset fun r : T =>
    (univ : Finset (ZMod q)).filter fun x => (γ₂ : ℤ) - β ≤ |lowBits q γ₂ x - v r|

lemma failE_card (hp : Params q γ₁ γ₂ β mb) {v : Fin (K * n) → ℤ} (hv : Bounded β v)
    (T : Finset (Fin (K * n))) :
    ((failE q γ₂ β v T).card : ℚ) / (q : ℚ) ^ Fintype.card T = pR q γ₂ β mb ^ T.card := by
  rw [failE, Fintype.card_piFinset]
  simp_rw [fail_card hp _ (hv _)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  push_cast
  rw [← div_pow, ← pR_eq hp]

lemma mem_failE (mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q))
    (v : Fin (K * n) → ℤ) (T : Finset (Fin (K * n))) (y : Fin (L * n) → ℤ)
    (a : Fin K → Fin L → Fin n → ZMod q) :
    PhiT mulmat T y a ∈ failE q γ₂ β v T ↔ ∀ j ∈ T, fR q γ₂ β (modMat mulmat a) v j y := by
  simp only [failE, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Subtype.forall]
  rfl

lemma pR_pos (hp : Params q γ₁ γ₂ β mb) : 0 < pR q γ₂ β mb := by
  rw [← pR_eq hp]
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply div_pos _ hq
  have : mb * (2 * (γ₂ - β) - 1) < q := by
    rw [hp.q_eq]
    have h1 : 2 * (γ₂ - β) - 1 ≤ 2 * γ₂ := by omega
    have := Nat.mul_le_mul_left mb h1
    nlinarith
  exact_mod_cast Nat.sub_pos_of_lt this

/-- Second moment of the joint deviation for one coordinate set `T`. -/
lemma moment_T (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) {v : Fin (K * n) → ℤ} (hv : Bounded β v) (T : Finset (Fin (K * n)))
    (B' : Finset (Fin (L * n) → ℤ)) (hsub : B' ⊆ box γ₁ (L * n)) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2)
      ≤ 3 * (pR q γ₂ β mb ^ T.card) ^ 2 * QBt q n K L γ₁ T.card := by
  have hγ1 : 0 < γ₁ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  have hBne : (box γ₁ (L * n)).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_box_nat]; positivity
  have hsm := second_moment (PhiT (K := K) (L := L) mulmat T)
    (fun y a b => PhiT_add h.add T y a b) (failE q γ₂ β v T) (box γ₁ (L * n)) B' hBne hsub
  rw [failE_card hp hv] at hsm
  have key : ∀ (a : Fin K → Fin L → Fin n → ZMod q)
      (inst : DecidablePred fun y => ∀ j ∈ T, fR q γ₂ β (modMat mulmat a) v j y),
      (@Finset.filter _ (fun y => ∀ j ∈ T, fR q γ₂ β (modMat mulmat a) v j y) inst B').card
        = (B'.filter fun y => PhiT mulmat T y a ∈ failE q γ₂ β v T).card := by
    intro a inst
    congr 1
    ext y
    simp only [Finset.mem_filter, mem_failE]
  have hpR := pR_nonneg hp
  have hnn : (0 : ℚ) ≤ 3 * (pR q γ₂ β mb ^ T.card) ^ 2 := by positivity
  have hsm' : avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      (((B'.filter fun y => PhiT mulmat T y a ∈ failE q γ₂ β v T).card : ℚ)
            / (box γ₁ (L * n)).card
          - (B'.card : ℚ) / (box γ₁ (L * n)).card * pR q γ₂ β mb ^ T.card) ^ 2)
      ≤ 3 * (pR q γ₂ β mb ^ T.card) ^ 2 * QBt q n K L γ₁ T.card := by
    refine hsm.trans (mul_le_mul_of_nonneg_left ?_ hnn)
    exact Q_le (L := L) h hγ1 hγ T
  have e : ∀ a : Fin K → Fin L → Fin n → ZMod q,
      (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2
      = (((B'.filter fun y => PhiT mulmat T y a ∈ failE q γ₂ β v T).card : ℚ)
            / (box γ₁ (L * n)).card
          - (B'.card : ℚ) / (box γ₁ (L * n)).card * pR q γ₂ β mb ^ T.card) ^ 2 := by
    intro a
    unfold jdev
    rw [sq_abs, key]
  simp_rw [e]
  exact hsm'

variable (q n K L γ₁ γ₂ β mb) in
/-- The closed-form error: a double sum over `t = |T|` and `σ = |S|`. -/
def Gt (s : ℕ) : ℚ :=
  (∑ t ∈ range (K * n + 1), ((K * n).choose t : ℚ) *
      (if t ≤ s then pR q γ₂ β mb ^ t else 0))
  * ∑ t ∈ range (K * n + 1), ((K * n).choose t : ℚ) *
      (if t ≤ s then 3 * pR q γ₂ β mb ^ t * QBt q n K L γ₁ t else 0)

/-- **Sparse-test near-uniformity for a module-structured matrix.** For `A` uniform in
`R_q^{K×L}`, the total deviation of the "all of `T` fail" events is at most `δ` on average,
provided `δ²` dominates the explicit double sum `Gt`. -/
theorem sparseFailAvg_module (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) {s : ℕ} {δ : ℚ} (hδ : 0 ≤ δ)
    (hG : Gt q n K L γ₁ γ₂ β mb s ≤ δ ^ 2) :
    SparseFailAvg q γ₁ γ₂ β mb
      (fun a : Fin K → Fin L → Fin n → ZMod q => modMat (K := K) (L := L) mulmat a) s δ := by
  unfold Gt at hG
  rw [← sum_idx s (fun t => pR q γ₂ β mb ^ t),
    ← sum_idx s (fun t => 3 * pR q γ₂ β mb ^ t * QBt q n K L γ₁ t)] at hG
  intro v hv B' hsub
  set idx := (univ : Finset (Fin (K * n))).powerset.filter (fun T => T.card ≤ s) with hidx
  set p := pR q γ₂ β mb with hpdef
  have hp0 : 0 < p := pR_pos hp
  set X : (Fin K → Fin L → Fin n → ZMod q) → ℚ := fun a =>
    jdevSum q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' s with hX
  have hX0 : ∀ a, 0 ≤ X a := fun a => Finset.sum_nonneg fun T _ => abs_nonneg _
  set W : ℚ := ∑ T ∈ idx, p ^ T.card with hW
  have hW0 : 0 < W := by
    apply Finset.sum_pos (fun T _ => by positivity)
    exact ⟨∅, by simp [hidx]⟩
  -- weighted Cauchy–Schwarz over the coordinate sets
  have h1 : ∀ a, X a ^ 2 ≤ W * ∑ T ∈ idx,
      (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2 / p ^ T.card := by
    intro a
    have := Finset.sq_sum_div_le_sum_sq_div idx
      (fun T => jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T)
      (g := fun T => p ^ T.card) (fun T _ => by positivity)
    rw [div_le_iff₀ hW0] at this
    rw [mul_comm]; exact this
  -- Jensen over the matrix
  have hcard : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
    exact_mod_cast Fintype.card_pos
  have h2 : avg X ^ 2 ≤ avg (fun a => X a ^ 2) := by
    unfold avg
    rw [div_pow, div_le_div_iff₀ (by positivity) hcard]
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin K → Fin L → Fin n → ZMod q)))
      (f := X)
    rw [Finset.card_univ] at this
    nlinarith
  have h3 : avg (fun a => X a ^ 2) ≤ W * ∑ T ∈ idx, 3 * p ^ T.card * QBt q n K L γ₁ T.card := by
    refine (avg_mono h1).trans ?_
    rw [avg_mul_left, avg_finset_sum]
    apply mul_le_mul_of_nonneg_left _ hW0.le
    refine Finset.sum_le_sum fun T _ => ?_
    have hm := moment_T hp h hγ hv T B' hsub
    have hpt : (0 : ℚ) < p ^ T.card := by positivity
    have e : avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2 / p ^ T.card)
        = avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2) / p ^ T.card := by
      unfold avg; rw [← Finset.sum_div]; ring
    rw [e, div_le_iff₀ hpt]
    calc _ ≤ 3 * (p ^ T.card) ^ 2 * QBt q n K L γ₁ T.card := hm
      _ = _ := by ring
  have h4 : avg X ^ 2 ≤ δ ^ 2 := (h2.trans h3).trans hG
  have hav : 0 ≤ avg X := avg_nonneg hX0
  by_contra hcon
  rw [not_le] at hcon
  have := pow_lt_pow_left₀ hcon hδ two_ne_zero
  linarith

/-! ## The capped route -/

/-- As `Q_le`, for the test vectors with support of size below `σ*`. -/
lemma Qs_le {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (T : Finset (Fin (K * n))) (σs : ℕ) (hσs : σs ≤ n + 1) :
    ∑ ℓ ∈ ((univ : Finset (T ⊕ T → ZMod q)).erase 0).filter (fun ℓ => (jsupp ζ T ℓ).card < σs),
        prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
          (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0)
      ≤ QBs q n K L γ₁ σs T.card := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  set g : Finset (Fin n) → ℚ := fun S => 1 / (2 * γ₁ : ℚ) ^ (L * S.card) with hg
  set G : ℕ → ℚ := fun σ => (((q ^ (2 * min T.card (eB n K T.card σ)) : ℕ) : ℚ) - 1)
    / (2 * γ₁ : ℚ) ^ (L * σ) with hGdef
  have hG0 : ∀ σ, 0 ≤ G σ := fun σ => div_nonneg (by
    have : (1 : ℚ) ≤ ((q ^ (2 * min T.card (eB n K T.card σ)) : ℕ) : ℚ) := by
      exact_mod_cast Nat.one_le_pow _ _ hq1
    linarith) (by positivity)
  set L₂ := ((univ : Finset (T ⊕ T → ZMod q)).erase 0).filter
    (fun ℓ => (jsupp ζ T ℓ).card < σs) with hL₂
  set 𝒮 := ((univ : Finset (Finset (Fin n))).erase ∅).filter (fun S => S.card < σs) with h𝒮
  have hmaps : ∀ ℓ ∈ L₂, jsupp ζ T ℓ ∈ 𝒮 := by
    intro ℓ hℓ
    rw [hL₂, Finset.mem_filter] at hℓ
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩, hℓ.2⟩
    exact (Finset.mem_erase.mp hℓ.1).1 (eq_zero_of_jsupp h.inj h.ne0 T ℓ he)
  calc ∑ ℓ ∈ L₂, prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
          (fun yy => ∀ a, ℓ ⬝ᵥ pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0)
      ≤ ∑ ℓ ∈ L₂, g (jsupp ζ T ℓ) :=
        Finset.sum_le_sum fun ℓ _ => orth_prob h hγ1 hγ T ℓ
    _ = ∑ S ∈ 𝒮, ∑ ℓ ∈ L₂ with jsupp ζ T ℓ = S, g S :=
        (Finset.sum_fiberwise_of_maps_to' hmaps g).symm
    _ ≤ ∑ S ∈ 𝒮, G S.card := by
        refine Finset.sum_le_sum fun S _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, hg, mul_one_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hsub : L₂.filter (fun ℓ => jsupp ζ T ℓ = S) ⊆ (suppIn ζ T S).erase 0 := by
          intro ℓ hℓ
          rw [Finset.mem_filter, hL₂, Finset.mem_filter] at hℓ
          refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hℓ.1.1).1, ?_⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ.2.le⟩
        have h0 : (0 : T ⊕ T → ZMod q) ∈ suppIn ζ T S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [jsupp_zero]; exact Finset.empty_subset _⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem h0] at hc
        replace hc := hc.trans (Nat.sub_le_sub_right (card_suppIn_le h.inj h.ne0 T S) 1)
        have := Nat.cast_le (α := ℚ).mpr hc
        rwa [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_one] at this
    _ ≤ ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card < σs), G S.card :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (Finset.erase_subset _ _)) fun S _ _ => hG0 _
    _ = ∑ σ ∈ range (n + 1), (n.choose σ : ℚ) * (if σ < σs then G σ else 0) := by
        rw [Finset.sum_filter, ← Finset.powerset_univ,
          Finset.sum_powerset_apply_card (fun σ => if σ < σs then G σ else 0), Finset.card_univ,
          Fintype.card_fin]
        exact Finset.sum_congr rfl fun σ _ => by rw [nsmul_eq_mul]
    _ = ∑ σ ∈ range σs, (n.choose σ : ℚ) * (if σ < σs then G σ else 0) :=
        (Finset.sum_subset (Finset.range_subset_range.mpr hσs) fun σ _ hσ => by
          rw [Finset.mem_range] at hσ; rw [if_neg hσ, mul_zero]).symm
    _ = QBs q n K L γ₁ σs T.card := by
        unfold QBs
        exact Finset.sum_congr rfl fun σ hσ => by rw [if_pos (Finset.mem_range.mp hσ)]

/-- The one-sided orthogonal test vectors on the event of at least `σ*` degenerate slots. -/
lemma R_le {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ1 : 0 < γ₁) (hγ : 2 * γ₁ ≤ q) (T : Finset (Fin (K * n))) (σs : ℕ) :
    ∑ κ ∈ (univ : Finset (T → ZMod q)).erase 0,
        prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
          (fun yy => (∀ a, κ ⬝ᵥ PhiT mulmat T yy.1 a = 0) ∧ σs ≤ (degS ζ yy.1 yy.2).card)
      ≤ RBt q n K L γ₁ σs T.card := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  set g : Finset (Fin n) → ℚ := fun S => hBq q n L γ₁ σs S.card with hg
  set G : ℕ → ℚ := fun σ => ((((q ^ (min T.card (eB n K T.card σ))) : ℕ) : ℚ) - 1)
    * hBq q n L γ₁ σs σ with hGdef
  have hh0 : ∀ σ, 0 ≤ hBq q n L γ₁ σs σ := fun σ => le_min (by positivity) (by positivity)
  have hG0 : ∀ σ, 0 ≤ G σ := fun σ => mul_nonneg (by
    have : (1 : ℚ) ≤ ((q ^ (min T.card (eB n K T.card σ)) : ℕ) : ℚ) := by
      exact_mod_cast Nat.one_le_pow _ _ hq1
    linarith) (hh0 σ)
  set L₁ := (univ : Finset (T → ZMod q)).erase 0 with hL₁
  have hmaps : ∀ κ ∈ L₁, jsupp ζ T (Sum.elim κ 0) ∈ (univ : Finset (Finset (Fin n))).erase ∅ := by
    intro κ hκ
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have h0 := eq_zero_of_jsupp h.inj h.ne0 T _ he
    exact (Finset.mem_erase.mp hκ).1 (funext fun r => congrFun h0 (Sum.inl r))
  have hz : (Sum.elim (0 : T → ZMod q) 0 : T ⊕ T → ZMod q) = 0 := by
    funext x; cases x <;> rfl
  calc ∑ κ ∈ L₁, prob (box γ₁ (L * n) ×ˢ box γ₁ (L * n))
          (fun yy => (∀ a, κ ⬝ᵥ PhiT mulmat T yy.1 a = 0) ∧ σs ≤ (degS ζ yy.1 yy.2).card)
      ≤ ∑ κ ∈ L₁, g (jsupp ζ T (Sum.elim κ 0)) := by
        refine Finset.sum_le_sum fun κ _ => ?_
        rw [prob_congr (Q := fun yy => (∀ a, (Sum.elim κ 0 : T ⊕ T → ZMod q) ⬝ᵥ
            pairΦ (PhiT mulmat T yy.1) (PhiT mulmat T yy.2) a = 0)
            ∧ σs ≤ (degS ζ yy.1 yy.2).card) _ (fun yy _ => by simp only [dot_inl])]
        exact orth_deg_prob h hγ1 hγ T _ σs
    _ = ∑ S ∈ (univ : Finset (Finset (Fin n))).erase ∅,
          ∑ κ ∈ L₁ with jsupp ζ T (Sum.elim κ 0) = S, g S :=
        (Finset.sum_fiberwise_of_maps_to' hmaps g).symm
    _ ≤ ∑ S ∈ (univ : Finset (Finset (Fin n))).erase ∅, G S.card := by
        refine Finset.sum_le_sum fun S _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, hg, hGdef]
        apply mul_le_mul_of_nonneg_right _ (hh0 _)
        have hsub : L₁.filter (fun κ => jsupp ζ T (Sum.elim κ 0) = S) ⊆ (suppIn1 ζ T S).erase 0 := by
          intro κ hκ
          rw [Finset.mem_filter] at hκ
          refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hκ.1).1, ?_⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hκ.2.le⟩
        have h0 : (0 : T → ZMod q) ∈ suppIn1 ζ T S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [hz, jsupp_zero]; exact Finset.empty_subset _⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem h0] at hc
        replace hc := hc.trans (Nat.sub_le_sub_right (card_suppIn1_le h.inj h.ne0 T S) 1)
        have := Nat.cast_le (α := ℚ).mpr hc
        rwa [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_one] at this
    _ ≤ ∑ S ∈ (univ : Finset (Finset (Fin n))), G S.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun S _ _ => hG0 _
    _ = RBt q n K L γ₁ σs T.card := by
        rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ,
          Fintype.card_fin]
        unfold RBt
        exact Finset.sum_congr rfl fun σ _ => by rw [nsmul_eq_mul]

/-- Capped second moment of the joint deviation for one coordinate set `T`. -/
lemma moment_T_cap (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) {v : Fin (K * n) → ℤ} (hv : Bounded β v) (T : Finset (Fin (K * n)))
    (B' : Finset (Fin (L * n) → ℤ)) (hsub : B' ⊆ box γ₁ (L * n)) (σs : ℕ) (hσs : σs ≤ n) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2)
      ≤ pR q γ₂ β mb ^ T.card * (3 * pR q γ₂ β mb ^ T.card * QBs q n K L γ₁ σs T.card
          + (1 + pR q γ₂ β mb ^ T.card) * PDq q n L γ₁ σs + RBt q n K L γ₁ σs T.card) := by
  have hγ1 : 0 < γ₁ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  have hBne : (box γ₁ (L * n)).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_box_nat]; positivity
  have hsm := second_moment_cap (PhiT (K := K) (L := L) mulmat T)
    (fun y a b => PhiT_add h.add T y a b) (failE q γ₂ β v T) (box γ₁ (L * n)) B' hBne hsub
    (fun yy => σs ≤ (degS ζ yy.1 yy.2).card) (fun ℓ => (jsupp ζ T ℓ).card < σs)
    (fun yy hb ℓ ho => lt_of_le_of_lt
      (Finset.card_le_card (jsupp_sub_degS h T ℓ yy.1 yy.2 ho)) (not_le.mp hb))
  rw [failE_card hp hv] at hsm
  have key : ∀ (a : Fin K → Fin L → Fin n → ZMod q)
      (inst : DecidablePred fun y => ∀ j ∈ T, fR q γ₂ β (modMat mulmat a) v j y),
      (@Finset.filter _ (fun y => ∀ j ∈ T, fR q γ₂ β (modMat mulmat a) v j y) inst B').card
        = (B'.filter fun y => PhiT mulmat T y a ∈ failE q γ₂ β v T).card := by
    intro a inst
    congr 1
    ext y
    simp only [Finset.mem_filter, mem_failE]
  set μ := pR q γ₂ β mb ^ T.card with hμ
  have hμ0 : 0 ≤ μ := pow_nonneg (pR_nonneg hp) _
  have e : ∀ a : Fin K → Fin L → Fin n → ZMod q,
      (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2
      = (((B'.filter fun y => PhiT mulmat T y a ∈ failE q γ₂ β v T).card : ℚ)
            / (box γ₁ (L * n)).card
          - (B'.card : ℚ) / (box γ₁ (L * n)).card * μ) ^ 2 := by
    intro a
    unfold jdev
    rw [sq_abs, key]
  simp_rw [e]
  refine hsm.trans ?_
  have h1 := Qs_le (L := L) h hγ1 hγ T σs (by omega)
  have h2 := deg_card_prob (L := L) h.inj hγ1 hγ σs
  have h3 := R_le (L := L) h hγ1 hγ T σs
  have i1 : 0 ≤ 3 * μ ^ 2 := by positivity
  have i2 : 0 ≤ μ * (1 + μ) := by positivity
  calc _ ≤ 3 * μ ^ 2 * QBs q n K L γ₁ σs T.card + μ * (1 + μ) * PDq q n L γ₁ σs
        + μ * RBt q n K L γ₁ σs T.card := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 i1)
          (mul_le_mul_of_nonneg_left h2 i2)) (mul_le_mul_of_nonneg_left h3 hμ0)
    _ = _ := by ring

variable (q n K L γ₁ γ₂ β mb) in
/-- The closed-form error of the capped route. -/
def Gt2 (σs s : ℕ) : ℚ :=
  (∑ t ∈ range (K * n + 1), ((K * n).choose t : ℚ) *
      (if t ≤ s then pR q γ₂ β mb ^ t else 0))
  * ∑ t ∈ range (K * n + 1), ((K * n).choose t : ℚ) *
      (if t ≤ s then 3 * pR q γ₂ β mb ^ t * QBs q n K L γ₁ σs t
        + (1 + pR q γ₂ β mb ^ t) * PDq q n L γ₁ σs + RBt q n K L γ₁ σs t else 0)

/-- **Sparse-test near-uniformity, capped route.** As `sparseFailAvg_module`, with the capped
second moment and a threshold `σ*` on the number of degenerate slots. -/
theorem sparseFailAvg_module_cap (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) {σs s : ℕ} (hσs : σs ≤ n) {δ : ℚ} (hδ : 0 ≤ δ)
    (hG : Gt2 q n K L γ₁ γ₂ β mb σs s ≤ δ ^ 2) :
    SparseFailAvg q γ₁ γ₂ β mb
      (fun a : Fin K → Fin L → Fin n → ZMod q => modMat (K := K) (L := L) mulmat a) s δ := by
  set F : ℕ → ℚ := fun t => 3 * pR q γ₂ β mb ^ t * QBs q n K L γ₁ σs t
    + (1 + pR q γ₂ β mb ^ t) * PDq q n L γ₁ σs + RBt q n K L γ₁ σs t with hF
  unfold Gt2 at hG
  rw [← sum_idx s (fun t => pR q γ₂ β mb ^ t), ← sum_idx s F] at hG
  intro v hv B' hsub
  set idx := (univ : Finset (Fin (K * n))).powerset.filter (fun T => T.card ≤ s) with hidx
  set p := pR q γ₂ β mb with hpdef
  have hp0 : 0 < p := pR_pos hp
  set X : (Fin K → Fin L → Fin n → ZMod q) → ℚ := fun a =>
    jdevSum q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' s with hX
  have hX0 : ∀ a, 0 ≤ X a := fun a => Finset.sum_nonneg fun T _ => abs_nonneg _
  set W : ℚ := ∑ T ∈ idx, p ^ T.card with hW
  have hW0 : 0 < W := by
    apply Finset.sum_pos (fun T _ => by positivity)
    exact ⟨∅, by simp [hidx]⟩
  -- weighted Cauchy–Schwarz over the coordinate sets
  have h1 : ∀ a, X a ^ 2 ≤ W * ∑ T ∈ idx,
      (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2 / p ^ T.card := by
    intro a
    have := Finset.sq_sum_div_le_sum_sq_div idx
      (fun T => jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T)
      (g := fun T => p ^ T.card) (fun T _ => by positivity)
    rw [div_le_iff₀ hW0] at this
    rw [mul_comm]; exact this
  -- Jensen over the matrix
  have hcard : (0 : ℚ) < Fintype.card (Fin K → Fin L → Fin n → ZMod q) := by
    exact_mod_cast Fintype.card_pos
  have h2 : avg X ^ 2 ≤ avg (fun a => X a ^ 2) := by
    unfold avg
    rw [div_pow, div_le_div_iff₀ (by positivity) hcard]
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin K → Fin L → Fin n → ZMod q)))
      (f := X)
    rw [Finset.card_univ] at this
    nlinarith
  have h3 : avg (fun a => X a ^ 2) ≤ W * ∑ T ∈ idx, F T.card := by
    refine (avg_mono h1).trans ?_
    rw [avg_mul_left, avg_finset_sum]
    apply mul_le_mul_of_nonneg_left _ hW0.le
    refine Finset.sum_le_sum fun T _ => ?_
    have hm := moment_T_cap hp h hγ hv T B' hsub σs hσs
    have hpt : (0 : ℚ) < p ^ T.card := by positivity
    have e : avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2 / p ^ T.card)
        = avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (jdev q γ₂ β mb (modMat mulmat a) v (box γ₁ (L * n)) B' T) ^ 2) / p ^ T.card := by
      unfold avg; rw [← Finset.sum_div]; ring
    rw [e, div_le_iff₀ hpt]
    calc _ ≤ p ^ T.card * F T.card := hm
      _ = _ := by ring
  have h4 : avg X ^ 2 ≤ δ ^ 2 := (h2.trans h3).trans hG
  have hav : 0 ≤ avg X := avg_nonneg hX0
  by_contra hcon
  rw [not_le] at hcon
  have := pow_lt_pow_left₀ hcon hδ two_ne_zero
  linarith

end RejOrder

end
end ModuleMain

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

/-- Matrix of multiplication by `a` in `Z_q[X]/(X^n + 1)`: column `t` holds the coefficients
of `a · X^t`. -/
def negacyclic (a : Fin n → ZMod q) : Matrix (Fin n) (Fin n) (ZMod q) :=
  fun s t => if t ≤ s then a (s - t) else -a (s - t)

lemma negacyclic_col (ζ : ZMod q) (hζ : ζ ^ n = -1) (a : Fin n → ZMod q) (t : Fin n) :
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
    (hroot : ∀ k, ζ k ^ n = -1) : IsNTTMul ζ (negacyclic (q := q) (n := n)) where
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
theorem isNTTMul_mldsa : IsNTTMul zetaMLDSA (negacyclic (q := 8380417) (n := 256)) :=
  isNTTMul_negacyclic zetaMLDSA zetaMLDSA_inj zetaMLDSA_root

end RejOrder

end
end Negacyclic

section Numeric
/-!
# Evaluating the error bound

`Gt` and `Gt2` are rewritten as quotients of natural numbers given by structurally recursive functions, so
that the final inequality for each parameter set is checked by kernel evaluation.
-/

open Finset Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace RejOrder

/-! ## Computable sums -/

/-- `∑ i < k, f i`. -/
def sumR (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumR f k + f k

/-- `max_{1 ≤ r ≤ k} f r`. -/
def supR (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => max (supR f k) (f (k + 1))

def chooseC (m t : ℕ) : ℕ := m.descFactorial t / t.factorial

def eBc (n K t σ : ℕ) : ℕ :=
  supR (fun r => (r * (σ + 1) * (t + r) - (n + 1) * r * r) / (t + r)) K

def Wn (q P m s : ℕ) : ℕ := sumR (fun t => chooseC m t * (P ^ t * q ^ (s - t))) (s + 1)

def QBn (q n K L b t : ℕ) : ℕ :=
  sumR (fun σ => chooseC n σ * ((q ^ (2 * min t (eBc n K t σ)) - 1) * b ^ (L * (n - σ)))) (n + 1)

def Vn (q P n K L b s : ℕ) : ℕ :=
  sumR (fun t => chooseC (K * n) t * (3 * (P ^ t * q ^ (s - t)) * QBn q n K L b t)) (s + 1)

/-- Numerators of `QBs`, `PDq`, `RBt` and of the second factor of `Gt2`, over `(2γ₁)^(L·n)` and
`q^s · (2γ₁)^(L·n)`. -/
def QBan (q n K L b σs t : ℕ) : ℕ :=
  sumR (fun σ => chooseC n σ * ((q ^ (2 * min t (eBc n K t σ)) - 1) * b ^ (L * (n - σ)))) σs

def PDn (q n L b σs : ℕ) : ℕ := chooseC n σs * ((q + 1) ^ σs * b ^ (L * (n - σs)))

def Rn (q n K L b σs t : ℕ) : ℕ :=
  sumR (fun σ => chooseC n σ * ((q ^ (min t (eBc n K t σ)) - 1) *
    min (b ^ (L * (n - σ)))
      (chooseC (n - σ) (σs - σ) * ((q + 1) ^ (σs - σ) * b ^ (L * (n - σ - (σs - σ)))))))
    (n + 1)

def V2n (q P n K L b σs s : ℕ) : ℕ :=
  sumR (fun t => chooseC (K * n) t * (3 * (P ^ t * q ^ (s - t)) * QBan q n K L b σs t
    + (P ^ t * q ^ (s - t) + q ^ s) * PDn q n L b σs + q ^ s * Rn q n K L b σs t)) (s + 1)

lemma sumR_eq (f : ℕ → ℕ) (k : ℕ) : sumR f k = ∑ i ∈ range k, f i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sumR, ih, Finset.sum_range_succ]

lemma le_supR (f : ℕ → ℕ) (K r : ℕ) (h1 : 1 ≤ r) (hK : r ≤ K) : f r ≤ supR f K := by
  induction K with
  | zero => omega
  | succ K ih =>
    rw [supR]
    rcases Nat.lt_or_ge r (K + 1) with h | h
    · exact (ih (by omega)).trans (le_max_left _ _)
    · have : r = K + 1 := by omega
      rw [this]; exact le_max_right _ _

lemma chooseC_eq (m t : ℕ) : chooseC m t = m.choose t :=
  (Nat.choose_eq_descFactorial_div_factorial m t).symm

lemma eB_le_eBc (n K t σ : ℕ) : eB n K t σ ≤ eBc n K t σ :=
  Finset.sup_le fun r hr => le_supR (fun r => (r * (σ + 1) * (t + r) - (n + 1) * r * r) / (t + r))
    K r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2

/-! ## From rationals to naturals -/

variable {q : ℕ} [NeZero q] [Fact q.Prime] {n K L : ℕ} {γ₁ γ₂ β mb : ℕ}

lemma pR_pow (hp : Params q γ₁ γ₂ β mb) {s t : ℕ} (ht : t ≤ s) :
    pR q γ₂ β mb ^ t
      = (((q - mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ) ^ t * (q : ℚ) ^ (s - t)) / (q : ℚ) ^ s := by
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [← pR_eq hp, div_pow]
  have : (q : ℚ) ^ s = (q : ℚ) ^ t * (q : ℚ) ^ (s - t) := by rw [← pow_add]; congr 1; omega
  rw [this]; field_simp

lemma W_eq (hp : Params q γ₁ γ₂ β mb) (m s : ℕ) (hs : s ≤ m) :
    ∑ t ∈ range (m + 1), (m.choose t : ℚ) * (if t ≤ s then pR q γ₂ β mb ^ t else 0)
      = (Wn q (q - mb * (2 * (γ₂ - β) - 1)) m s : ℚ) / (q : ℚ) ^ s := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : s + 1 ≤ m + 1))
    (fun t _ ht => by rw [Finset.mem_range] at ht; rw [if_neg (by omega), mul_zero])]
  unfold Wn
  rw [sumR_eq]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hts : t ≤ s := by have := Finset.mem_range.mp ht; omega
  rw [if_pos hts, chooseC_eq, pR_pow hp hts]
  push_cast
  ring

lemma QBt_le (hγ1 : 0 < γ₁) (t : ℕ) :
    QBt q n K L γ₁ t ≤ (QBn q n K L (2 * γ₁) t : ℚ) / (2 * γ₁ : ℚ) ^ (L * n) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  unfold QBt QBn
  rw [sumR_eq]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun σ hσ => ?_
  have hσn : σ ≤ n := by have := Finset.mem_range.mp hσ; omega
  rw [chooseC_eq]
  have hsplit : (2 * γ₁ : ℚ) ^ (L * n) = (2 * γ₁ : ℚ) ^ (L * σ) * (2 * γ₁ : ℚ) ^ (L * (n - σ)) := by
    rw [← pow_add, ← Nat.mul_add]; congr 2; omega
  have hmono : q ^ (2 * min t (eB n K t σ)) ≤ q ^ (2 * min t (eBc n K t σ)) :=
    Nat.pow_le_pow_right hq1 (Nat.mul_le_mul_left _ (min_le_min_left _ (eB_le_eBc n K t σ)))
  have h1 : 1 ≤ q ^ (2 * min t (eBc n K t σ)) := Nat.one_le_pow _ _ hq1
  have hA : (((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) - 1)
      ≤ (((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ) := by
    rw [Nat.cast_sub h1, Nat.cast_one]
    have : ((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) ≤ ((q ^ (2 * min t (eBc n K t σ)) : ℕ) : ℚ) :=
      Nat.cast_le.mpr hmono
    linarith
  have hC : (0 : ℚ) ≤ (n.choose σ : ℚ) := Nat.cast_nonneg _
  have e : (n.choose σ : ℚ) * ((((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ)
        * ((2 * γ₁ : ℕ) : ℚ) ^ (L * (n - σ))) / (2 * γ₁ : ℚ) ^ (L * n)
      = (n.choose σ : ℚ) * ((((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ)
        / (2 * γ₁ : ℚ) ^ (L * σ)) := by
    rw [hsplit]; push_cast; field_simp
  have hgoal : (n.choose σ : ℚ) * ((((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) - 1)
        / (2 * γ₁ : ℚ) ^ (L * σ))
      ≤ (n.choose σ : ℚ) * ((((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ)
        * ((2 * γ₁ : ℕ) : ℚ) ^ (L * (n - σ))) / (2 * γ₁ : ℚ) ^ (L * n) := by
    rw [e]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hA (by positivity)) hC
  convert hgoal using 2
  all_goals try rfl
  all_goals push_cast
  all_goals try ring

lemma V_le (hp : Params q γ₁ γ₂ β mb) (s : ℕ) (hs : s ≤ K * n) :
    ∑ t ∈ range (K * n + 1), ((K * n).choose t : ℚ) *
        (if t ≤ s then 3 * pR q γ₂ β mb ^ t * QBt q n K L γ₁ t else 0)
      ≤ (Vn q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) s : ℚ)
          / ((q : ℚ) ^ s * (2 * γ₁ : ℚ) ^ (L * n)) := by
  have hγ1 : 0 < γ₁ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : s + 1 ≤ K * n + 1))
    (fun t _ ht => by rw [Finset.mem_range] at ht; rw [if_neg (by omega), mul_zero])]
  unfold Vn
  rw [sumR_eq]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun t ht => ?_
  have hts : t ≤ s := by have := Finset.mem_range.mp ht; omega
  rw [if_pos hts, chooseC_eq, pR_pow hp hts]
  have hQ := QBt_le (q := q) (n := n) (K := K) (L := L) hγ1 t
  set X : ℚ := ((q - mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ) ^ t * (q : ℚ) ^ (s - t) with hX
  have hX0 : 0 ≤ X := by positivity
  have hC : (0 : ℚ) ≤ ((K * n).choose t : ℚ) := Nat.cast_nonneg _
  have step : ((K * n).choose t : ℚ) * (3 * (X / (q : ℚ) ^ s) * QBt q n K L γ₁ t)
      ≤ ((K * n).choose t : ℚ) * (3 * (X / (q : ℚ) ^ s)
          * ((QBn q n K L (2 * γ₁) t : ℚ) / (2 * γ₁ : ℚ) ^ (L * n))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (by positivity)) hC
  refine le_trans (le_of_eq ?_) (step.trans (le_of_eq ?_))
  · push_cast; ring
  · simp only [hX]; push_cast; field_simp

/-- The closed-form error is at most `(1/2^k)²` if a natural-number inequality holds. -/
theorem Gt_le (hp : Params q γ₁ γ₂ β mb) (s k : ℕ) (hs : s ≤ K * n)
    (h : Wn q (q - mb * (2 * (γ₂ - β) - 1)) (K * n) s
        * Vn q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) s * 2 ^ (2 * k)
      ≤ q ^ (2 * s) * (2 * γ₁) ^ (L * n)) :
    Gt q n K L γ₁ γ₂ β mb s ≤ (1 / 2 ^ k : ℚ) ^ 2 := by
  have hγ1 : 0 < γ₁ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  unfold Gt
  rw [W_eq hp (K * n) s hs]
  set W : ℚ := (Wn q (q - mb * (2 * (γ₂ - β) - 1)) (K * n) s : ℚ) with hW
  set V : ℚ := (Vn q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) s : ℚ) with hV
  have hW0 : 0 ≤ W / (q : ℚ) ^ s := by positivity
  refine (mul_le_mul_of_nonneg_left (V_le (L := L) hp s hs) hW0).trans ?_
  have hcast : W * V * (2 : ℚ) ^ (2 * k) ≤ (q : ℚ) ^ (2 * s) * (2 * γ₁ : ℚ) ^ (L * n) := by
    have := Nat.cast_le (α := ℚ).mpr h
    push_cast at this
    exact this
  rw [one_div, inv_pow, ← pow_mul, mul_comm k 2, div_mul_div_comm,
    div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc W * V * 2 ^ (2 * k) ≤ (q : ℚ) ^ (2 * s) * (2 * γ₁ : ℚ) ^ (L * n) := hcast
    _ = _ := by rw [two_mul, pow_add]; ring

/-! ## The capped route in naturals -/

lemma QBs_le (hγ1 : 0 < γ₁) {σs : ℕ} (hσs : σs ≤ n + 1) (t : ℕ) :
    QBs q n K L γ₁ σs t ≤ (QBan q n K L (2 * γ₁) σs t : ℚ) / (2 * γ₁ : ℚ) ^ (L * n) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  unfold QBs QBan
  rw [sumR_eq]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun σ hσ => ?_
  have hσn : σ ≤ n := by have := Finset.mem_range.mp hσ; omega
  rw [chooseC_eq]
  have hsplit : (2 * γ₁ : ℚ) ^ (L * n) = (2 * γ₁ : ℚ) ^ (L * σ) * (2 * γ₁ : ℚ) ^ (L * (n - σ)) := by
    rw [← pow_add, ← Nat.mul_add]; congr 2; omega
  have hmono : q ^ (2 * min t (eB n K t σ)) ≤ q ^ (2 * min t (eBc n K t σ)) :=
    Nat.pow_le_pow_right hq1 (Nat.mul_le_mul_left _ (min_le_min_left _ (eB_le_eBc n K t σ)))
  have h1 : 1 ≤ q ^ (2 * min t (eBc n K t σ)) := Nat.one_le_pow _ _ hq1
  have hA : (((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) - 1)
      ≤ (((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ) := by
    rw [Nat.cast_sub h1, Nat.cast_one]
    have : ((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) ≤ ((q ^ (2 * min t (eBc n K t σ)) : ℕ) : ℚ) :=
      Nat.cast_le.mpr hmono
    linarith
  have hC : (0 : ℚ) ≤ (n.choose σ : ℚ) := Nat.cast_nonneg _
  have e : (n.choose σ : ℚ) * ((((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ)
        * ((2 * γ₁ : ℕ) : ℚ) ^ (L * (n - σ))) / (2 * γ₁ : ℚ) ^ (L * n)
      = (n.choose σ : ℚ) * ((((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ)
        / (2 * γ₁ : ℚ) ^ (L * σ)) := by
    rw [hsplit]; push_cast; field_simp
  have hgoal : (n.choose σ : ℚ) * ((((q ^ (2 * min t (eB n K t σ)) : ℕ) : ℚ) - 1)
        / (2 * γ₁ : ℚ) ^ (L * σ))
      ≤ (n.choose σ : ℚ) * ((((q ^ (2 * min t (eBc n K t σ)) - 1 : ℕ)) : ℚ)
        * ((2 * γ₁ : ℕ) : ℚ) ^ (L * (n - σ))) / (2 * γ₁ : ℚ) ^ (L * n) := by
    rw [e]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hA (by positivity)) hC
  convert hgoal using 2
  all_goals push_cast
  all_goals try ring

lemma PDq_eq (hγ1 : 0 < γ₁) {σs : ℕ} (hσs : σs ≤ n) :
    PDq q n L γ₁ σs = (PDn q n L (2 * γ₁) σs : ℚ) / (2 * γ₁ : ℚ) ^ (L * n) := by
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hsplit : (2 * γ₁ : ℚ) ^ (L * n)
      = (2 * γ₁ : ℚ) ^ (L * σs) * (2 * γ₁ : ℚ) ^ (L * (n - σs)) := by
    rw [← pow_add, ← Nat.mul_add]; congr 2; omega
  unfold PDq PDn
  rw [hsplit, chooseC_eq]
  push_cast
  field_simp

lemma hBq_eq (hγ1 : 0 < γ₁) {σs σ : ℕ} (hσs : σs ≤ n) (hσ : σ ≤ n) :
    hBq q n L γ₁ σs σ = ((min ((2 * γ₁) ^ (L * (n - σ)))
      (chooseC (n - σ) (σs - σ) * ((q + 1) ^ (σs - σ) * (2 * γ₁) ^ (L * (n - σ - (σs - σ)))))
        : ℕ) : ℚ) / (2 * γ₁ : ℚ) ^ (L * n) := by
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hs1 : (2 * γ₁ : ℚ) ^ (L * n)
      = (2 * γ₁ : ℚ) ^ (L * σ) * (2 * γ₁ : ℚ) ^ (L * (n - σ)) := by
    rw [← pow_add, ← Nat.mul_add]; congr 2; omega
  have hs2 : (2 * γ₁ : ℚ) ^ (L * n)
      = (2 * γ₁ : ℚ) ^ (L * (σ + (σs - σ))) * (2 * γ₁ : ℚ) ^ (L * (n - σ - (σs - σ))) := by
    rw [← pow_add, ← Nat.mul_add]; congr 2; omega
  unfold hBq
  rw [Nat.cast_min, ← min_div_div_right (by positivity), chooseC_eq]
  congr 1
  · rw [hs1]; push_cast; field_simp
  · rw [hs2]; push_cast; field_simp

lemma RBt_le (hγ1 : 0 < γ₁) {σs : ℕ} (hσs : σs ≤ n) (t : ℕ) :
    RBt q n K L γ₁ σs t ≤ (Rn q n K L (2 * γ₁) σs t : ℚ) / (2 * γ₁ : ℚ) ^ (L * n) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  unfold RBt Rn
  rw [sumR_eq, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun σ hσ => ?_
  have hσn : σ ≤ n := by have := Finset.mem_range.mp hσ; omega
  rw [hBq_eq hγ1 hσs hσn]
  simp only [chooseC_eq]
  have hmono : q ^ (min t (eB n K t σ)) ≤ q ^ (min t (eBc n K t σ)) :=
    Nat.pow_le_pow_right hq1 (min_le_min_left _ (eB_le_eBc n K t σ))
  have h1 : 1 ≤ q ^ (min t (eBc n K t σ)) := Nat.one_le_pow _ _ hq1
  have hA : (((q ^ (min t (eB n K t σ)) : ℕ) : ℚ) - 1)
      ≤ (((q ^ (min t (eBc n K t σ)) - 1 : ℕ)) : ℚ) := by
    rw [Nat.cast_sub h1, Nat.cast_one]
    have : ((q ^ (min t (eB n K t σ)) : ℕ) : ℚ) ≤ ((q ^ (min t (eBc n K t σ)) : ℕ) : ℚ) :=
      Nat.cast_le.mpr hmono
    linarith
  have hC : (0 : ℚ) ≤ (n.choose σ : ℚ) := Nat.cast_nonneg _
  have key : ∀ Hm : ℚ, 0 ≤ Hm →
      (n.choose σ : ℚ) * ((((q ^ (min t (eB n K t σ)) : ℕ) : ℚ) - 1) * Hm)
        ≤ (n.choose σ : ℚ) * ((((q ^ (min t (eBc n K t σ)) - 1 : ℕ)) : ℚ) * Hm) :=
    fun Hm hH => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hH) hC
  refine le_trans (key _ (by positivity)) (le_of_eq ?_)
  push_cast
  ring

lemma V2_le (hp : Params q γ₁ γ₂ β mb) {σs : ℕ} (hσs : σs ≤ n) (s : ℕ) (hs : s ≤ K * n) :
    ∑ t ∈ range (K * n + 1), ((K * n).choose t : ℚ) *
        (if t ≤ s then 3 * pR q γ₂ β mb ^ t * QBs q n K L γ₁ σs t
          + (1 + pR q γ₂ β mb ^ t) * PDq q n L γ₁ σs + RBt q n K L γ₁ σs t else 0)
      ≤ (V2n q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) σs s : ℚ)
          / ((q : ℚ) ^ s * (2 * γ₁ : ℚ) ^ (L * n)) := by
  have hγ1 : 0 < γ₁ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : s + 1 ≤ K * n + 1))
    (fun t _ ht => by rw [Finset.mem_range] at ht; rw [if_neg (by omega), mul_zero])]
  unfold V2n
  rw [sumR_eq, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun t ht => ?_
  have hts : t ≤ s := by have := Finset.mem_range.mp ht; omega
  rw [if_pos hts, chooseC_eq, pR_pow hp hts, PDq_eq hγ1 hσs]
  have hQ := QBs_le (q := q) (n := n) (K := K) (L := L) hγ1 (σs := σs) (by omega) t
  have hR := RBt_le (q := q) (n := n) (K := K) (L := L) hγ1 hσs t
  set X : ℚ := ((q - mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ) ^ t * (q : ℚ) ^ (s - t) with hX
  have hX0 : 0 ≤ X := by positivity
  have hC : (0 : ℚ) ≤ ((K * n).choose t : ℚ) := Nat.cast_nonneg _
  have step : ((K * n).choose t : ℚ) * (3 * (X / (q : ℚ) ^ s) * QBs q n K L γ₁ σs t
        + (1 + X / (q : ℚ) ^ s) * ((PDn q n L (2 * γ₁) σs : ℚ) / (2 * γ₁ : ℚ) ^ (L * n))
        + RBt q n K L γ₁ σs t)
      ≤ ((K * n).choose t : ℚ) * (3 * (X / (q : ℚ) ^ s)
          * ((QBan q n K L (2 * γ₁) σs t : ℚ) / (2 * γ₁ : ℚ) ^ (L * n))
        + (1 + X / (q : ℚ) ^ s) * ((PDn q n L (2 * γ₁) σs : ℚ) / (2 * γ₁ : ℚ) ^ (L * n))
        + (Rn q n K L (2 * γ₁) σs t : ℚ) / (2 * γ₁ : ℚ) ^ (L * n)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    have : 0 ≤ 3 * (X / (q : ℚ) ^ s) := by positivity
    have := mul_le_mul_of_nonneg_left hQ this
    linarith
  refine le_trans (le_of_eq ?_) (step.trans (le_of_eq ?_))
  · ring
  · simp only [hX]; push_cast; field_simp; ring

/-- The capped closed-form error is at most `(1/2^k)²` if a natural-number inequality holds. -/
theorem Gt2_le (hp : Params q γ₁ γ₂ β mb) (σs s k : ℕ) (hσs : σs ≤ n) (hs : s ≤ K * n)
    (h : Wn q (q - mb * (2 * (γ₂ - β) - 1)) (K * n) s
        * V2n q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) σs s * 2 ^ (2 * k)
      ≤ q ^ (2 * s) * (2 * γ₁) ^ (L * n)) :
    Gt2 q n K L γ₁ γ₂ β mb σs s ≤ (1 / 2 ^ k : ℚ) ^ 2 := by
  have hγ1 : 0 < γ₁ := lt_of_le_of_lt (Nat.zero_le _) hp.β_lt_γ₁
  have hb : (0 : ℚ) < 2 * γ₁ := by exact_mod_cast (by omega : 0 < 2 * γ₁)
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  unfold Gt2
  rw [W_eq hp (K * n) s hs]
  set W : ℚ := (Wn q (q - mb * (2 * (γ₂ - β) - 1)) (K * n) s : ℚ) with hW
  set V : ℚ := (V2n q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) σs s : ℚ) with hV
  have hW0 : 0 ≤ W / (q : ℚ) ^ s := by positivity
  refine (mul_le_mul_of_nonneg_left (V2_le (L := L) hp hσs s hs) hW0).trans ?_
  have hcast : W * V * (2 : ℚ) ^ (2 * k) ≤ (q : ℚ) ^ (2 * s) * (2 * γ₁ : ℚ) ^ (L * n) := by
    have := Nat.cast_le (α := ℚ).mpr h
    push_cast at this
    exact this
  rw [one_div, inv_pow, ← pow_mul, mul_comm k 2, div_mul_div_comm,
    div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc W * V * 2 ^ (2 * k) ≤ (q : ℚ) ^ (2 * s) * (2 * γ₁ : ℚ) ^ (L * n) := hcast
    _ = _ := by rw [two_mul, pow_add]; ring

/-- The final error is at most `1/2^k'` if a natural-number inequality holds. -/
lemma eps_le (hp : Params q γ₁ γ₂ β mb) (m l s k k' : ℕ)
    (h : (m + l) * (2 * chooseC m s * (q - mb * (2 * (γ₂ - β) - 1)) ^ s * 2 ^ k + 2 * q ^ s)
        * 2 ^ k' ≤ q ^ s * 2 ^ k) :
    ((m : ℚ) + l) * (2 * (m.choose s : ℚ) * pR q γ₂ β mb ^ s + 2 * (1 / 2 ^ k)) ≤ 1 / 2 ^ k' := by
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← pR_eq hp, div_pow, ← chooseC_eq]
  have := Nat.cast_le (α := ℚ).mpr h
  push_cast at this
  rw [le_div_iff₀ (by positivity)]
  have e : ((m : ℚ) + l) * (2 * (chooseC m s : ℚ)
        * (((q - mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ) ^ s / (q : ℚ) ^ s) + 2 * (1 / 2 ^ k)) * 2 ^ k'
      = (((m : ℚ) + l) * (2 * (chooseC m s : ℚ) * ((q - mb * (2 * (γ₂ - β) - 1) : ℕ) : ℚ) ^ s * 2 ^ k
          + 2 * (q : ℚ) ^ s) * 2 ^ k') / ((q : ℚ) ^ s * 2 ^ k) := by
    field_simp
  rw [e, div_le_one (by positivity)]
  exact this

/-- **Main theorem.** For `A` uniform in `R_q^{K×L}` and any fixed bounded `u = c·s₁`,
`v = c·s₂`, the leak of one attempt is at most `2^-k'` on average over `A`, given two
natural-number inequalities that are checked by evaluation. -/
theorem leak_avg_module (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) (s k k' : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ K * n)
    (c1 : Wn q (q - mb * (2 * (γ₂ - β) - 1)) (K * n) s
        * Vn q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) s * 2 ^ (2 * k)
      ≤ q ^ (2 * s) * (2 * γ₁) ^ (L * n))
    (c2 : (K * n + L * n) * (2 * chooseC (K * n) s * (q - mb * (2 * (γ₂ - β) - 1)) ^ s * 2 ^ k
        + 2 * q ^ s) * 2 ^ k' ≤ q ^ s * 2 ^ k)
    {u : Fin (L * n) → ℤ} {v : Fin (K * n) → ℤ} (hu : Bounded β u) (hv : Bounded β v) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      leak q γ₁ γ₂ β mb (modMat (K := K) (L := L) mulmat a) u v) ≤ 1 / 2 ^ k' :=
  (leak_avg hp hs1 (sparseFailAvg_module hp h hγ (by positivity) (Gt_le hp s k hs c1))
    hu hv).trans (eps_le hp _ _ s k k' c2)

/-- **Main theorem, capped route.** As `leak_avg_module`, with the capped second moment and a
threshold `σ*` on the number of degenerate slots. -/
theorem leak_avg_module_cap (hp : Params q γ₁ γ₂ β mb) {ζ : Fin n → ZMod q}
    {mulmat : (Fin n → ZMod q) → Matrix (Fin n) (Fin n) (ZMod q)} (h : IsNTTMul ζ mulmat)
    (hγ : 2 * γ₁ ≤ q) (σs s k k' : ℕ) (hσs : σs ≤ n) (hs1 : 1 ≤ s) (hs : s ≤ K * n)
    (c1 : Wn q (q - mb * (2 * (γ₂ - β) - 1)) (K * n) s
        * V2n q (q - mb * (2 * (γ₂ - β) - 1)) n K L (2 * γ₁) σs s * 2 ^ (2 * k)
      ≤ q ^ (2 * s) * (2 * γ₁) ^ (L * n))
    (c2 : (K * n + L * n) * (2 * chooseC (K * n) s * (q - mb * (2 * (γ₂ - β) - 1)) ^ s * 2 ^ k
        + 2 * q ^ s) * 2 ^ k' ≤ q ^ s * 2 ^ k)
    {u : Fin (L * n) → ℤ} {v : Fin (K * n) → ℤ} (hu : Bounded β u) (hv : Bounded β v) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
      leak q γ₁ γ₂ β mb (modMat (K := K) (L := L) mulmat a) u v) ≤ 1 / 2 ^ k' :=
  (leak_avg hp hs1 (sparseFailAvg_module_cap hp h hγ hσs (by positivity)
    (Gt2_le hp σs s k hσs hs c1)) hu hv).trans (eps_le hp _ _ s k k' c2)

end RejOrder

end
end Numeric

section MLDSA
/-!
# The three ML-DSA parameter sets

For `A` uniform in `R_q^{K×L}` with `R_q = Z_q[X]/(X^256 + 1)`, the leak of one signing attempt is
negligible on average over `A`. The numerical inequalities are checked by kernel evaluation.
-/

open Finset Matrix

noncomputable section

namespace RejOrder

/-- `A ∈ R_q^{K×L}` as a `K·256 × L·256` matrix over `Z_q`. -/
abbrev mldsaMat (K L : ℕ) (a : Fin K → Fin L → Fin 256 → ZMod 8380417) :
    Matrix (Fin (K * 256)) (Fin (L * 256)) (ZMod 8380417) :=
  modMat (K := K) (L := L) negacyclic a

/-- ML-DSA-44: q = 8380417, γ₁ = 2^17, γ₂ = 95232, β = 78, mb = 44. -/
theorem params_mldsa44 : Params 8380417 (2 ^ 17) 95232 78 44 := by constructor <;> norm_num
/-- ML-DSA-65: q = 8380417, γ₁ = 2^19, γ₂ = 261888, β = 196, mb = 16. -/
theorem params_mldsa65 : Params 8380417 (2 ^ 19) 261888 196 16 := by constructor <;> norm_num
/-- ML-DSA-87: q = 8380417, γ₁ = 2^19, γ₂ = 261888, β = 120, mb = 16. -/
theorem params_mldsa87 : Params 8380417 (2 ^ 19) 261888 120 16 := by constructor <;> norm_num

/-- **ML-DSA-44.** -/
theorem leak_mldsa44 {u : Fin (4 * 256) → ℤ} {v : Fin (4 * 256) → ℤ}
    (hu : Bounded 78 u) (hv : Bounded 78 v) :
    avg (fun a => leak 8380417 (2 ^ 17) 95232 78 44 (mldsaMat 4 4 a) u v) ≤ 1 / 2 ^ 239 :=
  leak_avg_module_cap params_mldsa44 isNTTMul_mldsa (by norm_num) 20 54 254 239 (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) hu hv

/-- **ML-DSA-65.** -/
theorem leak_mldsa65 {u : Fin (5 * 256) → ℤ} {v : Fin (6 * 256) → ℤ}
    (hu : Bounded 196 u) (hv : Bounded 196 v) :
    avg (fun a => leak 8380417 (2 ^ 19) 261888 196 16 (mldsaMat 6 5 a) u v) ≤ 1 / 2 ^ 291 :=
  leak_avg_module_cap params_mldsa65 isNTTMul_mldsa (by norm_num) 20 68 304 291 (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) hu hv

/-- **ML-DSA-87.** -/
theorem leak_mldsa87 {u : Fin (7 * 256) → ℤ} {v : Fin (8 * 256) → ℤ}
    (hu : Bounded 120 u) (hv : Bounded 120 v) :
    avg (fun a => leak 8380417 (2 ^ 19) 261888 120 16 (mldsaMat 8 7 a) u v) ≤ 1 / 2 ^ 380 :=
  leak_avg_module params_mldsa87 isNTTMul_mldsa (by norm_num) 79 393 380 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hu hv

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
    ((univ.filter fun a => η ≤ ∑ i, w i *
        leak 8380417 (2 ^ 17) 95232 78 44 (mldsaMat 4 4 a) (us i) (vs i)).card : ℚ)
        / Fintype.card (Fin 4 → Fin 4 → Fin 256 → ZMod 8380417)
      ≤ (∑ i, w i) * (1 / 2 ^ 239) / η :=
  bad_frac (fun _ _ hu hv => leak_mldsa44 hu hv) w hw us vs hus hvs hη

/-- **ML-DSA-65, many attempts.** -/
theorem bad_frac_mldsa65 {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (us : ι → Fin (5 * 256) → ℤ) (vs : ι → Fin (6 * 256) → ℤ)
    (hus : ∀ i, Bounded 196 (us i)) (hvs : ∀ i, Bounded 196 (vs i)) {η : ℚ} (hη : 0 < η) :
    ((univ.filter fun a => η ≤ ∑ i, w i *
        leak 8380417 (2 ^ 19) 261888 196 16 (mldsaMat 6 5 a) (us i) (vs i)).card : ℚ)
        / Fintype.card (Fin 6 → Fin 5 → Fin 256 → ZMod 8380417)
      ≤ (∑ i, w i) * (1 / 2 ^ 291) / η :=
  bad_frac (fun _ _ hu hv => leak_mldsa65 hu hv) w hw us vs hus hvs hη

/-- **ML-DSA-87, many attempts.** -/
theorem bad_frac_mldsa87 {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (us : ι → Fin (7 * 256) → ℤ) (vs : ι → Fin (8 * 256) → ℤ)
    (hus : ∀ i, Bounded 120 (us i)) (hvs : ∀ i, Bounded 120 (vs i)) {η : ℚ} (hη : 0 < η) :
    ((univ.filter fun a => η ≤ ∑ i, w i *
        leak 8380417 (2 ^ 19) 261888 120 16 (mldsaMat 8 7 a) (us i) (vs i)).card : ℚ)
        / Fintype.card (Fin 8 → Fin 7 → Fin 256 → ZMod 8380417)
      ≤ (∑ i, w i) * (1 / 2 ^ 380) / η :=
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
