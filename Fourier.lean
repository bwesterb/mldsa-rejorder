import Mathlib

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
