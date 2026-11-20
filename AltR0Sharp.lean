import AltR0Exc

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
def numL2 (e e₂ q n K Bd Dc pn pn' pd s₁ dm₁ s₂ dm₂ M : ℕ) : ℕ :=
  sumF (fun d => if 1 ≤ d then chooseC n d * pn ^ d * pd ^ (M - d)
      * EN e e₂ q n K (Bd ^ 2) (Dc ^ 2) d s₁ else 0) (dm₁ + 1)
    + chooseC n (dm₁ + 1) * pn ^ (dm₁ + 1) * pd ^ (M - (dm₁ + 1)) * q ^ (2 * (K * n))
    + sumF (fun d => if 1 ≤ d then chooseC n d * (pn' ^ d - pn ^ d) * pd ^ (M - d)
      * EN e e₂ q n K Bd Dc d s₂ ^ 2 else 0) (dm₂ + 1)
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
    (h₀ : Fin L) (e e₂ s₁ dm₁ s₂ dm₂ M k : ℕ) (hs₁ : s₁ ≤ K * n) (hs₂ : s₂ ≤ K * n)
    (hM₁ : dm₁ + 1 ≤ M) (hM₂ : dm₂ + 1 ≤ M)
    (hnum : 2 ^ k * numL2 e e₂ q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        ((2 * γ₁) ^ (L - 1) + w) ((2 * γ₁) ^ (L - 1) + w + 2) (w * (2 * γ₁) ^ (L - 1))
        s₁ dm₁ s₂ dm₂ M
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
        ≤ (EN e e₂ q n K Bd Dc S.card s₂ : ℚ) / (Dc : ℚ) ^ (K * n) :=
    fun S _ _ => (wsum_le h.inj h.ne0 hwz S (by positivity)).trans
      (wcount_le_EN hn e e₂ q Bd Dc S.card s₂ hq1 hDc0 hs₂)
  have hbt2 : bt ^ 2 = ((Bd ^ 2 : ℕ) : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) := by
    simp only [bt]; push_cast; rw [div_pow]
  have hEb₂ : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ dm₁ →
      ∑ ξ ∈ (univ : Finset (Fin (K * n) → ZMod q)).erase 0,
        (if DualIn ζ S ξ then (bt ^ 2) ^ (supp ξ).card else 0)
        ≤ (EN e e₂ q n K (Bd ^ 2) (Dc ^ 2) S.card s₁ : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) ^ (K * n) := by
    intro S _ _
    rw [hbt2]
    exact (wsum_le h.inj h.ne0 hwz S (by positivity)).trans
      (wcount_le_EN hn e e₂ q (Bd ^ 2) (Dc ^ 2) S.card s₁ hq1 (by positivity) hs₁)
  have hPexc : ∀ e', 1 ≤ e' → prob (trip lo w γ₁ h₀) (fun x =>
        e' ≤ (degS ζ (join h₀ x.1.1 x.2) (join h₀ x.1.2 x.2)).card ∧ ¬ NX ζ h₀ x)
      ≤ n.choose e' * ((1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)
          + 2 / ((w : ℚ) * ((2 * γ₁ : ℚ)) ^ (L - 1))) ^ e'
        - (1 / (w : ℚ) + 1 / ((2 * γ₁ : ℚ)) ^ (L - 1)) ^ e') := by
    intro e' he'
    exact (prob_mono _ fun x _ hx => ⟨hx.1, not_NX_exc h₀ x hx.2⟩).trans
      (prob_deg_exc h.inj hw0 hwq hγ1 hγ h₀ e' he')
  refine (var_le_sharp h hw0 hwq hγ1 hγ h₀ bt (by positivity) hbad dm₁ dm₂
    (fun d => (EN e e₂ q n K Bd Dc d s₂ : ℚ) / (Dc : ℚ) ^ (K * n))
    (fun d => (EN e e₂ q n K (Bd ^ 2) (Dc ^ 2) d s₁ : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) ^ (K * n))
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
    * (EN e e₂ q n K (Bd ^ 2) (Dc ^ 2) d s₁ : ℚ)
  set A₂ : ℚ := (n.choose (dm₁ + 1) : ℚ) * (pn : ℚ) ^ (dm₁ + 1) * (pd : ℚ) ^ (M - (dm₁ + 1)) * Q
  set A₃ : ℚ := ∑ d ∈ Icc 1 dm₂, (n.choose d : ℚ) * (((pn' : ℚ) ^ d - (pn : ℚ) ^ d))
    * (pd : ℚ) ^ (M - d) * (EN e e₂ q n K Bd Dc d s₂ : ℚ) ^ 2
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
        ((EN e e₂ q n K (Bd ^ 2) (Dc ^ 2) d s₁ : ℚ) / ((Dc ^ 2 : ℕ) : ℚ) ^ (K * n))
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
        ((EN e e₂ q n K Bd Dc d s₂ : ℚ) / (Dc : ℚ) ^ (K * n)) ^ 2
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
    (h₀ : Fin L) (e e₂ s₁ dm₁ s₂ dm₂ M j : ℕ) (hs₁ : s₁ ≤ K * n) (hs₂ : s₂ ≤ K * n)
    (hM₁ : dm₁ + 1 ≤ M) (hM₂ : dm₂ + 1 ≤ M)
    (hnum : 2 ^ (2 * j) * numL2 e e₂ q n K (q - mb * (2 * (γ₂ - β) - 1)) (mb * (2 * (γ₂ - β) - 1))
        ((2 * γ₁) ^ (L - 1) + w) ((2 * γ₁) ^ (L - 1) + w + 2) (w * (2 * γ₁) ^ (L - 1))
        s₁ dm₁ s₂ dm₂ M
      ≤ (mb * (2 * (γ₂ - β) - 1)) ^ (2 * (K * n)) * (w * (2 * γ₁) ^ (L - 1)) ^ M) :
    avg (fun a : Fin K → Fin L → Fin n → ZMod q =>
        (∑ t ∈ tbox γ₁ h₀, |rhoC mulmat γ₂ β v lo w h₀ a t
          - ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q|) / (tbox (n := n) γ₁ h₀).card)
      ≤ (∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q) / 2 ^ j := by
  set μ := ∏ r, ((good (q := q) γ₂ β v r).card : ℚ) / q with hμ
  have hvar := var_rel_sharp (lo := lo) h hwz hn hp hv hw0 hwq hγ1 hγ h₀ e e₂ s₁ dm₁ s₂ dm₂ M (2 * j)
    hs₁ hs₂ hM₁ hM₂ hnum
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
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 3100 300 25 250 19 26 147
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 3100 300 25 250 19 26 147
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

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
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 4700 400 26 400 19 27 182
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 4700 400 26 400 19 27 182
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

set_option maxHeartbeats 2000000 in
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
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 6450 500 27 500 17 28 190
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  · exact dev_rel_sharp isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 6450 500 27 500 17 28 190
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

end MLDSASharp

end AltR0
