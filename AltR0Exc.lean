import AltR0

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
