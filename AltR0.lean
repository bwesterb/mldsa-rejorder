import RejOrder
import Fourier

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

/-! ## ML-DSA -/

section MLDSA
set_option maxRecDepth 100000

/-- **ML-DSA-44.** For every `v = c·s₂` and every head box (the full box, or the z-pass box shifted by
`c·s₁`), `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^123`. -/
theorem dev_mldsa44 {v : Fin (4 * 256) → ℤ} (hv : Bounded 78 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 17 ∨ w = 2 * (2 ^ 17 - 78) - 1) (h₀ : Fin 4) :
    avg (fun a : Fin 4 → Fin 4 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 17) h₀, |rhoC (negacyclic (q := 8380417) (n := 256)) 95232 78 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417|)
          / (tbox (n := 256) (2 ^ 17) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 95232 78 v r).card : ℚ) / 8380417) / 2 ^ 123 := by
  rcases hw with rfl | rfl
  · exact dev_rel isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 2500 250 19 123 (by norm_num) (by decide +kernel)
  · exact dev_rel isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa44 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 2500 250 19 123 (by norm_num) (by decide +kernel)

/-- **ML-DSA-65.** For every `v = c·s₂` and every head box (the full box, or the z-pass box shifted by
`c·s₁`), `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^145`. -/
theorem dev_mldsa65 {v : Fin (6 * 256) → ℤ} (hv : Bounded 196 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 196) - 1) (h₀ : Fin 5) :
    avg (fun a : Fin 6 → Fin 5 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, |rhoC (negacyclic (q := 8380417) (n := 256)) 261888 196 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417|)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 196 v r).card : ℚ) / 8380417) / 2 ^ 145 := by
  rcases hw with rfl | rfl
  · exact dev_rel isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 3700 400 19 145 (by norm_num) (by decide +kernel)
  · exact dev_rel isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa65 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 3700 400 19 145 (by norm_num) (by decide +kernel)

/-- **ML-DSA-87.** For every `v = c·s₂` and every head box (the full box, or the z-pass box shifted by
`c·s₁`), `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^133`. -/
theorem dev_mldsa87 {v : Fin (8 * 256) → ℤ} (hv : Bounded 120 v) {lo : Fin 256 → ℤ} {w : ℕ}
    (hw : w = 2 * 2 ^ 19 ∨ w = 2 * (2 ^ 19 - 120) - 1) (h₀ : Fin 7) :
    avg (fun a : Fin 8 → Fin 7 → Fin 256 → ZMod 8380417 =>
        (∑ t ∈ tbox (2 ^ 19) h₀, |rhoC (negacyclic (q := 8380417) (n := 256)) 261888 120 v lo w h₀ a t
          - ∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417|)
          / (tbox (n := 256) (2 ^ 19) h₀).card)
      ≤ (∏ r, ((good (q := 8380417) 261888 120 v r).card : ℚ) / 8380417) / 2 ^ 133 := by
  rcases hw with rfl | rfl
  · exact dev_rel isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 4600 500 17 133 (by norm_num) (by decide +kernel)
  · exact dev_rel isNTTMul_mldsa zetaMLDSA_root (by norm_num) params_mldsa87 hv (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h₀ 330 4600 500 17 133 (by norm_num) (by decide +kernel)

end MLDSA

end AltR0
