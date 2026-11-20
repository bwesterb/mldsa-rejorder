import AltR0

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
