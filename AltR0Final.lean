import Bathwater
import AltR0

/-!
# alt-r0 for ML-DSA: end to end

`Bathwater.lean` computes the output law of `alt-r0` with a set `H` of resampled coordinates
(`Bathwater.altR0Set_law`) and bounds its distance to vanilla signing in terms of the relative mean
deviation `dev` of `ρ` (the r₀ pass probability with the `H` part fresh) from a constant `μ₀`
(`Bathwater.altR0Set_close`). `AltR0.lean` bounds `E_A E_t |ρ_c(t) − μ| ≤ μ / 2^j` for ML-DSA, for
every `c·s₂`, every head box and every head index (`AltR0.dev_mldsa44/65/87`). This file joins the
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
   `dev_mldsa*` gives `E_a X ≤ μ/2^j` and `E_a Xz ≤ μ/2^j`.
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
      mu 8380417 95232 78 44 4 256 * (1 / 2 ^ 123) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa44 (hv c) (lo := fun _ => -((2 ^ 17 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 17) (Or.inl rfl) h₀
  rw [mu_eq_44 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hv : ∀ c, Bounded 78 (v c)) (h₀ : Fin 4) :
    avg (fun a => Xz (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀ a) ≤
      mu 8380417 95232 78 44 4 256 * (1 / 2 ^ 123) := by
  apply avg_Xz_le
  intro c
  have := AltR0.dev_mldsa44 (hv c) (lo := zlo (2 ^ 17) 78 h₀ (u c)) (w := zw (2 ^ 17) 78)
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

/-- **ML-DSA-44, any level `ε`.** At most a `2^-122 / ε` fraction of matrices `A` are bad; for
every other `A` with `2ε < p_z`, alt-r0's output law is within `2ε / (p_z − 2ε)` of vanilla's in
`ℓ¹`, and it fails to terminate with probability at most `ε / (p_z − 2ε)`. -/
theorem altR0_mldsa44_eps {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hu : ∀ c, Bounded 78 (u c)) (hv : ∀ c, Bounded 78 (v c))
    (h₀ : Fin 4) {ε : ℚ} (hε : 0 < ε) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀ ε)).card
        : ℚ) / Fintype.card (Fin 4 → Fin 4 → Fin 256 → ZMod 8380417) ≤ 2 * (1 / 2 ^ 123) / ε ∧
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

/-- **ML-DSA-44, headline.** Take `ε = 2^-60`. For at least a `1 − 2^-62` fraction of
matrices `A`, alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law within
`2^-58` of vanilla's in `ℓ¹` (statistical distance `≤ 2^-59`), and fails to terminate with
probability at most `2^-59`. -/
theorem altR0_mldsa44 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (4 * 256) → ℤ)
    (v : C → Fin (4 * 256) → ℤ) (hu : ∀ c, Bounded 78 (u c)) (hv : ∀ c, Bounded 78 (v c))
    (h₀ : Fin 4) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀
        (1 / 2 ^ 60))).card : ℚ) / Fintype.card (Fin 4 → Fin 4 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 62 ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 17) 95232 78 44 u v h₀
          (1 / 2 ^ 60) a →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 17) 95232 78 v a)
              (zok (2 ^ 17) 78 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 17) 95232 78 v a y c &&
              zok (2 ^ 17) 78 u y c) x| ≤ 1 / 2 ^ 58 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 17) 95232 78 v a)
              (zok (2 ^ 17) 78 u) x ≤ 1 / 2 ^ 59 := by
  obtain ⟨h1, h2⟩ := altR0_mldsa44_eps u v hu hv h₀ (ε := 1 / 2 ^ 60) (by norm_num)
  refine ⟨h1.trans (le_of_eq (by norm_num)), fun a ha => ?_⟩
  have hpz := pz_ge_44
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 17) 78 4 256 - 2 * (1 / 2 ^ 60) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 60) ≤ 27 / 50 := by norm_num
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
      mu 8380417 261888 196 16 6 256 * (1 / 2 ^ 145) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa65 (hv c) (lo := fun _ => -((2 ^ 19 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 19) (Or.inl rfl) h₀
  rw [mu_eq_65 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hv : ∀ c, Bounded 196 (v c)) (h₀ : Fin 5) :
    avg (fun a => Xz (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀ a) ≤
      mu 8380417 261888 196 16 6 256 * (1 / 2 ^ 145) := by
  apply avg_Xz_le
  intro c
  have := AltR0.dev_mldsa65 (hv c) (lo := zlo (2 ^ 19) 196 h₀ (u c)) (w := zw (2 ^ 19) 196)
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

/-- **ML-DSA-65, any level `ε`.** At most a `2^-144 / ε` fraction of matrices `A` are bad; for
every other `A` with `2ε < p_z`, alt-r0's output law is within `2ε / (p_z − 2ε)` of vanilla's in
`ℓ¹`, and it fails to terminate with probability at most `ε / (p_z − 2ε)`. -/
theorem altR0_mldsa65_eps {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hu : ∀ c, Bounded 196 (u c)) (hv : ∀ c, Bounded 196 (v c))
    (h₀ : Fin 5) {ε : ℚ} (hε : 0 < ε) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀ ε)).card
        : ℚ) / Fintype.card (Fin 6 → Fin 5 → Fin 256 → ZMod 8380417) ≤ 2 * (1 / 2 ^ 145) / ε ∧
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

/-- **ML-DSA-65, headline.** Take `ε = 2^-72`. For at least a `1 − 2^-72` fraction of
matrices `A`, alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law within
`2^-70` of vanilla's in `ℓ¹` (statistical distance `≤ 2^-71`), and fails to terminate with
probability at most `2^-71`. -/
theorem altR0_mldsa65 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (5 * 256) → ℤ)
    (v : C → Fin (6 * 256) → ℤ) (hu : ∀ c, Bounded 196 (u c)) (hv : ∀ c, Bounded 196 (v c))
    (h₀ : Fin 5) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀
        (1 / 2 ^ 72))).card : ℚ) / Fintype.card (Fin 6 → Fin 5 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 72 ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 196 16 u v h₀
          (1 / 2 ^ 72) a →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 196 v a)
              (zok (2 ^ 19) 196 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 19) 261888 196 v a y c &&
              zok (2 ^ 19) 196 u y c) x| ≤ 1 / 2 ^ 70 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 196 v a)
              (zok (2 ^ 19) 196 u) x ≤ 1 / 2 ^ 71 := by
  obtain ⟨h1, h2⟩ := altR0_mldsa65_eps u v hu hv h₀ (ε := 1 / 2 ^ 72) (by norm_num)
  refine ⟨h1.trans (le_of_eq (by norm_num)), fun a ha => ?_⟩
  have hpz := pz_ge_65
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 196 5 256 - 2 * (1 / 2 ^ 72) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 72) ≤ 3 / 5 := by norm_num
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
      mu 8380417 261888 120 16 8 256 * (1 / 2 ^ 133) := by
  apply avg_X_le
  intro c
  have := AltR0.dev_mldsa87 (hv c) (lo := fun _ => -((2 ^ 19 : ℕ) : ℤ) + 1)
    (w := 2 * 2 ^ 19) (Or.inl rfl) h₀
  rw [mu_eq_87 (hv c)] at this
  rw [mul_one_div]; exact this

lemma avg_Xz_87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hv : ∀ c, Bounded 120 (v c)) (h₀ : Fin 7) :
    avg (fun a => Xz (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀ a) ≤
      mu 8380417 261888 120 16 8 256 * (1 / 2 ^ 133) := by
  apply avg_Xz_le
  intro c
  have := AltR0.dev_mldsa87 (hv c) (lo := zlo (2 ^ 19) 120 h₀ (u c)) (w := zw (2 ^ 19) 120)
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

/-- **ML-DSA-87, any level `ε`.** At most a `2^-132 / ε` fraction of matrices `A` are bad; for
every other `A` with `2ε < p_z`, alt-r0's output law is within `2ε / (p_z − 2ε)` of vanilla's in
`ℓ¹`, and it fails to terminate with probability at most `ε / (p_z − 2ε)`. -/
theorem altR0_mldsa87_eps {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hu : ∀ c, Bounded 120 (u c)) (hv : ∀ c, Bounded 120 (v c))
    (h₀ : Fin 7) {ε : ℚ} (hε : 0 < ε) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀ ε)).card
        : ℚ) / Fintype.card (Fin 8 → Fin 7 → Fin 256 → ZMod 8380417) ≤ 2 * (1 / 2 ^ 133) / ε ∧
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

/-- **ML-DSA-87, headline.** Take `ε = 2^-66`. For at least a `1 − 2^-66` fraction of
matrices `A`, alt-r0 (r₀ check first, resample only `y_{h₀}` on an r₀ failure) has output law within
`2^-64` of vanilla's in `ℓ¹` (statistical distance `≤ 2^-65`), and fails to terminate with
probability at most `2^-65`. -/
theorem altR0_mldsa87 {C : Type*} [Fintype C] [Nonempty C] (u : C → Fin (7 * 256) → ℤ)
    (v : C → Fin (8 * 256) → ℤ) (hu : ∀ c, Bounded 120 (u c)) (hv : ∀ c, Bounded 120 (v c))
    (h₀ : Fin 7) :
    ((univ.filter (Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀
        (1 / 2 ^ 66))).card : ℚ) / Fintype.card (Fin 8 → Fin 7 → Fin 256 → ZMod 8380417)
        ≤ 1 / 2 ^ 66 ∧
      ∀ a, ¬ Bad (negacyclic (q := 8380417) (n := 256)) (2 ^ 19) 261888 120 16 u v h₀
          (1 / 2 ^ 66) a →
        ∑ x, |Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 120 v a)
              (zok (2 ^ 19) 120 u) x -
            Bathwater.AltR0Set.vanLaw (fun y c => r0 negacyclic (2 ^ 19) 261888 120 v a y c &&
              zok (2 ^ 19) 120 u y c) x| ≤ 1 / 2 ^ 64 ∧
        1 - ∑ x, Bathwater.AltR0Set.altLaw {h₀} (r0 negacyclic (2 ^ 19) 261888 120 v a)
              (zok (2 ^ 19) 120 u) x ≤ 1 / 2 ^ 65 := by
  obtain ⟨h1, h2⟩ := altR0_mldsa87_eps u v hu hv h₀ (ε := 1 / 2 ^ 66) (by norm_num)
  refine ⟨h1.trans (le_of_eq (by norm_num)), fun a ha => ?_⟩
  have hpz := pz_ge_87
  have hgap : (1 / 2 : ℚ) ≤ pz (2 ^ 19) 120 7 256 - 2 * (1 / 2 ^ 66) := by
    have : (1 / 2 : ℚ) + 2 * (1 / 2 ^ 66) ≤ 3 / 5 := by norm_num
    linarith
  obtain ⟨d1, d2⟩ := h2 a ha (by linarith)
  refine ⟨d1.trans ?_, d2.trans ?_⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))
  · exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hgap).trans (le_of_eq (by norm_num))

end MLDSA87

end AltR0Final
