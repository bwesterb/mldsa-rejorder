# ePrint Algorithm 3 is statistically close to vanilla: proof sketch

Status: paper sketch. Names of existing declarations were checked against `Bathwater.lean` at
commit `619d7a0` (after `main2`). None of the new statements has been tried in Lean.

## Goal

Algorithm 3 = r₀-check first; on an r₀ failure resample only `y₁`; on a z failure at polynomial
`i` resample `y₁..y_i` and keep `y_{i+1}..y_ℓ`.

Show that for ML-DSA, outside a small fraction of matrices, its output is close to vanilla's, per
attempt and cumulatively. No new lattice or Fourier work: it reuses `X`, `Xz` (via `X2`, `Xz2`,
`Bad2`) and `dev_mldsa*_sharp`.

Why not extend `altR0Set_law`: that theorem relies on the closed-form visit measure
`ν(y) = κ/(N·ρ(y))`. Algorithm 3 resamples a different prefix depending on where z fails, and
there is no evident closed form. Part A replaces the closed form by a perturbation argument.

## Part A. General theorem: approximate invariance ⇒ approximate exactness

Place: section `Reuse`, after `outAt_eq_of_invariant`.

For `P : ReusePolicy ι V C`, `N = Fintype.card (ι → V)`, `p = P.pAcc`:

```lean
def ReusePolicy.defect (P : ReusePolicy ι V C) : ℚ :=
  ∑ y', |(∑ y, P.loop.B y y') / N - (1 - P.pAcc) / N|
```

This is `‖πB − (1−p)π‖₁`. Invariant policies have defect 0 (that is the content of
`exact_of_invariant`: every column of `B` sums to `1 − p`).

Statements:

1. `state_close`:
   `∑ y, |P.loop.state k y − (1 − p)^k / N| ≤ P.defect * ∑ j ∈ range k, (1 − p)^j`.
   Corollary: `≤ P.defect / p` if `0 < p`.
   - Proof: with `e_k = state_k − (1−p)^k π`,
     `e_{k+1} = e_k · B + (1−p)^k (πB − (1−p)π)` (`Loop.state_succ`).
   - `‖e·B‖₁ ≤ ‖e‖₁` because `B ≥ 0` and rows of `B` sum to at most 1
     (`ReusePolicy.B_nonneg`, `ReusePolicy.row`). Check whether `Loop.norm_iter_le` already
     gives this.
2. `outAt_close`: if `Q.Invariant` and `∀ y c, P y c = none ↔ Q y c = none`, then
   `∑ x, |P.loop.outAt k x − Q.loop.outAt k x| ≤ P.defect / p`.
   - `Q.loop.state k` is `(1−p)^k π` by `exact_of_invariant`; `P.pAcc = Q.pAcc` as in
     `outAt_eq_of_invariant`; the `A` matrices agree; rows of `A` sum to at most 1.
3. `outUpTo_close`: same for `outUpTo K`, bound `K * P.defect / p`.
4. `survive_close`: `∑ y, P.loop.state K y ≤ (1 − p)^K + P.defect / p`.
   This is "still running after `K` attempts". It replaces the non-termination statement.

No limits, no fixed point. The statements are about the joint law of attempt number and
output, which `altR0Set_close` does not give.

Sanity checks worth doing in Lean before Part C:
- `defect = 0` for invariant policies.
- For `altR0Set H r0 zok`, `defect = E_y |ρ(y) − E ρ|` (from `AltR0Set.B_eq`). This re-derives
  a weaker alt-r0 closeness and tests the theorem on a known case.

## Part B. The policy

Place: section `Policies`.

```lean
def alg3 (zc : ι → V → C → Bool) (r0 : (ι → V) → C → Bool) : ReusePolicy ι V C := fun y c =>
  if r0 y c then
    match firstFail zc y c with
    | some i => some (univ.filter fun j => i < j)
    | none => none
  else some (univ.filter fun j => ⊥ < j)   -- keep everything except the first polynomial
```

- Needs `[OrderBot ι]` or take `ι = Fin (L+1)` / `Fin L` with `0 < L` and head index `0`.
- `alg3_accept`: `alg3 zc r0 y c = none ↔ pass zc r0 y c = true` (as `altZ_accept`).
- The repo's `r0FirstPrefixZ` is only the z half (it keeps `∅` on r₀ failure).

Instance (section `AltR0Final`, `General`): `ι = Fin L`, `V = V γ₁ n`, head `h₀ = 0`,
`r0 := r0 mulmat γ₁ γ₂ β v a`, and a per-block z-check

```lean
def zcB (γ₁ β : ℕ) (u : C → Fin (L * n) → ℤ) (j : Fin L) (x : V γ₁ n) (c : C) : Bool :=
  decide (∀ s, |x.1 s + u c (finProdFinEquiv (j, s))| < (γ₁ : ℤ) - β)
```

with `zok γ₁ β u y c = decide (∀ j, zcB γ₁ β u j (y j) c)` (compare `zok_join`).

## Part C. Bound the defect by `X` and `Xz`

Target, for every matrix `a`:

```
(alg3 (zcB …) (r0 … a)).defect ≤ 2 * (2 * X … a + L * Xz … a)
```

(The outer factor 2 is from centring, see the last bullet.)

Column sum at `y'`, as an average over `c` (analogue of `AltR0Set.B_eq`):

```
∑ y, B y y' = avg_c [ T_r0(c, y') + ∑_i T_i(c, y') ]
```

| Term | Arrival | Value | Ideal value (constant in `y'`) | Deviation, averaged over `y'` |
|---|---|---|---|---|
| `T_r0` | r₀ failed, `y₁` fresh | `1 − rhoC(full box; tail y')` | `1 − μ` | `c`-term of `X` |
| `T_1` | r₀ passed, z first fails at 1 | `rhoC(full; tail y') − (zw/2γ₁)^n · rhoC(z-box; tail y')` | `μ·(1 − (zw/2γ₁)^n)` | `c`-terms of `X` and `Xz` |
| `T_i`, `i ≥ 2` | r₀ passed, z first fails at `i` | `E_{y₂..y_i} [ 1[zcB passes 2..i−1, fails i] · (zw/2γ₁)^n · rhoC(z-box; tail (y₂..y_i, y'_{>i})) ]` | `μ · Pr[firstFail = i]` | `c`-term of `Xz` |

Details:

- `rhoC … lo w h₀ a t` is the r₀ pass probability with the head uniform in `hbox lo w`.
  Full box: `lo = fun _ => -γ₁ + 1`, `w = 2γ₁`. z-box: `lo = zlo γ₁ β 0 (u c)`, `w = zw γ₁ β`.
  `(zw/2γ₁)^n` is the probability that the head passes its z-check.
- `T_1`: "head fails z" = full box minus z-box; triangle inequality gives two terms.
- `T_i`, `i ≥ 2` (the only new idea): `y₁` must pass z (so it ranges over the z-box), and
  `y₂..y_i` are fresh too. Treat `y₂..y_i` as part of the tail: inside the absolute value,
  bound their indicator by 1. After summing over `y'`, the pair `(y₂..y_i, y'_{>i})` is a
  uniform element of `tbox γ₁ 0`, so the result is the inner sum of `Xz`.
- `firstFail zc y c = some i` depends only on `y₁..y_i` and `c` (`firstFail_eq_some`,
  `firstFail_congr`); this is why the ideal value is a constant.
- Centring: the column sums have mean exactly `1 − p` (sum of `ReusePolicy.row` over `y`).
  For any constant `m`, `∑|c(y') − (1−p)| ≤ 2 ∑|c(y') − m|`. Take `m` = the ideal value.
- Averaging over `c`: `|avg_c f − avg_c m| ≤ avg_c |f − m|` (`abs_avg_sub_le`).

Lean ingredients that exist: `sum_split`, `sum_split'`, `joinV`, `tailOf`, `rhoC_eq`,
`card_Y`, `zok_join`, `card_ztail`. Expect this part to be most of the work; it is the same
kind of bookkeeping as `dev_le` and `count_ge`.

## Part D. End-to-end

1. Bridge the two acceptance probabilities:
   `ReusePolicy.pAcc (alg3 …) = AltR0Set.pacc (fun y c => r0 … && zok …)`.
   Then `pacc_ge` gives `p ≥ μ·p_z − Xz`.
2. For `a` with `¬ Bad2 … ε a`: `X2, Xz2 < (με)²`, hence `X, Xz ≤ με` by Cauchy–Schwarz (the
   step already inside `main2`; factor it out as a lemma if it is not one).
   So `defect ≤ 2(L+2)·με` and `p ≥ μ(p_z − ε)`.
3. Theorem `alg3_main` (general) and `alg3_mldsa44/65/87`: for `a` not bad and every `K`,
   - `∑ x |alg3.outUpTo K x − vanilla.outUpTo K x| ≤ K · 2(L+2)ε / (p_z − ε)`,
   - `∑ y alg3.state K y ≤ (1 − p)^K + 2(L+2)ε / (p_z − ε)`.
   The bad fraction is the one `main2` already gives.
4. Optional headline with a fixed `K`: needs `(1 − p)^K` small, i.e. a numeric lower bound on
   `p` (`pz_ge_44` etc. and `μ`), checked by the kernel.

Rough numbers for ML-DSA-44 with `ε = 2^-98`: about `2^-93` per attempt, `2^-85` for
`K = 256` (vanilla's own tail `(1−p)^256` is about `2^-99`).

## Write-up notes (not to prove)

- `MinEntropy` applies unchanged: `y₁` is fresh in every attempt.
- Sign→Trans and the many-signature hybrid stay unformalised.
- Timing now reveals the number of resampled polynomials; `RejOrder` does not cover reused
  tails.
- "z first, keep tail on r₀ failure" (`zFirstThenY1`): its column sums depend on whether the
  kept tail passes z, which varies with the tail and `c·s₁`. The defect is not small; skip.

## Order

A (self-contained, test on alt-r0) → B → C → D.
