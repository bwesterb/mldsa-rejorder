# Item 3: a slot condition costs `1/q`, not `1/w`

Status: paper sketch, not tried in Lean. The argument below is elementary except for one
algebraic fact (step 2). Do step 0 first: it decides whether this is worth doing.

## What changes

Today (`card_sol_le`, `card_head_le`, `card_tail_le` in `Bathwater.lean`; `window`,
`slot_prob` in `RejOrder.lean`): prescribing the NTT of a box polynomial at `r` slots leaves at
most `w^(n−r)` of the `w^n` polynomials, i.e. probability `≤ w^-r`, `w` the box width.

Truth: about `q^-r`. Per slot this is `2^-23` instead of `2^-18` (ML-DSA-44, `w ≈ 2^18`) or
`2^-20` (65/87, `w ≈ 2^20`).

Target lemma (replaces `card_sol_le`; note it is for arbitrary targets `τ`, so it covers
cosets):

```
(#{f ∈ hbox lo w | ∀ k ∈ S, nttP ζ (f mod q) k = τ k}) * q^|S|  ≤  (w + 2·N)^n
```

where `N = n·B` and `B` is any natural number with `(B+1)^n > q^|S|`.

So the probability is at most `(1 + 2nB/w)^n · q^-|S|`. The factor is a constant, paid once,
not per slot:

| | `B` for `|S| ≤ 28` | `(1 + 2nB/w)^n` |
|---|---|---|
| ML-DSA-44, `w ≈ 2^18` | 5 (`6^256 > q^28`) | about `e^2.5 ≈ 12` |
| ML-DSA-65/87, `w ≈ 2^20` | 5 | about `e^0.63 ≈ 1.9` |

For `|S| ≤ 11`, `B = 1` works and the constants are `1.7` and `1.1`.

## Step 0. Measure the payoff before proving anything

`numL2` (and `numL`) are computable. Evaluate them outside the kernel with the new `p`:

- old: `p = 1/w + 1/(2γ₁)^(L−1)`, i.e. `pn/pd = ((2γ₁)^(L−1) + w) / (w·(2γ₁)^(L−1))`;
- new: `p = 1/q + 1/(2γ₁)^(L−1)`, and multiply the whole sum by the constant above.

Find the largest `k` that passes for each parameter set, with `d_m` re-tuned (the cut-off term
`C(n, d_m+1)·p^(d_m+1)` also shrinks, so a smaller `d_m` may do).

What to expect: the gain is `5d` bits (44) or `3d` bits (65/87) on the terms with `d`
degenerate slots, so it depends on which `d` dominates the sum; I do not know that. If item 2
(exceptional slots by Cauchy–Schwarz) is not in yet, ML-DSA-44 is limited by the exceptional
term and gains much less; do item 2 first.

## The proof

Setting: `R = Z[X]/(X^n+1)`, vectors `Fin n → ℤ`, `x·y` the negacyclic product, `x̂(k)` the
evaluation of `x mod q` at `ζ_k` (`nttP`). Fix `S` with `|S| = r`.
`L_S = {x : x̂(k) = 0 for k ∈ S}`.

1. **A short vector (pigeonhole).** If `(B+1)^n > q^r`, two distinct points of `[0,B]^n` have
   the same values `x̂|_S ∈ (ZMod q)^S`. Their difference `v` satisfies `v ≠ 0`,
   `|v s| ≤ B`, `v ∈ L_S`.
   Lean: `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`.

2. **`L_S` is an ideal, and `v` is not a zero divisor.**
   - Ideal: for integer `t`, `(v·t)^(k) = v̂(k)·t̂(k) = 0`. This needs the integer negacyclic
     product to reduce to `negacyclic` over `ZMod q` and `IsNTTMul` (`isNTTMul_negacyclic`).
   - Non-zero-divisor over `ℚ`: there is `u : Fin n → ℚ` with `v·u = e₀`. This is where
     `n` being a power of two is used: `X^n + 1` is the `2n`-th cyclotomic polynomial
     (`Polynomial.cyclotomic_prime_pow_eq_geom_sum` with `p = 2`) and is irreducible over `ℚ`
     (`Polynomial.cyclotomic.irreducible_rat`). So `ℚ[X]/(X^n+1)` is a field.
   - This bridge (negacyclic matrices ↔ `ℚ[X]/(X^n+1)`) is the main Mathlib cost of the
     item. An acceptable shortcut: state the general lemmas under a hypothesis
     `hinv : ∀ v : Fin n → ℤ, v ≠ 0 → ∃ u : Fin n → ℚ, v ·ℚ u = e₀` and discharge it once
     for `n = 256`. Equivalent form: `det (negacyclic v) ≠ 0` over `ℚ`.
   - Do not try to get an odd coefficient sum for `v` to make it invertible mod 2; pigeonhole
     does not give that.

3. **Reduction.** For `x : Fin n → ℤ` put `t = u·x ∈ ℚ^n` (so `x = v·t`) and
   `red x = x − v·⌊t⌋ = v·frac(t)`, floors coordinatewise.
   - `red x − x ∈ L_S` (step 2), so `red x` has the same values on `S` as `x`.
   - `|red x s| < ‖v‖₁ ≤ n·B =: N`, because each coordinate of `v·frac(t)` is a signed sum
     of the coefficients of `v` with weights in `[0,1)`.

4. **Short representatives.** There is `P : Finset (Fin n → ℤ)` with `|P| = q^r`,
   `P ⊆ (−N, N)^n`, and `x ↦ x̂|_S` injective on `P`.
   - Every `τ ∈ (ZMod q)^S` is `x̂|_S` for some integer `x`: the map from vectors supported on
     the first `r` coordinates with entries in `[0,q)` is injective by `window`
     (`win_inj_P` with `w = q`), hence bijective by cardinality.
   - `P` = the image of these `q^r` vectors under `red`.

5. **Packing.** Let `F = {f ∈ hbox lo w : f̂|_S = τ}`. The sets `f + P`, `f ∈ F`, are
   pairwise disjoint: `f + p = f' + p'` gives `p − p' = f' − f ∈ L_S`, so `p = p'` by
   injectivity, so `f = f'`. They all lie in the box `∏_s [lo_s − N, lo_s + w + N)`, which has
   `(w + 2N)^n` points. Hence `|F|·q^r ≤ (w + 2N)^n`.

Everything is finite counting over `ℤ`-vectors; no measure theory, no real volumes.

Toy check already run (`n = 8`, `q = 17`, `ζ_k = 3^(2k+1)`, `|S| ≤ 3`, 12 random `S`):
steps 1, 2 and 4 hold (pigeonhole vector found, its multiples stay in `L_S`, all `q^r` classes
have a representative in `(−‖v‖₁, ‖v‖₁)^n`), and the exact coset counts are within a small
factor of `w^n/q^r`. The final inequality is vacuous at that size (`w ≤ 4` is smaller than
`N`), so the toy does not test the constant.

## Wiring it in

- `card_sol_le` → new lemma (keep the old one; the bound to use is the minimum, and the old one
  is better when `|S|` is large).
- `card_head_le`: pairs `(f, f')` with `(f − f')^` vanishing on `S`: for each `f'` this is the
  coset count with `τ = f̂'|_S`. Bound `w^n · (w+2N)^n / q^|S|`.
- Exceptional slots (`card_head2_le`, `prob_Z_exc`): a head vanishing on a set is the same
  lemma with `τ = 0`.
- Tail (`card_tail_le`): optional. Its term `(2γ₁)^-(L−1)` is already far below `1/q`; leaving
  it avoids a constant per tail polynomial.
- `prob_Z`, `prob_deg_ge`, `prob_deg_exc`: `p` becomes `1/q + 1/(2γ₁)^(L−1)` and the bound
  gets the constant factor `Cst` with hypothesis `(w + 2nB)^n ≤ Cst · w^n` (kernel-checkable:
  numbers of about 4600 bits). Two head boxes are in use (`w = 2γ₁` and `w = zw γ₁ β`), so two
  checks per parameter set.
- `var_le`, `var_le_sharp`, `var_rel*`: only `p` and the constant change. Re-run the numeric
  checks with the `k` found in step 0, then `main2` picks up the improvement.

## Optional follow-up

`RejOrder.slot_prob` / `orth_prob` use the same window bound with `(2γ₁)^-(L|S|)`. The new
lemma applies there for small `|S|` (it degrades once `q^(|S|/n)` is not small, roughly
`|S| > 30`), so the bound there would be a minimum of the two. Not needed if item 4 replaces
that part.
