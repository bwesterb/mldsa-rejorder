# Item 4: the `RejOrder` leak bound via the product-Fourier bound

Status: paper sketch, not tried in Lean. More speculative than the other items: the argument
is sound as far as I can see, but the resulting numbers are unknown until step 0 is run.

## Idea

`RejOrder.lean` proves `E_A[leak] ≤ 2^-289 / 2^-418 / 2^-568` by: Bonferroni truncation at
`s` failing coordinates, a second moment for every coordinate set `T` with `|T| ≤ s`, a cap for
bad pairs, and gap counts summed over `T`. The truncation term `C(m,s)·p_R^s` is what limits
the result (for ML-DSA-44, `s = 62` gives about `2^-300`).

`Bathwater.lean` has a tool that needs none of this: `AltR0.cov_le` bounds the covariance over
`A` of two indicators of a *product* set, with a factor `b = p_R/(1−p_R)` per nonzero
frequency. The events in the `RejOrder` view are differences of product sets. So:

- no truncation, no sets `T`, no cap;
- pairs `(y, y')` are independent (no shared tail), so a degenerate slot has probability
  `ρ = (q+1)/(2γ₁)^L` (`2^-49`, `2^-77`, `2^-117`) instead of alt-r0's `2^-18`.

Expected outcome: a much shorter proof and a better exponent. I cannot predict the exponent.

## The reduction

Notation as in `RejOrder`: `m = K·n` output coordinates, `good_r ⊆ ZMod q` the passing values
of coordinate `r` (`AltR0.good γ₂ β v r`, all of size `mb·(2(γ₂−β)−1)` by `card_good`),
`p_R` the failure probability of a uniform coordinate.

Prefix-pass sets, for `0 ≤ i ≤ m`:

```
P_i = ∏_{r < i} good_r × ∏_{r ≥ i} univ        density (1 − p_R)^i
```

1. **Views as differences of product sets.**
   - `view = rFail i` ⟺ `Ay ∈ P_i` and `Ay ∉ P_{i+1}`. So
     `Pr[rFail i] = Pr[Ay ∈ P_i] − Pr[Ay ∈ P_{i+1}]`, and `geom p_R m (some i)` is the same
     difference of densities.
   - `view = zFail j` ⟺ `y ∈ Bset j` and `Ay ∈ P_m`. `Pr[y ∈ Bset j]` is exactly
     `geom p_Z l (some j)` (`J_dist`).
   - Using the complement this way avoids any Fourier bound for the *failing* set, so
     `cov_le` applies as it stands: `univ` satisfies its hypothesis `hbad` for every `β ≥ 0`.

2. **One quantity per `i`.** For `B' ⊆ box` put
   `D_i(B') = |#{y ∈ B' : Ay ∈ P_i}/|box| − (|B'|/|box|)·(1−p_R)^i|`. Then

   ```
   leak ≤ ∑_{i<m} (D_i(box) + D_{i+1}(box)) + ∑_{j<l} D_m(Bset j)
   ```

3. **Second moment over `A`.** With `X_y(A) = 1[Ay ∈ P_i] − (1−p_R)^i`,
   `E_A D_i(B')² = |box|^-2 ∑_{y,y' ∈ B'} E_A[X_y X_y'] ≤ |box|^-2 ∑_{y,y' ∈ box} |E_A[X_y X_y']|`.
   The last step is why the bound is uniform in `B'`. `cov_le` with `φ = phiHom h (zc y)`,
   `φ' = phiHom h (zc y')` gives

   ```
   |E_A[X_y X_y']| ≤ (1−p_R)^(2i) · W(y,y'),
   W(y,y') = ∑_{ξ,ξ' ≠ 0, orthogonal for (y,y')} b^(wt ξ + wt ξ')
   ```

   `W` does not depend on `i` (for `r ≥ i` the true coefficient is 0; bounding it by `b` is
   wasteful but harmless).

4. **Bound `E_{y,y'} W`.** Same three steps as `var_le`, with independent pairs:
   - support: `dualIn_of_orth` (already stated for arbitrary `y, y'`);
   - probability of `d` degenerate slots: `RejOrder.deg_prob` with `S₀ = ∅`, giving
     `Pr[|degS| ≥ d] ≤ C(n,d)·ρ^d`;
   - weighted count on `d` slots: `wsum_le`, `wcount_le_EN` (unchanged; they only depend on
     the slot set).

   Result, with the trivial bound `|E_A[X_y X_y']| ≤ 1` for pairs with more than `d_m`
   degenerate slots:

   ```
   E_A D_i(B')² ≤ (1−p_R)^(2i) · ∑_{d=1}^{d_m} C(n,d) ρ^d E_b(d)²  +  C(n,d_m+1) ρ^(d_m+1)
   ```

   This is `var_le` with `p := ρ` and the triple distribution replaced by `box × box`.
   Suggested refactor: split `var_le` into (i) a statement that takes the pair distribution
   and a hypothesis `Pr[d ≤ |degS|] ≤ C(n,d)·p^d`, and (ii) the alt-r0 instance. Then this
   item is a second instance.

5. **Assemble.** If the right-hand side of step 4 is `≤ (1−p_R)^(2m)·δ²` for all `i`
   (worst case `i = m` for the absolute term), then `E_A D_i ≤ (1−p_R)^i·δ` (Jensen), and

   ```
   E_A[leak] ≤ ∑_i ((1−p_R)^i + (1−p_R)^(i+1))·δ + l·(1−p_R)^m·δ ≤ (2/p_R + l)·δ
   ```

   `2/p_R ≈ 2^11.3`, `l ≤ 2^11`. For the z part, Cauchy–Schwarz over the disjoint `Bset j`
   gives `√l` instead of `l`; not worth it unless bits are tight.

6. **Numbers.** `var_rel`'s numeric side `numL e e₂ q n K Bd Dc pn pd s dm` is generic in
   `p = pn/pd`. Use `pn = q + 1`, `pd = (2γ₁)^L`.

## Step 0. Find the exponent first

Evaluate `numL` outside the kernel with `pn = q+1`, `pd = (2γ₁)^L` for the three parameter
sets, tuning `d_m`, and find the largest `k` with
`2^k · numL … ≤ good^(2Kn) · pd^(d_m+1)` (the shape of `hnum` in `var_rel`).
The leak bound is then about `2^(−k/2 + 12)`.

Decision rule: continue only if this beats `2^-289 / 2^-418 / 2^-568`, or if it is close and
the simplification alone is wanted.

If the crude `E_b(d)²` is not enough, the pairing trick applies to independent pairs too: at
a degenerate slot where both `ŷ(k)` and `ŷ'(k)` are nonzero, `ŷ' = λ ŷ` forces
`ξ̃'(k) = −λ⁻¹ ξ̃(k)`. With item 2's Cauchy–Schwarz form the bound is
`q^(K(z+z')/2) · E_{b²}(D)`, `z, z'` the numbers of slots where `ŷ`, `ŷ'` vanish entirely.
Here such a slot is only a factor `q` rarer than an ordinary degenerate slot while costing
`q^(K/2)`, so the effective per-slot probability becomes about `(2γ₁)^-L · (q + 2q^(K/2))`
(`2^-25`, `2^-31`, `2^-48`). Compare both variants numerically.

## Where to put it

`cov_le`, `phiHom`, `dualIn_of_orth`, `wsum_le`, `wcount_le_EN` live in `Bathwater.lean`,
which imports `RejOrder.lean`. So add a new section at the end of `Bathwater.lean`
(or a new file importing it), reusing `RejOrder.leak`, `view`, `J_dist`, `Bset`, `deg_prob`,
`avg`, `markov`. Do not touch `RejOrder.lean` until the new numbers are in.

New theorems, mirroring the existing names: `leak_fourier_avg` (general),
`leak_mldsa44_fourier` etc., and optionally `bad_frac` variants. Since step 4 bounds a second
moment, a Markov step on the second moment (as in `main2`) gives better bad fractions than
`bad_frac` gets from the first moment.

## What would become removable afterwards

Only if the new bound is at least as good for all three parameter sets:

- `Layer2` (Bonferroni: `alt`, `dev`, `devSum`), `jdev`, `SparseFailAvg`, `leak_avg`;
- `SecondMoment` (`second_moment`, `second_moment_cap`), `ModuleCount` (`PhiT`, `jsupp`,
  `suppIn`, `suppIn1`), `Profile`, `ModuleMain`, the capped routes, `GapMain`, `GapNumeric`.

Must stay (used by the weighted counts): `Uncertainty`, `Module`, `ModuleProb` (`deg_prob`,
`degS`), `GapCount`, `GapComb`, `GapEval`, `GapSum`, `Negacyclic`, and `Layer0`/`Layer1`
(`view_pass`, `J_dist`, `indist`).

## Risks

- The numbers (step 0).
- `deg_prob` is stated with extra data (`c₀`, `c₀'`, `S₀`); check that `S₀ = ∅` gives the
  clean form needed in step 4.
- Step 1 needs `firstIdx … = some i` rewritten as "all earlier pass, `i` fails"; `passSet` /
  `failSet` in `Layer2` already do this, so keep those lemmas if `Layer2` is later removed.
- `wOf` in `RejOrder` and `modMat mulmat a *ᵥ zc y` in `Bathwater` are two spellings of
  `A·y`; `AltR0Final.r0` already bridges them for the r₀ check.
