# Numerics for the alt-r0 bounds and for items 3 and 4

Exact rational arithmetic in Python (`fractions`), mirroring the Lean definitions. Nothing
here is checked in Lean except what `kcheck.py` reproduces.

- `gapeval.py`: Python copies of RejOrder's `GapEval` definitions (`sumF`, `digit`, `geomK`,
  `compK`, `NBk`, `GBk`, `sumGB`, `packGB`, `coefK`).
- `kcheck.py`: the integer inequality `2^k · numL2 ≤ Dc^(2Kn) · pd^M` that
  `Bathwater.lean` checks with `decide +kernel` (`num_44_full` etc.). It uses the row-factorised
  count `ENr` (`wcount_le_rows`). Prints the largest passing `k`. Usage:
  `python3 kcheck.py 44,330,25,19 65,330,26,19 87,330,27,17` (set, `e`, `d₁`, `d₂`).
- `step0.py`: the "step 0" measurements for Fable's `item3.md` and `item4.md`.

All quantities are log₂. Running time: a few seconds each.

## Current kernel checks (`kcheck.py`)

| | `k` (second moment `≤ μ²·2^-k`) | used in Lean |
|---|---|---|
| ML-DSA-44 | 295 | 294 (`d₁ = 25`, `d₂ = 19`) |
| ML-DSA-65 | 365 | 364 (`d₁ = 26`, `d₂ = 19`) |
| ML-DSA-87 | 381 | 380 (`d₁ = 27`, `d₂ = 17`) |

## Item 3 (slot condition `1/q` instead of `1/w`)

Variance of the alt-r0 second moment, split as in `var_le_sharp`: main term (no exceptional
slot, `b²` weights) and exceptional term (crude weights). "New" replaces the head per-slot
probability `1/w` by `1/q` (so `p = 1/q + τ` and the exceptional increment `2τ/q`), and
multiplies by the packing constant `Cst = ((w + 2nB)/w)^n` with `B = 5` (valid for at most 28
prescribed slots, since `6^256 > q^28`); the exceptional term gets `Cst²` (two head conditions).
The tail factor `τ = (2γ₁)^-(L-1)` is unchanged.

| | old main | old exc | old total | new main | new exc | new total | `Cst` |
|---|---|---|---|---|---|---|---|
| ML-DSA-44 | −394 | −298 | −298 | −531 | −386 | −386 | 2^3.6 |
| ML-DSA-65 | −453 | −369 | −369 | −538 | −424 | −424 | 2^0.9 |
| ML-DSA-87 | −470 | −417 | −417 | −558 | −475 | −475 | 2^0.9 |

With the cut-off restricted to `d₁ ≤ 27` (inside the range where `B = 5` is valid), the totals
are unchanged (−386, −424, −475); the main term becomes −517 / −519 / −519.

These are estimates of the variance only (no `−1` for rounding `k`). Through `main2`
(Markov on the second moment, `ε ≈ 2^(-k/3)`), the headline `ε` would move from
`2^-98 / 2^-121 / 2^-126` to about `2^-128 / 2^-141 / 2^-158`. The exceptional term still
dominates after item 3, so item 2 (with its caveat that slots where both heads vanish stay
crude) would be the next step on top of it.

## Item 4 (RejOrder leak via `cov_le` on prefix-pass product sets)

Pairs `(y, y')` independent; a degenerate slot has probability `ρ = (q+1)/(2γ₁)^L`; crude
weights `E_b(d)²` (factorised, `b = p_R/(1−p_R)`); pairs with more than `d_m` degenerate slots
charged the trivial bound. Relative variance
`V = ∑_{d=1}^{d_m} C(n,d) ρ^d E_b(d)² + C(n, d_m+1) ρ^(d_m+1) / μ²`, and
`leak ≲ (2/p_R + L·n) · √V` (item4.md step 5).

| | relative variance | `d_m` | leak estimate | RejOrder now |
|---|---|---|---|---|
| ML-DSA-44 | 2^-835 | 19 | 2^-406 | 2^-289 |
| ML-DSA-65 | 2^-1122 | 19 | 2^-549 | 2^-418 |
| ML-DSA-87 | 2^-1486 | 19 | 2^-730 | 2^-568 |

Caveats:

- The `l = L·n` prefactor uses the crude `∑_j D_m(Bset j)` bound (item4.md step 5).
- `ρ` uses `q + 1` lines per slot as in `RejOrder.deg_prob`.
- Not yet checked: that `deg_prob` with `S₀ = ∅` gives exactly the form needed, and the
  uniformity over the sub-events `Bset j`.
