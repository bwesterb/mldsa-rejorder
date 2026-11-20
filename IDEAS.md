# Ideas: faster signing and better bounds

Status: brainstorm. Nothing here is checked in Lean. Performance numbers come from an
operation-count model (see "Cost model" at the end), not from benchmarks. Related sketches:
`alg13.md` (Algorithm 3), `item3.md` (`1/q` per slot), `item4.md` (`RejOrder` via Fourier).

Notation: `k × ℓ` matrix `A`, `n = 256`, nonce `y ∈ (−γ₁, γ₁]^{ℓn}`, `w = Ay`,
`c = H(μ ‖ HighBits(w))`, `z = y + c·s₁`, `β = τ·η` so `‖c·s₁‖∞, ‖c·s₂‖∞ ≤ β` always.
`ρ(t)` = r₀ pass probability with the head fresh and tail `t` kept, `μ` = its ideal value,
`Var` = `E_A E_t (ρ − μ)²/μ²` (currently about `2^-294`, `2^-364`, `2^-380`).

---

# Part I. Performance

## P1. Check only the borderline coefficients

**Claim.** Both rejection checks are decided by a few coefficients per attempt. The rest pass
for every possible challenge.

- **z-check** `|y_i + (c·s₁)_i| < γ₁ − β`. If `|y_i| < γ₁ − 2β` the coefficient passes whatever
  `c` is. Call the others *z-borderline*. Their fraction is about `2β/γ₁`.
- **r₀-check** `|LowBits(w − c·s₂)_i| < γ₂ − β`. By the shift lemma
  (`RejOrder.lowBits_shift`) this is equivalent to `|LowBits(w)_i − (c·s₂)_i| < γ₂ − β`.
  If `|LowBits(w)_i| < γ₂ − 2β` the coefficient passes whatever `c` is. Call the others
  *r₀-borderline*. Their fraction is about `2β/γ₂`.

Expected number of borderline coefficients per attempt:

| | r₀ (`2β/γ₂ · kn`) | z (`2β/γ₁ · ℓn`) |
|---|---|---|
| ML-DSA-44 | 1.68 | 1.22 |
| ML-DSA-65 | 2.30 | 0.96 |
| ML-DSA-87 | 1.88 | 0.82 |

Consistency check: each r₀-borderline coefficient fails with probability about 1/2, and
`e^(−1.68/2) ≈ 0.43` matches the r₀ pass probability `0.436` of ML-DSA-44.

**Algorithm for one attempt.**
1. Compute `w`, `Decompose` it, hash, get `c` (as now).
2. While decomposing, record the r₀-borderline positions. While sampling `y` (or once per
   kept polynomial), record the z-borderline positions; these do not depend on `c`, so for a
   kept tail they are computed once.
3. For each borderline position compute the single coefficient `(c·s₂)_i` or `(c·s₁)_i`
   directly: `c` has `τ` nonzero `±1` coefficients, so this is `τ` additions of small numbers
   (`τ = 39, 49, 60`).
4. Reject or accept. Only on accept compute `NTT(c)`, the full `c·s₁`, `c·s₂`, `c·t₀`, `z`
   and the hint.

**What it saves per rejected attempt:** `NTT(c)`, `k` inverse NTTs (for `c·s₂`), up to `ℓ`
inverse NTTs (for `c·s₁`), and the pointwise products. About `2k + 1` NTTs' worth in the
r₀-first order.

**Correctness.** The accept set is unchanged, so the output distribution and the number of
attempts are exactly those of the underlying policy. No new distribution proof. A Lean
statement would be a two-line corollary of `lowBits_shift` and `|c·s| ≤ β`:
"if no borderline coefficient fails, the full check passes".

**Timing: this is the part that needs care.**
- Rejected attempts: the set of r₀-borderline positions is a function of `w = Ay` only, and
  the z-borderline set a function of `y` only; neither involves the key. Which borderline
  coefficient fails first is the kind of view `RejOrder` studies, but the view is richer here
  (it includes the borderline pattern). It is not covered by `RejOrder` as it stands.
  With the product-set approach of `item4.md` a three-way classification per coordinate
  (interior / borderline-pass / borderline-fail) is again a product event, so an extension
  looks possible; not worked out.
- Accepted attempt: the number of r₀-borderline coefficients of the accepted `w` must not
  leak. From a signature (and `t₀`, which is not secret in practice) one knows `w − c·s₂`.
  Whether coefficient `i` of `w` is borderline then says whether `(c·s₂)_i` pushes
  `LowBits` over the threshold `γ₂ − 2β`, i.e. gives inequalities on `c·s₂`.
  Leakage of `w₀` is a known attack surface for Dilithium.
- Mitigation: process a fixed budget of `M` candidate slots per check (extract up to `M` set
  bits from the borderline bitmask in constant time, pad with dummies). With `M = 16` the
  overflow probability (Poisson with mean about 2) is below `2^-30`; on overflow fall back to
  the full constant-time check. The overflow event itself is then the only leak.

**Prior work.** Not checked. Coefficient-wise / sparse `c·s` multiplication is known from
embedded implementations. Whether "only the borderline coefficients" is published I do not
know; a paper titled "Speedup signing: pre-rejection sampling towards Dilithium" showed up in
a search and should be read before claiming novelty.

## P2. Resample only a short head of `y₁`

**Claim.** The statistical-closeness proof does not need the fresh part to be a whole
polynomial. Let the head be the first `h` coefficients of `y₁` and move the other `n − h`
coefficients of `y₁` into the tail.

Why the proof survives:
- At slot `k` the pair of vectors is `(â(k) + r̂(k), t̂(k))` and `(â'(k) + r̂(k), t̂(k))` with
  `a, a'` the two heads (polynomials of degree `< h`), `r` the kept part of `y₁`, `t` the other
  polynomials. They are dependent iff `â(k) = â'(k)`, or `t̂(k) = 0` (then with the usual
  sub-cases). This is the same case split as `degS_sub`.
- The window argument (`win_inj_P`, `card_sol_le`) prescribes `|S|` NTT values by fixing
  `|S|` consecutive coefficients. It needs `|S| ≤ h`. The sums use `|S| ≤ d_m + 1 < 30`.
- Pairs with `a = a'` have probability `w^-h`; they are part of the cut-off term.

Choice of `h`: `h = 60` gives `60 · 18 = 1080` bits `= 135` bytes, one SHAKE-256 block instead
of five (`h = 54` for `γ₁ = 2^19`, 20 bits per coefficient). Smaller is possible in principle
(`h ≥ 32` keeps the cut-off term harmless) but saves nothing more in Keccak calls.

What it saves per r₀-retry: four Keccak permutations. The NTT of the head and the `k` inverse
NTTs for `A·head` stay. (A head of the form `g(X^{n/h})` would make its NTT cheaper, but then
the slot conditions repeat in groups and the window bound degrades; not recommended.)

What needs new work:
1. `hbox`/`join`/`tbox` with the head a coefficient prefix. The policy lives on a finer index
   set: `ι` = blocks of coefficients, not polynomials. `ReusePolicy` is already generic in
   `ι` and `V`.
2. **Min-entropy of `w₁`** (`MinEntropyPart`). `guess_le` uses one row `i` and the fact that
   `y₁ ↦ A_{i,1} y₁` is injective on a full polynomial; its bound
   `((2γ₂+1)/(2γ₁))^n (2γ₁)^z` is useless for a head with `2^1080` values, because a single
   row leaves `(2γ₂+1)^n ≫ 2^1080` candidates. Use all `k` rows:
   two heads with the same `HighBits(Ay)` differ by `δ ≠ 0` (degree `< h`, coefficients in
   `(−2γ₁, 2γ₁)`) with `A_{·,1}·δ ∈ [−2γ₂, 2γ₂]^{kn}` roughly. For uniform `A` and fixed `δ`
   whose NTT has `z` zero slots this has probability about `((4γ₂+1)/q)^{k(n − z)}`;
   `δ` of degree `< h` has at most `h − 1` zero slots. Union bound over `δ`:
   `(4γ₁)^h · ((4γ₂+1)/q)^{k(n−h)}`, which is astronomically small
   (ML-DSA-44: `2^(19·60 − 5.4·4·196)`). So outside a negligible fraction of `A`, `w₁`
   determines the head and the guessing probability is `(2γ₁)^-h`.
3. Alg-3-style policies on the finer index set (see P4).

## P3. Retry cap

Restart with a completely fresh `y` after `T` consecutive r₀ failures on the same tail
(e.g. `T = 64`; probability about `0.56^64 ≈ 2^-53` per tail for ML-DSA-44).

- No measurable cost.
- No stuck tails, so no non-termination term at all. The toy's "tails that can never be
  accepted" disappear.
- The output weight of a tail becomes proportional to `(1 − (1−ρ)^T)/ρ ≤ min(T, 1/ρ)` instead
  of `1/ρ`. The density ratio to vanilla is then bounded by a constant (about `T·μ`), which
  is what B2 needs.
- Proof: the loop state needs a failure counter. With `Loop`/`ReusePolicy` as they are, the
  counter is not part of the nonce; either extend the state, or analyse the capped loop as
  "epochs" (each epoch = one tail, at most `T` head draws) which are i.i.d. Epoch analysis is
  probably simpler than the fixed-point route: an epoch outputs `(y,c)` with probability
  `[pass]·(1 − (1−ρ)^T)/(ρ·N·|C|)`-shaped weights, and epochs are independent.
- With `alg13.md` Part A (defect bound) the cap is not needed for the statistical-distance
  result; it matters for B2 and for implementations that want a hard bound on the loop.

## P4. Exact prefix resampling at coefficient granularity (minor)

`exact_of_invariant` holds for any index set. Take `ι` = single coefficients (or blocks) in
a fixed order and z-check them in that order. On a z failure at coefficient `i`, resample
coefficients `≤ i` and keep the rest. The reject event depends only on the resampled
coordinates, so this is exact (same proof as `altZ_invariant`).

Gain over polynomial-level alt-z is small: the polynomial containing `i` still needs its NTT.
Worth it only together with P2, where the index set is already finer.

## Where the time goes after P1 + P2 + Algorithm 3

Per r₀-retry: one Keccak for the head, one forward NTT, `k` pointwise products, `k` inverse
NTTs, `Decompose`, the `w₁` hash (7 to 9 Keccak), `SampleInBall`, a few sparse sums.
The `k` inverse NTTs and the hash are inherent: `c` must be a hash of the new `w₁`.

Estimated loop savings versus vanilla with early abort (range: Keccak-f = 0.3 to 1 NTT):

| Variant | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
|---|---|---|---|
| alt-z | 9–11% | 8–10% | 8–10% |
| Algorithm 3 | 23–28% | 30–36% | 31–36% |
| vanilla + P1 | 10–17% | 12–19% | 11–16% |
| Algorithm 3 + P1 | 39–40% | 47% | 45–46% |
| Algorithm 3 + P1 + P2 | 42–43% | 49–51% | 47–48% |

`ExpandA` and the key NTTs are outside the loop; if `A` is not cached, end-to-end savings are
roughly 0.55 to 0.7 times these.

---

# Part II. Bounds

The current headline per signature (`2^-96` distance outside a `2^-97` fraction of `A`, for
ML-DSA-44) is weak over many signatures: `2^64 · 2^-96 = 2^-32`. B1 and B2 change what the
existing variance bound is worth, without touching the lattice argument.

## B1. Do not apply Markov over `A` in the security bound

`A` is generated in key generation, independently of `s₁, s₂`, and EUF-CMA advantage is a
probability over key generation. The hop "replace alt-r0 signing by vanilla signing" costs

```
E_A [ N · dist_A ]  ≤  N · const · E_A E_t |ρ − μ| / μ  ≤  N · const · sqrt(Var)
```

i.e. `2^-147`, `2^-182`, `2^-190` per signature (`dev_mldsa*_sharp`), not the Markov-ed
`2^-96`. The theorems hold for every fixed bounded `c·s₁`, `c·s₂`, so independence of `A`
from the secret is all that is used.

To do: state the averaged closeness theorem (`E_a` of the `ℓ¹` distance and of the
non-termination probability). `close` gives the bound for one `a` only when
`D = μ p_z − Xz − X > 0`; for the average, split on `Bad2` and bound the distance by 2 on the
bad set, or go through `alg13.md` Part A whose bounds are linear in the defect.
Keep `main2` as the per-matrix statement; it answers a different question
("is *this* key fine?" cannot be decided by it either, since the bad set is not explicit).

## B2. Rényi divergence with the second moment

Forgery is a search event, so the hop can use Rényi divergence (Bai, Langlois, Lepoint,
Stehlé, Steinfeld; "Improved security proofs in lattice-based cryptography: using the Rényi
divergence rather than the statistical distance"). For an event `E` and order `a > 1`:

```
Pr_real[E] ≤ ( Pr_ideal[E] · R_a(real ‖ ideal) )^((a−1)/a),    R_a multiplicative over N signatures.
```

For alt-r0, `U(y,c) ∝ [pass]/ρ(tail y)` and vanilla `V(y,c) ∝ [pass]`. So `U/V = g(ρ)/E[g]`
with `g(ρ) = 1/ρ`, and

```
R_2(U ‖ V) = Σ U²/V = 1 + (variance of the density ratio under V) = 1 + O(Var)
```

provided the ratio is controlled. So the *variance itself* (`2^-294`) enters, with no square
root and no cube root, and `N` signatures cost a factor `(1 + O(Var))^N`.

Obstacles and how to handle them:
- **Tails with tiny `ρ`**, where `1/ρ` is huge. Two options:
  (a) remove them by statistical distance first: `Pr_t[ρ < μ/2] ≤ 4·Var` by Chebyshev, and
      their output mass under `U` is at most `κ` times that because `sacc ≤ ρ`
      (`AltR0Set.sacc_le`); on the remaining tails the ratio is at most about 2;
  (b) the retry cap P3, which bounds the ratio by a constant for all tails.
- **The exponent `(a−1)/a`.** With the ratio bounded by `C`, the order-`a` divergence is at
  most `1 + a²·C^(a−2)·Var`-shaped. With `Var·N ≈ 2^-230` an order around 40 is affordable,
  so a 128-bit forgery bound becomes about 125 bits. Order 2 alone would halve it.
- **Dependence on `A`.** `R_a` depends on `A`. `E_A[R_2 − 1] = O(Var)`, and `R_a ≤ C^(a−1)`
  always (after (a) or (b)), so one Markov step with a tiny bad fraction suffices
  (bad fraction `δ` gives `R_2 − 1 ≤ O(Var)/δ`).
- The direction matters: the hop needs `R(real ‖ ideal)`, the one with `1/ρ`. The other
  direction is harmless but is not the one used.

To do in Lean: one theorem bounding `Σ U²/V − 1` (restricted to good tails, or for the capped
loop) by a constant times `E_t (ρ − μ)²/μ²`, starting from `altR0Set_law` and
`var_le_sharp`. The reduction itself stays on paper, as the Sign→Trans hop does.

With B2 in place, improvements to `Var` (items 2 and 3) pay at full value instead of a third.

## B3. Sharper Fourier weights (hard)

`cov_le` charges `b = p_R/(1−p_R)` for every nonzero frequency in a coordinate; that is the
trivial bound (size of the complement). The pass set is a union of `mb` evenly spaced
intervals, so its Fourier coefficient at frequency `x` is a Dirichlet kernel times a
geometric sum: it is of size `b` only for `x` near multiples of a fixed step, and much
smaller elsewhere. Using the true weight `D(x)` turns the weighted count into
`Σ_ξ Π_r D(ξ_r)` over test vectors with dual support on `S`, which depends on the *values*
of the coefficients of `ξ`, not only on its Hamming weight. Bounding that needs shortness
arguments in the ideal lattice (as in `item3.md`, but for the test vectors). Potentially a
large gain; no concrete plan.

## B4. Fourth moment (probably not worth it)

`E_A (E_t|ρ−μ|)` loses a square root from the second moment. A fourth-moment bound would
recover most of it for statistical distance, but needs orthogonality conditions for
quadruples of nonces sharing a tail. B2 gets the same benefit more cheaply.

---

# Suggested order

1. B1: restate what is already proved; no new mathematics.
2. P1 as an implementation experiment (it is exact; measure it, then decide how much timing
   analysis it deserves).
3. B2 on paper, then the one Lean theorem; decide then whether P3 is needed.
4. Algorithm 3 (`alg13.md`), then P2 on top of it.
5. Items 2, 3, 4 as before; B3 only if someone wants a research problem.

---

# Cost model (for the tables above)

Unit: one NTT. `K` = one Keccak-f permutation (0.3 to 1 NTT depending on vectorisation),
pointwise product or `Decompose` of one polynomial = 0.25.

- Sampling one polynomial of `y`: `5K`; forward NTT: 1.
- `w`: `k·ℓ` pointwise products (only for fresh polynomials; the kept partial sum is cached),
  `k` inverse NTTs, `k` decompositions.
- Challenge: `h·K` with `h = 8, 8, 9` (hash of `w₁` plus `SampleInBall`), `NTT(c)`: 1.
- z-check with early abort per polynomial: expected `(1 − p_z)/(1 − p_z^{1/ℓ})` polynomials,
  each one pointwise product and one inverse NTT.
- r₀-check: `k` pointwise products and `k` inverse NTTs.
- Accepted attempt additionally: `c·t₀` and the hint (`k` products and inverse NTTs).
- With P1: checks cost 0.1 per rejected attempt; `NTT(c)` and the full `c·s₁`, `c·s₂` are
  paid once, on the accepted attempt.
- Pass probabilities: `p_z = 0.54, 0.62, 0.66`; expected attempts `4.25, 5.1, 3.85`;
  r₀ pass probability `μ = 1/(attempts · p_z)`.
- Ignored: `c·t₀`/hint rejections, the cost of keeping the cached partial product, memory.
