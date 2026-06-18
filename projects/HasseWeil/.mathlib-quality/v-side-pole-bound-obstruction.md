> **⛔ PARKED 2026-05-26 — fallback only.** QF witness committed to Route 1 (Pic⁰ / restricted
> dual additivity); see `expert-review/2026-05-26/integration.md` and `tickets/QF-PIC0-ROUTE.md`.
> **Reviewer correction (Q6):** the blanket `ord_∞((rV−s)*x) = −2` claim is valid only when the
> isogeny is separable at O; the general local formula is `ord_O(α*x) = −2·e_α(O)` with `e_α(O)`
> the ramification/inseparable contribution (tied to `deg_i(α)`). This affects only this parked
> V-side computation — it does NOT touch the in-hand V.1.3 bridge, where the isogeny is `1 − π`
> (separable, `e = 1`), so the `ord = −2` at kernel primes there is correct.

# V-side pole-bound discharge — sharp obstruction

Worker B's V-side D-track ships axiom-clean infrastructure
(commits `7350a72`, `3e81522`, `96e3da2`):
σ-V commute foundation, σ-action on `(V.zsmul r).pb`, pair σ-invariance
+ K(x_gen) image, witness-parametric `genuineIsogSmulSubV_of_pole_witness`.

**Open piece**: discharge `h_pole : ord_∞(addPullback_x_pair) < 0` for
the V-side family. Mirrors the π-side discharge
`ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg = -2` (commit
`84954ee`).

## What the π-side argument used

Strict ord-mismatch in the reduced numerator:

* `α₁(x) = (mulByInt_x r)^q` ord `-2q` (Frobenius q-th power).
* `α₂(x) = mulByInt_x (-s)` ord `-2`.
* `α₁(y)` ord `-3q`, `α₂(y)` ord `-3`.
* `(α₁(x) - α₂(x))²` ord `-4q`.
* Reduced numerator dominant: `α₁(x)²·α₂(x)` ord `-4q-2`.
* Other 7 terms ord `≥ -3q-3`, strictly above `-4q-2` for `q ≥ 2`.
* `ord(addPullback_x_pair) = -4q-2 − (-4q) = -2`.

The strict-dominance step is `ord_add_eq_of_lt` chained 7 times.

## What changes on V-side

V's x-coord pullback is the **q-th root** of the Frobenius-iterated
mulByInt_x:

```
(V.pb x_gen)^q = mulByInt_x W q     (via [q] = π · V)
```

For `(q : K) = 0` (which always holds since `q = #K` is a power of
char K), `mulByInt_x W q` has natDegree `q² − q` in `ΨSq_q` (not
`q² − 1` as the `(n : K) ≠ 0` case), giving x-degree `q`. Hence
`ord(mulByInt_x W q) = -2q` and **`ord(V.pb x_gen) = -2`** (not
`-2q` — the user's brief had this wrong).

Concretely on V-side:

* `α₁(x) = V.pb(mulByInt_x W r)` ord `-2`.
* `α₂(x) = mulByInt_x (-s)` ord `-2`.
* `α₁(y) = V.pb(mulByInt_y W r)` ord `-3` (curve-equation argument
  applied to `(V.pb(mulByInt_x r), V.pb(mulByInt_y r))` on `W_KE`).
* `α₂(y) = mulByInt_y (-s)` ord `-3`.

## The obstruction

The reduced-numerator term ords:

| term | x-side | y-side | combined ord |
|------|--------|--------|--------------|
| `X₁²·X₂` | `-4 + -2 = -6` | — | `-6` |
| `X₁·X₂²` | `-2 + -4 = -6` | — | `-6` |
| `2·Y₁·Y₂` | — | `-3 + -3 = -6` | `-6` |
| `a₄·(X₁+X₂)` | `≥ -2` | — | `≥ -2` |
| `2·a₆` | `≥ 0` | — | `≥ 0` |
| `-a₃·(Y₁+Y₂)` | — | `≥ -3` | `≥ -3` |
| `-a₁·(X₁Y₂+X₂Y₁)` | `≥ -2-3 = -5` | — | `≥ -5` |
| `2·a₂·X₁·X₂` | `≥ -4` | — | `≥ -4` |

**Three terms compete for dominant ord `-6`**: `X₁²X₂`, `X₁X₂²`, and
`-2Y₁Y₂`. The π-side had a unique strict dominant
(`α₁(x)²·α₂(x) = -4q-2`, all others `≥ -3q-3 > -4q-2`); V-side has a
3-way tie at `-6`.

The strict non-arch chain `ord_add_eq_of_lt` requires unique dominant.
For V-side with three competing terms at `-6`, we'd need:

1. A specific algebraic identity showing the sum of the three has ord
   exactly `-6` (no full cancellation), OR
2. A finer ord argument distinguishing among the three.

Neither is straightforward. The Weierstrass equations for `(X_i, Y_i)`
on `W_KE` do give algebraic relations among `X_i^j`, `Y_i Y_j`,
`X_i Y_j`, but expressing `X₁²X₂ + X₁X₂² − 2Y₁Y₂` as a sum with
cleanly-bounded ord requires curve-coefficient-specific work.

## Why this isn't a per-prime issue

The V-side ord values (`-2` for x, `-3` for y) are **universal in q**
— they don't depend on q at all (since V's q-th iterate gives the
factor of q, but V itself doesn't scale ords). So the obstruction is
**structural**, not q-specific: a 3-way ord tie at the dominant level
of the reduced numerator.

## Failed approaches

1. **Strict ord-mismatch on x-coord**: ord(α₁(x)) = ord(α₂(x)) = -2.
   No ord mismatch. ❌
2. **Strict ord-mismatch on y-coord**: ord(α₁(y)) = ord(α₂(y)) = -3.
   No mismatch. ❌
3. **x-degree mismatch via π-pullback**: applying π.pb to a putative
   `V.pb(mulByInt_x r) = mulByInt_x s` gives `mulByInt_x (qr) =
   (mulByInt_x s)^q`. Both have ord `-2q` (computed via
   `(V.pb(mulByInt_x r))^q` = `mulByInt_x (qr)`). x-degrees in
   `K(x_gen)` are both `q`. **No mismatch**. ❌
4. **Slope ord**: `ord(L) = ord(Y₁-Y₂) - ord(X₁-X₂) ≥ -3 - (-2) = -1`.
   Typically `-1` for h_x_ne case. `ord(L²) ≥ -2`. Doesn't strictly
   distinguish. ❌
5. **Curve specialisation**: for specific curves (e.g.
   `b₂ = 1, b₈ = 0, b₆ = -b₄` in char 2), `V.pb(x_gen) = x_gen` and
   the x-conjunct of AddNonInverse fails for `(r, s) = (1, 1)`.
   Smoothness (Δ ≠ 0) doesn't exclude these (Δ = c³ ≠ 0 for c ≠ 0
   under the constraints). So per-curve discharge has a non-trivial
   obstruction set. ❌

## Forward path

The V-side pole bound likely needs Worker C's universal Φ_q output
(for the explicit V structure beyond the witness-parametric
`verschiebungIsog_of_witness`) AND a more detailed analysis of the
3-way ord tie at `-6` in the reduced numerator. Specifically:

* **Either** prove a curve-coefficient identity showing
  `X₁²X₂ + X₁X₂² − 2Y₁Y₂ ≠ -2 a₂ X₁ X₂` modulo the curve relations
  (so the three `-6` terms plus the `2 a₂ X₁ X₂` correction don't
  cancel completely), giving a strict-ord argument.
* **Or** use a different pole-bound argument: e.g., compute
  `(rq − s)·P_gen ≠ O` directly (the addition is non-trivial as a
  group hom) and chain to the function-field level via the
  `degree_quadratic_genuine_addIsog` polarisation argument (which
  itself needs the pole bound).

The cleanest path is likely Worker C's universal Φ_q + a generic
"non-trivial isogeny → pole at infinity" lemma. Both are upstream of
Worker B's current scope.

## Status

* **Shipped axiom-clean** (commits `7350a72`, `3e81522`, `96e3da2`):
  V-side σ-V commute, σ-action on `(V.zsmul r).pb` of x/y generators,
  pair σ-invariance + K(x_gen) image, witness-parametric
  `genuineIsogSmulSubV_of_pole_witness`.
* **Open**: pole-bound discharge for V-side. Sharp 3-way ord tie at
  `-6` in the reduced numerator; requires curve-coefficient identity
  or different non-pole approach.
