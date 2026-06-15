# D3b general (r,s) `AddNonInversePair` — `rw` wall

Worker B encountered a stubborn `rw` pattern-matching wall while
generalising Worker A's `(r, s) = (1, 1)` `AddNonInversePair` (in
`HasseWeil/AdditionPullback/Frobenius.lean`, commit `4bd0ab8`) to
arbitrary `(r, s) ≠ (0, 0)`. Sound math (ord-at-infinity argument), but
the Lean implementation walls on what looks like coercion / instance /
metavariable mismatch around `WithTop ℤ` arithmetic. Recording the wall
here so Worker A can attempt with deeper LSP traces.

## Math approach (sound)

For `(r, s)` with `r ≠ 0`, `(r : K) ≠ 0`, `s ≠ 0`, `(s : K) ≠ 0`:

* `((zsmul r π).pullback x_gen) = ((mulByInt r).pullback x_gen) ^ q`
  (contravariant pullback composition + Frobenius q-th-power on `K(E)`).
* For `(r : K) ≠ 0`, `ord_∞ ((mulByInt r).pullback x_gen) = -2`
  (Sutherland 6.9 / Silverman III.2.5: the pole order of `x` at the
  identity point is preserved under `[r]`, since `mulByInt_x = Φ_r / ΨSq_r`
  with `deg Φ_r = r²` and `deg ΨSq_r = r² - 1`; the difference is
  consistently `-2`).
* Hence `ord_∞ ((zsmul r π).pullback x_gen) = -2 q`.
* For `(s : K) ≠ 0`, `ord_∞ ((mulByInt -s).pullback x_gen) = -2`.
* For `q ≥ 2`, `-2q ≠ -2`, so the two pullbacks differ.
* `AddNonInversePair_of_x_ne` then concludes the pair is non-inverse.

## Wall instances (4 distinct named-tactic failures)

All in a draft `HasseWeil/AdditionPullback/FrobeniusZsmul.lean` (since
deleted; reconstruct from the math sketch above).

### Failure 1: `simp at this` not closing for `↑(-2 · n²) = ⊤`

Goal:
```
this : ((-2 * (n.natAbs : ℤ) ^ 2 : ℤ) : WithTop ℤ) = ⊤
⊢ False
```

`simp [SmoothPlaneCurve.ordAtInfty_zero] at this` failed with
"unsolved goals". The `↑(-2 · n²)` coercion to `WithTop ℤ` doesn't
reduce against `⊤` via simp. Tried `WithTop.coe_ne_top this` directly —
also failed (type mismatch between `((... : ℤ) : WithTop ℤ)` and
`(⊤ : WithTop ℤ)`).

### Failure 2: `rw [SmoothPlaneCurve.ordAtInfty_div_eq_mul_inv ...]`

Pattern: `(W_smooth W).ordAtInfty (Φ_ff W n / ΨSq_ff W n)`.

Target: `(W_smooth W).ordAtInfty (Φ_ff W n / ΨSq_ff W n) = ↑(-2)`.

Lean error: "Did not find an occurrence of the pattern X in the target
expression X" — pattern and target visually identical.

Tried with `(W_smooth W).ordAtInfty_div_eq_mul_inv ...` (dot notation),
also `Curves.SmoothPlaneCurve.ordAtInfty_div_eq_mul_inv (W_smooth W) ...`
(fully qualified). Both failed identically.

Hypothesis: `f / g` in `Φ_ff W n / ΨSq_ff W n` may use `HDiv.hDiv` while
`ordAtInfty_div_eq_mul_inv` expects `Div.div` (or vice versa); the two
are definitionally equal but `rw` is syntactic.

### Failure 3: `simp at this` not closing for `↑(-2) = ⊤`

Same as Failure 1, different specific equation. The `WithTop.coe_ne_top`
+ simp combo doesn't auto-discharge.

### Failure 4: `rw [SmoothPlaneCurve.ordAtInfty_pow ... h_ne (Fintype.card K)]`

Pattern: `(W_smooth W).ordAtInfty (mulByInt_x W r ^ ?n)` (where `?n` is
metavar to be unified with `Fintype.card K`).

Target: `(W_smooth W).ordAtInfty (mulByInt_x W r ^ Fintype.card K) =
↑(-2 * ↑(Fintype.card K))`.

Lean error: "Did not find an occurrence of the pattern X in the target
expression X" — pattern (with the metavar resolved) and target visually
identical.

Tried `SmoothPlaneCurve.ordAtInfty_pow_of_ord_eq` instead (avoids the
intermediate `n • ord` form); same failure mode.

## Wall-break techniques to attempt

Per Worker B's H3 break (commit `d38e833`), the techniques that worked
were inner-K[X] induction + sidestepping `algebraMap` ↔ `aeval`
identification. For this wall, candidates not exhausted:

1. **`set_option pp.all true` + manual goal inspection** — print the
   actual term structure; the visible `pattern = target` mismatch is
   almost certainly a hidden coercion or instance-resolution artefact.
2. **`change` instead of `rw`** — if patterns mysteriously fail to
   match. Force the goal to defeq form.
3. **`@`-explicit instance threading** — bypass instance unification
   ambiguity. For `WithTop ℤ`, the `Add`, `HMul`, `HPow` instances may
   resolve through different paths.
4. **`norm_cast` + `push_cast` chains** — normalise WithTop ℤ
   coercions before applying lemmas.
5. **`convert` instead of `rw`** — emits remaining goals for any
   pieces that don't unify, instead of an opaque "pattern not found".
6. **Inline manual proof via `have h : ... = ... := ... ; exact
   h.trans ...`** — bypasses `rw` pattern matching entirely.

## Files / commits to reference

* Worker A's (1, 1) base case:
  `HasseWeil/AdditionPullback/Frobenius.lean:2749`
  (`AddNonInversePair_zsmul_one_frobenius_mulByInt_neg_one`),
  commit `4bd0ab8`.
* `AddNonInversePair_of_x_ne` builder: `HasseWeil/AdditionPullback.lean:719`.
* Existing `ordAtInfty_*` infrastructure:
  `HasseWeil/OrdAtInftyBridge.lean` (unconditional ord values for
  `Φ_ff`, `ΨSq_ff`, `x_gen`, `y_gen`, `x_gen ^ n`, `y_gen ^ n`).
* `mulByInt_pullback_x`: `HasseWeil/OmegaPullbackCoeff.lean:130`.
* `SmoothPlaneCurve.ordAtInfty_div_of_ord_eq`,
  `ordAtInfty_pow_of_ord_eq`: `HasseWeil/Curves/Infinity.lean:917`,
  `:935` — the integer-friendly variants that should avoid the `WithTop
  ℤ` arithmetic mess (Worker B's second attempt also walled here).

## Why this matters

Discharging this would close the qf_nonneg side of the bound for non-zero
`(r, s)` where both are coprime to `char K`. Combined with `qf_nonneg`
trivially holding at `(0, 0)` (`0 ≤ 0`), and a separate handling of
`(r, s)` divisible by `char K` (likely via the `mulByInt p` placeholder
shape and an analogous ord argument), the full `qf_nonneg` lemma feeds
the `HasseWitnesses` record's `qf_nonneg` field.

That field is one of the two outstanding witnesses on the bound (the
other being `pc_fiber_witness`, in flight via Worker B's Mathlib PR for
Silverman III.4.10(a)).

## Recommended next worker action

Worker A or whoever picks this up next: enable `set_option pp.all true`
on the failing rewrite, capture the actual `WithTop ℤ` term structure of
both pattern and target, and pinpoint the hidden mismatch. Most likely
candidates: `HDiv.hDiv` vs `Div.div`, or `HPow.hPow` with implicit
universe variables, or `WithTop.coe` vs `Nat.cast ∘ Int.cast` chains.
