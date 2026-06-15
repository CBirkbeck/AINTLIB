# Reviewer reply — ChatGPT Pro (round 13) — 2026-05-15

## Assessment

Round 13's denominator-cleared formulas are valuation-correct, but they're NOT valid unconditionally as `RationalLocData A`. The formulas represent:
- `ratioPlusDatumDC D f g` = `R(D) ∩ {v(f) ≤ v(g)} ∩ {v(g) ≠ 0}`
- `ratioMinusDatumDC D f g` = `R(D) ∩ {v(g) ≤ v(f)} ∩ {v(f) ≠ 0}`

They cover `R(D)` only when `f`, `g` don't vanish simultaneously — true in the unit-ratio Wedhorn case, but NOT for arbitrary `f, g`. The `hopen` proofs aren't automatic either.

## Manager message

Don't keep unconditional definitions with sorry-filled hopen. Introduce a **validity package** like:

```lean
structure RatioNodeData (D : RationalLocData A) (f g : A) where
  plus : RationalLocData A
  minus : RationalLocData A
  cover : RationalCovering A
  cover_base : cover.base = D
  cover_pieces : cover.covers = {plus, minus}
  plus_open_eq : rationalOpen plus.T plus.s = R(D) ∩ {v(f) ≤ v(g)}
  minus_open_eq : rationalOpen minus.T minus.s = R(D) ∩ {v(g) ≤ v(f)}
```

Use this in BOTH `Refines` and `allSplitsInducing` so the same sub-bases are used coherently.

Then add the key transport theorem: relative Laurent split at `u_g · u_h⁻¹` over `𝒪(L)` transports to denominator-cleared absolute split `R(L) ∩ {v(g) ≤ v(h)}`.

After that, switch I.1 to output `RatioLaurentTree A`, embed outer Laurent tree via `nodeLaurent`, prove ratio-tree induction theorem.

## Answers

- Q1: Formulas valuation-correct but conditional. Need validity package.
- Q2: `ratioCoveringDC` right under unit/nonvanishing hypotheses. Inducing follows from relative Laurent + transport.
- Q3: Yes, captures Wedhorn's ratio split.
- Q4: Yes, switch I.1 to RatioLaurentTree A *after* validity package is in place.
