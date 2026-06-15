# Reviewer reply — ChatGPT Pro (round 12) — 2026-05-15

## Assessment

The switch to `RatioLaurentTree A` is correct conceptually. But the current `nodeRatio` definitions require global inverses `f_inv, g_inv ∈ A₀` — which is mathematically WRONG for Wedhorn's setting. Wedhorn's ratio units are units in `O(D)`, NOT in `A`.

## Fix: denominator-cleared ratio data

Replace the existential-global-inverse formulation with **deterministic denominator-cleared** sub-bases:

```lean
ratioPlusDatumDC D f g:
  denominator: D.s * g
  numerators:  {t*g | t ∈ D.T} ∪ {D.s*f}

ratioMinusDatumDC D f g:
  denominator: D.s * f
  numerators:  {t*f | t ∈ D.T} ∪ {D.s*g}
```

No `f_inv`/`g_inv` required. The rational opens are:
- plus: `D ∩ {v(f) ≤ v(g)}`
- minus: `D ∩ {v(g) ≤ v(f)}`

Then update `RatioLaurentTree.Refines` and `.allSplitsInducing` to use these.

## Other answers

- Q1: Refines not correctly stated with global inverses; switch to denominator-cleared.
- Q2: `ratioCovering` correct only if denominator-cleared (the existing project version uses global inverses).
- Q3: I.1 should output `RatioLaurentTree A`; outer first-stage `LaurentTree A` embeds via `nodeLaurent`; need `graftAt` for RatioLaurentTree.
- Q4: Not quite final until nodeRatio's unit notion is fixed.

## Manager message

Wedhorn's ratio units live in `O(D)`, not `A`. The `nodeRatio` case must use denominator-cleared rational data, not global inverses. After this fix, the architecture is correct.
