# Reviewer reply — ChatGPT Pro (round 14) — 2026-05-15

## Assessment

Round 14's `RatioNodeData` is conceptually correct, but coherence is broken: `Refines` and `allSplitsInducing` each existentially pick their own `RatioNodeData` at each `nodeRatio`, so the same subtree could be interpreted over different sub-bases.

## Fixes required

1. **Add** `cover_covers : cover.covers = {plus, minus}` to `RatioNodeData` (exact 2-cover shape).

2. **Stop** independent existentials in separate predicates. Introduce a realization/decorated-tree object:

```lean
inductive RatioTreeRealization : RatioLaurentTree A → RationalLocData A → Type
  | leaf : RatioTreeRealization .leaf D
  | nodeLaurent :
      RatioTreeRealization L (laurentPlusDatum D f) →
      RatioTreeRealization R (laurentMinusDatum D f) →
      RatioTreeRealization (.nodeLaurent f L R) D
  | nodeRatio :
      (data : RatioNodeData D f g) →
      RatioTreeRealization L data.plus →
      RatioTreeRealization R data.minus →
      RatioTreeRealization (.nodeRatio f g L R) D
```

3. Define `RatioTreeRealization.Refines` and `RatioTreeRealization.allSplitsInducing` relative to the SAME realization `ρ`.

4. I.1's final output:
```lean
∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base),
  ρ.Refines C ∧ ρ.allSplitsInducing
```

## Manager message

This is the last structural correction. The validity package is correct; it just needs exact-two-cover data AND coherent use across the tree via a realization object.
