# T-II-2-006: A degree-1 morphism is an isomorphism

**Status**: PARTIAL (worker-I, 2026-04-20) — function-field half delivered
(`pullback_surjective_of_degree_one`); full "IsIso of curves" packaging needs
the image-point correspondence (blocked).
**Silverman**: II.2.4.1 (Corollary)
**Module**: `HasseWeil/Curves/CurveMap.lean`
**Owner**: worker-I (partial)
**Estimated lines**: 30 (delivered ~20 for the pullback-surjective lemma)
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-2-003 (curves ↔ extensions functor)
- T-II-2-004 (degree)

## Blocks
- T-III-1-009 (singular Weierstrass equation analysis sometimes uses this)

## Statement (Silverman II.2.4.1)
Let `C₁`, `C₂` be smooth curves and `φ : C₁ → C₂` a morphism of degree one. Then
`φ` is an isomorphism.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A degree-1 morphism of smooth curves is an isomorphism.
    Reference: Silverman II.2.4.1. -/
theorem Morphism.isIso_of_degree_one (φ : Morphism C₁ C₂) (h : φ.degree = 1) :
    IsIso φ

end HasseWeil.Curves
```

## Notes
- Direct from II.2.4(b): if `[K(C₁) : φ*K(C₂)] = 1`, then `φ*` is an iso of
  function fields, which corresponds to an iso of curves by II.2.4(b).

## Progress log

- **2026-04-20** (worker-I): delivered `CurveMap.pullback_surjective_of_degree_one`
  in `HasseWeil/Curves/CurveMap.lean`: if `φ.degree = 1`, then `φ.pullback` is
  surjective. Combined with the automatic injectivity (`pullback_injective`),
  the pullback is a field bijection.
  Proof: use `Module.finrank_eq_one_iff'` (for `Module.Free` modules over a
  field, `finrank = 1 ↔ ∃ v ≠ 0, ∀ w, ∃ c, c • v = w`). Extract `c₀` such
  that `c₀ • v = 1`, deduce `v = (algebraMap c₀)⁻¹`, and then express any
  `w = c • v` as `algebraMap (c / c₀)`. Axiom-clean.
  **Blocker for full "IsIso of curves" form**: packaging as an isomorphism
  of `SmoothPlaneCurve` objects (with an inverse CurveMap, forward point map)
  requires the image-point correspondence (same as T-II-2-007 full form).

