# T-II-2-003: Equivalence smooth curves ↔ finitely generated extensions

**Status**: OPEN
**Silverman**: II.2.4 (Theorem)
**Module**: `HasseWeil/Curves/Maps.lean`
**Owner**: (unassigned)
**Estimated lines**: 120
**Difficulty**: hard
**Stream**: A

## Depends on
- T-II-2-001, T-II-2-002

## Blocks
- T-III-4-010 (every isogeny is a homomorphism)

## Statement (Silverman II.2.4)
(a) Let `φ : C₁ → C₂` be a nonconstant map defined over K. Then `K(C₁)` is a
    finite extension of `φ*(K(C₂))`.
(b) Let `ι : K(C₂) → K(C₁)` be an injection of function fields fixing K. Then
    there exists a unique nonconstant map `φ : C₁ → C₂` (defined over K) such
    that `φ* = ι`.
(c) Let `K ⊂ K(C₁)` be a subfield of finite index containing K. Then there
    exists a smooth curve C'/K, unique up to K-isomorphism, and a nonconstant
    map `φ : C₁ → C'` defined over K such that `φ*(K(C')) = K`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- (a) A nonconstant morphism induces a finite extension of function fields. -/
theorem map_finite_extension {C₁ C₂ : SmoothPlaneCurve F}
    (φ : Morphism C₁ C₂) (hφ : ¬ IsConst φ) :
    FiniteDimensional (φ.pullback.range) C₁.FunctionField

/-- (b) Every K-injection of function fields comes from a unique nonconstant map. -/
theorem map_of_field_injection {C₁ C₂ : SmoothPlaneCurve F}
    (ι : C₂.FunctionField →ₐ[F] C₁.FunctionField) (hι : Function.Injective ι) :
    ∃! φ : Morphism C₁ C₂, φ.pullback = ι

/-- (c) Every finite-index subfield of K(C₁) corresponds to a smooth curve C'. -/
theorem curve_of_subfield {C₁ : SmoothPlaneCurve F} (M : Subalgebra F C₁.FunctionField)
    (h : Module.Finite M C₁.FunctionField) :
    ∃ C' : SmoothPlaneCurve F, ∃ φ : Morphism C₁ C',
      Function.Surjective φ.pullback ∧ φ.pullback.range = M

end HasseWeil.Curves
```

## Notes
- This is a major theorem and is **the** equivalence of categories between smooth
  curves over K and finitely generated field extensions of K of transcendence
  degree 1.
- The proof in Silverman is two pages and references [111, II.6.8] and others.
- For (b), the key construction: given ι, take generators g_i ∈ K(C₁) of K(C₁)
  over K. Use ι to define φ via the homogeneous coordinates [1, ι(g_1), ..., ι(g_N)].
- Mathlib has `Scheme.RationalMap.functionFieldEquiv` which is closely related.

## Progress log
