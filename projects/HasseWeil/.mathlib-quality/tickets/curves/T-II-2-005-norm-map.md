# T-II-2-005: Norm map φ_*

**Status**: REVIEW (worker-I, 2026-04-20)
**Silverman**: II.2 (definition)
**Module**: `HasseWeil/Curves/CurveMap.lean`
**Owner**: worker-I
**Estimated lines**: 30 (delivered ~20)
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-2-003, T-II-2-004

## Blocks
- T-II-3-011 (φ_* on divisors)
- T-II-3-012 (Prop II.3.6)

## Statement
For a nonconstant map `φ : C₁ → C₂` of smooth curves, define the norm map (also
called pushforward) `φ_* : K(C₁) → K(C₂)` as the composition

```
φ_* = (φ*)⁻¹ ∘ N_{K(C₁)/φ*K(C₂)}
```

where `N` is the algebra norm.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The norm map `φ_* : K(C₁) → K(C₂)` for a nonconstant morphism of curves.
    Defined as the composition of the field norm with the inverse pullback.
    Reference: Silverman II.2 (definition). -/
noncomputable def Morphism.pushforward (φ : Morphism C₁ C₂) (hφ : ¬ IsConst φ) :
    C₁.FunctionField → C₂.FunctionField

theorem Morphism.pushforward_pullback (φ : Morphism C₁ C₂) (hφ : ¬ IsConst φ)
    (g : C₂.FunctionField) :
    φ.pushforward hφ (φ.pullback g) = (φ.degree : C₂.FunctionField) * g

end HasseWeil.Curves
```

## Notes
- `Algebra.norm` from mathlib (`Mathlib.RingTheory.Norm.Basic`) gives the norm of
  a finite field extension.
- φ_* is multiplicative: `φ_*(fg) = φ_*(f) φ_*(g)`. This is a property of the norm.
- For a Galois extension with Galois group G, `φ_*(f) = ∏_{σ ∈ G} σ(f)` where σ
  ranges over Aut(K(C₁)/φ*K(C₂)).

## Progress log

- **2026-04-20** (worker-I): delivered in `HasseWeil/Curves/CurveMap.lean`:
  - `CurveMap.pushforward φ : K(C₁) →* K(C₂)` — mathlib's `Algebra.norm`
    over the `φ.toAlgebra` structure (pullback-induced). Simplification
    of Silverman's `(φ*)⁻¹ ∘ N`: mathlib's `Algebra.norm R : S →* R` already
    lands in the base, so no inversion needed.
  - `pushforward_pullback : pushforward (pullback g) = g ^ degree φ` via
    `Algebra.norm_algebraMap`.
  - `pushforward_mul`, `pushforward_one` (simp, via `MonoidHom.map_mul/one`).
  All axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
