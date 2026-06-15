# T-II-2-004: deg, deg_s, deg_i

**Status**: DONE (2026-04-18)
**Silverman**: II.2 (definitions)
**Module**: `HasseWeil/Curves/CurveMap.lean`
**Owner**: worker-H
**Estimated lines**: 40 (delivered in CurveMap.lean as `degree`, `separableDegree`, `inseparableDegree`, `IsSeparable`, `IsPurelyInseparable`)
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-2-003 (finite extension)

## Blocks
- T-II-2-008, T-II-2-009 (formulas)
- T-III-4-002 (isogeny degrees)

## Statement
For a nonconstant map `φ : C₁ → C₂`, define:
- `deg(φ) = [K(C₁) : φ*K(C₂)]` (extension degree)
- `deg_s(φ) = [K(C₁) : φ*K(C₂)]_s` (separable degree)
- `deg_i(φ) = [K(C₁) : φ*K(C₂)]_i` (inseparable degree)

For constant maps, `deg = 0`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- Degree of a map of smooth curves. Defined as `[K(C₁) : φ*K(C₂)]` for nonconstant φ,
    and 0 for constant φ. Reference: Silverman II.2 (definition). -/
noncomputable def Morphism.degree (φ : Morphism C₁ C₂) : ℕ

/-- Separable degree. -/
noncomputable def Morphism.degreeSep (φ : Morphism C₁ C₂) : ℕ

/-- Inseparable degree. -/
noncomputable def Morphism.degreeInsep (φ : Morphism C₁ C₂) : ℕ

theorem Morphism.degree_eq_sep_mul_insep (φ : Morphism C₁ C₂) :
    φ.degree = φ.degreeSep * φ.degreeInsep

/-- A morphism is **separable** if its inseparable degree is 1. -/
def Morphism.IsSeparable (φ : Morphism C₁ C₂) : Prop := φ.degreeInsep = 1

/-- A morphism is **purely inseparable** if its separable degree is 1. -/
def Morphism.IsPurelyInseparable (φ : Morphism C₁ C₂) : Prop := φ.degreeSep = 1

end HasseWeil.Curves
```

## Notes
- We already have similar definitions in `SeparableDegree.lean` for isogenies.
  This generalizes to maps of curves (and the isogeny version becomes a special
  case).
- mathlib has `Field.finSepDegree` which gives `deg_s`. The product
  `deg = deg_s * deg_i` is `Field.finSepDegree_mul_finSepDegree`.

## Progress log
