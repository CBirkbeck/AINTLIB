# T-III-6-009: deg : Hom(E₁,E₂) → ℤ is positive definite quadratic form

**Status**: PARTIAL (HasseWeil/DegreeQuadraticForm.lean exists)
**Silverman**: III.6.3
**Module**: `HasseWeil/DegreeQuadraticForm.lean` → `HasseWeil/EC/DegreeForm.lean`
**Owner**: (existing)
**Estimated lines**: 100
**Difficulty**: medium (CRITICAL)
**Stream**: C

## Depends on
- T-III-6-005 (dual additivity)
- T-III-6-006 ([m]^ = [m], deg [m] = m²)
- T-III-6-007 (deg dual)

## Blocks
- T-V-1-005 (Cauchy-Schwarz)
- T-V-1-006 (Hasse bound)

## Statement (Silverman III.6.3)
The function `deg : Hom(E₁, E₂) → ℤ` is a **positive definite quadratic form**.
That is, the associated bilinear pairing
`⟨φ, ψ⟩ := deg(φ + ψ) − deg φ − deg ψ`
is symmetric and bilinear, and `deg φ ≥ 0` with equality iff `φ = 0`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The degree map is a positive definite integer-valued quadratic form on Hom.
    Reference: Silverman III.6.3. -/
def Isogeny.degForm (E₁ E₂ : WeierstrassCurve F) [Fact (E₁.Δ ≠ 0)] [Fact (E₂.Δ ≠ 0)] :
    QuadraticForm ℤ (Isogeny E₁ E₂)

theorem Isogeny.degForm_pos_def (E₁ E₂ : WeierstrassCurve F)
    [Fact (E₁.Δ ≠ 0)] [Fact (E₂.Δ ≠ 0)] :
    (Isogeny.degForm E₁ E₂).PosDef

end HasseWeil.EC
```

## Notes
- Quadratic: `deg(φ + ψ)` expanded via `(φ+ψ)^ ∘ (φ+ψ) = φ̂φ + φ̂ψ + ψ̂φ + ψ̂ψ
  = [deg φ + deg ψ + tr(φ̂ψ)]`. The trace term is the bilinear pairing.
- Positive definite from `deg φ > 0` for nonzero φ.
- Existing `DegreeQuadraticForm.lean` has the algebraic structure but pulls in
  the additivity from a SORRY (which is T-III-5-002 / T-III-6-005).

## Detailed Silverman III.6.3 proof

**Bilinearity of `⟨φ, ψ⟩ := deg(φ+ψ) - deg φ - deg ψ`**:

Compute `deg(φ+ψ) = (φ+ψ)̂ ∘ (φ+ψ)` (applied to some fixed point, giving
a multiplication-by-n map). By III.6.2(c) (dual additivity, T-III-6-005):
`(φ+ψ)̂ = φ̂ + ψ̂`.
Hence:
```
deg(φ+ψ) = (φ̂ + ψ̂) ∘ (φ + ψ)
         = φ̂∘φ + φ̂∘ψ + ψ̂∘φ + ψ̂∘ψ
         = [deg φ] + φ̂∘ψ + ψ̂∘φ + [deg ψ]
         = [deg φ + deg ψ + (deg of φ̂∘ψ + ψ̂∘φ as an integer)]
```
So `⟨φ, ψ⟩ = deg(φ̂∘ψ + ψ̂∘φ)` — this is symmetric in φ, ψ (swap roles of
dual) and bilinear (dual is additive by T-III-6-005).

**Positive definiteness**:
- `deg φ ≥ 0` since `deg` is a nonnegative integer (III.4.2).
- `deg φ = 0` ⟺ `φ = 0`: one direction is III.4.2(b) (deg 0 = 0, by
  convention). Other direction: if `φ ≠ 0`, then `φ` is surjective
  (II.2.2), so ker is finite and `deg φ = [K(E₁) : φ*K(E₂)]` is a positive
  integer.

## File `DegreeQuadraticForm.lean` sorry (L88)

The current file has:
```
theorem degree_form_expansion_of_smul_sub ... :
    (β.degree : ℤ) = (α.degree : ℤ) * r^2 - (isogTrace α one_sub_α) * r * s + s^2
```

This is the explicit form of `⟨·,·⟩` applied to `β = r·α - s·id`, expanded
via `deg β = (r·α̂ - s·id̂)(r·α - s·id) = r² (α̂∘α) + s² - rs(α̂ + α)`
(using `id̂ = id` by T-III-6-006).

The sorry needs:
- `isogDual_add` (T-III-6-005)
- `isogDual_mulByInt` (T-III-6-006)
- `isogDual_comp_self` (T-III-6-001, via α̂∘α = [deg α])

All these depend on T-III-6-001 which is BLOCKED.

## Progress log
