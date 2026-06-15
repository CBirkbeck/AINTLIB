# T-III-6-002: Dual as composition E₂ → Pic⁰(E₂) → Pic⁰(E₁) → E₁

**Status**: OPEN
**Silverman**: III.6.1(b)
**Module**: `HasseWeil/EC/DualIsogeny.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-3-004 (Pic⁰ ≅ E)
- T-II-3-011 (φ_*)
- T-III-6-001 (dual exists)

## Blocks
- T-III-6-005 (dual additivity)

## Statement (Silverman III.6.1(b))
The dual isogeny `φ̂ : E₂ → E₁` is given by the composition
`E₂ ≅ Pic⁰(E₂) → Pic⁰(E₁) ≅ E₁`,
where the middle map is induced by the pullback `φ* : Div(E₂) → Div(E₁)`
restricted to `Div⁰` and quotiented to `Pic⁰`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The dual isogeny equals the Pic⁰ functoriality composition.
    Reference: Silverman III.6.1(b). -/
theorem Isogeny.dual_eq_pic_pullback (φ : Isogeny E₁ E₂) (hφ : φ ≠ 0) :
    φ.dual = (E₁.picZeroEquiv.toAddMonoidHom.comp
                (Divisor.pullback ... .restrict_picZero).toAddMonoidHom).comp
              E₂.picZeroEquiv.symm.toAddMonoidHom

end HasseWeil.EC
```

## Notes
- This is the conceptual definition. Useful for proving functoriality and
  additivity (T-III-6-004, T-III-6-005).

## Progress log
