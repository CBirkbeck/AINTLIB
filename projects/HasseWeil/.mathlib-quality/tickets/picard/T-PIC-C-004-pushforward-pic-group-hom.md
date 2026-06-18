# T-PIC-C-004: `φ_∗ : Pic⁰(E₁) → Pic⁰(E₂)` is a group hom

**Status**: OPEN
**Silverman**: III.4.8 proof — `φ_∗` group hom by functoriality
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean`
**Owner**: —
**Estimated lines**: ~50
**Difficulty**: easy
**Phase**: C

## Depends on
- T-PIC-C-002 (`pushforwardDegZero` lands in Div⁰)
- T-PIC-C-003 (preserves principal)

## Blocks
- T-PIC-D-001 (diagram commute)
- T-PIC-F-002 (Pic⁰ ≅ E packaging)
- T-PIC-F-003 (B-4-003 closure)

## Statement

```lean
/-- Pushforward `φ_∗ : Pic⁰(E₁) → Pic⁰(E₂)` for an isogeny with coord
witness. By T-PIC-C-002 the pushforward preserves degree-zero, and by
T-PIC-C-003 it preserves principal divisors, so it descends to the
quotient `Pic⁰`. -/
noncomputable def pushforwardPicZero (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) :
    PicProj₀ (⟨W₁⟩ : Curves.SmoothPlaneCurve F) →+
      PicProj₀ (⟨W₂⟩ : Curves.SmoothPlaneCurve F) := by
  -- Use QuotientAddGroup.lift on `pushforwardDegZero` (T-PIC-C-002),
  -- with vanishing on principal-mod-degZero from T-PIC-C-003.
  ...

@[simp] theorem pushforwardPicZero_mk (φ) (cd) (D) :
    pushforwardPicZero φ cd (PicProj₀.mk D) =
      PicProj₀.mk (pushforwardDegZero φ cd D) := rfl
```

## Mathlib check
Standard `QuotientAddGroup.lift` machinery.

## Naming
`pushforwardPicZero`.

## Generality
Same as Phase C defaults (likely with `[IsAlgClosed F]` inherited from
T-PIC-C-003).

## Proof approach

`QuotientAddGroup.lift`:
- Pre-quotient hom: `pushforwardDegZero φ cd : Div⁰_E₁ → Div⁰_E₂`
  (T-PIC-C-002).
- Vanishing on principal subgroup: T-PIC-C-003 + the principal-divisor-is-
  in-principal-subgroup quotient closure.

## Acceptance criteria

`#print axioms HasseWeil.EC.Isogeny.pushforwardPicZero` reports only
standard axioms.

## Progress log
