# T-PIC-C-001: `pushforwardDivisor`: divisor-level pushforward via `toPointMap`

**Status**: DONE (`pushforwardProjectiveDivisor` in
`HasseWeil/Curves/PicZeroPushforward.lean`, axiom-clean)
**Silverman**: II.3.7 (referenced from III.4.8 proof) — finite morphism
pushforward of divisors
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean` (NEW FILE)
**Owner**: —
**Estimated lines**: ~60
**Difficulty**: easy
**Phase**: C

## Depends on
- `HasseWeil/EC/IsogenyAG.lean` — `Isogeny W₁ W₂`, `toPointMap`, `coordHom`
- T-II-3-001b (DONE) — `ProjectiveDivisor`
- T-PIC-A-001 (`Point.toProjectiveSmoothPoint` may need to be defined here
  or in PicZero.lean; this ticket can build it locally)

## Blocks
- T-PIC-C-002, C-003, C-004 (downstream Phase C)

## Statement

For `φ : Isogeny W₁ W₂` with a coordHom witness, define the pushforward
of divisors:

```lean
namespace HasseWeil.EC.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
  {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- Pushforward of a `ProjectiveDivisor` along an isogeny: the divisor
`Σ n_i (P_i)` maps to `Σ n_i (φ(P_i))`, where `φ(P_i)` uses the induced
point map.

Defined for `Isogeny.AG` with a coord-ring witness, since the point map
requires it. -/
noncomputable def pushforwardProjectiveDivisor (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (D : ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F)) :
    ProjectiveDivisor (⟨W₂⟩ : Curves.SmoothPlaneCurve F) :=
  D.mapDomain fun P => (φ.toPointMap cd P.toAffinePoint).toProjectiveSmoothPoint

@[simp] theorem pushforwardProjectiveDivisor_zero (φ) (cd) :
    pushforwardProjectiveDivisor φ cd 0 = 0

@[simp] theorem pushforwardProjectiveDivisor_add (φ) (cd) (D₁ D₂) :
    pushforwardProjectiveDivisor φ cd (D₁ + D₂) =
      pushforwardProjectiveDivisor φ cd D₁ + pushforwardProjectiveDivisor φ cd D₂

theorem pushforwardProjectiveDivisor_smul (n : ℤ) (φ) (cd) (D) :
    pushforwardProjectiveDivisor φ cd (n • D) = n • pushforwardProjectiveDivisor φ cd D
```

## Mathlib check
`Finsupp.mapDomain` provides the underlying machinery; preserves `+` and
`smul`. Standard mathlib lemmas should give the API.

## Naming
`pushforwardProjectiveDivisor` (long but unambiguous).

## Generality
- `[DecidableEq F]` (needed because `W.Point` has Add, requiring DecidableEq).
- Otherwise standard Phase A/B/C parametrization.
- Don't require `[IsAlgClosed F]`.

## Proof approach

```lean
noncomputable def pushforwardProjectiveDivisor (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) :
    ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F) →+ ProjectiveDivisor (⟨W₂⟩ : SmoothPlaneCurve F) :=
  Finsupp.mapDomain.addMonoidHom fun P =>
    (φ.toPointMap cd P.toAffinePoint).toProjectiveSmoothPoint
```

Then the simp lemmas come from `Finsupp.mapDomain` API.

May need a helper:
```lean
def Affine.Point.toProjectiveSmoothPoint (P : W.Point) :
    ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F) :=
  match P with | .zero => .infinity | .some x y h => .affine ⟨x, y, h⟩
```

## Acceptance criteria

`#print axioms HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor` reports
only standard axioms.

## Progress log
