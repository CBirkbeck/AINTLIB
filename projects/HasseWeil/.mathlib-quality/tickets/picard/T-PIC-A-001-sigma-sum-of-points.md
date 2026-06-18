# T-PIC-A-001: σ : ProjectiveDiv⁰(E) → E (sum-of-points map)

**Status**: DONE (verified axiom-clean 2026-05-13: `projectiveDivisorSum`, `projectiveDivisorSumHom`, `projectiveDivisorSum_zsmul` all depend only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: III.3.4 definition of σ
**Module**: `HasseWeil/Curves/PicZero.lean` (NEW FILE)
**Owner**: —
**Estimated lines**: ~80
**Difficulty**: easy
**Phase**: A

## Depends on
- T-II-3-001b (DONE) — `ProjectiveDivisor C`
- T-II-3-001b (DONE) — `ProjectiveDivisor.degZero`
- Existing: `Affine.Point` group structure (mathlib)
- `HasseWeil/EC/IsogenyAG.lean` — for `Affine F = WeierstrassCurve F` aliases

## Blocks
- T-PIC-A-002, T-PIC-A-003 (downstream Phase A)
- T-PIC-D-001 (diagram commute)

## Statement

For an elliptic Weierstrass curve `W : Affine F` with `[W.IsElliptic]`,
define the sum-of-points map on degree-0 projective divisors:

```lean
namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]

/-- The "sum of points" map on a `ProjectiveDivisor`: send
`Σ n_i (P_i)` to `Σ n_i • P_i` using the elliptic-curve group law.
The point at infinity contributes `0`. -/
noncomputable def projectiveDivisorSum (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    W.Point :=
  D.support.sum fun P => D P • P.toAffinePoint
  -- where ProjectiveSmoothPoint.toAffinePoint sends infinity ↦ 0,
  -- affine ⟨x, y, h⟩ ↦ Point.some x y h

@[simp] theorem projectiveDivisorSum_zero : projectiveDivisorSum W 0 = 0 := ...

@[simp] theorem projectiveDivisorSum_add (D₁ D₂ : ProjectiveDivisor _) :
    projectiveDivisorSum W (D₁ + D₂) =
      projectiveDivisorSum W D₁ + projectiveDivisorSum W D₂ := ...

theorem projectiveDivisorSum_smul (n : ℤ) (D : ProjectiveDivisor _) :
    projectiveDivisorSum W (n • D) = n • projectiveDivisorSum W D := ...

@[simp] theorem projectiveDivisorSum_single (P : ProjectiveSmoothPoint _) (n : ℤ) :
    projectiveDivisorSum W (Finsupp.single P n) = n • P.toAffinePoint := ...
```

The map is a **group homomorphism** `ProjectiveDivisor → W.Point`.
**Note**: defined on full `ProjectiveDivisor`, not just `Div⁰` — restriction
to `Div⁰` is in T-PIC-A-003.

## Mathlib check
Not in mathlib. Closest: `Finsupp.sum` is the underlying iteration
mechanism we'll use. `AddMonoidHom.finsupp_sum` may simplify the proofs.

## Naming
- `projectiveDivisorSum` (camelCase function)
- `projectiveDivisorSum_zero`, `_add`, `_smul`, `_single` (snake_case)
- Tag `_zero`, `_add`, `_single` with `@[simp]`.

## Generality
- Parametrize by `(F : Type*) [Field F] [DecidableEq F]` (DecidableEq
  needed for `W.Point` to have addition).
- Require `[W.IsElliptic]` so `W.Point` has the group structure.
- Do NOT require `[IsAlgClosed F]` here.

## Proof approach

Use `Finsupp.sum_add_index` for the additivity. The key is the helper
`ProjectiveSmoothPoint.toAffinePoint`:

```lean
/-- Send a `ProjectiveSmoothPoint` to its `Affine.Point` representative:
the point at infinity ↦ `0 : W.Point`, an affine point ⟨x, y, h⟩ ↦
`Point.some x y h`. -/
noncomputable def ProjectiveSmoothPoint.toAffinePoint
    (P : ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) : W.Point :=
  match P with
  | .infinity => 0
  | .affine Q => Q.toAffinePoint  -- the SmoothPoint.toAffinePoint we already have
```

Note: `SmoothPoint.toAffinePoint` is already defined in
`HasseWeil/Curves/PointFunctor.lean`.

## Acceptance criteria

`#print axioms HasseWeil.Curves.projectiveDivisorSum` reports only
`[propext, Classical.choice, Quot.sound]`. Build clean.

## Progress log

- 2026-05-13: Verified T-PIC-A-001 is shipped. `HasseWeil/Curves/PicZero.lean`
  contains `projectiveDivisorSum`, `projectiveDivisorSum_zero/_single/_add`,
  `projectiveDivisorSumHom`, plus the bonus `_neg/_sub/_zsmul` derived from
  the AddMonoidHom bundle. All axiom-clean (`propext, Classical.choice,
  Quot.sound`). Status flipped to DONE.

