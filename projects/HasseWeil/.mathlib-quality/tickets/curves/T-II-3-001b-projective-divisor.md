# T-II-3-001b: Extend Divisor to include the point at infinity

**Status**: DONE (verified axiom-clean 2026-04-22: `ProjectiveSmoothPoint`, `ProjectiveDivisor` depend only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.3 (definition, projective form)
**Module**: `HasseWeil/Curves/ProjectiveDivisor.lean` (new)
**Owner**: worker-K
**Checked out at**: 2026-04-20T17:09Z
**Estimated lines**: 150–300
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-3-001 (`Divisor C`) — REVIEW
- T-II-3-002 (`Divisor.degree`) — REVIEW
- T-II-3-005 (`divisorOf f`) — REVIEW
- Pre-existing `ordAtInfty` in `HasseWeil/Curves/Infinity.lean`

## Blocks
- T-III-3-003 (P ∼ Q ⇒ P = Q) — main motivation
- T-II-3-009 (`deg(div f) = 0`) — Silverman II.3.1(b), the degree-zero fact
  applies to projective divisors, not the affine-only `divisorOf`
- T-III-3-004 (Pic⁰(E) ≅ E) — the Silverman proof uses projective divisors
- All downstream Pic⁰-based tickets

## Statement

The project's `Divisor C = C.SmoothPoint →₀ ℤ` supports only affine smooth
points. Silverman's divisors are projective: they also include the place at
infinity (which for a Weierstrass curve `C` is the single point `[0:1:0]`
with valuation `ordAtInfty`).

Extend the divisor framework to handle the infinity place so that
`projectiveDivisorOf f` captures **all** zeros and poles of `f ∈ F(C)*`,
including any pole or zero at infinity.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A place on the projective closure: either an affine smooth point, or the
place at infinity. Reference: Silverman II.3, projective form. -/
inductive ProjectiveSmoothPoint (C : SmoothPlaneCurve F) : Type _
  | affine (P : C.SmoothPoint) : ProjectiveSmoothPoint C
  | infinity : ProjectiveSmoothPoint C

/-- A **projective divisor** on `C`: a formal ℤ-linear sum of places. -/
abbrev ProjectiveDivisor (C : SmoothPlaneCurve F) : Type _ :=
  C.ProjectiveSmoothPoint →₀ ℤ

namespace ProjectiveDivisor

variable {C : SmoothPlaneCurve F}

/-- Degree = sum of coefficients. -/
def degree (D : ProjectiveDivisor C) : ℤ := ...

@[simp] theorem degree_zero : degree (0 : ProjectiveDivisor C) = 0
@[simp] theorem degree_add (D₁ D₂ : ProjectiveDivisor C) :
    (D₁ + D₂).degree = D₁.degree + D₂.degree

def degreeHom (C : SmoothPlaneCurve F) : ProjectiveDivisor C →+ ℤ := ...

end ProjectiveDivisor

/-- The projective divisor of a nonzero rational function on `C`:
`projectiveDivisorOf f = Σ_P ord_P(f) · (P) + ordAtInfty(f) · (∞)`.
Reference: Silverman II.3 (projective form). -/
noncomputable def SmoothPlaneCurve.projectiveDivisorOf
    (C : SmoothPlaneCurve F) (f : C.FunctionField) :
    ProjectiveDivisor C := ...

/-- Multiplicativity on nonzero inputs. -/
theorem SmoothPlaneCurve.projectiveDivisorOf_mul (C : SmoothPlaneCurve F)
    {f g : C.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    C.projectiveDivisorOf (f * g) =
      C.projectiveDivisorOf f + C.projectiveDivisorOf g

end HasseWeil.Curves
```

Plus: principal subgroup, linear equivalence, `Pic`, `Pic⁰` lifted to the
projective setting (API mirroring `Divisors.lean`).

## Optional (overlaps T-II-3-009)

```lean
/-- Silverman II.3.1(b): the projective divisor of a nonzero rational function
has degree zero. -/
theorem SmoothPlaneCurve.projectiveDivisorOf_degree_zero
    (C : SmoothPlaneCurve F) {f : C.FunctionField} (hf : f ≠ 0) :
    (C.projectiveDivisorOf f).degree = 0
```

If `projectiveDivisorOf_degree_zero` proves to be tractable in-line with
this ticket (using the algebra-norm / `intDegree` chain already set up in
`Infinity.lean`), close T-II-3-009 here as well. Otherwise, leave
T-II-3-009 as the dedicated ticket and this sub-ticket delivers only the
type/API.

## Notes

- One point at ∞ is correct for a Weierstrass plane curve (projective closure
  of `y² = x³ + ax + b` has `[0:1:0]` as its unique infinity point). For
  more general smooth plane curves, the number of infinity places can be
  larger, but that is out of scope here.
- `ordAtInfty_coordX = -2`, `ordAtInfty_coordY = -3` (from `Infinity.lean`)
  should become `projectiveDivisorOf`-level facts once the type is in place.

## Progress log

- **2026-04-20T17:09Z** [worker-K] created (spun out from T-III-3-003 scope
  audit).
- **2026-04-20T17:30Z** [worker-K] Delivered `HasseWeil/Curves/ProjectiveDivisor.lean`
  (300 lines, axiom-clean):
  - `ProjectiveSmoothPoint C` inductive (`affine P` | `infinity`).
  - `ProjectiveDivisor C := ProjectiveSmoothPoint C →₀ ℤ`.
  - `ProjectiveDivisor.{degree, degreeHom, degZero, mem_degZero}` + simp API.
  - `Divisor.toProjective` embedding + `degree_toProjective`.
  - `SmoothPlaneCurve.projectiveDivisorOf f` = affine `divisorOf` + ∞ place
    with `ordAtInfty f` coefficient.
  - `projectiveDivisorOf_{zero, one, mul, inv, apply_affine, apply_infinity}`.
  - `ProjIsPrincipal`, `ProjLinearlyEquiv` (refl/symm/trans) and
    `projPrincipalSubgroup`.
  - `PicProj`, `PicProj₀` abbrevs.
  - All declarations axiom-clean (propext, Classical.choice, Quot.sound only).

  Status: REVIEW (type + API delivered; `projectiveDivisorOf_degree_zero`
  (II.3.1(b)) deliberately deferred — it is the substantial Silverman
  theorem and properly belongs to **T-II-3-009**; this ticket delivers the
  type-theoretic scaffolding only).
