# Silverman III.6.3 — Degree as Quadratic Form Ticket

**Sorry**: `HasseWeil/DegreeQuadraticForm.lean:145` — `degree_quadratic`.

## Goal

Discharge the substantive Silverman III.6.3 statement:
```lean
theorem degree_quadratic
    (α : Isogeny E E) (one_sub_α : Isogeny E E) (r s : ℤ)
    (β : Isogeny E E)
    (hβ_hom : β.toAddMonoidHom = r • α.toAddMonoidHom - s • (AddMonoidHom.id _)) :
    (β.degree : ℤ) =
      (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2
```

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.6.3.

## Mathematical content (3-piece chain)

The theorem reduces via the dual isogeny chain:

### Piece 1: Dual isogeny commutativity (T-III-6-001)

For any endomorphism isogeny α : E → E, there exists a dual α̂ : E → E with:
- α · α̂ = α̂ · α = [deg α] (multiplication-by-degree).
- (rα + sβ)̂ = r·α̂ + s·β̂ (additivity).

### Piece 2: deg = α · α̂ as norm form (T-III-6-005)

For any β = r·α + s·id (or r·α − s·id):
- β · β̂ = (r·α + s·id)(r·α̂ + s·id) = r²·α·α̂ + rs·(α + α̂) + s²
       = r²·deg(α) + rs·tr(α) + s²
- So deg(β) = β·β̂ = the quadratic form value.

### Piece 3: trace formula (III.8 / Silverman Section III.8 trace)

For α with conjugate α̂:
- α + α̂ = [tr(α)]·id at the AddMonoidHom level.
- tr(α) = 1 + deg(α) − deg(1 − α). (= `isogTrace α one_sub_α` definition)

## Existing infrastructure

- `Isogeny.toAlgebra` for the pullback algebra structure.
- `Isogeny.degree` defined as `Module.finrank` of the algebra.
- `IsDualOf` predicate (axiom-clean for q=2/3/5/7 via Worker C's verschiebungIsog).
- `isogSmulSub` placeholder (uses `AlgHom.id` for pullback) — does NOT have the genuine algebra structure for `r·α - s·id`.

## Substantive obstruction: genuine pullback

The placeholder `isogSmulSub α r s` uses `pullback := AlgHom.id`, giving `degree = 1` (Module.finrank K(E) K(E) = 1). For `degree_quadratic` to hold non-trivially, β needs the GENUINE pullback for `r·α − s·id` (the addition-formula pullback, generalizing Worker A's `addPullbackAlgHom_negFrobenius`).

## Mathlib-PR shape

This belongs in `Mathlib.AlgebraicGeometry.EllipticCurve.Isogeny.QuadraticForm` (new file) as:

```lean
/-- Silverman III.6.3 — degree is a positive-definite quadratic form on
    the lattice of endomorphism isogenies. -/
theorem WeierstrassCurve.Affine.degree_quadratic
    {F : Type*} [Field F] [DecidableEq F] {E : Affine F} [E.IsElliptic]
    (α : Isogeny E E) (r s : ℤ)
    (β : Isogeny E E)
    (hβ : ∃ (P : KE →ₐ[F] KE), β.pullback = P ∧
      ∀ Q : E.Point, β.toAddMonoidHom Q = r • α.toAddMonoidHom Q - s • Q) :
    (β.degree : ℤ) = ... := ...
```

The hypothesis `hβ` is what makes the degree well-defined from the point map. Without specifying which pullback corresponds to a given toAddMonoidHom, the degree is not a function of toAddMonoidHom alone.

## Three-step PR plan

1. **`Isogeny.dual` construction** (~200 LOC):
   - Define dual isogeny via the universal property (mathlib has the structure).
   - Prove `α · α̂ = [deg α]` and `α̂ · α = [deg α]`.

2. **`Isogeny.dual_additivity`** (~150 LOC):
   - For β = r·α + s·γ, compute β̂ = r·α̂ + s·γ̂.
   - Requires defining ℤ-module structure on the endomorphism ring.

3. **`degree_quadratic` consumer** (~80 LOC):
   - Compose dual + additivity + trace formula.
   - Direct algebraic computation: β · β̂ = (rα + s·id)(rα̂ + s·id).

## Estimated effort

- **Step 1 (dual construction)**: 5-10 sessions (substantial mathlib content).
- **Step 2 (dual additivity)**: 3-5 sessions.
- **Step 3 (consumer)**: 1-2 sessions once 1-2 land.
- **Mathlib review**: 4-8 weeks per PR.

## Path-not-on-critical-for-bound

The Hasse-Weil bound chain (`hasse_bound_for_finite_field`) takes `degree_quadratic` as a HYPOTHESIS via `h_qf_signed`, not as a proven theorem. Worker C's per-prime IsDualOf certificates supply the per-prime form.

For the universal char-agnostic form, this sorry needs to be discharged via the 3-step PR above. Until then, the bound is parametric on this hypothesis.

This is the same wall as Worker A's `addPullbackAlgHom_negFrobenius` generalization, but at the `Isogeny.dual` abstract level rather than the function-field-pullback level. The two routes are mathematically equivalent but Lean-implementation-wise distinct.
