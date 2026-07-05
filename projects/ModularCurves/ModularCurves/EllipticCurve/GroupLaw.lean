import ModularCurves.EllipticCurve.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# The group law on an elliptic curve over a base

An elliptic curve `E/S` (pure geometry: `EllipticCurve.Basic`) carries a unique structure
of commutative group scheme over `S` with identity the zero section. This is a **theorem**
(Abel; KM 2.1.2: the map `E(T) → Pic⁰(E_T/T)`, `P ↦ I(P)⁻¹ ⊗ I(0)`, is an isomorphism of
functors), not part of the definition — all our sources define elliptic curves without
group data.

We register the group structure as construction `DS2` (data-`sorry`): a `GrpObj` structure
on `E` viewed in `Over S` (mathlib's group objects, with the cartesian monoidal structure
on `Over S` via pullbacks). Everything downstream (`[N]`, torsion, level structures)
consumes it through this single registered instance and the specification theorems below
(`grpObj_one_eq_zero`, `grpObj_unique`, `grpObj_comm`), so the bundled data is pinned down
by theorems and cannot drift from the mathematics. Discharge route (ticket chain `T-A6*`):
KM 2.1 — rigidified degree-0 line bundles; the cohomology-and-base-change inputs are
black-box register items (BB-COHBC).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- `E/S` as an object of `Over S`. -/
noncomputable abbrev asOver : Over S := Over.mk E.π

/-- **(DS2, ticket chain T-A6)** The group-scheme structure on an elliptic curve `E/S`:
a group-object structure on `E` in `Over S`.

DATA-SORRY (register entry DS2). Mathematical content (KM 2.1.2, Abel): `E(T)` is in
natural bijection with `Pic⁰(E_T/T)` via `P ↦ I(P)⁻¹ ⊗ I(0)`, transporting the group
structure of the Picard group; the required representability and base-change facts are
the black boxes BB-COHBC of the register (plan.md). -/
noncomputable instance grpObj : GrpObj E.asOver := sorry

/-- **(T-A6a)** Normalisation: the unit of the registered group structure is the zero
section (as morphisms from the underlying scheme of the monoidal unit of `Over S`).
This is part of the *specification* of DS2. -/
theorem grpObj_one_eq_zero :
    (η[E.asOver]).left = (𝟙_ (Over S)).hom ≫ E.zero := by sorry

/-- **(T-A6b, uniqueness — KM 2.1.2 + rigidity)** Any two group-object structures on
`E/S` whose units are the zero section coincide. Consequently DS2 is canonical data.
Source: KM 2.1.2 (uniqueness of the Abel isomorphism); rigidity. -/
theorem grpObj_unique (g₁ g₂ : GrpObj E.asOver)
    (h₁ : (letI := g₁; (η[E.asOver] : _ ⟶ E.asOver)).left = (𝟙_ (Over S)).hom ≫ E.zero)
    (h₂ : (letI := g₂; (η[E.asOver] : _ ⟶ E.asOver)).left = (𝟙_ (Over S)).hom ≫ E.zero) :
    g₁ = g₂ := by sorry

/-- **(T-A6c)** The group law is commutative.
Source: KM 2.1.2 (`Pic⁰` is abelian); alternatively fibrewise rigidity via mathlib's
`AlgebraicGeometry.Group.Abelian`. -/
theorem grpObj_comm : IsCommMonObj E.asOver := by sorry

/-- Multiplication by `n` on `E/S`, as an endomorphism over `S`: the `n`-th power of the
identity in the group `Hom_{Over S}(E, E)` induced by the group-object structure
(mathlib's `MonObj.Hom.group`). Source: KM 2.3 ("the structure of `[N]`"). -/
noncomputable def mulBy (n : ℤ) : E.asOver ⟶ E.asOver :=
  letI : Group (E.asOver ⟶ E.asOver) := Hom.group
  (𝟙 E.asOver) ^ n

/-- The underlying scheme morphism of `mulBy`. -/
noncomputable abbrev mulByHom (n : ℤ) : E.E ⟶ E.E := (E.mulBy n).left

@[simp]
theorem mulByHom_π (n : ℤ) : E.mulByHom n ≫ E.π = E.π :=
  Over.w (E.mulBy n)

/-- The additive commutative group structure on `T`-points `E.Point g`, induced by DS2:
`E.Point g` is definitionally the hom-set `Over.mk g ⟶ E.asOver` (as a subtype), which
carries the group structure of morphisms into a group object; commutativity by
`grpObj_comm`. Registered with DS2 (its compatibility specification
`point_smul_eq_comp_mulBy` is T-A6d). -/
noncomputable instance pointAddCommGroup {T : Scheme.{u}} (g : T ⟶ S) :
    AddCommGroup (E.Point g) := sorry

/-- **(T-A6d, specification)** Scalar multiplication on points is composition with
`mulBy`: `(n • P) = P ≫ [n]`. This ties the point-level group structure (DS2 via
`pointAddCommGroup`) to the morphism `mulBy`, so the two can never diverge. -/
theorem point_smul_eq_comp_mulBy {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) (P : E.Point g) :
    ((n • P : E.Point g) : T ⟶ E.E) = (P : T ⟶ E.E) ≫ E.mulByHom n := by sorry

end EllipticCurve

end ModularCurves
