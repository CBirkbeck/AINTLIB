import ModularCurves.GroupScheme.TranslationAction

/-!
# Translation by a section

Construction support for `[CHARTER-HOPF]` Wave C leaf `[HG-C3a]`
(`.mathlib-quality/decomposition-hopf-c3-cover.md`). For a point `x` of `E` over `S`
(an `Over S`-morphism `𝟙_ (Over S) ⟶ E.asOver`, i.e. a section `S ⟶ E`), translation
`p ↦ p + x` is an automorphism `translateByIso x : E.asOver ≅ E.asOver` of the elliptic
curve over `S`, with inverse translation by `-x`. It is pure group-object algebra: the
maps into the group object `E.asOver` form a commutative group under `Hom.commGroup`, and
`translateBy x = 𝟙 * (const x)` where `const x` is the constant map at `x`. The coset
`x + G` used by the `[HG-C3]` cover is the image of `G` under this automorphism.

## Main definitions
* `EllipticCurve.translateBy` — the endomorphism `p ↦ p + x`.
* `EllipticCurve.translateByIso` — the automorphism, inverse `translateBy (-x)`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The constant endomorphism of `E.asOver` at a point `x` over `S`: `p ↦ x`. -/
noncomputable def constPt (x : 𝟙_ (Over S) ⟶ E.asOver) : E.asOver ⟶ E.asOver :=
  toUnit E.asOver ≫ x

/-- **Translation by a section** `x`, as an endomorphism `p ↦ p + x` of the elliptic curve
over `S`, in hom-group form: the identity times the constant map at `x`. -/
noncomputable def translateBy (x : 𝟙_ (Over S) ⟶ E.asOver) : E.asOver ⟶ E.asOver :=
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  𝟙 E.asOver * E.constPt x

theorem translateBy_def (x : 𝟙_ (Over S) ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.translateBy x = 𝟙 E.asOver * E.constPt x :=
  rfl

/-- The constant map at `x` absorbs precomposition: `f ≫ (const x) = const x` (terminal). -/
theorem comp_constPt (f : E.asOver ⟶ E.asOver) (x : 𝟙_ (Over S) ⟶ E.asOver) :
    f ≫ E.constPt x = E.constPt x := by
  rw [constPt, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (f ≫ toUnit E.asOver) (toUnit E.asOver)]

/-- The constant map is multiplicative in the point: `const (x * y) = const x * const y`. -/
theorem constPt_mul (x y : 𝟙_ (Over S) ⟶ E.asOver) :
    letI : CommGroup (𝟙_ (Over S) ⟶ E.asOver) := Hom.commGroup
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.constPt (x * y) = E.constPt x * E.constPt y := by
  rw [constPt, constPt, constPt, MonObj.comp_mul]

/-- Translating by the zero point is the identity. -/
theorem translateBy_one :
    letI : CommGroup (𝟙_ (Over S) ⟶ E.asOver) := Hom.commGroup
    E.translateBy 1 = 𝟙 E.asOver := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  rw [translateBy, constPt, MonObj.comp_one]
  exact mul_one _

/-- Translating by `x` then by `y` is translating by `x + y` (composition adds the shifts). -/
theorem translateBy_comp (x y : 𝟙_ (Over S) ⟶ E.asOver) :
    letI : CommGroup (𝟙_ (Over S) ⟶ E.asOver) := Hom.commGroup
    E.translateBy x ≫ E.translateBy y = E.translateBy (x * y) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (𝟙_ (Over S) ⟶ E.asOver) := Hom.commGroup
  rw [E.translateBy_def y, MonObj.comp_mul, Category.comp_id, E.comp_constPt,
    E.translateBy_def x, E.translateBy_def (x * y), E.constPt_mul]
  exact mul_assoc _ _ _

/-- **Translation by a section is an automorphism**, with inverse the translation by `-x`. -/
noncomputable def translateByIso (x : 𝟙_ (Over S) ⟶ E.asOver) : E.asOver ≅ E.asOver :=
  letI : CommGroup (𝟙_ (Over S) ⟶ E.asOver) := Hom.commGroup
  { hom := E.translateBy x
    inv := E.translateBy x⁻¹
    hom_inv_id := by rw [E.translateBy_comp, mul_inv_cancel, E.translateBy_one]
    inv_hom_id := by rw [E.translateBy_comp, inv_mul_cancel, E.translateBy_one] }

end EllipticCurve

end ModularCurves
