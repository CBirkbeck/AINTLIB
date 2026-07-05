import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The projective Weierstrass model as a scheme

Mathlib's `WeierstrassCurve R` is an equation (a tuple `a₁, …, a₆`), not a scheme. This file
fixes the interface between that equation-level API and honest schemes: what it means for a
pointed `R`-scheme to *be* the plane projective model
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³` of `W`, with base point `[0:1:0]`.

## Mathematical content

For `W : WeierstrassCurve R` the projective model is the closed subscheme of `ℙ²_R` cut out by
the homogeneous Weierstrass cubic, together with its structure morphism to `Spec R` and the
section at infinity `[0:1:0]`. It is proper, and it is smooth of relative dimension 1 iff `Δ(W)`
is a unit (KM 2.2; Loeffler, *Modular curves*, §3.3, Def 3.3.3; Silverman III.3).

**Construction status.** The model is *declared* here (`projModel`, a registered data-`sorry`,
see the DATA-SORRY REGISTER in `.mathlib-quality/plan.md`) and *characterised* by
`IsWeierstrassModel`; ticket `T-A2` constructs it by gluing the two standard affine charts
(`z = 1` and `y = 1`) along their common localisation, and discharges the characterisation.
No downstream file may use `projModel` except through `IsWeierstrassModel` and the theorems
stated here.

## References

* [KM] Katz–Mazur, *Arithmetic moduli of elliptic curves*, Ch. 2.2.
* [Loe] Loeffler, *Modular curves* lecture notes, §3.3.
* [Sil] Silverman, *AEC* III.3.1 (every pointed smooth genus-1 curve over a field is a
  Weierstrass cubic — the Riemann–Roch input, black-boxed by this project).
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- The `K`-points of an `R`-scheme `X`, for `K` an `R`-algebra: morphisms
`Spec K ⟶ X` over `Spec R`. -/
def SpecPoints (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) (K : Type u) [CommRing K] [Algebra R K] :
    Type u :=
  { g : Spec (.of K) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) }

/-- `IsWeierstrassModel W X f x₀` says that the pointed `R`-scheme `(X, f, x₀)` is *a* plane
projective model of the Weierstrass curve `W`: it is proper, of finite presentation, and for
every `R`-algebra field `K` its `K`-points biject with the mathlib affine-chart points
`(W.baseChange K).toAffine.Point` (which include the point at infinity `0`), naturally in `K`
and sending `x₀` to `0`.

This is the *interface* by which the rest of the library consumes the projective model; the
model itself is constructed in ticket `T-A2`. The point-level bijection plus properness and
smoothness pins the model down uniquely (`isWeierstrassModel_unique`, via KM 2.2.5 —
Riemann–Roch black box). -/
structure IsWeierstrassModel (W : WeierstrassCurve R) (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (x₀ : Spec (.of R) ⟶ X) : Prop where
  isProper : IsProper f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  section_comp : x₀ ≫ f = 𝟙 _
  /-- The `K`-points of `X` over `R` biject with the Weierstrass points over `K`. -/
  points (K : Type u) [Field K] [Algebra R K] :
    Nonempty (SpecPoints X f K ≃ (W.baseChange K).toAffine.Point)

/-- **(T-A2)** The plane projective model of a Weierstrass curve, as a scheme over `Spec R`:
the closed subscheme of `ℙ²_R` defined by the homogeneous Weierstrass cubic.

DATA-SORRY (register entry DS1): to be constructed by gluing the affine charts
`Spec R[x,y]/(W)` (chart `z = 1`) and `Spec R[t,s]/(W_∞)` (chart `y = 1`), following KM 2.2.
Consumers must use only `IsWeierstrassModel` facts about it. -/
noncomputable def projModel (W : WeierstrassCurve R) : Scheme.{u} := sorry

/-- **(T-A2)** The structure morphism of the projective Weierstrass model. -/
noncomputable def projModelπ (W : WeierstrassCurve R) : projModel W ⟶ Spec (.of R) := sorry

/-- **(T-A2)** The section at infinity `[0:1:0]` of the projective Weierstrass model. -/
noncomputable def projModelZero (W : WeierstrassCurve R) : Spec (.of R) ⟶ projModel W := sorry

/-- **(T-A2)** The constructed model satisfies its interface.
Source: KM 2.2; Loeffler §3.3 Def 3.3.3. -/
theorem projModel_isWeierstrassModel (W : WeierstrassCurve R) :
    IsWeierstrassModel W (projModel W) (projModelπ W) (projModelZero W) := by sorry

/-- **(T-A3)** The projective model of an *elliptic* Weierstrass curve (unit discriminant) is
smooth of relative dimension 1 over the base.
Source: Loeffler §3.3 ("If `Δ(α,β) ∈ Γ(S,O_S)ˣ`, this is an elliptic curve over `S`");
KM 2.2.4; Silverman III.1.4(a). -/
theorem projModel_smooth (W : WeierstrassCurve R) [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (projModelπ W) := by sorry

/-- **(T-A4, uniqueness of the model)** Any two pointed `R`-schemes satisfying
`IsWeierstrassModel W` are isomorphic over `Spec R`, compatibly with the base points.
Source: KM 2.2.5 (uniqueness of Weierstrass models; Riemann–Roch black box). -/
theorem isWeierstrassModel_unique (W : WeierstrassCurve R) {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {x₀ : Spec (.of R) ⟶ X} {f' : X' ⟶ Spec (.of R)}
    {x₀' : Spec (.of R) ⟶ X'} (h : IsWeierstrassModel W X f x₀)
    (h' : IsWeierstrassModel W X' f' x₀') :
    ∃ e : X ≅ X', e.hom ≫ f' = f ∧ x₀ ≫ e.hom = x₀' := by sorry

end ModularCurves
