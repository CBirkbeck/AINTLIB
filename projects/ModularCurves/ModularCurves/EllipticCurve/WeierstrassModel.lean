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
`IsWeierstrassModel`; ticket `T-A2` constructs it by Hida's route of record
(decomposition-gme2 A7.e): `Proj (R[X,Y,Z]/(Weierstrass cubic))`, smoothness by the
chartwise Jacobian analysis (GME pp. 114–115), and discharges the characterisation.
No downstream file may use `projModel` except through `IsWeierstrassModel`, the theorems
stated here, and the fibrewise bridge `FibrewiseElliptic` (sanctioned raw-iso consumer,
expert review Q2).

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

/-- `IsWeierstrassModel W X f x₀` says that the pointed `R`-scheme `(X, f, x₀)` is *a*
plane projective model of the Weierstrass curve `W`: proper, of finite presentation,
with a section, and — **when `W` is elliptic** — its `K`-points over every `R`-algebra
field `K` biject with the Weierstrass points `(W.baseChange K).toAffine.Point`,
POINTEDLY (`x₀ ↦ 0`).

ADVERSARIAL FIX (2026-07-05, DEF-7): the points clause is (i) guarded by
`W.IsElliptic` — mathlib's `Affine.Point` contains only NONSINGULAR points, so for
singular `W` the honest projective cubic has strictly more `K`-points (cuspidal
`y² = x³` over `𝔽₅`: 6 vs 5) and the unguarded clause was false of the registered
model; and (ii) pointed — the bare `Nonempty (≃)` form did not tie `x₀` to `0` and
pinned nothing. Field-points cannot detect nilpotents, so this interface alone can
NEVER pin the model up to isomorphism (thickening counterexample `V(F)` vs `V(F²)`);
uniqueness additionally requires smoothness — see `isWeierstrassModel_unique`. -/
structure IsWeierstrassModel (W : WeierstrassCurve R) (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (x₀ : Spec (.of R) ⟶ X) : Prop where
  isProper : IsProper f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  section_comp : x₀ ≫ f = 𝟙 _
  /-- Pointed `K`-points comparison, for elliptic `W`. -/
  points : ∀ (_ : W.IsElliptic) (K : Type u) [Field K] [Algebra R K],
    ∃ e : SpecPoints X f K ≃ (W.baseChange K).toAffine.Point,
      e ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x₀, by
        rw [Category.assoc, section_comp, Category.comp_id]⟩ = 0

/-- **(T-A2)** The plane projective model of a Weierstrass curve, as a scheme over `Spec R`:
the closed subscheme of `ℙ²_R` defined by the homogeneous Weierstrass cubic.

DATA-SORRY (register entry DS1). Route of record (decomposition-gme2 A7.e, adopted
2026-07-05, superseding the two-chart gluing sketch): Hida's construction —
`Proj (R[X,Y,Z]/(Weierstrass cubic))` with `0 = (0,1,0)`, smoothness via the
eight-equivalent-conditions chartwise Jacobian analysis (GME pp. 114–115).
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

/-- **(T-A4, uniqueness of the model — KM 2.2.5 scope)** For **elliptic** `W`, any two
pointed **smooth** models satisfying `IsWeierstrassModel W` are isomorphic over
`Spec R`, compatibly with the base points.

ADVERSARIAL FIX (2026-07-05, DEF-7): ellipticity and smoothness hypotheses are
REQUIRED — without them `V(F)` and its first-order thickening `V(F²)` both satisfy
the field-points interface (reduced `Spec K` cannot see nilpotents) yet are not
isomorphic; KM 2.2.5's uniqueness is among smooth pointed models of an elliptic
curve, and the previous unconditional statement was strictly stronger than the
source and false. Source: KM 2.2.5 ⧗ (Riemann–Roch black box; Hida GME §2.2.6
"Moduli of Weierstrass Type" as interim proof-bearing source). -/
theorem isWeierstrassModel_unique (W : WeierstrassCurve R) [W.IsElliptic]
    {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {x₀ : Spec (.of R) ⟶ X} {f' : X' ⟶ Spec (.of R)}
    {x₀' : Spec (.of R) ⟶ X'}
    (hs : SmoothOfRelativeDimension 1 f) (hs' : SmoothOfRelativeDimension 1 f')
    (h : IsWeierstrassModel W X f x₀)
    (h' : IsWeierstrassModel W X' f' x₀') :
    ∃ e : X ≅ X', e.hom ≫ f' = f ∧ x₀ ≫ e.hom = x₀' := by sorry

end ModularCurves
