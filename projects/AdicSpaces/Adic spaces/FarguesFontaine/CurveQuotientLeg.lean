/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveVMorphism
import «Adic spaces».FarguesFontaine.CurveAdicPresentation
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# The quotient leg is an open immersion (Campaign 9, P5-5d)

On a *wandering* open `V` of `𝒴` — one all of whose Frobenius translates miss it
— the projection `𝒴|_V ⟶ X` is an open immersion of presheafed spaces: an open
embedding on carriers, and an isomorphism on sections over every open of the
image.  The section half is P5-5c (`curveSectionEquiv` with both directions
continuous); this file adds the carrier half and the bookkeeping that identifies
the `c`-map with the section comparison, then reads off

    `quotientLegIsoRestrict : 𝒴|_V ≅ X|_{π V}`

via mathlib's `IsOpenImmersion.isoRestrict`.  This is the chart form of the
Fargues–Fontaine presentation `X = 𝒴 / φ^ℤ`.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology
  Filter CategoryTheory Opposite Pointwise

open scoped AlgebraicGeometry

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-! ### (a) the base of the quotient leg is an open embedding -/

theorem yRestrictToCurve_base_apply (V : Opens ↥(yTop p F ϖ)) (v : ↥V) :
    ConcreteCategory.hom (yRestrictToCurve p F ϖ V).toHom.base v
      = yTopToCurve p F ϖ v.1 := rfl

theorem yRestrictToCurve_base_isOpenEmbedding (V : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    Topology.IsOpenEmbedding (yRestrictToCurve p F ϖ V).toHom.base := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact (continuous_yTopToCurve p F ϖ).comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (yTopToCurve_injOn_of_disjoint_translates p F ϖ hdis
      a.2 b.2 hab)
  · exact (isOpenQuotientMap_yTopToCurve p F ϖ).isOpenMap.comp
      (V.2.isOpenEmbedding_subtypeVal.isOpenMap)


/-! ### (b) bookkeeping: the image open, wandering descent, the slice -/

/-- The `𝒴`-image of an open of the restricted carrier sits inside `V`. -/
theorem restrictOpenFunctor_obj_le (V : Opens ↥(yTop p F ϖ)) (U : Opens ↥V) :
    (ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U ≤ V := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- **The open-immersion functor image is the curve image of the `𝒴`-image.** -/
theorem base_functor_obj_eq (V : Opens ↥(yTop p F ϖ))
    (hb : Topology.IsOpenEmbedding (yRestrictToCurve p F ϖ V).toHom.base)
    (U : Opens ↥V) :
    hb.functor.obj U
      = xImage p F ϖ
        ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U) := by
  refine Opens.ext (Set.ext fun x => ⟨?_, ?_⟩)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- **Wandering descends to smaller opens.** -/
theorem disjoint_translates_mono {V W : Opens ↥(yTop p F ϖ)} (hW : W ≤ V)
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) := by
  intro k hk
  refine (hdis k hk).mono ?_ ?_
  · exact fun z hz => hW (hz : yFrobTop p F ϖ k z ∈ W)
  · exact fun z hz => hW hz

/-- **The slice collapses**: inside a wandering `V`, the saturated preimage of the
image of a subopen `W` meets `V` in exactly `W`. -/
theorem inf_curvePreimage_xImage (V W : Opens ↥(yTop p F ϖ)) (hW : W ≤ V)
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    V ⊓ curvePreimage p F ϖ (xImage p F ϖ W) = W := by
  refine le_antisymm ?_ (le_inf hW (le_curvePreimage_xImage p F ϖ W))
  rintro y ⟨hyV, hysat⟩
  have hysat' : y ∈ (⨆ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W
      : Opens ↥(yTop p F ϖ)) := by
    rw [← curvePreimage_xImage p F ϖ W]
    exact hysat
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hysat'
  rcases eq_or_ne k 0 with rfl | hk0
  · have : yFrobTop p F ϖ 0 y ∈ W := hk
    rwa [yFrobTop_zero p F ϖ y] at this
  · exact absurd hyV (Set.disjoint_left.mp (hdis k hk0)
      (show yFrobTop p F ϖ k y ∈ V from hW hk))


/-! ### (b) the section comparison as an isomorphism of complete topological rings -/

/-- **The section comparison of the quotient leg, as an isomorphism in
`CompleteTopCommRingCat`** — the bijection of `curveSectionEquiv` upgraded by the
continuity of both directions. -/
noncomputable def curveSectionCatIso (W : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    CompleteTopCommRingCat.of ↥(frobFixed p F ϖ (xImage p F ϖ W))
      ≅ CompleteTopCommRingCat.of ↥(limitSections ((yFunctor p F ϖ).obj W)) where
  hom := ⟨(curveSectionEquiv p F ϖ W hdis).toRingHom,
    curveSectionRestrict_continuous p F ϖ W⟩
  inv := ⟨(curveSectionEquiv p F ϖ W hdis).symm.toRingHom,
    curveSectionEquiv_symm_continuous p F ϖ W hdis⟩
  hom_inv_id := Subtype.ext (RingHom.ext fun x =>
    (curveSectionEquiv p F ϖ W hdis).symm_apply_apply x)
  inv_hom_id := Subtype.ext (RingHom.ext fun x =>
    (curveSectionEquiv p F ϖ W hdis).apply_symm_apply x)


/-- **From the section formula to invertibility**: a map out of the invariant
sections over `xImage W` that computes as "underlying section, restricted along
`Z ≤ π⁻¹ (xImage W)`" is an isomorphism as soon as `Z = W` and `W` is
wandering. -/
theorem isIso_of_eq_curveSectionRestrict (W : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))
    (Z : Opens ↥(yTop p F ϖ)) (hZ : Z = W)
    (hle : (yFunctor p F ϖ).obj Z
      ≤ (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))
    (g : CompleteTopCommRingCat.of ↥(frobFixed p F ϖ (xImage p F ϖ W))
      ⟶ CompleteTopCommRingCat.of ↥(limitSections ((yFunctor p F ϖ).obj Z)))
    (hg : ∀ t, g.1 t
      = limitRestrict hle (piComponent p F ϖ (xImage p F ϖ W) t)) :
    IsIso g := by
  subst hZ
  have hgeq : g = (curveSectionCatIso p F ϖ Z hdis).hom :=
    Subtype.ext (RingHom.ext fun t => hg t)
  rw [hgeq]
  infer_instance


/-! ### The quotient leg is an open immersion -/

/-- **The quotient leg of the adic Fargues–Fontaine curve is an open immersion**
of presheafed spaces: on a wandering open `V` of `𝒴` the projection
`𝒴|_V ⟶ X` is an open embedding on carriers and an isomorphism on sections
over every open of the image. -/
theorem yRestrictToCurve_isOpenImmersion (V : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
      (yRestrictToCurve p F ϖ V).toHom :=
  { base_open := yRestrictToCurve_base_isOpenEmbedding p F ϖ V hdis
    c_iso := fun U => by
      have hU'le : (ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U
          ≤ V := restrictOpenFunctor_obj_le p F ϖ V U
      have hobj : (yRestrictToCurve_base_isOpenEmbedding p F ϖ V hdis).functor.obj U
          = xImage p F ϖ
            ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U) :=
        base_functor_obj_eq p F ϖ V _ U
      rw [hobj]
      refine isIso_of_eq_curveSectionRestrict p F ϖ
        ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U)
        (disjoint_translates_mono p F ϖ hU'le hdis)
        ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj
          ((Opens.map (yRestrictToCurve p F ϖ V).toHom.base).obj
            (xImage p F ϖ
              ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U))))
        ?_
        (leOfHom ((yFunctor p F ϖ).map (homOfLE (legOpen_le_curvePreimage p F ϖ
          (xImage p F ϖ
            ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U)) V))))
        _
        (yRestrictToCurve_c_app_apply p F ϖ
          (xImage p F ϖ
            ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U)) V)
      rw [legOpen_eq p F ϖ
        (xImage p F ϖ
          ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U)) V]
      exact inf_curvePreimage_xImage p F ϖ V
        ((ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj U)
        hU'le hdis }


/-- **`𝒴|_V` is isomorphic, as a presheafed space, to the restriction of the
curve to the open image `π V`** — mathlib's `isoRestrict` at the quotient leg.
This is the chart form of the Fargues–Fontaine presentation `X = 𝒴 / φ^ℤ`. -/
noncomputable def quotientLegIsoRestrict (V : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    ((yVPreObj p F ϖ).restrictOpen V).toPresheafedSpace
      ≅ (xVPreObj p F ϖ).toPresheafedSpace.restrict
          (yRestrictToCurve_base_isOpenEmbedding p F ϖ V hdis) :=
  letI := yRestrictToCurve_isOpenImmersion p F ϖ V hdis
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict
    (yRestrictToCurve p F ϖ V).toHom


/-- The range of the quotient leg is exactly the open image. -/
theorem range_yRestrictToCurve_eq (V : Opens ↥(yTop p F ϖ)) :
    Set.range (ConcreteCategory.hom (yRestrictToCurve p F ϖ V).toHom.base)
      = ((xImage p F ϖ V : Opens (Curve p F ϖ)) : Set (Curve p F ϖ)) := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v.1, v.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- **The quotient leg in `restrictOpen` form** — the shape Wedhorn 8.22 needs:
`𝒴|_V ≅ X|_{π V}` with both sides written as restrictions of the `𝒱^pre`-objects
to named opens. -/
noncomputable def quotientLegIsoRestrictOpen (V : Opens ↥(yTop p F ϖ))
    (hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    ((yVPreObj p F ϖ).restrictOpen V).toPresheafedSpace
      ≅ (xVPreObj p F ϖ).toPresheafedSpace.restrict
          (ValuationSpectrum.openIncl_isOpenEmbedding
            (X := (xVPreObj p F ϖ).toPresheafedSpace) (xImage p F ϖ V)) :=
  letI := yRestrictToCurve_isOpenImmersion p F ϖ V hdis
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (f := (yRestrictToCurve p F ϖ V).toHom)
    (g := (xVPreObj p F ϖ).toPresheafedSpace.ofRestrict
      (ValuationSpectrum.openIncl_isOpenEmbedding
        (X := (xVPreObj p F ϖ).toPresheafedSpace) (xImage p F ϖ V)))
    ((range_yRestrictToCurve_eq p F ϖ V).trans Subtype.range_val.symm)


/-! ### The quotient leg as an isomorphism of `𝒱` (P5-5, the headline)

`quotientLegVPreHom` (P5-5b) and `quotientLegIsoRestrictOpen` have the SAME
underlying morphism — both are mathlib's `IsOpenImmersion.lift` — so the
`𝒱^pre`-morphism is invertible, and `VPreHom.asIso` promotes it. -/

variable (V : Opens ↥(yTop p F ϖ))
  (hdis : ∀ k : ℤ, k ≠ 0 →
    Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
        : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
      ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))

/-- The quotient leg's `𝒱^pre`-morphism and the open-immersion isomorphism have
the same underlying map (both are mathlib's `IsOpenImmersion.lift`). -/
theorem quotientLegVPreHom_toHom_eq :
    (quotientLegVPreHom p F ϖ V).toHom
      = (quotientLegIsoRestrictOpen p F ϖ V hdis).hom := rfl

include hdis in
theorem isIso_quotientLegVPreHom_toHom :
    IsIso (quotientLegVPreHom p F ϖ V).toHom := by
  rw [quotientLegVPreHom_toHom_eq p F ϖ V hdis]
  exact (quotientLegIsoRestrictOpen p F ϖ V hdis).isIso_hom

include hdis in
/-- **THE QUOTIENT LEG IS AN ISOMORPHISM OF `𝒱^pre`** (P5-5): for a wandering
open `V` of `𝒴`, the projection induces `𝒴|_V ≅ X|_{π V}` in Wedhorn's category
— carrying the structure sheaf, the stalk local rings and the stalk valuations,
not merely the topology. -/
noncomputable def quotientLegVIso :
    (yVPreObj p F ϖ).restrictOpen V
      ≅ (xVPreObj p F ϖ).restrictOpen (xImage p F ϖ V) :=
  letI := isIso_quotientLegVPreHom_toHom p F ϖ V hdis
  ValuationSpectrum.VPreHom.asIso (quotientLegVPreHom p F ϖ V)

include hdis in
/-- **The quotient leg as an isomorphism of `𝒱`** (both sides are sheafy). -/
noncomputable def quotientLegVObjIso :
    (yVObj p F ϖ).restrictOpen V
      ≅ (xVObj p F ϖ).restrictOpen (xImage p F ϖ V) :=
  ValuationSpectrum.VObj.isoOfVPreIso (quotientLegVIso p F ϖ V hdis)

end FarguesFontaine

end
