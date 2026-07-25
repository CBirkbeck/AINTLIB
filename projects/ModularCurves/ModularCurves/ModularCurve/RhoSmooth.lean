/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.RhoSections
import ModularCurves.Moduli.LegendreSmooth
import ModularCurves.Moduli.BaseChangeIso
import ModularCurves.Moduli.ProductProblem
import ModularCurves.ForMathlib.SmoothDescentScheme

/-!
# The Legendre-anchored ρ-cover is smooth of relative dimension one

**[T-YR-6 carrier]** The free `GL₂`-quotient of the symplectically framed
moduli at the universal Legendre anchor is finite étale over the λ-line, hence
smooth of relative dimension one over `Spec ℚ`. This is the smooth carrier for
the `Y(ρ̄)` smoothness leaf: `Y(ρ̄)` itself receives a finite étale surjective
cover from this scheme (the Legendre-datum forget map), so its smoothness
follows once smoothness descends along finite étale covers (T-YR-6 (c1)).
-/

noncomputable section

namespace ModularCurves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {N : ℕ} [NeZero N]

open scoped FintypeCatDiscrete in
/-- **[T-YR-6 carrier]** The Legendre-anchored ρ-quotient is smooth of relative
dimension one over `Spec ℚ`: finite étale over the λ-line, which is smooth of
relative dimension one. -/
theorem rhoLegendre_carrier_smooth (D : GaloisRepData N) [Fact (1 < N)]
    (hR : IsUnit (2 : (CommRingCat.of ℚ)))
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D)
      (universalLegendreObj (CommRingCat.of ℚ) hR))
    [IsAffineHom d.f] :
    SmoothOfRelativeDimension 1
      (d.σZ.relQuotientStruct d.f d.over_base ≫
        (universalLegendreObj (CommRingCat.of ℚ) hR).structMap) := by
  have hfe := d.σZ.relQuotientStruct_finite_etale_of_free d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D)) d.finite d.etale
  haveI hFin : IsFinite (d.σZ.relQuotientStruct d.f d.over_base) := hfe.1
  haveI hEt : Etale (d.σZ.relQuotientStruct d.f d.over_base) := hfe.2
  haveI h0 : SmoothOfRelativeDimension 0
      (d.σZ.relQuotientStruct d.f d.over_base) := inferInstance
  haveI h1 : SmoothOfRelativeDimension 1
      ((universalLegendreObj (CommRingCat.of ℚ) hR).structMap) :=
    universalLegendreObj_structMap_smooth (CommRingCat.of ℚ) hR
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1)
    (d.σZ.relQuotientStruct d.f d.over_base ≫
      (universalLegendreObj (CommRingCat.of ℚ) hR).structMap))


open scoped FintypeCatDiscrete in
/-- **[T-YR-6-APP (i)]** The ρ-level problem over `ℚ` is represented by an object with
**affine** base: the engine's `D(3)` leg produces one over `ℚ[1/3]`, and `3` is a unit
in `ℚ`, so the base-change isomorphism transports it back. -/
theorem rhoProblem_exists_representableBy_isAffine (D : GaloisRepData N) [Fact (1 < N)]
    (hN : 3 ≤ (N : ℤ)) :
    ∃ Y : EllObj (CommRingCat.of ℚ), IsAffine Y.base ∧
      Nonempty ((rhoProblem D).RepresentableBy Y) := by
  haveI : IsIso (ModuliProblem.awayHomWire (CommRingCat.of ℚ) (3 : CommRingCat.of ℚ)) :=
    isIso_awayHomWire_of_isUnit _ _ (by
      refine isUnit_iff_ne_zero.mpr ?_
      norm_num)
  exact ModuliProblem.exists_representableBy_isAffine_of_isIso _
    (ModuliProblem.exists_representableBy_isAffine_baseChange_three
      (CommRingCat.of ℚ) (rhoProblem D) (rhoProblem_affineOverEll D) (rho_rigidNoeth D hN))

/-- **[T-YR-6-APP (i)]** Every representing object of the ρ-level problem has affine base. -/
theorem rhoProblem_isAffine_base (D : GaloisRepData N) [Fact (1 < N)] (hN : 3 ≤ (N : ℤ))
    {X : EllObj (CommRingCat.of ℚ)} (r : (rhoProblem D).RepresentableBy X) :
    IsAffine X.base :=
  ModuliProblem.isAffine_base_of_representableBy
    (rhoProblem_exists_representableBy_isAffine D hN) r


open scoped FintypeCatDiscrete in
/-- **[T-YR-7, affine conjunct]** The structure map of a representing object of the
ρ-level problem is affine (both source and target are affine schemes). -/
theorem rhoProblem_isAffineHom_structMap (D : GaloisRepData N) [Fact (1 < N)]
    (hN : 3 ≤ (N : ℤ)) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) :
    IsAffineHom X.structMap := by
  haveI := rhoProblem_isAffine_base D hN r
  infer_instance

open scoped FintypeCatDiscrete in
/-- **[T-YR-6-APP S4]** The Legendre-anchored total space (the ρ-relative
representation over the universal Legendre object) has standard-smooth-of-relative-
dimension-one global sections over `ℚ`: it is finite étale over the λ-line, which is
standard smooth of relative dimension one. -/
theorem rhoLegendre_total_isStandardSmooth (D : GaloisRepData N) [Fact (1 < N)]
    (hR : IsUnit (2 : CommRingCat.of ℚ))
    (d : ModuliProblem.RelRepData (rhoProblem D)
      (universalLegendreObj (CommRingCat.of ℚ) hR))
    (hfin : IsFinite d.f) (het : Etale d.f) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((((universalLegendreObj (CommRingCat.of ℚ) hR).pullbackAlong d.f).structMap).appTop).hom := by
  haveI : IsFinite d.f := hfin
  haveI : Etale d.f := het
  haveI : Etale (show d.Z ⟶
      Spec (CommRingCat.of (LegendreModuliRing (CommRingCat.of ℚ))) from d.f) := het
  haveI : IsAffine (universalLegendreObj (CommRingCat.of ℚ) hR).base :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (LegendreModuliRing (CommRingCat.of ℚ)))))
  haveI : IsAffine d.Z := isAffine_of_isAffineHom d.f
  have hφ : RingHom.IsStandardSmoothOfRelativeDimension 1
      (CommRingCat.ofHom (algebraMap (CommRingCat.of ℚ)
        (LegendreModuliRing (CommRingCat.of ℚ)))).hom :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
      (legendreModuliRing_isStandardSmoothOfRelativeDimension (CommRingCat.of ℚ))
  exact isStandardSmoothOfRelativeDimension_appTop_of_etale_over_spec
    (CommRingCat.ofHom (algebraMap (CommRingCat.of ℚ)
      (LegendreModuliRing (CommRingCat.of ℚ)))) d.f hφ

/-- **[T-YR-6-APP S5]** Standard smoothness of the global-sections structure map is
invariant under isomorphism of `Ell`-objects. -/
theorem isStandardSmoothOfRelativeDimension_appTop_of_ellIso {n : ℕ}
    {R : CommRingCat.{0}} {A B : EllObj R} (e : A ≅ B)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (B.structMap.appTop).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n (A.structMap.appTop).hom := by
  haveI : IsIso e.hom.baseHom :=
    ⟨e.inv.baseHom, congrArg EllHom.baseHom e.hom_inv_id,
      congrArg EllHom.baseHom e.inv_hom_id⟩
  have hA : A.structMap = e.hom.baseHom ≫ B.structMap := e.hom.base_w.symm
  haveI : IsIso (e.hom.baseHom.appTop) := by
    refine ⟨e.inv.baseHom.appTop, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_appTop,
        show e.inv.baseHom ≫ e.hom.baseHom = 𝟙 _ from
          congrArg EllHom.baseHom e.inv_hom_id]
      simp
    · rw [← Scheme.Hom.comp_appTop,
        show e.hom.baseHom ≫ e.inv.baseHom = 𝟙 _ from
          congrArg EllHom.baseHom e.hom_inv_id]
      simp
  rw [hA, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1
    (B.structMap.appTop).hom
    (asIso (e.hom.baseHom.appTop)).commRingCatIsoToRingEquiv h

open scoped FintypeCatDiscrete in
/-- **[T-YR-6-APP S3+S5]** The Legendre cover of the representing curve has
standard-smooth-of-relative-dimension-one global sections over `ℚ`: it is isomorphic,
as an `Ell/ℚ`-object, to the Legendre-anchored ρ-total-space. -/
theorem legendreCover_isStandardSmooth (D : GaloisRepData N) [Fact (1 < N)]
    (hR : IsUnit (2 : CommRingCat.of ℚ)) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X)
    (rL : (legendreDeltaProblem (CommRingCat.of ℚ)).RepresentableBy
      (universalLegendreObj (CommRingCat.of ℚ) hR))
    (dL : ModuliProblem.RelRepData (legendreDeltaProblem (CommRingCat.of ℚ)) X)
    (dρ : ModuliProblem.RelRepData (rhoProblem D)
      (universalLegendreObj (CommRingCat.of ℚ) hR))
    (hfin : IsFinite dρ.f) (het : Etale dρ.f) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      (((X.pullbackAlong dL.f).structMap).appTop).hom :=
  isStandardSmoothOfRelativeDimension_appTop_of_ellIso
    (ModuliProblem.prodUniqueUpToIso r dL rL dρ)
    (rhoLegendre_total_isStandardSmooth D hR dρ hfin het)

end ModularCurves

end
