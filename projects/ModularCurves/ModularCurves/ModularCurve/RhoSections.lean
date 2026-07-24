import ModularCurves.ModularCurve.RhoDescent
import ModularCurves.ModularCurve.RhoPairingBridge

/-!
# [T-EQ-3c] Sections ↔ ρ-structures: the quotient dictionary

The symplectically framed quotient `Z₀` of the full-level moduli times the frame
torsor carves its values by the single map-level condition
`pairEZMap = frameDetMap`. This module turns sections of `Z₀` into ρ-level
structures and back:

* `framedSymp_of_pairEZMap` — the carve condition alone implies the pointwise
  symplectic compatibility `FramedSymp` (via the DS3 keystone
  `muNRoots_correspondence_read` and the determinant-side correspondence reads);
* `rhoLevelStructureOfCarve` — the ρ-dictionary from the carve alone (no separate
  pointwise hypothesis): `hsymp` from `framedSymp_of_pairEZMap`, `hsymp_scheme`
  from `framedPinned_pairing_scheme`;
* (3c) sections of the quotient package give ρ-level structures by cover-lift,
  dictionary application, `GL₂`-orbit agreement (T-EQ-2) and descent (T-EQ-3b);
* (3d) ρ-level structures give sections by étale-local trivialisation and gluing;
* (3e) the two constructions are mutually inverse.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ModularCurves

noncomputable section

variable {N : ℕ} [NeZero N]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3c-i-5]** The pointwise symplectic condition from the carve: the
map-level condition `pairEZMap = frameDetMap` alone implies the geometric-points
symplectic compatibility `FramedSymp`. The Weil-pairing side is the
`torsionPairEval`-read of `t ≫ pairEZMap` (naturality + `torsionPairEval_read`);
the frame side is the determinant-correspondence read of `t ≫ frameDetMap`
through the DS3 keystone (`muNRoots_correspondence_read`) and the two
`qbarPointsRead_map` steps for `detFrameMor`/`detCompMor`. -/
theorem framedSymp_of_pairEZMap (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (P Q : E.Section) (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (hcond : pairEZMap D sT E P Q hP hQ = frameDetMap D h) :
    FramedSymp D sT E P Q hP hQ h hover := by
  intro t ht
  have hmap : torsionPairEval D sT t (EllipticCurve.Point.pull E t P)
      (EllipticCurve.Point.pull E t Q)
      (sectionPull_raw_kill t hP) (sectionPull_raw_kill t hQ) =
      t ≫ frameDetMap D h :=
    (torsionPairEval_comp D sT t P Q
      (EllipticCurve.Point.pull E t P) (EllipticCurve.Point.pull E t Q) rfl rfl
      ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP)
      ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ)
      (sectionPull_raw_kill t hP) (sectionPull_raw_kill t hQ)).trans
      (congrArg (fun (m : T ⟶ muNRootsScheme D) => t ≫ m) hcond)
  have hπ2 : (t ≫ frameDetMap D h) ≫ muNRootsSchemeπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, frameDetMap_π D hover, ht]
  have hreads : muNRootsRead D (t ≫ sT)
      (torsionPairEval D sT t (EllipticCurve.Point.pull E t P)
        (EllipticCurve.Point.pull E t Q)
        (sectionPull_raw_kill t hP) (sectionPull_raw_kill t hQ))
      (torsionPairEval_π D sT t
        (EllipticCurve.Point.pull E t P) (EllipticCurve.Point.pull E t Q)
        (sectionPull_raw_kill t hP) (sectionPull_raw_kill t hQ)) =
      muNRootsRead D
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
        (t ≫ frameDetMap D h) hπ2 :=
    muNRootsRead_congr D ht hmap _
  have hπ3 : (t ≫ h) ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, hover, ht]
  have hπ4 : ((t ≫ h) ≫ corrSpecMap (detFrameMor D)) ≫
      corrSpecπ (cycloUnitsContAction D) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun (m : corrSpec (frameContAction D) ⟶
          Spec (CommRingCat.of ℚ)) => (t ≫ h) ≫ m)
        (corrSpecMap_π (detFrameMor D))).trans hπ3)
  have hsubtype : (⟨t ≫ frameDetMap D h, hπ2⟩ :
      { m : Spec (.of (AlgebraicClosure ℚ)) ⟶ corrSpec (muNRootsContAction D) //
        m ≫ corrSpecπ (muNRootsContAction D) =
          Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) =
      ⟨((t ≫ h) ≫ corrSpecMap (detFrameMor D)) ≫ corrSpecMap (detCompMor D),
        (Category.assoc _ _ _).trans
          ((congrArg (fun (m : corrSpec (cycloUnitsContAction D) ⟶
              Spec (CommRingCat.of ℚ)) =>
              ((t ≫ h) ≫ corrSpecMap (detFrameMor D)) ≫ m)
            (corrSpecMap_π (detCompMor D))).trans hπ4)⟩ := by
    refine Subtype.ext ?_
    show t ≫ h ≫ detFrameScheme D ≫ detCompScheme D = _
    simp only [Category.assoc]
    rfl
  have hdet : qbarPointsRead (muNRootsContAction D) ⟨t ≫ frameDetMap D h, hπ2⟩ =
      D.p (Multiplicative.ofAdd
        (((Matrix.GeneralLinearGroup.det (wFramesPointsEquiv D ⟨t ≫ h, hπ3⟩) :
          (ZMod N)ˣ) : ZMod N))) := by
    refine Eq.trans (congrArg (qbarPointsRead (muNRootsContAction D)) hsubtype) ?_
    refine Eq.trans (qbarPointsRead_map (detCompMor D)
      ⟨(t ≫ h) ≫ corrSpecMap (detFrameMor D), hπ4⟩) ?_
    refine Eq.trans (congrArg (detCompMor D).hom.hom
      (qbarPointsRead_map (detFrameMor D) ⟨t ≫ h, hπ3⟩)) ?_
    rfl
  refine Eq.trans (congrArg
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
    ((torsionPairEval_read D sT t
      (EllipticCurve.Point.pull E t P) (EllipticCurve.Point.pull E t Q)
      (sectionPull_raw_kill t hP) (sectionPull_raw_kill t hQ)).symm.trans
      hreads)) ?_
  refine Eq.trans (muNRoots_correspondence_read D (t ≫ frameDetMap D h) hπ2) ?_
  exact congrArg (fun z : rootsOfUnity N (AlgebraicClosure ℚ) =>
    ((z : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) hdet

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3c-i COMPLETE]** The ρ-dictionary from the carve alone: a full-level
structure and a frame satisfying the single map-level condition
`pairEZMap = frameDetMap` yield a ρ-level structure (pointwise compatibility from
`framedSymp_of_pairEZMap`, morphism-level compatibility from
`framedPinned_pairing_scheme`). -/
noncomputable def rhoLevelStructureOfCarve (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (hcond : pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 = frameDetMap D h) :
    RhoLevelStructure D sT E :=
  rhoLevelStructureOfFramed D sT E hinv L h hover
    (framedSymp_of_pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 h hover hcond)
    (fun t x y hx hy =>
      framedPinned_pairing_scheme D sT hinv L h hover hcond t x y hx hy)

end

end ModularCurves
