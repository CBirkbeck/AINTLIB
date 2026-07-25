import ModularCurves.ModularCurve.RhoDescent
import ModularCurves.ModularCurve.RhoPairingBridge
import Mathlib.AlgebraicGeometry.Sites.Fpqc

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

/-- **[T-EQ-3c-L1]** The trivialisation map is natural in the curve: the
constant-scheme base-change comparison followed by the level map upstairs is the
pulled level map followed by the torsion comparison. Stated against an arbitrary
level `L'` downstairs whose sections are the pulled sections, so any spelling of
the transported value applies. -/
theorem fullLevelHom_mapAlong {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (L : B.curve.FullLevelPt N) (L' : A.curve.FullLevelPt N)
    (hP : L'.1.1 = EllHom.pullSection (CommRingCat.of ℚ) g L.1.1)
    (hQ : L'.1.2 = EllHom.pullSection (CommRingCat.of ℚ) g L.1.2) :
    constSchemeMapAlong g.baseHom (Fin 2 → ZMod N) ≫ B.curve.fullLevelHom L =
      A.curve.fullLevelHom L' ≫ torsionMapOfEllHom g N := by
  refine Sigma.hom_ext _ _ fun v => ?_
  have hcomb : ((v 0).val : ℤ) • L'.1.1 + ((v 1).val : ℤ) • L'.1.2 =
      EllHom.pullSection (CommRingCat.of ℚ) g
        (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2) := by
    rw [hP, hQ, EllHom.pullSection_add, EllHom.pullSection_zsmul,
      EllHom.pullSection_zsmul]
  have hval : (EllHom.mapPoint g (𝟙 A.base)
      (((v 0).val : ℤ) • L'.1.1 + ((v 1).val : ℤ) • L'.1.2)).1 =
      g.baseHom ≫ (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2).1 := by
    refine (EllHom.mapPoint_coe g _ _).trans ?_
    rw [hcomb]
    exact g.isPullback.lift_fst _ _ _
  rw [← Category.assoc, ι_constSchemeMapAlong, Category.assoc]
  rw [show B.curve.fullLevelHom L = Limits.Sigma.desc fun w : Fin 2 → ZMod N =>
      B.curve.pointToTorsion
        (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
        ((B.curve.smul_eq_zero_iff_comp_mulByHom _ N _).mp (by
          rw [smul_add, smul_comm (N : ℤ) ((w 0).val : ℤ),
            smul_comm (N : ℤ) ((w 1).val : ℤ), L.2.1.1, L.2.1.2, smul_zero,
            smul_zero, add_zero])) from rfl]
  rw [show A.curve.fullLevelHom L' = Limits.Sigma.desc fun w : Fin 2 → ZMod N =>
      A.curve.pointToTorsion
        (((w 0).val : ℤ) • L'.1.1 + ((w 1).val : ℤ) • L'.1.2)
        ((A.curve.smul_eq_zero_iff_comp_mulByHom _ N _).mp (by
          rw [smul_add, smul_comm (N : ℤ) ((w 0).val : ℤ),
            smul_comm (N : ℤ) ((w 1).val : ℤ), L'.2.1.1, L'.2.1.2, smul_zero,
            smul_zero, add_zero])) from rfl]
  rw [Limits.Sigma.ι_desc, ← Category.assoc, Limits.Sigma.ι_desc]
  refine Eq.trans ?_ (pointToTorsion_mapPoint g _ _).symm
  exact (pointToTorsion_comp g.baseHom _ _ hval _ _).symm

/-- **[T-EQ-3c-L2f]** Functoriality of the constant-scheme comparison. -/
@[reassoc]
theorem constSchemeMapAlong_comp {T₁ T₂ T₃ : Scheme.{0}} (k₁ : T₁ ⟶ T₂)
    (k₂ : T₂ ⟶ T₃) (A : Type) [Finite A] :
    constSchemeMapAlong k₁ A ≫ constSchemeMapAlong k₂ A =
      constSchemeMapAlong (k₁ ≫ k₂) A := by
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, ι_constSchemeMapAlong, Category.assoc,
    ι_constSchemeMapAlong, ι_constSchemeMapAlong, ← Category.assoc]

/-- **[T-EQ-3c-L2]** The coordinate map of a pinned framed trivialization: the
`V_ρ`-component of the pinned iso. All the `3c` invariance and descent arguments
run through this composite (the `snd`-leg is just `torsionπ`). -/
noncomputable def framedCoordMap (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) :
    E.torsion N ⟶ vRho D :=
  (framedTorsionIsoPinned D sT E hinv L h hover).hom ≫ pullback.fst (vRhoπ D) sT

/-- **[T-EQ-3c-L2 mid]** The constant-side chain of the pinned iso is natural in
the base. -/
theorem pinnedMidChain_mapAlong {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B) :
    constSchemeMapAlong g.baseHom (Fin 2 → ZMod N) ≫
      ((isPullback_constSchemeMapAlong B.structMap
          (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
        pullback.map B.structMap
          (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) B.structMap
          (constVecSchemeπ N) (𝟙 B.base) (constVecSchemeIso N).hom
          (𝟙 (Spec (.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
        pullback.map B.structMap (constVecSchemeπ N) B.structMap
          (constVecSchemeπ N) (𝟙 B.base) (corrSchemeIso N).hom
          (𝟙 (Spec (.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm)) =
      ((isPullback_constSchemeMapAlong A.structMap
          (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
        pullback.map A.structMap
          (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) A.structMap
          (constVecSchemeπ N) (𝟙 A.base) (constVecSchemeIso N).hom
          (𝟙 (Spec (.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
        pullback.map A.structMap (constVecSchemeπ N) A.structMap
          (constVecSchemeπ N) (𝟙 A.base) (corrSchemeIso N).hom
          (𝟙 (Spec (.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm)) ≫
      pullback.map A.structMap (constVecSchemeπ N) B.structMap
        (constVecSchemeπ N) g.baseHom (𝟙 _) (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id]; exact g.base_w.symm)
        (by rw [Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.comp_id, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_fst_assoc, constSchemeMapAlong_π]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.comp_id, IsPullback.isoPullback_hom_snd_assoc]
    rw [constSchemeMapAlong_comp_assoc, g.base_w]

/-- **[T-EQ-3c-L2 slice]** The frame-evaluation slice is natural in the base. -/
theorem frameEvalSlice_mapAlong (D : GaloisRepData N)
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (hB : B.base ⟶ wFrames D) (hoverB : hB ≫ wFramesπ D = B.structMap) :
    pullback.map A.structMap (constVecSchemeπ N) B.structMap
        (constVecSchemeπ N) g.baseHom (𝟙 _) (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id]; exact g.base_w.symm)
        (by rw [Category.comp_id, Category.id_comp]) ≫
      frameEvalSlice D B.structMap hB hoverB =
    frameEvalSlice D A.structMap (g.baseHom ≫ hB)
        (by rw [Category.assoc, hoverB, g.base_w]) ≫
      pullback.map (vRhoπ D) A.structMap (vRhoπ D) B.structMap
        (𝟙 (vRho D)) g.baseHom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact g.base_w.symm) := by
  have hinner : pullback.map A.structMap (constVecSchemeπ N) B.structMap
      (constVecSchemeπ N) g.baseHom (𝟙 _) (𝟙 (Spec (.of ℚ)))
      (by rw [Category.comp_id]; exact g.base_w.symm)
      (by rw [Category.comp_id, Category.id_comp]) ≫
      pullback.lift (pullback.snd B.structMap (constVecSchemeπ N))
        (pullback.fst B.structMap (constVecSchemeπ N) ≫ hB)
        (by rw [Category.assoc, hoverB, ← pullback.condition]) =
      pullback.lift (pullback.snd A.structMap (constVecSchemeπ N))
        (pullback.fst A.structMap (constVecSchemeπ N) ≫ g.baseHom ≫ hB)
        (by
          simp only [Category.assoc]
          rw [hoverB, show g.baseHom ≫ B.structMap = A.structMap from g.base_w,
            pullback.condition]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc]
  apply pullback.hom_ext
  · simp only [Category.assoc, frameEvalSlice_fst, pullback.lift_fst,
      Category.comp_id]
    rw [← Category.assoc]
    exact congrArg (· ≫ frameEval D) hinner
  · simp only [Category.assoc, frameEvalSlice_snd, frameEvalSlice_snd_assoc,
      pullback.lift_fst, pullback.lift_snd]

/-- **[T-EQ-3c-L2]** Base-change naturality of the coordinate map: the torsion
comparison followed by the coordinate map upstairs is the coordinate map of the
pulled data. -/
theorem framedCoordMap_mapAlong (D : GaloisRepData N)
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (hinvA : NIsInvertible A.base N) (hinvB : NIsInvertible B.base N)
    (L : B.curve.FullLevelPt N) (L' : A.curve.FullLevelPt N)
    (hP : L'.1.1 = EllHom.pullSection (CommRingCat.of ℚ) g L.1.1)
    (hQ : L'.1.2 = EllHom.pullSection (CommRingCat.of ℚ) g L.1.2)
    (hB : B.base ⟶ wFrames D) (hoverB : hB ≫ wFramesπ D = B.structMap) :
    torsionMapOfEllHom g N ≫
        framedCoordMap D B.structMap B.curve hinvB L hB hoverB =
      framedCoordMap D A.structMap A.curve hinvA L' (g.baseHom ≫ hB)
        (by rw [Category.assoc, hoverB, g.base_w]) := by
  rw [← cancel_epi (A.curve.fullLevelIso hinvA L').hom]
  rw [framedCoordMap, framedCoordMap, framedTorsionIsoPinned,
    framedTorsionIsoPinned]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [Iso.hom_inv_id_assoc]
  rw [← Category.assoc (A.curve.fullLevelIso hinvA L').hom
    (torsionMapOfEllHom g N)]
  rw [show (A.curve.fullLevelIso hinvA L').hom ≫ torsionMapOfEllHom g N =
    constSchemeMapAlong g.baseHom (Fin 2 → ZMod N) ≫
      (B.curve.fullLevelIso hinvB L).hom from
    (fullLevelHom_mapAlong g L L' hP hQ).symm]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc]
  rw [reassoc_of% (pinnedMidChain_mapAlong g)]
  rw [reassoc_of% (frameEvalSlice_mapAlong D g hB hoverB)]
  simp only [pullback.lift_fst, Category.comp_id]

/-- **[T-EQ-3c-L2]** `γ`-invariance of the coordinate map (the `fst`-leg shadow of
`framedTorsionIsoPinned_glSmul`). -/
theorem framedCoordMap_glSmul (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    framedCoordMap D sT E hinv (E.glSmul γ L) (h ≫ wFramesRightMul D γ)
        (by rw [Category.assoc, wFramesRightMul_π, hover]) =
      framedCoordMap D sT E hinv L h hover :=
  congrArg (fun (m : E.torsion N ≅ pullback (vRhoπ D) sT) =>
    m.hom ≫ pullback.fst (vRhoπ D) sT)
    (framedTorsionIsoPinned_glSmul D sT E hinv L h hover γ)

/-- **[T-EQ-3c-L3a]** The `Ell/ℚ` comparison between base changes of `X` along any
morphism intertwining the base maps (generalizes `EllObj.pullbackAlongMap`, which
is the case `g₁ = u ≫ g₂` definitionally; this form takes the intertwining as a
propositional hypothesis, so `γ`-actions on covers apply). -/
noncomputable def pullbackAlongMapOf (X : EllObj (CommRingCat.of ℚ))
    {T₁ T₂ : Scheme.{0}} {g₁ : T₁ ⟶ X.base} {g₂ : T₂ ⟶ X.base}
    (u : T₁ ⟶ T₂) (hu : u ≫ g₂ = g₁) :
    X.pullbackAlong g₁ ⟶ X.pullbackAlong g₂ where
  baseHom := u
  base_w := by
    show u ≫ g₂ ≫ X.structMap = g₁ ≫ X.structMap
    rw [← Category.assoc, hu]
  top := pullback.map X.curve.π g₁ X.curve.π g₂ (𝟙 _) u (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, hu])
  isPullback := by
    subst hu
    have hbig := IsPullback.of_hasPullback X.curve.π (u ≫ g₂)
    have hfst : pullback.map X.curve.π (u ≫ g₂) X.curve.π g₂ (𝟙 _) u (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]) ≫
          pullback.fst X.curve.π g₂ =
        pullback.fst X.curve.π (u ≫ g₂) := by
      rw [pullback.lift_fst, Category.comp_id]
    rw [← hfst] at hbig
    refine IsPullback.of_right hbig ?_ (IsPullback.of_hasPullback X.curve.π g₂)
    show pullback.map X.curve.π (u ≫ g₂) X.curve.π g₂ (𝟙 _) u (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]) ≫
        pullback.snd X.curve.π g₂ =
      pullback.snd X.curve.π (u ≫ g₂) ≫ u
    rw [pullback.lift_snd]
  zero_w := by
    show pullback.lift (g₁ ≫ X.curve.zero) (𝟙 T₁)
        (by rw [Category.assoc, X.curve.zero_π, Category.comp_id,
          Category.id_comp]) ≫
      pullback.map X.curve.π g₁ X.curve.π g₂ (𝟙 _) u (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hu]) =
      u ≫ pullback.lift (g₂ ≫ X.curve.zero) (𝟙 T₂)
        (by rw [Category.assoc, X.curve.zero_π, Category.comp_id,
          Category.id_comp])
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [← Category.assoc, hu]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id, Category.id_comp]

@[simp]
theorem pullbackAlongMapOf_baseHom (X : EllObj (CommRingCat.of ℚ))
    {T₁ T₂ : Scheme.{0}} {g₁ : T₁ ⟶ X.base} {g₂ : T₂ ⟶ X.base}
    (u : T₁ ⟶ T₂) (hu : u ≫ g₂ = g₁) :
    (pullbackAlongMapOf X u hu).baseHom = u := rfl

/-- **[T-EQ-3c-L3b]** The base-change reassociation comparison in `Ell/ℚ`: the
double base change along `c` then `k` maps to the base change along `c ≫ k`, over
the identity of the inner base (the canonical comparison of the composite
projection). -/
noncomputable def pullbackAlongAssocHom (X : EllObj (CommRingCat.of ℚ))
    {T' T'' : Scheme.{0}} (k : T' ⟶ X.base) (c : T'' ⟶ T') :
    (X.pullbackAlong k).pullbackAlong c ⟶ X.pullbackAlong (c ≫ k) :=
  EllObj.toPullbackAlong
    ((X.pullbackAlong k).pullbackAlongπ c ≫ X.pullbackAlongπ k)

@[simp]
theorem pullbackAlongAssocHom_baseHom (X : EllObj (CommRingCat.of ℚ))
    {T' T'' : Scheme.{0}} (k : T' ⟶ X.base) (c : T'' ⟶ T') :
    (pullbackAlongAssocHom X k c).baseHom = 𝟙 T'' := rfl

/-- The reassociation comparison recovers the composite projection. -/
theorem pullbackAlongAssocHom_π (X : EllObj (CommRingCat.of ℚ))
    {T' T'' : Scheme.{0}} (k : T' ⟶ X.base) (c : T'' ⟶ T') :
    pullbackAlongAssocHom X k c ≫ X.pullbackAlongπ (c ≫ k) =
      (X.pullbackAlong k).pullbackAlongπ c ≫ X.pullbackAlongπ k :=
  EllObj.toPullbackAlong_pullbackAlongπ _

/-- **[T-EQ-3c-L3c1]** Naturality of a relative representation datum's classifying
bijection along any intertwining morphism (the `MapOf`-generalization of
`RelRepData.nat`; at `hu := rfl` it is `nat` itself). -/
theorem RelRepData.eqv_mapOf {Q : ModularCurves.ModuliProblem (CommRingCat.of ℚ)}
    {X : EllObj (CommRingCat.of ℚ)} (d : ModuliProblem.RelRepData Q X)
    {T₁ T₂ : Scheme.{0}} {g₁ : T₁ ⟶ X.base} {g₂ : T₂ ⟶ X.base}
    (u : T₁ ⟶ T₂) (hu : u ≫ g₂ = g₁)
    (h : { m : T₂ ⟶ d.Z // m ≫ d.f = g₂ }) :
    d.eqv g₁ ⟨u ≫ h.1, by rw [Category.assoc, h.2, hu]⟩ =
      Q.map (pullbackAlongMapOf X u hu).op (d.eqv g₂ h) := by
  subst hu
  exact d.nat g₂ u h

/-- **[T-EQ-3c-L3c3]** The exchange law between a base-endomorphism comparison and
the reassociation comparison: translating downstairs then reassociating equals
reassociating then translating upstairs. -/
theorem pullbackAlongMapOf_assocHom (X : EllObj (CommRingCat.of ℚ))
    {T' T'' : Scheme.{0}} (k : T' ⟶ X.base) (c : T'' ⟶ T')
    (u : T'' ⟶ T'') (hu : u ≫ c = c) :
    pullbackAlongMapOf (X.pullbackAlong k) u hu ≫ pullbackAlongAssocHom X k c =
      pullbackAlongAssocHom X k c ≫
        pullbackAlongMapOf X u (by
          rw [← Category.assoc, hu]) := by
  refine EllHom.ext ?_ ?_
  · show u ≫ 𝟙 T'' = 𝟙 T'' ≫ u
    rw [Category.comp_id, Category.id_comp]
  · show (pullbackAlongMapOf (X.pullbackAlong k) u hu).top ≫
        (pullbackAlongAssocHom X k c).top =
      (pullbackAlongAssocHom X k c).top ≫
        (pullbackAlongMapOf X u (by rw [← Category.assoc, hu])).top
    apply pullback.hom_ext
    · have hLfst : (pullbackAlongAssocHom X k c).top ≫
          pullback.fst X.curve.π (c ≫ k) =
          pullback.fst (X.curve.baseChange k).π c ≫ pullback.fst X.curve.π k :=
        ((X.pullbackAlong k).pullbackAlongπ c ≫
          X.pullbackAlongπ k).isPullback.isoPullback_hom_fst
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg
        ((pullbackAlongMapOf (X.pullbackAlong k) u hu).top ≫ ·) hLfst) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (· ≫ pullback.fst X.curve.π k)
        ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg ((pullbackAlongAssocHom X k c).top ≫ ·)
        ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
      exact hLfst
    · have hLsnd : (pullbackAlongAssocHom X k c).top ≫
          pullback.snd X.curve.π (c ≫ k) =
          pullback.snd (X.curve.baseChange k).π c :=
        ((X.pullbackAlong k).pullbackAlongπ c ≫
          X.pullbackAlongπ k).isPullback.isoPullback_hom_snd
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg
        ((pullbackAlongMapOf (X.pullbackAlong k) u hu).top ≫ ·) hLsnd) ?_
      refine Eq.trans (pullback.lift_snd _ _ _) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg ((pullbackAlongAssocHom X k c).top ≫ ·)
        (pullback.lift_snd _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact congrArg (· ≫ u) hLsnd

/-- **[T-EQ-3c-L2 congr]** The coordinate map is congruent in the frame (proofs
transport). -/
theorem framedCoordMap_congr_frame (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    {h₁ h₂ : T ⟶ wFrames D} (hh : h₁ = h₂) (hover : h₁ ≫ wFramesπ D = sT) :
    framedCoordMap D sT E hinv L h₁ hover =
      framedCoordMap D sT E hinv L h₂ (hh ▸ hover) := by
  subst hh; rfl

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3c-L3c2]** The classified value translates under a `σZ`-intertwining
base endomorphism by the diagonal `γ`-translation of the symplectically framed
problem (the value-level equivariance of the correspondence). -/
theorem eqv_smul_translate (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    {T₀ : Scheme.{0}} {g : T₀ ⟶ X.base}
    (m : { m : T₀ ⟶ d.Z // m ≫ d.f = g })
    (uT : T₀ ⟶ T₀) (huT : uT ≫ g = g)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hcomm : uT ≫ m.1 = m.1 ≫ d.σZ.hom γ) :
    (sympFramedProblem D).map (pullbackAlongMapOf X uT huT).op (d.eqv g m) =
      (sympFramedSmulNat D γ).app (Opposite.op (X.pullbackAlong g))
        (d.eqv g m) := by
  have hsub : (⟨uT ≫ m.1, by rw [Category.assoc, m.2, huT]⟩ :
      { m' : T₀ ⟶ d.Z // m' ≫ d.f = g }) =
      ⟨m.1 ≫ d.σZ.hom γ, by rw [Category.assoc, d.over_base, m.2]⟩ :=
    Subtype.ext hcomm
  refine Eq.trans (RelRepData.eqv_mapOf d.toRelRepData uT huT m).symm ?_
  refine Eq.trans (congrArg (d.eqv g) hsub) ?_
  refine Eq.trans (d.equivariant g m γ) ?_
  exact congrArg (fun γ' => (sympFramedSmulNat D γ').app
    (Opposite.op (X.pullbackAlong g)) (d.eqv g m)) (inv_inv γ)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3c-L3c4]** The transported value on the double base change translates
under the `σZ`-intertwining endomorphism by the `γ`-translation (the `w`-level
equivariance: conjugate the base-change comparison through the exchange law, use
the value-level equivariance, and push through by naturality of the diagonal
translation). -/
theorem w_smul_translate (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    {T' T'' : Scheme.{0}} (k : T' ⟶ X.base) (c : T'' ⟶ T')
    (m : { m : T'' ⟶ d.Z // m ≫ d.f = c ≫ k })
    (uT : T'' ⟶ T'') (huT : uT ≫ c = c)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hcomm : uT ≫ m.1 = m.1 ≫ d.σZ.hom γ) :
    (sympFramedProblem D).map
        (pullbackAlongMapOf (X.pullbackAlong k) uT huT).op
        ((sympFramedProblem D).map (pullbackAlongAssocHom X k c).op
          (d.eqv (c ≫ k) m)) =
      (sympFramedSmulNat D γ).app
        (Opposite.op ((X.pullbackAlong k).pullbackAlong c))
        ((sympFramedProblem D).map (pullbackAlongAssocHom X k c).op
          (d.eqv (c ≫ k) m)) := by
  have h1 := (congrArg
    (fun (F : (sympFramedProblem D).obj
        (Opposite.op (X.pullbackAlong (c ≫ k))) ⟶
      (sympFramedProblem D).obj
        (Opposite.op ((X.pullbackAlong k).pullbackAlong c))) =>
      F (d.eqv (c ≫ k) m))
    ((sympFramedProblem D).map_comp (pullbackAlongAssocHom X k c).op
      (pullbackAlongMapOf (X.pullbackAlong k) uT huT).op)).symm
  have h2 := congrArg
    (fun (q : (X.pullbackAlong k).pullbackAlong c ⟶ X.pullbackAlong (c ≫ k)) =>
      (sympFramedProblem D).map q.op (d.eqv (c ≫ k) m))
    (pullbackAlongMapOf_assocHom X k c uT huT)
  have h3 := congrArg
    (fun (F : (sympFramedProblem D).obj
        (Opposite.op (X.pullbackAlong (c ≫ k))) ⟶
      (sympFramedProblem D).obj
        (Opposite.op ((X.pullbackAlong k).pullbackAlong c))) =>
      F (d.eqv (c ≫ k) m))
    ((sympFramedProblem D).map_comp
      (pullbackAlongMapOf X uT (by rw [← Category.assoc, huT])).op
      (pullbackAlongAssocHom X k c).op)
  have h4 := congrArg
    ((sympFramedProblem D).map (pullbackAlongAssocHom X k c).op)
    (eqv_smul_translate D d m uT (by rw [← Category.assoc, huT]) γ hcomm)
  have h5 := (congrArg
    (fun (F : (sympFramedProblem D).obj
        (Opposite.op (X.pullbackAlong (c ≫ k))) ⟶
      (sympFramedProblem D).obj
        (Opposite.op ((X.pullbackAlong k).pullbackAlong c))) =>
      F (d.eqv (c ≫ k) m))
    ((sympFramedSmulNat D γ).naturality
      (pullbackAlongAssocHom X k c).op)).symm
  exact (((h1.trans h2).trans h3).trans h4).trans h5

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

section AgreeLocus

/-- **[T-EQ-3d-L1]** The tautological frame over a frames-product base lies over
the base (`pullback.condition`). -/
theorem tautFrame_over (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) :
    pullback.snd sT (wFramesπ D) ≫ wFramesπ D =
      pullback.fst sT (wFramesπ D) ≫ sT :=
  pullback.condition.symm

variable (D : GaloisRepData N) [Fact (1 < N)] {Tt : Scheme.{0}}
variable (f g : Tt ⟶ muNRootsScheme D)
variable (hfg : f ≫ muNRootsSchemeπ D = g ≫ muNRootsSchemeπ D)

/-- **[T-EQ-3d-L2]** The paired comparison of two roots-scheme maps over a
common base. -/
noncomputable def agreePair :
    Tt ⟶ pullback (muNRootsSchemeπ D) (muNRootsSchemeπ D) :=
  pullback.lift f g hfg

/-- **[T-EQ-3d-L2]** The agreement locus of two roots-scheme maps (value-level
`sympLocus`): the pullback of the diagonal along the paired comparison. -/
noncomputable def agreeLocus : Scheme.{0} :=
  pullback (pullback.diagonal (muNRootsSchemeπ D)) (agreePair D f g hfg)

/-- Its inclusion into the base. -/
noncomputable def agreeLocusι : agreeLocus D f g hfg ⟶ Tt :=
  pullback.snd _ _

/-- The inclusion is an open immersion (unramified + finite-type diagonal). -/
theorem agreeLocusι_isOpenImmersion :
    IsOpenImmersion (agreeLocusι D f g hfg) := by
  haveI : Etale (muNRootsSchemeπ D) := (muNRootsSchemeπ_finite_etale D).2
  haveI : IsFinite (muNRootsSchemeπ D) := (muNRootsSchemeπ_finite_etale D).1
  show IsOpenImmersion
    (pullback.snd (pullback.diagonal (muNRootsSchemeπ D))
      (agreePair D f g hfg))
  infer_instance

/-- The inclusion is a closed immersion (separated diagonal). -/
theorem agreeLocusι_isClosedImmersion :
    IsClosedImmersion (agreeLocusι D f g hfg) := by
  haveI : IsSeparated (muNRootsSchemeπ D) :=
    inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (muNRootsAlgebra D : Type 0)))))
  show IsClosedImmersion
    (pullback.snd (pullback.diagonal (muNRootsSchemeπ D))
      (agreePair D f g hfg))
  exact MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _
    inferInstance

/-- **[T-EQ-3d-L2]** Factoring through the agreement locus is exactly the
agreement of the two maps. -/
theorem agreeLocus_factor_iff {W : Scheme.{0}} (h : W ⟶ Tt) :
    (∃ w : W ⟶ agreeLocus D f g hfg, w ≫ agreeLocusι D f g hfg = h) ↔
      h ≫ f = h ≫ g := by
  have hcond : agreeLocusι D f g hfg ≫ agreePair D f g hfg =
      pullback.fst (pullback.diagonal (muNRootsSchemeπ D))
          (agreePair D f g hfg) ≫
        pullback.diagonal (muNRootsSchemeπ D) :=
    pullback.condition.symm
  have hιe : agreeLocusι D f g hfg ≫ f =
      pullback.fst (pullback.diagonal (muNRootsSchemeπ D))
        (agreePair D f g hfg) :=
    (congrArg (agreeLocusι D f g hfg ≫ ·) (pullback.lift_fst f g hfg).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.fst (muNRootsSchemeπ D) (muNRootsSchemeπ D))
            hcond).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (pullback.fst (pullback.diagonal (muNRootsSchemeπ D))
                (agreePair D f g hfg) ≫ ·) (pullback.diagonal_fst _)).trans
              (Category.comp_id _)))))
  have hιd : agreeLocusι D f g hfg ≫ g =
      pullback.fst (pullback.diagonal (muNRootsSchemeπ D))
        (agreePair D f g hfg) :=
    (congrArg (agreeLocusι D f g hfg ≫ ·) (pullback.lift_snd f g hfg).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.snd (muNRootsSchemeπ D) (muNRootsSchemeπ D))
            hcond).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (pullback.fst (pullback.diagonal (muNRootsSchemeπ D))
                (agreePair D f g hfg) ≫ ·) (pullback.diagonal_snd _)).trans
              (Category.comp_id _)))))
  constructor
  · rintro ⟨w, rfl⟩
    rw [Category.assoc, Category.assoc, hιe, hιd]
  · intro he
    refine ⟨pullback.lift (h ≫ f) h ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst,
        Category.comp_id, agreePair, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, agreePair, Category.assoc, pullback.lift_snd]
      exact he

end AgreeLocus

section CorrSurjective

open scoped FintypeCatDiscrete

/-- **[T-EQ-3d-L3a piece 1]** Every `ℚ̄`-algebra evaluation of the target algebra
of a set-surjective correspondence morphism factors through the morphism's
algebra map (lift the classified point through the set-map). -/
theorem qbarAlgHom_factors
    {X Y : ContAction FintypeCat.{0}
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (m : X ⟶ Y) (hm : Function.Surjective m.hom.hom)
    (χ : (corrAlgebra Y : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ χ' : (corrAlgebra X : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ,
      χ = χ'.comp
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          m).unop.hom.hom := by
  obtain ⟨xv, hxv⟩ := hm (qbarPointsRead Y
    ((specPointsEquivAlgHom ℚ (corrAlgebra Y : Type 0)
      (AlgebraicClosure ℚ)).symm χ))
  set ptX := (qbarPointsRead X).symm xv with hptX
  have hpt : (⟨ptX.1 ≫ corrSpecMap m, by
      rw [Category.assoc, corrSpecMap_π, ptX.2]⟩ :
      { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ corrSpec Y //
        h ≫ corrSpecπ Y =
          Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) =
      (specPointsEquivAlgHom ℚ (corrAlgebra Y : Type 0)
        (AlgebraicClosure ℚ)).symm χ := by
    refine (qbarPointsRead Y).injective ?_
    refine Eq.trans (qbarPointsRead_map m ptX) ?_
    rw [hptX, Equiv.apply_symm_apply, hxv]
  refine ⟨specPointsEquivAlgHom ℚ (corrAlgebra X : Type 0)
    (AlgebraicClosure ℚ) ptX, ?_⟩
  have hχ : χ = specPointsEquivAlgHom ℚ (corrAlgebra Y : Type 0)
      (AlgebraicClosure ℚ) ⟨ptX.1 ≫ corrSpecMap m,
        (Category.assoc _ _ _).trans
          ((congrArg (ptX.1 ≫ ·) (corrSpecMap_π m)).trans ptX.2)⟩ :=
    ((congrArg (specPointsEquivAlgHom ℚ (corrAlgebra Y : Type 0)
      (AlgebraicClosure ℚ)) hpt).trans
      (Equiv.apply_symm_apply _ χ)).symm
  refine hχ.trans ?_
  have hpre := spec_preimage_comp ptX.1 (CommRingCat.ofHom
    (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      m).unop.hom.hom.toRingHom))
  refine AlgHom.ext fun a => ?_
  exact congrArg (fun q : CommRingCat.of (corrAlgebra Y : Type 0) ⟶
    CommRingCat.of (AlgebraicClosure ℚ) => q.hom a) hpre

/-- **[T-EQ-3d-L3a piece 2]** `ℚ̄`-evaluations separate elements of a finite
étale `ℚ`-algebra (split into a finite product of finite separable field
extensions and evaluate the nonvanishing component). -/
theorem corrAlgebra_exists_eval_ne
    (Y : ContAction FintypeCat.{0}
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    {b : (corrAlgebra Y : Type 0)} (hb : b ≠ 0) :
    ∃ χ : (corrAlgebra Y : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ, χ b ≠ 0 := by
  classical
  obtain ⟨I, hIfin, Ai, hFld, hAlgI, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod ℚ
      (corrAlgebra Y : Type 0)).mp inferInstance
  have heb : e b ≠ 0 := fun h => hb (e.injective (h.trans (map_zero e).symm))
  have hcomp : ∃ i : I, e b i ≠ 0 := by
    by_contra hall
    exact heb (funext fun i => by
      by_contra h
      exact hall ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hcomp
  letI := hFld i
  letI := hAlgI i
  haveI : Module.Finite ℚ (Ai i) := by
    refine Module.Finite.of_surjective
      ((Pi.evalAlgHom ℚ Ai i).comp e.toAlgHom).toLinearMap ?_
    have hsurj : Function.Surjective
        (fun z : (corrAlgebra Y : Type 0) => e z i) :=
      fun y => by
        obtain ⟨w, hw⟩ := e.surjective (Function.update 0 i y)
        exact ⟨w, (congrFun hw i).trans (Function.update_self _ _ _)⟩
    exact hsurj
  haveI : Algebra.IsAlgebraic ℚ (Ai i) := Algebra.IsAlgebraic.of_finite ℚ _
  let χ₀ : Ai i →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  refine ⟨χ₀.comp ((Pi.evalAlgHom ℚ Ai i).comp e.toAlgHom), ?_⟩
  show χ₀ (e b i) ≠ 0
  intro h0
  exact hi (by
    have := congrArg (fun z => z) h0
    rw [show (0 : AlgebraicClosure ℚ) = χ₀ 0 from (map_zero χ₀).symm] at this
    exact RingHom.injective (χ₀.toRingHom) this)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3a]** A correspondence morphism with surjective set-map has a
surjective spectrum map (injectivity of the algebra map by evaluation
separation + the factoring, then integral lying-over). -/
theorem corrSpecMap_surjective
    {X Y : ContAction FintypeCat.{0}
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (m : X ⟶ Y) (hm : Function.Surjective m.hom.hom) :
    Surjective (corrSpecMap m) := by
  have hinj : Function.Injective
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        m).unop.hom.hom.toRingHom) := by
    rw [injective_iff_map_eq_zero]
    intro b hb0
    by_contra hne
    obtain ⟨χ, hχne⟩ := corrAlgebra_exists_eval_ne Y hne
    obtain ⟨χ', hfac⟩ := qbarAlgHom_factors m hm χ
    refine hχne ?_
    rw [hfac]
    show χ' (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      m).unop.hom.hom b) = 0
    rw [show ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      m).unop.hom.hom b = 0 from hb0]
    exact map_zero χ'
  have hint : (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      m).unop.hom.hom.toRingHom).IsIntegral := by
    refine RingHom.IsIntegral.tower_top
      (algebraMap ℚ (corrAlgebra Y : Type 0)) _ ?_
    have hcomp : (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        m).unop.hom.hom.toRingHom).comp
          (algebraMap ℚ (corrAlgebra Y : Type 0)) =
        algebraMap ℚ (corrAlgebra X : Type 0) :=
      RingHom.ext fun r =>
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          m).unop.hom.hom.commutes r
    exact cast (congrArg RingHom.IsIntegral hcomp).symm
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr
        (corrAlgebra X).property.left))
  constructor
  exact RingHom.IsIntegral.comap_surjective hint hinj

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3b]** The determinant read of frames is surjective (every unit is
a determinant: `Matrix.GeneralLinearGroup.det_surjective`). -/
theorem detFrameScheme_surjective (D : GaloisRepData N) :
    Surjective (detFrameScheme D) := by
  refine corrSpecMap_surjective (detFrameMor D) ?_
  intro u
  obtain ⟨A, hA⟩ := Matrix.GeneralLinearGroup.det_surjective
    (n := Fin 2) (R := ZMod N) u
  exact ⟨A, hA⟩

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c i]** A set-injective correspondence morphism has a monic
algebra-side image (the mono-chain through the faithful forgetful functors and
the equivalence). -/
theorem corrInverse_mono_of_injective
    {X Y : ContAction FintypeCat.{0}
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (m : X ⟶ Y) (hm : Function.Injective m.hom.hom) :
    Mono ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m) := by
  haveI h3 : Mono m := by
    constructor
    intro W g₁ g₂ hg
    ext x : 3
    exact hm (congrArg (fun q => q.hom.hom x) hg)
  exact ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.mono_map_iff_mono
    m).mpr h3

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c i]** The determinant-side comparison is set-injective (the
pairing normalisation is an equivalence on the units). -/
theorem detCompMor_injective (D : GaloisRepData N) [Fact (1 < N)] :
    Function.Injective (detCompMor D).hom.hom := by
  intro u v huv
  have h1 : D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) =
      D.p (Multiplicative.ofAdd ((v : (ZMod N)ˣ) : ZMod N)) := huv
  have h2 : ((u : (ZMod N)ˣ) : ZMod N) = ((v : (ZMod N)ˣ) : ZMod N) :=
    Multiplicative.ofAdd.injective (D.p.injective h1)
  exact Units.ext h2

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c ii]** The direct-summand splitting of the roots algebra along
the determinant-side comparison (the mono splits off a binary cofactor by the
Chinese remainder engine of the Galois correspondence). -/
theorem detComp_splitting (D : GaloisRepData N) [Fact (1 < N)] :
    ∃ (Z : (CommAlgCat.FiniteEtale.{0} ℚ)ᵒᵖ)
      (u : Z ⟶ (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.obj
        (muNRootsContAction D)),
      Nonempty (CategoryTheory.Limits.IsColimit (BinaryCofan.mk
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (detCompMor D)) u)) := by
  haveI := corrInverse_mono_of_injective (detCompMor D) (detCompMor_injective D)
  exact FiniteEtaleGalois.monoInducesIsoOnDirectSummand_op _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c ii]** The determinant-side comultiplication is a surjective
algebra map (epi of finite étale algebras, from the op-mono). -/
theorem detCompAlgHom_surjective (D : GaloisRepData N) [Fact (1 < N)] :
    Function.Surjective (detCompAlgHom D).hom.hom := by
  haveI hmono := corrInverse_mono_of_injective (detCompMor D)
    (detCompMor_injective D)
  haveI : Epi ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (detCompMor D)).unop := unop_epi_of_mono _
  exact FiniteEtaleGalois.surjective_of_epi
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (detCompMor D)).unop

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c ii]** The determinant-side comparison is a clopen immersion:
closed from the surjective comultiplication, open from flat + mono
(`IsOpenImmersion.of_flat_of_mono`, with étaleness by cancellation along the
finite étale structure maps). -/
theorem detCompScheme_isOpenImmersion (D : GaloisRepData N) [Fact (1 < N)] :
    IsOpenImmersion (detCompScheme D) := by
  haveI hCI : IsClosedImmersion (detCompScheme D) :=
    IsClosedImmersion.spec_of_surjective _ (detCompAlgHom_surjective D)
  haveI hEt2 : Etale (muNRootsSchemeπ D) := (muNRootsSchemeπ_finite_etale D).2
  haveI hEtComp : Etale (detCompScheme D ≫ muNRootsSchemeπ D) := by
    rw [detCompScheme_π]
    show Etale (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (cycloUnitsAlgebra D : Type 0))))
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  haveI : Etale (detCompScheme D) :=
    Etale.of_comp (detCompScheme D) (muNRootsSchemeπ D)
  exact IsOpenImmersion.of_flat_of_mono _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c iii]** Factoring through the determinant clopen immersion
from the range condition. -/
theorem factors_detComp_of_range (D : GaloisRepData N) [Fact (1 < N)]
    {W : Scheme.{0}} (φ : W ⟶ muNRootsScheme D)
    (hr : Set.range φ.base ⊆ Set.range (detCompScheme D).base) :
    ∃ w : W ⟶ cycloUnitsScheme D, w ≫ detCompScheme D = φ := by
  haveI := detCompScheme_isOpenImmersion D
  exact ⟨IsOpenImmersion.lift (detCompScheme D) φ hr,
    IsOpenImmersion.lift_fac (detCompScheme D) φ hr⟩

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c iv]** The field-generic classify lemma: the
`μ_N`-group-scheme read of a `K`-point of the roots scheme is the classifying
map evaluated at the cyclotomic root (the `ℚ̄`-statement's proof verbatim — every
ingredient is field-generic). -/
theorem muNRootsRead_classify_field (D : GaloisRepData N) [Fact (1 < N)]
    (K : Type) [Field K] [Algebra ℚ K]
    (φ : Spec (.of K) ⟶ corrSpec (muNRootsContAction D))
    (hφ : φ ≫ corrSpecπ (muNRootsContAction D) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        (muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) φ hφ) =
    (specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0) K
        ⟨φ, hφ⟩)
      ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) := by
  have h1 : muNRootsRead D
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) φ hφ =
      ((φ ≫ (muNSpecQIso D).inv) ≫
        pullback.snd (terminal.from (Spec (CommRingCat.of ℚ)))
          (terminal.from (muNAbs N))).appTop.hom
        ((Scheme.ΓSpecIso (muNRing N)).inv.hom (muNAbsGen N)) :=
    muNPointsEquiv_coe (Spec (CommRingCat.of ℚ)) N _ _
  have h2 : (φ ≫ (muNSpecQIso D).inv) ≫
      pullback.snd (terminal.from (Spec (CommRingCat.of ℚ)))
        (terminal.from (muNAbs N)) =
      (φ ≫ Spec.map (CommRingCat.ofHom
        (muNRootsAlgebraIso D).inv.hom.hom.toRingHom)) ≫
        Spec.map (Spec.preimage ((muNSpecFieldIso ℚ N).inv ≫
          pullback.snd (terminal.from (Spec (CommRingCat.of ℚ)))
            (terminal.from (muNAbs N)))) := by
    rw [Spec.map_preimage]
    show (φ ≫ (Spec.map (CommRingCat.ofHom
        (muNRootsAlgebraIso D).inv.hom.hom.toRingHom) ≫
        (muNSpecFieldIso ℚ N).inv)) ≫
      pullback.snd (terminal.from (Spec (CommRingCat.of ℚ)))
        (terminal.from (muNAbs N)) = _
    simp only [Category.assoc]
    rfl
  refine Eq.trans (congrArg
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (h1.trans (congrArg
      (fun (m : Spec (.of K) ⟶ muNAbs N) =>
        m.appTop.hom ((Scheme.ΓSpecIso (muNRing N)).inv.hom (muNAbsGen N)))
      h2))) ?_
  refine Eq.trans (gammaSpec_read _ (muNAbsGen N)) ?_
  refine Eq.trans (congrArg
    (fun (q : muNRing N ⟶ CommRingCat.of K) =>
      q.hom (muNAbsGen N))
    (spec_preimage_comp
      (φ ≫ Spec.map (CommRingCat.ofHom
        (muNRootsAlgebraIso D).inv.hom.hom.toRingHom))
      (Spec.preimage ((muNSpecFieldIso ℚ N).inv ≫
        pullback.snd (terminal.from (Spec (CommRingCat.of ℚ)))
          (terminal.from (muNAbs N)))))) ?_
  refine Eq.trans (congrArg
    (Spec.preimage (φ ≫ Spec.map (CommRingCat.ofHom
      (muNRootsAlgebraIso D).inv.hom.hom.toRingHom))).hom
    (muNSpecFieldIso_inv_snd_gen ℚ N)) ?_
  exact congrArg
    (fun (q : CommRingCat.of
        (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ⟶
      CommRingCat.of K) =>
      q.hom (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)))
    (spec_preimage_comp φ (CommRingCat.ofHom
      (muNRootsAlgebraIso D).inv.hom.hom.toRingHom))

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c v]** The `K`-read of the value-level pairing comparison is the
`Γ`-restriction of the Weil-pairing evaluation (base-transported
`pairEZMap_read`). -/
theorem pairEZ_read_eval (D : GaloisRepData N) [Fact (1 < N)]
    (K : Type) [Field K] [Algebra ℚ K]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (L : E.FullLevelPt N) (tk : Spec (.of K) ⟶ T)
    (htk : tk ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) :
    muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))
        (tk ≫ pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2)
        (by rw [Category.assoc, pairEZMap_π, htk]) =
      (Scheme.Γ.map tk.op).hom
        (E.weilPairingEval L.1.1 L.1.2
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.1).mp L.2.1.1)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.2).mp L.2.1.2)).1 := by
  refine Eq.trans ?_ (pairEZMap_read D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 tk)
  exact (muNRootsRead_congr D htk rfl _).symm

/-- **[T-EQ-3d-L3c vi]** Order forcing in a rank-two torsion group: if a pair
with annihilators `N` and `d ∣ N` generates all the `N`-torsion, and the
`N`-torsion is `(ℤ/N)²`, then `N ∣ d` (cardinality of the generated subgroup). -/
theorem dvd_of_closure_pair_torsion {G : Type} [AddCommGroup G]
    (a b : G) (d : ℕ) (hdN : d ∣ N) (hdpos : 0 < d)
    (hNa : (N : ℤ) • a = 0) (hdb : (d : ℤ) • b = 0)
    (hfull : ∀ g : G, (N : ℤ) • g = 0 → g ∈ AddSubgroup.closure {a, b})
    (hiso : Nonempty
      ((Submodule.torsionBy ℤ G (N : ℤ)) ≃+ (Fin 2 → ZMod N))) :
    N ∣ d := by
  obtain ⟨e⟩ := hiso
  haveI : NeZero d := ⟨hdpos.ne'⟩
  have hNb : (N : ℤ) • b = 0 := by
    obtain ⟨c, hc⟩ := hdN
    rw [hc, mul_comm]
    push_cast
    rw [mul_smul, hdb, smul_zero]
  set f : ZMod N × ZMod d → Submodule.torsionBy ℤ G (N : ℤ) :=
    fun ij => ⟨(ij.1.val : ℤ) • a + (ij.2.val : ℤ) • b, by
      rw [Submodule.mem_torsionBy_iff]
      show (N : ℤ) • ((ij.1.val : ℤ) • a + (ij.2.val : ℤ) • b) = 0
      rw [smul_add, smul_comm (N : ℤ) ((ij.1.val : ℤ)),
        smul_comm (N : ℤ) ((ij.2.val : ℤ)), hNa, hNb, smul_zero, smul_zero,
        add_zero]⟩ with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : (N : ℤ) • z = 0 := (Submodule.mem_torsionBy_iff _ _).mp hz
    have hcl := hfull z hz'
    rw [AddSubgroup.mem_closure_pair] at hcl
    obtain ⟨m, n, hmn⟩ := hcl
    refine ⟨((m : ZMod N), (n : ZMod d)), ?_⟩
    refine Subtype.ext ?_
    show ((((m : ZMod N)).val : ℤ)) • a + ((((n : ZMod d)).val : ℤ)) • b = z
    have ha' : (((m : ZMod N)).val : ℤ) • a = m • a := by
      refine EllipticCurve.zsmul_eq_of_intCast_eq a hNa ?_
      simp [ZMod.natCast_val]
    have hb' : (((n : ZMod d)).val : ℤ) • b = n • b := by
      refine EllipticCurve.zsmul_eq_of_intCast_eq b hdb ?_
      simp [ZMod.natCast_val]
    rw [ha', hb', hmn]
  have hcard : (N : ℕ) * N ≤ N * d := by
    have h1 : Nat.card (Submodule.torsionBy ℤ G (N : ℤ)) =
        Nat.card (Fin 2 → ZMod N) := Nat.card_congr e.toEquiv
    have h2 : Nat.card (Fin 2 → ZMod N) = N * N := by
      rw [Nat.card_fun]
      simp [Nat.card_eq_fintype_card, ZMod.card, sq]
    have h3 : Nat.card (Submodule.torsionBy ℤ G (N : ℤ)) ≤
        Nat.card (ZMod N × ZMod d) := Nat.card_le_card_of_surjective f hsurj
    have h4 : Nat.card (ZMod N × ZMod d) = N * d := by
      rw [Nat.card_prod]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    omega
  have hNd : N ≤ d := Nat.le_of_mul_le_mul_left hcard (Nat.pos_of_ne_zero
    (NeZero.ne N))
  have hdd : d = N := Nat.le_antisymm
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdN) hNd
  rw [hdd]

/-- **[T-EQ-3d-L3c vii]** The order-forcing at a geometric point: if the Weil
pairing of a generating torsion pair satisfies `e^d = 1` for `d ∣ N`, then
`N ∣ d` (pair everything against `d•Q'` via the symplectic register, kill it by
nondegeneracy, and force the order by the rank-two count). -/
theorem weilPairing_pair_order (K : Type) [Field K] [IsAlgClosed K]
    {T : Scheme.{0}} {E : EllipticCurve T}
    (t : Spec (.of K) ⟶ T) (P' Q' : E.Point t)
    (hP' : (N : ℤ) • P' = 0) (hQ' : (N : ℤ) • Q' = 0)
    (hfull : ∀ z : E.Point t, (N : ℤ) • z = 0 →
      z ∈ AddSubgroup.closure {P', Q'})
    (hNK : (N : K) ≠ 0)
    (d : ℕ) (hd : d ∣ N) (hdpos : 0 < d)
    (hpow : (E.weilPairingEval P' Q'
        ((E.smul_eq_zero_iff_comp_mulByHom t N P').mp hP')
        ((E.smul_eq_zero_iff_comp_mulByHom t N Q').mp hQ')).1 ^ d = 1) :
    N ∣ d := by
  have hkill_dQ : (N : ℤ) • ((d : ℤ) • Q') = 0 := by
    rw [smul_comm, hQ', smul_zero]
  have hpair : ∀ (z : E.Point t) (hz : (N : ℤ) • z = 0),
      (E.weilPairingEval ((d : ℤ) • Q') z
        ((E.smul_eq_zero_iff_comp_mulByHom t N _).mp hkill_dQ)
        ((E.smul_eq_zero_iff_comp_mulByHom t N z).mp hz)).1 = 1 := by
    intro z hz
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp (hfull z hz)
    have h0d : (0 : ℤ) • P' + (d : ℤ) • Q' = (d : ℤ) • Q' := by
      rw [zero_smul, zero_add]
    have hsymp := E.weilPairingEval_symplectic P' Q' 0 (d : ℤ) m n
      ((E.smul_eq_zero_iff_comp_mulByHom t N P').mp hP')
      ((E.smul_eq_zero_iff_comp_mulByHom t N Q').mp hQ')
      (by
        rw [h0d]
        exact (E.smul_eq_zero_iff_comp_mulByHom t N _).mp hkill_dQ)
      (by
        rw [hmn]
        exact (E.smul_eq_zero_iff_comp_mulByHom t N z).mp hz)
    have hEcongr := weilPairingEval_congr_raw (E := E) rfl
      (congrArg Subtype.val h0d) (congrArg Subtype.val hmn)
      (by
        rw [h0d]
        exact (E.smul_eq_zero_iff_comp_mulByHom t N _).mp hkill_dQ)
      (by
        rw [hmn]
        exact (E.smul_eq_zero_iff_comp_mulByHom t N z).mp hz)
      ((E.smul_eq_zero_iff_comp_mulByHom t N _).mp hkill_dQ)
      ((E.smul_eq_zero_iff_comp_mulByHom t N z).mp hz)
    rw [← hEcongr, hsymp]
    have hdvd : (d : ℤ) ∣ ((0 * n - (d : ℤ) * m) % (N : ℤ)) := by
      have h1 : (d : ℤ) ∣ (0 * n - (d : ℤ) * m) := ⟨-m, by ring⟩
      have h2 : (d : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hd
      rw [Int.emod_def]
      exact dvd_sub h1 (h2.mul_right _)
    obtain ⟨e', he'⟩ := hdvd
    have hNz : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
    have hnn : (0 : ℤ) ≤ (0 * n - (d : ℤ) * m) % (N : ℤ) :=
      Int.emod_nonneg _ hNz
    have hto : ((0 * n - (d : ℤ) * m) % (N : ℤ)).toNat = d * e'.toNat := by
      have he'' : (0 * n - (d : ℤ) * m) % (N : ℤ) = (d : ℤ) * e' := he'
      have hepos : (0 : ℤ) ≤ e' := by
        by_contra hneg
        rw [not_le] at hneg
        have : (d : ℤ) * e' < 0 :=
          mul_neg_of_pos_of_neg (by exact_mod_cast hdpos) hneg
        omega
      have he3 : (0 * n - (d : ℤ) * m) % (N : ℤ) = ((d * e'.toNat : ℕ) : ℤ) := by
        rw [he'']
        push_cast
        rw [Int.toNat_of_nonneg hepos]
      rw [he3, Int.toNat_natCast]
    rw [hto, pow_mul, hpow, one_pow]
  have hzero : (d : ℤ) • Q' = 0 := by
    have hzp : (d : ℤ) • Q' = E.zeroPoint t := by
      refine E.weilPairingEval_nondegenerate K t ((d : ℤ) • Q')
        ((E.smul_eq_zero_iff_comp_mulByHom t N _).mp hkill_dQ) ?_
      intro y hy
      have hyz : (N : ℤ) • y = 0 :=
        (E.smul_eq_zero_iff_comp_mulByHom t N y).mpr hy
      exact hpair y hyz
    refine hzp.trans (Subtype.ext ?_)
    exact (E.point_zero_val t).symm
  refine dvd_of_closure_pair_torsion P' Q' d hd hdpos hP' hzero hfull ?_
  exact E.torsion_geometricFibre_rank_two N K t hNK

/-- **[T-EQ-3d-L3c viii]** A field-valued ring hom kills one side of any
complemented ideal pair (the idempotent dichotomy: `e + f = 1`, `e·f = 0`, a
field has no nontrivial idempotent products). -/
theorem field_hom_ker_dichotomy {B : Type} [CommRing B] {K' : Type} [Field K']
    (I J : Ideal B) (hIJ : IsCompl I J) (χ : B →+* K') :
    I ≤ RingHom.ker χ ∨ J ≤ RingHom.ker χ := by
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp
    (show (1 : B) ∈ I ⊔ J from hIJ.sup_eq_top ▸ Submodule.mem_top)
  have hprod : χ e * χ f = 0 := by
    have hmem : e * f ∈ I ⊓ J := ⟨I.mul_mem_right f he, J.mul_mem_left e hf⟩
    rw [hIJ.inf_eq_bot] at hmem
    rw [← map_mul, (Submodule.mem_bot B).mp hmem, map_zero]
  rcases mul_eq_zero.mp hprod with h0 | h0
  · -- `χ e = 0`: every `i ∈ I` satisfies `i = i·e + i·f` with `i·f ∈ I ⊓ J = 0`
    refine Or.inl fun i hi => ?_
    have hif : i * f = 0 := by
      have hmem : i * f ∈ I ⊓ J := ⟨I.mul_mem_right f hi, J.mul_mem_left i hf⟩
      rw [hIJ.inf_eq_bot] at hmem
      exact (Submodule.mem_bot B).mp hmem
    have hi_eq : i = i * e := by
      have h1 : i * (e + f) = i := by rw [hef, mul_one]
      calc i = i * (e + f) := h1.symm
        _ = i * e + i * f := by ring
        _ = i * e := by rw [hif, add_zero]
    show χ i = 0
    rw [hi_eq, map_mul, h0, mul_zero]
  · refine Or.inr fun j hj => ?_
    have hje : j * e = 0 := by
      have hmem : j * e ∈ I ⊓ J := ⟨I.mul_mem_left j he, J.mul_mem_right e hj⟩
      rw [hIJ.inf_eq_bot] at hmem
      exact (Submodule.mem_bot B).mp hmem
    have hj_eq : j = j * f := by
      have h1 : j * (e + f) = j := by rw [hef, mul_one]
      calc j = j * (e + f) := h1.symm
        _ = j * e + j * f := by ring
        _ = j * f := by rw [hje, zero_add]
    show χ j = 0
    rw [hj_eq, map_mul, h0, mul_zero]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c viii]** The kernel of the determinant comultiplication is a
complemented ideal (the roots algebra is semisimple: reduced Artinian over a
field). -/
theorem ker_detCompAlgHom_isCompl (D : GaloisRepData N) [Fact (1 < N)] :
    ∃ J : Ideal (muNRootsAlgebra D : Type 0),
      IsCompl (RingHom.ker (detCompAlgHom D).hom.hom.toRingHom) J := by
  haveI : IsReduced (muNRootsAlgebra D : Type 0) :=
    Algebra.FormallyUnramified.isReduced_of_field ℚ _
  haveI : IsArtinianRing (muNRootsAlgebra D : Type 0) :=
    isArtinian_of_tower ℚ inferInstance
  haveI : IsSemisimpleRing (muNRootsAlgebra D : Type 0) :=
    IsArtinianRing.isSemisimpleRing_of_isReduced _
  exact exists_isCompl _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c ix]** The read-power is kernel-determined: the `K`-read of a
roots-scheme point has `r^d = 1` iff its classifier kills the model element
`root^d − 1` (through the cyclotomic identification). -/
theorem classify_read_pow_eq_one_iff (D : GaloisRepData N) [Fact (1 < N)]
    (K : Type) [Field K] [Algebra ℚ K]
    (φ : Spec (.of K) ⟶ corrSpec (muNRootsContAction D))
    (hφ : φ ≫ corrSpecπ (muNRootsContAction D) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))
    (d : ℕ) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        (muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) φ hφ)
        ^ d = 1 ↔
      (muNRootsAlgebraIso D).inv.hom.hom
          ((AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d - 1) ∈
        RingHom.ker (specPointsEquivAlgHom ℚ
          (corrAlgebra (muNRootsContAction D) : Type 0) K
          ⟨φ, hφ⟩).toRingHom := by
  have hread := muNRootsRead_classify_field D K φ hφ
  rw [hread]
  have hcomp : ∀ z : AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1),
      (specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0) K
        ⟨φ, hφ⟩) ((muNRootsAlgebraIso D).inv.hom.hom z) =
      ((specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0) K
        ⟨φ, hφ⟩).comp (muNRootsAlgebraIso D).inv.hom.hom) z := fun _ => rfl
  constructor
  · intro h1
    refine RingHom.mem_ker.mpr ?_
    refine (hcomp _).trans ?_
    refine (map_sub _ _ _).trans ?_
    refine sub_eq_zero.mpr ?_
    refine (map_pow _ _ _).trans ?_
    refine Eq.trans ?_ (map_one _).symm
    exact (congrArg (· ^ d) (hcomp _)).symm.trans h1
  · intro h0
    have h0' := RingHom.mem_ker.mp h0
    have h1 := ((hcomp _).symm.trans h0')
    have h2 := (map_sub ((specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K
        ⟨φ, hφ⟩).comp (muNRootsAlgebraIso D).inv.hom.hom) _ _).symm.trans
      ((hcomp _).symm.trans h0')
    have h3 := sub_eq_zero.mp h2
    refine Eq.trans (congrArg (· ^ d) (hcomp _)) ?_
    refine Eq.trans (map_pow _ _ _).symm ?_
    exact h3.trans (map_one _)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c x]** A root of unity none of whose proper-divisor powers is
trivial lies in the range of the determinant comparison: its discrete logarithm
along the pinning `p` is a unit (otherwise the `N/gcd` power would already be
trivial). -/
theorem roots_mem_range_detComp_of_pow_ne_one (D : GaloisRepData N)
    [Fact (1 < N)] (ρ : rootsOfUnity N (AlgebraicClosure ℚ))
    (hne : ∀ d ∈ N.properDivisors,
      ((ρ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ d ≠ 1) :
    ρ ∈ Set.range (detCompMor D).hom.hom := by
  set a : ZMod N := (D.p.symm ρ).toAdd with ha
  have hρ : D.p (Multiplicative.ofAdd a) = ρ := by
    rw [ha, ofAdd_toAdd]
    exact D.p.apply_symm_apply ρ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hunit : IsUnit a := by
    by_contra hnu
    have hg : ¬ Nat.Coprime a.val N := by
      intro hcop
      refine hnu ?_
      rw [show a = ((a.val : ℕ) : ZMod N) from by
        rw [ZMod.natCast_val, ZMod.cast_id]]
      exact (ZMod.isUnit_iff_coprime a.val N).mpr hcop
    set g := Nat.gcd a.val N with hgdef
    have hg1 : g ≠ 1 := fun h => hg h
    have hgdvdN : g ∣ N := Nat.gcd_dvd_right a.val N
    have hgdvda : g ∣ a.val := Nat.gcd_dvd_left a.val N
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right a.val hNpos
    have h1g : 1 < g := by omega
    set d := N / g with hddef
    have hd : d ∣ N := Nat.div_dvd_of_dvd hgdvdN
    have hdlt : d < N := Nat.div_lt_self hNpos h1g
    have hdproper : d ∈ N.properDivisors := Nat.mem_properDivisors.mpr ⟨hd, hdlt⟩
    have hmul : d * a.val = N * (a.val / g) := by
      have h2 : a.val = g * (a.val / g) := (Nat.mul_div_cancel' hgdvda).symm
      calc d * a.val = d * (g * (a.val / g)) := by rw [← h2]
        _ = (d * g) * (a.val / g) := by ring
        _ = N * (a.val / g) := by rw [hddef, Nat.div_mul_cancel hgdvdN]
    have h1 : d • a = 0 := by
      rw [nsmul_eq_mul, show a = ((a.val : ℕ) : ZMod N) from by
        rw [ZMod.natCast_val, ZMod.cast_id], ← Nat.cast_mul, hmul,
        Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have hρd : ρ ^ d = 1 := by
      rw [← hρ, ← map_pow,
        show (Multiplicative.ofAdd a) ^ d = Multiplicative.ofAdd (d • a) from
          (ofAdd_nsmul d a).symm,
        h1, ofAdd_zero, map_one]
    refine hne d hdproper ?_
    have hcoe := congrArg
      (fun z : rootsOfUnity N (AlgebraicClosure ℚ) =>
        ((z : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) hρd
    simpa using hcoe
  obtain ⟨u, hu⟩ := hunit
  refine ⟨u, ?_⟩
  show D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) = ρ
  rw [hu]
  exact hρ

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c xi]** A `ℚ̄`-point whose set-read lies in the determinant
range kills the kernel of the determinant comultiplication (lift the read
across the points equivalence, identify the point as a pushforward, and factor
its classifier through the comultiplication). -/
theorem eval_kills_ker_of_read_mem_range (D : GaloisRepData N) [Fact (1 < N)]
    (pt : { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
        corrSpec (muNRootsContAction D) //
      h ≫ corrSpecπ (muNRootsContAction D) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) })
    (hmem : qbarPointsRead (muNRootsContAction D) pt ∈
      Set.range (detCompMor D).hom.hom) :
    RingHom.ker (detCompAlgHom D).hom.hom.toRingHom ≤
      RingHom.ker (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0)
        (AlgebraicClosure ℚ) pt).toRingHom := by
  obtain ⟨u₀, hu₀⟩ := hmem
  set ψ₀ := (qbarPointsRead (cycloUnitsContAction D)).symm u₀ with hψ₀
  have hread : qbarPointsRead (muNRootsContAction D)
      ⟨ψ₀.1 ≫ corrSpecMap (detCompMor D), by
        rw [Category.assoc, corrSpecMap_π, ψ₀.2]⟩ =
      qbarPointsRead (muNRootsContAction D) pt := by
    refine (qbarPointsRead_map (detCompMor D) ψ₀).trans ?_
    rw [hψ₀, Equiv.apply_symm_apply]
    exact hu₀
  have hpt : (⟨ψ₀.1 ≫ corrSpecMap (detCompMor D), by
      rw [Category.assoc, corrSpecMap_π, ψ₀.2]⟩ :
      { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
          corrSpec (muNRootsContAction D) //
        h ≫ corrSpecπ (muNRootsContAction D) =
          Spec.map (CommRingCat.ofHom
            (algebraMap ℚ (AlgebraicClosure ℚ))) }) = pt :=
    (qbarPointsRead (muNRootsContAction D)).injective hread
  have hA : specPointsEquivAlgHom ℚ
      (corrAlgebra (muNRootsContAction D) : Type 0)
      (AlgebraicClosure ℚ) pt =
      (specPointsEquivAlgHom ℚ
        (corrAlgebra (cycloUnitsContAction D) : Type 0)
        (AlgebraicClosure ℚ) ψ₀).comp
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (detCompMor D)).unop.hom.hom := by
    rw [← hpt]
    have hpre := spec_preimage_comp ψ₀.1 (CommRingCat.ofHom
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (detCompMor D)).unop.hom.hom.toRingHom))
    refine AlgHom.ext fun b => ?_
    exact congrArg (fun q : CommRingCat.of
      (corrAlgebra (muNRootsContAction D) : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom b) hpre
  intro i hi
  refine RingHom.mem_ker.mpr ?_
  have h0 : ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (detCompMor D)).unop.hom.hom i = 0 := RingHom.mem_ker.mp hi
  have happ : (specPointsEquivAlgHom ℚ
      (corrAlgebra (muNRootsContAction D) : Type 0)
      (AlgebraicClosure ℚ) pt) i =
      (specPointsEquivAlgHom ℚ
        (corrAlgebra (cycloUnitsContAction D) : Type 0)
        (AlgebraicClosure ℚ) ψ₀)
        (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (detCompMor D)).unop.hom.hom i) :=
    congrArg (fun (F : (corrAlgebra (muNRootsContAction D) : Type 0) →ₐ[ℚ]
      AlgebraicClosure ℚ) => F i) hA
  refine happ.trans ?_
  exact (congrArg _ h0).trans (map_zero _)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c xii]** The classifier's value at the cyclotomic model root
is the set-read of the point (the field-generic classification glued to the
keystone). -/
theorem eval_root_eq_read (D : GaloisRepData N) [Fact (1 < N)]
    (pt : { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
        corrSpec (muNRootsContAction D) //
      h ≫ corrSpecπ (muNRootsContAction D) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) :
    (specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0)
        (AlgebraicClosure ℚ) pt)
      ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) =
    (((qbarPointsRead (muNRootsContAction D) pt :
      rootsOfUnity N (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)ˣ) :
      AlgebraicClosure ℚ) := by
  refine Eq.trans (muNRootsRead_classify_field D (AlgebraicClosure ℚ)
    pt.1 pt.2).symm ?_
  exact muNRoots_correspondence_read D pt.1 pt.2

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c xiii]** The non-primitivity product annihilates any
determinant-kernel part of a complement decomposition: every `ℚ̄`-evaluation
kills `(∏ (root^d − 1)) · e` — an evaluation either kills the determinant
kernel (so kills `e`), or kills the complement, in which case its read cannot
be primitive (else it would kill both sides), so a product factor vanishes —
and evaluations separate points of the reduced algebra. -/
theorem prod_mul_e_eq_zero (D : GaloisRepData N) [Fact (1 < N)]
    (J : Ideal (muNRootsAlgebra D : Type 0))
    (hIJ : IsCompl (RingHom.ker (detCompAlgHom D).hom.hom.toRingHom) J)
    (e f : (muNRootsAlgebra D : Type 0))
    (he : e ∈ RingHom.ker (detCompAlgHom D).hom.hom.toRingHom) (hf : f ∈ J)
    (hef : e + f = 1) :
    (∏ d ∈ N.properDivisors,
      ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d - 1))
      * e = 0 := by
  by_contra hne
  obtain ⟨χ, hχ⟩ := corrAlgebra_exists_eval_ne (muNRootsContAction D) hne
  rcases field_hom_ker_dichotomy
    (RingHom.ker (detCompAlgHom D).hom.hom.toRingHom) J hIJ χ.toRingHom
    with hkI | hkJ
  · exact hχ ((map_mul χ _ _).trans
      (mul_eq_zero_of_right _ (RingHom.mem_ker.mp (hkI he))))
  · have hχf : χ f = 0 := RingHom.mem_ker.mp (hkJ hf)
    have hχe : χ e = 1 :=
      ((add_zero (χ e)).symm.trans
        (congrArg (HAdd.hAdd (χ e)) hχf.symm)).trans
        (((map_add χ e f).symm.trans (congrArg χ hef)).trans (map_one χ))
    set pt := (specPointsEquivAlgHom ℚ
      (corrAlgebra (muNRootsContAction D) : Type 0)
      (AlgebraicClosure ℚ)).symm χ with hptdef
    have hχpt : specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0)
        (AlgebraicClosure ℚ) pt = χ := by
      rw [hptdef]
      exact Equiv.apply_symm_apply _ χ
    have hroot : χ ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) =
        (((qbarPointsRead (muNRootsContAction D) pt :
          rootsOfUnity N (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) := by
      rw [← hχpt]
      exact eval_root_eq_read D pt
    by_cases hprim : ∃ d₀ ∈ N.properDivisors,
        (((qbarPointsRead (muNRootsContAction D) pt :
          rootsOfUnity N (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)ˣ) :
          AlgebraicClosure ℚ) ^ d₀ = 1
    · obtain ⟨d₀, hd₀mem, hd₀⟩ := hprim
      have hfac : χ (((muNRootsAlgebraIso D).inv.hom.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d₀ - 1 :
            (muNRootsAlgebra D : Type 0)))
          = 0 :=
        (map_sub χ _ _).trans
          ((congrArg (· - χ 1) (map_pow χ _ d₀)).trans
            ((congrArg (fun z => z ^ d₀ - χ 1) hroot).trans
              ((congrArg (· - χ 1) hd₀).trans
                ((congrArg (HSub.hSub (1 : AlgebraicClosure ℚ))
                  (map_one χ)).trans (sub_self 1)))))
      refine hχ ?_
      refine (map_mul χ _ _).trans ?_
      refine ((congrArg (HMul.hMul _) hχe).trans (mul_one _)).trans ?_
      refine (map_prod χ _ _).trans ?_
      exact Finset.prod_eq_zero hd₀mem hfac
    · have hall : ∀ d ∈ N.properDivisors,
          (((qbarPointsRead (muNRootsContAction D) pt :
            rootsOfUnity N (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)ˣ) :
            AlgebraicClosure ℚ) ^ d ≠ 1 :=
        fun d hd hcontra => hprim ⟨d, hd, hcontra⟩
      have hmem := roots_mem_range_detComp_of_pow_ne_one D
        (qbarPointsRead (muNRootsContAction D) pt) hall
      have hkills := eval_kills_ker_of_read_mem_range D pt hmem
      have hχe0 : χ e = 0 := by
        rw [← hχpt]
        exact RingHom.mem_ker.mp (hkills he)
      rw [hχe0] at hχe
      exact zero_ne_one hχe

/-- **[T-EQ-3d-L3c xiv-prep]** The geometric field at a point: the algebraic
closure of the residue field. -/
noncomputable abbrev geomResidue (T : Scheme.{0}) (x : T) : Type 0 :=
  AlgebraicClosure ↑(T.residueField x)

/-- **[T-EQ-3d-L3c xiv-prep]** The geometric point through `x`. -/
noncomputable def geomPt (T : Scheme.{0}) (x : T) :
    Spec (CommRingCat.of (geomResidue T x)) ⟶ T :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ↑(T.residueField x) (geomResidue T x))) ≫
    T.fromSpecResidueField x

theorem geomPt_base (T : Scheme.{0}) (x : T)
    (s : Spec (CommRingCat.of (geomResidue T x))) :
    (geomPt T x).base s = x := by
  show (T.fromSpecResidueField x).base ((Spec.map (CommRingCat.ofHom
    (algebraMap ↑(T.residueField x) (geomResidue T x)))).base s) = x
  exact Scheme.fromSpecResidueField_apply x _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c xiv]** A `K`-point whose read has no trivial proper-divisor
power kills the determinant kernel: the kernel dichotomy's right case is
refuted by the annihilation identity `P₀·e = 0` (each factor of the
non-primitivity product evaluates away from zero). -/
theorem eval_kills_ker_of_pow_ne_one (D : GaloisRepData N) [Fact (1 < N)]
    {K : Type} [Field K] [Algebra ℚ K]
    (φ : Spec (.of K) ⟶ corrSpec (muNRootsContAction D))
    (hφ : φ ≫ corrSpecπ (muNRootsContAction D) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))
    (hpow : ∀ d ∈ N.properDivisors,
      (specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0) K
          ⟨φ, hφ⟩)
        ((muNRootsAlgebraIso D).inv.hom.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d ≠ 1) :
    RingHom.ker (detCompAlgHom D).hom.hom.toRingHom ≤
      RingHom.ker (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩).toRingHom := by
  obtain ⟨J, hIJ⟩ := ker_detCompAlgHom_isCompl D
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp
    (show (1 : (muNRootsAlgebra D : Type 0)) ∈
      RingHom.ker (detCompAlgHom D).hom.hom.toRingHom ⊔ J from
      hIJ.sup_eq_top ▸ Submodule.mem_top)
  rcases field_hom_ker_dichotomy
    (RingHom.ker (detCompAlgHom D).hom.hom.toRingHom) J hIJ
    (specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0) K
      ⟨φ, hφ⟩).toRingHom with hkI | hkJ
  · exact hkI
  · exfalso
    have hχf : (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩) f = 0 :=
      RingHom.mem_ker.mp (hkJ hf)
    have hχe : (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩) e = 1 := by
      refine Eq.trans ?_
        (((map_add (specPointsEquivAlgHom ℚ
          (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩) e f).symm.trans
          (congrArg (specPointsEquivAlgHom ℚ
            (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩)
            hef)).trans (map_one _))
      exact (add_zero _).symm.trans (congrArg (HAdd.hAdd _) hχf.symm)
    have hP₀e := prod_mul_e_eq_zero D J hIJ e f he hf hef
    have h0 : (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩)
        ((∏ d ∈ N.properDivisors,
          ((muNRootsAlgebraIso D).inv.hom.hom
            (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d - 1))
          * e) = 0 :=
      (congrArg _ hP₀e).trans (map_zero _)
    have h1 : (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩)
        (∏ d ∈ N.properDivisors,
          (((muNRootsAlgebraIso D).inv.hom.hom
            (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d - 1 :
            (muNRootsAlgebra D : Type 0)))) *
        (specPointsEquivAlgHom ℚ
          (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩) e = 0 :=
      (map_mul _ _ _).symm.trans h0
    have h2 : (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩)
        (∏ d ∈ N.properDivisors,
          (((muNRootsAlgebraIso D).inv.hom.hom
            (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d - 1 :
            (muNRootsAlgebra D : Type 0))))
        = 0 :=
      (mul_one _).symm.trans ((congrArg (HMul.hMul _) hχe.symm).trans h1)
    have h4 : ∏ d ∈ N.properDivisors,
        (specPointsEquivAlgHom ℚ
          (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩)
          (((muNRootsAlgebraIso D).inv.hom.hom
            (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d - 1 :
            (muNRootsAlgebra D : Type 0))) = 0 :=
      (map_prod _ _ _).symm.trans h2
    obtain ⟨d₁, hd₁mem, hd₁⟩ := Finset.prod_eq_zero_iff.mp h4
    have hfac : (specPointsEquivAlgHom ℚ
        (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩)
        (((muNRootsAlgebraIso D).inv.hom.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ d₁ - 1 :
          (muNRootsAlgebra D : Type 0))) =
        (specPointsEquivAlgHom ℚ
          (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩)
          ((muNRootsAlgebraIso D).inv.hom.hom
            (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d₁ - 1 :=
      (map_sub _ _ _).trans
        ((congrArg (· - (specPointsEquivAlgHom ℚ
          (corrAlgebra (muNRootsContAction D) : Type 0) K ⟨φ, hφ⟩) 1)
          (map_pow _ _ d₁)).trans
          (congrArg (HSub.hSub _) (map_one _)))
    exact hpow d₁ hd₁mem (sub_eq_zero.mp (hfac.symm.trans hd₁))

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c xv]** A `K`-point of the roots spectrum whose classifier kills
the determinant kernel lands in the range of the clopen determinant piece: lift
the classifier along the surjective comultiplication and take the spectrum. -/
theorem base_mem_range_detComp_of_ker_le (D : GaloisRepData N) [Fact (1 < N)]
    {K : Type} [Field K]
    (φ : Spec (.of K) ⟶ corrSpec (muNRootsContAction D))
    (hker : RingHom.ker (detCompAlgHom D).hom.hom.toRingHom ≤
      RingHom.ker (Spec.preimage φ).hom)
    (s₀ : Spec (CommRingCat.of K)) :
    φ.base s₀ ∈ Set.range (detCompScheme D).base := by
  obtain ⟨sec, hsec⟩ := (detCompAlgHom_surjective D).hasRightInverse
  have hcomp : ((detCompAlgHom D).hom.hom.toRingHom.liftOfRightInverse sec hsec
      ⟨(Spec.preimage φ).hom, hker⟩).comp
      (detCompAlgHom D).hom.hom.toRingHom = (Spec.preimage φ).hom :=
    RingHom.liftOfRightInverse_comp _ sec hsec _
  have h5 : CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom ((detCompAlgHom D).hom.hom.toRingHom.liftOfRightInverse
        sec hsec ⟨(Spec.preimage φ).hom, hker⟩) = Spec.preimage φ :=
    CommRingCat.hom_ext hcomp
  have hfact : Spec.map (CommRingCat.ofHom
      ((detCompAlgHom D).hom.hom.toRingHom.liftOfRightInverse sec hsec
        ⟨(Spec.preimage φ).hom, hker⟩)) ≫ detCompScheme D = φ :=
    (Spec.map_comp (CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom)
      (CommRingCat.ofHom
        ((detCompAlgHom D).hom.hom.toRingHom.liftOfRightInverse sec hsec
          ⟨(Spec.preimage φ).hom, hker⟩))).symm.trans
      ((congrArg Spec.map h5).trans (Spec.map_preimage φ))
  refine ⟨(Spec.map (CommRingCat.ofHom
    ((detCompAlgHom D).hom.hom.toRingHom.liftOfRightInverse sec hsec
      ⟨(Spec.preimage φ).hom, hker⟩))).base s₀, ?_⟩
  exact congrArg (fun (m : Spec (CommRingCat.of K) ⟶
    corrSpec (muNRootsContAction D)) => m.base s₀) hfact

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c xvi]** PRIMITIVITY per point: the value-level pairing
comparison of a full level structure lands in the determinant range at every
point. Localise at the algebraic closure of the residue field: there the read
is the Weil pairing of a generating torsion pair (base-change naturality), whose
proper-divisor powers are nontrivial (nondegeneracy through the symplectic
register plus the rank-two count), so the classifier kills the determinant
kernel and the point factors through the clopen piece. -/
theorem pairEZ_base_mem_range (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (L : E.FullLevelPt N) (x : T) :
    (pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2).base x ∈
      Set.range (detCompScheme D).base := by
  classical
  letI : Algebra ℚ ↑(T.residueField x) :=
    ((Spec.preimage (T.fromSpecResidueField x ≫ sT)).hom).toAlgebra
  letI : Algebra ℚ (geomResidue T x) :=
    ((algebraMap ↑(T.residueField x) (geomResidue T x)).comp
      (algebraMap ℚ ↑(T.residueField x))).toAlgebra
  haveI : CharZero (geomResidue T x) :=
    charZero_of_injective_algebraMap
      (RingHom.injective (algebraMap ℚ (geomResidue T x)))
  have hcompatL : T.fromSpecResidueField x ≫ sT =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ↑(T.residueField x))) := by
    rw [show CommRingCat.ofHom (algebraMap ℚ ↑(T.residueField x)) =
      Spec.preimage (T.fromSpecResidueField x ≫ sT) from rfl, Spec.map_preimage]
  have hqK : geomPt T x ≫ sT =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (geomResidue T x))) := by
    show (Spec.map (CommRingCat.ofHom
      (algebraMap ↑(T.residueField x) (geomResidue T x))) ≫
      T.fromSpecResidueField x) ≫ sT = _
    rw [Category.assoc, hcompatL, ← Spec.map_comp]
    rfl
  have hφKπ : (geomPt T x ≫ pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2) ≫
      corrSpecπ (muNRootsContAction D) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (geomResidue T x))) := by
    rw [Category.assoc]
    rw [show pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 ≫
        corrSpecπ (muNRootsContAction D) = sT from
      pairEZMap_π D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2]
    exact hqK
  have hpow_ne : ∀ d ∈ N.properDivisors,
      (specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0)
          (geomResidue T x)
          ⟨geomPt T x ≫ pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2, hφKπ⟩)
        ((muNRootsAlgebraIso D).inv.hom.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d ≠ 1 := by
    intro d hd hcon
    rw [Nat.mem_properDivisors] at hd
    have hζ := muNRootsRead_classify_field D (geomResidue T x)
      (geomPt T x ≫ pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2) hφKπ
    have hii : ∀ z : Γ(Spec (CommRingCat.of (geomResidue T x)), ⊤),
        (Scheme.ΓSpecIso (CommRingCat.of (geomResidue T x))).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (geomResidue T x))).hom.hom z) =
          z := fun z =>
      congrArg (fun (q : Γ(Spec (CommRingCat.of (geomResidue T x)), ⊤) ⟶
        Γ(Spec (CommRingCat.of (geomResidue T x)), ⊤)) => q.hom z)
        (Scheme.ΓSpecIso (CommRingCat.of (geomResidue T x))).hom_inv_id
    have hΓ : muNRootsRead D (Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (geomResidue T x))))
        (geomPt T x ≫ pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2) hφKπ ^ d
        = 1 :=
      ((hii _).symm.trans (congrArg
        (Scheme.ΓSpecIso (CommRingCat.of (geomResidue T x))).inv.hom
        ((map_pow (Scheme.ΓSpecIso
          (CommRingCat.of (geomResidue T x))).hom.hom _ d).trans
          ((congrArg (· ^ d) hζ).trans hcon)))).trans
        (map_one (Scheme.ΓSpecIso (CommRingCat.of (geomResidue T x))).inv.hom)
    have hread := pairEZ_read_eval D (geomResidue T x) sT E L (geomPt T x) hqK
    have hΓ2 : ((Scheme.Γ.map (geomPt T x).op).hom
        (E.weilPairingEval L.1.1 L.1.2
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.1).mp L.2.1.1)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.2).mp L.2.1.2)).1) ^ d
        = 1 :=
      (congrArg (· ^ d) hread.symm).trans hΓ
    have hres1 : (EllipticCurve.Point.restrict E (geomPt T x) L.1.1).1 ≫ E.mulByHom N =
        (geomPt T x ≫ 𝟙 T) ≫ E.zero := by
      show (geomPt T x ≫ (L.1.1).1) ≫ E.mulByHom N =
        (geomPt T x ≫ 𝟙 T) ≫ E.zero
      rw [Category.assoc,
        (E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.1).mp L.2.1.1,
        ← Category.assoc]
    have hres2 : (EllipticCurve.Point.restrict E (geomPt T x) L.1.2).1 ≫ E.mulByHom N =
        (geomPt T x ≫ 𝟙 T) ≫ E.zero := by
      show (geomPt T x ≫ (L.1.2).1) ≫ E.mulByHom N =
        (geomPt T x ≫ 𝟙 T) ≫ E.zero
      rw [Category.assoc,
        (E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.2).mp L.2.1.2,
        ← Category.assoc]
    have hres := E.weilPairingEval_restrict (geomPt T x) L.1.1 L.1.2
      ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.1).mp L.2.1.1)
      ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.2).mp L.2.1.2)
      hres1 hres2
    have hΓ3 : (E.weilPairingEval (EllipticCurve.Point.restrict E (geomPt T x) L.1.1)
        (EllipticCurve.Point.restrict E (geomPt T x) L.1.2) hres1 hres2).1 ^ d = 1 :=
      (congrArg (· ^ d) hres).trans hΓ2
    have hpull1 : (EllipticCurve.Point.pull E (geomPt T x) L.1.1).1 ≫ E.mulByHom N =
        geomPt T x ≫ E.zero := by
      show (geomPt T x ≫ (L.1.1).1) ≫ E.mulByHom N = geomPt T x ≫ E.zero
      rw [Category.assoc,
        (E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.1).mp L.2.1.1,
        ← Category.assoc, Category.comp_id]
    have hpull2 : (EllipticCurve.Point.pull E (geomPt T x) L.1.2).1 ≫ E.mulByHom N =
        geomPt T x ≫ E.zero := by
      show (geomPt T x ≫ (L.1.2).1) ≫ E.mulByHom N = geomPt T x ≫ E.zero
      rw [Category.assoc,
        (E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.2).mp L.2.1.2,
        ← Category.assoc, Category.comp_id]
    have hraw := weilPairingEval_congr_raw (E := E)
      (Category.comp_id (geomPt T x)) rfl rfl hres1 hres2 hpull1 hpull2
    have hΓ4 : (E.weilPairingEval (EllipticCurve.Point.pull E (geomPt T x) L.1.1)
        (EllipticCurve.Point.pull E (geomPt T x) L.1.2) hpull1 hpull2).1 ^ d = 1 :=
      (congrArg (· ^ d) hraw.symm).trans hΓ3
    have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hNK : ((N : ℕ) : geomResidue T x) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne N)
    have horder := weilPairing_pair_order (geomResidue T x) (geomPt T x)
      (EllipticCurve.Point.pull E (geomPt T x) L.1.1) (EllipticCurve.Point.pull E (geomPt T x) L.1.2)
      ((E.smul_eq_zero_iff_comp_mulByHom (geomPt T x) N _).mpr hpull1)
      ((E.smul_eq_zero_iff_comp_mulByHom (geomPt T x) N _).mpr hpull2)
      (L.2.2 (geomResidue T x) (geomPt T x)) hNK d hd.1
      (Nat.pos_of_dvd_of_pos hd.1 hNpos) hΓ4
    have hled : N ≤ d :=
      Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd.1 hNpos) horder
    omega
  have hker0 := eval_kills_ker_of_pow_ne_one D
    (geomPt T x ≫ pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2) hφKπ hpow_ne
  have hker : RingHom.ker (detCompAlgHom D).hom.hom.toRingHom ≤
      RingHom.ker (Spec.preimage (geomPt T x ≫
        pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2)).hom := by
    intro i hi
    exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp (hker0 hi))
  obtain ⟨s₀⟩ : Nonempty (Spec (CommRingCat.of (geomResidue T x))) :=
    inferInstance
  have hmem := base_mem_range_detComp_of_ker_le D
    (geomPt T x ≫ pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2) hker s₀
  have hpt : (geomPt T x ≫
      pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2).base s₀ =
      (pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2).base x := by
    show (pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2).base
      ((geomPt T x).base s₀) =
      (pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2).base x
    rw [geomPt_base]
  rw [← hpt]
  exact hmem

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-L3c]** THE FACTORING: the value-level pairing comparison of a
full level structure factors through the determinant clopen piece (pointwise
primitivity + the open-immersion lift). -/
theorem pairEZMap_factors_detComp (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (L : E.FullLevelPt N) :
    ∃ w : T ⟶ cycloUnitsScheme D,
      w ≫ detCompScheme D = pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 := by
  refine factors_detComp_of_range D _ ?_
  rintro _ ⟨x, rfl⟩
  exact pairEZ_base_mem_range D sT E L x

end CorrSurjective

section SectionsToStructures

open scoped FintypeCatDiscrete

variable (D : GaloisRepData N) [Fact (1 < N)] {X : EllObj (CommRingCat.of ℚ)}
variable (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
variable [IsAffineHom d.f]
variable {T' : Scheme.{0}} (k : T' ⟶ X.base)
variable (s : T' ⟶ d.σZ.relQuotient d.f d.over_base)

/-- **[T-EQ-3c main]** The section cover: the base change of the quotient
projection along a section of the quotient. -/
noncomputable def secCover :
    pullback (d.σZ.relQuotientπ d.f d.over_base) s ⟶ T' :=
  pullback.snd _ s

/-- **[T-EQ-3c main]** The tautological lift of the section cover into the
framed total space. -/
noncomputable def secLift :
    pullback (d.σZ.relQuotientπ d.f d.over_base) s ⟶ d.Z :=
  pullback.fst _ s

/-- The lift classifies over the covered base. -/
theorem secLift_f (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k) :
    secLift D d s ≫ d.f = secCover D d s ≫ k := by
  refine Eq.trans (congrArg (secLift D d s ≫ ·)
    (d.σZ.relQuotientπ_comp_relQuotientStruct d.f d.over_base).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ d.σZ.relQuotientStruct d.f d.over_base)
    pullback.condition) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (secCover D d s ≫ ·) hs

/-- **[T-EQ-3c main]** The symplectically framed value classified by the lifted
section. -/
noncomputable def secValue
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k) :
    (sympFramedProblem D).obj
      (Opposite.op (X.pullbackAlong (secCover D d s ≫ k))) :=
  d.eqv (secCover D d s ≫ k) ⟨secLift D d s, secLift_f D d k s hs⟩

/-- **[T-EQ-3c main]** The classified value transported to the double base
change (the descent-input presentation). -/
noncomputable def secW
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k) :
    (sympFramedProblem D).obj
      (Opposite.op ((X.pullbackAlong k).pullbackAlong (secCover D d s))) :=
  (sympFramedProblem D).map (pullbackAlongAssocHom X k (secCover D d s)).op
    (secValue D d k s hs)

/-- **[T-EQ-3c main]** The local ρ-level structure on the section cover, from
the carve condition of the transported value. -/
noncomputable def secStruct
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N) :
    RhoLevelStructure D
      ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap
      ((X.pullbackAlong k).pullbackAlong (secCover D d s)).curve :=
  rhoLevelStructureOfCarve D
    ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap
    ((X.pullbackAlong k).pullbackAlong (secCover D d s)).curve hinv
    (secW D d k s hs).val.1 (secW D d k s hs).val.2.val
    (secW D d k s hs).val.2.property (secW D d k s hs).property

/-- **[T-EQ-3c main]** The `γ`-translation of the section cover (the pulled
`σZ`-action). -/
noncomputable def secSmul (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    pullback (d.σZ.relQuotientπ d.f d.over_base) s ⟶
      pullback (d.σZ.relQuotientπ d.f d.over_base) s :=
  d.σZ.pullbackRelQSMul d.f d.over_base s γ

theorem secSmul_secCover (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    secSmul D d s γ ≫ secCover D d s = secCover D d s :=
  d.σZ.pullbackRelQSMul_snd d.f d.over_base s γ

theorem secSmul_secLift (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    secSmul D d s γ ≫ secLift D d s = secLift D d s ≫ d.σZ.hom γ :=
  d.σZ.pullbackRelQSMul_fst d.f d.over_base s γ

/-- **[T-EQ-3c main]** The `γ`-translation as an `Ell/ℚ`-endomorphism of the
double base change. -/
noncomputable def secGSmul (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (X.pullbackAlong k).pullbackAlong (secCover D d s) ⟶
      (X.pullbackAlong k).pullbackAlong (secCover D d s) :=
  pullbackAlongMapOf (X.pullbackAlong k) (secSmul D d s γ)
    (secSmul_secCover D d s γ)

/-- **[T-EQ-3c main]** The `γ`-translation on the `V_ρ`-side pullback (trivial
on the `V_ρ`-coordinate). -/
noncomputable def secVSmul (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    pullback (vRhoπ D)
        ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap ⟶
      pullback (vRhoπ D)
        ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap :=
  pullback.map _ _ _ _ (𝟙 (vRho D)) (secSmul D d s γ)
    (𝟙 (Spec (CommRingCat.of ℚ)))
    (by rw [Category.comp_id, Category.id_comp])
    (by
      show ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap ≫
          𝟙 _ = secSmul D d s γ ≫
        ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap
      rw [Category.comp_id]
      show ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap =
        secSmul D d s γ ≫ secCover D d s ≫ (X.pullbackAlong k).structMap
      rw [← Category.assoc, secSmul_secCover]
      rfl)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3c main, THE CONJUGATION]** The torsion-level `γ`-translation
intertwines the local trivialization with the `V_ρ`-side `γ`-translation: the
coordinate leg is `γ`-invariant (the `w`-level equivariance turns the pulled
data into the `γ`-translated data, and the pinned iso is translation-invariant),
and the base leg twists by `secSmul γ`. -/
theorem secTorsion_smul_conj
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    torsionMapOfEllHom (secGSmul D d k s γ) N ≫
        (secStruct D d k s hs hinv).torsionIso.hom =
      (secStruct D d k s hs hinv).torsionIso.hom ≫ secVSmul D d k s γ := by
  have hw := w_smul_translate D d k (secCover D d s)
    ⟨secLift D d s, secLift_f D d k s hs⟩ (secSmul D d s γ)
    (secSmul_secCover D d s γ) γ (secSmul_secLift D d s γ)
  have hP : ((((X.pullbackAlong k).pullbackAlong
      (secCover D d s)).curve.glSmul γ (secW D d k s hs).val.1)).1.1 =
      EllHom.pullSection (CommRingCat.of ℚ) (secGSmul D d k s γ)
        (secW D d k s hs).val.1.1.1 :=
    (congrArg (fun z => z.val.1.1.1) hw).symm
  have hQ : ((((X.pullbackAlong k).pullbackAlong
      (secCover D d s)).curve.glSmul γ (secW D d k s hs).val.1)).1.2 =
      EllHom.pullSection (CommRingCat.of ℚ) (secGSmul D d k s γ)
        (secW D d k s hs).val.1.1.2 :=
    (congrArg (fun z => z.val.1.1.2) hw).symm
  have hframe : secSmul D d s γ ≫ (secW D d k s hs).val.2.val =
      (secW D d k s hs).val.2.val ≫ wFramesRightMul D γ :=
    congrArg (fun z => z.val.2.val) hw
  apply pullback.hom_ext
  · show torsionMapOfEllHom (secGSmul D d k s γ) N ≫
        (secStruct D d k s hs hinv).torsionIso.hom ≫
        pullback.fst (vRhoπ D) _ =
      (secStruct D d k s hs hinv).torsionIso.hom ≫ secVSmul D d k s γ ≫
        pullback.fst (vRhoπ D) _
    rw [show secVSmul D d k s γ ≫ pullback.fst (vRhoπ D)
        ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap =
        pullback.fst (vRhoπ D) _ ≫ 𝟙 (vRho D) from pullback.lift_fst _ _ _,
      Category.comp_id]
    show torsionMapOfEllHom (secGSmul D d k s γ) N ≫
        framedCoordMap D _ _ hinv (secW D d k s hs).val.1
          (secW D d k s hs).val.2.val (secW D d k s hs).val.2.property =
      framedCoordMap D _ _ hinv (secW D d k s hs).val.1
        (secW D d k s hs).val.2.val (secW D d k s hs).val.2.property
    refine Eq.trans (framedCoordMap_mapAlong D (secGSmul D d k s γ) hinv hinv
      (secW D d k s hs).val.1
      (((X.pullbackAlong k).pullbackAlong
        (secCover D d s)).curve.glSmul γ (secW D d k s hs).val.1)
      hP hQ (secW D d k s hs).val.2.val
      (secW D d k s hs).val.2.property) ?_
    refine Eq.trans (framedCoordMap_congr_frame D _ _ hinv
      (((X.pullbackAlong k).pullbackAlong
        (secCover D d s)).curve.glSmul γ (secW D d k s hs).val.1)
      hframe _) ?_
    exact framedCoordMap_glSmul D _ _ hinv (secW D d k s hs).val.1
      (secW D d k s hs).val.2.val (secW D d k s hs).val.2.property γ
  · show torsionMapOfEllHom (secGSmul D d k s γ) N ≫
        (secStruct D d k s hs hinv).torsionIso.hom ≫
        pullback.snd (vRhoπ D) _ =
      (secStruct D d k s hs hinv).torsionIso.hom ≫ secVSmul D d k s γ ≫
        pullback.snd (vRhoπ D) _
    rw [show secVSmul D d k s γ ≫ pullback.snd (vRhoπ D)
        ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap =
        pullback.snd (vRhoπ D) _ ≫ secSmul D d s γ from pullback.lift_snd _ _ _]
    rw [show (secStruct D d k s hs hinv).torsionIso.hom ≫
        pullback.snd (vRhoπ D) _ =
        ((X.pullbackAlong k).pullbackAlong
          (secCover D d s)).curve.torsionπ N from
      (secStruct D d k s hs hinv).over_T]
    refine Eq.trans (torsionMapOfEllHom_π (secGSmul D d k s γ) N) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (· ≫ secSmul D d s γ) (secStruct D d k s hs hinv).over_T

/-- The `V_ρ`-side translation is killed by the cover projection. -/
theorem secVSmul_prj (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    secVSmul D d k s γ ≫ vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) =
      vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (secVSmul D d k s γ ≫ ·)
      (vRhoCoverPrj_fst D (X.pullbackAlong k) (secCover D d s))) ?_
    refine Eq.trans ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) ?_
    exact (vRhoCoverPrj_fst D (X.pullbackAlong k) (secCover D d s)).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (secVSmul D d k s γ ≫ ·)
      (vRhoCoverPrj_snd D (X.pullbackAlong k) (secCover D d s))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ secCover D d s)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.snd (vRhoπ D) _ ≫ ·)
      (secSmul_secCover D d s γ)) ?_
    exact (vRhoCoverPrj_snd D (X.pullbackAlong k) (secCover D d s)).symm

/-- **[T-EQ-3c main]** `γ`-invariance of the coordinate-projection composite
(the map the descent factors). -/
theorem secFleg_smul
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    torsionMapOfEllHom (secGSmul D d k s γ) N ≫
        (secStruct D d k s hs hinv).torsionIso.hom ≫
        vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) =
      (secStruct D d k s hs hinv).torsionIso.hom ≫
        vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (· ≫ vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s))
    (secTorsion_smul_conj D d k s hs hinv γ)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg ((secStruct D d k s hs hinv).torsionIso.hom ≫ ·)
    (secVSmul_prj D d k s γ)

/-- The `γ`-translation is killed by the projection to the middle base
change. -/
theorem secGSmul_π (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    secGSmul D d k s γ ≫
        (X.pullbackAlong k).pullbackAlongπ (secCover D d s) =
      (X.pullbackAlong k).pullbackAlongπ (secCover D d s) := by
  refine EllHom.ext ?_ ?_
  · show secSmul D d s γ ≫ secCover D d s = secCover D d s
    exact secSmul_secCover D d s γ
  · show (secGSmul D d k s γ).top ≫
        pullback.fst (X.pullbackAlong k).curve.π (secCover D d s) =
      pullback.fst (X.pullbackAlong k).curve.π (secCover D d s)
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The torsion-level `γ`-translation is killed by the torsion cover map. -/
theorem secTorsionSmul_cover
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    torsionMapOfEllHom (secGSmul D d k s γ) N ≫
        torsionMapOfEllHom
          ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N =
      torsionMapOfEllHom
        ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N := by
  refine Eq.trans (torsionMapOfEllHom_comp (secGSmul D d k s γ)
    ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N).symm ?_
  exact congrArg (torsionMapOfEllHom · N) (secGSmul_π D d k s γ)

/-- **[T-EQ-3c main]** The torsion cover is the base change of the quotient
projection along the torsion-level section composite (pasting the cartesian
torsion square with the section-cover square). -/
theorem secTorsionPB :
    IsPullback
      (((X.pullbackAlong k).pullbackAlong
        (secCover D d s)).curve.torsionπ N ≫ secLift D d s)
      (torsionMapOfEllHom
        ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N)
      (d.σZ.relQuotientπ d.f d.over_base)
      ((X.pullbackAlong k).curve.torsionπ N ≫ s) :=
  (isPullback_torsionMapOfEllHom
    ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N).flip.paste_horiz
    (IsPullback.of_hasPullback (d.σZ.relQuotientπ d.f d.over_base) s)

/-- The torsion-level `γ`-translation is conjugate, under the pasting
identification, to the pulled quotient action. -/
theorem secTorsionSmul_u (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    torsionMapOfEllHom (secGSmul D d k s γ) N ≫
        (secTorsionPB D d k s).isoPullback.hom =
      (secTorsionPB D d k s).isoPullback.hom ≫
        d.σZ.pullbackRelQSMul d.f d.over_base
          ((X.pullbackAlong k).curve.torsionπ N ≫ s) γ := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (torsionMapOfEllHom (secGSmul D d k s γ) N ≫ ·)
      (secTorsionPB D d k s).isoPullback_hom_fst) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ secLift D d s)
      (torsionMapOfEllHom_π (secGSmul D d k s γ) N)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      (((X.pullbackAlong k).pullbackAlong
        (secCover D d s)).curve.torsionπ N ≫ ·)
      (secSmul_secLift D d s γ)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      ((secTorsionPB D d k s).isoPullback.hom ≫ ·)
      (d.σZ.pullbackRelQSMul_fst d.f d.over_base
        ((X.pullbackAlong k).curve.torsionπ N ≫ s) γ)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ d.σZ.hom γ)
      (secTorsionPB D d k s).isoPullback_hom_fst) ?_
    exact Category.assoc _ _ _
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (torsionMapOfEllHom (secGSmul D d k s γ) N ≫ ·)
      (secTorsionPB D d k s).isoPullback_hom_snd) ?_
    refine Eq.trans (secTorsionSmul_cover D d k s γ) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      ((secTorsionPB D d k s).isoPullback.hom ≫ ·)
      (d.σZ.pullbackRelQSMul_snd d.f d.over_base
        ((X.pullbackAlong k).curve.torsionπ N ≫ s) γ)) ?_
    exact (secTorsionPB D d k s).isoPullback_hom_snd

/-- **[T-EQ-3c main]** The coordinate-projection composite descends through the
torsion cover: the `γ`-invariance (`secFleg_smul`) discharges the invariant-lift
criterion of the free quotient. -/
theorem secFleg_factors
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N) :
    ∃ q : (X.pullbackAlong k).curve.torsion N ⟶
        pullback (vRhoπ D) (X.pullbackAlong k).structMap,
      torsionMapOfEllHom
          ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N ≫ q =
        (secStruct D d k s hs hinv).torsionIso.hom ≫
          vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) := by
  have hswap : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N),
      d.σZ.pullbackRelQSMul d.f d.over_base
          ((X.pullbackAlong k).curve.torsionπ N ≫ s) γ ≫
        (secTorsionPB D d k s).isoPullback.inv =
      (secTorsionPB D d k s).isoPullback.inv ≫
        torsionMapOfEllHom (secGSmul D d k s γ) N := by
    intro γ
    rw [Iso.comp_inv_eq, Category.assoc, secTorsionSmul_u,
      Iso.inv_hom_id_assoc]
  obtain ⟨q, hq⟩ := d.σZ.exists_relQuotientπ_lift_baseChange d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D))
    ((X.pullbackAlong k).curve.torsionπ N ≫ s)
    ((secTorsionPB D d k s).isoPullback.inv ≫
      (secStruct D d k s hs hinv).torsionIso.hom ≫
      vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s))
    (fun γ => by
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg
        (· ≫ (secStruct D d k s hs hinv).torsionIso.hom ≫
          vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s))
        (hswap γ)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg ((secTorsionPB D d k s).isoPullback.inv ≫ ·)
        (secFleg_smul D d k s hs hinv γ))
  refine ⟨q, ?_⟩
  refine Eq.trans (congrArg (· ≫ q)
    (secTorsionPB D d k s).isoPullback_hom_snd.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((secTorsionPB D d k s).isoPullback.hom ≫ ·) hq) ?_
  exact Iso.hom_inv_id_assoc _ _

/-- **[T-EQ-3c main]** The `Hhom`-descent hypothesis: maps coequalized by the
torsion cover are coequalized by the coordinate-projection composite. -/
theorem secHhom
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ ((X.pullbackAlong k).pullbackAlong
      (secCover D d s)).curve.torsion N)
    (hg : g₁ ≫ torsionMapOfEllHom
        ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N =
      g₂ ≫ torsionMapOfEllHom
        ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N) :
    g₁ ≫ (secStruct D d k s hs hinv).torsionIso.hom ≫
        vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) =
      g₂ ≫ (secStruct D d k s hs hinv).torsionIso.hom ≫
        vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) := by
  obtain ⟨q, hq⟩ := secFleg_factors D d k s hs hinv
  refine Eq.trans (congrArg (g₁ ≫ ·) hq.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ q) hg) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (g₂ ≫ ·) hq

/-- **[T-EQ-3c main]** The `V_ρ`-side cover is the base change of the quotient
projection along the `V_ρ`-side section composite. -/
theorem secVRhoPB :
    IsPullback
      (pullback.snd (vRhoπ D)
        ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap ≫
        secLift D d s)
      (vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s))
      (d.σZ.relQuotientπ d.f d.over_base)
      (pullback.snd (vRhoπ D) (X.pullbackAlong k).structMap ≫ s) :=
  (isPullback_vRhoCoverPrj D (X.pullbackAlong k)
    (secCover D d s)).flip.paste_horiz
    (IsPullback.of_hasPullback (d.σZ.relQuotientπ d.f d.over_base) s)

/-- The `V_ρ`-side `γ`-translation is conjugate, under the pasting
identification, to the pulled quotient action. -/
theorem secVSmul_u (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    secVSmul D d k s γ ≫ (secVRhoPB D d k s).isoPullback.hom =
      (secVRhoPB D d k s).isoPullback.hom ≫
        d.σZ.pullbackRelQSMul d.f d.over_base
          (pullback.snd (vRhoπ D) (X.pullbackAlong k).structMap ≫ s) γ := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (secVSmul D d k s γ ≫ ·)
      (secVRhoPB D d k s).isoPullback_hom_fst) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ secLift D d s)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      (pullback.snd (vRhoπ D) _ ≫ ·) (secSmul_secLift D d s γ)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      ((secVRhoPB D d k s).isoPullback.hom ≫ ·)
      (d.σZ.pullbackRelQSMul_fst d.f d.over_base
        (pullback.snd (vRhoπ D) (X.pullbackAlong k).structMap ≫ s) γ)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ d.σZ.hom γ)
      (secVRhoPB D d k s).isoPullback_hom_fst) ?_
    exact Category.assoc _ _ _
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (secVSmul D d k s γ ≫ ·)
      (secVRhoPB D d k s).isoPullback_hom_snd) ?_
    refine Eq.trans (secVSmul_prj D d k s γ) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      ((secVRhoPB D d k s).isoPullback.hom ≫ ·)
      (d.σZ.pullbackRelQSMul_snd d.f d.over_base
        (pullback.snd (vRhoπ D) (X.pullbackAlong k).structMap ≫ s) γ)) ?_
    exact (secVRhoPB D d k s).isoPullback_hom_snd

/-- **[T-EQ-3c main]** `γ`-invariance of the inverse-leg composite. -/
theorem secFinv_smul
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    secVSmul D d k s γ ≫ (secStruct D d k s hs hinv).torsionIso.inv ≫
        torsionMapOfEllHom
          ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N =
      (secStruct D d k s hs hinv).torsionIso.inv ≫
        torsionMapOfEllHom
          ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N := by
  have hswap : secVSmul D d k s γ ≫
      (secStruct D d k s hs hinv).torsionIso.inv =
      (secStruct D d k s hs hinv).torsionIso.inv ≫
        torsionMapOfEllHom (secGSmul D d k s γ) N := by
    rw [Iso.comp_inv_eq, Category.assoc, secTorsion_smul_conj,
      Iso.inv_hom_id_assoc]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (· ≫ torsionMapOfEllHom
      ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N) hswap) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg ((secStruct D d k s hs hinv).torsionIso.inv ≫ ·)
    (secTorsionSmul_cover D d k s γ)

/-- **[T-EQ-3c main]** The inverse-leg composite descends through the
`V_ρ`-side cover. -/
theorem secFinv_factors
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N) :
    ∃ q : pullback (vRhoπ D) (X.pullbackAlong k).structMap ⟶
        (X.pullbackAlong k).curve.torsion N,
      vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) ≫ q =
        (secStruct D d k s hs hinv).torsionIso.inv ≫
          torsionMapOfEllHom
            ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N := by
  have hswap : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N),
      d.σZ.pullbackRelQSMul d.f d.over_base
          (pullback.snd (vRhoπ D) (X.pullbackAlong k).structMap ≫ s) γ ≫
        (secVRhoPB D d k s).isoPullback.inv =
      (secVRhoPB D d k s).isoPullback.inv ≫ secVSmul D d k s γ := by
    intro γ
    rw [Iso.comp_inv_eq, Category.assoc, secVSmul_u, Iso.inv_hom_id_assoc]
  obtain ⟨q, hq⟩ := d.σZ.exists_relQuotientπ_lift_baseChange d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D))
    (pullback.snd (vRhoπ D) (X.pullbackAlong k).structMap ≫ s)
    ((secVRhoPB D d k s).isoPullback.inv ≫
      (secStruct D d k s hs hinv).torsionIso.inv ≫
      torsionMapOfEllHom
        ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N)
    (fun γ => by
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg
        (· ≫ (secStruct D d k s hs hinv).torsionIso.inv ≫
          torsionMapOfEllHom
            ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N)
        (hswap γ)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg ((secVRhoPB D d k s).isoPullback.inv ≫ ·)
        (secFinv_smul D d k s hs hinv γ))
  refine ⟨q, ?_⟩
  refine Eq.trans (congrArg (· ≫ q)
    (secVRhoPB D d k s).isoPullback_hom_snd.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((secVRhoPB D d k s).isoPullback.hom ≫ ·) hq) ?_
  exact Iso.hom_inv_id_assoc _ _

/-- **[T-EQ-3c main]** The `Hinv`-descent hypothesis. -/
theorem secHinv
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ pullback (vRhoπ D)
      ((X.pullbackAlong k).pullbackAlong (secCover D d s)).structMap)
    (hg : g₁ ≫ vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s) =
      g₂ ≫ vRhoCoverPrj D (X.pullbackAlong k) (secCover D d s)) :
    g₁ ≫ (secStruct D d k s hs hinv).torsionIso.inv ≫
        torsionMapOfEllHom
          ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N =
      g₂ ≫ (secStruct D d k s hs hinv).torsionIso.inv ≫
        torsionMapOfEllHom
          ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) N := by
  obtain ⟨q, hq⟩ := secFinv_factors D d k s hs hinv
  refine Eq.trans (congrArg (g₁ ≫ ·) hq.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ q) hg) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (g₂ ≫ ·) hq

/-- **[T-EQ-3c FORWARD MAP]** A section of the free quotient of the
symplectically framed moduli yields a ρ-level structure on the base: lift along
the torsor pullback, read the classified carve value, apply the dictionary, and
descend along the finite étale cover (the `γ`-invariance discharged by the
quotient's invariant-lift property). -/
noncomputable def rhoOfSection
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N) :
    RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve := by
  haveI hFin : IsFinite (d.σZ.relQuotientπ d.f d.over_base) :=
    d.σZ.isFinite_relQuotientπ_of_free d.f d.over_base
      (d.free_on_points (sympFramedAut_freeAction D))
  haveI hEt : Etale (d.σZ.relQuotientπ d.f d.over_base) :=
    d.σZ.etale_relQuotientπ_of_free d.f d.over_base
      (d.free_on_points (sympFramedAut_freeAction D))
  haveI hFl : Flat (d.σZ.relQuotientπ d.f d.over_base) :=
    d.σZ.flat_relQuotientπ_of_free d.f d.over_base
      (d.free_on_points (sympFramedAut_freeAction D))
  haveI hSu : Surjective (d.σZ.relQuotientπ d.f d.over_base) :=
    d.σZ.surjective_relQuotientπ_of_free d.f d.over_base
  haveI hQC : QuasiCompact (d.σZ.relQuotientπ d.f d.over_base) := inferInstance
  haveI : IsFinite (secCover D d s) :=
    MorphismProperty.pullback_snd _ _ hFin
  haveI : Etale (secCover D d s) :=
    MorphismProperty.pullback_snd _ _ hEt
  haveI : Flat (secCover D d s) :=
    MorphismProperty.pullback_snd _ _ hFl
  haveI : Surjective (secCover D d s) :=
    MorphismProperty.pullback_snd _ _ hSu
  haveI : QuasiCompact (secCover D d s) :=
    MorphismProperty.pullback_snd _ _ hQC
  haveI : IsFinite (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) :=
    MorphismProperty.pullback_snd _ _ hFin
  haveI : Etale (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) :=
    MorphismProperty.pullback_snd _ _ hEt
  haveI : Flat (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) :=
    MorphismProperty.pullback_snd _ _ hFl
  haveI : Surjective (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) :=
    MorphismProperty.pullback_snd _ _ hSu
  haveI : QuasiCompact (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) :=
    MorphismProperty.pullback_snd _ _ hQC
  exact @RhoLevelStructure.descend N ‹_› D (X.pullbackAlong k) _
    (secCover D d s) ‹_› ‹_› ‹_› (secStruct D d k s hs hinv) ‹_› ‹_›
    (secHhom D d k s hs hinv) (secHinv D d k s hs hinv)

/-- `rhoOfSection` is definitionally the descend of the section structure (the
unfolding lemma, given its own elaboration budget). -/
theorem rhoOfSection_eq_descend
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    [IsFinite (secCover D d s)] [Etale (secCover D d s)]
    [Flat (secCover D d s)] [Surjective (secCover D d s)]
    [QuasiCompact (secCover D d s)] :
    rhoOfSection D d k s hs hinv =
      @RhoLevelStructure.descend N ‹_› D (X.pullbackAlong k) _
        (secCover D d s) ‹_› ‹_› ‹_› (secStruct D d k s hs hinv) ‹_› ‹_›
        (secHhom D d k s hs hinv) (secHinv D d k s hs hinv) := rfl

end SectionsToStructures

section StructuresToSections

open scoped FintypeCatDiscrete

variable (D : GaloisRepData N)

/-- **[T-EQ-3d-A1]** The frames product over a structure's base — the intrinsic
trivialising cover of the 3d direction. -/
noncomputable def strCover (X' : EllObj (CommRingCat.of ℚ)) : Scheme.{0} :=
  pullback X'.structMap (wFramesπ D)

/-- Its projection to the base. -/
noncomputable def strPr (X' : EllObj (CommRingCat.of ℚ)) :
    strCover D X' ⟶ X'.base :=
  pullback.fst _ _

/-- The tautological frame over the cover. -/
noncomputable def strTaut (X' : EllObj (CommRingCat.of ℚ)) :
    strCover D X' ⟶ wFrames D :=
  pullback.snd _ _

@[reassoc]
theorem strTaut_π (X' : EllObj (CommRingCat.of ℚ)) :
    strTaut D X' ≫ wFramesπ D = strPr D X' ≫ X'.structMap :=
  pullback.condition.symm

/-- **[T-EQ-3d-A1]** The tautological `V_ρ`-point at a constant vector `v`:
evaluate the tautological frame at `v`. -/
noncomputable def strVPt (X' : EllObj (CommRingCat.of ℚ)) (v : Fin 2 → ZMod N) :
    strCover D X' ⟶ pullback (vRhoπ D) X'.structMap :=
  pullback.lift (strTaut D X' ≫ frameSlotEval D v) (strPr D X') (by
    rw [Category.assoc, frameSlotEval_π]
    exact strTaut_π D X')

@[reassoc]
theorem strVPt_fst (X' : EllObj (CommRingCat.of ℚ)) (v : Fin 2 → ZMod N) :
    strVPt D X' v ≫ pullback.fst (vRhoπ D) X'.structMap =
      strTaut D X' ≫ frameSlotEval D v :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem strVPt_snd (X' : EllObj (CommRingCat.of ℚ)) (v : Fin 2 → ZMod N) :
    strVPt D X' v ≫ pullback.snd (vRhoπ D) X'.structMap = strPr D X' :=
  pullback.lift_snd _ _ _

variable {X' : EllObj (CommRingCat.of ℚ)}
variable (str : RhoLevelStructure D X'.structMap X'.curve)

/-- **[T-EQ-3d-A1]** The tautological torsion point at `v` (through the
structure's trivialisation). -/
noncomputable def strTor (v : Fin 2 → ZMod N) :
    strCover D X' ⟶ X'.curve.torsion N :=
  strVPt D X' v ≫ str.torsionIso.inv

@[reassoc]
theorem strTor_π (v : Fin 2 → ZMod N) :
    strTor D str v ≫ X'.curve.torsionπ N = strPr D X' := by
  rw [strTor, Category.assoc]
  rw [show str.torsionIso.inv ≫ X'.curve.torsionπ N =
      pullback.snd (vRhoπ D) X'.structMap from by
    rw [← str.over_T, Iso.inv_hom_id_assoc]]
  exact strVPt_snd D X' v

/-- **[T-EQ-3d-A1]** The tautological `E`-point over the cover at `v`. -/
noncomputable def strPt (v : Fin 2 → ZMod N) :
    X'.curve.Point (strPr D X') :=
  ⟨strTor D str v ≫ X'.curve.torsionι N, by
    rw [Category.assoc, EllipticCurve.torsionι_π]
    exact strTor_π D str v⟩

theorem strPt_raw_kill (v : Fin 2 → ZMod N) :
    (strPt D str v).1 ≫ X'.curve.mulByHom N = strPr D X' ≫ X'.curve.zero := by
  show (strTor D str v ≫ X'.curve.torsionι N) ≫ X'.curve.mulByHom N =
    strPr D X' ≫ X'.curve.zero
  rw [Category.assoc]
  rw [show X'.curve.torsionι N ≫ X'.curve.mulByHom N =
    X'.curve.torsionπ N ≫ X'.curve.zero from pullback.condition]
  rw [← Category.assoc, strTor_π]

theorem strPt_kill (v : Fin 2 → ZMod N) : (N : ℤ) • strPt D str v = 0 :=
  (X'.curve.smul_eq_zero_iff_comp_mulByHom (strPr D X') N _).mpr
    (strPt_raw_kill D str v)

/-- **[T-EQ-3d-A1]** `pointToTorsion` round-trips the tautological point back to
the tautological torsion map. -/
theorem strPt_pointToTorsion (v : Fin 2 → ZMod N) :
    X'.curve.pointToTorsion (strPt D str v) (strPt_raw_kill D str v) =
      strTor D str v := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans (strTor_π D str v).symm

/-- **[T-EQ-3d-A2 heart]** If the Weil pairing of a killed pair has no trivial
power below `N`, the pair generates the `N`-torsion of the geometric fibre: the
symplectic register makes the combination map injective, and the rank-two count
makes it surjective. -/
theorem full_of_weilPairing_order (K : Type) [Field K] [IsAlgClosed K]
    {T : Scheme.{0}} {E : EllipticCurve T}
    (t : Spec (.of K) ⟶ T) (P' Q' : E.Point t)
    (hP' : (N : ℤ) • P' = 0) (hQ' : (N : ℤ) • Q' = 0)
    (hNK : (N : K) ≠ 0)
    (hord : ∀ d : ℕ, 0 < d → d < N →
      (E.weilPairingEval P' Q'
        ((E.smul_eq_zero_iff_comp_mulByHom t N P').mp hP')
        ((E.smul_eq_zero_iff_comp_mulByHom t N Q').mp hQ')).1 ^ d ≠ 1)
    (z : E.Point t) (hz : (N : ℤ) • z = 0) :
    z ∈ AddSubgroup.closure {P', Q'} := by
  classical
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- killing of integer combinations
  have hcomb_kill : ∀ a b : ℤ, (N : ℤ) • (a • P' + b • Q') = 0 := by
    intro a b
    rw [smul_add, smul_comm (N : ℤ) a, smul_comm (N : ℤ) b, hP', hQ',
      smul_zero, smul_zero, add_zero]
  have hcomb_raw : ∀ a b : ℤ,
      (a • P' + b • Q').1 ≫ E.mulByHom N = t ≫ E.zero := fun a b =>
    (E.smul_eq_zero_iff_comp_mulByHom t N _).mp (hcomb_kill a b)
  -- the zero-combination pairing is trivial
  have hzero_pair : ∀ c d : ℤ,
      (E.weilPairingEval ((0 : ℤ) • P' + (0 : ℤ) • Q') (c • P' + d • Q')
        (hcomb_raw 0 0) (hcomb_raw c d)).1 = 1 := by
    intro c d
    have hs := E.weilPairingEval_symplectic P' Q' 0 0 c d
      ((E.smul_eq_zero_iff_comp_mulByHom t N P').mp hP')
      ((E.smul_eq_zero_iff_comp_mulByHom t N Q').mp hQ')
      (hcomb_raw 0 0) (hcomb_raw c d)
    rw [hs]
    norm_num
  -- injectivity of the combination map
  have hinj : ∀ a b : ZMod N,
      (a.val : ℤ) • P' + (b.val : ℤ) • Q' = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hpow : ∀ c d : ℤ,
        (E.weilPairingEval P' Q'
            ((E.smul_eq_zero_iff_comp_mulByHom t N P').mp hP')
            ((E.smul_eq_zero_iff_comp_mulByHom t N Q').mp hQ')).1 ^
          ((((a.val : ℤ) * d - (b.val : ℤ) * c) % (N : ℤ)).toNat) = 1 := by
      intro c d
      have hs := E.weilPairingEval_symplectic P' Q' (a.val : ℤ) (b.val : ℤ) c d
        ((E.smul_eq_zero_iff_comp_mulByHom t N P').mp hP')
        ((E.smul_eq_zero_iff_comp_mulByHom t N Q').mp hQ')
        (hcomb_raw _ _) (hcomb_raw c d)
      have hcongr := weilPairingEval_congr_raw (E := E) (rfl : t = t)
        (congrArg Subtype.val (hab.trans (by
          rw [zero_smul, zero_smul, add_zero] :
          ((0 : ℤ) • P' + (0 : ℤ) • Q' : E.Point t) = 0).symm))
        rfl (hcomb_raw _ _) (hcomb_raw c d) (hcomb_raw 0 0) (hcomb_raw c d)
      rw [← hs, hcongr]
      exact hzero_pair c d
    constructor
    · -- (c,d) = (0,1): exponent a.val
      have h1 := hpow 0 1
      have h2 : (((a.val : ℤ) * 1 - (b.val : ℤ) * 0) % (N : ℤ)).toNat = a.val := by
        have : ((a.val : ℤ) * 1 - (b.val : ℤ) * 0) = (a.val : ℤ) := by ring
        rw [this, Int.emod_eq_of_lt (Int.natCast_nonneg _)
          (Nat.cast_lt.mpr (ZMod.val_lt a)), Int.toNat_natCast]
      rw [h2] at h1
      by_contra ha
      exact hord a.val (Nat.pos_of_ne_zero fun h0 =>
        ha ((ZMod.val_eq_zero _).mp h0)) (ZMod.val_lt a) h1
    · -- (c,d) = (-1,0): exponent b.val
      have h1 := hpow (-1) 0
      have h2 : (((a.val : ℤ) * 0 - (b.val : ℤ) * (-1)) % (N : ℤ)).toNat =
          b.val := by
        have : ((a.val : ℤ) * 0 - (b.val : ℤ) * (-1)) = (b.val : ℤ) := by ring
        rw [this, Int.emod_eq_of_lt (Int.natCast_nonneg _)
          (Nat.cast_lt.mpr (ZMod.val_lt b)), Int.toNat_natCast]
      rw [h2] at h1
      by_contra hb
      exact hord b.val (Nat.pos_of_ne_zero fun h0 =>
        hb ((ZMod.val_eq_zero _).mp h0)) (ZMod.val_lt b) h1
  -- the combination map into the torsion submodule
  set f : ZMod N × ZMod N → Submodule.torsionBy ℤ (E.Point t) (N : ℤ) :=
    fun ab => ⟨(ab.1.val : ℤ) • P' + (ab.2.val : ℤ) • Q', by
      rw [Submodule.mem_torsionBy_iff]
      exact hcomb_kill _ _⟩ with hf
  have hfinj : Function.Injective f := by
    intro ab₁ ab₂ hab
    have hdiff : ((ab₁.1 - ab₂.1).val : ℤ) • P' +
        ((ab₁.2 - ab₂.2).val : ℤ) • Q' = 0 := by
      have h1 : (ab₁.1.val : ℤ) • P' + (ab₁.2.val : ℤ) • Q' =
          (ab₂.1.val : ℤ) • P' + (ab₂.2.val : ℤ) • Q' :=
        congrArg Subtype.val hab
      have h2 : ((ab₁.1 - ab₂.1).val : ℤ) • P' =
          ((ab₁.1.val : ℤ) - (ab₂.1.val : ℤ)) • P' :=
        EllipticCurve.zsmul_eq_of_intCast_eq P' hP'
          (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
      have h3 : ((ab₁.2 - ab₂.2).val : ℤ) • Q' =
          ((ab₁.2.val : ℤ) - (ab₂.2.val : ℤ)) • Q' :=
        EllipticCurve.zsmul_eq_of_intCast_eq Q' hQ'
          (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
      rw [h2, h3, sub_smul, sub_smul]
      rw [show (ab₁.1.val : ℤ) • P' - (ab₂.1.val : ℤ) • P' +
          ((ab₁.2.val : ℤ) • Q' - (ab₂.2.val : ℤ) • Q') =
          ((ab₁.1.val : ℤ) • P' + (ab₁.2.val : ℤ) • Q') -
          ((ab₂.1.val : ℤ) • P' + (ab₂.2.val : ℤ) • Q') from by abel]
      rw [h1, sub_self]
    obtain ⟨hA, hB⟩ := hinj _ _ hdiff
    exact Prod.ext (sub_eq_zero.mp hA) (sub_eq_zero.mp hB)
  -- surjectivity by the rank-two count
  obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N K t hNK
  have hcards : Nat.card (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)) = N * N := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun]
    simp [Nat.card_eq_fintype_card, ZMod.card, sq]
  haveI : Finite (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)) :=
    Finite.of_equiv _ e.toEquiv.symm
  have hfsurj : Function.Surjective f := by
    refine ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, ?_⟩).2
    rw [hcards, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨⟨a, b⟩, hab⟩ := hfsurj ⟨z, (Submodule.mem_torsionBy_iff _ _).mpr hz⟩
  have hz' : (a.val : ℤ) • P' + (b.val : ℤ) • Q' = z := congrArg Subtype.val hab
  rw [← hz']
  exact AddSubgroup.add_mem _
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) _)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) _)

/-- **[T-EQ-3d-α1]** The pinned read of a unit has no trivial power below `N`. -/
theorem pUnit_read_pow_ne_one (D : GaloisRepData N)
    (u : (ZMod N)ˣ) (d : ℕ) (hdpos : 0 < d) (hdlt : d < N) :
    (((D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N))) :
      (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ d ≠ 1 := by
  intro h
  have h2 : D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) ^ d = 1 := by
    refine Subtype.ext (Units.ext ?_)
    simpa using h
  have h3 : (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) ^ d = 1 :=
    D.p.injective (by rw [map_pow, h2, map_one])
  have h4 : d • ((u : (ZMod N)ˣ) : ZMod N) = 0 := by
    have h5 := (ofAdd_nsmul d ((u : (ZMod N)ˣ) : ZMod N)).trans h3
    have h6 := congrArg Multiplicative.toAdd h5
    simpa using h6
  have h5 : ((d : ℕ) : ZMod N) * ((u : (ZMod N)ˣ) : ZMod N) = 0 := by
    rw [← nsmul_eq_mul]
    exact h4
  have h6 : ((d : ℕ) : ZMod N) = 0 := by
    have h7 := congrArg (· * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) h5
    simpa [mul_assoc] using h7
  have h7 : (N : ℕ) ∣ d := (CharP.cast_eq_zero_iff (ZMod N) N d).mp h6
  have h8 : N ≤ d := Nat.le_of_dvd hdpos h7
  omega

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-α3]** The determinant-side power element is a unit: every `ℚ̄`-
evaluation reads a unit root (exact order `N`), so no proper power of the
transported root meets `1` anywhere on the units component. -/
theorem detComp_root_pow_sub_one_isUnit (D : GaloisRepData N) [Fact (1 < N)]
    (d : ℕ) (hdpos : 0 < d) (hdlt : d < N) :
    IsUnit ((detCompAlgHom D).hom.hom
      ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d - 1) := by
  classical
  by_contra hnu
  obtain ⟨m, hmax, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
  haveI := hmax
  haveI hfield := Ideal.Quotient.field m
  haveI : Module.Finite ℚ ((cycloUnitsAlgebra D : Type 0) ⧸ m) := by
    haveI : Module.Finite ℚ (cycloUnitsAlgebra D : Type 0) :=
      (cycloUnitsAlgebra D).property.left
    exact Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ ℚ m).toLinearMap (Ideal.Quotient.mk_surjective)
  haveI : Algebra.IsAlgebraic ℚ ((cycloUnitsAlgebra D : Type 0) ⧸ m) :=
    Algebra.IsAlgebraic.of_finite ℚ _
  set χ' : (cycloUnitsAlgebra D : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ :=
    (IsAlgClosed.lift (M := AlgebraicClosure ℚ)).comp
      (Ideal.Quotient.mkₐ ℚ m) with hχ'
  have hzero : χ' ((detCompAlgHom D).hom.hom
      ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d - 1)
      = 0 := by
    rw [hχ']
    show (IsAlgClosed.lift (M := AlgebraicClosure ℚ))
      ((Ideal.Quotient.mkₐ ℚ m) _) = 0
    rw [show (Ideal.Quotient.mkₐ ℚ m) ((detCompAlgHom D).hom.hom
        ((muNRootsAlgebraIso D).inv.hom.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d - 1) =
      0 from (Ideal.Quotient.eq_zero_iff_mem).mpr hmem]
    exact map_zero _
  -- the composite evaluation of the roots algebra
  set χ'' : (muNRootsAlgebra D : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ :=
    χ'.comp ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (detCompMor D)).unop.hom.hom with hχ''
  -- its point and read
  set ptc := (specPointsEquivAlgHom ℚ
    (corrAlgebra (cycloUnitsContAction D) : Type 0)
    (AlgebraicClosure ℚ)).symm χ' with hptc
  have hχ'pt : specPointsEquivAlgHom ℚ
      (corrAlgebra (cycloUnitsContAction D) : Type 0)
      (AlgebraicClosure ℚ) ptc = χ' := by
    rw [hptc]
    exact Equiv.apply_symm_apply _ χ'
  have hπc : (ptc.1 ≫ corrSpecMap (detCompMor D)) ≫
      corrSpecπ (muNRootsContAction D) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    (Category.assoc _ _ _).trans
      ((congrArg (CategoryStruct.comp ptc.1)
        (corrSpecMap_π (detCompMor D))).trans ptc.2)
  have hA : specPointsEquivAlgHom ℚ
      (corrAlgebra (muNRootsContAction D) : Type 0) (AlgebraicClosure ℚ)
      ⟨ptc.1 ≫ corrSpecMap (detCompMor D), hπc⟩ = χ'' := by
    have hpre := spec_preimage_comp ptc.1 (CommRingCat.ofHom
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (detCompMor D)).unop.hom.hom.toRingHom))
    refine AlgHom.ext fun b => ?_
    refine Eq.trans (congrArg (fun q : CommRingCat.of
      (corrAlgebra (muNRootsContAction D) : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom b) hpre) ?_
    rw [hχ'']
    exact congrArg (fun (F : (corrAlgebra (cycloUnitsContAction D) : Type 0)
      →ₐ[ℚ] AlgebraicClosure ℚ) =>
      F ((((FiniteEtaleGalois.finiteEtaleEquivContAction
        ℚ).inverse.map (detCompMor D)).unop.hom.hom) b)) hχ'pt
  -- the read of the pushed point is a unit read
  have hread := eval_root_eq_read D ⟨ptc.1 ≫ corrSpecMap (detCompMor D), hπc⟩
  have hnat := qbarPointsRead_map (detCompMor D) ptc
  have hζ : χ'' ((muNRootsAlgebraIso D).inv.hom.hom
      (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) =
      (((D.p (Multiplicative.ofAdd
        (((qbarPointsRead (cycloUnitsContAction D) ptc : (ZMod N)ˣ) :
          (ZMod N)ˣ) : ZMod N))) : (AlgebraicClosure ℚ)ˣ) :
        AlgebraicClosure ℚ) := by
    refine Eq.trans (congrArg (fun (F : (corrAlgebra (muNRootsContAction D) :
      Type 0) →ₐ[ℚ] AlgebraicClosure ℚ) => F ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)))) hA.symm) ?_
    refine hread.trans ?_
    exact congrArg (fun (z : rootsOfUnity N (AlgebraicClosure ℚ)) =>
      (((z : (AlgebraicClosure ℚ)ˣ)) : AlgebraicClosure ℚ)) hnat
  -- contradiction: the evaluation kills a nonvanishing element
  have hker : χ'' ((muNRootsAlgebraIso D).inv.hom.hom
      (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d - 1 = 0 := by
    have h1 : χ' ((detCompAlgHom D).hom.hom
        ((muNRootsAlgebraIso D).inv.hom.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d - 1) =
        χ'' ((muNRootsAlgebraIso D).inv.hom.hom
          (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d - 1 :=
      (map_sub χ' _ _).trans
        ((congrArg (· - χ' 1) (map_pow χ' _ d)).trans
          (congrArg (HSub.hSub _) (map_one χ')))
    exact h1.symm.trans hzero
  refine pUnit_read_pow_ne_one D
    (qbarPointsRead (cycloUnitsContAction D) ptc) d hdpos hdlt ?_
  rw [← hζ]
  exact sub_eq_zero.mp hker

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-α2]** The read of a `K`-point factoring through the determinant
component has no trivial power below `N` (its classifier factors through the
comultiplication, which sends the power element to a unit). -/
theorem detComp_point_read_pow_ne_one (D : GaloisRepData N) [Fact (1 < N)]
    {K : Type} [Field K] [Algebra ℚ K]
    (ψ : Spec (CommRingCat.of K) ⟶ cycloUnitsScheme D)
    (hφ : (ψ ≫ detCompScheme D) ≫ corrSpecπ (muNRootsContAction D) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))
    (d : ℕ) (hdpos : 0 < d) (hdlt : d < N) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      (muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))
        (ψ ≫ detCompScheme D) hφ) ^ d ≠ 1 := by
  intro hcon
  have hζ := muNRootsRead_classify_field D K (ψ ≫ detCompScheme D) hφ
  have hpre := spec_preimage_comp ψ (CommRingCat.ofHom
    (detCompAlgHom D).hom.hom.toRingHom)
  have hfac : ∀ z : (muNRootsAlgebra D : Type 0),
      (specPointsEquivAlgHom ℚ (corrAlgebra (muNRootsContAction D) : Type 0) K
        ⟨ψ ≫ detCompScheme D, hφ⟩) z =
      (Spec.preimage ψ).hom ((detCompAlgHom D).hom.hom z) := fun z =>
    congrArg (fun q : CommRingCat.of (corrAlgebra (muNRootsContAction D) :
      Type 0) ⟶ CommRingCat.of K => q.hom z) hpre
  have h1 : (Spec.preimage ψ).hom ((detCompAlgHom D).hom.hom
      ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)))) ^ d = 1 :=
    (congrArg (· ^ d) (hfac _).symm).trans
      ((congrArg (· ^ d) hζ.symm).trans hcon)
  have hkill : (Spec.preimage ψ).hom ((detCompAlgHom D).hom.hom
      ((muNRootsAlgebraIso D).inv.hom.hom
        (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ^ d - 1)
      = 0 :=
    (map_sub _ _ _).trans (sub_eq_zero.mpr ((map_pow _ _ d).trans
      (h1.trans (map_one _).symm)))
  exact ((detComp_root_pow_sub_one_isUnit D d hdpos hdlt).map
    (Spec.preimage ψ).hom).ne_zero hkill

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-A3 prep]** The roots power morphism at exponent 1 is the identity. -/
theorem muNRootsPowMor_one (D : GaloisRepData N) [Fact (1 < N)] :
    muNRootsPowMor D 1 = 𝟙 (muNRootsContAction D) := by
  ext ζ
  exact congrArg (fun z : rootsOfUnity N (AlgebraicClosure ℚ) =>
    ((z : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) (pow_one ζ)

open scoped FintypeCatDiscrete in
theorem muNRootsPowScheme_one (D : GaloisRepData N) [Fact (1 < N)] :
    muNRootsPowScheme D 1 = 𝟙 (muNRootsScheme D) := by
  have h1 : muNRootsPowAlg D 1 = 𝟙 (muNRootsAlgebra D) := by
    show ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (muNRootsPowMor D 1)).unop = 𝟙 (muNRootsAlgebra D)
    exact congrArg Quiver.Hom.unop
      ((congrArg (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (muNRootsPowMor_one D)).trans (CategoryTheory.Functor.map_id _ _))
  rw [muNRootsPowScheme, h1]
  show Spec.map (𝟙 (CommRingCat.of (muNRootsAlgebra D : Type 0))) =
    𝟙 (muNRootsScheme D)
  exact Spec.map_id _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-A3]** The standard-basis slot pair evaluates the pairing to the
determinant composite on the nose (the symplectic exponent of the standard
basis is `1`). -/
theorem pairSlot_basis_det (D : GaloisRepData N) [Fact (1 < N)] :
    pullback.lift (frameSlotEval D (Pi.single 0 1))
        (frameSlotEval D (Pi.single 1 1))
        ((frameSlotEval_π D _).trans (frameSlotEval_π D _).symm) ≫
      vRhoPairingMap D =
    detFrameScheme D ≫ detCompScheme D := by
  have habs := habs_of_ring D
    (fun v w => hring_of_finiteEtale D (fun v' w' => pairSlot_hFE D v' w') v w)
    (Pi.single 0 1) (Pi.single 1 1)
  have h1N : (1 : ℕ) < N := Fact.out
  have hexp : (((((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ) *
      (((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ) -
      (((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ) *
      (((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat
      = 1 := by
    rw [show (Pi.single 0 1 : Fin 2 → ZMod N) 0 = 1 from Pi.single_eq_same _ _,
      show (Pi.single 0 1 : Fin 2 → ZMod N) 1 = 0 from
        Pi.single_eq_of_ne (by decide) _,
      show (Pi.single 1 1 : Fin 2 → ZMod N) 0 = 0 from
        Pi.single_eq_of_ne (by decide) _,
      show (Pi.single 1 1 : Fin 2 → ZMod N) 1 = 1 from Pi.single_eq_same _ _,
      ZMod.val_one, ZMod.val_zero]
    norm_num
    rw [Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast h1N)]
    rfl
  rw [habs, hexp, muNRootsPowScheme_one, Category.comp_id]

omit [NeZero N] in
/-- **[T-EQ-3d-A3 prep]** The raw kill of an `asSection`-transported point. -/
theorem asSection_raw_kill {B : EllObj (CommRingCat.of ℚ)} {W : Scheme.{0}}
    (c : W ⟶ B.base) (x : B.curve.Point c)
    (hx : x.1 ≫ B.curve.mulByHom N = c ≫ B.curve.zero) :
    (EllipticCurve.Point.asSection B.curve c x).1 ≫
      (B.curve.baseChange c).mulByHom N = 𝟙 W ≫ (B.curve.baseChange c).zero := by
  refine Eq.trans (pullback.hom_ext ?_ ?_) (Category.id_comp _).symm
  · refine Eq.trans ((Category.assoc _ _ _).trans
      ((congrArg ((EllipticCurve.Point.asSection B.curve c x).1 ≫ ·)
        (B.curve.mulByHom_baseChange_fst c N)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ B.curve.mulByHom N)
            (EllipticCurve.Point.asSection_val_fst B.curve c x)).trans hx)))) ?_
    exact (pullback.lift_fst _ _ _).symm
  · refine Eq.trans ((Category.assoc _ _ _).trans
      ((congrArg ((EllipticCurve.Point.asSection B.curve c x).1 ≫ ·)
        (B.curve.mulByHom_baseChange_snd c N)).trans
        (EllipticCurve.Point.asSection_val_snd B.curve c x))) ?_
    exact (pullback.lift_snd _ _ _).symm

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-A3]** The value-level pairing of `asSection`-transported points is
the scheme-level pairing read of the points over the base map (the two
presentations of the same Weil-pairing read agree, through the projection and
the registered naturalities). -/
theorem pairEZMap_asSection (D : GaloisRepData N) [Fact (1 < N)]
    {B : EllObj (CommRingCat.of ℚ)} {W : Scheme.{0}} (c : W ⟶ B.base)
    (x y : B.curve.Point c)
    (hxr : x.1 ≫ B.curve.mulByHom N = c ≫ B.curve.zero)
    (hyr : y.1 ≫ B.curve.mulByHom N = c ≫ B.curve.zero) :
    pairEZMap D (B.pullbackAlong c).structMap (B.pullbackAlong c).curve
      (EllipticCurve.Point.asSection B.curve c x)
      (EllipticCurve.Point.asSection B.curve c y)
      (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mpr
        (asSection_raw_kill c x hxr))
      (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mpr
        (asSection_raw_kill c y hyr)) =
    torsionPairEval D B.structMap c x y hxr hyr := by
  have hπ2 : torsionPairEval D B.structMap c x y hxr hyr ≫
      muNRootsSchemeπ D = (B.pullbackAlong c).structMap :=
    torsionPairEval_π D B.structMap c x y hxr hyr
  refine muNRoots_hom_ext D
    (pairEZMap_π D (B.pullbackAlong c).structMap (B.pullbackAlong c).curve
      _ _ _ _) hπ2 ?_
  refine Eq.trans (pairEZMap_read_self D _ _ _ _ _ _) ?_
  refine Eq.symm ?_
  refine Eq.trans (torsionPairEval_read D B.structMap c x y hxr hyr) ?_
  -- (eval-B x y).1 = (eval-A asSec-x asSec-y).1
  have hvx : x.1 = (EllHom.mapPoint (B.pullbackAlongπ c) (𝟙 W)
      (EllipticCurve.Point.asSection B.curve c x)).1 :=
    ((EllipticCurve.Point.asSection_val_fst B.curve c x).symm).trans
      (EllHom.mapPoint_coe (B.pullbackAlongπ c) (𝟙 W)
        (EllipticCurve.Point.asSection B.curve c x)).symm
  have hvy : y.1 = (EllHom.mapPoint (B.pullbackAlongπ c) (𝟙 W)
      (EllipticCurve.Point.asSection B.curve c y)).1 :=
    ((EllipticCurve.Point.asSection_val_fst B.curve c y).symm).trans
      (EllHom.mapPoint_coe (B.pullbackAlongπ c) (𝟙 W)
        (EllipticCurve.Point.asSection B.curve c y)).symm
  refine Eq.trans (weilPairingEval_congr_raw (E := B.curve)
    ((Category.id_comp c).symm : c = 𝟙 W ≫ c) hvx hvy hxr hyr
    (EllHom.mapPoint_torsion (B.pullbackAlongπ c) _
      (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mp
        (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mpr
          (asSection_raw_kill c x hxr))))
    (EllHom.mapPoint_torsion (B.pullbackAlongπ c) _
      (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mp
        (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mpr
          (asSection_raw_kill c y hyr))))) ?_
  exact weilPairingEval_mapPoint (B.pullbackAlongπ c) (𝟙 W)
    (EllipticCurve.Point.asSection B.curve c x)
    (EllipticCurve.Point.asSection B.curve c y)
    (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mp
      (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mpr
        (asSection_raw_kill c x hxr)))
    (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mp
      (((B.curve.baseChange c).smul_eq_zero_iff_comp_mulByHom (𝟙 W) N _).mpr
        (asSection_raw_kill c y hyr)))

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-A3]** THE TAUTOLOGICAL CARVE: the pairing comparison of the
tautological level equals the determinant read of the tautological frame — the
structure's morphism-level pairing compatibility instantiated at the
standard-basis slots. -/
theorem strCond (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve) :
    pairEZMap D (X'.pullbackAlong (strPr D X')).structMap
      (X'.pullbackAlong (strPr D X')).curve
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)))
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1)))
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        (𝟙 (strCover D X')) N _).mpr
        (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _)))
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        (𝟙 (strCover D X')) N _).mpr
        (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))) =
    frameDetMap D (strTaut D X') := by
  refine (pairEZMap_asSection D (strPr D X')
    (strPt D str (Pi.single 0 1)) (strPt D str (Pi.single 1 1))
    (strPt_raw_kill D str _) (strPt_raw_kill D str _)).trans ?_
  refine (str.pairing_scheme (strPr D X')
    (strPt D str (Pi.single 0 1)) (strPt D str (Pi.single 1 1))
    (strPt_raw_kill D str _) (strPt_raw_kill D str _)).trans ?_
  have hcpl : coordPairLift D X'.structMap str.torsionIso str.over_T
      (strPr D X') (strPt D str (Pi.single 0 1)) (strPt D str (Pi.single 1 1))
      (strPt_raw_kill D str _) (strPt_raw_kill D str _) =
      strTaut D X' ≫ pullback.lift (frameSlotEval D (Pi.single 0 1))
        (frameSlotEval D (Pi.single 1 1))
        ((frameSlotEval_π D _).trans (frameSlotEval_π D _).symm) := by
    have hleg : ∀ v : Fin 2 → ZMod N,
        X'.curve.pointToTorsion (strPt D str v) (strPt_raw_kill D str v) ≫
          str.torsionIso.hom ≫ pullback.fst (vRhoπ D) X'.structMap =
        strTaut D X' ≫ frameSlotEval D v := by
      intro v
      refine Eq.trans (congrArg (· ≫ str.torsionIso.hom ≫
        pullback.fst (vRhoπ D) X'.structMap) (strPt_pointToTorsion D str v)) ?_
      refine Eq.trans (congrArg (· ≫ str.torsionIso.hom ≫
        pullback.fst (vRhoπ D) X'.structMap) (rfl :
          strTor D str v = strVPt D X' v ≫ str.torsionIso.inv)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (strVPt D X' v ≫ ·)
        (Iso.inv_hom_id_assoc str.torsionIso
          (pullback.fst (vRhoπ D) X'.structMap))) ?_
      exact strVPt_fst D X' v
    apply pullback.hom_ext
    · refine Eq.trans (pullback.lift_fst _ _ _) ?_
      refine Eq.trans (hleg (Pi.single 0 1)) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg (strTaut D X' ≫ ·) (pullback.lift_fst _ _ _)
    · refine Eq.trans (pullback.lift_snd _ _ _) ?_
      refine Eq.trans (hleg (Pi.single 1 1)) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg (strTaut D X' ≫ ·) (pullback.lift_snd _ _ _)
  refine Eq.trans (congrArg (· ≫ vRhoPairingMap D) hcpl) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (strTaut D X' ≫ ·) (pairSlot_basis_det D)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-A2]** The tautological pair is a naive full level: kills are
inherited, and on every geometric fibre the pair generates — its pairing is the
determinant read of the tautological frame (strCond), which is primitive
(detComp_point_read_pow_ne_one), so the counting engine applies. -/
theorem strLevel_isNaiveFullLevel (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve) :
    (X'.curve.baseChange (strPr D X')).IsNaiveFullLevel N
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)))
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1))) := by
  classical
  refine ⟨⟨((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mpr
      (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _)),
    ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mpr
      (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))⟩, ?_⟩
  intro kk _ _ t z hz
  letI : Algebra ℚ kk :=
    ((Spec.preimage (t ≫ strPr D X' ≫ X'.structMap)).hom).toAlgebra
  have hqk : t ≫ strPr D X' ≫ X'.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)) := by
    rw [show CommRingCat.ofHom (algebraMap ℚ kk) =
      Spec.preimage (t ≫ strPr D X' ≫ X'.structMap) from rfl, Spec.map_preimage]
  haveI : CharZero kk := charZero_of_injective_algebraMap
    (RingHom.injective (algebraMap ℚ kk))
  have hNK : ((N : ℕ) : kk) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- section kills
  have hkP : ((N : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 0 1)) : (X'.curve.baseChange
        (strPr D X')).Point (𝟙 (strCover D X'))) = 0 :=
    ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mpr
      (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))
  have hkQ : ((N : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 1 1)) : (X'.curve.baseChange
        (strPr D X')).Point (𝟙 (strCover D X'))) = 0 :=
    ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mpr
      (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))
  -- pulled raw kills
  have hpullP : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      t ≫ (X'.curve.baseChange (strPr D X')).zero := by
    show (t ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 0 1))).1) ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N = _
    rw [Category.assoc, asSection_raw_kill (strPr D X') _
      (strPt_raw_kill D str _), ← Category.assoc, Category.comp_id]
  have hpullQ : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1)))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      t ≫ (X'.curve.baseChange (strPr D X')).zero := by
    show (t ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 1 1))).1) ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N = _
    rw [Category.assoc, asSection_raw_kill (strPr D X') _
      (strPt_raw_kill D str _), ← Category.assoc, Category.comp_id]
  -- restricted raw kills
  have hres1 : (EllipticCurve.Point.restrict (X'.curve.baseChange (strPr D X'))
      t (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      (t ≫ 𝟙 (strCover D X')) ≫ (X'.curve.baseChange (strPr D X')).zero := by
    show (t ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 0 1))).1) ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N = _
    rw [Category.assoc, asSection_raw_kill (strPr D X') _
      (strPt_raw_kill D str _), ← Category.assoc]
  have hres2 : (EllipticCurve.Point.restrict (X'.curve.baseChange (strPr D X'))
      t (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1)))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      (t ≫ 𝟙 (strCover D X')) ≫ (X'.curve.baseChange (strPr D X')).zero := by
    show (t ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 1 1))).1) ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N = _
    rw [Category.assoc, asSection_raw_kill (strPr D X') _
      (strPt_raw_kill D str _), ← Category.assoc]
  -- the order hypothesis at the fibre
  have hord : ∀ d : ℕ, 0 < d → d < N →
      ((X'.curve.baseChange (strPr D X')).weilPairingEval
        (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))))
        (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1))))
        (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
          t N _).mp
          (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
            t N _).mpr hpullP))
        (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
          t N _).mp
          (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
            t N _).mpr hpullQ))).1 ^ d ≠ 1 := by
    intro d hdpos hdlt hcon
    -- restrict = pull (values agree)
    have hraw := weilPairingEval_congr_raw
      (E := X'.curve.baseChange (strPr D X')) (Category.comp_id t) rfl rfl
      hres1 hres2
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        t N _).mp
        (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
          t N _).mpr hpullP))
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        t N _).mp
        (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
          t N _).mpr hpullQ))
    have h1 : ((X'.curve.baseChange (strPr D X')).weilPairingEval
        (EllipticCurve.Point.restrict (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))))
        (EllipticCurve.Point.restrict (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))) hres1 hres2).1 ^ d = 1 :=
      (congrArg (· ^ d) hraw).trans hcon
    have hres := (X'.curve.baseChange (strPr D X')).weilPairingEval_restrict t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)))
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1)))
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        (𝟙 (strCover D X')) N _).mp hkP)
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        (𝟙 (strCover D X')) N _).mp hkQ)
      hres1 hres2
    have h2 : ((Scheme.Γ.map t.op).hom
        ((X'.curve.baseChange (strPr D X')).weilPairingEval
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1)))
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))
          (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
            (𝟙 (strCover D X')) N _).mp hkP)
          (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
            (𝟙 (strCover D X')) N _).mp hkQ)).1) ^ d = 1 :=
      (congrArg (· ^ d) hres.symm).trans h1
    -- the read of the composed point
    have h3 := pairEZMap_read D (X'.pullbackAlong (strPr D X')).structMap
      (X'.curve.baseChange (strPr D X'))
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)))
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1))) hkP hkQ t
    have h4 : muNRootsRead D
        (t ≫ (X'.pullbackAlong (strPr D X')).structMap)
        (t ≫ pairEZMap D (X'.pullbackAlong (strPr D X')).structMap
          (X'.curve.baseChange (strPr D X'))
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1)))
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1))) hkP hkQ)
        (by rw [Category.assoc, pairEZMap_π]) ^ d = 1 :=
      (congrArg (· ^ d) h3).trans h2
    -- transport the point across the tautological carve
    have hφeq : t ≫ pairEZMap D (X'.pullbackAlong (strPr D X')).structMap
        (X'.curve.baseChange (strPr D X'))
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1)))
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))) hkP hkQ =
        ((t ≫ strTaut D X') ≫ detFrameScheme D) ≫ detCompScheme D :=
      (congrArg (CategoryStruct.comp t) (strCond D str)).trans
        ((Category.assoc t (strTaut D X')
          (detFrameScheme D ≫ detCompScheme D)).symm.trans
          (Category.assoc (t ≫ strTaut D X') (detFrameScheme D)
            (detCompScheme D)).symm)
    have hφ2 : (((t ≫ strTaut D X') ≫ detFrameScheme D) ≫ detCompScheme D) ≫
        corrSpecπ (muNRootsContAction D) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)) := by
      rw [Category.assoc]
      rw [show detCompScheme D ≫ corrSpecπ (muNRootsContAction D) =
        cycloUnitsSchemeπ D from detCompScheme_π D]
      rw [Category.assoc, detFrameScheme_π, Category.assoc, strTaut_π]
      rw [show strPr D X' ≫ X'.structMap = strPr D X' ≫ X'.structMap from rfl]
      exact hqk
    have h5 : muNRootsRead D
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
        (((t ≫ strTaut D X') ≫ detFrameScheme D) ≫ detCompScheme D) hφ2 ^ d
        = 1 := by
      have hcongr := muNRootsRead_congr D
        (show t ≫ (X'.pullbackAlong (strPr D X')).structMap =
          Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)) from hqk) hφeq
        (by rw [Category.assoc, pairEZMap_π])
      exact (congrArg (· ^ d) hcongr.symm).trans h4
    have h6 : (Scheme.ΓSpecIso (CommRingCat.of kk)).hom.hom
        (muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
          (((t ≫ strTaut D X') ≫ detFrameScheme D) ≫ detCompScheme D) hφ2) ^ d
        = 1 :=
      (map_pow _ _ d).symm.trans
        ((congrArg (Scheme.ΓSpecIso (CommRingCat.of kk)).hom.hom h5).trans
          (map_one _))
    exact detComp_point_read_pow_ne_one D
      ((t ≫ strTaut D X') ≫ detFrameScheme D) hφ2 d hdpos hdlt h6
  exact full_of_weilPairing_order kk t _ _
    (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      t N _).mpr hpullP)
    (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      t N _).mpr hpullQ) hNK hord z hz

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-B]** The tautological symplectically-framed value over the
cover. -/
noncomputable def strValue (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve) :
    (sympFramedProblem D).obj (Opposite.op (X'.pullbackAlong (strPr D X'))) :=
  ⟨⟨⟨⟨EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)),
      EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1))⟩,
    strLevel_isNaiveFullLevel D str⟩,
    ⟨strTaut D X', strTaut_π D X'⟩⟩,
  strCond D str⟩

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-B]** The classified `Z`-point of the tautological value. -/
noncomputable def strZ (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve) :
    { h : strCover D (X.pullbackAlong k) ⟶ d.Z //
      h ≫ d.f = strPr D (X.pullbackAlong k) ≫ k } :=
  (d.eqv (strPr D (X.pullbackAlong k) ≫ k)).symm
    ((sympFramedProblem D).map
      (EllObj.toPullbackAlong
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))).op
      (strValue D str))

section GenAgreeLocus

variable {Y Bs : Scheme.{0}} (pi : Y ⟶ Bs)
variable {Tt : Scheme.{0}} (f g : Tt ⟶ Y) (hfg : f ≫ pi = g ≫ pi)

/-- **[T-EQ-3d-M1]** The paired comparison of two maps into a common target
over a common base (the generic form of `agreePair`). -/
noncomputable def genAgreePair : Tt ⟶ pullback pi pi :=
  pullback.lift f g hfg

/-- **[T-EQ-3d-M1]** The agreement locus of two maps into a finite étale
separated target (generic `agreeLocus`). -/
noncomputable def genAgreeLocus : Scheme.{0} :=
  pullback (pullback.diagonal pi) (genAgreePair pi f g hfg)

/-- Its inclusion into the source. -/
noncomputable def genAgreeLocusι : genAgreeLocus pi f g hfg ⟶ Tt :=
  pullback.snd _ _

theorem genAgreeLocusι_isOpenImmersion [IsFinite pi] [Etale pi] :
    IsOpenImmersion (genAgreeLocusι pi f g hfg) := by
  show IsOpenImmersion
    (pullback.snd (pullback.diagonal pi) (genAgreePair pi f g hfg))
  infer_instance

theorem genAgreeLocusι_isClosedImmersion [IsSeparated pi] :
    IsClosedImmersion (genAgreeLocusι pi f g hfg) := by
  show IsClosedImmersion
    (pullback.snd (pullback.diagonal pi) (genAgreePair pi f g hfg))
  exact MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _
    inferInstance

/-- **[T-EQ-3d-M1]** Factoring through the agreement locus is exactly the
agreement of the two maps. -/
theorem genAgreeLocus_factor_iff {W : Scheme.{0}} (h : W ⟶ Tt) :
    (∃ w : W ⟶ genAgreeLocus pi f g hfg,
      w ≫ genAgreeLocusι pi f g hfg = h) ↔ h ≫ f = h ≫ g := by
  have hcond : genAgreeLocusι pi f g hfg ≫ genAgreePair pi f g hfg =
      pullback.fst (pullback.diagonal pi) (genAgreePair pi f g hfg) ≫
        pullback.diagonal pi :=
    pullback.condition.symm
  have hιe : genAgreeLocusι pi f g hfg ≫ f =
      pullback.fst (pullback.diagonal pi) (genAgreePair pi f g hfg) :=
    (congrArg (genAgreeLocusι pi f g hfg ≫ ·)
        (pullback.lift_fst f g hfg).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.fst pi pi) hcond).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (pullback.fst (pullback.diagonal pi)
                (genAgreePair pi f g hfg) ≫ ·) (pullback.diagonal_fst _)).trans
              (Category.comp_id _)))))
  have hιd : genAgreeLocusι pi f g hfg ≫ g =
      pullback.fst (pullback.diagonal pi) (genAgreePair pi f g hfg) :=
    (congrArg (genAgreeLocusι pi f g hfg ≫ ·)
        (pullback.lift_snd f g hfg).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.snd pi pi) hcond).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (pullback.fst (pullback.diagonal pi)
                (genAgreePair pi f g hfg) ≫ ·) (pullback.diagonal_snd _)).trans
              (Category.comp_id _)))))
  constructor
  · rintro ⟨w, rfl⟩
    rw [Category.assoc, Category.assoc, hιe, hιd]
  · intro he
    refine ⟨pullback.lift (h ≫ f) h ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst,
        Category.comp_id, genAgreePair, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, genAgreePair, Category.assoc, pullback.lift_snd]
      exact he

include hfg in
/-- **[T-EQ-3d-M1/M6 engine]** Two maps into a finite étale separated target
that agree at the geometric point through every point are equal: the agreement
locus is clopen and hits every point, hence is an isomorphism. -/
theorem eq_of_forall_geomPt_agree [IsFinite pi] [Etale pi] [IsSeparated pi]
    (hpt : ∀ ω : Tt, geomPt Tt ω ≫ f = geomPt Tt ω ≫ g) : f = g := by
  haveI hoi := genAgreeLocusι_isOpenImmersion pi f g hfg
  have hsurj : Function.Surjective (genAgreeLocusι pi f g hfg).base := by
    intro ω
    obtain ⟨w, hw⟩ := (genAgreeLocus_factor_iff pi f g hfg
      (geomPt Tt ω)).mpr (hpt ω)
    obtain ⟨s₀⟩ : Nonempty (Spec (CommRingCat.of (geomResidue Tt ω))) :=
      inferInstance
    refine ⟨w.base s₀, ?_⟩
    have h1 : (genAgreeLocusι pi f g hfg).base (w.base s₀) =
        (w ≫ genAgreeLocusι pi f g hfg).base s₀ := rfl
    rw [h1, hw]
    exact geomPt_base Tt ω s₀
  haveI : Epi (genAgreeLocusι pi f g hfg).base :=
    (TopCat.epi_iff_surjective _).mpr hsurj
  haveI : IsIso (genAgreeLocusι pi f g hfg) :=
    AlgebraicGeometry.IsOpenImmersion.isIso (genAgreeLocusι pi f g hfg)
  have h2 := (genAgreeLocus_factor_iff pi f g hfg (𝟙 Tt)).mp
    ⟨inv (genAgreeLocusι pi f g hfg), IsIso.inv_hom_id _⟩
  rw [Category.id_comp, Category.id_comp] at h2
  exact h2

end GenAgreeLocus

section FiniteEtaleEval

/-- **[T-EQ-3d-M2]** Every nonzero element of a finite étale `ℚ`-algebra has a
nonvanishing `ℚ̄`-evaluation (the product-of-fields decomposition; the generic
form of `corrAlgebra_exists_eval_ne`). -/
theorem finiteEtale_exists_eval_ne (A : CommAlgCat.FiniteEtale.{0} ℚ)
    {b : (A : Type 0)} (hb : b ≠ 0) :
    ∃ χ : (A : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ, χ b ≠ 0 := by
  classical
  obtain ⟨I, hIfin, Ai, hFld, hAlgI, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod ℚ (A : Type 0)).mp
      inferInstance
  have heb : e b ≠ 0 := fun h => hb (e.injective (h.trans (map_zero e).symm))
  have hcomp : ∃ i : I, e b i ≠ 0 := by
    by_contra hall
    exact heb (funext fun i => by
      by_contra h
      exact hall ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hcomp
  letI := hFld i
  letI := hAlgI i
  haveI : Module.Finite ℚ (Ai i) := by
    refine Module.Finite.of_surjective
      ((Pi.evalAlgHom ℚ Ai i).comp e.toAlgHom).toLinearMap ?_
    have hsurj : Function.Surjective (fun z : (A : Type 0) => e z i) :=
      fun y => by
        obtain ⟨w, hw⟩ := e.surjective (Function.update 0 i y)
        exact ⟨w, (congrFun hw i).trans (Function.update_self _ _ _)⟩
    exact hsurj
  haveI : Algebra.IsAlgebraic ℚ (Ai i) := Algebra.IsAlgebraic.of_finite ℚ _
  let χ₀ : Ai i →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  refine ⟨χ₀.comp ((Pi.evalAlgHom ℚ Ai i).comp e.toAlgHom), ?_⟩
  show χ₀ (e b i) ≠ 0
  intro h0
  exact hi (by
    rw [show (0 : AlgebraicClosure ℚ) = χ₀ 0 from (map_zero χ₀).symm] at h0
    exact RingHom.injective (χ₀.toRingHom) h0)

end FiniteEtaleEval

section FrameGraphs

open scoped FintypeCatDiscrete

variable (D : GaloisRepData N)

/-- **[T-EQ-3d-M3]** The graph of the right `γ`-translation in the frames
square. -/
noncomputable def frameGraph (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    wFrames D ⟶ pullback (wFramesπ D) (wFramesπ D) :=
  pullback.lift (𝟙 (wFrames D)) (wFramesRightMul D γ)
    (by rw [Category.id_comp, wFramesRightMul_π])

@[reassoc]
theorem frameGraph_fst (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameGraph D γ ≫ pullback.fst (wFramesπ D) (wFramesπ D) = 𝟙 (wFrames D) :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem frameGraph_snd (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameGraph D γ ≫ pullback.snd (wFramesπ D) (wFramesπ D) =
      wFramesRightMul D γ :=
  pullback.lift_snd _ _ _

theorem frameGraph_isClosedImmersion
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    IsClosedImmersion (frameGraph D γ) := by
  haveI h1 : IsFinite (pullback.fst (wFramesπ D) (wFramesπ D)) :=
    MorphismProperty.pullback_fst _ _ (wFramesπ_finite_etale D).1
  have h2 : IsClosedImmersion (frameGraph D γ ≫
      pullback.fst (wFramesπ D) (wFramesπ D)) := by
    rw [frameGraph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (frameGraph D γ)
    (pullback.fst (wFramesπ D) (wFramesπ D))

theorem frameGraph_isOpenImmersion
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    IsOpenImmersion (frameGraph D γ) := by
  haveI h1 : Etale (pullback.fst (wFramesπ D) (wFramesπ D)) :=
    MorphismProperty.pullback_fst _ _ (wFramesπ_finite_etale D).2
  haveI h2 : Etale (frameGraph D γ ≫
      pullback.fst (wFramesπ D) (wFramesπ D)) := by
    rw [frameGraph_fst]
    infer_instance
  haveI h3 : Etale (frameGraph D γ) :=
    Etale.of_comp (frameGraph D γ) (pullback.fst (wFramesπ D) (wFramesπ D))
  haveI h4 : IsSplitMono (frameGraph D γ) :=
    ⟨⟨⟨pullback.fst (wFramesπ D) (wFramesπ D), frameGraph_fst D γ⟩⟩⟩
  exact IsOpenImmersion.of_flat_of_mono _

/-- **[T-EQ-3d-M3]** Two `ℚ̄`-frames over `ℚ` differ by a right translation
(the frames form a `GL₂`-torsor set). -/
theorem qbar_frames_rel (F₁ F₂ : Spec (.of (AlgebraicClosure ℚ)) ⟶ wFrames D)
    (h₁ : F₁ ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (h₂ : F₂ ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N),
      F₂ = F₁ ≫ wFramesRightMul D γ := by
  refine ⟨(wFramesPointsEquiv D ⟨F₁, h₁⟩)⁻¹ * wFramesPointsEquiv D ⟨F₂, h₂⟩, ?_⟩
  have hnat := qbarPointsRead_map
    (frameRightMulMor D ((wFramesPointsEquiv D ⟨F₁, h₁⟩)⁻¹ *
      wFramesPointsEquiv D ⟨F₂, h₂⟩)) ⟨F₁, h₁⟩
  have hread : qbarPointsRead (frameContAction D)
      ⟨F₁ ≫ wFramesRightMul D ((wFramesPointsEquiv D ⟨F₁, h₁⟩)⁻¹ *
        wFramesPointsEquiv D ⟨F₂, h₂⟩),
        (Category.assoc _ _ _).trans
          ((congrArg (CategoryStruct.comp F₁)
            (wFramesRightMul_π D ((wFramesPointsEquiv D ⟨F₁, h₁⟩)⁻¹ *
              wFramesPointsEquiv D ⟨F₂, h₂⟩))).trans h₁)⟩ =
      qbarPointsRead (frameContAction D) ⟨F₂, h₂⟩ := by
    refine hnat.trans ?_
    show (qbarPointsRead (frameContAction D) ⟨F₁, h₁⟩ :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) *
      ((wFramesPointsEquiv D ⟨F₁, h₁⟩)⁻¹ * wFramesPointsEquiv D ⟨F₂, h₂⟩) =
      qbarPointsRead (frameContAction D) ⟨F₂, h₂⟩
    show (wFramesPointsEquiv D ⟨F₁, h₁⟩) *
      ((wFramesPointsEquiv D ⟨F₁, h₁⟩)⁻¹ * wFramesPointsEquiv D ⟨F₂, h₂⟩) =
      wFramesPointsEquiv D ⟨F₂, h₂⟩
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hinj := (qbarPointsRead (frameContAction D)).injective hread
  exact (congrArg Subtype.val hinj).symm

end FrameGraphs

/-- **[T-EQ-3d-M4 prep]** Any two morphisms from a `Spec` into `Spec ℚ` agree
(ring maps out of `ℚ` are unique). -/
theorem specQhom_eq {K : Type} [CommRing K]
    (g h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h]
  exact congrArg Spec.map (CommRingCat.hom_ext (Subsingleton.elim _ _))

section FrameGraphs2

open scoped FintypeCatDiscrete

variable (D : GaloisRepData N)

/-- **[T-EQ-3d-M4]** Two `Ω`-frames over a common base point differ by a
constant right translation: the pair-point of the frames square lies on some
graph (its residue field embeds in `ℚ̄`, where the torsor relation holds), and
the graph is a clopen immersion, so the pair factors. -/
theorem exists_frameGraph_rel {Ω : Type} [Field Ω]
    (F₁ F₂ : Spec (CommRingCat.of Ω) ⟶ wFrames D)
    (hover : F₁ ≫ wFramesπ D = F₂ ≫ wFramesπ D) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N),
      F₂ = F₁ ≫ wFramesRightMul D γ := by
  classical
  set p : Spec (CommRingCat.of Ω) ⟶ pullback (wFramesπ D) (wFramesπ D) :=
    pullback.lift F₁ F₂ hover with hp
  obtain ⟨s₀⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  -- the ℚ̄-point through the image point, via the tensor presentation
  set q₀ : PrimeSpectrum (TensorProduct ℚ (wFramesAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0)) :=
    (AlgebraicGeometry.pullbackSpecIso ℚ (wFramesAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0)).hom.base (p.base s₀) with hq₀
  haveI : Module.Finite ℚ (TensorProduct ℚ (wFramesAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0)) :=
    Module.Finite.tensorProduct ℚ _ _
  haveI : IsArtinianRing (TensorProduct ℚ (wFramesAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0)) :=
    isArtinian_of_tower ℚ inferInstance
  haveI hqmax : q₀.asIdeal.IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime q₀.asIdeal
  haveI := Ideal.Quotient.field q₀.asIdeal
  haveI : Module.Finite ℚ ((TensorProduct ℚ (wFramesAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0)) ⧸ q₀.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ q₀.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic ℚ ((TensorProduct ℚ (wFramesAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0)) ⧸ q₀.asIdeal) :=
    Algebra.IsAlgebraic.of_finite ℚ _
  set χκ : (TensorProduct ℚ (wFramesAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0))
      →ₐ[ℚ] AlgebraicClosure ℚ :=
    (IsAlgClosed.lift (M := AlgebraicClosure ℚ)).comp
      (Ideal.Quotient.mkₐ ℚ q₀.asIdeal) with hχκ
  set pt₀ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
      pullback (wFramesπ D) (wFramesπ D) :=
    Spec.map (CommRingCat.ofHom χκ.toRingHom) ≫
      (AlgebraicGeometry.pullbackSpecIso ℚ (wFramesAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)).inv with hpt₀
  -- the two ℚ̄-frames and the torsor relation
  have hG₁ : (pt₀ ≫ pullback.fst (wFramesπ D) (wFramesπ D)) ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    specQhom_eq _ _
  have hG₂ : (pt₀ ≫ pullback.snd (wFramesπ D) (wFramesπ D)) ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    specQhom_eq _ _
  obtain ⟨γ, hγ⟩ := qbar_frames_rel D
    (pt₀ ≫ pullback.fst (wFramesπ D) (wFramesπ D))
    (pt₀ ≫ pullback.snd (wFramesπ D) (wFramesπ D)) hG₁ hG₂
  -- the ℚ̄-pair factors through the γ-graph
  have hfac : pt₀ = (pt₀ ≫ pullback.fst (wFramesπ D) (wFramesπ D)) ≫
      frameGraph D γ := by
    apply pullback.hom_ext
    · refine Eq.symm ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (CategoryStruct.comp
        (pt₀ ≫ pullback.fst (wFramesπ D) (wFramesπ D)))
        (frameGraph_fst D γ)).trans ?_
      exact Category.comp_id _
    · refine Eq.symm ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (CategoryStruct.comp
        (pt₀ ≫ pullback.fst (wFramesπ D) (wFramesπ D)))
        (frameGraph_snd D γ)).trans ?_
      exact hγ.symm
  -- hence the image point lies in the graph's range
  have hsub : q₀.asIdeal ≤ RingHom.ker χκ.toRingHom := fun x hx =>
    RingHom.mem_ker.mpr (by
      show (IsAlgClosed.lift (M := AlgebraicClosure ℚ))
        ((Ideal.Quotient.mkₐ ℚ q₀.asIdeal) x) = 0
      rw [show (Ideal.Quotient.mkₐ ℚ q₀.asIdeal) x = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact map_zero _)
  have hnetop : RingHom.ker χκ.toRingHom ≠ ⊤ := by
    intro htop
    have h1 : (1 : TensorProduct ℚ (wFramesAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)) ∈ RingHom.ker χκ.toRingHom :=
      htop ▸ Submodule.mem_top
    have h2 := RingHom.mem_ker.mp h1
    rw [map_one] at h2
    exact one_ne_zero h2
  have hker : RingHom.ker χκ.toRingHom = q₀.asIdeal :=
    (hqmax.eq_of_le hnetop hsub).symm
  obtain ⟨sq⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure ℚ))) :=
    inferInstance
  have hsq : sq.asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim sq ⟨⊥, Ideal.isPrime_bot⟩)
  have hbase : (Spec.map (CommRingCat.ofHom χκ.toRingHom)).base sq = q₀ := by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap χκ.toRingHom sq.asIdeal = q₀.asIdeal
    rw [hsq]
    exact hker
  have hp₀mem : p.base s₀ ∈ Set.range (frameGraph D γ).base := by
    have h1 : pt₀.base sq = p.base s₀ := by
      have h2 : pt₀.base sq =
          (AlgebraicGeometry.pullbackSpecIso ℚ (wFramesAlgebra D : Type 0)
            (wFramesAlgebra D : Type 0)).inv.base
            ((Spec.map (CommRingCat.ofHom χκ.toRingHom)).base sq) := rfl
      rw [h2, hbase, hq₀]
      have h3 := congrArg (fun (m : pullback (wFramesπ D) (wFramesπ D) ⟶
          pullback (wFramesπ D) (wFramesπ D)) => m.base (p.base s₀))
        (AlgebraicGeometry.pullbackSpecIso ℚ (wFramesAlgebra D : Type 0)
          (wFramesAlgebra D : Type 0)).hom_inv_id
      exact h3
    rw [← h1, hfac]
    exact ⟨((pt₀ ≫ pullback.fst (wFramesπ D) (wFramesπ D))).base sq, rfl⟩
  haveI := frameGraph_isOpenImmersion D γ
  have hrange : Set.range p.base ⊆ Set.range (frameGraph D γ).base := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s₀]
    exact hp₀mem
  have hlift := IsOpenImmersion.lift_fac (frameGraph D γ) p hrange
  refine ⟨γ, ?_⟩
  have hpf : p ≫ pullback.fst (wFramesπ D) (wFramesπ D) = F₁ :=
    pullback.lift_fst _ _ _
  have hps : p ≫ pullback.snd (wFramesπ D) (wFramesπ D) = F₂ :=
    pullback.lift_snd _ _ _
  have hF₁ : IsOpenImmersion.lift (frameGraph D γ) p hrange = F₁ := by
    have h5 := congrArg (· ≫ pullback.fst (wFramesπ D) (wFramesπ D)) hlift
    simp only [Category.assoc, frameGraph_fst, Category.comp_id] at h5
    exact h5.trans hpf
  have h6 := congrArg (· ≫ pullback.snd (wFramesπ D) (wFramesπ D)) hlift
  simp only [Category.assoc, frameGraph_snd] at h6
  refine Eq.symm ?_
  refine Eq.trans (congrArg (· ≫ wFramesRightMul D γ) hF₁.symm) ?_
  exact h6.trans hps

end FrameGraphs2

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 prep]** The frames algebra is nontrivial (the frames set is
nonempty — it contains the identity frame). -/
theorem wFramesAlgebra_nontrivial (D : GaloisRepData N) :
    Nontrivial (wFramesAlgebra D : Type 0) := by
  refine ⟨1, 0, fun h10 => ?_⟩
  have h1 := congrArg (specPointsEquivAlgHom ℚ (wFramesAlgebra D : Type 0)
    (AlgebraicClosure ℚ) ((wFramesPointsEquiv D).symm 1)) h10
  exact one_ne_zero ((map_one _).symm.trans (h1.trans (map_zero _)))

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 prep]** The frames structure morphism is surjective
(integral lying-over for the injective structure map of a nontrivial finite
algebra). -/
theorem wFramesπ_surjective (D : GaloisRepData N) :
    Surjective (wFramesπ D) := by
  haveI := wFramesAlgebra_nontrivial D
  constructor
  refine RingHom.IsIntegral.comap_surjective ?_ ?_
  · exact RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr
      (wFramesAlgebra D).property.left)
  · exact RingHom.injective _

section StrAct

open scoped FintypeCatDiscrete

variable (D : GaloisRepData N)

/-- **[T-EQ-3d-M5]** The right `γ`-translation of the frames cover. -/
noncomputable def strAct (X' : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strCover D X' ⟶ strCover D X' :=
  pullback.map X'.structMap (wFramesπ D) X'.structMap (wFramesπ D)
    (𝟙 X'.base) (wFramesRightMul D γ) (𝟙 (Spec (CommRingCat.of ℚ)))
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, wFramesRightMul_π])

@[reassoc]
theorem strAct_pr (X' : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strAct D X' γ ≫ strPr D X' = strPr D X' := by
  refine (pullback.lift_fst _ _ _).trans ?_
  exact Category.comp_id _

@[reassoc]
theorem strAct_taut (X' : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strAct D X' γ ≫ strTaut D X' = strTaut D X' ≫ wFramesRightMul D γ :=
  pullback.lift_snd _ _ _

end StrAct

/-- **[T-EQ-3d-M5 (1)]** Every point of the spectrum of a finite `ℚ`-algebra
has a `ℚ̄`-point through it (maximal residue + embedding into the closure). -/
theorem finiteQ_exists_qbarPt_through (A : Type) [CommRing A] [Algebra ℚ A]
    [Module.Finite ℚ A] (ω : Spec (CommRingCat.of A)) :
    ∃ pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
      Spec (CommRingCat.of A),
      ∀ s : Spec (CommRingCat.of (AlgebraicClosure ℚ)), pt.base s = ω := by
  classical
  haveI : IsArtinianRing A := isArtinian_of_tower ℚ inferInstance
  haveI hqmax : ω.asIdeal.IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime ω.asIdeal
  haveI := Ideal.Quotient.field ω.asIdeal
  haveI : Module.Finite ℚ (A ⧸ ω.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ ω.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic ℚ (A ⧸ ω.asIdeal) :=
    Algebra.IsAlgebraic.of_finite ℚ _
  set χκ : A →ₐ[ℚ] AlgebraicClosure ℚ :=
    (IsAlgClosed.lift (M := AlgebraicClosure ℚ)).comp
      (Ideal.Quotient.mkₐ ℚ ω.asIdeal) with hχκ
  have hsub : ω.asIdeal ≤ RingHom.ker χκ.toRingHom := fun x hx =>
    RingHom.mem_ker.mpr (by
      show (IsAlgClosed.lift (M := AlgebraicClosure ℚ))
        ((Ideal.Quotient.mkₐ ℚ ω.asIdeal) x) = 0
      rw [show (Ideal.Quotient.mkₐ ℚ ω.asIdeal) x = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact map_zero _)
  have hnetop : RingHom.ker χκ.toRingHom ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ RingHom.ker χκ.toRingHom := htop ▸ Submodule.mem_top
    have h2 := RingHom.mem_ker.mp h1
    rw [map_one] at h2
    exact one_ne_zero h2
  have hker : RingHom.ker χκ.toRingHom = ω.asIdeal :=
    (hqmax.eq_of_le hnetop hsub).symm
  refine ⟨Spec.map (CommRingCat.ofHom χκ.toRingHom), fun s => ?_⟩
  have hsq : s.asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim s ⟨⊥, Ideal.isPrime_bot⟩)
  refine PrimeSpectrum.ext ?_
  show Ideal.comap χκ.toRingHom s.asIdeal = ω.asIdeal
  rw [hsq]
  exact hker

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (2)]** Morphisms out of the frames scheme into a finite
étale separated target over `ℚ` are determined by their `ℚ̄`-points. -/
theorem wFrames_hom_ext_of_qbar (D : GaloisRepData N)
    {Y : Scheme.{0}} {pi : Y ⟶ Spec (CommRingCat.of ℚ)}
    [IsFinite pi] [Etale pi] [IsSeparated pi]
    {f g : wFrames D ⟶ Y} (hfg : f ≫ pi = g ≫ pi)
    (hpt : ∀ pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ wFrames D,
      pt ≫ f = pt ≫ g) : f = g := by
  haveI hoi := genAgreeLocusι_isOpenImmersion pi f g hfg
  have hsurj : Function.Surjective (genAgreeLocusι pi f g hfg).base := by
    intro ω
    obtain ⟨pt, hptω⟩ := finiteQ_exists_qbarPt_through
      (wFramesAlgebra D : Type 0) ω
    obtain ⟨w, hw⟩ := (genAgreeLocus_factor_iff pi f g hfg pt).mpr (hpt pt)
    obtain ⟨s₀⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure ℚ))) :=
      inferInstance
    refine ⟨w.base s₀, ?_⟩
    have h1 : (genAgreeLocusι pi f g hfg).base (w.base s₀) =
        (w ≫ genAgreeLocusι pi f g hfg).base s₀ := rfl
    rw [h1, hw]
    exact hptω s₀
  haveI : Epi (genAgreeLocusι pi f g hfg).base :=
    (TopCat.epi_iff_surjective _).mpr hsurj
  haveI : IsIso (genAgreeLocusι pi f g hfg) :=
    AlgebraicGeometry.IsOpenImmersion.isIso (genAgreeLocusι pi f g hfg)
  have h2 := (genAgreeLocus_factor_iff pi f g hfg (𝟙 _)).mp
    ⟨inv (genAgreeLocusι pi f g hfg), IsIso.inv_hom_id _⟩
  rw [Category.id_comp, Category.id_comp] at h2
  exact h2

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (3) frame]** The slot-twist statement, reduced to `ℚ̄`-points
by the density engine (the per-point computation is the next step). -/
theorem rightMul_frameSlotEval (D : GaloisRepData N) [Fact (1 < N)]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N)
    (hpt : ∀ pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ wFrames D,
      pt ≫ wFramesRightMul D γ ≫ frameSlotEval D v =
      pt ≫ frameSlotEval D (γ • v)) :
    wFramesRightMul D γ ≫ frameSlotEval D v = frameSlotEval D (γ • v) := by
  haveI hFin : IsFinite (vRhoπ D) := (vRhoπ_finite_etale D).1
  haveI hEt : Etale (vRhoπ D) := (vRhoπ_finite_etale D).2
  haveI hSep : IsSeparated (vRhoπ D) :=
    inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (vRhoAlgebra D : Type 0)))))
  refine wFrames_hom_ext_of_qbar D (pi := vRhoπ D) ?_ hpt
  rw [Category.assoc, frameSlotEval_π, wFramesRightMul_π, frameSlotEval_π]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (3b-i)]** The read correction is `GL₂`-equivariant: both the
abstract counit read and the concrete index read intertwine the `γ`-translation
of points with the vector action. -/
theorem readCorrection_GL (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (v : Fin 2 → ZMod N) :
    readCorrection N (γ • v) = γ • readCorrection N v := by
  classical
  -- realize v as an index read
  set pt := (constVecIndexRead N).symm v with hptdef
  have hv : constVecIndexRead N pt = v := by
    rw [hptdef]
    exact (constVecIndexRead N).apply_symm_apply v
  -- the γ-translated point
  have hπγ : (pt.1 ≫ Spec.map (CommRingCat.ofHom
      (constVecGLAlg N γ).hom.hom.toRingHom)) ≫ constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    (Category.assoc _ _ _).trans
      ((congrArg (CategoryStruct.comp pt.1) (constVecGLScheme_π N γ)).trans
        pt.2)
  -- index read of the translated point is the γ-translate
  have hidx : constVecIndexRead N
      ⟨pt.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom), hπγ⟩ =
      γ • constVecIndexRead N pt := by
    have hpre := spec_preimage_comp pt.1 (CommRingCat.ofHom
      (constVecGLAlg N γ).hom.hom.toRingHom)
    have hA : specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
        (AlgebraicClosure ℚ)
        ⟨pt.1 ≫ Spec.map (CommRingCat.ofHom
          (constVecGLAlg N γ).hom.hom.toRingHom), hπγ⟩ =
        (specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
          (AlgebraicClosure ℚ) pt).comp (constVecGLAlg N γ).hom.hom := by
      refine AlgHom.ext fun b => ?_
      exact congrArg (fun q : CommRingCat.of (constVecAlgebra N : Type 0) ⟶
        CommRingCat.of (AlgebraicClosure ℚ) => q.hom b) hpre
    have h1 := congrArg (fun (ψ : (constVecAlgebra N : Type 0) →ₐ[ℚ]
        AlgebraicClosure ℚ) =>
      piAlgHomEquiv ℚ (Fin 2 → ZMod N) (SeparableClosure ℚ)
        (precompCvIsoEquiv N ((AlgEquiv.arrowCongr AlgEquiv.refl
          sepClosureQAlgEquiv.symm) ψ))) hA
    have hsq : (constVecGLAlg N γ).hom.hom.comp
        ((constVecAlgebraIso N).inv.hom.hom) =
        ((constVecAlgebraIso N).inv.hom.hom).comp (piGLAlgHom N γ) :=
      congrArg (fun (m : CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
        constVecAlgebra N) => m.hom.hom) (constVecGLAlg_square_inv N γ)
    have h2 := congrArg (fun (g : ((Fin 2 → ZMod N) → ℚ) →ₐ[ℚ]
        (constVecAlgebra N : Type 0)) =>
      piAlgHomEquiv ℚ (Fin 2 → ZMod N) (SeparableClosure ℚ)
        (((AlgEquiv.arrowCongr AlgEquiv.refl sepClosureQAlgEquiv.symm)
          (specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
            (AlgebraicClosure ℚ) pt)).comp g)) hsq
    refine (h1.trans h2).trans ?_
    show piAlgHomIndex ((((AlgEquiv.arrowCongr AlgEquiv.refl
        sepClosureQAlgEquiv.symm) (specPointsEquivAlgHom ℚ
        (constVecAlgebra N : Type 0) (AlgebraicClosure ℚ) pt)).comp
        ((constVecAlgebraIso N).inv.hom.hom)).comp (piGLAlgHom N γ)) =
      γ • constVecIndexRead N pt
    exact piAlgHomIndex_piGL N γ _
  -- points read of the translated point is the γ-translate
  have hpts : constVecPointsEquiv N
      ⟨pt.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom), hπγ⟩ =
      γ • constVecPointsEquiv N pt := constVecPointsEquiv_GL N γ pt
  -- assemble
  show constVecPointsEquiv N ((constVecIndexRead N).symm (γ • v)) =
    γ • constVecPointsEquiv N ((constVecIndexRead N).symm v)
  rw [show (constVecIndexRead N).symm (γ • v) =
    ⟨pt.1 ≫ Spec.map (CommRingCat.ofHom
      (constVecGLAlg N γ).hom.hom.toRingHom), hπγ⟩ from
    (constVecIndexRead N).injective (by
      rw [hidx, hv]
      exact (constVecIndexRead N).apply_symm_apply _)]
  rw [hpts, ← hptdef]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (3b-ii)]** The corrected component point intertwines the
`GL₂`-translations: the correction morphism commutes with the coordinate
change (readCorrection_GL), so the evaluation chain transports. -/
theorem constVecCorrPt_GL (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (v : Fin 2 → ZMod N) :
    constVecCorrPt N v ≫ constVecGLScheme N γ = constVecCorrPt N (γ • v) := by
  -- set-level commutation of the correction with the coordinate change
  have hset : corrMor N ≫ constVecGLMor N γ =
      constVecGLMor N γ ≫ corrMor N := by
    ext w x
    refine congrArg (fun z : Fin 2 → ZMod N => z x) (show
      γ • (readCorrection N).symm w = (readCorrection N).symm (γ • w) from ?_)
    refine ((readCorrection N).injective ?_).symm
    rw [Equiv.apply_symm_apply]
    rw [readCorrection_GL γ ((readCorrection N).symm w)]
    rw [Equiv.apply_symm_apply]
  -- algebra-level commutation through the correspondence
  have halg : constVecGLAlg N γ ≫ corrAlgHom N =
      corrAlgHom N ≫ constVecGLAlg N γ := by
    have h1 := congrArg
      (fun m => ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        m).unop) hset
    refine Eq.trans ?_ (Eq.trans h1 ?_)
    · exact (congrArg Quiver.Hom.unop
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          (corrMor N) (constVecGLMor N γ))).symm
    · exact congrArg Quiver.Hom.unop
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          (constVecGLMor N γ) (corrMor N))
  -- ring-level chain
  have hring : CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom ≫
      constVecCorrPtRing N v = constVecCorrPtRing N (γ • v) := by
    show CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom ≫
      CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom ≫
      CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => ℚ) v) =
      CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom ≫
      CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => ℚ)
        (γ • v))
    have h2 : CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom ≫
        CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom =
        CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom ≫
        CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom :=
      congrArg (fun (m : constVecAlgebra N ⟶ constVecAlgebra N) =>
        CommRingCat.ofHom m.hom.hom.toRingHom) halg
    have h3 : CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom ≫
        CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom =
        CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom ≫
        CommRingCat.ofHom (piGLAlgHom N γ).toRingHom :=
      congrArg (fun (m : constVecAlgebra N ⟶
        CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) =>
        CommRingCat.ofHom m.hom.hom.toRingHom) (constVecGLAlg_square N γ)
    have h4 : CommRingCat.ofHom (piGLAlgHom N γ).toRingHom ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => ℚ) v) =
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => ℚ)
          (γ • v)) :=
      CommRingCat.hom_ext (RingHom.ext fun f => rfl)
    rw [← Category.assoc, h2, Category.assoc,
      ← Category.assoc (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom), h3, Category.assoc, h4]
  refine Eq.trans (congrArg (· ≫ constVecGLScheme N γ)
    (constVecCorrPt_eq_Spec N v)) ?_
  refine Eq.trans ((AlgebraicGeometry.Spec.map_comp
    (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom)
    (constVecCorrPtRing N v)).symm) ?_
  exact (congrArg Spec.map hring).trans (constVecCorrPt_eq_Spec N (γ • v)).symm

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (3b)]** THE SLOT TWIST: right translation followed by slot
evaluation is slot evaluation at the translated vector. -/
theorem rightMul_frameSlotEval_eq (D : GaloisRepData N) [Fact (1 < N)]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    wFramesRightMul D γ ≫ frameSlotEval D v = frameSlotEval D (γ • v) := by
  classical
  have hcond : ∀ w : Fin 2 → ZMod N,
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        constVecCorrPt N w) ≫ constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    fun w => (Category.assoc _ _ _).trans
      ((congrArg (CategoryStruct.comp (Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))))) (constVecCorrPt_π N w)).trans
        (Category.comp_id _))
  refine rightMul_frameSlotEval D γ v ?_
  intro pt
  have hpair : ∀ (q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ wFrames D)
      (w : Fin 2 → ZMod N),
      q ≫ frameSlotEval D w =
      pullback.lift (Spec.map (CommRingCat.ofHom
          (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ constVecCorrPt N w) q
        ((hcond w).trans (specQhom_eq _ _).symm) ≫ frameEval D := by
    intro q w
    rw [frameSlotEval, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst,
        ← Category.assoc]
      exact congrArg (· ≫ constVecCorrPt N w) (specQhom_eq _ _)
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
        Category.comp_id]
  have hLHS := hpair (pt ≫ wFramesRightMul D γ) v
  have hRHS := hpair pt (γ • v)
  refine Eq.trans (Category.assoc _ _ _).symm (hLHS.trans (Eq.trans ?_
    hRHS.symm))
  set P₁ := pullback.lift (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ constVecCorrPt N v)
      (pt ≫ wFramesRightMul D γ)
      ((hcond v).trans (specQhom_eq _ _).symm) with hP₁
  set P₂ := pullback.lift (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ constVecCorrPt N (γ • v)) pt
      ((hcond (γ • v)).trans (specQhom_eq _ _).symm) with hP₂
  have hp₁ : P₁ ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) ≫
      constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ constVecSchemeπ N) (pullback.lift_fst _ _ _)).trans
        (hcond v))
  have hp₂ : P₂ ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) ≫
      constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ constVecSchemeπ N) (pullback.lift_fst _ _ _)).trans
        (hcond (γ • v)))
  have hread₁ := frameEval_points D P₁ hp₁
  have hread₂ := frameEval_points D P₂ hp₂
  refine congrArg Subtype.val ((vRhoPointsEquiv D).injective
    (hread₁.trans (Eq.trans ?_ hread₂.symm)))
  -- (A*γ) • c v = A • c (γ•v)
  have hm1 : (wFramesPointsEquiv D ⟨P₁ ≫ pullback.snd (constVecSchemeπ N)
      (wFramesπ D), by rw [Category.assoc, ← pullback.condition]; exact hp₁⟩)
      = wFramesPointsEquiv D ⟨pt ≫ wFramesRightMul D γ, specQhom_eq _ _⟩ :=
    congrArg (wFramesPointsEquiv D) (Subtype.ext (pullback.lift_snd _ _ _))
  have hm1' : (constVecPointsEquiv N ⟨P₁ ≫ pullback.fst (constVecSchemeπ N)
      (wFramesπ D), by rw [Category.assoc]; exact hp₁⟩) =
      constVecPointsEquiv N ⟨Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ constVecCorrPt N v,
        hcond v⟩ :=
    congrArg (constVecPointsEquiv N) (Subtype.ext (pullback.lift_fst _ _ _))
  have hm5 : (wFramesPointsEquiv D ⟨P₂ ≫ pullback.snd (constVecSchemeπ N)
      (wFramesπ D), by rw [Category.assoc, ← pullback.condition]; exact hp₂⟩)
      = wFramesPointsEquiv D ⟨pt, specQhom_eq _ _⟩ :=
    congrArg (wFramesPointsEquiv D) (Subtype.ext (pullback.lift_snd _ _ _))
  have hm5' : (constVecPointsEquiv N ⟨P₂ ≫ pullback.fst (constVecSchemeπ N)
      (wFramesπ D), by rw [Category.assoc]; exact hp₂⟩) =
      constVecPointsEquiv N ⟨Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ constVecCorrPt N (γ • v),
        hcond (γ • v)⟩ :=
    congrArg (constVecPointsEquiv N) (Subtype.ext (pullback.lift_fst _ _ _))
  -- the frames read of the translated point
  have hframes : wFramesPointsEquiv D ⟨pt ≫ wFramesRightMul D γ,
      specQhom_eq _ _⟩ =
      wFramesPointsEquiv D ⟨pt, specQhom_eq _ _⟩ * γ :=
    qbarPointsRead_map (frameRightMulMor D γ) ⟨pt, specQhom_eq _ _⟩
  -- the constVec γ-law through the corrected point
  have hGLπ : (Spec.map (CommRingCat.ofHom (algebraMap ℚ
      (AlgebraicClosure ℚ))) ≫ constVecCorrPt N v) ≫
      Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom) ≫
      constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    (congrArg (CategoryStruct.comp _) (constVecGLScheme_π N γ)).trans
      (hcond v)
  have hGL := constVecPointsEquiv_GL N γ
    ⟨Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
      constVecCorrPt N v, hcond v⟩
  have htrans : (⟨(Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ constVecCorrPt N v) ≫
      Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom),
        (Category.assoc _ _ _).trans hGLπ⟩ :
      { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
          Spec (CommRingCat.of (constVecAlgebra N : Type 0)) //
        h ≫ constVecSchemeπ N = Spec.map (CommRingCat.ofHom
          (algebraMap ℚ (AlgebraicClosure ℚ))) }) =
      ⟨Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        constVecCorrPt N (γ • v), hcond (γ • v)⟩ := by
    refine Subtype.ext ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (CategoryStruct.comp (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (AlgebraicClosure ℚ))))) (constVecCorrPt_GL γ v)
  have hcγ : constVecPointsEquiv N
      ⟨Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        constVecCorrPt N (γ • v), hcond (γ • v)⟩ =
      γ • constVecPointsEquiv N
        ⟨Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
          constVecCorrPt N v, hcond v⟩ :=
    (congrArg (constVecPointsEquiv N) htrans).symm.trans hGL
  -- assemble
  refine Eq.trans (congrArg (· • constVecPointsEquiv N
      ⟨P₁ ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D), by
        rw [Category.assoc]; exact hp₁⟩) (hm1.trans hframes)) ?_
  refine Eq.trans (congrArg ((wFramesPointsEquiv D ⟨pt, specQhom_eq _ _⟩ *
    γ) • ·) hm1') ?_
  refine Eq.trans (mul_smul _ _ _) ?_
  refine Eq.trans (congrArg (wFramesPointsEquiv D ⟨pt, specQhom_eq _ _⟩ • ·)
    hcγ.symm) ?_
  refine Eq.symm ?_
  refine Eq.trans (congrArg (· • constVecPointsEquiv N
      ⟨P₂ ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D), by
        rw [Category.assoc]; exact hp₂⟩) hm5) ?_
  exact congrArg (wFramesPointsEquiv D ⟨pt, specQhom_eq _ _⟩ • ·) hm5'

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (4a)]** The tautological `V_ρ`-point twists along the cover
translation. -/
theorem strAct_strVPt (D : GaloisRepData N) [Fact (1 < N)]
    (X' : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    strAct D X' γ ≫ strVPt D X' v = strVPt D X' (γ • v) := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (CategoryStruct.comp (strAct D X' γ))
      (strVPt_fst D X' v)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ frameSlotEval D v) (strAct_taut D X' γ)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (CategoryStruct.comp (strTaut D X'))
      (rightMul_frameSlotEval_eq D γ v)) ?_
    exact (strVPt_fst D X' (γ • v)).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (CategoryStruct.comp (strAct D X' γ))
      (strVPt_snd D X' v)) ?_
    refine Eq.trans (strAct_pr D X' γ) ?_
    exact (strVPt_snd D X' (γ • v)).symm

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (4b)]** The tautological torsion point twists along the
cover translation. -/
theorem strAct_strTor (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    strAct D X' γ ≫ strTor D str v = strTor D str (γ • v) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (· ≫ str.torsionIso.inv) (strAct_strVPt D X' γ v)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (4c)]** The tautological point's carrier twists along the
cover translation. -/
theorem strAct_strPt (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    strAct D X' γ ≫ (strPt D str v).1 = (strPt D str (γ • v)).1 := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (· ≫ X'.curve.torsionι N) (strAct_strTor D str γ v)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (5a)]** The general tautological pairing: the pairing
comparison of two tautological points reads as the determinant composite
raised to the symplectic pairing of the slots. -/
theorem strCondVW (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (v w : Fin 2 → ZMod N) :
    pairEZMap D (X'.pullbackAlong (strPr D X')).structMap
      (X'.pullbackAlong (strPr D X')).curve
      (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v))
      (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str w))
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        (𝟙 (strCover D X')) N _).mpr
        (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _)))
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        (𝟙 (strCover D X')) N _).mpr
        (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))) =
    strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D ≫
      muNRootsPowScheme D
        (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
          ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat) := by
  refine (pairEZMap_asSection D (strPr D X')
    (strPt D str v) (strPt D str w)
    (strPt_raw_kill D str _) (strPt_raw_kill D str _)).trans ?_
  refine (str.pairing_scheme (strPr D X')
    (strPt D str v) (strPt D str w)
    (strPt_raw_kill D str _) (strPt_raw_kill D str _)).trans ?_
  have hcpl : coordPairLift D X'.structMap str.torsionIso str.over_T
      (strPr D X') (strPt D str v) (strPt D str w)
      (strPt_raw_kill D str _) (strPt_raw_kill D str _) =
      strTaut D X' ≫ pullback.lift (frameSlotEval D v)
        (frameSlotEval D w)
        ((frameSlotEval_π D _).trans (frameSlotEval_π D _).symm) := by
    have hleg : ∀ u : Fin 2 → ZMod N,
        X'.curve.pointToTorsion (strPt D str u) (strPt_raw_kill D str u) ≫
          str.torsionIso.hom ≫ pullback.fst (vRhoπ D) X'.structMap =
        strTaut D X' ≫ frameSlotEval D u := by
      intro u
      refine Eq.trans (congrArg (· ≫ str.torsionIso.hom ≫
        pullback.fst (vRhoπ D) X'.structMap) (strPt_pointToTorsion D str u)) ?_
      refine Eq.trans (congrArg (· ≫ str.torsionIso.hom ≫
        pullback.fst (vRhoπ D) X'.structMap) (rfl :
          strTor D str u = strVPt D X' u ≫ str.torsionIso.inv)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (strVPt D X' u ≫ ·)
        (Iso.inv_hom_id_assoc str.torsionIso
          (pullback.fst (vRhoπ D) X'.structMap))) ?_
      exact strVPt_fst D X' u
    apply pullback.hom_ext
    · refine Eq.trans (pullback.lift_fst _ _ _) ?_
      refine Eq.trans (hleg v) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg (strTaut D X' ≫ ·) (pullback.lift_fst _ _ _)
    · refine Eq.trans (pullback.lift_snd _ _ _) ?_
      refine Eq.trans (hleg w) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg (strTaut D X' ≫ ·) (pullback.lift_snd _ _ _)
  refine Eq.trans (congrArg (· ≫ vRhoPairingMap D) hcpl) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (strTaut D X' ≫ ·) ?_
  exact habs_of_ring D
    (fun v' w' => hring_of_finiteEtale D
      (fun v'' w'' => pairSlot_hFE D v'' w'') v' w') v w

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (5c-i)]** The fibre pairing of two pulled tautological points
is the read of the determinant-power composite (strCondVW pulled to a field
point). -/
theorem strVW_pull_read (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (kk : Type) [Field kk] [Algebra ℚ kk]
    (t : Spec (CommRingCat.of kk) ⟶ strCover D X')
    (hqk : t ≫ strPr D X' ≫ X'.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
    (v w : Fin 2 → ZMod N)
    (hpv : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str v))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      t ≫ (X'.curve.baseChange (strPr D X')).zero)
    (hpw : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str w))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      t ≫ (X'.curve.baseChange (strPr D X')).zero) :
    ((X'.curve.baseChange (strPr D X')).weilPairingEval
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)))
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str w))) hpv hpw).1 =
    muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
      (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D ≫
        muNRootsPowScheme D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)))
      (by
        rw [Category.assoc]
        rw [show (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D ≫
            muNRootsPowScheme D
              (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
                ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)) ≫
            muNRootsSchemeπ D = strPr D X' ≫ X'.structMap from by
          simp only [Category.assoc]
          rw [muNRootsPowScheme_π]
          rw [show detCompScheme D ≫ muNRootsSchemeπ D = cycloUnitsSchemeπ D
            from detCompScheme_π D]
          rw [detFrameScheme_π]
          exact strTaut_π D X']
        exact hqk) := by
  -- restrict kills for the register
  have hkv : ((N : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str v) : (X'.curve.baseChange
        (strPr D X')).Point (𝟙 (strCover D X'))) = 0 :=
    ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mpr
      (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))
  have hkw : ((N : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str w) : (X'.curve.baseChange
        (strPr D X')).Point (𝟙 (strCover D X'))) = 0 :=
    ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mpr
      (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))
  have hres1 : (EllipticCurve.Point.restrict (X'.curve.baseChange (strPr D X'))
      t (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str v))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      (t ≫ 𝟙 (strCover D X')) ≫ (X'.curve.baseChange (strPr D X')).zero := by
    show (t ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str v)).1) ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N = _
    rw [Category.assoc, asSection_raw_kill (strPr D X') _
      (strPt_raw_kill D str _), ← Category.assoc]
  have hres2 : (EllipticCurve.Point.restrict (X'.curve.baseChange (strPr D X'))
      t (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str w))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      (t ≫ 𝟙 (strCover D X')) ≫ (X'.curve.baseChange (strPr D X')).zero := by
    show (t ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str w)).1) ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N = _
    rw [Category.assoc, asSection_raw_kill (strPr D X') _
      (strPt_raw_kill D str _), ← Category.assoc]
  -- pull = restrict on values
  have hraw := weilPairingEval_congr_raw
    (E := X'.curve.baseChange (strPr D X')) (Category.comp_id t) rfl rfl
    hres1 hres2 hpv hpw
  refine Eq.trans hraw.symm ?_
  -- restrict register
  have hres := (X'.curve.baseChange (strPr D X')).weilPairingEval_restrict t
    (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v))
    (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str w))
    (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mp hkv)
    (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mp hkw)
    hres1 hres2
  refine Eq.trans hres ?_
  -- the read of the composed point through strCondVW
  have h3 := pairEZMap_read D (X'.pullbackAlong (strPr D X')).structMap
    (X'.curve.baseChange (strPr D X'))
    (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v))
    (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str w))
    hkv hkw t
  refine Eq.trans h3.symm ?_
  refine muNRootsRead_congr D
    (show t ≫ (X'.pullbackAlong (strPr D X')).structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)) from hqk) ?_ _
  exact congrArg (CategoryStruct.comp t) (strCondVW D str v w)

omit [NeZero N] in
/-- **[T-EQ-3d-M5 (5c) prep]** Powers collapse modulo `N` for `N`-th roots. -/
theorem pow_mod_of_pow_N_eq_one {R : Type} [CommMonoid R] {x : R}
    (hx : x ^ N = 1) (a : ℕ) : x ^ a = x ^ (a % N) := by
  conv_lhs => rw [← Nat.div_add_mod a N]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (5c) prep]** The roots read is an `N`-th root of unity. -/
theorem muNRootsRead_pow_N (D : GaloisRepData N) [Fact (1 < N)]
    {W : Scheme.{0}} (b : W ⟶ Spec (CommRingCat.of ℚ))
    (φ : W ⟶ muNRootsScheme D) (hφ : φ ≫ muNRootsSchemeπ D = b) :
    muNRootsRead D b φ hφ ^ N = 1 :=
  (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N b
    ⟨φ ≫ (muNSpecQIso D).inv, by
      rw [Category.assoc, muNSpecQIso_π_inv, hφ]⟩).2

/-- **[T-EQ-3d-M5 (5c) prep]** The negative-exponent cancellation for `N`-th
roots: `x^((-a) mod N) · x^a = 1`. -/
theorem pow_neg_emod_cancel {R : Type} [CommMonoid R] {x : R}
    (hx : x ^ N = 1) (a : ℕ) :
    x ^ ((((-(a : ℤ))) % (N : ℤ)).toNat) * x ^ a = 1 := by
  have hNz : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have hnn : (0 : ℤ) ≤ (-(a : ℤ)) % (N : ℤ) := Int.emod_nonneg _ hNz
  have hdvd : (N : ℤ) ∣ ((-(a : ℤ)) % (N : ℤ) + a) := by
    rw [Int.emod_def]
    exact ⟨-((-(a : ℤ)) / N), by ring⟩
  have hcast : (((((-(a : ℤ))) % (N : ℤ)).toNat + a : ℕ) : ℤ) =
      (-(a : ℤ)) % (N : ℤ) + a := by
    push_cast [Int.toNat_of_nonneg hnn]
    ring
  have hdvdN : N ∣ ((((-(a : ℤ))) % (N : ℤ)).toNat + a) := by
    refine Int.natCast_dvd_natCast.mp ?_
    rw [hcast]
    exact hdvd
  obtain ⟨k, hk⟩ := hdvdN
  rw [← pow_add, hk, pow_mul, hx, one_pow]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (5c-ii)]** THE FIBRE ADDITIVITY: over a geometric point of the
cover, the pulled tautological point at any vector is the integer combination
of the pulled tautological basis. Nondegeneracy of the Weil pairing: the
difference pairs trivially against the pulled basis (the reads agree by the
general tautological pairing), hence against every torsion point (closure +
the second-slot bilinearity registers). -/
theorem strPt_pull_comb (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (kk : Type) [Field kk] [IsAlgClosed kk] [Algebra ℚ kk]
    (t : Spec (CommRingCat.of kk) ⟶ strCover D X')
    (hqk : t ≫ strPr D X' ≫ X'.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
    (v : Fin 2 → ZMod N) :
    EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v)) =
    ((v 0).val : ℤ) • EllipticCurve.Point.pull
      (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1))) +
    ((v 1).val : ℤ) • EllipticCurve.Point.pull
      (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1))) := by
  classical
  -- raw kills of pulled tautological points
  have hpull : ∀ u : Fin 2 → ZMod N,
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str u))).1 ≫
        (X'.curve.baseChange (strPr D X')).mulByHom N =
        t ≫ (X'.curve.baseChange (strPr D X')).zero := by
    intro u
    show (t ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str u)).1) ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N = _
    rw [Category.assoc, asSection_raw_kill (strPr D X') _
      (strPt_raw_kill D str _), ← Category.assoc, Category.comp_id]
  have hkill : ∀ u : Fin 2 → ZMod N,
      ((N : ℤ) • EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str u)) : (X'.curve.baseChange
            (strPr D X')).Point t) = 0 := fun u =>
    ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      t N _).mpr (hpull u)
  -- the combination and its kill
  have hcombkill : ∀ a b : ℤ,
      ((N : ℤ) • (a • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) +
        b • EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))) :
        (X'.curve.baseChange (strPr D X')).Point t) = 0 := by
    intro a b
    rw [smul_add, smul_comm (N : ℤ) a, smul_comm (N : ℤ) b,
      hkill (Pi.single 0 1), hkill (Pi.single 1 1), smul_zero, smul_zero,
      add_zero]
  -- the base read and the general pairing value
  have hζπ : (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) ≫
      muNRootsSchemeπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)) := by
    rw [Category.assoc]
    rw [show (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D) ≫
        muNRootsSchemeπ D = strPr D X' ≫ X'.structMap from by
      simp only [Category.assoc]
      rw [show detCompScheme D ≫ muNRootsSchemeπ D = cycloUnitsSchemeπ D from
        detCompScheme_π D]
      rw [detFrameScheme_π]
      exact strTaut_π D X']
    exact hqk
  have hζN : muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
      (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^ N = 1 :=
    muNRootsRead_pow_N D _ _ _
  have hVW : ∀ v' w' : Fin 2 → ZMod N,
      ((X'.curve.baseChange (strPr D X')).weilPairingEval
        (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str v')))
        (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str w'))) (hpull v') (hpull w')).1 =
      muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
        (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^
        (((((v' 0).val : ℤ) * ((w' 1).val : ℤ) -
          ((v' 1).val : ℤ) * ((w' 0).val : ℤ)) % (N : ℤ)).toNat) := by
    intro v' w'
    refine (strVW_pull_read D str kk t hqk v' w' (hpull v') (hpull w')).trans ?_
    refine Eq.trans (muNRootsRead_congr D rfl
      (show t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D ≫
          muNRootsPowScheme D
            (((((v' 0).val : ℤ) * ((w' 1).val : ℤ) -
              ((v' 1).val : ℤ) * ((w' 0).val : ℤ)) % (N : ℤ)).toNat)) =
        (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) ≫
          muNRootsPowScheme D
            (((((v' 0).val : ℤ) * ((w' 1).val : ℤ) -
              ((v' 1).val : ℤ) * ((w' 0).val : ℤ)) % (N : ℤ)).toNat) from by
        simp only [Category.assoc])
      (by
        refine Eq.trans (congrArg (· ≫ muNRootsSchemeπ D)
          (show t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D ≫
              muNRootsPowScheme D
                (((((v' 0).val : ℤ) * ((w' 1).val : ℤ) -
                  ((v' 1).val : ℤ) * ((w' 0).val : ℤ)) % (N : ℤ)).toNat)) =
            (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) ≫
              muNRootsPowScheme D
                (((((v' 0).val : ℤ) * ((w' 1).val : ℤ) -
                  ((v' 1).val : ℤ) * ((w' 0).val : ℤ)) % (N : ℤ)).toNat)
            from by simp only [Category.assoc])) ?_
        rw [Category.assoc, muNRootsPowScheme_π]
        exact hζπ)) ?_
    exact muNRootsRead_pow D _ _ hζπ _
  -- exponent computations at the basis
  have h1N : (1 : ℕ) < N := Fact.out
  have hs11 : (((((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ) *
      (((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ) -
      (((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ) *
      (((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat = 1 := by
    rw [show (Pi.single 0 1 : Fin 2 → ZMod N) 0 = 1 from Pi.single_eq_same _ _,
      show (Pi.single 0 1 : Fin 2 → ZMod N) 1 = 0 from
        Pi.single_eq_of_ne (by decide) _,
      show (Pi.single 1 1 : Fin 2 → ZMod N) 0 = 0 from
        Pi.single_eq_of_ne (by decide) _,
      show (Pi.single 1 1 : Fin 2 → ZMod N) 1 = 1 from Pi.single_eq_same _ _,
      ZMod.val_one, ZMod.val_zero]
    norm_num
    rw [Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast h1N)]
    rfl
  have hsv1 : ∀ u : Fin 2 → ZMod N,
      ((((u 0).val : ℤ) * (((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ) -
        ((u 1).val : ℤ) * (((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ)) %
        (N : ℤ)).toNat =
      (((-(((u 1).val : ℤ)))) % (N : ℤ)).toNat := by
    intro u
    rw [show (Pi.single 0 1 : Fin 2 → ZMod N) 0 = 1 from Pi.single_eq_same _ _,
      show (Pi.single 0 1 : Fin 2 → ZMod N) 1 = 0 from
        Pi.single_eq_of_ne (by decide) _, ZMod.val_one, ZMod.val_zero]
    norm_num
  have hsv2 : ∀ u : Fin 2 → ZMod N,
      ((((u 0).val : ℤ) * (((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ) -
        ((u 1).val : ℤ) * (((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) %
        (N : ℤ)).toNat = ((((u 0).val : ℤ)) % (N : ℤ)).toNat := by
    intro u
    rw [show (Pi.single 1 1 : Fin 2 → ZMod N) 0 = 0 from
        Pi.single_eq_of_ne (by decide) _,
      show (Pi.single 1 1 : Fin 2 → ZMod N) 1 = 1 from Pi.single_eq_same _ _,
      ZMod.val_one, ZMod.val_zero]
    norm_num
  -- the difference and its kill
  have hδkill : ((N : ℤ) • (EllipticCurve.Point.pull
      (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v)) -
      (((v 0).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) +
      ((v 1).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))))) :
      (X'.curve.baseChange (strPr D X')).Point t) = 0 := by
    rw [smul_sub, hkill v, hcombkill, sub_zero]
  have hδraw := ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
    t N _).mp hδkill
  -- the difference pairs trivially against each basis point
  have hbasis : ∀ (w : Fin 2 → ZMod N),
      (((-(((v 0).val : ℤ))) * ((w 1).val : ℤ) -
        (-(((v 1).val : ℤ))) * ((w 0).val : ℤ)) % (N : ℤ)).toNat =
        ((((-(((v 0).val : ℤ))) * ((w 1).val : ℤ) -
          (-(((v 1).val : ℤ))) * ((w 0).val : ℤ))) % (N : ℤ)).toNat →
      ∀ (hbj : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str w))).1 ≫
        (X'.curve.baseChange (strPr D X')).mulByHom N =
        t ≫ (X'.curve.baseChange (strPr D X')).zero)
      (hb2 : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str w))).1 =
        ((((w 0).val : ℤ)) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        (((w 1).val : ℤ)) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))).1)
      (hcancel : muNRootsRead D (Spec.map (CommRingCat.ofHom
          (algebraMap ℚ kk)))
          (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat) *
        muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk)))
          (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^
          (((((-(((v 0).val : ℤ))) * ((w 1).val : ℤ) -
            (-(((v 1).val : ℤ))) * ((w 0).val : ℤ))) % (N : ℤ)).toNat) = 1),
      ((X'.curve.baseChange (strPr D X')).weilPairingEval
        (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str v)) -
        (((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))))
        (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str w))) hδraw hbj).1 = 1 := by
    intro w _ hbj hb2 hcancel
    -- kills
    have hknegcomb : ((N : ℤ) •
        (-(((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
          ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1))))) :
        (X'.curve.baseChange (strPr D X')).Point t) = 0 := by
      rw [smul_neg, hcombkill, neg_zero]
    have hnegraw := ((X'.curve.baseChange
      (strPr D X')).smul_eq_zero_iff_comp_mulByHom t N _).mp hknegcomb
    have hsumkill : ((N : ℤ) • (EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)) +
        -(((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
          ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1))))) :
        (X'.curve.baseChange (strPr D X')).Point t) = 0 := by
      rw [smul_add, hkill v, hknegcomb, add_zero]
    have hsumraw := ((X'.curve.baseChange
      (strPr D X')).smul_eq_zero_iff_comp_mulByHom t N _).mp hsumkill
    -- δ = y₁ + (-comb) on values, then expand the first slot
    have hδeval := weilPairingEval_congr_raw
      (E := X'.curve.baseChange (strPr D X')) (rfl :
        (t : Spec (CommRingCat.of kk) ⟶ strCover D X') = t)
      (congrArg Subtype.val (sub_eq_add_neg _ _)) rfl
      hδraw hbj hsumraw hbj
    refine hδeval.trans ?_
    have hadd := (X'.curve.baseChange (strPr D X')).weilPairingEval_add_left
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)))
      (-(((v 0).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) +
        ((v 1).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))))
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str w)))
      (hpull v) hnegraw hbj hsumraw
    refine hadd.trans ?_
    -- the neg-comb evaluated against the basis point via the register
    have hcombkillraw : ∀ cd : ℤ × ℤ,
        (cd.1 • EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        cd.2 • EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))).1 ≫
          (X'.curve.baseChange (strPr D X')).mulByHom N =
        t ≫ (X'.curve.baseChange (strPr D X')).zero := fun cd =>
      ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        t N _).mp (hcombkill cd.1 cd.2)
    have hneg := weilPairingEval_congr_raw
      (E := X'.curve.baseChange (strPr D X')) (rfl :
        (t : Spec (CommRingCat.of kk) ⟶ strCover D X') = t)
      (congrArg Subtype.val (by
        rw [neg_add, ← neg_smul, ← neg_smul] :
        (-(((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
          ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))) :
          (X'.curve.baseChange (strPr D X')).Point t) =
        (-(((v 0).val : ℤ))) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        (-(((v 1).val : ℤ))) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))))
      hb2 hnegraw hbj
      (hcombkillraw ((-(((v 0).val : ℤ))), (-(((v 1).val : ℤ)))))
      (hcombkillraw ((((w 0).val : ℤ)), (((w 1).val : ℤ))))
    have hsymp := (X'.curve.baseChange (strPr D X')).weilPairingEval_symplectic
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))))
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))))
      (-(((v 0).val : ℤ))) (-(((v 1).val : ℤ)))
      (((w 0).val : ℤ)) (((w 1).val : ℤ))
      (hpull (Pi.single 0 1)) (hpull (Pi.single 1 1))
      (hcombkillraw ((-(((v 0).val : ℤ))), (-(((v 1).val : ℤ)))))
      (hcombkillraw ((((w 0).val : ℤ)), (((w 1).val : ℤ))))
    have hPQ := hVW (Pi.single 0 1) (Pi.single 1 1)
    rw [hs11, pow_one] at hPQ
    refine Eq.trans (congrArg₂ (· * ·) (hVW v w)
      (hneg.trans (hsymp.trans (congrArg
        (· ^ ((((-(((v 0).val : ℤ))) * ((w 1).val : ℤ) -
          (-(((v 1).val : ℤ))) * ((w 0).val : ℤ))) % (N : ℤ)).toNat)
        hPQ)))) ?_
    exact hcancel
  -- basis-as-combination values
  have hb2P : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)))).1 =
      (((((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ)) •
        EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) +
      ((((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ)) •
        EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))).1 :=
    congrArg Subtype.val (by
      rw [show (Pi.single 0 1 : Fin 2 → ZMod N) 0 = 1 from
          Pi.single_eq_same _ _,
        show (Pi.single 0 1 : Fin 2 → ZMod N) 1 = 0 from
          Pi.single_eq_of_ne (by decide) _, ZMod.val_one, ZMod.val_zero]
      norm_num)
  have hb2Q : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1)))).1 =
      (((((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) •
        EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) +
      ((((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ)) •
        EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))).1 :=
    congrArg Subtype.val (by
      rw [show (Pi.single 1 1 : Fin 2 → ZMod N) 0 = 0 from
          Pi.single_eq_of_ne (by decide) _,
        show (Pi.single 1 1 : Fin 2 → ZMod N) 1 = 1 from
          Pi.single_eq_same _ _, ZMod.val_one, ZMod.val_zero]
      norm_num)
  -- exponent cancellations at the two basis points
  have hval : ∀ a : ℕ, a < N → ((((a : ℤ)) % (N : ℤ))).toNat = a := by
    intro a ha
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Nat.cast_lt.mpr ha),
      Int.toNat_natCast]
  have hcancel0 : muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk))) (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^ (((((v 0).val : ℤ) * (((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ) - ((v 1).val : ℤ) * (((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat) * muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk))) (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^ ((((-((v 0).val : ℤ)) * (((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ) - (-((v 1).val : ℤ)) * (((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat) = 1 := by
    rw [hsv1 v]
    rw [show ((((-((v 0).val : ℤ)) * (((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ) - (-((v 1).val : ℤ)) * (((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat) = (((((v 1).val : ℤ)) % (N : ℤ)).toNat) from by
      rw [show (Pi.single 0 1 : Fin 2 → ZMod N) 0 = 1 from
          Pi.single_eq_same _ _,
        show (Pi.single 0 1 : Fin 2 → ZMod N) 1 = 0 from
          Pi.single_eq_of_ne (by decide) _,
        ZMod.val_one, ZMod.val_zero]
      norm_num]
    rw [hval ((v 1).val) (ZMod.val_lt _)]
    exact pow_neg_emod_cancel hζN ((v 1).val)
  have hcancel1 : muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk))) (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^ (((((v 0).val : ℤ) * (((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ) - ((v 1).val : ℤ) * (((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat) * muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ kk))) (t ≫ (strTaut D X' ≫ detFrameScheme D ≫ detCompScheme D)) hζπ ^ ((((-((v 0).val : ℤ)) * (((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ) - (-((v 1).val : ℤ)) * (((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat) = 1 := by
    rw [hsv2 v]
    rw [show ((((-((v 0).val : ℤ)) * (((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ) - (-((v 1).val : ℤ)) * (((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) % (N : ℤ)).toNat) = (((-((v 0).val : ℤ)) % (N : ℤ)).toNat) from by
      rw [show (Pi.single 1 1 : Fin 2 → ZMod N) 0 = 0 from
          Pi.single_eq_of_ne (by decide) _,
        show (Pi.single 1 1 : Fin 2 → ZMod N) 1 = 1 from
          Pi.single_eq_same _ _,
        ZMod.val_one, ZMod.val_zero]
      norm_num]
    rw [hval ((v 0).val) (ZMod.val_lt _), mul_comm]
    exact pow_neg_emod_cancel hζN ((v 0).val)
  have hb0 := hbasis (Pi.single 0 1) rfl (hpull _) hb2P hcancel0
  have hb1 := hbasis (Pi.single 1 1) rfl (hpull _) hb2Q hcancel1
  -- every torsion point pairs trivially with the difference
  have hker : ∀ (y : (X'.curve.baseChange (strPr D X')).Point t)
      (hy : y.1 ≫ (X'.curve.baseChange (strPr D X')).mulByHom N =
        t ≫ (X'.curve.baseChange (strPr D X')).zero),
      ((X'.curve.baseChange (strPr D X')).weilPairingEval
        (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str v)) -
        (((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1))))) y hδraw hy).1 = 1 := by
    intro y hy
    have hyk : ((N : ℤ) • y :
        (X'.curve.baseChange (strPr D X')).Point t) = 0 :=
      ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        t N y).mpr hy
    obtain ⟨c, d, hcd⟩ := AddSubgroup.mem_closure_pair.mp
      ((strLevel_isNaiveFullLevel D str).2 kk t y hyk)
    -- kills of the scalar pieces
    have hkc : ((N : ℤ) • (c • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1)))) :
        (X'.curve.baseChange (strPr D X')).Point t) = 0 := by
      rw [smul_comm, hkill (Pi.single 0 1), smul_zero]
    have hkd : ((N : ℤ) • (d • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))) :
        (X'.curve.baseChange (strPr D X')).Point t) = 0 := by
      rw [smul_comm, hkill (Pi.single 1 1), smul_zero]
    have hkcraw := ((X'.curve.baseChange
      (strPr D X')).smul_eq_zero_iff_comp_mulByHom t N _).mp hkc
    have hkdraw := ((X'.curve.baseChange
      (strPr D X')).smul_eq_zero_iff_comp_mulByHom t N _).mp hkd
    -- substitute the combination for y
    have hsubst := weilPairingEval_congr_raw
      (E := X'.curve.baseChange (strPr D X')) (rfl :
        (t : Spec (CommRingCat.of kk) ⟶ strCover D X') = t) rfl
      (congrArg Subtype.val hcd.symm) hδraw hy hδraw
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        t N _).mp (by
          rw [smul_add, hkc, hkd, add_zero]))
    refine hsubst.trans ?_
    -- expand the second slot
    have haddr := (X'.curve.baseChange (strPr D X')).weilPairingEval_add_right
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)) -
        (((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))))
      (c • EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))))
      (d • EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))))
      hδraw hkcraw hkdraw
      (((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
        t N _).mp (by rw [smul_add, hkc, hkd, add_zero]))
    refine haddr.trans ?_
    -- collapse the scalars
    have hzc := (X'.curve.baseChange (strPr D X')).weilPairingEval_zsmul_right
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)) -
        (((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))))
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1)))) c hδraw (hpull _) hkcraw
    have hzd := (X'.curve.baseChange (strPr D X')).weilPairingEval_zsmul_right
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)) -
        (((v 0).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1))) +
        ((v 1).val : ℤ) • EllipticCurve.Point.pull
          (X'.curve.baseChange (strPr D X')) t
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 1 1)))))
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))) d hδraw (hpull _) hkdraw
    refine Eq.trans (congrArg₂ (· * ·) hzc hzd) ?_
    rw [hb0, hb1, one_pow, one_pow, mul_one]
  -- nondegeneracy
  have hzp := (X'.curve.baseChange (strPr D X')).weilPairingEval_nondegenerate
    kk t
    (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str v)) -
      (((v 0).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) +
      ((v 1).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))))) hδraw hker
  have hzero : (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X')) t
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str v)) -
      (((v 0).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) +
      ((v 1).val : ℤ) • EllipticCurve.Point.pull
        (X'.curve.baseChange (strPr D X')) t
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))) :
      (X'.curve.baseChange (strPr D X')).Point t) = 0 := by
    refine hzp.trans (Subtype.ext ?_)
    exact ((X'.curve.baseChange (strPr D X')).point_zero_val t).symm
  exact sub_eq_zero.mp hzero

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (5c-iii)]** THE SECTION ADDITIVITY: the tautological section
at any vector is the integer combination of the tautological basis sections
(the fibre additivity densified through the torsion). -/
theorem strSec_comb (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (v : Fin 2 → ZMod N) :
    EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v) =
    ((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 0 1)) +
    ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (Pi.single 1 1)) := by
  classical
  -- N is invertible over ℚ, hence on the cover
  have hinvQ : NIsInvertible (Spec (CommRingCat.of ℚ)) N := by
    have hq : IsUnit ((N : ℚ)) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
    have h2 := hq.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
    rwa [map_natCast] at h2
  have hinv : NIsInvertible (strCover D X') N :=
    NIsInvertible.of_hom (strPr D X' ≫ X'.structMap) hinvQ
  haveI hFin : IsFinite ((X'.curve.baseChange (strPr D X')).torsionπ N) :=
    (X'.curve.baseChange (strPr D X')).torsionπ_isFinite N
  haveI hEt : Etale ((X'.curve.baseChange (strPr D X')).torsionπ N) :=
    (X'.curve.baseChange (strPr D X')).torsionπ_etale N hinv
  haveI hSep : IsSeparated ((X'.curve.baseChange (strPr D X')).torsionπ N) :=
    inferInstance
  -- the two classifiers and their kills
  have hkL : (EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str v)).1 ≫ (X'.curve.baseChange (strPr D X')).mulByHom N =
      𝟙 (strCover D X') ≫ (X'.curve.baseChange (strPr D X')).zero :=
    asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _)
  have hkR : (((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve
      (strPr D X') (strPt D str (Pi.single 0 1)) +
      ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1))).1 ≫
      (X'.curve.baseChange (strPr D X')).mulByHom N =
      𝟙 (strCover D X') ≫ (X'.curve.baseChange (strPr D X')).zero :=
    ((X'.curve.baseChange (strPr D X')).smul_eq_zero_iff_comp_mulByHom
      (𝟙 (strCover D X')) N _).mp (by
      rw [smul_add, smul_comm ((N : ℤ)) (((v 0).val : ℤ)),
        smul_comm ((N : ℤ)) (((v 1).val : ℤ))]
      rw [show ((N : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1)) :
          (X'.curve.baseChange (strPr D X')).Point (𝟙 (strCover D X'))) = 0
        from ((X'.curve.baseChange
          (strPr D X')).smul_eq_zero_iff_comp_mulByHom _ N _).mpr
          (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))]
      rw [show ((N : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)) :
          (X'.curve.baseChange (strPr D X')).Point (𝟙 (strCover D X'))) = 0
        from ((X'.curve.baseChange
          (strPr D X')).smul_eq_zero_iff_comp_mulByHom _ N _).mpr
          (asSection_raw_kill (strPr D X') _ (strPt_raw_kill D str _))]
      rw [smul_zero, smul_zero, add_zero])
  -- the torsion classifiers agree at every geometric point
  have hfg : (X'.curve.baseChange (strPr D X')).pointToTorsion
      (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v))
      hkL ≫ (X'.curve.baseChange (strPr D X')).torsionπ N =
      (X'.curve.baseChange (strPr D X')).pointToTorsion
      (((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)) +
        ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))) hkR ≫
      (X'.curve.baseChange (strPr D X')).torsionπ N := by
    rw [EllipticCurve.pointToTorsion_torsionπ,
      EllipticCurve.pointToTorsion_torsionπ]
  have heq := eq_of_forall_geomPt_agree
    ((X'.curve.baseChange (strPr D X')).torsionπ N)
    ((X'.curve.baseChange (strPr D X')).pointToTorsion
      (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v))
      hkL)
    ((X'.curve.baseChange (strPr D X')).pointToTorsion
      (((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)) +
        ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))) hkR) hfg ?_
  · -- carriers agree
    refine Subtype.ext ?_
    calc (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)).1
        = (X'.curve.baseChange (strPr D X')).pointToTorsion
            (EllipticCurve.Point.asSection X'.curve (strPr D X')
              (strPt D str v)) hkL ≫
            (X'.curve.baseChange (strPr D X')).torsionι N :=
          (EllipticCurve.pointToTorsion_torsionι _ _ _).symm
      _ = (X'.curve.baseChange (strPr D X')).pointToTorsion
            (((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve
              (strPr D X') (strPt D str (Pi.single 0 1)) +
              ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve
                (strPr D X') (strPt D str (Pi.single 1 1))) hkR ≫
            (X'.curve.baseChange (strPr D X')).torsionι N :=
          congrArg (· ≫ (X'.curve.baseChange (strPr D X')).torsionι N) heq
      _ = _ := EllipticCurve.pointToTorsion_torsionι _ _ _
  · -- the geometric-point check
    intro ω
    letI : Algebra ℚ (geomResidue (strCover D X') ω) :=
      ((Spec.preimage (geomPt (strCover D X') ω ≫ strPr D X' ≫
        X'.structMap)).hom).toAlgebra
    have hqk : geomPt (strCover D X') ω ≫ strPr D X' ≫ X'.structMap =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ
          (geomResidue (strCover D X') ω))) := by
      rw [show CommRingCat.ofHom (algebraMap ℚ
          (geomResidue (strCover D X') ω)) =
        Spec.preimage (geomPt (strCover D X') ω ≫ strPr D X' ≫
          X'.structMap) from rfl, Spec.map_preimage]
    -- the pulled points and the fibre additivity
    have hcomb := strPt_pull_comb D str (geomResidue (strCover D X') ω)
      (geomPt (strCover D X') ω) hqk v
    -- transport through pointToTorsion
    have hL := pointToTorsion_comp (E := X'.curve.baseChange (strPr D X'))
      (geomPt (strCover D X') ω)
      (EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str v))
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X'))
        (geomPt (strCover D X') ω)
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v))) rfl hkL
      (by
        show (geomPt (strCover D X') ω ≫ (EllipticCurve.Point.asSection
          X'.curve (strPr D X') (strPt D str v)).1) ≫
          (X'.curve.baseChange (strPr D X')).mulByHom N = _
        rw [Category.assoc, hkL, ← Category.assoc, Category.comp_id])
    have hR := pointToTorsion_comp (E := X'.curve.baseChange (strPr D X'))
      (geomPt (strCover D X') ω)
      (((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)) +
        ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1)))
      (EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X'))
        (geomPt (strCover D X') ω)
        (((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1)) +
          ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve
            (strPr D X') (strPt D str (Pi.single 1 1)))) rfl hkR
      (by
        show (geomPt (strCover D X') ω ≫ (((v 0).val : ℤ) •
          EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str (Pi.single 0 1)) +
          ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve
            (strPr D X') (strPt D str (Pi.single 1 1))).1) ≫
          (X'.curve.baseChange (strPr D X')).mulByHom N = _
        rw [Category.assoc, hkR, ← Category.assoc, Category.comp_id])
    rw [← hL, ← hR]
    -- reduce to the pulled-point equality
    have hpulleq : EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X'))
        (geomPt (strCover D X') ω)
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)) =
        EllipticCurve.Point.pull (X'.curve.baseChange (strPr D X'))
        (geomPt (strCover D X') ω)
        (((v 0).val : ℤ) • EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1)) +
          ((v 1).val : ℤ) • EllipticCurve.Point.asSection X'.curve
            (strPr D X') (strPt D str (Pi.single 1 1))) := by
      rw [EllipticCurve.Point.pull_add, EllipticCurve.Point.pull_zsmul,
        EllipticCurve.Point.pull_zsmul]
      exact hcomb
    have hcongr : ∀ (z₁ z₂ : (X'.curve.baseChange (strPr D X')).Point
        (geomPt (strCover D X') ω)) (h12 : z₁ = z₂)
        (h1 : z₁.1 ≫ (X'.curve.baseChange (strPr D X')).mulByHom N =
          geomPt (strCover D X') ω ≫
            (X'.curve.baseChange (strPr D X')).zero),
        (X'.curve.baseChange (strPr D X')).pointToTorsion z₁ h1 =
        (X'.curve.baseChange (strPr D X')).pointToTorsion z₂ (h12 ▸ h1) := by
      intro z₁ z₂ h12 h1
      subst h12
      rfl
    exact hcongr _ _ hpulleq _

/-- **[T-EQ-3d-M5 (6a)]** The translated basis vector reads the matrix column. -/
theorem smul_single_apply (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (j i : Fin 2) :
    (γ • (Pi.single j 1 : Fin 2 → ZMod N)) i =
      (γ : Matrix (Fin 2) (Fin 2) (ZMod N)) i j := by
  show ((γ : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec
    (Pi.single j 1 : Fin 2 → ZMod N)) i = _
  rw [Matrix.mulVec_single]
  exact mul_one _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6b)]** The tautological section at a translated basis vector
is the matrix-column combination of the basis sections. -/
theorem strSec_col (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (j : Fin 2) :
    EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (γ • Pi.single j 1)) =
    ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 j).val : ℤ)) •
      EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 0 1)) +
    ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 j).val : ℤ)) •
      EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str (Pi.single 1 1)) := by
  refine (strSec_comb D str (γ • Pi.single j 1)).trans ?_
  rw [smul_single_apply γ j 0, smul_single_apply γ j 1]

/-- **[T-EQ-3d-M5 (6c) prep]** Sections of a base change are determined by
their first legs. -/
theorem section_ext_fst {S T : Scheme.{0}} (E : EllipticCurve S) (g : T ⟶ S)
    (s₁ s₂ : (E.baseChange g).Point (𝟙 T))
    (h : s₁.1 ≫ pullback.fst E.π g = s₂.1 ≫ pullback.fst E.π g) : s₁ = s₂ :=
  Subtype.ext (pullback.hom_ext h (s₁.2.trans s₂.2.symm))

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6c)]** The cover translation as an endomorphism of the
pulled object in `Ell/ℚ`. -/
noncomputable def strActHom (D : GaloisRepData N)
    (X' : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    X'.pullbackAlong (strPr D X') ⟶ X'.pullbackAlong (strPr D X') where
  baseHom := strAct D X' γ
  base_w := by
    show strAct D X' γ ≫ strPr D X' ≫ X'.structMap = strPr D X' ≫ X'.structMap
    rw [← Category.assoc, strAct_pr]
  top := pullback.map X'.curve.π (strPr D X') X'.curve.π (strPr D X')
    (𝟙 X'.curve.E) (strAct D X' γ) (𝟙 X'.base)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, strAct_pr])
  isPullback := by
    have hfst : pullback.map X'.curve.π (strPr D X') X'.curve.π (strPr D X')
        (𝟙 X'.curve.E) (strAct D X' γ) (𝟙 X'.base)
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, strAct_pr]) ≫
        pullback.fst X'.curve.π (strPr D X') =
        pullback.fst X'.curve.π (strPr D X') := by
      rw [Limits.pullback.lift_fst, Category.comp_id]
    have hbig : IsPullback (pullback.map X'.curve.π (strPr D X') X'.curve.π
        (strPr D X') (𝟙 X'.curve.E) (strAct D X' γ) (𝟙 X'.base)
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, strAct_pr]) ≫
        pullback.fst X'.curve.π (strPr D X'))
        (pullback.snd X'.curve.π (strPr D X')) X'.curve.π
        (strAct D X' γ ≫ strPr D X') := by
      rw [hfst, strAct_pr]
      exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right hbig (Limits.pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback X'.curve.π (strPr D X'))
  zero_w := by
    show Limits.pullback.lift (strPr D X' ≫ X'.curve.zero) (𝟙 (strCover D X'))
        (by rw [Category.assoc, X'.curve.zero_π, Category.comp_id,
          Category.id_comp]) ≫
      pullback.map X'.curve.π (strPr D X') X'.curve.π (strPr D X')
        (𝟙 X'.curve.E) (strAct D X' γ) (𝟙 X'.base)
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, strAct_pr]) =
      strAct D X' γ ≫ Limits.pullback.lift (strPr D X' ≫ X'.curve.zero)
        (𝟙 (strCover D X'))
        (by rw [Category.assoc, X'.curve.zero_π, Category.comp_id,
          Category.id_comp])
    apply Limits.pullback.hom_ext
    · refine ((Category.assoc _ _ _).trans ((congrArg (CategoryStruct.comp _)
        (Limits.pullback.lift_fst _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ 𝟙 X'.curve.E) (Limits.pullback.lift_fst _ _ _)).trans
        (Category.comp_id _))))).trans ?_
      refine Eq.symm ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (CategoryStruct.comp (strAct D X' γ))
        (Limits.pullback.lift_fst _ _ _)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact congrArg (· ≫ X'.curve.zero) (strAct_pr D X' γ)
    · refine ((Category.assoc _ _ _).trans ((congrArg (CategoryStruct.comp _)
        (Limits.pullback.lift_snd _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ strAct D X' γ) (Limits.pullback.lift_snd _ _ _)).trans
        (Category.id_comp _))))).trans ?_
      refine Eq.symm ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (CategoryStruct.comp (strAct D X' γ))
        (Limits.pullback.lift_snd _ _ _)).trans ?_
      exact Category.comp_id _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6d)]** Pulling the tautological section along the cover
translation yields the tautological section at the translated vector. -/
theorem strActHom_pullSection (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    EllHom.pullSection (CommRingCat.of ℚ) (strActHom D X' γ)
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str v)) =
    EllipticCurve.Point.asSection X'.curve (strPr D X')
      (strPt D str (γ • v)) := by
  refine section_ext_fst X'.curve (strPr D X') _ _ ?_
  -- LHS-fst: through the top and the map's fst law
  have h1 : (EllHom.pullSection (CommRingCat.of ℚ) (strActHom D X' γ)
      (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str v))).1 ≫ (strActHom D X' γ).top =
      strAct D X' γ ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
        (strPt D str v)).1 :=
    (strActHom D X' γ).isPullback.lift_fst _ _ _
  have h2 : (strActHom D X' γ).top ≫ pullback.fst X'.curve.π (strPr D X') =
      pullback.fst X'.curve.π (strPr D X') := by
    refine (Limits.pullback.lift_fst _ _ _).trans ?_
    exact Category.comp_id _
  calc (EllHom.pullSection (CommRingCat.of ℚ) (strActHom D X' γ)
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v))).1 ≫ pullback.fst X'.curve.π (strPr D X')
      = (EllHom.pullSection (CommRingCat.of ℚ) (strActHom D X' γ)
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str v))).1 ≫ (strActHom D X' γ).top ≫
          pullback.fst X'.curve.π (strPr D X') :=
        (congrArg (CategoryStruct.comp _) h2).symm
    _ = ((EllHom.pullSection (CommRingCat.of ℚ) (strActHom D X' γ)
          (EllipticCurve.Point.asSection X'.curve (strPr D X')
            (strPt D str v))).1 ≫ (strActHom D X' γ).top) ≫
          pullback.fst X'.curve.π (strPr D X') :=
        (Category.assoc _ _ _).symm
    _ = (strAct D X' γ ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)).1) ≫ pullback.fst X'.curve.π (strPr D X') :=
        congrArg (· ≫ pullback.fst X'.curve.π (strPr D X')) h1
    _ = strAct D X' γ ≫ (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str v)).1 ≫ pullback.fst X'.curve.π (strPr D X') :=
        Category.assoc _ _ _
    _ = strAct D X' γ ≫ (strPt D str v).1 :=
        congrArg (CategoryStruct.comp (strAct D X' γ))
          (EllipticCurve.Point.asSection_val_fst X'.curve (strPr D X')
            (strPt D str v))
    _ = (strPt D str (γ • v)).1 := strAct_strPt D str γ v
    _ = (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (γ • v))).1 ≫ pullback.fst X'.curve.π (strPr D X') :=
        (EllipticCurve.Point.asSection_val_fst X'.curve (strPr D X')
          (strPt D str (γ • v))).symm

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6e)]** THE VALUE EQUIVARIANCE: transporting the tautological
value along the cover translation is the `γ`-translation of the framed problem
(level components by the section additivity at the matrix columns; frame by the
tautological frame law). -/
theorem strValue_equivariant (D : GaloisRepData N) [Fact (1 < N)]
    {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (sympFramedProblem D).map (strActHom D X' γ).op (strValue D str) =
    (sympFramedSmulNat D γ).app
      (Opposite.op (X'.pullbackAlong (strPr D X'))) (strValue D str) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · -- the level components
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show EllHom.pullSection (CommRingCat.of ℚ) (strActHom D X' γ)
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 0 1))) = _
      refine (strActHom_pullSection D str γ (Pi.single 0 1)).trans ?_
      exact strSec_col D str γ 0
    · show EllHom.pullSection (CommRingCat.of ℚ) (strActHom D X' γ)
        (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str (Pi.single 1 1))) = _
      refine (strActHom_pullSection D str γ (Pi.single 1 1)).trans ?_
      exact strSec_col D str γ 1
  · -- the frame component
    refine Subtype.ext ?_
    show (strActHom D X' γ).baseHom ≫ strTaut D X' =
      strTaut D X' ≫ wFramesRightMul D γ
    exact strAct_taut D X' γ

/-- **[T-EQ-3d-M5 (6f) prep]** The base morphism of an `eqToHom` in `Ell/ℚ`. -/
theorem eqToHom_baseHom {A B : EllObj (CommRingCat.of ℚ)} (h : A = B) :
    (eqToHom h : A ⟶ B).baseHom =
      eqToHom (congrArg ModularCurves.EllObj.base h) := by
  subst h
  rfl

/-- **[T-EQ-3d-M5 (6f) prep]** The top morphism of an `eqToHom` in `Ell/ℚ`. -/
theorem eqToHom_top {A B : EllObj (CommRingCat.of ℚ)} (h : A = B) :
    (eqToHom h : A ⟶ B).top =
      eqToHom (congrArg (fun O : EllObj (CommRingCat.of ℚ) => O.curve.E) h) := by
  subst h
  rfl

/-- **[T-EQ-3d-M5 (6f) prep]** `eqToHom`-legs of pullback comparisons along an
equality of base maps. -/
theorem eqToHom_pullback_fst {Y W : Scheme.{0}} (π : Y ⟶ W)
    {T : Scheme.{0}} {a b : T ⟶ W} (hab : a = b) :
    eqToHom (congrArg (fun m : T ⟶ W => pullback π m) hab) ≫
      pullback.fst π b = pullback.fst π a := by
  subst hab
  simp

theorem eqToHom_pullback_snd {Y W : Scheme.{0}} (π : Y ⟶ W)
    {T : Scheme.{0}} {a b : T ⟶ W} (hab : a = b) :
    eqToHom (congrArg (fun m : T ⟶ W => pullback π m) hab) ≫
      pullback.snd π b = pullback.snd π a := by
  subst hab
  simp

/-- **[T-EQ-3d-M5 (6f) prep]** Presentation-independent naturality of a relative
representation datum (public form of the engine-side `map_eqv`). -/
theorem rhoMap_eqv {P : ModularCurves.ModuliProblem (CommRingCat.of ℚ)}
    {X₀ : EllObj (CommRingCat.of ℚ)}
    (d₀ : ModuliProblem.RelRepData P X₀) {T T' : Scheme.{0}}
    {g : T ⟶ X₀.base} {g' : T' ⟶ X₀.base}
    (w : X₀.pullbackAlong g' ⟶ X₀.pullbackAlong g) (kk : T' ⟶ T)
    (hbk : w.baseHom = kk) (hk : kk ≫ g = g')
    (hwπ : w ≫ X₀.pullbackAlongπ g = X₀.pullbackAlongπ g')
    (h : { h : T ⟶ d₀.Z // h ≫ d₀.f = g }) :
    P.map w.op (d₀.eqv g h) =
      d₀.eqv g' ⟨kk ≫ h.1, by rw [Category.assoc, h.2, hk]⟩ := by
  subst hk
  have hw : w = X₀.pullbackAlongMap g kk := by
    apply (EllObj.homPullbackAlongEquiv X₀ g
      (X₀.pullbackAlong (kk ≫ g))).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show w ≫ X₀.pullbackAlongπ g =
        X₀.pullbackAlongMap g kk ≫ X₀.pullbackAlongπ g
      rw [hwπ, ModuliProblem.pullbackAlongMap_pullbackAlongπ]
    · exact hbk
  rw [hw]
  exact (d₀.nat g kk h).symm

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6f)]** The cover translation as an endomorphism of the
`g₃`-pullback of the anchor object. -/
noncomputable def strActX (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)} {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    X.pullbackAlong (strPr D (X.pullbackAlong k) ≫ k) ⟶
      X.pullbackAlong (strPr D (X.pullbackAlong k) ≫ k) :=
  EllObj.homToPullbackAlong
    (X.pullbackAlongπ (strPr D (X.pullbackAlong k) ≫ k))
    (strAct D (X.pullbackAlong k) γ)
    (by
      show strAct D (X.pullbackAlong k) γ ≫ strPr D (X.pullbackAlong k) ≫ k =
        strPr D (X.pullbackAlong k) ≫ k
      rw [← Category.assoc, strAct_pr])

open scoped FintypeCatDiscrete in
theorem strActX_π (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)} {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strActX D k γ ≫ X.pullbackAlongπ (strPr D (X.pullbackAlong k) ≫ k) =
      X.pullbackAlongπ (strPr D (X.pullbackAlong k) ≫ k) :=
  EllObj.homToPullbackAlong_pullbackAlongπ _ _ _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6f)]** The cover translation commutes with the tautological
projection of the pulled object. -/
theorem strActHom_π (D : GaloisRepData N) [Fact (1 < N)]
    (X' : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strActHom D X' γ ≫ X'.pullbackAlongπ (strPr D X') =
      X'.pullbackAlongπ (strPr D X') := by
  refine EllHom.ext ?_ ?_
  · show strAct D X' γ ≫ strPr D X' = strPr D X'
    exact strAct_pr D X' γ
  · show (strActHom D X' γ).top ≫ pullback.fst X'.curve.π (strPr D X') =
      pullback.fst X'.curve.π (strPr D X')
    refine (Limits.pullback.lift_fst _ _ _).trans ?_
    exact Category.comp_id _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6f)]** The anchor-side translation commutes with the chart
comparison. -/
theorem strActX_pullbackAlongMap (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)} {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strActX D k γ ≫ X.pullbackAlongMap k (strPr D (X.pullbackAlong k)) =
      X.pullbackAlongMap k (strPr D (X.pullbackAlong k)) := by
  refine EllHom.ext ?_ ?_
  · show strAct D (X.pullbackAlong k) γ ≫ strPr D (X.pullbackAlong k) =
      strPr D (X.pullbackAlong k)
    exact strAct_pr D (X.pullbackAlong k) γ
  · apply Limits.pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (CategoryStruct.comp (strActX D k γ).top)
        ((Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
      refine Eq.trans (Limits.pullback.lift_fst _ _ _) ?_
      exact ((Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (CategoryStruct.comp (strActX D k γ).top)
        (Limits.pullback.lift_snd _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg
        (· ≫ strPr D (X.pullbackAlong k))
        (Limits.pullback.lift_snd _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (CategoryStruct.comp (Limits.pullback.snd
        X.curve.π (strPr D (X.pullbackAlong k) ≫ k)))
        (strAct_pr D (X.pullbackAlong k) γ)) ?_
      exact (Limits.pullback.lift_snd _ _ _).symm

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6f)]** THE TRANSLATION SQUARE: the anchor-side translation
conjugates to the cover-side translation across the associativity comparison. -/
theorem strActX_square (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)} {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strActX D k γ ≫ EllObj.toPullbackAlong
      (X.pullbackAlongMap k (strPr D (X.pullbackAlong k))) =
    EllObj.toPullbackAlong
      (X.pullbackAlongMap k (strPr D (X.pullbackAlong k))) ≫
      strActHom D (X.pullbackAlong k) γ := by
  apply (EllObj.homPullbackAlongEquiv (X.pullbackAlong k)
    (strPr D (X.pullbackAlong k)) _).injective
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show (strActX D k γ ≫ EllObj.toPullbackAlong
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))) ≫
        (X.pullbackAlong k).pullbackAlongπ (strPr D (X.pullbackAlong k)) =
      (EllObj.toPullbackAlong
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k))) ≫
        strActHom D (X.pullbackAlong k) γ) ≫
        (X.pullbackAlong k).pullbackAlongπ (strPr D (X.pullbackAlong k))
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (CategoryStruct.comp (strActX D k γ))
      (EllObj.toPullbackAlong_pullbackAlongπ
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k))))) ?_
    refine Eq.trans (strActX_pullbackAlongMap D k γ) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (CategoryStruct.comp (EllObj.toPullbackAlong
      (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))))
      (strActHom_π D (X.pullbackAlong k) γ)) ?_
    exact EllObj.toPullbackAlong_pullbackAlongπ
      (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))
  · show (strActX D k γ).baseHom ≫ 𝟙 _ = 𝟙 _ ≫ strAct D (X.pullbackAlong k) γ
    rw [Category.comp_id, Category.id_comp]
    rfl

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M5 (6f) DONE]** THE Z-POINT EQUIVARIANCE: the classified point of
the tautological value intertwines the cover translation with the quotient
action. -/
theorem strZ_equivariant (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strAct D (X.pullbackAlong k) γ ≫ (strZ D d k str).1 =
      (strZ D d k str).1 ≫ d.σZ.hom γ := by
  have hg : strAct D (X.pullbackAlong k) γ ≫
      (strPr D (X.pullbackAlong k) ≫ k) = strPr D (X.pullbackAlong k) ≫ k := by
    rw [← Category.assoc, strAct_pr]
  -- the classified value of strZ
  have hVAL : d.eqv (strPr D (X.pullbackAlong k) ≫ k) (strZ D d k str) =
      (sympFramedProblem D).map
        (EllObj.toPullbackAlong
          (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))).op
        (strValue D str) := by
    show d.eqv _ ((d.eqv _).symm _) = _
    exact (d.eqv (strPr D (X.pullbackAlong k) ≫ k)).apply_symm_apply _
  -- the left side through the presentation-independent naturality
  have hnat := rhoMap_eqv d.toRelRepData (strActX D k γ)
    (strAct D (X.pullbackAlong k) γ) rfl hg (strActX_π D k γ)
    (strZ D d k str)
  -- the value computation
  have hval2 : (sympFramedProblem D).map (strActX D k γ).op
      (d.eqv (strPr D (X.pullbackAlong k) ≫ k) (strZ D d k str)) =
      ((sympFramedAut D) γ⁻¹).hom.app
        (Opposite.op (X.pullbackAlong (strPr D (X.pullbackAlong k) ≫ k)))
        (d.eqv (strPr D (X.pullbackAlong k) ≫ k) (strZ D d k str)) := by
    rw [hVAL]
    refine Eq.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      (EllObj.toPullbackAlong (X.pullbackAlongMap k
        (strPr D (X.pullbackAlong k)))).op (strActX D k γ).op
      (strValue D str)).symm ?_
    rw [show (EllObj.toPullbackAlong (X.pullbackAlongMap k
        (strPr D (X.pullbackAlong k)))).op ≫ (strActX D k γ).op =
      (strActX D k γ ≫ EllObj.toPullbackAlong (X.pullbackAlongMap k
        (strPr D (X.pullbackAlong k)))).op from rfl]
    rw [strActX_square D k γ]
    refine Eq.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      (strActHom D (X.pullbackAlong k) γ).op
      (EllObj.toPullbackAlong (X.pullbackAlongMap k
        (strPr D (X.pullbackAlong k)))).op (strValue D str)) ?_
    rw [strValue_equivariant D str γ]
    -- naturality of the translation
    have hφ : ((sympFramedAut D) γ⁻¹).hom = sympFramedSmulNat D γ := by
      rw [show ((sympFramedAut D) γ⁻¹).hom =
        sympFramedSmulNat D ((γ⁻¹)⁻¹) from rfl, inv_inv]
    have hn := (sympFramedSmulNat D γ).naturality
      (EllObj.toPullbackAlong (X.pullbackAlongMap k
        (strPr D (X.pullbackAlong k)))).op
    have hnat2 := congrArg
      (fun (F : (sympFramedProblem D).obj (Opposite.op
          ((X.pullbackAlong k).pullbackAlong (strPr D (X.pullbackAlong k)))) ⟶
        (sympFramedProblem D).obj (Opposite.op
          (X.pullbackAlong (strPr D (X.pullbackAlong k) ≫ k)))) =>
        F (strValue D str)) hn
    refine Eq.trans hnat2.symm ?_
    exact congrArg (fun (m : sympFramedProblem D ⟶ sympFramedProblem D) =>
      m.app (Opposite.op (X.pullbackAlong
        (strPr D (X.pullbackAlong k) ≫ k)))
      ((sympFramedProblem D).map (EllObj.toPullbackAlong
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))).op
        (strValue D str))) hφ.symm
  -- assemble via the equivariance and injectivity
  have hfinal := hnat.symm.trans (hval2.trans (d.equivariant
    (strPr D (X.pullbackAlong k) ≫ k) (strZ D d k str) γ).symm)
  have hsub := (d.eqv (strPr D (X.pullbackAlong k) ≫ k)).injective hfinal
  exact congrArg Subtype.val hsub

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6]** The descent-ready invariant map over the cover: the
classified `Z`-point followed by the quotient projection. -/
noncomputable def strSigmaP (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve) :
    strCover D (X.pullbackAlong k) ⟶ d.σZ.relQuotient d.f d.over_base :=
  (strZ D d k str).1 ≫ d.σZ.relQuotientπ d.f d.over_base

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 (6g)]** σP is invariant under the cover translation. -/
theorem strAct_strSigmaP (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    strAct D (X.pullbackAlong k) γ ≫ strSigmaP D d k str =
      strSigmaP D d k str := by
  rw [strSigmaP, ← Category.assoc, strZ_equivariant, Category.assoc,
    d.σZ.hom_comp_relQuotientπ d.f d.over_base γ]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6]** σP lies over the base leg `strPr ≫ k`. -/
theorem strSigmaP_struct (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve) :
    strSigmaP D d k str ≫ d.σZ.relQuotientStruct d.f d.over_base =
      strPr D (X.pullbackAlong k) ≫ k := by
  rw [strSigmaP, Category.assoc,
    d.σZ.relQuotientπ_comp_relQuotientStruct d.f d.over_base,
    (strZ D d k str).2]

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 (7a)]** THE H-CONDITION: any two maps into the cover with equal
base legs have equal `σP`-composites — at each geometric point the two lifts
differ by a frame translation (M4), which `σP` absorbs (6g); conclude by the
clopen-agreement engine at the finite étale quotient structure map. -/
theorem strSigmaP_coequalizes (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve)
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ strCover D (X.pullbackAlong k))
    (hbase : g₁ ≫ strPr D (X.pullbackAlong k) =
      g₂ ≫ strPr D (X.pullbackAlong k)) :
    g₁ ≫ strSigmaP D d k str = g₂ ≫ strSigmaP D d k str := by
  have hfe := d.σZ.relQuotientStruct_finite_etale_of_free d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D)) d.finite d.etale
  haveI hFin : IsFinite (d.σZ.relQuotientStruct d.f d.over_base) := hfe.1
  haveI hEt : Etale (d.σZ.relQuotientStruct d.f d.over_base) := hfe.2
  haveI hSep : IsSeparated (d.σZ.relQuotientStruct d.f d.over_base) :=
    inferInstance
  have hfg : (g₁ ≫ strSigmaP D d k str) ≫
      d.σZ.relQuotientStruct d.f d.over_base =
      (g₂ ≫ strSigmaP D d k str) ≫
      d.σZ.relQuotientStruct d.f d.over_base := by
    rw [Category.assoc, Category.assoc, strSigmaP_struct,
      ← Category.assoc, ← Category.assoc, hbase]
  refine eq_of_forall_geomPt_agree
    (d.σZ.relQuotientStruct d.f d.over_base) _ _ hfg ?_
  intro ω
  -- the two tautological frames over the geometric point lie over one base point
  have hover : (geomPt Z ω ≫ g₁ ≫ strTaut D (X.pullbackAlong k)) ≫
      wFramesπ D =
      (geomPt Z ω ≫ g₂ ≫ strTaut D (X.pullbackAlong k)) ≫ wFramesπ D := by
    simp only [Category.assoc, strTaut_π]
    rw [← Category.assoc g₁, ← Category.assoc g₂, hbase]
  -- the frame-graph relation: they differ by a right translation
  obtain ⟨γ, hγ⟩ := exists_frameGraph_rel D
    (geomPt Z ω ≫ g₁ ≫ strTaut D (X.pullbackAlong k))
    (geomPt Z ω ≫ g₂ ≫ strTaut D (X.pullbackAlong k)) hover
  -- hence the cover points differ by the cover translation
  have hcov : geomPt Z ω ≫ g₂ =
      (geomPt Z ω ≫ g₁) ≫ strAct D (X.pullbackAlong k) γ := by
    apply pullback.hom_ext
    · show (geomPt Z ω ≫ g₂) ≫ strPr D (X.pullbackAlong k) =
        ((geomPt Z ω ≫ g₁) ≫ strAct D (X.pullbackAlong k) γ) ≫
          strPr D (X.pullbackAlong k)
      rw [Category.assoc _ (strAct D (X.pullbackAlong k) γ), strAct_pr,
        Category.assoc, Category.assoc, hbase]
    · show (geomPt Z ω ≫ g₂) ≫ strTaut D (X.pullbackAlong k) =
        ((geomPt Z ω ≫ g₁) ≫ strAct D (X.pullbackAlong k) γ) ≫
          strTaut D (X.pullbackAlong k)
      simp only [Category.assoc, strAct_taut]
      simpa only [Category.assoc] using hγ
  -- σP absorbs the translation
  calc geomPt Z ω ≫ g₁ ≫ strSigmaP D d k str
      = (geomPt Z ω ≫ g₁) ≫ strSigmaP D d k str :=
        (Category.assoc _ _ _).symm
    _ = (geomPt Z ω ≫ g₁) ≫ strAct D (X.pullbackAlong k) γ ≫
          strSigmaP D d k str := by rw [strAct_strSigmaP]
    _ = ((geomPt Z ω ≫ g₁) ≫ strAct D (X.pullbackAlong k) γ) ≫
          strSigmaP D d k str := (Category.assoc _ _ _).symm
    _ = (geomPt Z ω ≫ g₂) ≫ strSigmaP D d k str := by rw [← hcov]
    _ = geomPt Z ω ≫ g₂ ≫ strSigmaP D d k str := Category.assoc _ _ _

open scoped FintypeCatDiscrete in
/-- The cover projection is (fpqc-)surjective: base change of the surjective
frames structure map. -/
instance strPr_surjective (X' : EllObj (CommRingCat.of ℚ)) :
    Surjective (strPr D X') :=
  MorphismProperty.pullback_fst _ _ (wFramesπ_surjective D)

open scoped FintypeCatDiscrete in
/-- The cover projection is flat (base change of the finite étale frames map). -/
instance strPr_flat (X' : EllObj (CommRingCat.of ℚ)) : Flat (strPr D X') :=
  haveI : Etale (wFramesπ D) := (wFramesπ_finite_etale D).2
  MorphismProperty.pullback_fst _ _ (inferInstance : Flat (wFramesπ D))

open scoped FintypeCatDiscrete in
/-- The cover projection is quasi-compact (base change of a finite morphism). -/
instance strPr_quasiCompact (X' : EllObj (CommRingCat.of ℚ)) :
    QuasiCompact (strPr D X') :=
  haveI : IsFinite (wFramesπ D) := (wFramesπ_finite_etale D).1
  MorphismProperty.pullback_fst _ _ (inferInstance : QuasiCompact (wFramesπ D))

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 (7b)]** The cover projection is an fpqc effective epimorphism. -/
instance strPr_effectiveEpi (X' : EllObj (CommRingCat.of ℚ)) :
    EffectiveEpi (strPr D X') :=
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat _

open scoped FintypeCatDiscrete in
instance strPr_epi (X' : EllObj (CommRingCat.of ℚ)) : Epi (strPr D X') :=
  Flat.epi_of_flat_of_surjective _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 (7b)] THE 3d DESCENT MAP** — the invariant map descends through
the fpqc effective-epi cover projection to a section of the quotient (typed at
the pullback base, which is definitionally `T'`). -/
noncomputable def strSection (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve) :
    (X.pullbackAlong k).base ⟶ d.σZ.relQuotient d.f d.over_base :=
  EffectiveEpi.desc (strPr D (X.pullbackAlong k)) (strSigmaP D d k str)
    (fun g₁ g₂ h => strSigmaP_coequalizes D d k str g₁ g₂ h)

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 (7b)]** The descent factorisation: the section pulls back to
the invariant map. -/
theorem strPr_strSection (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve) :
    strPr D (X.pullbackAlong k) ≫ strSection D d k str = strSigmaP D d k str :=
  EffectiveEpi.fac _ _ _

open scoped FintypeCatDiscrete in
/-- **[T-EQ-3d-M6 (7b)]** The descended section lies over `k`. -/
theorem strSection_struct (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve) :
    strSection D d k str ≫ d.σZ.relQuotientStruct d.f d.over_base = k := by
  have h1 := congrArg (· ≫ d.σZ.relQuotientStruct d.f d.over_base)
    (strPr_strSection D d k str)
  simp only [Category.assoc] at h1
  rw [strSigmaP_struct] at h1
  exact (cancel_epi (strPr D (X.pullbackAlong k))).mp h1

end StructuresToSections

section PointLifting

/-- **[T-3E-L1]** Every algebraically-closed-field point lifts through a finite
surjective morphism: the fibre is a nonzero finite algebra over the field, whose
residue at any maximal ideal is the field itself. -/
theorem exists_specPoint_lift_of_finite_surjective {Y Z : Scheme.{0}}
    (f : Y ⟶ Z) [IsFinite f] [Surjective f]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (z : Spec (CommRingCat.of Ω) ⟶ Z) :
    ∃ y : Spec (CommRingCat.of Ω) ⟶ Y, y ≫ f = z := by
  classical
  haveI hFinP : IsFinite (pullback.snd f z) :=
    MorphismProperty.pullback_snd _ _ ‹IsFinite f›
  haveI hSurP : Surjective (pullback.snd f z) :=
    MorphismProperty.pullback_snd _ _ ‹Surjective f›
  haveI : IsAffineHom (pullback.snd f z) := inferInstance
  haveI : IsAffine (pullback f z) :=
    isAffine_of_isAffineHom (pullback.snd f z)
  set φ : CommRingCat.of Ω ⟶ Γ(pullback f z, ⊤) :=
    Spec.preimage ((pullback f z).isoSpec.inv ≫ pullback.snd f z) with hφdef
  have hφ : Spec.map φ = (pullback f z).isoSpec.inv ≫ pullback.snd f z :=
    Spec.map_preimage _
  -- finiteness of the fibre algebra
  have hφfin : φ.hom.Finite := by
    have hcomp : pullback.snd f z = (pullback f z).isoSpec.hom ≫ Spec.map φ := by
      rw [hφ, Iso.hom_inv_id_assoc]
    have h1 : (pullback.snd f z).appTop.hom.Finite := Scheme.Hom.finite_appTop _
    rw [hcomp, Scheme.Hom.comp_appTop] at h1
    haveI : IsIso ((pullback f z).isoSpec.hom.appTop) :=
      ⟨⟨(pullback f z).isoSpec.inv.appTop,
        by rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop],
        by rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]⟩⟩
    have h2 : (Spec.map φ).appTop.hom.Finite := by
      have h3 : (Spec.map φ).appTop =
          ((Spec.map φ).appTop ≫ (pullback f z).isoSpec.hom.appTop) ≫
            inv ((pullback f z).isoSpec.hom.appTop) := by
        rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [h3]
      exact RingHom.Finite.comp
        (RingHom.Finite.of_surjective _
          ((ConcreteCategory.bijective_of_isIso
            (inv ((pullback f z).isoSpec.hom.appTop))).2)) h1
    have hφeq : φ = (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫
        (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso Γ(pullback f z, ⊤)).hom := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [hφeq]
    exact RingHom.Finite.comp
      (RingHom.Finite.comp
        (RingHom.Finite.of_surjective _
          ((ConcreteCategory.bijective_of_isIso
            (Scheme.ΓSpecIso Γ(pullback f z, ⊤)).hom).2)) h2)
      (RingHom.Finite.of_surjective _
        ((ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).2))
  letI : Algebra Ω ↑Γ(pullback f z, ⊤) := φ.hom.toAlgebra
  haveI hMF : Module.Finite Ω ↑Γ(pullback f z, ⊤) := hφfin
  -- the fibre is nonempty, so its algebra is nontrivial
  have hne : Nonempty ↥(pullback f z) := by
    obtain ⟨s₀⟩ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstance
    obtain ⟨p₀, _⟩ := hSurP.1 s₀
    exact ⟨p₀⟩
  haveI hnt : Nontrivial ↑Γ(pullback f z, ⊤) := by
    obtain ⟨p⟩ := hne
    set q := (pullback f z).isoSpec.hom.base p with hq
    exact ⟨0, 1, fun h01 => q.asIdeal.ne_top_iff_one.mp q.isPrime.ne_top
      (h01 ▸ q.asIdeal.zero_mem)⟩
  -- a maximal ideal with residue field Ω
  obtain ⟨m, hm⟩ := Ideal.exists_maximal ↑Γ(pullback f z, ⊤)
  haveI := hm
  haveI : Field (↑Γ(pullback f z, ⊤) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite Ω (↑Γ(pullback f z, ⊤) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ Ω m).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral Ω (↑Γ(pullback f z, ⊤) ⧸ m) :=
    Algebra.IsIntegral.of_finite Ω _
  have hbij : Function.Bijective (algebraMap Ω (↑Γ(pullback f z, ⊤) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  set e := RingEquiv.ofBijective _ hbij with he
  set χ : Γ(pullback f z, ⊤) ⟶ CommRingCat.of Ω :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk m)) with hχ
  have hχφ : φ ≫ χ = 𝟙 (CommRingCat.of Ω) := by
    refine CommRingCat.hom_ext (RingHom.ext fun ω => ?_)
    show e.symm (Ideal.Quotient.mk m (φ.hom ω)) = ω
    have hmk : Ideal.Quotient.mk m (φ.hom ω) =
        algebraMap Ω (↑Γ(pullback f z, ⊤) ⧸ m) ω := rfl
    rw [hmk]
    exact e.symm_apply_apply ω
  have hpre : Spec.preimage (𝟙 (Spec (CommRingCat.of Ω))) =
      𝟙 (CommRingCat.of Ω) :=
    Spec.map_injective (by rw [Spec.map_preimage, Spec.map_id])
  set secpair := (EllipticCurve.sectionsEquivRingHomUnder
    (pullback.snd f z) φ hφ (𝟙 (Spec (CommRingCat.of Ω)))).symm
    ⟨χ, by rw [hχφ, hpre]⟩ with hsp
  refine ⟨secpair.1 ≫ pullback.fst f z, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, secpair.2,
    Category.id_comp]

/-- **[T-3E-W0]** Two `Ω`-points of a finite `ℚ`-algebra factor jointly through
a common finite subfield `κ ≤ Ω`, which embeds into `ℚ̄`: transport of point
comparisons from arbitrary field bases to the algebraic closure. -/
theorem ringHomPair_factor_qbar {B : Type} [CommRing B] [Algebra ℚ B]
    [Module.Finite ℚ B] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (χ₁ χ₂ : B →ₐ[ℚ] Ω) :
    ∃ (κ : Subalgebra ℚ Ω) (mk₁ mk₂ : B →ₐ[ℚ] κ)
      (lam : ↥κ →ₐ[ℚ] AlgebraicClosure ℚ),
      Function.Injective lam ∧
      κ.val.comp mk₁ = χ₁ ∧ κ.val.comp mk₂ = χ₂ := by
  classical
  haveI h1 : Module.Finite ℚ ↥χ₁.range :=
    Module.Finite.of_surjective χ₁.rangeRestrict.toLinearMap
      χ₁.rangeRestrict_surjective
  haveI h2 : Module.Finite ℚ ↥χ₂.range :=
    Module.Finite.of_surjective χ₂.rangeRestrict.toLinearMap
      χ₂.rangeRestrict_surjective
  haveI hκfin : Module.Finite ℚ ↥(χ₁.range ⊔ χ₂.range) :=
    Subalgebra.finite_sup _ _
  haveI hκint : Algebra.IsIntegral ℚ ↥(χ₁.range ⊔ χ₂.range) :=
    Algebra.IsIntegral.of_finite ℚ _
  have hfield : IsField ↥(χ₁.range ⊔ χ₂.range) :=
    isField_of_isIntegral_of_isField' (Field.toIsField ℚ)
  letI : Field ↥(χ₁.range ⊔ χ₂.range) := hfield.toField
  haveI : Algebra.IsAlgebraic ℚ ↥(χ₁.range ⊔ χ₂.range) :=
    Algebra.IsAlgebraic.of_finite ℚ _
  refine ⟨χ₁.range ⊔ χ₂.range,
    (Subalgebra.inclusion le_sup_left).comp χ₁.rangeRestrict,
    (Subalgebra.inclusion le_sup_right).comp χ₂.rangeRestrict,
    IsAlgClosed.lift, ?_, ?_, ?_⟩
  · exact RingHom.injective _
  · exact AlgHom.ext fun b => rfl
  · exact AlgHom.ext fun b => rfl

open scoped FintypeCatDiscrete in
/-- **[T-3E-W1]** Right-translation cancellation at arbitrary field points: the
frames form a torsor, so a translated point determines the translator
(image-field factoring + the ℚ̄-reads). -/
theorem wFramesRightMul_cancel (D : GaloisRepData N) {Ω : Type} [Field Ω]
    (F : Spec (CommRingCat.of Ω) ⟶ wFrames D)
    {γ γ' : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)}
    (h : F ≫ wFramesRightMul D γ = F ≫ wFramesRightMul D γ') : γ = γ' := by
  classical
  set c := Spec.preimage F with hc
  have hF : Spec.map c = F := Spec.map_preimage F
  have halg : CommRingCat.ofHom (wFramesRightMulAlg D γ).hom.hom.toRingHom ≫ c =
      CommRingCat.ofHom (wFramesRightMulAlg D γ').hom.hom.toRingHom ≫ c := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hF]
    exact h
  -- ℚ-algebra structure on Ω through the base point
  letI : Algebra ℚ Ω := (Spec.preimage (F ≫ wFramesπ D)).hom.toAlgebra
  haveI hMF : Module.Finite ℚ (wFramesAlgebra D : Type 0) :=
    (wFramesAlgebra D).property.left
  set χ : (wFramesAlgebra D : Type 0) →ₐ[ℚ] Ω := c.hom.toRatAlgHom with hχ
  -- the image field and its ℚ̄-embedding
  haveI hκfin : Module.Finite ℚ ↥χ.range :=
    Module.Finite.of_surjective χ.rangeRestrict.toLinearMap
      χ.rangeRestrict_surjective
  haveI hκint : Algebra.IsIntegral ℚ ↥χ.range :=
    Algebra.IsIntegral.of_finite ℚ _
  have hfield : IsField ↥χ.range :=
    isField_of_isIntegral_of_isField' (Field.toIsField ℚ)
  letI : Field ↥χ.range := hfield.toField
  haveI : Algebra.IsAlgebraic ℚ ↥χ.range := Algebra.IsAlgebraic.of_finite ℚ _
  set ν : (wFramesAlgebra D : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ :=
    (IsAlgClosed.lift (M := AlgebraicClosure ℚ)).comp χ.rangeRestrict with hν
  -- the translated algebra maps agree into the image field, hence into ℚ̄
  have hmkeq : χ.rangeRestrict.comp (wFramesRightMulAlg D γ).hom.hom =
      χ.rangeRestrict.comp (wFramesRightMulAlg D γ').hom.hom := by
    refine AlgHom.ext fun b => Subtype.ext ?_
    show χ ((wFramesRightMulAlg D γ).hom.hom b) =
      χ ((wFramesRightMulAlg D γ').hom.hom b)
    exact RingHom.congr_fun (congrArg (fun (m : CommRingCat.of
      (wFramesAlgebra D : Type 0) ⟶ CommRingCat.of Ω) => m.hom) halg) b
  have hνeq : ν.comp (wFramesRightMulAlg D γ).hom.hom =
      ν.comp (wFramesRightMulAlg D γ').hom.hom := by
    rw [hν, AlgHom.comp_assoc, AlgHom.comp_assoc, hmkeq]
  -- the ℚ̄-point and the translated-point equality
  set Ft : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ wFrames D :=
    Spec.map (CommRingCat.ofHom ν.toRingHom) with hFt
  have hpts : Ft ≫ wFramesRightMul D γ = Ft ≫ wFramesRightMul D γ' := by
    show Spec.map (CommRingCat.ofHom ν.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (wFramesRightMulAlg D γ).hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom ν.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (wFramesRightMulAlg D γ').hom.hom.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext ?_)
    show ν.toRingHom.comp (wFramesRightMulAlg D γ).hom.hom.toRingHom =
      ν.toRingHom.comp (wFramesRightMulAlg D γ').hom.hom.toRingHom
    have h1 : ν.toRingHom.comp (wFramesRightMulAlg D γ).hom.hom.toRingHom =
        (ν.comp (wFramesRightMulAlg D γ).hom.hom).toRingHom := rfl
    have h2 : ν.toRingHom.comp (wFramesRightMulAlg D γ').hom.hom.toRingHom =
        (ν.comp (wFramesRightMulAlg D γ').hom.hom).toRingHom := rfl
    rw [h1, h2, hνeq]
  -- read the equality at ℚ̄ through the torsor structure
  have h₁ : Ft ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    specQhom_eq _ _
  have hnatγ := qbarPointsRead_map (frameRightMulMor D γ) ⟨Ft, h₁⟩
  have hnatγ' := qbarPointsRead_map (frameRightMulMor D γ') ⟨Ft, h₁⟩
  have hrdeq : qbarPointsRead (frameContAction D)
      ⟨Ft ≫ wFramesRightMul D γ, specQhom_eq _ _⟩ =
      qbarPointsRead (frameContAction D)
      ⟨Ft ≫ wFramesRightMul D γ', specQhom_eq _ _⟩ :=
    congrArg (qbarPointsRead (frameContAction D)) (Subtype.ext hpts)
  have hfin : (qbarPointsRead (frameContAction D) ⟨Ft, h₁⟩ :
      Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) * γ =
      qbarPointsRead (frameContAction D) ⟨Ft, h₁⟩ * γ' :=
    (hnatγ.symm.trans (hrdeq.trans hnatγ'))
  exact mul_left_cancel hfin

open scoped FintypeCatDiscrete in
/-- **[T-3E-L2 prep]** The pulled quotient action as a `SchemeAction` on the
π-fibre along any quotient point. -/
noncomputable def relQFibreAction (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f] {W : Scheme.{0}}
    (p : W ⟶ d.σZ.relQuotient d.f d.over_base) :
    AlgebraicGeometry.SchemeAction
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
      (pullback (d.σZ.relQuotientπ d.f d.over_base) p) where
  hom γ := d.σZ.pullbackRelQSMul d.f d.over_base p γ
  hom_one := by
    apply pullback.hom_ext
    · rw [Category.id_comp]
      refine (d.σZ.pullbackRelQSMul_fst d.f d.over_base p 1).trans ?_
      rw [d.σZ.hom_one, Category.comp_id]
    · rw [Category.id_comp]
      exact d.σZ.pullbackRelQSMul_snd d.f d.over_base p 1
  hom_mul γ δ := by
    apply pullback.hom_ext
    · rw [Category.assoc,
        d.σZ.pullbackRelQSMul_fst d.f d.over_base p (γ * δ),
        d.σZ.pullbackRelQSMul_fst d.f d.over_base p δ,
        ← Category.assoc, d.σZ.pullbackRelQSMul_fst d.f d.over_base p γ,
        Category.assoc, d.σZ.hom_mul]
    · rw [Category.assoc,
        d.σZ.pullbackRelQSMul_snd d.f d.over_base p (γ * δ),
        d.σZ.pullbackRelQSMul_snd d.f d.over_base p δ,
        d.σZ.pullbackRelQSMul_snd d.f d.over_base p γ]

@[simp]
theorem relQFibreAction_hom (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f] {W : Scheme.{0}}
    (p : W ⟶ d.σZ.relQuotient d.f d.over_base)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (relQFibreAction D d p).hom γ =
      d.σZ.pullbackRelQSMul d.f d.over_base p γ := rfl

/-- **[T-3E-L2 core] THE AFFINE SECTION-ORBIT LEMMA**: for a finite group acting
on an affine scheme over an algebraically-closed-field point, two sections whose
invariant maps descend lie in one orbit. All section-algebra reasoning happens
at the abstract affine `Q`, so instances stay small. -/
theorem exists_smul_of_sections_of_affine {G : Type} [Group G] [Finite G]
    {Q : Scheme.{0}} [IsAffine Q] (σQ : AlgebraicGeometry.SchemeAction G Q)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (t : Q ⟶ Spec (CommRingCat.of Ω))
    (htinv : ∀ γ : G, σQ.hom γ ≫ t = t)
    (hdesc : ∀ {Y : Scheme.{0}} (F : Q ⟶ Y), (∀ γ : G, σQ.hom γ ≫ F = F) →
      ∃ q0 : Spec (CommRingCat.of Ω) ⟶ Y, t ≫ q0 = F)
    (s₁ s₂ : Spec (CommRingCat.of Ω) ⟶ Q)
    (hs₁ : s₁ ≫ t = 𝟙 _) (hs₂ : s₂ ≫ t = 𝟙 _) :
    ∃ γ : G, s₂ = s₁ ≫ σQ.hom γ := by
  classical
  have htop : σQ.IsStableOpen ⊤ := fun γ => by
    show (σQ.hom γ) ⁻¹ᵁ ⊤ = ⊤
    simp
  letI := σQ.gammaMulSemiringAction htop
  set ψ : CommRingCat.of Ω ⟶ Γ(Q, ⊤) :=
    Spec.preimage (Q.isoSpec.inv ≫ t) with hψdef
  have hψ : Spec.map ψ = Q.isoSpec.inv ≫ t := Spec.map_preimage _
  letI : Algebra Ω ↑Γ(Q, ⊤) := ψ.hom.toAlgebra
  have hAlg : algebraMap Ω ↑Γ(Q, ⊤) = ψ.hom := rfl
  have hofHom : ∀ γ : G,
      CommRingCat.ofHom (MulSemiringAction.toRingHom _ ↑Γ(Q, ⊤) γ) =
      (σQ.hom γ).appTop := by
    intro γ
    ext b
    show ((σQ.hom γ).appLE ⊤ ⊤ (htop γ).ge).hom b = ((σQ.hom γ).appTop).hom b
    simp [Scheme.Hom.appLE]
  have hbridge : ∀ γ : G,
      Q.isoSpec.hom ≫ AlgebraicGeometry.specSMul γ =
      σQ.hom γ ≫ Q.isoSpec.hom := by
    intro γ
    rw [AlgebraicGeometry.specSMul, hofHom]
    exact Scheme.isoSpec_hom_naturality (σQ.hom γ)
  have hψinv : ∀ (γ : G) (c : Ω), γ • (ψ.hom c) = ψ.hom c := by
    intro γ c
    have hmapeq : Spec.map (ψ ≫ (σQ.hom γ).appTop) = Spec.map ψ := by
      rw [Spec.map_comp, hψ,
        show Spec.map ((σQ.hom γ).appTop) =
          Q.isoSpec.inv ≫ σQ.hom γ ≫ Q.isoSpec.hom from by
          rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [htinv γ]
    have hcomp : ψ ≫ (σQ.hom γ).appTop = ψ := Spec.map_injective hmapeq
    have h := congrArg (fun (m : CommRingCat.of Ω ⟶ Γ(Q, ⊤)) => m.hom c) hcomp
    simpa [← hofHom] using h
  have hcommlaw : ∀ (γ : G) (c : Ω) (s : ↑Γ(Q, ⊤)),
      γ • (c • s) = c • (γ • s) := fun γ c s =>
    (congrArg (γ • ·) (Algebra.smul_def c s)).trans
      ((smul_mul' γ (ψ.hom c) s).trans
        ((congrArg (· * (γ • s)) (hψinv γ c)).trans
          (Algebra.smul_def c (γ • s)).symm))
  haveI : SMulCommClass G Ω ↑Γ(Q, ⊤) := ⟨hcommlaw⟩
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ : Γ(Q, ⊤) ⟶ CommRingCat.of Ω,
      Spec.map φ = s₁ ≫ Q.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ : Γ(Q, ⊤) ⟶ CommRingCat.of Ω,
      Spec.map φ = s₂ ≫ Q.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hcommutes : ∀ (ss : Spec (CommRingCat.of Ω) ⟶ Q)
      (_ : ss ≫ t = 𝟙 _)
      (φ : Γ(Q, ⊤) ⟶ CommRingCat.of Ω)
      (_ : Spec.map φ = ss ≫ Q.isoSpec.hom),
      ψ ≫ φ = 𝟙 (CommRingCat.of Ω) := by
    intro ss hss φ hφ
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Spec.map_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hss
  have hc₁ := hcommutes s₁ hs₁ φ₁ hφ₁
  have hc₂ := hcommutes s₂ hs₂ φ₂ hφ₂
  obtain ⟨q0, hq0⟩ := hdesc
    (Q.isoSpec.hom ≫ AlgebraicGeometry.invariantsπ G ↑Γ(Q, ⊤) ℤ)
    (fun γ => by
      rw [← Category.assoc, ← hbridge γ, Category.assoc,
        AlgebraicGeometry.specSMul_invariantsπ])
  have hFeq : s₁ ≫ (Q.isoSpec.hom ≫
      AlgebraicGeometry.invariantsπ G ↑Γ(Q, ⊤) ℤ) =
      s₂ ≫ (Q.isoSpec.hom ≫
        AlgebraicGeometry.invariantsπ G ↑Γ(Q, ⊤) ℤ) := by
    rw [← hq0, ← Category.assoc, hs₁, ← Category.assoc, hs₂]
  obtain ⟨γ₀, hγ₀⟩ := AlgebraicGeometry.exists_smul_algHom_eq
    (k := Ω) (B := ↑Γ(Q, ⊤))
    ⟨φ₁.hom, fun c => congrArg
      (fun (m : CommRingCat.of Ω ⟶ CommRingCat.of Ω) => m.hom c) hc₁⟩
    ⟨φ₂.hom, fun c => congrArg
      (fun (m : CommRingCat.of Ω ⟶ CommRingCat.of Ω) => m.hom c) hc₂⟩
    (by
      intro b hbfix
      have hmem : b ∈ FixedPoints.subalgebra ℤ ↑Γ(Q, ⊤) G := hbfix
      have hSpec : Spec.map (CommRingCat.ofHom
          (algebraMap (FixedPoints.subalgebra ℤ ↑Γ(Q, ⊤) G) ↑Γ(Q, ⊤)) ≫ φ₁) =
          Spec.map (CommRingCat.ofHom
          (algebraMap (FixedPoints.subalgebra ℤ ↑Γ(Q, ⊤) G) ↑Γ(Q, ⊤)) ≫ φ₂) := by
        rw [Spec.map_comp, Spec.map_comp, hφ₁, hφ₂]
        show _ ≫ AlgebraicGeometry.invariantsπ G ↑Γ(Q, ⊤) ℤ =
          _ ≫ AlgebraicGeometry.invariantsπ G ↑Γ(Q, ⊤) ℤ
        simpa only [Category.assoc] using hFeq
      have hh := Spec.map_injective hSpec
      exact congrArg (fun (m : CommRingCat.of
        (FixedPoints.subalgebra ℤ ↑Γ(Q, ⊤) G) ⟶
        CommRingCat.of Ω) => m.hom ⟨b, hmem⟩) hh)
  refine ⟨γ₀, ?_⟩
  have hφeq : φ₂ = CommRingCat.ofHom
      (MulSemiringAction.toRingHom _ ↑Γ(Q, ⊤) γ₀) ≫ φ₁ := by
    ext b
    exact hγ₀ b
  have hSpec2 : Spec.map φ₂ = Spec.map φ₁ ≫
      AlgebraicGeometry.specSMul (G := G) γ₀ := by
    rw [hφeq, Spec.map_comp]
    rfl
  rw [hφ₁, hφ₂] at hSpec2
  have hσ : s₂ ≫ Q.isoSpec.hom = (s₁ ≫ σQ.hom γ₀) ≫ Q.isoSpec.hom := by
    rw [hSpec2]
    simp only [Category.assoc]
    rw [← hbridge γ₀]
  exact (cancel_mono Q.isoSpec.hom).mp hσ

open scoped FintypeCatDiscrete in
/-- **[T-3E-L2] THE POINTWISE ORBIT LEMMA**: two field-valued points of the
framed total space over one quotient point differ by the group action. -/
theorem exists_smul_of_relQuotientπ_eq (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (z₁ z₂ : Spec (CommRingCat.of Ω) ⟶ d.Z)
    (hπ : z₁ ≫ d.σZ.relQuotientπ d.f d.over_base =
      z₂ ≫ d.σZ.relQuotientπ d.f d.over_base) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N),
      z₂ = z₁ ≫ d.σZ.hom γ := by
  classical
  set p := z₁ ≫ d.σZ.relQuotientπ d.f d.over_base with hpdef
  haveI hFinπ : IsFinite (d.σZ.relQuotientπ d.f d.over_base) :=
    d.σZ.isFinite_relQuotientπ_of_free d.f d.over_base
      (d.free_on_points (sympFramedAut_freeAction D))
  haveI : IsFinite (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) p) :=
    MorphismProperty.pullback_snd _ _ hFinπ
  haveI : IsAffineHom (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) p) :=
    inferInstance
  haveI : IsAffine (pullback (d.σZ.relQuotientπ d.f d.over_base) p) :=
    isAffine_of_isAffineHom
      (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) p)
  obtain ⟨γ, hγ⟩ := exists_smul_of_sections_of_affine
    (relQFibreAction D d p)
    (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) p)
    (fun γ => d.σZ.pullbackRelQSMul_snd d.f d.over_base p γ)
    (fun {Y} F hF => d.σZ.exists_relQuotientπ_lift_baseChange d.f d.over_base
      (d.free_on_points (sympFramedAut_freeAction D)) p F hF)
    (pullback.lift z₁ (𝟙 _) (by rw [Category.id_comp]))
    (pullback.lift z₂ (𝟙 _) (by rw [Category.id_comp]; exact hπ.symm))
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
  refine ⟨γ, ?_⟩
  have h2 := congrArg
    (· ≫ pullback.fst (d.σZ.relQuotientπ d.f d.over_base) p) hγ
  simp only [Category.assoc] at h2
  rw [pullback.lift_fst] at h2
  rw [show (relQFibreAction D d p).hom γ ≫
      pullback.fst (d.σZ.relQuotientπ d.f d.over_base) p =
      pullback.fst (d.σZ.relQuotientπ d.f d.over_base) p ≫ d.σZ.hom γ from
      d.σZ.pullbackRelQSMul_fst d.f d.over_base p γ] at h2
  rw [← Category.assoc, pullback.lift_fst] at h2
  exact h2

end PointLifting

section MutualInverses

open scoped FintypeCatDiscrete

variable (D : GaloisRepData N) [Fact (1 < N)]

/-- **[T-3E-1]** Pulling structures along a surjective flat quasi-compact cover
is injective: the coordinate leg is recovered by epi-cancellation through the
torsion base change. -/
theorem RhoLevelStructure.pull_injective {X' : EllObj (CommRingCat.of ℚ)}
    {T'' : Scheme.{0}} (c : T'' ⟶ X'.base)
    [Flat c] [Surjective c] [QuasiCompact c]
    (str₁ str₂ : RhoLevelStructure D X'.structMap X'.curve)
    (h : RhoLevelStructure.pull D (X'.pullbackAlongπ c) str₁ =
      RhoLevelStructure.pull D (X'.pullbackAlongπ c) str₂) :
    str₁ = str₂ := by
  have hpb := isPullback_torsionMapOfEllHom (X'.pullbackAlongπ c) N
  haveI hFl : Flat (torsionMapOfEllHom (X'.pullbackAlongπ c) N) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip
      (inferInstance : Flat c)
  haveI hSur : Surjective (torsionMapOfEllHom (X'.pullbackAlongπ c) N) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip
      (inferInstance : Surjective c)
  haveI hEpi : Epi (torsionMapOfEllHom (X'.pullbackAlongπ c) N) :=
    Flat.epi_of_flat_of_surjective _
  -- the pulled coordinate legs agree
  have hfst := congrArg (fun (β : RhoLevelStructure D
      (X'.pullbackAlong c).structMap (X'.pullbackAlong c).curve) =>
    β.torsionIso.hom ≫ pullback.fst (vRhoπ D)
      (X'.pullbackAlong c).structMap) h
  rw [show (RhoLevelStructure.pull D (X'.pullbackAlongπ c) str₁).torsionIso =
        pullTorsionIso D (X'.pullbackAlongπ c) str₁ from rfl,
      show (RhoLevelStructure.pull D (X'.pullbackAlongπ c) str₂).torsionIso =
        pullTorsionIso D (X'.pullbackAlongπ c) str₂ from rfl,
      pullTorsionIso_fst, pullTorsionIso_fst] at hfst
  have hcoord := (cancel_epi
    (torsionMapOfEllHom (X'.pullbackAlongπ c) N)).mp hfst
  -- assemble the iso equality
  refine RhoLevelStructure.ext_torsionIso (Iso.ext (pullback.hom_ext ?_ ?_))
  · exact hcoord
  · exact str₁.over_T.trans str₂.over_T.symm

/-- **[T-3E-1b]** Descent uniqueness: the descended structure is the unique one
pulling back to the given local structure. -/
theorem descend_eq_of_pull {X' : EllObj (CommRingCat.of ℚ)}
    {T'' : Scheme.{0}} {c : T'' ⟶ X'.base}
    [IsFinite c] [Etale c] [Flat c] [Surjective c] [QuasiCompact c]
    {α : RhoLevelStructure D (X'.pullbackAlong c).structMap
      (X'.pullbackAlong c).curve}
    (Hhom : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ (X'.pullbackAlong c).curve.torsion N),
      g₁ ≫ torsionMapOfEllHom (X'.pullbackAlongπ c) N =
        g₂ ≫ torsionMapOfEllHom (X'.pullbackAlongπ c) N →
      g₁ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X' c =
        g₂ ≫ α.torsionIso.hom ≫ vRhoCoverPrj D X' c)
    (Hinv : ∀ {Z : Scheme.{0}}
      (g₁ g₂ : Z ⟶ pullback (vRhoπ D) (X'.pullbackAlong c).structMap),
      g₁ ≫ vRhoCoverPrj D X' c = g₂ ≫ vRhoCoverPrj D X' c →
      g₁ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X'.pullbackAlongπ c) N =
        g₂ ≫ α.torsionIso.inv ≫ torsionMapOfEllHom (X'.pullbackAlongπ c) N)
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (hpull : RhoLevelStructure.pull D (X'.pullbackAlongπ c) str = α) :
    RhoLevelStructure.descend (α := α) Hhom Hinv = str := by
  refine RhoLevelStructure.pull_injective D c _ _ ?_
  rw [pull_descend, hpull]

open scoped FintypeCatDiscrete in
/-- **[T-3E-V] THE VALUE–STRUCTURE COMPATIBILITY (iso level)**: the pinned framed
trivialization reconstructed from the tautological value is exactly the pulled
trivialization of the structure. Componentwise over the constant scheme: both
sides read the `w`-slot as the frame evaluation (`framedPinned_leg_comb` on the
pinned side; the section additivity + the tautological reads on the pulled
side). -/
theorem strPinned_eq_pullTorsionIso {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (hinv : NIsInvertible (strCover D X') N) :
    framedTorsionIsoPinned D (X'.pullbackAlong (strPr D X')).structMap
        (X'.pullbackAlong (strPr D X')).curve hinv
        (strValue D str).val.1 (strValue D str).val.2.val
        (strValue D str).val.2.property =
      pullTorsionIso D (X'.pullbackAlongπ (strPr D X')) str := by
  refine Iso.ext ?_
  rw [← cancel_epi ((X'.pullbackAlong (strPr D X')).curve.fullLevelIso hinv
    (strValue D str).val.1).hom]
  refine Sigma.hom_ext _ _ fun w => ?_
  have hι : Sigma.ι (fun _ : (Fin 2 → ZMod N) =>
      (X'.pullbackAlong (strPr D X')).base) w ≫
      ((X'.pullbackAlong (strPr D X')).curve.fullLevelIso hinv
        (strValue D str).val.1).hom =
      (X'.pullbackAlong (strPr D X')).curve.pointToTorsion
        (((w 0).val : ℤ) • (strValue D str).val.1.1.1 +
          ((w 1).val : ℤ) • (strValue D str).val.1.1.2)
        (((X'.pullbackAlong (strPr D X')).curve.smul_eq_zero_iff_comp_mulByHom
          (𝟙 (strCover D X')) N _).mp (levelComb_kill (strValue D str).val.1 w)) := by
    exact Limits.Sigma.ι_desc _ _
  rw [← Category.assoc, ← Category.assoc, hι]
  refine pullback.hom_ext ?_ ?_
  · -- fst legs: both are the tautological slot evaluation
    rw [Category.assoc, Category.assoc]
    refine Eq.trans (framedPinned_leg_comb D
      (X'.pullbackAlong (strPr D X')).structMap hinv (strValue D str).val.1
      (strValue D str).val.2.val (strValue D str).val.2.property w) ?_
    -- now the pulled side
    rw [pullTorsionIso_fst]
    -- rewrite the combination as the tautological section
    have hcomb : ((w 0).val : ℤ) • (strValue D str).val.1.1.1 +
        ((w 1).val : ℤ) • (strValue D str).val.1.1.2 =
        EllipticCurve.Point.asSection X'.curve (strPr D X') (strPt D str w) :=
      (strSec_comb D str w).symm
    have hclassify : (X'.pullbackAlong (strPr D X')).curve.pointToTorsion
        (((w 0).val : ℤ) • (strValue D str).val.1.1.1 +
          ((w 1).val : ℤ) • (strValue D str).val.1.1.2)
        (((X'.pullbackAlong (strPr D X')).curve.smul_eq_zero_iff_comp_mulByHom
          (𝟙 (strCover D X')) N _).mp (levelComb_kill (strValue D str).val.1 w)) ≫
        torsionMapOfEllHom (X'.pullbackAlongπ (strPr D X')) N =
        strTor D str w := by
      rw [pointToTorsion_mapPoint (X'.pullbackAlongπ (strPr D X'))]
      rw [← strPt_pointToTorsion D str w]
      refine (pointToTorsion_comp (𝟙 (strCover D X')) (strPt D str w) _ ?_ _ _).trans
        (Category.id_comp _)
      -- carrier: the mapped combination is the tautological point
      show (EllHom.mapPoint (X'.pullbackAlongπ (strPr D X')) (𝟙 _) _).1 =
        𝟙 (strCover D X') ≫ (strPt D str w).1
      refine Eq.trans ?_ (Category.id_comp _).symm
      refine Eq.trans (EllHom.mapPoint_coe (X'.pullbackAlongπ (strPr D X'))
        (𝟙 _) _) ?_
      refine Eq.trans (congrArg (· ≫ (X'.pullbackAlongπ (strPr D X')).top)
        (congrArg Subtype.val hcomb)) ?_
      show (EllipticCurve.Point.asSection X'.curve (strPr D X')
          (strPt D str w)).1 ≫ pullback.fst X'.curve.π (strPr D X') =
        (strPt D str w).1
      exact EllipticCurve.Point.asSection_val_fst X'.curve (strPr D X')
        (strPt D str w)
    rw [← Category.assoc, hclassify]
    have h2 : strTor D str w ≫ str.torsionIso.hom = strVPt D X' w :=
      (Category.assoc _ _ _).trans
        ((congrArg (strVPt D X' w ≫ ·) str.torsionIso.inv_hom_id).trans
          (Category.comp_id _))
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact (strVPt_fst D X' w).symm.trans
      (congrArg (· ≫ pullback.fst (vRhoπ D) X'.structMap) h2.symm)
  · -- snd legs: both are the structure map to the cover
    rw [Category.assoc, Category.assoc, framedTorsionIsoPinned_π,
      pullTorsionIso_over, EllipticCurve.pointToTorsion_torsionπ]

open scoped FintypeCatDiscrete in
/-- **[T-3E-V structure level]** The dictionary applied to the tautological value
recovers the pulled structure. -/
theorem rhoLevelStructureOfCarve_strValue {X' : EllObj (CommRingCat.of ℚ)}
    (str : RhoLevelStructure D X'.structMap X'.curve)
    (hinv : NIsInvertible (strCover D X') N) :
    rhoLevelStructureOfCarve D (X'.pullbackAlong (strPr D X')).structMap
        (X'.pullbackAlong (strPr D X')).curve hinv
        (strValue D str).val.1 (strValue D str).val.2.val
        (strValue D str).val.2.property (strValue D str).property =
      RhoLevelStructure.pull D (X'.pullbackAlongπ (strPr D X')) str :=
  RhoLevelStructure.ext_torsionIso (strPinned_eq_pullTorsionIso D str hinv)

open scoped FintypeCatDiscrete in
/-- **[T-3E-REC]** The pinned trivialization determines the level: two full
levels pinning to the same iso through one frame are equal (read the basis
slots back through the iso). -/
theorem fullLevelPt_eq_of_pinned_eq {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L L' : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (heq : framedTorsionIsoPinned D sT E hinv L h hover =
      framedTorsionIsoPinned D sT E hinv L' h hover) : L = L' := by
  classical
  -- the basis combinations classify equally
  have hcombeq : ∀ v : Fin 2 → ZMod N,
      (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2) =
      (((v 0).val : ℤ) • L'.1.1 + ((v 1).val : ℤ) • L'.1.2) := by
    intro v
    have h1 := framedPinned_leg_comb D sT hinv L h hover v
    have h2 := framedPinned_leg_comb D sT hinv L' h hover v
    rw [heq] at h1
    have hfst : E.pointToTorsion _
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v)) ≫
        (framedTorsionIsoPinned D sT E hinv L' h hover).hom ≫
          pullback.fst (vRhoπ D) sT =
        E.pointToTorsion _
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
          (levelComb_kill L' v)) ≫
        (framedTorsionIsoPinned D sT E hinv L' h hover).hom ≫
          pullback.fst (vRhoπ D) sT :=
      h1.trans h2.symm
    have hsnd : E.pointToTorsion _
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v)) ≫
        (framedTorsionIsoPinned D sT E hinv L' h hover).hom ≫
          pullback.snd (vRhoπ D) sT =
        E.pointToTorsion _
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
          (levelComb_kill L' v)) ≫
        (framedTorsionIsoPinned D sT E hinv L' h hover).hom ≫
          pullback.snd (vRhoπ D) sT := by
      rw [framedTorsionIsoPinned_π, EllipticCurve.pointToTorsion_torsionπ,
        EllipticCurve.pointToTorsion_torsionπ]
    have hcls : E.pointToTorsion _
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v)) =
        E.pointToTorsion _
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
          (levelComb_kill L' v)) := by
      have hh : E.pointToTorsion _
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
            (levelComb_kill L v)) ≫
          (framedTorsionIsoPinned D sT E hinv L' h hover).hom =
          E.pointToTorsion _
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
            (levelComb_kill L' v)) ≫
          (framedTorsionIsoPinned D sT E hinv L' h hover).hom := by
        apply pullback.hom_ext
        · exact (Category.assoc _ _ _).trans
            (hfst.trans (Category.assoc _ _ _).symm)
        · exact (Category.assoc _ _ _).trans
            (hsnd.trans (Category.assoc _ _ _).symm)
      exact (cancel_mono
        (framedTorsionIsoPinned D sT E hinv L' h hover).hom).mp hh
    have hcar := congrArg (· ≫ E.torsionι N) hcls
    simp only [EllipticCurve.pointToTorsion_torsionι] at hcar
    exact Subtype.ext hcar
  -- read off the two basis points
  have hone : ((((Pi.single 0 1 : Fin 2 → ZMod N) 0).val : ℤ)) = 1 := by
    rw [Pi.single_eq_same, ZMod.val_one]
    exact Nat.cast_one
  have hzero01 : ((((Pi.single 0 1 : Fin 2 → ZMod N) 1).val : ℤ)) = 0 := by
    rw [show (Pi.single 0 1 : Fin 2 → ZMod N) 1 = 0 from
      Pi.single_eq_of_ne (by decide) 1, ZMod.val_zero]
    rfl
  have hzero10 : ((((Pi.single 1 1 : Fin 2 → ZMod N) 0).val : ℤ)) = 0 := by
    rw [show (Pi.single 1 1 : Fin 2 → ZMod N) 0 = 0 from
      Pi.single_eq_of_ne (by decide) 1, ZMod.val_zero]
    rfl
  have hone1 : ((((Pi.single 1 1 : Fin 2 → ZMod N) 1).val : ℤ)) = 1 := by
    rw [Pi.single_eq_same, ZMod.val_one]
    exact Nat.cast_one
  have hP : L.1.1 = L'.1.1 := by
    have hc := hcombeq (Pi.single 0 1)
    rwa [hone, hzero01, one_smul, zero_smul, add_zero, one_smul, zero_smul,
      add_zero] at hc
  have hQ : L.1.2 = L'.1.2 := by
    have hc := hcombeq (Pi.single 1 1)
    rwa [hone1, hzero10, one_smul, zero_smul, zero_add, one_smul, zero_smul,
      zero_add] at hc
  exact Subtype.ext (Prod.ext hP hQ)

open scoped FintypeCatDiscrete in
/-- **[T-3E-VC prep]** The pinned trivialization is congruent in the frame. -/
theorem framedTorsionIsoPinned_congr_frame {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    {h₁ h₂ : T ⟶ wFrames D} (hh : h₁ = h₂)
    (hover : h₁ ≫ wFramesπ D = sT) :
    framedTorsionIsoPinned D sT E hinv L h₁ hover =
      framedTorsionIsoPinned D sT E hinv L h₂ (hh ▸ hover) := by
  subst hh; rfl

open scoped FintypeCatDiscrete in
/-- **[T-3E-VC] THE VALUE COMPARISON**: two framed values with `γ`-related
frames and equal carve structures are `γ`-translates — the common structure
pins both levels through the common frame (T-EQ-2 + the recovery lemma). -/
theorem value_eq_smulNat_of_carve_eq {A : EllObj (CommRingCat.of ℚ)}
    (hinv : NIsInvertible A.base N)
    (v₁ v₂ : (sympFramedProblem D).obj (Opposite.op A))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hframe : v₂.val.2.val = v₁.val.2.val ≫ wFramesRightMul D γ)
    (hstr : rhoLevelStructureOfCarve D A.structMap A.curve hinv
        v₁.val.1 v₁.val.2.val v₁.val.2.property v₁.property =
      rhoLevelStructureOfCarve D A.structMap A.curve hinv
        v₂.val.1 v₂.val.2.val v₂.val.2.property v₂.property) :
    v₂ = (sympFramedSmulNat D γ).app (Opposite.op A) v₁ := by
  classical
  -- the pinned isos agree
  have hiso := congrArg RhoLevelStructure.torsionIso hstr
  have hiso' : framedTorsionIsoPinned D A.structMap A.curve hinv
      v₁.val.1 v₁.val.2.val v₁.val.2.property =
      framedTorsionIsoPinned D A.structMap A.curve hinv
      v₂.val.1 v₂.val.2.val v₂.val.2.property := hiso
  -- translate the first through γ (T-EQ-2 iso level)
  have hgl := framedTorsionIsoPinned_glSmul D A.structMap A.curve hinv
    v₁.val.1 v₁.val.2.val v₁.val.2.property γ
  -- transport the frame equality
  have hovRm : (v₁.val.2.val ≫ wFramesRightMul D γ) ≫ wFramesπ D =
      A.structMap := by
    rw [Category.assoc, wFramesRightMul_π]
    exact v₁.val.2.property
  have hcongr : framedTorsionIsoPinned D A.structMap A.curve hinv
      v₂.val.1 v₂.val.2.val v₂.val.2.property =
      framedTorsionIsoPinned D A.structMap A.curve hinv
      v₂.val.1 (v₁.val.2.val ≫ wFramesRightMul D γ) hovRm :=
    framedTorsionIsoPinned_congr_frame D A.structMap A.curve hinv
      v₂.val.1 hframe v₂.val.2.property
  -- the recovered level identity
  have hlevel : (v₂.val.1 : A.curve.FullLevelPt N) =
      A.curve.glSmul γ (v₁.val.1 : A.curve.FullLevelPt N) :=
    fullLevelPt_eq_of_pinned_eq D A.structMap A.curve hinv _ _
      (v₁.val.2.val ≫ wFramesRightMul D γ) hovRm
      ((hcongr.symm.trans hiso'.symm).trans hgl.symm)
  -- assemble
  refine Subtype.ext (Prod.ext ?_ (Subtype.ext ?_))
  · exact hlevel
  · show v₂.val.2.val = v₁.val.2.val ≫ wFramesRightMul D γ
    exact hframe

open scoped FintypeCatDiscrete in
/-- **[T-3E-N]** Naturality of the carve dictionary: the structure carved from a
mapped value is the pull of the carved structure. -/
theorem rhoLevelStructureOfCarve_map {A B : EllObj (CommRingCat.of ℚ)}
    (g : A ⟶ B) (hinvA : NIsInvertible A.base N)
    (hinvB : NIsInvertible B.base N)
    (v : (sympFramedProblem D).obj (Opposite.op B)) :
    rhoLevelStructureOfCarve D A.structMap A.curve hinvA
        ((sympFramedProblem D).map g.op v).val.1
        ((sympFramedProblem D).map g.op v).val.2.val
        ((sympFramedProblem D).map g.op v).val.2.property
        ((sympFramedProblem D).map g.op v).property =
      RhoLevelStructure.pull D g
        (rhoLevelStructureOfCarve D B.structMap B.curve hinvB
          v.val.1 v.val.2.val v.val.2.property v.property) := by
  refine RhoLevelStructure.ext_torsionIso (Iso.ext (pullback.hom_ext ?_ ?_))
  · refine Eq.trans ?_ (pullTorsionIso_fst D g _).symm
    exact (framedCoordMap_mapAlong D g hinvA hinvB v.val.1 _ rfl rfl
      v.val.2.val v.val.2.property).symm
  · exact (framedTorsionIsoPinned_π D A.structMap A.curve hinvA _ _ _).trans
      (pullTorsionIso_over D g _).symm

open scoped FintypeCatDiscrete in
/-- **[T-3E-A core]** The pointwise translation relation: at a field point, the
classified lift of the descended structure and the section lift differ by the
group action (both carve to the same pulled structure). -/
theorem rhoOfSection_zrel
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (s : T' ⟶ d.σZ.relQuotient d.f d.over_base)
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ T')
    (ξt : Spec (CommRingCat.of Ω) ⟶ strCover D (X.pullbackAlong k))
    (hξt : ξt ≫ strPr D (X.pullbackAlong k) = ξ)
    (ζ : Spec (CommRingCat.of Ω) ⟶
      pullback (d.σZ.relQuotientπ d.f d.over_base) s)
    (hζ : ζ ≫ pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s = ξ) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N),
      ζ ≫ secLift D d s =
        (ξt ≫ (strZ D d k (rhoOfSection D d k s hs hinv)).1) ≫
          d.σZ.hom γ := by
  classical
  set str' := rhoOfSection D d k s hs hinv with hstr'
  set z₁ := ξt ≫ (strZ D d k str').1 with hz₁
  set z₂ := ζ ≫ secLift D d s with hz₂
  -- the comparison maps into the two pulled presentations
  have hh₁ : ξt ≫ (strPr D (X.pullbackAlong k) ≫ k) =
      (X.pullbackAlongπ (ξ ≫ k)).baseHom := by
    show ξt ≫ strPr D (X.pullbackAlong k) ≫ k = ξ ≫ k
    rw [← Category.assoc, hξt]
    exact rfl
  set w₁ := EllObj.homToPullbackAlong (X.pullbackAlongπ (ξ ≫ k)) ξt hh₁ with hw₁
  have hh₂ : ζ ≫ secCover D d s = (X.pullbackAlongMap k ξ).baseHom := hζ
  set w₂ := EllObj.homToPullbackAlong (X.pullbackAlongMap k ξ) ζ hh₂ with hw₂
  set u₁ := EllObj.toPullbackAlong
    (X.pullbackAlongMap k (strPr D (X.pullbackAlong k))) with hu₁
  -- the transported values
  set v₁ := (sympFramedProblem D).map (w₁ ≫ u₁).op (strValue D str') with hv₁
  set v₂ := (sympFramedProblem D).map w₂.op (secW D d k s hs) with hv₂
  -- value identifications
  have hVAL : d.eqv (strPr D (X.pullbackAlong k) ≫ k) (strZ D d k str') =
      (sympFramedProblem D).map u₁.op (strValue D str') :=
    (d.eqv (strPr D (X.pullbackAlong k) ≫ k)).apply_symm_apply _
  have pf₁ : z₁ ≫ d.f = ξ ≫ k := by
    rw [hz₁, Category.assoc, (strZ D d k str').2, ← Category.assoc, hξt]
    exact rfl
  have heqv₁ : d.eqv (ξ ≫ k) ⟨z₁, pf₁⟩ =
      v₁ := by
    have hnat := rhoMap_eqv d.toRelRepData w₁ ξt rfl
      (by show ξt ≫ strPr D (X.pullbackAlong k) ≫ k = ξ ≫ k
          rw [← Category.assoc, hξt]
          exact rfl)
      (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)
      (strZ D d k str')
    rw [hVAL] at hnat
    exact hnat.symm.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      u₁.op w₁.op (strValue D str')).symm
  have pf₂ : z₂ ≫ d.f = ξ ≫ k := by
    rw [hz₂, Category.assoc, secLift_f D d k s hs, ← Category.assoc]
    exact congrArg (· ≫ k) hζ
  have heqv₂ : d.eqv (ξ ≫ k) ⟨z₂, pf₂⟩ = v₂ := by
    have hnat := rhoMap_eqv d.toRelRepData
      (w₂ ≫ pullbackAlongAssocHom X k (secCover D d s)) ζ
      (Category.comp_id ζ)
      (by rw [← Category.assoc]; exact congrArg (· ≫ k) hζ)
      (by rw [Category.assoc, pullbackAlongAssocHom_π, ← Category.assoc,
        EllObj.homToPullbackAlong_pullbackAlongπ,
        ModuliProblem.pullbackAlongMap_pullbackAlongπ])
      ⟨secLift D d s, secLift_f D d k s hs⟩
    exact hnat.symm.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      (pullbackAlongAssocHom X k (secCover D d s)).op w₂.op
      (secValue D d k s hs))
  -- invertibility of N on the relevant bases
  have hinvSpec : NIsInvertible (Spec (CommRingCat.of ℚ)) N := by
    have hq : IsUnit ((N : ℚ)) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
    rwa [map_natCast] at this
  have hinvΩob : NIsInvertible (X.pullbackAlong (ξ ≫ k)).base N :=
    NIsInvertible.of_hom ((ξ ≫ k) ≫ X.structMap) hinvSpec
  have hinvCover : NIsInvertible (strCover D (X.pullbackAlong k)) N :=
    NIsInvertible.of_hom
      (strPr D (X.pullbackAlong k) ≫ (X.pullbackAlong k).structMap) hinvSpec
  -- the two carve structures agree (both are the ξ-pull of str')
  have hMAPEQ : (w₁ ≫ u₁) ≫
      (X.pullbackAlong k).pullbackAlongπ (strPr D (X.pullbackAlong k)) =
      w₂ ≫ (X.pullbackAlong k).pullbackAlongπ (secCover D d s) := by
    apply (EllObj.homPullbackAlongEquiv X k (X.pullbackAlong (ξ ≫ k))).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show ((w₁ ≫ u₁) ≫
          (X.pullbackAlong k).pullbackAlongπ (strPr D (X.pullbackAlong k))) ≫
          X.pullbackAlongπ k =
        (w₂ ≫ (X.pullbackAlong k).pullbackAlongπ (secCover D d s)) ≫
          X.pullbackAlongπ k
      rw [Category.assoc w₁ u₁]
      refine Eq.trans (congrArg (· ≫ X.pullbackAlongπ k)
        (congrArg (w₁ ≫ ·) (EllObj.toPullbackAlong_pullbackAlongπ
          (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (w₁ ≫ ·)
        (ModuliProblem.pullbackAlongMap_pullbackAlongπ X k
          (strPr D (X.pullbackAlong k)))) ?_
      refine Eq.trans (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _) ?_
      refine Eq.symm ?_
      refine Eq.trans (congrArg (· ≫ X.pullbackAlongπ k)
        (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)) ?_
      exact ModuliProblem.pullbackAlongMap_pullbackAlongπ X k ξ
    · show (ξt ≫ 𝟙 _) ≫ strPr D (X.pullbackAlong k) = ζ ≫ secCover D d s
      rw [Category.comp_id, hξt]
      exact hζ.symm
  have hN₁ := rhoLevelStructureOfCarve_map D (w₁ ≫ u₁) hinvΩob hinvCover
    (strValue D str')
  have hV := rhoLevelStructureOfCarve_strValue D str' hinvCover
  have hN₂ := rhoLevelStructureOfCarve_map D w₂ hinvΩob hinv
    (secW D d k s hs)
  -- str' pulls back to the section structure along its own cover
  haveI hFinsc : IsFinite (secCover D d s) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.isFinite_relQuotientπ_of_free d.f d.over_base
        (d.free_on_points (sympFramedAut_freeAction D)))
  haveI hEtsc : Etale (secCover D d s) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.etale_relQuotientπ_of_free d.f d.over_base
        (d.free_on_points (sympFramedAut_freeAction D)))
  haveI hFlsc : Flat (secCover D d s) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.flat_relQuotientπ_of_free d.f d.over_base
        (d.free_on_points (sympFramedAut_freeAction D)))
  haveI hSusc : Surjective (secCover D d s) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.surjective_relQuotientπ_of_free d.f d.over_base)
  haveI hQCsc : QuasiCompact (secCover D d s) := by
    haveI : IsAffineHom (secCover D d s) := inferInstance
    infer_instance
  have hPD : RhoLevelStructure.pull D
      ((X.pullbackAlong k).pullbackAlongπ (secCover D d s)) str' =
      secStruct D d k s hs hinv := by
    rw [hstr', rhoOfSection_eq_descend D d k s hs hinv]
    exact @pull_descend N ‹_› D (X.pullbackAlong k) _ (secCover D d s)
      ‹_› ‹_› ‹_› (secStruct D d k s hs hinv) ‹_› ‹_›
      (secHhom D d k s hs hinv) (secHinv D d k s hs hinv)
  have hcarve : rhoLevelStructureOfCarve D
      (X.pullbackAlong (ξ ≫ k)).structMap (X.pullbackAlong (ξ ≫ k)).curve
      hinvΩob v₁.val.1 v₁.val.2.val v₁.val.2.property v₁.property =
      rhoLevelStructureOfCarve D
      (X.pullbackAlong (ξ ≫ k)).structMap (X.pullbackAlong (ξ ≫ k)).curve
      hinvΩob v₂.val.1 v₂.val.2.val v₂.val.2.property v₂.property := by
    refine hN₁.trans (Eq.trans ?_ hN₂.symm)
    refine Eq.trans (congrArg (RhoLevelStructure.pull D (w₁ ≫ u₁)) hV) ?_
    refine Eq.trans (RhoLevelStructure.pull_comp D _ _ _).symm ?_
    refine Eq.trans
      (congrArg (fun m => RhoLevelStructure.pull D m str') hMAPEQ) ?_
    refine Eq.trans (RhoLevelStructure.pull_comp D _ _ _) ?_
    exact congrArg (RhoLevelStructure.pull D w₂) hPD
  -- the frames differ by a translation; conclude by the value comparison
  obtain ⟨γ, hγ⟩ := exists_frameGraph_rel D v₁.val.2.val v₂.val.2.val
    (v₁.val.2.property.trans v₂.val.2.property.symm)
  have hvc := value_eq_smulNat_of_carve_eq D hinvΩob v₁ v₂ γ hγ hcarve
  have hφ : ((sympFramedAut D) γ⁻¹).hom = sympFramedSmulNat D γ := by
    rw [show ((sympFramedAut D) γ⁻¹).hom =
      sympFramedSmulNat D ((γ⁻¹)⁻¹) from rfl, inv_inv]
  have hequi := d.equivariant (ξ ≫ k) ⟨z₁, pf₁⟩ γ
  rw [hφ, heqv₁] at hequi
  have hfinal := heqv₂.trans (hvc.trans hequi.symm)
  have hz := congrArg Subtype.val ((d.eqv (ξ ≫ k)).injective hfinal)
  exact ⟨γ, hz⟩

open scoped FintypeCatDiscrete in
/-- **[T-3E-A] ROUNDTRIP A**: descending the structure of a section recovers the
section (clopen-agreement engine + the pointwise translation relation). -/
theorem strSection_rhoOfSection
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (s : T' ⟶ d.σZ.relQuotient d.f d.over_base)
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = k)
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N) :
    strSection D d k (rhoOfSection D d k s hs hinv) = s := by
  classical
  set str' := rhoOfSection D d k s hs hinv with hstr'
  have hfe := d.σZ.relQuotientStruct_finite_etale_of_free d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D)) d.finite d.etale
  haveI hFin : IsFinite (d.σZ.relQuotientStruct d.f d.over_base) := hfe.1
  haveI hEt : Etale (d.σZ.relQuotientStruct d.f d.over_base) := hfe.2
  haveI hSep : IsSeparated (d.σZ.relQuotientStruct d.f d.over_base) :=
    inferInstance
  refine eq_of_forall_geomPt_agree (d.σZ.relQuotientStruct d.f d.over_base) _ _
    ((strSection_struct D d k str').trans hs.symm) ?_
  intro ω
  haveI hFinPr : IsFinite (strPr D (X.pullbackAlong k)) :=
    MorphismProperty.pullback_fst _ _ (wFramesπ_finite_etale D).1
  obtain ⟨ξt, hξt⟩ := exists_specPoint_lift_of_finite_surjective
    (strPr D (X.pullbackAlong k)) (geomPt T' ω)
  haveI hFinπ : IsFinite (d.σZ.relQuotientπ d.f d.over_base) :=
    d.σZ.isFinite_relQuotientπ_of_free d.f d.over_base
      (d.free_on_points (sympFramedAut_freeAction D))
  haveI hSurπ : Surjective (d.σZ.relQuotientπ d.f d.over_base) :=
    d.σZ.surjective_relQuotientπ_of_free d.f d.over_base
  haveI : IsFinite (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) :=
    MorphismProperty.pullback_snd _ _ hFinπ
  haveI : Surjective (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) :=
    MorphismProperty.pullback_snd _ _ hSurπ
  obtain ⟨ζ, hζ⟩ := exists_specPoint_lift_of_finite_surjective
    (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) s) (geomPt T' ω)
  obtain ⟨γ, hz⟩ := rhoOfSection_zrel D d k s hs hinv (geomPt T' ω) ξt hξt ζ hζ
  calc geomPt T' ω ≫ strSection D d k str'
      = (ξt ≫ strPr D (X.pullbackAlong k)) ≫ strSection D d k str' := by
        rw [hξt]
        exact rfl
    _ = ξt ≫ strSigmaP D d k str' := by
        rw [Category.assoc, strPr_strSection]
    _ = (ξt ≫ (strZ D d k str').1) ≫ d.σZ.relQuotientπ d.f d.over_base := by
        rw [strSigmaP, Category.assoc]
    _ = ((ξt ≫ (strZ D d k str').1) ≫ d.σZ.hom γ) ≫
          d.σZ.relQuotientπ d.f d.over_base :=
        ((Category.assoc _ _ _).trans (congrArg ((ξt ≫ (strZ D d k str').1) ≫ ·)
          (d.σZ.hom_comp_relQuotientπ d.f d.over_base γ))).symm
    _ = (ζ ≫ secLift D d s) ≫ d.σZ.relQuotientπ d.f d.over_base := by
        rw [← hz]
    _ = ζ ≫ secCover D d s ≫ s := by
        rw [Category.assoc]
        exact congrArg (ζ ≫ ·) pullback.condition
    _ = geomPt T' ω ≫ s := by
        rw [← Category.assoc, show ζ ≫ secCover D d s = geomPt T' ω from hζ]

open scoped FintypeCatDiscrete in
/-- **[T-3E-VCinv]** The carve structure is invariant under the diagonal
translation of values (T-EQ-2 at the value level). -/
theorem rhoLevelStructureOfCarve_smulNat {A : EllObj (CommRingCat.of ℚ)}
    (hinvA : NIsInvertible A.base N)
    (v : (sympFramedProblem D).obj (Opposite.op A))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    rhoLevelStructureOfCarve D A.structMap A.curve hinvA
        ((sympFramedSmulNat D γ).app (Opposite.op A) v).val.1
        ((sympFramedSmulNat D γ).app (Opposite.op A) v).val.2.val
        ((sympFramedSmulNat D γ).app (Opposite.op A) v).val.2.property
        ((sympFramedSmulNat D γ).app (Opposite.op A) v).property =
      rhoLevelStructureOfCarve D A.structMap A.curve hinvA
        v.val.1 v.val.2.val v.val.2.property v.property :=
  RhoLevelStructure.ext_torsionIso
    (framedTorsionIsoPinned_glSmul D A.structMap A.curve hinvA
      v.val.1 v.val.2.val v.val.2.property γ)

open scoped FintypeCatDiscrete in
/-- **[T-3E-B core]** The pointwise section-cover comparison: at every field
point of the section cover of `strSection str`, the section structure and the
pulled structure agree (both classified lifts lie in one orbit by the pointwise
orbit lemma, and the carve is orbit-invariant). -/
theorem strSection_pull_pointwise
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve)
    (hinv₀ : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base)
      (strSection D d k str)) N)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (ζ₀ : Spec (CommRingCat.of Ω) ⟶
      pullback (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str))
    (ξt : Spec (CommRingCat.of Ω) ⟶ strCover D (X.pullbackAlong k))
    (hξt : ξt ≫ strPr D (X.pullbackAlong k) =
      ζ₀ ≫ pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
        (strSection D d k str)) :
    RhoLevelStructure.pull D
      (EllObj.homToPullbackAlong
        (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str))) ζ₀ rfl)
      (secStruct D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀) =
    RhoLevelStructure.pull D
      (EllObj.homToPullbackAlong
        (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str))) ζ₀ rfl)
      (RhoLevelStructure.pull D
        ((X.pullbackAlong k).pullbackAlongπ
          (secCover D d (strSection D d k str))) str) := by
  classical
  -- the two lifts lie over one quotient point
  have hπeq : (ξt ≫ (strZ D d k str).1) ≫
      d.σZ.relQuotientπ d.f d.over_base =
      (ζ₀ ≫ secLift D d (strSection D d k str)) ≫
      d.σZ.relQuotientπ d.f d.over_base := by
    rw [Category.assoc, Category.assoc]
    calc ξt ≫ (strZ D d k str).1 ≫ d.σZ.relQuotientπ d.f d.over_base
        = ξt ≫ strSigmaP D d k str := by rw [strSigmaP]
      _ = ξt ≫ strPr D (X.pullbackAlong k) ≫ strSection D d k str := by
          rw [← strPr_strSection D d k str]
      _ = (ξt ≫ strPr D (X.pullbackAlong k)) ≫ strSection D d k str :=
          (Category.assoc _ _ _).symm
      _ = (ζ₀ ≫ pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
            (strSection D d k str)) ≫ strSection D d k str := by rw [hξt]
      _ = ζ₀ ≫ secLift D d (strSection D d k str) ≫
            d.σZ.relQuotientπ d.f d.over_base := by
          rw [Category.assoc]
          exact (congrArg (ζ₀ ≫ ·) pullback.condition).symm
  obtain ⟨γ, hzz⟩ := exists_smul_of_relQuotientπ_eq D d
    (ξt ≫ (strZ D d k str).1) (ζ₀ ≫ secLift D d (strSection D d k str)) hπeq
  -- transports (as in the A-core)
  have hh₁ : ξt ≫ (strPr D (X.pullbackAlong k) ≫ k) =
      (X.pullbackAlongπ ((ζ₀ ≫ pullback.snd
        (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫
        k)).baseHom := by
    show ξt ≫ strPr D (X.pullbackAlong k) ≫ k = _ ≫ k
    rw [← Category.assoc, hξt]
    exact rfl
  have hVAL : d.eqv (strPr D (X.pullbackAlong k) ≫ k) (strZ D d k str) =
      (sympFramedProblem D).map (EllObj.toPullbackAlong
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))).op
        (strValue D str) :=
    (d.eqv (strPr D (X.pullbackAlong k) ≫ k)).apply_symm_apply _
  have pf₁ : (ξt ≫ (strZ D d k str).1) ≫ d.f =
      (ζ₀ ≫ pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
        (strSection D d k str)) ≫ k := by
    rw [Category.assoc, (strZ D d k str).2, ← Category.assoc, hξt]
  have heqv₁ : d.eqv ((ζ₀ ≫ pullback.snd
      (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k)
      ⟨ξt ≫ (strZ D d k str).1, pf₁⟩ =
      (sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ ((ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k))
          ξt hh₁) ≫ EllObj.toPullbackAlong
          (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))).op
        (strValue D str) := by
    have hnat := rhoMap_eqv d.toRelRepData
      (EllObj.homToPullbackAlong (X.pullbackAlongπ ((ζ₀ ≫ pullback.snd
        (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k))
        ξt hh₁) ξt rfl
      (by show ξt ≫ strPr D (X.pullbackAlong k) ≫ k = _ ≫ k
          rw [← Category.assoc, hξt]
          exact rfl)
      (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)
      (strZ D d k str)
    rw [hVAL] at hnat
    exact hnat.symm.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      (EllObj.toPullbackAlong
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))).op
      (EllObj.homToPullbackAlong (X.pullbackAlongπ ((ζ₀ ≫ pullback.snd
        (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k))
        ξt hh₁).op
      (strValue D str)).symm
  have pf₂ : (ζ₀ ≫ secLift D d (strSection D d k str)) ≫ d.f =
      (ζ₀ ≫ pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
        (strSection D d k str)) ≫ k := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (ζ₀ ≫ ·)
      (secLift_f D d k (strSection D d k str)
        (strSection_struct D d k str))) ?_
    exact (Category.assoc _ _ _).symm
  have heqv₂ : d.eqv ((ζ₀ ≫ pullback.snd
      (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k)
      ⟨ζ₀ ≫ secLift D d (strSection D d k str), pf₂⟩ =
      (sympFramedProblem D).map
        (EllObj.homToPullbackAlong
          (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
            (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)))
          ζ₀ rfl).op
        (secW D d k (strSection D d k str) (strSection_struct D d k str)) := by
    have hnat := rhoMap_eqv d.toRelRepData
      ((EllObj.homToPullbackAlong
        (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)))
        ζ₀ rfl) ≫
        pullbackAlongAssocHom X k (secCover D d (strSection D d k str))) ζ₀
      (Category.comp_id ζ₀)
      (by rw [← Category.assoc]; exact rfl)
      ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (pullbackAlongAssocHom_π X k
          (secCover D d (strSection D d k str)))).trans
        ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ X.pullbackAlongπ k)
          (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)).trans
        (ModuliProblem.pullbackAlongMap_pullbackAlongπ X k _)))))
      ⟨secLift D d (strSection D d k str),
        secLift_f D d k (strSection D d k str) (strSection_struct D d k str)⟩
    exact hnat.symm.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      (pullbackAlongAssocHom X k (secCover D d (strSection D d k str))).op
      (EllObj.homToPullbackAlong
        (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)))
        ζ₀ rfl).op
      (secValue D d k (strSection D d k str) (strSection_struct D d k str)))
  -- the value translation
  have hφ : ((sympFramedAut D) γ⁻¹).hom = sympFramedSmulNat D γ := by
    rw [show ((sympFramedAut D) γ⁻¹).hom =
      sympFramedSmulNat D ((γ⁻¹)⁻¹) from rfl, inv_inv]
  have hequi := d.equivariant ((ζ₀ ≫ pullback.snd
    (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k)
    ⟨ξt ≫ (strZ D d k str).1, pf₁⟩ γ
  have hequi' := hequi.trans
    ((congrArg (fun (F : sympFramedProblem D ⟶ sympFramedProblem D) =>
      F.app (Opposite.op (X.pullbackAlong ((ζ₀ ≫ pullback.snd
        (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k)))
      (d.eqv _ ⟨ξt ≫ (strZ D d k str).1, pf₁⟩)) hφ).trans
    (congrArg ((sympFramedSmulNat D γ).app _) heqv₁))
  have hveq : (sympFramedProblem D).map
      (EllObj.homToPullbackAlong
        (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)))
        ζ₀ rfl).op
      (secW D d k (strSection D d k str) (strSection_struct D d k str)) =
      (sympFramedSmulNat D γ).app _
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ ((ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k))
          ξt hh₁) ≫ EllObj.toPullbackAlong
          (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))).op
        (strValue D str)) := by
    refine heqv₂.symm.trans (Eq.trans ?_ hequi')
    exact congrArg (d.eqv _) (Subtype.ext hzz)
  -- invertibility on the point
  have hinvSpec : NIsInvertible (Spec (CommRingCat.of ℚ)) N := by
    have hq : IsUnit ((N : ℚ)) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
    rwa [map_natCast] at this
  have hinvΩob : NIsInvertible (X.pullbackAlong ((ζ₀ ≫ pullback.snd
      (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k)).base
      N :=
    NIsInvertible.of_hom (((ζ₀ ≫ pullback.snd
      (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k) ≫
      X.structMap) hinvSpec
  have hinvCover : NIsInvertible (strCover D (X.pullbackAlong k)) N :=
    NIsInvertible.of_hom
      (strPr D (X.pullbackAlong k) ≫ (X.pullbackAlong k).structMap) hinvSpec
  -- carve chains
  have hN₁ := rhoLevelStructureOfCarve_map D
    ((EllObj.homToPullbackAlong (X.pullbackAlongπ ((ζ₀ ≫ pullback.snd
      (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k))
      ξt hh₁) ≫ EllObj.toPullbackAlong
      (X.pullbackAlongMap k (strPr D (X.pullbackAlong k))))
    hinvΩob hinvCover (strValue D str)
  have hV := rhoLevelStructureOfCarve_strValue D str hinvCover
  have hN₂ := rhoLevelStructureOfCarve_map D
    (EllObj.homToPullbackAlong
      (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
        (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str))) ζ₀ rfl)
    hinvΩob hinv₀
    (secW D d k (strSection D d k str) (strSection_struct D d k str))
  have hMAPEQ : ((EllObj.homToPullbackAlong (X.pullbackAlongπ ((ζ₀ ≫
      pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
        (strSection D d k str)) ≫ k)) ξt hh₁) ≫
      EllObj.toPullbackAlong
        (X.pullbackAlongMap k (strPr D (X.pullbackAlong k)))) ≫
      (X.pullbackAlong k).pullbackAlongπ (strPr D (X.pullbackAlong k)) =
      (EllObj.homToPullbackAlong
        (X.pullbackAlongMap k (ζ₀ ≫ pullback.snd
          (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)))
        ζ₀ rfl) ≫
      (X.pullbackAlong k).pullbackAlongπ
        (secCover D d (strSection D d k str)) := by
    apply (EllObj.homPullbackAlongEquiv X k _).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (_ ≫ (X.pullbackAlong k).pullbackAlongπ
          (strPr D (X.pullbackAlong k))) ≫ X.pullbackAlongπ k =
        (_ ≫ (X.pullbackAlong k).pullbackAlongπ
          (secCover D d (strSection D d k str))) ≫ X.pullbackAlongπ k
      refine Eq.trans (congrArg (· ≫ X.pullbackAlongπ k)
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (EllObj.toPullbackAlong_pullbackAlongπ
            (X.pullbackAlongMap k (strPr D (X.pullbackAlong k))))))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (_ ≫ ·)
        (ModuliProblem.pullbackAlongMap_pullbackAlongπ X k
          (strPr D (X.pullbackAlong k)))) ?_
      refine Eq.trans (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _) ?_
      refine Eq.symm ?_
      refine Eq.trans (congrArg (· ≫ X.pullbackAlongπ k)
        (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)) ?_
      exact ModuliProblem.pullbackAlongMap_pullbackAlongπ X k _
    · show (ξt ≫ 𝟙 _) ≫ strPr D (X.pullbackAlong k) =
        ζ₀ ≫ secCover D d (strSection D d k str)
      rw [Category.comp_id, hξt]
      exact rfl
  -- assemble
  refine Eq.trans hN₂.symm ?_
  refine Eq.trans (congrArg (fun (w : (sympFramedProblem D).obj
      (Opposite.op (X.pullbackAlong ((ζ₀ ≫ pullback.snd
        (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str)) ≫ k)))) =>
    rhoLevelStructureOfCarve D _ _ hinvΩob
      w.val.1 w.val.2.val w.val.2.property w.property) hveq) ?_
  refine Eq.trans (rhoLevelStructureOfCarve_smulNat D hinvΩob _ γ) ?_
  refine Eq.trans hN₁ ?_
  refine Eq.trans (congrArg (RhoLevelStructure.pull D _) hV) ?_
  refine Eq.trans (RhoLevelStructure.pull_comp D _ _ _).symm ?_
  refine Eq.trans
    (congrArg (fun m => RhoLevelStructure.pull D m str) hMAPEQ) ?_
  exact RhoLevelStructure.pull_comp D _ _ _

open scoped FintypeCatDiscrete in
/-- **[T-3E-B fst-pointwise]** The coordinate legs of the pulled structure and
the section structure agree at every field-valued torsion point. -/
theorem strSection_pull_fst_pointwise
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve)
    (hinv₀ : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base)
      (strSection D d k str)) N)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (ζ₀ : Spec (CommRingCat.of Ω) ⟶
      pullback (d.σZ.relQuotientπ d.f d.over_base) (strSection D d k str))
    (ξt : Spec (CommRingCat.of Ω) ⟶ strCover D (X.pullbackAlong k))
    (hξt : ξt ≫ strPr D (X.pullbackAlong k) =
      ζ₀ ≫ pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
        (strSection D d k str))
    (ξv : Spec (CommRingCat.of Ω) ⟶
      ((X.pullbackAlong k).pullbackAlong
        (secCover D d (strSection D d k str))).curve.torsion N)
    (hξv : ξv ≫ ((X.pullbackAlong k).pullbackAlong
      (secCover D d (strSection D d k str))).curve.torsionπ N = ζ₀) :
    ξv ≫ ((RhoLevelStructure.pull D
      ((X.pullbackAlong k).pullbackAlongπ
        (secCover D d (strSection D d k str))) str).torsionIso.hom ≫
      pullback.fst (vRhoπ D) _) =
    ξv ≫ ((secStruct D d k (strSection D d k str)
      (strSection_struct D d k str) hinv₀).torsionIso.hom ≫
      pullback.fst (vRhoπ D) _) := by
  classical
  have hBP := strSection_pull_pointwise D d k str hinv₀ ζ₀ ξt hξt
  -- lift the torsion point along the point base change
  have hpb := isPullback_torsionMapOfEllHom
    (EllObj.homToPullbackAlong
      (X.pullbackAlongMap k ((ζ₀) ≫
        pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
          (strSection D d k str)))
      (ζ₀) rfl) N
  have hcone : ξv ≫ ((X.pullbackAlong k).pullbackAlong
      (secCover D d (strSection D d k str))).curve.torsionπ N =
      𝟙 _ ≫ ζ₀ := by
    rw [Category.id_comp]
    exact hξv
  -- the lifted torsion point
  have hfac := hpb.lift_fst (ξv) (𝟙 _) hcone
  -- read both structures through the lift
  have h₁ := pullTorsionIso_fst D
    (EllObj.homToPullbackAlong
      (X.pullbackAlongMap k ((ζ₀) ≫
        pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
          (strSection D d k str)))
      (ζ₀) rfl)
    (RhoLevelStructure.pull D
      ((X.pullbackAlong k).pullbackAlongπ
        (secCover D d (strSection D d k str))) str)
  have h₂ := pullTorsionIso_fst D
    (EllObj.homToPullbackAlong
      (X.pullbackAlongMap k ((ζ₀) ≫
        pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
          (strSection D d k str)))
      (ζ₀) rfl)
    (secStruct D d k (strSection D d k str)
      (strSection_struct D d k str) hinv₀)
  -- assemble: precompose with the lifted point and transport through hBP
  calc ξv ≫ ((RhoLevelStructure.pull D
        ((X.pullbackAlong k).pullbackAlongπ
          (secCover D d (strSection D d k str))) str).torsionIso.hom ≫
        pullback.fst (vRhoπ D) _)
      = (hpb.lift (ξv) (𝟙 _) hcone ≫
          torsionMapOfEllHom _ N) ≫
          ((RhoLevelStructure.pull D
            ((X.pullbackAlong k).pullbackAlongπ
              (secCover D d (strSection D d k str))) str).torsionIso.hom ≫
            pullback.fst (vRhoπ D) _) :=
        (congrArg (· ≫ ((RhoLevelStructure.pull D
          ((X.pullbackAlong k).pullbackAlongπ
            (secCover D d (strSection D d k str))) str).torsionIso.hom ≫
          pullback.fst (vRhoπ D) _)) hfac).symm
    _ = hpb.lift (ξv) (𝟙 _) hcone ≫
          ((RhoLevelStructure.pull D _ (RhoLevelStructure.pull D
            ((X.pullbackAlong k).pullbackAlongπ
              (secCover D d (strSection D d k str))) str)).torsionIso.hom ≫
            pullback.fst (vRhoπ D) _) :=
        (Category.assoc _ _ _).trans
          (congrArg (hpb.lift (ξv) (𝟙 _) hcone ≫ ·) h₁.symm)
    _ = hpb.lift (ξv) (𝟙 _) hcone ≫
          ((RhoLevelStructure.pull D _ (secStruct D d k
            (strSection D d k str) (strSection_struct D d k str)
            hinv₀)).torsionIso.hom ≫ pullback.fst (vRhoπ D) _) := by
        exact congrArg (fun (β : RhoLevelStructure D
            (X.pullbackAlong (((ζ₀) ≫ pullback.snd
              (d.σZ.relQuotientπ d.f d.over_base)
              (strSection D d k str)) ≫ k)).structMap
            (X.pullbackAlong (((ζ₀) ≫ pullback.snd
              (d.σZ.relQuotientπ d.f d.over_base)
              (strSection D d k str)) ≫ k)).curve) =>
          hpb.lift (ξv) (𝟙 _) hcone ≫
            (β.torsionIso.hom ≫ pullback.fst (vRhoπ D) _)) hBP.symm
    _ = (hpb.lift (ξv) (𝟙 _) hcone ≫
          torsionMapOfEllHom _ N) ≫
          ((secStruct D d k (strSection D d k str)
            (strSection_struct D d k str) hinv₀).torsionIso.hom ≫
            pullback.fst (vRhoπ D) _) :=
        (congrArg (hpb.lift (ξv) (𝟙 _) hcone ≫ ·) h₂).trans
          (Category.assoc _ _ _).symm
    _ = ξv ≫ ((secStruct D d k (strSection D d k str)
          (strSection_struct D d k str) hinv₀).torsionIso.hom ≫
          pullback.fst (vRhoπ D) _) :=
        congrArg (· ≫ ((secStruct D d k (strSection D d k str)
          (strSection_struct D d k str) hinv₀).torsionIso.hom ≫
          pullback.fst (vRhoπ D) _)) hfac




open scoped FintypeCatDiscrete in
/-- **[T-3E-B glue]** THE SECTION-COVER COMPARISON: the pull of a structure
along its own section cover is the section structure (geometric-point engine at
the ρ-scheme + the pointwise comparison). -/
theorem strSection_pull_eq_secStruct
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve)
    (hinv₀ : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base)
      (strSection D d k str)) N) :
    RhoLevelStructure.pull D
      ((X.pullbackAlong k).pullbackAlongπ
        (secCover D d (strSection D d k str))) str =
      secStruct D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀ := by
  classical
  refine RhoLevelStructure.ext_torsionIso (Iso.ext (pullback.hom_ext ?_ ?_))
  swap
  · -- snd legs
    exact (pullTorsionIso_over D _ str).trans
      (secStruct D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀).over_T.symm
  -- fst legs via the geometric-point engine at the ρ-scheme
  haveI hFinV : IsFinite (vRhoπ D) := (vRhoπ_finite_etale D).1
  haveI hEtV : Etale (vRhoπ D) := (vRhoπ_finite_etale D).2
  haveI hSepV : IsSeparated (vRhoπ D) :=
    inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (vRhoAlgebra D : Type 0)))))
  have hfg : ((RhoLevelStructure.pull D
      ((X.pullbackAlong k).pullbackAlongπ
        (secCover D d (strSection D d k str))) str).torsionIso.hom ≫
      pullback.fst (vRhoπ D) _) ≫ vRhoπ D =
      ((secStruct D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀).torsionIso.hom ≫
      pullback.fst (vRhoπ D) _) ≫ vRhoπ D := by
    rw [Category.assoc, pullback.condition, Category.assoc,
      pullback.condition, ← Category.assoc, ← Category.assoc]
    refine congrArg (· ≫ _) ?_
    exact (RhoLevelStructure.pull D
      ((X.pullbackAlong k).pullbackAlongπ
        (secCover D d (strSection D d k str))) str).over_T.trans
      (secStruct D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀).over_T.symm
  refine eq_of_forall_geomPt_agree (vRhoπ D) _ _ hfg ?_
  intro ω
  haveI hFinPr : IsFinite (strPr D (X.pullbackAlong k)) :=
    MorphismProperty.pullback_fst _ _ (wFramesπ_finite_etale D).1
  obtain ⟨ξt, hξt⟩ := exists_specPoint_lift_of_finite_surjective
    (strPr D (X.pullbackAlong k))
    ((geomPt _ ω ≫ ((X.pullbackAlong k).pullbackAlong
      (secCover D d (strSection D d k str))).curve.torsionπ N) ≫
      pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
        (strSection D d k str))
  exact strSection_pull_fst_pointwise D d k str hinv₀
    (geomPt _ ω ≫ ((X.pullbackAlong k).pullbackAlong
      (secCover D d (strSection D d k str))).curve.torsionπ N) ξt hξt
    (geomPt _ ω) rfl
open scoped FintypeCatDiscrete in
/-- **[T-3E-B] ROUNDTRIP B**: the structure descended from the section of a
structure is the structure itself. -/
theorem rhoOfSection_strSection
    {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' : Scheme.{0}} (k : T' ⟶ X.base)
    (str : RhoLevelStructure D (X.pullbackAlong k).structMap
      (X.pullbackAlong k).curve)
    (hinv₀ : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base)
      (strSection D d k str)) N) :
    rhoOfSection D d k (strSection D d k str)
      (strSection_struct D d k str) hinv₀ = str := by
  classical
  haveI hFinsc : IsFinite (secCover D d (strSection D d k str)) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.isFinite_relQuotientπ_of_free d.f d.over_base
        (d.free_on_points (sympFramedAut_freeAction D)))
  haveI hEtsc : Etale (secCover D d (strSection D d k str)) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.etale_relQuotientπ_of_free d.f d.over_base
        (d.free_on_points (sympFramedAut_freeAction D)))
  haveI hFlsc : Flat (secCover D d (strSection D d k str)) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.flat_relQuotientπ_of_free d.f d.over_base
        (d.free_on_points (sympFramedAut_freeAction D)))
  haveI hSusc : Surjective (secCover D d (strSection D d k str)) :=
    MorphismProperty.pullback_snd _ _
      (d.σZ.surjective_relQuotientπ_of_free d.f d.over_base)
  haveI hQCsc : QuasiCompact (secCover D d (strSection D d k str)) := by
    haveI : IsAffineHom (secCover D d (strSection D d k str)) := inferInstance
    infer_instance
  exact (@rhoOfSection_eq_descend N ‹_› D ‹_› X d ‹_› T' k
    (strSection D d k str)
    (strSection_struct D d k str) hinv₀ hFinsc hEtsc hFlsc hSusc hQCsc).trans
    (descend_eq_of_pull D
      (c := secCover D d (strSection D d k str))
      (α := secStruct D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀)
      (secHhom D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀)
      (secHinv D d k (strSection D d k str)
        (strSection_struct D d k str) hinv₀)
      str (strSection_pull_eq_secStruct D d k str hinv₀))

end MutualInverses

section EngineForm

open scoped FintypeCatDiscrete

variable (D : GaloisRepData N) [Fact (1 < N)]

/-- **[T-YR-3E plumbing]** The frames-cover comparison over a base map: the
covers of the two pullback presentations compare over `k'`. -/
noncomputable def strCoverMap {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    strCover D (X.pullbackAlong (k' ≫ g')) ⟶ strCover D (X.pullbackAlong g') :=
  pullback.map (X.pullbackAlong (k' ≫ g')).structMap (wFramesπ D)
    (X.pullbackAlong g').structMap (wFramesπ D) k' (𝟙 (wFrames D))
    (𝟙 (Spec (CommRingCat.of ℚ)))
    (by
      show (k' ≫ g') ≫ X.structMap ≫ 𝟙 _ = k' ≫ g' ≫ X.structMap
      rw [Category.comp_id, Category.assoc])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
theorem strCoverMap_pr {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    strCoverMap D g' k' ≫ strPr D (X.pullbackAlong g') =
      strPr D (X.pullbackAlong (k' ≫ g')) ≫ k' :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem strCoverMap_taut {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    strCoverMap D g' k' ≫ strTaut D (X.pullbackAlong g') =
      strTaut D (X.pullbackAlong (k' ≫ g')) := by
  refine (pullback.lift_snd _ _ _).trans ?_
  exact Category.comp_id _

/-- **[T-YR-3E plumbing]** The `Ell`-level lift of the cover comparison. -/
noncomputable def strCoverMapEll {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    (X.pullbackAlong (k' ≫ g')).pullbackAlong
        (strPr D (X.pullbackAlong (k' ≫ g'))) ⟶
      (X.pullbackAlong g').pullbackAlong (strPr D (X.pullbackAlong g')) :=
  EllObj.homToPullbackAlong
    ((X.pullbackAlong (k' ≫ g')).pullbackAlongπ
        (strPr D (X.pullbackAlong (k' ≫ g'))) ≫
      X.pullbackAlongMap g' k')
    (strCoverMap D g' k') (strCoverMap_pr D g' k')

@[reassoc]
theorem strCoverMapEll_π {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    strCoverMapEll D g' k' ≫
        (X.pullbackAlong g').pullbackAlongπ (strPr D (X.pullbackAlong g')) =
      (X.pullbackAlong (k' ≫ g')).pullbackAlongπ
          (strPr D (X.pullbackAlong (k' ≫ g'))) ≫
        X.pullbackAlongMap g' k' :=
  EllObj.homToPullbackAlong_pullbackAlongπ _ _ _

@[simp]
theorem strCoverMapEll_baseHom {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    (strCoverMapEll D g' k').baseHom = strCoverMap D g' k' := rfl

/-- **[T-YR-3E plumbing]** The `V_ρ`-side comparison over the two pullback
presentations. -/
noncomputable def vMapOf {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    pullback (vRhoπ D) (X.pullbackAlong (k' ≫ g')).structMap ⟶
      pullback (vRhoπ D) (X.pullbackAlong g').structMap :=
  pullback.map _ _ _ _ (𝟙 (vRho D)) k' (𝟙 (Spec (CommRingCat.of ℚ)))
    (by rw [Category.comp_id, Category.id_comp])
    (by
      show (X.pullbackAlong (k' ≫ g')).structMap ≫ 𝟙 _ =
        k' ≫ (X.pullbackAlong g').structMap
      show ((k' ≫ g') ≫ X.structMap) ≫ 𝟙 _ = k' ≫ g' ≫ X.structMap
      rw [Category.comp_id, Category.assoc])

@[reassoc]
theorem vMapOf_fst {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    vMapOf D g' k' ≫
        pullback.fst (vRhoπ D) (X.pullbackAlong g').structMap =
      pullback.fst (vRhoπ D) (X.pullbackAlong (k' ≫ g')).structMap := by
  refine (pullback.lift_fst _ _ _).trans ?_
  exact Category.comp_id _

@[reassoc]
theorem vMapOf_snd {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T') :
    vMapOf D g' k' ≫
        pullback.snd (vRhoπ D) (X.pullbackAlong g').structMap =
      pullback.snd (vRhoπ D) (X.pullbackAlong (k' ≫ g')).structMap ≫ k' :=
  pullback.lift_snd _ _ _

/-- **[T-YR-3E]** Naturality of the tautological `V_ρ`-points. -/
@[reassoc]
theorem strCoverMap_strVPt {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (v : Fin 2 → ZMod N) :
    strCoverMap D g' k' ≫ strVPt D (X.pullbackAlong g') v =
      strVPt D (X.pullbackAlong (k' ≫ g')) v ≫ vMapOf D g' k' := by
  apply pullback.hom_ext
  · rw [Category.assoc, strVPt_fst, Category.assoc, vMapOf_fst, strVPt_fst,
      ← Category.assoc, strCoverMap_taut]
  · rw [Category.assoc, strVPt_snd, Category.assoc, vMapOf_snd]
    exact (strCoverMap_pr D g' k').trans
      (((congrArg (· ≫ k') (strVPt_snd D (X.pullbackAlong (k' ≫ g')) v)).symm).trans
        (Category.assoc _ _ _))

/-- **[T-YR-3E]** The pulled trivialization square: the torsion base change
intertwines the structure's iso with the `V_ρ`-side comparison. -/
@[reassoc]
theorem pullTorsionIso_vMapOf {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (str0 : RhoLevelStructure D (X.pullbackAlong g').structMap
      (X.pullbackAlong g').curve) :
    torsionMapOfEllHom (X.pullbackAlongMap g' k') N ≫ str0.torsionIso.hom =
      (pullTorsionIso D (X.pullbackAlongMap g' k') str0).hom ≫
        vMapOf D g' k' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, vMapOf_fst]
    exact (pullTorsionIso_fst D (X.pullbackAlongMap g' k') str0).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (torsionMapOfEllHom _ N ≫ ·) str0.over_T) ?_
    refine Eq.trans (torsionMapOfEllHom_π _ N) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((pullTorsionIso D _ str0).hom ≫ ·)
      (vMapOf_snd D g' k')) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (· ≫ k') (pullTorsionIso_over D _ str0)

/-- **[T-YR-3E]** Naturality of the tautological torsion points: the torsion
base change carries the pulled tautological point to the original one. -/
@[reassoc]
theorem strTor_pull {X : EllObj (CommRingCat.of ℚ)}
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (str0 : RhoLevelStructure D (X.pullbackAlong g').structMap
      (X.pullbackAlong g').curve) (v : Fin 2 → ZMod N) :
    strTor D (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0) v ≫
        torsionMapOfEllHom (X.pullbackAlongMap g' k') N =
      strCoverMap D g' k' ≫ strTor D str0 v := by
  have hinv2 : (pullTorsionIso D (X.pullbackAlongMap g' k') str0).inv ≫
      torsionMapOfEllHom (X.pullbackAlongMap g' k') N =
      vMapOf D g' k' ≫ str0.torsionIso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← pullTorsionIso_vMapOf,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (strVPt D (X.pullbackAlong (k' ≫ g')) v ≫ ·)
    hinv2) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ str0.torsionIso.inv)
    (strCoverMap_strVPt D g' k' v).symm) ?_
  exact Category.assoc _ _ _

/-- **[T-YR-3E]** The identity translation acts trivially on framed values. -/
theorem sympFramedSmulNat_one_app {A : EllObj (CommRingCat.of ℚ)}
    (v : (sympFramedProblem D).obj (Opposite.op A)) :
    (sympFramedSmulNat D (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app
      (Opposite.op A) v = v := by
  refine Subtype.ext (Prod.ext ?_ (Subtype.ext ?_))
  · show A.curve.glSmul 1 v.val.1 = v.val.1
    rw [EllipticCurve.glSmul_one]
  · show v.val.2.val ≫ wFramesRightMul D 1 = v.val.2.val
    rw [wFramesRightMul_one, Category.comp_id]

/-- **[T-YR-3E (E1ii)]** THE POINTWISE strZ-PULL COMPARISON: at every field
point of the composite cover, the classified point of the pulled structure and
the comparison-transported classified point of the original agree (equal frames
and equal carve structures force the trivial translation). -/
theorem strZ_pull_pointwise {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (str0 : RhoLevelStructure D (X.pullbackAlong g').structMap
      (X.pullbackAlong g').curve)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (ξt : Spec (CommRingCat.of Ω) ⟶ strCover D (X.pullbackAlong (k' ≫ g'))) :
    ξt ≫ (strZ D d (k' ≫ g')
        (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0)).1 =
      ξt ≫ strCoverMap D g' k' ≫ (strZ D d g' str0).1 := by
  classical
  -- transports of the two classified values to the point object
  have hh₁ : ξt ≫ (strPr D (X.pullbackAlong (k' ≫ g')) ≫ (k' ≫ g')) =
      (X.pullbackAlongπ ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫
        (k' ≫ g'))).baseHom := rfl
  have hVAL'' : d.eqv (strPr D (X.pullbackAlong (k' ≫ g')) ≫ (k' ≫ g'))
      (strZ D d (k' ≫ g')
        (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0)) =
      (sympFramedProblem D).map (EllObj.toPullbackAlong
        (X.pullbackAlongMap (k' ≫ g')
          (strPr D (X.pullbackAlong (k' ≫ g'))))).op
        (strValue D (RhoLevelStructure.pull D
          (X.pullbackAlongMap g' k') str0)) :=
    (d.eqv (strPr D (X.pullbackAlong (k' ≫ g')) ≫ (k' ≫ g'))).apply_symm_apply _
  have hVAL' : d.eqv (strPr D (X.pullbackAlong g') ≫ g') (strZ D d g' str0) =
      (sympFramedProblem D).map (EllObj.toPullbackAlong
        (X.pullbackAlongMap g' (strPr D (X.pullbackAlong g')))).op
        (strValue D str0) :=
    (d.eqv (strPr D (X.pullbackAlong g') ≫ g')).apply_symm_apply _
  have pf₁ : (ξt ≫ (strZ D d (k' ≫ g')
      (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0)).1) ≫ d.f =
      ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')) := by
    rw [Category.assoc, (strZ D d (k' ≫ g') _).2, ← Category.assoc]
    exact rfl
  have heqv₁ : d.eqv ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))
      ⟨ξt ≫ (strZ D d (k' ≫ g')
        (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0)).1, pf₁⟩ =
      (sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
            (strPr D (X.pullbackAlong (k' ≫ g'))))).op
        (strValue D (RhoLevelStructure.pull D
          (X.pullbackAlongMap g' k') str0)) := by
    have hnat := rhoMap_eqv d.toRelRepData
      (EllObj.homToPullbackAlong (X.pullbackAlongπ
        ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁)
      ξt rfl rfl
      (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)
      (strZ D d (k' ≫ g')
        (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0))
    rw [hVAL''] at hnat
    exact hnat.symm.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      (EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
        (strPr D (X.pullbackAlong (k' ≫ g'))))).op
      (EllObj.homToPullbackAlong (X.pullbackAlongπ
        ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁).op
      (strValue D (RhoLevelStructure.pull D
        (X.pullbackAlongMap g' k') str0))).symm
  have hh₂ : (ξt ≫ strCoverMap D g' k') ≫
      (strPr D (X.pullbackAlong g') ≫ g') =
      (X.pullbackAlongπ ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫
        (k' ≫ g'))).baseHom := by
    show (ξt ≫ strCoverMap D g' k') ≫ strPr D (X.pullbackAlong g') ≫ g' =
      (ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ k' ≫ g'
    rw [Category.assoc, ← Category.assoc (strCoverMap D g' k'),
      strCoverMap_pr]
    simp only [Category.assoc]
    exact rfl
  have pf₂ : ((ξt ≫ strCoverMap D g' k') ≫ (strZ D d g' str0).1) ≫ d.f =
      ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')) := by
    rw [Category.assoc, (strZ D d g' str0).2, ← Category.assoc]
    exact hh₂.trans rfl
  have heqv₂ : d.eqv ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))
      ⟨(ξt ≫ strCoverMap D g' k') ≫ (strZ D d g' str0).1, pf₂⟩ =
      (sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
          (ξt ≫ strCoverMap D g' k') hh₂) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap g'
            (strPr D (X.pullbackAlong g')))).op
        (strValue D str0) := by
    have hnat := rhoMap_eqv d.toRelRepData
      (EllObj.homToPullbackAlong (X.pullbackAlongπ
        ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
        (ξt ≫ strCoverMap D g' k') hh₂)
      (ξt ≫ strCoverMap D g' k') rfl hh₂
      (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)
      (strZ D d g' str0)
    rw [hVAL'] at hnat
    exact hnat.symm.trans (FunctorToTypes.map_comp_apply (sympFramedProblem D)
      (EllObj.toPullbackAlong (X.pullbackAlongMap g'
        (strPr D (X.pullbackAlong g')))).op
      (EllObj.homToPullbackAlong (X.pullbackAlongπ
        ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
        (ξt ≫ strCoverMap D g' k') hh₂).op
      (strValue D str0)).symm
  -- frames agree (trivial translation)
  have hframe : ((sympFramedProblem D).map
      ((EllObj.homToPullbackAlong (X.pullbackAlongπ
        ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
        (ξt ≫ strCoverMap D g' k') hh₂) ≫
        EllObj.toPullbackAlong (X.pullbackAlongMap g'
          (strPr D (X.pullbackAlong g')))).op
      (strValue D str0)).val.2.val =
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
            (strPr D (X.pullbackAlong (k' ≫ g'))))).op
        (strValue D (RhoLevelStructure.pull D
          (X.pullbackAlongMap g' k') str0))).val.2.val ≫
      wFramesRightMul D 1 := by
    show ((ξt ≫ strCoverMap D g' k') ≫ 𝟙 _) ≫
        strTaut D (X.pullbackAlong g') =
      ((ξt ≫ 𝟙 _) ≫ strTaut D (X.pullbackAlong (k' ≫ g'))) ≫
        wFramesRightMul D 1
    rw [wFramesRightMul_one, Category.comp_id, Category.comp_id,
      Category.comp_id, Category.assoc, strCoverMap_taut]
  -- invertibility discharges
  have hinvSpec : NIsInvertible (Spec (CommRingCat.of ℚ)) N := by
    have hq : IsUnit ((N : ℚ)) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
    rwa [map_natCast] at this
  have hinvΩob : NIsInvertible (X.pullbackAlong
      ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))).base N :=
    NIsInvertible.of_hom
      (((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')) ≫
        X.structMap) hinvSpec
  have hinvCover'' : NIsInvertible (strCover D (X.pullbackAlong (k' ≫ g'))) N :=
    NIsInvertible.of_hom (strPr D (X.pullbackAlong (k' ≫ g')) ≫
      (X.pullbackAlong (k' ≫ g')).structMap) hinvSpec
  have hinvCover' : NIsInvertible (strCover D (X.pullbackAlong g')) N :=
    NIsInvertible.of_hom (strPr D (X.pullbackAlong g') ≫
      (X.pullbackAlong g').structMap) hinvSpec
  -- carve structures agree
  have hN₁ := rhoLevelStructureOfCarve_map D
    ((EllObj.homToPullbackAlong (X.pullbackAlongπ
      ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁) ≫
      EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
        (strPr D (X.pullbackAlong (k' ≫ g')))))
    hinvΩob hinvCover''
    (strValue D (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0))
  have hV'' := rhoLevelStructureOfCarve_strValue D
    (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0) hinvCover''
  have hN₂ := rhoLevelStructureOfCarve_map D
    ((EllObj.homToPullbackAlong (X.pullbackAlongπ
      ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
      (ξt ≫ strCoverMap D g' k') hh₂) ≫
      EllObj.toPullbackAlong (X.pullbackAlongMap g'
        (strPr D (X.pullbackAlong g'))))
    hinvΩob hinvCover' (strValue D str0)
  have hV' := rhoLevelStructureOfCarve_strValue D str0 hinvCover'
  have hMAPEQ : (((EllObj.homToPullbackAlong (X.pullbackAlongπ
      ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁ ≫
      EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
        (strPr D (X.pullbackAlong (k' ≫ g'))))) ≫
      (X.pullbackAlong (k' ≫ g')).pullbackAlongπ
        (strPr D (X.pullbackAlong (k' ≫ g')))) ≫
      X.pullbackAlongMap g' k') =
      ((EllObj.homToPullbackAlong (X.pullbackAlongπ
        ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
        (ξt ≫ strCoverMap D g' k') hh₂ ≫
        EllObj.toPullbackAlong (X.pullbackAlongMap g'
          (strPr D (X.pullbackAlong g')))) ≫
        (X.pullbackAlong g').pullbackAlongπ
          (strPr D (X.pullbackAlong g'))) := by
    apply (EllObj.homPullbackAlongEquiv X g' _).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show _ ≫ X.pullbackAlongπ g' = _ ≫ X.pullbackAlongπ g'
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (_ ≫ ·)
        (ModuliProblem.pullbackAlongMap_pullbackAlongπ X g' k')) ?_
      refine Eq.trans (congrArg (· ≫ X.pullbackAlongπ (k' ≫ g'))
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (EllObj.toPullbackAlong_pullbackAlongπ
            (X.pullbackAlongMap (k' ≫ g')
              (strPr D (X.pullbackAlong (k' ≫ g')))))))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (_ ≫ ·)
        (ModuliProblem.pullbackAlongMap_pullbackAlongπ X (k' ≫ g')
          (strPr D (X.pullbackAlong (k' ≫ g'))))) ?_
      refine Eq.trans (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _) ?_
      refine Eq.symm ?_
      refine Eq.trans (congrArg (· ≫ X.pullbackAlongπ g')
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (EllObj.toPullbackAlong_pullbackAlongπ
            (X.pullbackAlongMap g' (strPr D (X.pullbackAlong g'))))))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (_ ≫ ·)
        (ModuliProblem.pullbackAlongMap_pullbackAlongπ X g'
          (strPr D (X.pullbackAlong g')))) ?_
      exact EllObj.homToPullbackAlong_pullbackAlongπ _ _ _
    · show (((ξt ≫ 𝟙 _) ≫ 𝟙 _) ≫
          strPr D (X.pullbackAlong (k' ≫ g'))) ≫ k' =
        ((ξt ≫ strCoverMap D g' k') ≫ 𝟙 _) ≫
          strPr D (X.pullbackAlong g')
      rw [Category.comp_id, Category.comp_id, Category.comp_id,
        Category.assoc, Category.assoc, strCoverMap_pr]
      exact rfl
  have hcarve : rhoLevelStructureOfCarve D
      (X.pullbackAlong ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫
        (k' ≫ g'))).structMap
      (X.pullbackAlong ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫
        (k' ≫ g'))).curve hinvΩob
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
            (strPr D (X.pullbackAlong (k' ≫ g'))))).op
        (strValue D (RhoLevelStructure.pull D
          (X.pullbackAlongMap g' k') str0))).val.1
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
            (strPr D (X.pullbackAlong (k' ≫ g'))))).op
        (strValue D (RhoLevelStructure.pull D
          (X.pullbackAlongMap g' k') str0))).val.2.val
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
            (strPr D (X.pullbackAlong (k' ≫ g'))))).op
        (strValue D (RhoLevelStructure.pull D
          (X.pullbackAlongMap g' k') str0))).val.2.property
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))) ξt hh₁) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap (k' ≫ g')
            (strPr D (X.pullbackAlong (k' ≫ g'))))).op
        (strValue D (RhoLevelStructure.pull D
          (X.pullbackAlongMap g' k') str0))).property =
      rhoLevelStructureOfCarve D
      (X.pullbackAlong ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫
        (k' ≫ g'))).structMap
      (X.pullbackAlong ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫
        (k' ≫ g'))).curve hinvΩob
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
          (ξt ≫ strCoverMap D g' k') hh₂) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap g'
            (strPr D (X.pullbackAlong g')))).op
        (strValue D str0)).val.1
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
          (ξt ≫ strCoverMap D g' k') hh₂) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap g'
            (strPr D (X.pullbackAlong g')))).op
        (strValue D str0)).val.2.val
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
          (ξt ≫ strCoverMap D g' k') hh₂) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap g'
            (strPr D (X.pullbackAlong g')))).op
        (strValue D str0)).val.2.property
      ((sympFramedProblem D).map
        ((EllObj.homToPullbackAlong (X.pullbackAlongπ
          ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g')))
          (ξt ≫ strCoverMap D g' k') hh₂) ≫
          EllObj.toPullbackAlong (X.pullbackAlongMap g'
            (strPr D (X.pullbackAlong g')))).op
        (strValue D str0)).property := by
    refine hN₁.trans (Eq.trans ?_ hN₂.symm)
    refine Eq.trans (congrArg (RhoLevelStructure.pull D _) hV'') ?_
    refine Eq.trans (congrArg (fun β => RhoLevelStructure.pull D _
      (RhoLevelStructure.pull D _ β))
      (rfl : RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0 =
        RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0)) ?_
    refine Eq.trans (RhoLevelStructure.pull_comp D _ _ _).symm ?_
    refine Eq.trans (RhoLevelStructure.pull_comp D _ _ _).symm ?_
    refine Eq.trans (congrArg (fun m => RhoLevelStructure.pull D m str0)
      hMAPEQ) ?_
    refine Eq.trans (RhoLevelStructure.pull_comp D _ _ _) ?_
    exact congrArg (RhoLevelStructure.pull D _) hV'.symm
  -- the value comparison at the trivial translation
  have hvc := value_eq_smulNat_of_carve_eq D hinvΩob _ _ 1 hframe hcarve
  rw [sympFramedSmulNat_one_app] at hvc
  have hz := congrArg Subtype.val
    ((d.eqv ((ξt ≫ strPr D (X.pullbackAlong (k' ≫ g'))) ≫ (k' ≫ g'))).injective
      (heqv₂.trans (hvc.trans heqv₁.symm)))
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact hz.symm

/-- **[T-YR-3E (E1iii)]** THE strZ-PULL NATURALITY (global): the classified
point of the pulled structure is the comparison-transport of the original. -/
theorem strZ_pull {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (str0 : RhoLevelStructure D (X.pullbackAlong g').structMap
      (X.pullbackAlong g').curve) :
    (strZ D d (k' ≫ g')
        (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0)).1 =
      strCoverMap D g' k' ≫ (strZ D d g' str0).1 := by
  haveI hFinf : IsFinite d.f := d.finite
  haveI hEtf : Etale d.f := d.etale
  haveI hSepf : IsSeparated d.f := inferInstance
  have hfg : (strZ D d (k' ≫ g')
      (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0)).1 ≫ d.f =
      (strCoverMap D g' k' ≫ (strZ D d g' str0).1) ≫ d.f := by
    rw [(strZ D d (k' ≫ g') _).2, Category.assoc, (strZ D d g' str0).2,
      ← Category.assoc, strCoverMap_pr]
    exact (Category.assoc _ _ _).symm
  refine eq_of_forall_geomPt_agree d.f _ _ hfg ?_
  intro ω
  refine Eq.trans (strZ_pull_pointwise D d g' k' str0 (geomPt _ ω)) ?_
  exact (Category.assoc _ _ _).symm

/-- **[T-YR-3E (E1iv)]** σP-naturality. -/
theorem strSigmaP_pull {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (str0 : RhoLevelStructure D (X.pullbackAlong g').structMap
      (X.pullbackAlong g').curve) :
    strSigmaP D d (k' ≫ g')
        (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0) =
      strCoverMap D g' k' ≫ strSigmaP D d g' str0 := by
  rw [strSigmaP, strSigmaP, strZ_pull, Category.assoc]

/-- **[T-YR-3E (E1v)] THE strSection-PULL NATURALITY**: the descended section of
a pulled structure is the restricted section. -/
theorem strSection_pull {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (str0 : RhoLevelStructure D (X.pullbackAlong g').structMap
      (X.pullbackAlong g').curve) :
    strSection D d (k' ≫ g')
        (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0) =
      k' ≫ strSection D d g' str0 := by
  refine (EffectiveEpi.uniq (strPr D (X.pullbackAlong (k' ≫ g')))
    (strSigmaP D d (k' ≫ g')
      (RhoLevelStructure.pull D (X.pullbackAlongMap g' k') str0))
    (fun g₁ g₂ h => strSigmaP_coequalizes D d (k' ≫ g') _ g₁ g₂ h)
    (k' ≫ strSection D d g' str0) ?_).symm
  rw [← Category.assoc, ← strCoverMap_pr]
  exact ((Category.assoc _ _ _).trans
    (congrArg (strCoverMap D g' k' ≫ ·) (strPr_strSection D d g' str0))).trans
    (strSigmaP_pull D d g' k' str0).symm

/-- **[T-YR-3E (E2)]** THE rhoOfSection-NATURALITY: descending the restricted
section is the pull of the descended structure (via the section bijection and
the strSection pull-naturality). -/
theorem rhoOfSection_pull {X : EllObj (CommRingCat.of ℚ)}
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D) X)
    [IsAffineHom d.f]
    {T' T'' : Scheme.{0}} (g' : T' ⟶ X.base) (k' : T'' ⟶ T')
    (s : T' ⟶ d.σZ.relQuotient d.f d.over_base)
    (hs : s ≫ d.σZ.relQuotientStruct d.f d.over_base = g')
    (hinv : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base) s) N)
    (hs' : (k' ≫ s) ≫ d.σZ.relQuotientStruct d.f d.over_base = k' ≫ g')
    (hinv' : NIsInvertible (pullback (d.σZ.relQuotientπ d.f d.over_base)
      (k' ≫ s)) N) :
    RhoLevelStructure.pull D (X.pullbackAlongMap g' k')
        (rhoOfSection D d g' s hs hinv) =
      rhoOfSection D d (k' ≫ g') (k' ≫ s) hs' hinv' := by
  -- strSection is injective (roundtrip B), so compare the sections
  have hinj := rhoOfSection_strSection D d (k' ≫ g')
    (RhoLevelStructure.pull D (X.pullbackAlongMap g' k')
      (rhoOfSection D d g' s hs hinv))
  have hsec : strSection D d (k' ≫ g')
      (RhoLevelStructure.pull D (X.pullbackAlongMap g' k')
        (rhoOfSection D d g' s hs hinv)) = k' ≫ s := by
    rw [strSection_pull, strSection_rhoOfSection D d g' s hs hinv]
  -- transport the roundtrip along hsec
  have hinvSpec : NIsInvertible (Spec (CommRingCat.of ℚ)) N := by
    have hq : IsUnit ((N : ℚ)) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
    rwa [map_natCast] at this
  have hB := rhoOfSection_strSection D d (k' ≫ g')
    (RhoLevelStructure.pull D (X.pullbackAlongMap g' k')
      (rhoOfSection D d g' s hs hinv))
    (NIsInvertible.of_hom
      (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) _ ≫
        (k' ≫ g') ≫ X.structMap) hinvSpec)
  -- rewrite the strSection inside hB by hsec (proof-irrelevant hinv-slots)
  refine Eq.trans hB.symm ?_
  -- now: rhoOfSection (k'≫g') (strSection (pull …)) hinv₀ = rhoOfSection (k'≫g') (k'≫s) hs' hinv'
  -- congruence in the section argument
  have hcongr : ∀ (s₁ s₂ : T'' ⟶ d.σZ.relQuotient d.f d.over_base)
      (h12 : s₁ = s₂) (hs₁ : s₁ ≫ d.σZ.relQuotientStruct d.f d.over_base =
        k' ≫ g')
      (hinv₁ : NIsInvertible (pullback
        (d.σZ.relQuotientπ d.f d.over_base) s₁) N),
      rhoOfSection D d (k' ≫ g') s₁ hs₁ hinv₁ =
        rhoOfSection D d (k' ≫ g') s₂ (h12 ▸ hs₁) (h12 ▸ hinv₁) := by
    intro s₁ s₂ h12 hs₁ hinv₁
    subst h12
    rfl
  exact (hcongr _ _ hsec _ _).trans rfl

/-- **[T-YR-3 ENGINE FORM] AffineOverEll (rhoProblem D)** — the ρ-level moduli
problem is affine over `Ell/ℚ`: relatively representable by the finite étale
free `GL₂`-quotients, functorially in the base (KM 4.7.0 for `Y(ρ̄)`). -/
theorem rhoProblem_affineOverEll :
    ModuliProblem.AffineOverEll (rhoProblem D) := by
  classical
  intro X
  obtain ⟨d⟩ := sympFramed_equivariantRelRepData D X
  haveI hAf : IsAffineHom d.f := by
    haveI := d.finite
    infer_instance
  have hfe := d.σZ.relQuotientStruct_finite_etale_of_free d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D)) d.finite d.etale
  haveI hFinStruct : IsFinite (d.σZ.relQuotientStruct d.f d.over_base) := hfe.1
  have hinvSpec : NIsInvertible (Spec (CommRingCat.of ℚ)) N := by
    have hq : IsUnit ((N : ℚ)) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
    rwa [map_natCast] at this
  refine ⟨d.σZ.relQuotient d.f d.over_base,
    d.σZ.relQuotientStruct d.f d.over_base, inferInstance, ?_⟩
  refine ⟨fun {T} g => {
    toFun := fun h => rhoOfSection D d g h.1 h.2
      (NIsInvertible.of_hom
        (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) h.1 ≫
          g ≫ X.structMap) hinvSpec)
    invFun := fun str => ⟨strSection D d g str, strSection_struct D d g str⟩
    left_inv := fun h => Subtype.ext
      (strSection_rhoOfSection D d g h.1 h.2 _)
    right_inv := fun str => rhoOfSection_strSection D d g str _ }, ?_⟩
  intro T T' g k h
  exact (rhoOfSection_pull D d g k h.1 h.2 _ _ _).symm

/-- **[T-YR-5] THE ρ-LEVEL MODULI PROBLEM IS REPRESENTABLE** (`N ≥ 3`): the
KM 4.7.0 engine applied to the affine-over-`Ell` and rigidity inputs. `Y(ρ̄)`
exists as a fine moduli scheme. -/
theorem rhoProblem_representable (hN : 3 ≤ (N : ℤ)) :
    (rhoProblem D).Representable :=
  ModuliProblem.representable_of_affineOverEll_of_rigidNoeth _
    (rhoProblem_affineOverEll D)
    (rhoProblem_affineOverEll D).relativelyRepresentable
    (rho_rigidNoeth D hN)

end EngineForm

open scoped FintypeCatDiscrete in
/-- **(T-F6 = expert review Q9: the symplectic Isom-scheme route) — THE 3d/3e
CLOSURE.** Relative representability of the ρ-level problem: for every elliptic
curve `E` over a `ℚ`-scheme `T`, the functor `T' ↦ {ρ-level structures on
E ×_T T'}` is representable by a finite étale `T`-scheme — the free `GL₂`
quotient of the symplectically framed moduli. Same statement as
`rhoLevel_relativelyRepresentable` (YRho.lean); proven here downstream of the
section dictionary (3c/3d) and the mutual inverses (3e). -/
theorem rhoLevel_relativelyRepresentable' (hN : 3 ≤ N)
    (D : GaloisRepData N) {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ))
    (E : EllipticCurve T) :
    ∃ (I : Scheme.{0}) (f : I ⟶ T), IsFinite f ∧ Etale f ∧
      ∀ {T' : Scheme.{0}} (k : T' ⟶ T),
        Nonempty ({ h : T' ⟶ I // h ≫ f = k } ≃
          RhoLevelStructure D (k ≫ sT) (E.baseChange k)) := by
  classical
  haveI hFact : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨d⟩ := sympFramed_equivariantRelRepData D
    (⟨T, sT, E⟩ : EllObj (CommRingCat.of ℚ))
  haveI hAf : IsAffineHom d.f := by
    haveI := d.finite
    infer_instance
  have hfe := d.σZ.relQuotientStruct_finite_etale_of_free d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D)) d.finite d.etale
  refine ⟨d.σZ.relQuotient d.f d.over_base,
    d.σZ.relQuotientStruct d.f d.over_base, hfe.1, hfe.2, ?_⟩
  intro T' k
  have hinvSpec : NIsInvertible (Spec (CommRingCat.of ℚ)) N := by
    have hq : IsUnit ((N : ℚ)) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
    rwa [map_natCast] at this
  refine ⟨{
    toFun := fun h => rhoOfSection D d k h.1 h.2
      (NIsInvertible.of_hom
        (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) h.1 ≫ k ≫ sT)
        hinvSpec)
    invFun := fun str =>
      ⟨strSection D d k str, strSection_struct D d k str⟩
    left_inv := fun h => Subtype.ext
      (strSection_rhoOfSection D d k h.1 h.2
        (NIsInvertible.of_hom
          (pullback.snd (d.σZ.relQuotientπ d.f d.over_base) h.1 ≫ k ≫ sT)
          hinvSpec))
    right_inv := fun str => rhoOfSection_strSection D d k str
      (NIsInvertible.of_hom
        (pullback.snd (d.σZ.relQuotientπ d.f d.over_base)
          (strSection D d k str) ≫ k ≫ sT)
        hinvSpec) }⟩

end

end ModularCurves
