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

end SectionsToStructures

end

end ModularCurves
