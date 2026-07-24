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

end StructuresToSections

end

end ModularCurves
