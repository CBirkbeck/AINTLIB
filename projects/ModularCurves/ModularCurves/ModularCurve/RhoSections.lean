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

end

end ModularCurves
