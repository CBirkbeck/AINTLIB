/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.OrdPipeline
import ModularCurves.WeilPairing.SelfUniversal
import ModularCurves.Moduli.KeystoneGeometricPoint

/-!
# The field leaf of `e_N(x,x) = 1` (U5-AC)

Over an algebraically closed field `K` with `(N : K) ≠ 0`, the diagonal pairing value
is `1`: transport to the projective Weierstrass model along the pointed record iso of
`exists_projModelIso_of_field` (U1, `weilPairingEval_mapIso`), instantiate the
Katz–Mazur dataset through the κ-dictionary + G2′ chart machinery, and read the value
through `weilPairingEval_eq_torsionSplittingEval` (U5-L4) +
`torsionSplittingEval_self_eq_one` (U5-L5).

Stage plan (each stage replaces the trailing `sorry`):
1. model transport (DONE here);
2. the model-side instances (IsIntegral, Dedekind, Flat/IsFinite/LOFP for `[N]`);
3. the dataset (KAPPA-DICT + officiality + G2′);
4. the H-side splittings (D4-pipe) + the dictionaries (p, hxp, hT, zQm-data);
5. the L4-pin + L5-close.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ModularCurves

namespace EllipticCurve

/-- **(U5-AC, the algebraically closed field leaf)** `e_N(x, x) = 1` over an
algebraically closed field in which `N` is invertible. -/
theorem weilPairingEval_self_of_isAlgClosed {K : Type u} [Field K] [DecidableEq K]
    [IsAlgClosed K]
    (E : EllipticCurve (Spec (CommRingCat.of K))) {N : ℕ} [NeZero N]
    (hNK : (N : K) ≠ 0)
    (x : E.Point (𝟙 (Spec (CommRingCat.of K))))
    (hx : x.1 ≫ E.mulByHom N = 𝟙 _ ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(Spec (CommRingCat.of K), ⊤)) = 1 := by
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := by
    haveI : IsNoetherianRing K := inferInstance
    infer_instance
  -- stage 1: the model transport
  obtain ⟨W, hell, ψ, hψπ, hψz⟩ := exists_projModelIso_of_field E
  haveI := hell
  have hΦw : ψ.hom ≫ (modelEllipticCurve W).asOver.hom = E.asOver.hom := hψπ
  set Φ : E.asOver ≅ (modelEllipticCurve W).asOver := Over.isoMk ψ hΦw with hΦ
  have hΦη : (η[E.asOver] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.asOver) ≫ Φ.hom =
      η[(modelEllipticCurve W).asOver] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, E.one_eq_zero, (modelEllipticCurve W).one_eq_zero]
    exact (Category.assoc _ _ _).trans
      (congrArg _ (show E.zero ≫ ψ.hom = (modelEllipticCurve W).zero from hψz))
  haveI hmon : IsMonHom Φ.hom := isMonHom_of_pointed Φ.hom hΦη
  have hx' : (Point.mapIso Φ x).1 ≫ (modelEllipticCurve W).mulByHom N =
      𝟙 _ ≫ (modelEllipticCurve W).zero :=
    Point.mapIso_killedBy Φ hx
  rw [← weilPairingEval_mapIso Φ x x hx hx hx' hx']
  -- stage 2: the model-side instances
  haveI hIntP : AlgebraicGeometry.IsIntegral (projModel W) := isIntegral_projModel_u W
  haveI hFlat : Flat ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_flat N
  haveI hFin : IsFinite ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_isFinite N
  haveI hLofp : LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_locallyOfFinitePresentation N
  haveI hbcEll : ((W.baseChange K).toAffine).IsElliptic := by
    rw [EllipticCurve.baseChange_self_eq W]
    infer_instance
  haveI hDed : IsDedekindDomain
      (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve K).CoordinateRing := inferInstance
  haveI hsepπ : IsSeparated (modelEllipticCurve W).π := inferInstance
  haveI hIntE : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
  haveI hIntPB : AlgebraicGeometry.IsIntegral
      (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    isIntegral_pullback_id (modelEllipticCurve W)
  -- stage 3: the dataset at the model
  set Q : ((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))) :=
    EllipticCurve.Point.asSection (modelEllipticCurve W) (𝟙 _) (Point.mapIso Φ x)
    with hQdef
  have hQ : Q ∈ torsionPoints (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N :=
    asSection_mem_torsionPoints (modelEllipticCurve W) (Point.mapIso Φ x) hx'
  obtain ⟨M, hM, _hMinv⟩ := exists_module_kappa (modelEllipticCurve W)
    (modelEllipticCurve W).smooth (𝟙 (Spec (CommRingCat.of K))) Q
  obtain ⟨edict⟩ := nonempty_tensorObj_sectionIdeal_iso_zeroIdeal_of_field
    (modelEllipticCurve W) (modelEllipticCurve W).smooth Q M hM
  -- stage 3b: officiality covers + the G2′ dataset
  have hsmPB : SmoothOfRelativeDimension 1
      (pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _
      (modelEllipticCurve W).smooth
  have h₁ := (RelEffCartierDiv.sectionDivisor_isOfficial hsmPB
    (Q.1 : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) Q.2).locallyPrincipal
  have h₂ := (RelEffCartierDiv.sectionDivisor_isOfficial hsmPB
    (Scheme.Modules.baseChangeZero (modelEllipticCurve W).π (modelEllipticCurve W).zero
      (modelEllipticCurve W).zero_π (𝟙 (Spec (CommRingCat.of K))))
    (Scheme.Modules.baseChangeZero_snd _ _ _ _)).locallyPrincipal
  haveI hsepT : IsSeparated (terminal.from (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) := by
    haveI h1 : IsSeparated (pullback.snd (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))) :=
      MorphismProperty.pullback_snd (P := @IsSeparated) _ _ ‹_›
    haveI h2 : IsSeparated (pullback.snd (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K))) ≫ terminal.from (Spec (CommRingCat.of K))) :=
      inferInstance
    rw [show terminal.from (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) =
      pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) ≫
        terminal.from (Spec (CommRingCat.of K)) from (terminal.comp_from _).symm]
    exact h2
  haveI hdiag : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))))) :=
    inferInstance
  obtain ⟨V, f₁, f₂, ι', Wc, hWc, e, ch, A, hspan₁, hnzd₁, hspan₂, hnzd₂, hnorm, hWch, hu⟩ :=
    exists_normalized_chart_dataset_perChart (modelEllipticCurve W)
      (modelEllipticCurve W).smooth (𝟙 (Spec (CommRingCat.of K))) Q M hM
      (Scheme.Hom.ker (Q.1 : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))))
      (Scheme.Hom.ker (Scheme.Modules.baseChangeZero (modelEllipticCurve W).π
        (modelEllipticCurve W).zero (modelEllipticCurve W).zero_π
        (𝟙 (Spec (CommRingCat.of K)))))
      edict h₁ h₂
  -- stage 4: the H-side splittings, the SpecPoints dictionary, and the torsion transfer
  obtain ⟨h, hn, hsplit⟩ := exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints
    (modelEllipticCurve W) (modelEllipticCurve W).smooth (𝟙 (Spec (CommRingCat.of K)))
    N Q hQ M hM Wc hWc e hnorm
  have hspecid : Spec.map (CommRingCat.ofHom (algebraMap K K)) =
      𝟙 (Spec (CommRingCat.of K)) := by
    rw [show CommRingCat.ofHom (algebraMap K K) = 𝟙 (CommRingCat.of K) from rfl,
      Spec.map_id]
  set p : (modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap K K))) :=
    ⟨(Q.1 : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ≫
        pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))),
      (Category.assoc _ _ _).trans
        ((congrArg (fun m => (Q.1 : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ≫ m)
          (pullback.condition
            (f := (modelEllipticCurve W).π) (g := 𝟙 (Spec (CommRingCat.of K))))).trans
        ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ 𝟙 (Spec (CommRingCat.of K))) Q.2).trans
        ((Category.id_comp _).trans
          hspecid.symm))))⟩ with hpdef
  -- stage 4b: the torsion transfer to the cast point (local copies of the
  -- OrdPipeline-private cast micros; flagged for cleanup dedup)
  have castPoint_zsmul' : ∀ {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂)
      (n : ℤ) (X : V₁.toAffine.Point),
      (h ▸ (n • X) : V₂.toAffine.Point) = n • (h ▸ X : V₂.toAffine.Point) := by
    intro V₁ V₂ h n X
    subst h; rfl
  have basePointCast_eq_cast' : ∀ (X : ((W.baseChange K).toAffine).Point),
      EllipticCurve.basePointCast W X =
        ((EllipticCurve.baseChange_self_eq W) ▸ X : W.toAffine.Point) := by
    intro X
    have hzero : ∀ {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂),
        (h ▸ (WeierstrassCurve.Affine.Point.zero : V₁.toAffine.Point) :
          V₂.toAffine.Point) = WeierstrassCurve.Affine.Point.zero := by
      intro V₁ V₂ h; subst h; rfl
    have hsome : ∀ {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂) (x0 y0 : K)
        (ns : V₁.toAffine.Nonsingular x0 y0),
        (h ▸ (WeierstrassCurve.Affine.Point.some x0 y0 ns : V₁.toAffine.Point) :
          V₂.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x0 y0 (by rw [← h]; exact ns) := by
      intro V₁ V₂ h x0 y0 ns; subst h; rfl
    cases X with
    | zero => exact (hzero (EllipticCurve.baseChange_self_eq W)).symm
    | some xk yk hk =>
      exact (hsome (EllipticCurve.baseChange_self_eq W) xk yk hk).symm
  have basePointCast_zsmul' : ∀ (n : ℤ) (X : ((W.baseChange K).toAffine).Point),
      EllipticCurve.basePointCast W (n • X) =
        n • EllipticCurve.basePointCast W X := by
    intro n X
    rw [basePointCast_eq_cast', basePointCast_eq_cast',
      castPoint_zsmul' (EllipticCurve.baseChange_self_eq W) n X]
  -- the point-group transfer ξ : baseChange-points ≃+ Spec.map-points, ξ Q = p
  set ξ : ((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))) ≃+
      (modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap K K))) :=
    (EllipticCurve.Point.baseChangeEquiv (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) (𝟙 (Spec (CommRingCat.of K)))).trans
      (pointCongr (modelEllipticCurve W)
        ((Category.id_comp _).trans hspecid.symm)) with hξdef
  have hxiQ : ξ Q = p := by
    refine Subtype.ext ?_
    show (pointCongr (modelEllipticCurve W) _
      (EllipticCurve.Point.baseChangeEquiv _ _ _ Q)).1 = p.1
    rw [pointCongr_apply_coe, EllipticCurve.Point.baseChangeEquiv_apply_coe]
  have hNp : (N : ℤ) • p = 0 := by
    have hQ0 : (N : ℤ) • Q = 0 := hQ
    have h1 := congrArg ξ hQ0
    rw [map_zsmul, hxiQ, map_zero] at h1
    exact h1
  have hT : (N : ℤ) • EllipticCurve.basePointCast W (projModelPointsEquiv W K p) = 0 := by
    rw [← basePointCast_zsmul' (N : ℤ) (projModelPointsEquiv W K p),
      ← projModelPointsEquiv_zsmul W (N : ℤ) p, hNp]
    rw [show (0 : (modelEllipticCurve W).Point
        (Spec.map (CommRingCat.ofHom (algebraMap K K)))) =
      ⟨Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ projModelZero W,
        (Category.assoc _ _ _).trans
          ((congrArg (fun m => Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ m)
            (projModelZero_projModelπ W)).trans (Category.comp_id _))⟩ from rfl,
    ]
    exact (congrArg (EllipticCurve.basePointCast W)
      (projModelPointsEquiv_zero W K)).trans (EllipticCurve.basePointCast_zero W)
  -- stage 5: the remaining instance slots and the L4-pin + L5-close
  haveI hQC : QuasiCompact (Q.1 : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) := inferInstance
  haveI hsepPB : IsSeparated (pullback.snd (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ ‹_›
  haveI hICI : IsClosedImmersion (Q.1 : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) := by
    refine MorphismProperty.of_postcomp (W := @IsClosedImmersion)
      (W' := @IsSeparated) _
      (pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))
      hsepPB ?_
    rw [show (Q.1 : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ≫
      pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) =
      𝟙 (Spec (CommRingCat.of K)) from Q.2]
    infer_instance
  haveI hIsoτ : IsIso (translateByPoint (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) Q) := by
    show IsIso (((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).translateBy
      (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q)).left
    rw [show ((modelEllipticCurve W).baseChange
        (𝟙 (Spec (CommRingCat.of K)))).translateBy
        (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q) =
      (((modelEllipticCurve W).baseChange
        (𝟙 (Spec (CommRingCat.of K)))).translateByIso
        (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q)).hom from rfl]
    exact (Over.forget _).map_isIso
      (((modelEllipticCurve W).baseChange
        (𝟙 (Spec (CommRingCat.of K)))).translateByIso
        (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q)).hom
  haveI hDomτ : IsDominant (translateByPoint (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) Q) := inferInstance
  -- stage 5b: the chart choice, the L4-pin, and the L5-close
  haveI hIrr : IrreducibleSpace ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) := inferInstance
  obtain ⟨c₀, hc₀⟩ : ∃ i, (Nonempty.some inferInstance : ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ∈ Wc i := by
    have h1 : (Nonempty.some inferInstance : ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ∈
        ((⨆ i, Wc i) : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).Opens) := by
      rw [hWc]; trivial
    rwa [TopologicalSpace.Opens.mem_iSup] at h1
  obtain ⟨ypre, hypre⟩ := (mulByHom_surjective_global
    ((modelEllipticCurve W).baseChange (𝟙 (Spec (CommRingCat.of K)))) N).surj
    (Nonempty.some inferInstance : ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))))
  haveI hNec₀ : Nonempty ((mulByN (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc c₀) : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).Opens) :=
    ⟨⟨ypre, show (mulByN (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) N).base ypre ∈ Wc c₀ from hypre ▸ hc₀⟩⟩
  have hxp : (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q ≫
      baseChangeIdFstOver (modelEllipticCurve W)).left = p.1 := rfl
  have hNZ : ((N : ℤ) : K) ≠ 0 := by exact_mod_cast hNK
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  -- the L4-pin
  rw [weilPairingEval_eq_torsionSplittingEval (modelEllipticCurve W)
    (Point.mapIso Φ x) (Point.mapIso Φ x) hx' hx' M hM Wc hWc e hnorm]
  -- the L5-close through the ΓSpecIso injectivity
  set zQm : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) := Subtype.val Q with hzQmdef
  haveI : QuasiCompact zQm := hQC
  haveI : IsClosedImmersion zQm := hICI
  have h5 := torsionSplittingEval_self_eq_one (W := W)
    (hsm := (modelEllipticCurve W).smooth) (N := N) (hNZ := hNZ) (hN0 := hN0)
    (Q := Q) (hQ := hQ) (M := M) (hM := hM) (Wc := Wc) (hWc := hWc) (e := e)
    (hnorm := hnorm) (h := h) (hn := hn) (hsplit := hsplit) (c₀ := c₀)
    (p := p) (hxp := hxp) (hT := hT) (V := V) (f₁ := f₁) (f₂ := f₂) (ch := ch)
    (A := A) (zQm := zQm)
    (hzQm := show zQm ≫
      pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) =
      𝟙 (Spec (CommRingCat.of K)) from Q.2)
    (hzQfst := rfl) (hspan₁ := hspan₁) (hnzd₁ := hnzd₁) (hspan₂ := hspan₂)
    (hnzd₂ := hnzd₂) (hWch := hWch) (hu := fun i j hne => hu i j hWch hne)
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).injective
    (h5.trans (map_one _).symm)

end EllipticCurve

end ModularCurves
