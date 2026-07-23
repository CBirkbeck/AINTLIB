import ModularCurves.ModularCurve.YRho

/-!
# [T-EQ-3c-PIN] The pairing-side bridge: value-level symplectic condition ⟹
morphism-level pairing identity

The symplectically framed quotient carves its values by the single map-level
condition `pairEZMap = frameDetMap` (the Weil pairing of the *level pair* against
the determinant read of the frame). The `ρ`-level dictionary
(`rhoLevelStructureOfFramed`) needs the all-pairs `W`-quantified identity
`torsionPairEval = coordPairLift ≫ vRhoPairingMap` (`hsymp_scheme`). This module
proves the bridge:

* `pairEZMap` *is* `torsionPairEval` at the identity test (`pairEZMap_eq_torsionPairEval`);
* every morphism into the roots scheme is determined by its `Γ`-read
  (`muNRoots_hom_ext`, already landed), and the read of `torsionPairEval` is the
  Weil-pairing evaluation (`torsionPairEval_read`);
* the all-pairs identity reduces to the universal pair over the torsion fibre
  square, which decomposes into clopen pieces indexed by `(ℤ/N)² × (ℤ/N)²`
  through the full level (`constFiberCofanIsColimit`), where the symplectic-formula
  register (`weilPairingEval_symplectic`) and the frame-determinant condition close
  each piece.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ModularCurves

noncomputable section

variable {N : ℕ} [NeZero N]

/-- **[PIN-1]** The value-level pairing comparison is the scheme-level Weil-pairing
read at the identity test map. -/
theorem pairEZMap_eq_torsionPairEval (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (P Q : E.Section) (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    pairEZMap D sT E P Q hP hQ =
      torsionPairEval D sT (𝟙 T) P Q
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ) := rfl

/-- **[PIN-1]** The scheme-level Weil-pairing read lies over the base. -/
theorem torsionPairEval_π (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    torsionPairEval D sT t x y hx hy ≫ muNRootsSchemeπ D = t ≫ sT := by
  rw [torsionPairEval]
  simp only [Category.assoc]
  rw [muNSpecQIso_π, muNMapAlong_π, reassoc_of% (E.weilPairing_over N),
    pullback.lift_fst_assoc, ← Category.assoc, E.pointToTorsion_torsionπ]

/-- **[PIN-1]** The `Γ`-read of the scheme-level Weil-pairing read is the
Weil-pairing evaluation (the generic-test form of `pairEZMap_read`). -/
theorem torsionPairEval_read (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    muNRootsRead D (t ≫ sT) (torsionPairEval D sT t x y hx hy)
      (torsionPairEval_π D sT t x y hx hy) =
    (E.weilPairingEval x y hx hy).1 := by
  have hover : (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
      (by simp) ≫ E.weilPairing N) ≫ muNπ T N = t := by
    rw [Category.assoc, E.weilPairing_over N, ← Category.assoc,
      pullback.lift_fst, E.pointToTorsion_torsionπ]
  have hcancel : torsionPairEval D sT t x y hx hy ≫ (muNSpecQIso D).inv =
      (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
        (by simp) ≫ E.weilPairing N) ≫ muNMapAlong sT N := by
    rw [torsionPairEval]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id, Category.comp_id]
  have hsub : (⟨torsionPairEval D sT t x y hx hy ≫ (muNSpecQIso D).inv, by
        rw [Category.assoc, muNSpecQIso_π_inv, torsionPairEval_π]⟩ :
      { m : W ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N = t ≫ sT }) =
      ⟨(pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
          (by simp) ≫ E.weilPairing N) ≫ muNMapAlong sT N, by
        rw [Category.assoc, muNMapAlong_π, ← Category.assoc, hover]⟩ :=
    Subtype.ext hcancel
  show (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N (t ≫ sT)
      ⟨torsionPairEval D sT t x y hx hy ≫ (muNSpecQIso D).inv, by
        rw [Category.assoc, muNSpecQIso_π_inv, torsionPairEval_π]⟩ : Γ(W, ⊤)) = _
  refine Eq.trans (congrArg
    (fun v : { m : W ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N = t ≫ sT } =>
      (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N (t ≫ sT) v : Γ(W, ⊤))) hsub) ?_
  exact muNPointsEquiv_mapAlong sT N t
    ⟨pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
      (by simp) ≫ E.weilPairing N, hover⟩

/-- **[PIN-2]** The `V_ρ`-leg of a `ρ`-trivialization is compatible with the
structure maps. -/
theorem torsionLeg_vRhoπ (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N) :
    (torsionIso.hom ≫ pullback.fst (vRhoπ D) sT) ≫ vRhoπ D =
      E.torsionπ N ≫ sT := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hOver]

/-- **[PIN-2]** The coordinate-pair read factors through the pair square map. -/
theorem coordPairLift_eq_lift_map (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    coordPairLift D sT torsionIso hOver t x y hx hy =
      pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
        pullback.map (E.torsionπ N) (E.torsionπ N) (vRhoπ D) (vRhoπ D)
          (torsionIso.hom ≫ pullback.fst (vRhoπ D) sT)
          (torsionIso.hom ≫ pullback.fst (vRhoπ D) sT) sT
          (torsionLeg_vRhoπ D sT torsionIso hOver).symm
          (torsionLeg_vRhoπ D sT torsionIso hOver).symm := by
  apply pullback.hom_ext
  · show pullback.lift _ _ _ ≫ pullback.fst (vRhoπ D) (vRhoπ D) =
      (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) _ ≫
        pullback.map _ _ _ _ _ _ _ _ _) ≫ pullback.fst (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_fst, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, ← Category.assoc]
  · show pullback.lift _ _ _ ≫ pullback.snd (vRhoπ D) (vRhoπ D) =
      (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) _ ≫
        pullback.map _ _ _ _ _ _ _ _ _) ≫ pullback.snd (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_snd, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, ← Category.assoc]

/-- **[PIN-2]** The universal-pair reduction: the all-pairs morphism-level pairing
identity follows from its instance at the tautological pair over the torsion fibre
square (stated as an identity of maps out of the square). -/
theorem pairing_scheme_of_universal (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    (huniv : E.weilPairing N ≫ muNMapAlong sT N ≫ (muNSpecQIso D).hom =
      pullback.map (E.torsionπ N) (E.torsionπ N) (vRhoπ D) (vRhoπ D)
        (torsionIso.hom ≫ pullback.fst (vRhoπ D) sT)
        (torsionIso.hom ≫ pullback.fst (vRhoπ D) sT) sT
        (torsionLeg_vRhoπ D sT torsionIso hOver).symm
        (torsionLeg_vRhoπ D sT torsionIso hOver).symm ≫ vRhoPairingMap D)
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    torsionPairEval D sT t x y hx hy =
      coordPairLift D sT torsionIso hOver t x y hx hy ≫ vRhoPairingMap D := by
  rw [torsionPairEval, huniv, coordPairLift_eq_lift_map D sT torsionIso hOver]
  simp only [Category.assoc]

/-- **[PIN-3]** The `ℤ`-combination of a full level pair is killed by `N`. -/
theorem levelComb_kill {T : Scheme.{0}} {E : EllipticCurve T}
    (L : E.FullLevelPt N) (v : Fin 2 → ZMod N) :
    (N : ℤ) • (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2) = 0 := by
  rw [smul_add, smul_comm (N : ℤ) ((v 0).val : ℤ),
    smul_comm (N : ℤ) ((v 1).val : ℤ), L.2.1.1, L.2.1.2, smul_zero, smul_zero,
    add_zero]

/-- **[PIN-3]** The `(v, w)`-component of the torsion pair square: the pair of the
`v`- and `w`-combinations of the level. -/
noncomputable def levelPairLift {T : Scheme.{0}} {E : EllipticCurve T}
    (L : E.FullLevelPt N) (v w : Fin 2 → ZMod N) :
    T ⟶ pullback (E.torsionπ N) (E.torsionπ N) :=
  pullback.lift
    (E.pointToTorsion (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
      ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v)))
    (E.pointToTorsion (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
      ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)))
    (by simp)

/-- **[PIN-3]** The full-level trivialization carries the structure map to the
constant projection (inverse form). -/
theorem fullLevelIso_inv_constSchemeπ {T : Scheme.{0}} {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N) :
    (E.fullLevelIso hinv L).inv ≫ constSchemeπ T (Fin 2 → ZMod N) =
      E.torsionπ N := by
  rw [Iso.inv_comp_eq]
  exact (E.fullLevelHom_torsionπ L).symm

/-- **[PIN-3]** Maps out of the torsion pair square agree as soon as they agree
against every pair of level combinations: the square decomposes into clopen pieces
indexed by the pair of level reads, and on each piece the tautological pair is the
corresponding combination pair. -/
theorem torsionPairSquare_hom_ext {T : Scheme.{0}} {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N) {Y : Scheme.{0}}
    {F G : pullback (E.torsionπ N) (E.torsionπ N) ⟶ Y}
    (h : ∀ v w : Fin 2 → ZMod N,
      levelPairLift L v w ≫ F = levelPairLift L v w ≫ G) :
    F = G := by
  have hπx : (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫
      (E.fullLevelIso hinv L).inv) ≫ constSchemeπ T (Fin 2 → ZMod N) =
      pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N := by
    rw [Category.assoc, fullLevelIso_inv_constSchemeπ]
  have hπy : (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫
      (E.fullLevelIso hinv L).inv) ≫ constSchemeπ T (Fin 2 → ZMod N) =
      pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N := by
    rw [Category.assoc, fullLevelIso_inv_constSchemeπ]
  let c₀ : LocallyConstant
      (pullback (E.torsionπ N) (E.torsionπ N) : Scheme.{0})
      ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) :=
    ⟨fun p => (constSchemePointsEquiv T (Fin 2 → ZMod N)
        (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
        ⟨pullback.fst (E.torsionπ N) (E.torsionπ N) ≫
          (E.fullLevelIso hinv L).inv, hπx⟩ p,
      constSchemePointsEquiv T (Fin 2 → ZMod N)
        (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
        ⟨pullback.snd (E.torsionπ N) (E.torsionπ N) ≫
          (E.fullLevelIso hinv L).inv, hπy⟩ p),
      IsLocallyConstant.prodMk
        (constSchemePointsEquiv T (Fin 2 → ZMod N)
          (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
          ⟨pullback.fst (E.torsionπ N) (E.torsionπ N) ≫
            (E.fullLevelIso hinv L).inv, hπx⟩).isLocallyConstant
        (constSchemePointsEquiv T (Fin 2 → ZMod N)
          (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
          ⟨pullback.snd (E.torsionπ N) (E.torsionπ N) ≫
            (E.fullLevelIso hinv L).inv, hπy⟩).isLocallyConstant⟩
  refine locConst_hom_ext c₀ fun vw => ?_
  obtain ⟨v, w⟩ := vw
  have hfacx := constMap_factor_of_le
    (h := pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ (E.fullLevelIso hinv L).inv)
    hπx v (U := locConstPiece c₀ (v, w))
    (fun t ht => congrArg Prod.fst (mem_locConstPiece.mp ht))
  have hfacy := constMap_factor_of_le
    (h := pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ (E.fullLevelIso hinv L).inv)
    hπy w (U := locConstPiece c₀ (v, w))
    (fun t ht => congrArg Prod.snd (mem_locConstPiece.mp ht))
  have hhom : (E.fullLevelIso hinv L).hom = E.fullLevelHom L := rfl
  have hx : (locConstPiece c₀ (v, w)).ι ≫
      pullback.fst (E.torsionπ N) (E.torsionπ N) =
      ((locConstPiece c₀ (v, w)).ι ≫
        pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) ≫
        E.pointToTorsion (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v)) := by
    have h1 : (locConstPiece c₀ (v, w)).ι ≫
        pullback.fst (E.torsionπ N) (E.torsionπ N) =
        ((locConstPiece c₀ (v, w)).ι ≫
          (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫
            (E.fullLevelIso hinv L).inv)) ≫ (E.fullLevelIso hinv L).hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h1, hfacx, Category.assoc, hhom]
    rw [show Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) v ≫ E.fullLevelHom L =
      E.pointToTorsion (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
      from Sigma.ι_desc _ _]
  have hy : (locConstPiece c₀ (v, w)).ι ≫
      pullback.snd (E.torsionπ N) (E.torsionπ N) =
      ((locConstPiece c₀ (v, w)).ι ≫
        pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) ≫
        E.pointToTorsion (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)) := by
    have h1 : (locConstPiece c₀ (v, w)).ι ≫
        pullback.snd (E.torsionπ N) (E.torsionπ N) =
        ((locConstPiece c₀ (v, w)).ι ≫
          (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫
            (E.fullLevelIso hinv L).inv)) ≫ (E.fullLevelIso hinv L).hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h1, hfacy, Category.assoc, hhom]
    rw [show Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) w ≫ E.fullLevelHom L =
      E.pointToTorsion (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w))
      from Sigma.ι_desc _ _]
    rw [← Category.assoc, ← Category.assoc]
    refine congrArg (· ≫ E.pointToTorsion _ _) ?_
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hι : (locConstPiece c₀ (v, w)).ι =
      ((locConstPiece c₀ (v, w)).ι ≫
        pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) ≫
        levelPairLift L v w := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      rw [show levelPairLift L v w ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) =
        E.pointToTorsion (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
        from pullback.lift_fst _ _ _]
      exact hx
    · rw [Category.assoc]
      rw [show levelPairLift L v w ≫ pullback.snd (E.torsionπ N) (E.torsionπ N) =
        E.pointToTorsion (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w))
        from pullback.lift_snd _ _ _]
      exact hy
  rw [hι, Category.assoc, Category.assoc, h v w]
  simp only [Category.assoc]

/-- **[PIN-4]** The full reduction: the all-pairs morphism-level pairing identity
follows from its finitely many instances at the level-combination pairs (universal
pair + clopen decomposition). -/
theorem pairing_scheme_of_combPairs (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (hcomb : ∀ v w : Fin 2 → ZMod N,
      torsionPairEval D sT (𝟙 T)
          (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
          (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)) =
        coordPairLift D sT torsionIso hOver (𝟙 T)
          (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
          (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)) ≫
          vRhoPairingMap D)
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    torsionPairEval D sT t x y hx hy =
      coordPairLift D sT torsionIso hOver t x y hx hy ≫ vRhoPairingMap D := by
  refine pairing_scheme_of_universal D sT torsionIso hOver ?_ t x y hx hy
  refine torsionPairSquare_hom_ext hinv L fun v w => ?_
  refine Eq.trans
    (show levelPairLift L v w ≫ E.weilPairing N ≫ muNMapAlong sT N ≫
        (muNSpecQIso D).hom =
      torsionPairEval D sT (𝟙 T)
        (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
        (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w))
      from rfl) (Eq.trans (hcomb v w) ?_)
  rw [coordPairLift_eq_lift_map D sT torsionIso hOver]
  simp only [Category.assoc]
  rfl

/-- **[PIN-5]** The roots-scheme read is natural under precomposition. -/
theorem muNRootsRead_comp (D : GaloisRepData N) [Fact (1 < N)]
    {W W' : Scheme.{0}} (u : W' ⟶ W) {b : W ⟶ Spec (CommRingCat.of ℚ)}
    (φ : W ⟶ muNRootsScheme D) (hφ : φ ≫ muNRootsSchemeπ D = b) :
    muNRootsRead D (u ≫ b) (u ≫ φ) (by rw [Category.assoc, hφ]) =
      (Scheme.Γ.map u.op).hom (muNRootsRead D b φ hφ) := by
  show (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N (u ≫ b)
      ⟨(u ≫ φ) ≫ (muNSpecQIso D).inv, by
        rw [Category.assoc, muNSpecQIso_π_inv, Category.assoc, hφ]⟩ :
      Γ(W', ⊤)) = _
  have hsub : (⟨(u ≫ φ) ≫ (muNSpecQIso D).inv, by
        rw [Category.assoc, muNSpecQIso_π_inv, Category.assoc, hφ]⟩ :
      { m : W' ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N = u ≫ b }) =
      ⟨u ≫ (φ ≫ (muNSpecQIso D).inv), by
        rw [Category.assoc, Category.assoc, muNSpecQIso_π_inv, hφ]⟩ :=
    Subtype.ext (Category.assoc u φ (muNSpecQIso D).inv)
  refine Eq.trans (congrArg
    (fun v : { m : W' ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N = u ≫ b } =>
      (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N (u ≫ b) v : Γ(W', ⊤))) hsub) ?_
  exact muNPointsEquiv_natural (Spec (CommRingCat.of ℚ)) N b u
    ⟨φ ≫ (muNSpecQIso D).inv, by
      rw [Category.assoc, muNSpecQIso_π_inv, hφ]⟩

/-- **[PIN-5]** The scheme-level Weil read at a level-combination pair is the
level-pair comparison powered by the symplectic exponent (map-level symplectic
formula, from the DS4 register through the `Γ`-read dictionary). -/
theorem torsionPairEval_comb (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (L : E.FullLevelPt N) (v w : Fin 2 → ZMod N) :
    torsionPairEval D sT (𝟙 T)
        (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
        (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)) =
      pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 ≫ muNRootsPowScheme D
        (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
          ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat) := by
  refine muNRoots_hom_ext D
    (torsionPairEval_π D sT (𝟙 T) _ _ _ _)
    (by
      rw [Category.assoc, muNRootsPowScheme_π, pairEZMap_π, Category.id_comp])
    ?_
  refine Eq.trans (torsionPairEval_read D sT (𝟙 T) _ _ _ _) ?_
  refine Eq.trans (E.weilPairingEval_symplectic L.1.1 L.1.2
    ((v 0).val : ℤ) ((v 1).val : ℤ) ((w 0).val : ℤ) ((w 1).val : ℤ)
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp L.2.1.1)
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp L.2.1.2)
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w))) ?_
  refine Eq.trans ?_ (muNRootsRead_pow D (𝟙 T ≫ sT)
    (pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2)
    (by rw [pairEZMap_π, Category.id_comp])
    (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
      ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)).symm
  refine congrArg (· ^ (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
    ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)) ?_
  refine Eq.trans ?_ (muNRootsRead_congr D (Category.id_comp sT)
    (rfl : pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 = _)
    (by rw [pairEZMap_π, Category.id_comp])).symm
  exact (pairEZMap_read_self D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2).symm

/-- **[PIN-7, layered]** The morphism-level pairing identity of the pinned framed
trivialization, from the value-level symplectic condition and the frame-side core
identity (`hcore`, the `(v,w)`-component computation of the pinned coordinate pair
against the pairing map — [PIN-6]). -/
theorem framedPinned_pairing_scheme_of_core (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (hcond : pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 = frameDetMap D h)
    (hcore : ∀ v w : Fin 2 → ZMod N,
      coordPairLift D sT (framedTorsionIsoPinned D sT E hinv L h hover)
          (framedTorsionIsoPinned_π D sT E hinv L h hover) (𝟙 T)
          (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
          (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)) ≫
          vRhoPairingMap D =
        frameDetMap D h ≫ muNRootsPowScheme D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat))
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    torsionPairEval D sT t x y hx hy =
      coordPairLift D sT (framedTorsionIsoPinned D sT E hinv L h hover)
        (framedTorsionIsoPinned_π D sT E hinv L h hover) t x y hx hy ≫
        vRhoPairingMap D := by
  refine pairing_scheme_of_combPairs D sT
    (framedTorsionIsoPinned D sT E hinv L h hover)
    (framedTorsionIsoPinned_π D sT E hinv L h hover) hinv L
    (fun v w => ?_) t x y hx hy
  refine Eq.trans (torsionPairEval_comb D sT L v w) ?_
  refine Eq.trans (congrArg (· ≫ muNRootsPowScheme D _) hcond) ?_
  exact (hcore v w).symm

/-- **[PIN-6a]** The corrected `v`-component point of the constant vector scheme
over `ℚ` (component inclusion, read through the correspondence identification and
the read-correction). -/
noncomputable def constVecCorrPt (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    Spec (CommRingCat.of ℚ) ⟶ constVecScheme N :=
  Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) v ≫
    (constVecSchemeIso N).hom ≫ (corrSchemeIso N).hom

theorem constVecCorrPt_π (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    constVecCorrPt N v ≫ constVecSchemeπ N = 𝟙 (Spec (CommRingCat.of ℚ)) := by
  rw [constVecCorrPt]
  simp only [Category.assoc]
  refine Eq.trans (congrArg (fun m : constVecScheme N ⟶ Spec (CommRingCat.of ℚ) =>
    Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) v ≫
      ((constVecSchemeIso N).hom ≫ m)) (corrSchemeIso_π N)) ?_
  refine Eq.trans (congrArg (fun m : constScheme (Spec (CommRingCat.of ℚ))
      (Fin 2 → ZMod N) ⟶ Spec (CommRingCat.of ℚ) =>
    Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) v ≫ m)
    (constVecSchemeIso_π N)) ?_
  rw [show constSchemeπ (Spec (CommRingCat.of ℚ)) (Fin 2 → ZMod N) =
    Limits.Sigma.desc (fun _ => 𝟙 (Spec (CommRingCat.of ℚ))) from rfl,
    Limits.Sigma.ι_desc]

/-- **[PIN-6a]** The absolute `v`-slot evaluation of the universal frame: pair the
corrected `v`-component with the tautological frame and evaluate. -/
noncomputable def frameSlotEval (D : GaloisRepData N) (v : Fin 2 → ZMod N) :
    wFrames D ⟶ vRho D :=
  pullback.lift (wFramesπ D ≫ constVecCorrPt N v) (𝟙 (wFrames D)) (by
    rw [Category.assoc, constVecCorrPt_π, Category.comp_id, Category.id_comp]) ≫
    frameEval D

/-- **[PIN-6a]** The pinned framed leg at a level combination is the absolute
slot evaluation precomposed with the frame classifier. -/
theorem framedPinned_leg_comb (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) (v : Fin 2 → ZMod N) :
    E.pointToTorsion (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v)) ≫
      (framedTorsionIsoPinned D sT E hinv L h hover).hom ≫
      pullback.fst (vRhoπ D) sT =
    h ≫ frameSlotEval D v := by
  letI := frameEvalSlice_isIso D sT h hover
  have hstep1 : Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) v ≫ E.fullLevelHom L =
      E.pointToTorsion
        (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v)) := by
    rw [EllipticCurve.fullLevelHom]
    exact Sigma.ι_desc _ _
  rw [← hstep1]
  rw [show (framedTorsionIsoPinned D sT E hinv L h hover).hom =
    (E.fullLevelIso hinv L).inv ≫
      ((isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
      (pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
      (pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) ≫
      frameEvalSlice D sT h hover))) from rfl]
  rw [show E.fullLevelHom L = (E.fullLevelIso hinv L).hom from rfl]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc]
  have hkey : Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) v ≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
      pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
      pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) ≫
      pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ h)
        (by rw [Category.assoc, hover, ← pullback.condition]) =
      h ≫ pullback.lift (wFramesπ D ≫ constVecCorrPt N v) (𝟙 (wFrames D)) (by
        rw [Category.assoc, constVecCorrPt_π, Category.comp_id,
          Category.id_comp]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc]
      rw [IsPullback.isoPullback_hom_snd_assoc, ι_constSchemeMapAlong_assoc,
        constVecCorrPt, reassoc_of% hover]
      exact rfl
    · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd,
        Category.comp_id]
      rw [← Category.assoc _ _ h,
        IsPullback.isoPullback_hom_fst]
      rw [show constSchemeπ T (Fin 2 → ZMod N) =
        Limits.Sigma.desc (fun _ => 𝟙 T) from rfl]
      rw [← Category.assoc, Limits.Sigma.ι_desc, Category.id_comp]
  rw [frameEvalSlice_fst]
  rw [show pullback.lift (pullback.snd sT (constVecSchemeπ N))
      (pullback.fst sT (constVecSchemeπ N) ≫ h)
      (by rw [Category.assoc, hover, ← pullback.condition]) ≫ frameEval D =
    pullback.lift (pullback.snd sT (constVecSchemeπ N))
      (pullback.fst sT (constVecSchemeπ N) ≫ h)
      (by rw [Category.assoc, hover, ← pullback.condition]) ≫ frameEval D
    from rfl]
  rw [reassoc_of% hkey]
  rw [frameSlotEval]

theorem frameSlotEval_π (D : GaloisRepData N) (v : Fin 2 → ZMod N) :
    frameSlotEval D v ≫ vRhoπ D = wFramesπ D := by
  rw [frameSlotEval, Category.assoc, frameEval_π, ← Category.assoc,
    pullback.lift_fst, Category.assoc, constVecCorrPt_π, Category.comp_id]

/-- **[PIN-6b]** The pinned coordinate pair at a combination pair is the frame
classifier followed by the absolute slot-evaluation pair. -/
theorem coordPairLift_comb_framedPinned (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) (v w : Fin 2 → ZMod N) :
    coordPairLift D sT (framedTorsionIsoPinned D sT E hinv L h hover)
        (framedTorsionIsoPinned_π D sT E hinv L h hover) (𝟙 T)
        (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
        (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)) =
      h ≫ pullback.lift (frameSlotEval D v) (frameSlotEval D w)
        ((frameSlotEval_π D v).trans (frameSlotEval_π D w).symm) := by
  apply pullback.hom_ext
  · show pullback.lift _ _ _ ≫ pullback.fst (vRhoπ D) (vRhoπ D) =
      (h ≫ pullback.lift _ _ _) ≫ pullback.fst (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    exact framedPinned_leg_comb D sT hinv L h hover v
  · show pullback.lift _ _ _ ≫ pullback.snd (vRhoπ D) (vRhoπ D) =
      (h ≫ pullback.lift _ _ _) ≫ pullback.snd (vRhoπ D) (vRhoπ D)
    rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
    exact framedPinned_leg_comb D sT hinv L h hover w

/-- **[PIN-6, layered]** The frame-side core identity of the pinned trivialization
follows from the ABSOLUTE pairing-determinant identity on the universal frame
(`habs`, [PIN-6c] — no base, level, or classifier in sight). -/
theorem framedPinned_hcore_of_abs (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (habs : ∀ v w : Fin 2 → ZMod N,
      pullback.lift (frameSlotEval D v) (frameSlotEval D w)
          ((frameSlotEval_π D v).trans (frameSlotEval_π D w).symm) ≫
          vRhoPairingMap D =
        detFrameScheme D ≫ detCompScheme D ≫ muNRootsPowScheme D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat))
    (v w : Fin 2 → ZMod N) :
    coordPairLift D sT (framedTorsionIsoPinned D sT E hinv L h hover)
        (framedTorsionIsoPinned_π D sT E hinv L h hover) (𝟙 T)
        (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
        (((w 0).val : ℤ) • L.1.1 + ((w 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L v))
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp (levelComb_kill L w)) ≫
        vRhoPairingMap D =
      frameDetMap D h ≫ muNRootsPowScheme D
        (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
          ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat) := by
  rw [coordPairLift_comb_framedPinned D sT hinv L h hover v w]
  rw [Category.assoc, habs v w, frameDetMap]
  simp only [Category.assoc]

open TensorProduct in
/-- **[PIN-6c]** A pair of `Spec`-maps into a `Spec`-fibre square is the `Spec`-map
of the tensor product map. -/
theorem lift_pullbackSpecIso_hom (R A B C : Type) [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    pullback.lift (Spec.map (CommRingCat.ofHom f.toRingHom))
        (Spec.map (CommRingCat.ofHom g.toRingHom)) h ≫
      (AlgebraicGeometry.pullbackSpecIso R A B).hom =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap f g).toRingHom) := by
  rw [← Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc,
      AlgebraicGeometry.pullbackSpecIso_inv_fst, ← AlgebraicGeometry.Spec.map_comp]
    refine congrArg AlgebraicGeometry.Spec.map ?_
    ext a
    show f a = (Algebra.TensorProduct.productMap f g) (a ⊗ₜ[R] 1)
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  · rw [pullback.lift_snd, Category.assoc,
      AlgebraicGeometry.pullbackSpecIso_inv_snd, ← AlgebraicGeometry.Spec.map_comp]
    refine congrArg AlgebraicGeometry.Spec.map ?_
    ext b
    show g b = (Algebra.TensorProduct.productMap f g) (1 ⊗ₜ[R] b)
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]

/-- **[PIN-6c-i]** The corrected component point, ring side. -/
noncomputable def constVecCorrPtRing (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    CommRingCat.of (constVecAlgebra N : Type 0) ⟶ CommRingCat.of ℚ :=
  CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom ≫
    CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom ≫
    CommRingCat.ofHom (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => ℚ) v)

/-- **[PIN-6c-i]** The corrected component point is the `Spec` of its ring side. -/
theorem constVecCorrPt_eq_Spec (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    constVecCorrPt N v = Spec.map (constVecCorrPtRing N v) := by
  rw [constVecCorrPt]
  rw [show (constVecSchemeIso N).hom =
    (constSchemeSpecIso (CommRingCat.of ℚ) (Fin 2 → ZMod N)).hom ≫
      (constVecSpecIso N).hom from rfl]
  simp only [Category.assoc]
  rw [constSchemeSpecIso_ι_hom_assoc]
  rw [show (constVecSpecIso N).hom = Spec.map (CommRingCat.ofHom
    (constVecAlgebraIso N).hom.hom.hom.toRingHom) from rfl]
  rw [show (corrSchemeIso N).hom = Spec.map (CommRingCat.ofHom
    (corrAlgHom N).hom.hom.toRingHom) from rfl]
  refine Eq.trans (congrArg (fun m => Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => ℚ) v)) ≫ m)
    (AlgebraicGeometry.Spec.map_comp
      (CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom)
      (CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom)).symm) ?_
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp
    (CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom ≫
      CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom)
    (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => ℚ) v))).symm ?_
  rfl

/-- **[PIN-6c-ii]** The corrected component point, algebra side. -/
noncomputable def constVecCorrPtAlg (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    (constVecAlgebra N : Type 0) →ₐ[ℚ] ℚ :=
  (Pi.evalAlgHom ℚ (fun _ : (Fin 2 → ZMod N) => ℚ) v).comp
    ((constVecAlgebraIso N).hom.hom.hom.comp (corrAlgHom N).hom.hom)

theorem constVecCorrPtRing_eq_alg (N : ℕ) [NeZero N] (v : Fin 2 → ZMod N) :
    constVecCorrPtRing N v =
      CommRingCat.ofHom (constVecCorrPtAlg N v).toRingHom := rfl

/-- **[PIN-6c-ii]** The absolute slot evaluation, ring side. -/
noncomputable def frameSlotRing (D : GaloisRepData N) [Fact (1 < N)]
    (v : Fin 2 → ZMod N) :
    CommRingCat.of (vRhoAlgebra D : Type 0) ⟶
      CommRingCat.of ((wFramesAlgebra D : Type 0)) :=
  CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom ≫
    CommRingCat.ofHom (Algebra.TensorProduct.productMap
      ((Algebra.ofId ℚ (wFramesAlgebra D : Type 0)).comp (constVecCorrPtAlg N v))
      (AlgHom.id ℚ (wFramesAlgebra D : Type 0))).toRingHom

/-- **[PIN-6c-ii]** The absolute slot evaluation is the `Spec` of its ring side. -/
theorem frameSlotEval_eq_Spec (D : GaloisRepData N) [Fact (1 < N)]
    (v : Fin 2 → ZMod N) :
    frameSlotEval D v = Spec.map (frameSlotRing D v) := by
  have hlift : pullback.lift (wFramesπ D ≫ constVecCorrPt N v) (𝟙 (wFrames D))
      (by rw [Category.assoc, constVecCorrPt_π, Category.comp_id,
        Category.id_comp]) =
      pullback.lift
        (Spec.map (CommRingCat.ofHom ((Algebra.ofId ℚ
            (wFramesAlgebra D : Type 0)).comp
          (constVecCorrPtAlg N v)).toRingHom))
        (Spec.map (CommRingCat.ofHom
          (AlgHom.id ℚ (wFramesAlgebra D : Type 0)).toRingHom))
        (by
          rw [show CommRingCat.ofHom
              (AlgHom.id ℚ (wFramesAlgebra D : Type 0)).toRingHom =
            𝟙 (CommRingCat.of (wFramesAlgebra D : Type 0)) from rfl,
            AlgebraicGeometry.Spec.map_id, Category.id_comp]
          refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
          exact congrArg AlgebraicGeometry.Spec.map (by
            ext r
            exact ((Algebra.ofId ℚ (wFramesAlgebra D : Type 0)).comp
              (constVecCorrPtAlg N v)).commutes r)) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      rw [constVecCorrPt_eq_Spec]
      refine Eq.trans (AlgebraicGeometry.Spec.map_comp (constVecCorrPtRing N v)
        (CommRingCat.ofHom (algebraMap ℚ (wFramesAlgebra D : Type 0)))).symm ?_
      exact congrArg AlgebraicGeometry.Spec.map rfl
    · rw [pullback.lift_snd]
      refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      rw [show CommRingCat.ofHom (AlgHom.id ℚ
          (wFramesAlgebra D : Type 0)).toRingHom =
        𝟙 (CommRingCat.of (wFramesAlgebra D : Type 0)) from rfl,
        AlgebraicGeometry.Spec.map_id]
      exact rfl
  rw [frameSlotEval, hlift]
  rw [show frameEval D = (AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
    Spec.map (CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom)
    from rfl]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (frameEvalAlgHom D).hom.hom.toRingHom))
    (lift_pullbackSpecIso_hom ℚ (constVecAlgebra N : Type 0)
      (wFramesAlgebra D : Type 0) (wFramesAlgebra D : Type 0)
      ((Algebra.ofId ℚ (wFramesAlgebra D : Type 0)).comp (constVecCorrPtAlg N v))
      (AlgHom.id ℚ (wFramesAlgebra D : Type 0)) _)) ?_
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
  rfl

/-- **[PIN-6c-iii]** The absolute slot evaluation, algebra side. -/
noncomputable def frameSlotAlg (D : GaloisRepData N) [Fact (1 < N)]
    (v : Fin 2 → ZMod N) :
    (vRhoAlgebra D : Type 0) →ₐ[ℚ] (wFramesAlgebra D : Type 0) :=
  (Algebra.TensorProduct.productMap
      ((Algebra.ofId ℚ (wFramesAlgebra D : Type 0)).comp (constVecCorrPtAlg N v))
      (AlgHom.id ℚ (wFramesAlgebra D : Type 0))).comp
    (frameEvalAlgHom D).hom.hom

theorem frameSlotRing_eq_alg (D : GaloisRepData N) [Fact (1 < N)]
    (v : Fin 2 → ZMod N) :
    frameSlotRing D v = CommRingCat.ofHom (frameSlotAlg D v).toRingHom := rfl

/-- **[PIN-6c-iii]** The paired slot evaluation against the pairing map is a single
`Spec` map. -/
theorem pairSlot_vRhoPairingMap_eq_Spec (D : GaloisRepData N) [Fact (1 < N)]
    (v w : Fin 2 → ZMod N) :
    pullback.lift (frameSlotEval D v) (frameSlotEval D w)
        ((frameSlotEval_π D v).trans (frameSlotEval_π D w).symm) ≫
      vRhoPairingMap D =
    Spec.map (CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom (vRhoPairTensorIso D).hom.hom.hom.toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.productMap (frameSlotAlg D v)
        (frameSlotAlg D w)).toRingHom) := by
  have hlift : pullback.lift (frameSlotEval D v) (frameSlotEval D w)
      ((frameSlotEval_π D v).trans (frameSlotEval_π D w).symm) =
      pullback.lift
        (Spec.map (CommRingCat.ofHom (frameSlotAlg D v).toRingHom))
        (Spec.map (CommRingCat.ofHom (frameSlotAlg D w).toRingHom))
        (by
          rw [← frameSlotRing_eq_alg, ← frameSlotRing_eq_alg,
            ← frameSlotEval_eq_Spec, ← frameSlotEval_eq_Spec]
          exact (frameSlotEval_π D v).trans (frameSlotEval_π D w).symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      exact (frameSlotEval_eq_Spec D v).trans
        (congrArg Spec.map (frameSlotRing_eq_alg D v))
    · rw [pullback.lift_snd]
      refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      exact (frameSlotEval_eq_Spec D w).trans
        (congrArg Spec.map (frameSlotRing_eq_alg D w))
  rw [hlift]
  rw [show vRhoPairingMap D = ((AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (vRhoAlgebra D : Type 0)).hom ≫
    Spec.map (CommRingCat.ofHom (vRhoPairTensorIso D).hom.hom.hom.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom) from rfl]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (rhoPairAlgHom D).hom.hom.toRingHom)) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun m => (m ≫ Spec.map (CommRingCat.ofHom
      (vRhoPairTensorIso D).hom.hom.hom.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom))
    (lift_pullbackSpecIso_hom ℚ (vRhoAlgebra D : Type 0)
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)
      (frameSlotAlg D v) (frameSlotAlg D w) _)) ?_
  refine Eq.trans (congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (rhoPairAlgHom D).hom.hom.toRingHom))
    (AlgebraicGeometry.Spec.map_comp _ _).symm) ?_
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
  rfl

/-- **[PIN-6c-iv]** The determinant-power composite is a single `Spec` map. -/
theorem detPow_eq_Spec (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    detFrameScheme D ≫ detCompScheme D ≫ muNRootsPowScheme D k =
    Spec.map (CommRingCat.ofHom (muNRootsPowAlg D k).hom.hom.toRingHom ≫
      CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom) := by
  rw [show detFrameScheme D = Spec.map (CommRingCat.ofHom
    (detFrameAlgHom D).hom.hom.toRingHom) from rfl]
  rw [show detCompScheme D = Spec.map (CommRingCat.ofHom
    (detCompAlgHom D).hom.hom.toRingHom) from rfl]
  rw [show muNRootsPowScheme D k = Spec.map (CommRingCat.ofHom
    (muNRootsPowAlg D k).hom.hom.toRingHom) from rfl]
  refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom
      (detFrameAlgHom D).hom.hom.toRingHom) ≫ ·)
    (AlgebraicGeometry.Spec.map_comp
      (CommRingCat.ofHom (muNRootsPowAlg D k).hom.hom.toRingHom)
      (CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom)).symm) ?_
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp
    (CommRingCat.ofHom (muNRootsPowAlg D k).hom.hom.toRingHom ≫
      CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom)
    (CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom)).symm ?_
  rfl

/-- **[PIN-6c-iv, layered]** The absolute pairing-determinant identity follows from
its ring-side form. -/
theorem habs_of_ring (D : GaloisRepData N) [Fact (1 < N)]
    (hring : ∀ v w : Fin 2 → ZMod N,
      CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom ≫
        CommRingCat.ofHom (vRhoPairTensorIso D).hom.hom.hom.toRingHom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.productMap (frameSlotAlg D v)
          (frameSlotAlg D w)).toRingHom =
      CommRingCat.ofHom (muNRootsPowAlg D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)).hom.hom.toRingHom ≫
        CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom ≫
        CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom)
    (v w : Fin 2 → ZMod N) :
    pullback.lift (frameSlotEval D v) (frameSlotEval D w)
        ((frameSlotEval_π D v).trans (frameSlotEval_π D w).symm) ≫
      vRhoPairingMap D =
    detFrameScheme D ≫ detCompScheme D ≫ muNRootsPowScheme D
      (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
        ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat) := by
  rw [pairSlot_vRhoPairingMap_eq_Spec D v w, detPow_eq_Spec D]
  exact congrArg Spec.map (hring v w)

/-- **[PIN, stitched]** The morphism-level pairing identity of the pinned framed
trivialization, from the value-level symplectic condition and the ring-side
pairing-determinant identity. -/
theorem framedPinned_pairing_scheme_of_ring (D : GaloisRepData N) [Fact (1 < N)]
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ)) {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (hcond : pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 = frameDetMap D h)
    (hring : ∀ v w : Fin 2 → ZMod N,
      CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom ≫
        CommRingCat.ofHom (vRhoPairTensorIso D).hom.hom.hom.toRingHom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.productMap (frameSlotAlg D v)
          (frameSlotAlg D w)).toRingHom =
      CommRingCat.ofHom (muNRootsPowAlg D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)).hom.hom.toRingHom ≫
        CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom ≫
        CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom)
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    torsionPairEval D sT t x y hx hy =
      coordPairLift D sT (framedTorsionIsoPinned D sT E hinv L h hover)
        (framedTorsionIsoPinned_π D sT E hinv L h hover) t x y hx hy ≫
        vRhoPairingMap D :=
  framedPinned_pairing_scheme_of_core D sT hinv L h hover hcond
    (fun v w => framedPinned_hcore_of_abs D sT hinv L h hover
      (fun v' w' => habs_of_ring D hring v' w') v w) t x y hx hy

/-- **[PIN-6c-iv-γ]** The determinant-power ring composite is the correspondence
image of the composed set-level morphism. -/
theorem detPowRing_eq_inverse_map (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    CommRingCat.ofHom (muNRootsPowAlg D k).hom.hom.toRingHom ≫
      CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom =
    CommRingCat.ofHom (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (detFrameMor D ≫ detCompMor D ≫ muNRootsPowMor D k)).unop.hom.hom.toRingHom) := by
  have hsplit : (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (detFrameMor D ≫ detCompMor D ≫ muNRootsPowMor D k) =
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (detFrameMor D) ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (detCompMor D) ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (muNRootsPowMor D k) := by
    rw [Functor.map_comp, Functor.map_comp]
  rw [hsplit]
  rfl

/-- **[PIN-6c-iv-γ]** Finite étale algebra maps over `ℚ` are determined by their
`ℚ̄`-fiber maps (faithfulness of the Galois correspondence). -/
theorem finiteEtale_hom_ext_of_fiber
    {A B : (CommAlgCat.FiniteEtale.{0} ℚ)ᵒᵖ} {f g : A ⟶ B}
    (h : (CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ)).map f =
      (CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ)).map g) : f = g := by
  refine (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map_injective ?_
  ext x : 3
  show (ConcreteCategory.hom
      ((CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ)).map f)) x =
    (ConcreteCategory.hom
      ((CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ)).map g)) x
  rw [h]

/-- **[PIN-6c-iv-γ]** The paired-slot comparison as a finite étale algebra map. -/
noncomputable def pairSlotFE (D : GaloisRepData N) [Fact (1 < N)]
    (v w : Fin 2 → ZMod N) :
    FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (vRhoAlgebra D) ⟶
      wFramesAlgebra D :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    (Algebra.TensorProduct.productMap (frameSlotAlg D v) (frameSlotAlg D w)))

/-- **[PIN-6c-iv-γ, layered]** The ring identity follows from its finite-étale
form. -/
theorem hring_of_finiteEtale (D : GaloisRepData N) [Fact (1 < N)]
    (hFE : ∀ v w : Fin 2 → ZMod N,
      rhoPairAlgHom D ≫ (vRhoPairTensorIso D).hom ≫ pairSlotFE D v w =
      muNRootsPowAlg D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat) ≫
        detCompAlgHom D ≫ detFrameAlgHom D)
    (v w : Fin 2 → ZMod N) :
    CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom (vRhoPairTensorIso D).hom.hom.hom.toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.productMap (frameSlotAlg D v)
        (frameSlotAlg D w)).toRingHom =
    CommRingCat.ofHom (muNRootsPowAlg D
        (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
          ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)).hom.hom.toRingHom ≫
      CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom := by
  have h := hFE v w
  calc CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom ≫
        CommRingCat.ofHom (vRhoPairTensorIso D).hom.hom.hom.toRingHom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.productMap (frameSlotAlg D v)
          (frameSlotAlg D w)).toRingHom
      = CommRingCat.ofHom (rhoPairAlgHom D ≫ (vRhoPairTensorIso D).hom ≫
          pairSlotFE D v w).hom.hom.toRingHom := rfl
    _ = CommRingCat.ofHom (muNRootsPowAlg D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat) ≫
          detCompAlgHom D ≫ detFrameAlgHom D).hom.hom.toRingHom := by rw [h]
    _ = CommRingCat.ofHom (muNRootsPowAlg D
          (((((v 0).val : ℤ) * ((w 1).val : ℤ) -
            ((v 1).val : ℤ) * ((w 0).val : ℤ)) % (N : ℤ)).toNat)).hom.hom.toRingHom ≫
        CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom ≫
        CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom := rfl

open scoped FintypeCatDiscrete in
/-- **[PIN-6c-iv-γ]** First-leg compatibility of the pair correspondence. -/
theorem pairCorrespondenceIso_hom_fst (D : GaloisRepData N) [Fact (1 < N)] :
    (pairCorrespondenceIso D).hom ≫ rhoPairFst D =
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
            (vRhoAlgebra D : Type 0) →ₐ[ℚ]
              TensorProduct ℚ (vRhoAlgebra D : Type 0) (vRhoAlgebra D : Type 0))) :
          vRhoAlgebra D ⟶ FiniteEtaleGalois.tensorObj (vRhoAlgebra D)
            (vRhoAlgebra D))) ≫ (vRhoFiberIso D).hom := by
  have hcomp := Limits.IsLimit.conePointsIsoOfNatIso_hom_comp
    (Limits.isLimitOfPreserves
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor
      (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (vRhoAlgebra D) (vRhoAlgebra D)))
    (rhoPairBinaryFanIsLimit D)
    (Limits.pairComp _ _ _ ≪≫ Limits.mapPairIso (vRhoFiberIso D) (vRhoFiberIso D))
    ⟨Limits.WalkingPair.left⟩
  exact hcomp

open scoped FintypeCatDiscrete in
/-- **[PIN-6c-iv-γ]** Second-leg compatibility of the pair correspondence. -/
theorem pairCorrespondenceIso_hom_snd (D : GaloisRepData N) [Fact (1 < N)] :
    (pairCorrespondenceIso D).hom ≫ rhoPairSnd D =
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeRight (R := ℚ) :
            (vRhoAlgebra D : Type 0) →ₐ[ℚ]
              TensorProduct ℚ (vRhoAlgebra D : Type 0) (vRhoAlgebra D : Type 0))) :
          vRhoAlgebra D ⟶ FiniteEtaleGalois.tensorObj (vRhoAlgebra D)
            (vRhoAlgebra D))) ≫ (vRhoFiberIso D).hom := by
  have hcomp := Limits.IsLimit.conePointsIsoOfNatIso_hom_comp
    (Limits.isLimitOfPreserves
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor
      (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (vRhoAlgebra D) (vRhoAlgebra D)))
    (rhoPairBinaryFanIsLimit D)
    (Limits.pairComp _ _ _ ≪≫ Limits.mapPairIso (vRhoFiberIso D) (vRhoFiberIso D))
    ⟨Limits.WalkingPair.right⟩
  exact hcomp

end

end ModularCurves
