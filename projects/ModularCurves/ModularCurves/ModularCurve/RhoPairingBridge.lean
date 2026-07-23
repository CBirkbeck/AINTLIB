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

end

end ModularCurves
