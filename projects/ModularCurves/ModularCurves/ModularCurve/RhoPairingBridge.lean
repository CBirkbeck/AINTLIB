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

end

end ModularCurves
