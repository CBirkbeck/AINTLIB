/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldLeaf
import ModularCurves.WeilPairing.GlueDataset
import ModularCurves.WeilPairing.ValuationTransport

/-!
# The scheme-to-HasseWeil order pipeline ([FF-TRANSPORT] + [L1])

The U5 comparison chain's divisor layer (`.mathlib-quality/decomposition-e4a-self.md`,
cont.18–20). The `[N]`-splitting germ `H := germ (h c₀)` of the Katz–Mazur dataset lives
in the function field of the pullback presentation `pullback E.π (𝟙 (Spec K))`; the
classical Weil function `g_T` lives in HasseWeil's `W.toAffine.FunctionField`. This file:

* `pullbackCurveFunctionFieldEquiv` — the transport: the function field of the pullback
  presentation is the HasseWeil function field, via the first projection (an isomorphism
  over the identity base) and `projModelFunctionFieldEquiv` (K4 (B)).
* `exists_const_mul_weilFunction` ([L1], statement) — the factorisation
  `H_HW · [N]^* r = c · g_T`: the transported splitting germ agrees with the classical
  Weil function up to a nonzero constant and an `[N]`-pullback. Proof route: the
  pointwise divisor computation `ORD-G` over the per-chart dataset ([G2′]) with the
  RP-dictionary of `ValuationTransport`, then `exists_const_mul_of_projectiveDivisorOf_eq`
  (U5-L1b). The `[N]`-pullback factor `r` is existential — its τ-invariance (all that L3
  needs) holds for *any* `[N]`-pullback since `[N] ∘ τ_S = [N]`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

open EllipticCurve WeierstrassCurve HasseWeil HasseWeil.Curves HasseWeil.WeilPairing

section FFTransport

variable {K : Type u} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- **([FF-TRANSPORT])** The function field of the pullback presentation over the
identity base is the HasseWeil function field of the Weierstrass curve: the first
projection is an isomorphism, and the projective model's function field is
`W.toAffine.FunctionField` by `projModelFunctionFieldEquiv` (K4 (B)). -/
noncomputable def pullbackCurveFunctionFieldEquiv
    [hprojInt : AlgebraicGeometry.IsIntegral (projModel W)] :
    haveI : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
      inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
    haveI : AlgebraicGeometry.IsIntegral
        (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
      isIntegral_pullback_id (modelEllipticCurve W)
    (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))).functionField ≃+* W.toAffine.FunctionField :=
  haveI hIntE : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
  haveI hInt : AlgebraicGeometry.IsIntegral
      (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    isIntegral_pullback_id (modelEllipticCurve W)
  RingEquiv.trans
    (RingEquiv.ofRingHom
      ((inv (pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom)
      ((pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))).functionFieldMap.hom)
      (by
        have hc := (functionFieldMap_comp
          (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))))
          (pullback.fst (modelEllipticCurve W).π
            (𝟙 (Spec (CommRingCat.of K))))).symm.trans
          ((functionFieldMap_congr (IsIso.inv_hom_id
            (pullback.fst (modelEllipticCurve W).π
              (𝟙 (Spec (CommRingCat.of K)))))).trans functionFieldMap_id)
        exact congrArg CommRingCat.Hom.hom hc
      )
      (by
        have hc := (functionFieldMap_comp
          (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))
          (inv (pullback.fst (modelEllipticCurve W).π
            (𝟙 (Spec (CommRingCat.of K)))))).symm.trans
          ((functionFieldMap_congr (IsIso.hom_inv_id
            (pullback.fst (modelEllipticCurve W).π
              (𝟙 (Spec (CommRingCat.of K)))))).trans functionFieldMap_id)
        exact congrArg CommRingCat.Hom.hom hc
      ))
    (EllipticCurve.projModelFunctionFieldEquiv W)

end FFTransport

section L1

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic] [W.toAffine.IsElliptic]
variable (hsm : SmoothOfRelativeDimension 1 (modelEllipticCurve W).π)
variable [IsSeparated (modelEllipticCurve W).π]

/-- **([L1], statement)** The transported splitting germ factors through the classical
Weil function: for the Katz–Mazur normalized per-chart dataset of `κ(Q)` and a
normalized `[N]`-splitting family `h` with anchor chart `c₀`,

  `H_HW · [N]^* r = c · g_T`,

where `H_HW` is the `pullbackCurveFunctionFieldEquiv`-image of `germ (h c₀)`, `T` is
the HasseWeil point of `Q`, `g_T` the chosen Weil function with divisor
`[N]^*(T) − [N]^*(O)`, `c ∈ Kˣ`, and `r` some nonzero element of the function field.

Proof route (`ORD-G`, cont.18–20): the divisor of `H_HW · [N]^*(f₁/f₂-ratio at c₀)` is
computed pointwise — at a place `P` over chart `i`, the hsplit relation and the
per-chart dressed transition (`[G2′]`) express the germ as
`(unit germs) · [N]^*(generator ratio at ch i)`; unit germs have order zero, the
generator orders are pinned by the span data through the RP-dictionary
(`ValuationTransport`), and the `[N]`-transfer is
`projectiveDivisorOf_pullback_eq_pullbackDivisor`. Equality of divisors with
`weilFunction_divisor` then gives the factorisation by `U5-L1b`
(`exists_const_mul_of_projectiveDivisorOf_eq`). -/
theorem exists_const_mul_weilFunction
    [AlgebraicGeometry.IsIntegral (projModel W)]
    [IsDedekindDomain (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve K).CoordinateRing]
    (N : ℕ) [NeZero N] (hNZ : ((N : ℤ) : K) ≠ 0)
    (Q : ((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))))
    (hQ : Q ∈ torsionPoints (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N)
    (M : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback (modelEllipticCurve W).π (𝟙 (Spec (.of K))))
      (kappa (modelEllipticCurve W) hsm (𝟙 (Spec (CommRingCat.of K))) Q).val =
        toSkeleton M)
    {ι' : Type*}
    (Wc : ι' → (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))).Opens)
    (hWc : iSup Wc = ⊤)
    (e : ∀ i, M.over (Wc i) ≅
      _root_.SheafOfModules.unit ((pullback (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))).ringCatSheaf.over (Wc i)))
    (hnorm : ∀ i j, transitionUnitOfCover M Wc e i j ∈
      sectionUnits (baseChangeZero (modelEllipticCurve W).π (modelEllipticCurve W).zero
        (modelEllipticCurve W).zero_π (𝟙 (Spec (CommRingCat.of K)))) (Wc i ⊓ Wc j))
    (h : ∀ i, Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))),
      mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i)ˣ)
    (hn : ∀ i, h i ∈ sectionUnits (baseChangeZero (modelEllipticCurve W).π
        (modelEllipticCurve W).zero (modelEllipticCurve W).zero_π
        (𝟙 (Spec (CommRingCat.of K))))
      (mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i))
    (hsplit : ∀ i j, Units.map ((mulByN (modelEllipticCurve W)
          (𝟙 (Spec (CommRingCat.of K))) N).app (Wc i ⊓ Wc j)).hom.toMonoidHom
        (transitionUnitOfCover M Wc e i j) =
      Scheme.resUnit (inf_le_left : mulByN (modelEllipticCurve W)
          (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i ⊓
          mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc j ≤
          mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i)
        (h i) *
        (Scheme.resUnit (inf_le_right : mulByN (modelEllipticCurve W)
            (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i ⊓
            mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc j ≤
            mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc j)
          (h j))⁻¹)
    (c₀ : ι')
    [Nonempty (mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc c₀ :
      (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).Opens)]
    (p : SpecPoints (projModel W) (projModelπ W) K)
    (hxp : (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q ≫
      baseChangeIdFstOver (modelEllipticCurve W)).left = p.1)
    (hT : (N : ℤ) • EllipticCurve.basePointCast W (projModelPointsEquiv W K p) = 0) :
    haveI : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
      inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
    haveI : AlgebraicGeometry.IsIntegral
        (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
      isIntegral_pullback_id (modelEllipticCurve W)
    ∃ (c : K) (r : W.toAffine.FunctionField), c ≠ 0 ∧ r ≠ 0 ∧
      pullbackCurveFunctionFieldEquiv W
          ((pullback (modelEllipticCurve W).π
            (𝟙 (Spec (CommRingCat.of K)))).germToFunctionField
            (mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc c₀)
            ((h c₀ : Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))),
              mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc c₀)))) *
        HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ)
          (by exact_mod_cast NeZero.ne' N |>.symm) r =
      algebraMap K W.toAffine.FunctionField c *
        HasseWeil.WeilPairing.weilFunction W (N : ℤ) hNZ
          (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hT := by
  sorry

end L1

section L3

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic] [W.toAffine.IsElliptic]
variable (hsm : SmoothOfRelativeDimension 1 (modelEllipticCurve W).π)
variable [IsSeparated (modelEllipticCurve W).π]

/-- **([TAU-INV], statement)** Translation by an `n`-torsion point fixes every
`[n]`-pullback: `τ_S^# ∘ [n]^# = [n]^#` on the function field, since `[n] ∘ τ_S = [n]`
at the point level for `n • S = 0`. -/
theorem translateAlgEquivOfPoint_mulByInt_pullbackAlgHom
    (S : W.toAffine.Point) (n : ℤ) (hn : (n : K) ≠ 0) (hn0 : n ≠ 0) (hS : n • S = 0)
    (r : W.toAffine.FunctionField) :
    HasseWeil.translateAlgEquivOfPoint W S
        (HasseWeil.mulByInt_pullbackAlgHom W.toAffine n hn0 r) =
      HasseWeil.mulByInt_pullbackAlgHom W.toAffine n hn0 r := by
  have hpb : (HasseWeil.mulByInt W.toAffine n).pullback =
      HasseWeil.mulByInt_pullbackAlgHom W.toAffine n hn0 := dif_neg hn0
  have hk : S ∈ (HasseWeil.mulByInt W.toAffine n).kernel := by
    rw [HasseWeil.Isogeny.mem_kernel_iff, HasseWeil.mulByInt_apply]
    exact hS
  have hxy := HasseWeil.WeilPairing.TorsionGeometric.hxy_mulByInt W n hn0 ⟨S, hk⟩
  have hgx := HasseWeil.mulByInt_pullback_x W n hn0
  have hgy := HasseWeil.mulByInt_pullback_y W n hn0
  have hz := HasseWeil.WeilPairing.TorsionGeometric.hcov_of_xy W
    (HasseWeil.mulByInt W.toAffine n) S
    (by rw [show HasseWeil.x_gen W = algebraMap W.toAffine.CoordinateRing
        W.toAffine.FunctionField (algebraMap (Polynomial K)
          W.toAffine.CoordinateRing Polynomial.X) from rfl, hgx]
        exact hxy.1)
    (by rw [show HasseWeil.y_gen W = algebraMap W.toAffine.CoordinateRing
        W.toAffine.FunctionField (AdjoinRoot.root W.toAffine.polynomial) from rfl, hgy]
        exact hxy.2)
    r
  rw [← hpb]
  exact hz

/-- **([GERM-Z], statement)** The transport reads affine germs as `algebraMap`-images:
the `projModelFunctionFieldEquiv`-image of a `zChart`-germ is the `algebraMap`-image of
its `coordRingToZSection`-transport. Unfold of `IsLocalization.ringEquivOfRingEquiv_eq`
at the fraction-field instances. -/
theorem projModelFunctionFieldEquiv_germToFunctionField_zChart
    [AlgebraicGeometry.IsIntegral (projModel W)]
    (t : Γ(projModel W, EllipticCurve.zChart W)) :
    haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
      Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
    haveI : Nontrivial W.toAffine.CoordinateRing := inferInstance
    haveI : Nontrivial Γ(projModel W, EllipticCurve.zChart W) :=
      (coordRingToZSection W).toEquiv.symm.nontrivial
    haveI : Nonempty (EllipticCurve.zChart W) :=
      ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
    EllipticCurve.projModelFunctionFieldEquiv W
        ((projModel W).germToFunctionField (EllipticCurve.zChart W) t) =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        ((coordRingToZSection W).symm t) := by
  sorry

/-- **([CONST-SECTION], statement)** The `zChart`-restriction of a base constant pulled
along the structure morphism transports to the `algebraMap`-image of the constant:
`coordRingToZSection` reads `π^#`-constants as scalars. -/
theorem coordRingToZSection_res_pi_app
    [AlgebraicGeometry.IsIntegral (projModel W)]
    (Cv : Γ(Spec (CommRingCat.of K), ⊤))
    (hle : EllipticCurve.zChart W ≤
      (modelEllipticCurve W).π ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens)) :
    (coordRingToZSection W).symm
        ((projModel W).presheaf.map (homOfLE hle).op
          ((Scheme.Hom.app (modelEllipticCurve W).π
            (⊤ : (Spec (CommRingCat.of K)).Opens)).hom Cv)) =
      algebraMap K W.toAffine.CoordinateRing
        ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom Cv) := by
  sorry

/-- **([VAL-TRANSPORT], statement)** The transport of a base constant: the
`pullbackCurveFunctionFieldEquiv`-image of the germ of a `globalTwist` of a global unit
of the base is the `algebraMap`-image of that unit read through `ΓSpecIso`. -/
theorem pullbackCurveFunctionFieldEquiv_germ_globalTwist
    [AlgebraicGeometry.IsIntegral (projModel W)]
    (V : (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))).Opens) [Nonempty V]
    (C : Γ(Spec (CommRingCat.of K), ⊤)ˣ) :
    haveI : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
      inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
    haveI : AlgebraicGeometry.IsIntegral
        (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
      isIntegral_pullback_id (modelEllipticCurve W)
    pullbackCurveFunctionFieldEquiv W
        ((pullback (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))).germToFunctionField V
          ((globalTwist (pullback.snd (modelEllipticCurve W).π
            (𝟙 (Spec (CommRingCat.of K)))) V C :
              Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))), V)))) =
      algebraMap K W.toAffine.FunctionField
        ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          ((C : Γ(Spec (CommRingCat.of K), ⊤)))) := by
  haveI hIntE : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
  haveI hInt : AlgebraicGeometry.IsIntegral
      (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    isIntegral_pullback_id (modelEllipticCurve W)
  haveI hIrr : IrreducibleSpace
      ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    inferInstance
  haveI hIrrE : IrreducibleSpace ↥(modelEllipticCurve W).E := inferInstance
  have hVle : V ≤ (pullback.snd (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) :=
    le_top
  haveI hNeV : Nonempty ↥V.toScheme := ‹Nonempty V›
  haveI hNepre : Nonempty ↥((pullback.snd (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of K)).Opens)).toScheme := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨⟨v.1, hVle v.2⟩⟩
  -- 1-2. the twist germ is the germ of the pulled constant on the full preimage
  have h12 : (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))).germToFunctionField V
        ((globalTwist (pullback.snd (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))) V C :
            Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))), V))) =
      (pullback (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))).germToFunctionField
        ((pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of K)).Opens))
        ((Scheme.Hom.app (pullback.snd (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))) (⊤ : (Spec (CommRingCat.of K)).Opens)).hom
          ((C : Γ(Spec (CommRingCat.of K), ⊤)))) :=
    germToFunctionField_restrict hVle _
  -- 3. hop across the first-projection inverse
  have h3 := functionFieldMap_germToFunctionField
    (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))))
    ((pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of K)).Opens))
    ((Scheme.Hom.app (pullback.snd (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))) (⊤ : (Spec (CommRingCat.of K)).Opens)).hom
      ((C : Γ(Spec (CommRingCat.of K), ⊤))))
  -- 4-5. collapse to the zChart and read through the dictionary
  have hle₂ : EllipticCurve.zChart W ≤
      (inv (pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ
        ((pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of K)).Opens)) := le_top
  have hle : EllipticCurve.zChart W ≤
      (modelEllipticCurve W).π ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := le_top
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : Nontrivial W.toAffine.CoordinateRing := inferInstance
  haveI : Nontrivial Γ(projModel W, EllipticCurve.zChart W) :=
    (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNeZ : Nonempty (EllipticCurve.zChart W) :=
    ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI hNeZ' : Nonempty ↥(EllipticCurve.zChart W).toScheme := hNeZ
  haveI hNepre' : Nonempty ↥((inv (pullback.fst (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ
      ((pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
        (⊤ : (Spec (CommRingCat.of K)).Opens))).toScheme := by
    obtain ⟨z⟩ := hNeZ
    exact ⟨⟨z.1, hle₂ z.2⟩⟩
  have h45 : (projModel W).germToFunctionField
      ((inv (pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ
        ((pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of K)).Opens)))
      ((Scheme.Hom.app (inv (pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))))
        ((pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of K)).Opens))).hom
        ((Scheme.Hom.app (pullback.snd (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))) (⊤ : (Spec (CommRingCat.of K)).Opens)).hom
          ((C : Γ(Spec (CommRingCat.of K), ⊤))))) =
      (projModel W).germToFunctionField (EllipticCurve.zChart W)
        ((projModel W).presheaf.map (homOfLE hle).op
          ((Scheme.Hom.app (modelEllipticCurve W).π
            (⊤ : (Spec (CommRingCat.of K)).Opens)).hom
            ((C : Γ(Spec (CommRingCat.of K), ⊤))))) := by
    have hπ : (modelEllipticCurve W).π =
        inv (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))) ≫
          pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) := by
      rw [show pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) =
        pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) ≫
          (modelEllipticCurve W).π from
        (pullback.condition.trans (Category.comp_id _)).symm,
        IsIso.inv_hom_id_assoc]
    have hres := germToFunctionField_restrict (C := projModel W) hle₂
      ((Scheme.Hom.app (inv (pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))))
        ((pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of K)).Opens))).hom
        ((Scheme.Hom.app (pullback.snd (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))) (⊤ : (Spec (CommRingCat.of K)).Opens)).hom
          ((C : Γ(Spec (CommRingCat.of K), ⊤)))))
    refine hres.symm.trans ?_
    refine congrArg ((projModel W).germToFunctionField (EllipticCurve.zChart W)) ?_
    have happ := congrArg (fun (f : (modelEllipticCurve W).E ⟶
        Spec (CommRingCat.of K)) =>
      (Scheme.Hom.appLE f (⊤ : (Spec (CommRingCat.of K)).Opens)
        (EllipticCurve.zChart W) le_top).hom
        ((C : Γ(Spec (CommRingCat.of K), ⊤)))) hπ
    refine Eq.trans ?_ (Eq.trans happ.symm ?_)
    · rw [Scheme.Hom.comp_appLE]
      rfl
    · rfl
  have hdef : ∀ y, pullbackCurveFunctionFieldEquiv W y =
      EllipticCurve.projModelFunctionFieldEquiv W
        ((inv (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom y) := fun _ => rfl
  rw [h12]
  have hinner := h3.trans h45
  refine (hdef _).trans ?_
  refine (congrArg (fun y => EllipticCurve.projModelFunctionFieldEquiv W y)
    hinner).trans ?_
  refine (projModelFunctionFieldEquiv_germToFunctionField_zChart W _).trans ?_
  refine (congrArg (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
    (coordRingToZSection_res_pi_app W _ hle)).trans ?_
  exact (IsScalarTower.algebraMap_apply K W.toAffine.CoordinateRing
    W.toAffine.FunctionField _).symm

/-- **([EQUIV-TAU], statement)** The translation conjugation through the transport: the
`pullbackCurveFunctionFieldEquiv`-image of a `translateByPoint`-pullback is the HasseWeil
translation of the image. Composite of `functionFieldMap_translateByPoint_conj` (U5-L2f,
the `fst`-crossing) and `translateAlgEquivOfPoint_functionFieldMap_of_section` (U5-L2g,
the model bridge). -/
theorem pullbackCurveFunctionFieldEquiv_translateByPoint
    [AlgebraicGeometry.IsIntegral (projModel W)]
    [(W.baseChange K).toAffine.IsElliptic]
    (P' : ((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))))
    [IsDominant (translateByPoint (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) P')]
    (pS : SpecPoints (projModel W) (projModelπ W) K)
    (hxpS : (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
      baseChangeIdFstOver (modelEllipticCurve W)).left = pS.1)
    (τp : projModel W ⟶ projModel W)
    (hτp : τp = ((modelEllipticCurve W).translateBy
      (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
        baseChangeIdFstOver (modelEllipticCurve W))).left)
    [IsDominant τp]
    [AlgebraicGeometry.IsIntegral (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K))))]
    (x : (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))).functionField) :
    haveI : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
      inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
    haveI : AlgebraicGeometry.IsIntegral
        (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
      isIntegral_pullback_id (modelEllipticCurve W)
    haveI : IrreducibleSpace
        ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
      inferInstance
    pullbackCurveFunctionFieldEquiv W
        ((translateByPoint (modelEllipticCurve W)
          (𝟙 (Spec (CommRingCat.of K))) P').functionFieldMap.hom x) =
      HasseWeil.translateAlgEquivOfPoint W
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K pS))
        (pullbackCurveFunctionFieldEquiv W x) := by
  haveI hIntE : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
  haveI hIrrE : IrreducibleSpace ↥(modelEllipticCurve W).E := inferInstance
  haveI hIrr : IrreducibleSpace
      ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    inferInstance
  have hdef : ∀ y, pullbackCurveFunctionFieldEquiv W y =
      EllipticCurve.projModelFunctionFieldEquiv W
        ((inv (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom y) := fun _ => rfl
  have hfg : ∀ y : (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))).functionField,
      (pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))).functionFieldMap.hom
        ((inv (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom y) = y := by
    intro y
    have hc := (functionFieldMap_comp
      (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))
      (inv (pullback.fst (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))))).symm.trans
      ((functionFieldMap_congr (IsIso.hom_inv_id
        (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))))).trans functionFieldMap_id)
    exact congrArg (fun q => (CommRingCat.Hom.hom q) y) hc
  -- the fst-crossing (U5-L2f) at z := invfst♯ x, rearranged
  have hL2f := functionFieldMap_translateByPoint_conj (modelEllipticCurve W) P'
    τp hτp ((inv (pullback.fst (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom x)
  rw [hfg x] at hL2f
  -- hL2f : τpb♯ x = fst♯ (τp♯ (invfst♯ x))
  have hmid : (inv (pullback.fst (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom
      ((translateByPoint (modelEllipticCurve W)
        (𝟙 (Spec (CommRingCat.of K))) P').functionFieldMap.hom x) =
      τp.functionFieldMap.hom
        ((inv (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom x) := by
    rw [hL2f]
    have hgf : ∀ z : (projModel W).functionField,
        (inv (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom
          ((pullback.fst (modelEllipticCurve W).π
            (𝟙 (Spec (CommRingCat.of K)))).functionFieldMap.hom z) = z := by
      intro z
      have hc := (functionFieldMap_comp
        (inv (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K)))))
        (pullback.fst (modelEllipticCurve W).π
          (𝟙 (Spec (CommRingCat.of K))))).symm.trans
        ((functionFieldMap_congr (IsIso.inv_hom_id
          (pullback.fst (modelEllipticCurve W).π
            (𝟙 (Spec (CommRingCat.of K)))))).trans functionFieldMap_id)
      exact congrArg (fun q => (CommRingCat.Hom.hom q) z) hc
    exact hgf _
  -- assemble through the model bridge (U5-L2g)
  rw [hdef, hdef, hmid]
  exact (translateAlgEquivOfPoint_functionFieldMap_of_section W P' pS hxpS τp hτp
    ((inv (pullback.fst (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K))))).functionFieldMap.hom x)).symm

/-- **([L3], statement)** The Katz–Mazur torsion-splitting value is the Silverman–Weil
pairing: for the normalized dataset, the anchor-chart τ-relation (`U5-L2e`) transported
through `pullbackCurveFunctionFieldEquiv` (`U5-L2f/L2g`) exhibits the transported
splitting germ as a `τ_S`-eigenfunction with eigenvalue the KM value; the `[L1]`
factorisation `H_HW · [N]^* r = c · g_T` and `weilPairing_spec` exhibit the same
function with eigenvalue `e_N(S, T)`; eigenvalues of a fixed nonzero eigenfunction
agree. -/
theorem torsionSplittingEval_eq_weilPairing
    [AlgebraicGeometry.IsIntegral (projModel W)]
    [IsDedekindDomain (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve K).CoordinateRing]
    (N : ℕ) [NeZero N] (hNZ : ((N : ℤ) : K) ≠ 0) (hN0 : (N : ℤ) ≠ 0)
    (Q : ((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))))
    (hQ : Q ∈ torsionPoints (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N)
    (M : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback (modelEllipticCurve W).π (𝟙 (Spec (.of K))))
      (kappa (modelEllipticCurve W) hsm (𝟙 (Spec (CommRingCat.of K))) Q).val =
        toSkeleton M)
    {ι' : Type*}
    (Wc : ι' → (pullback (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K)))).Opens)
    (hWc : iSup Wc = ⊤)
    (e : ∀ i, M.over (Wc i) ≅
      _root_.SheafOfModules.unit ((pullback (modelEllipticCurve W).π
        (𝟙 (Spec (CommRingCat.of K)))).ringCatSheaf.over (Wc i)))
    (hnorm : ∀ i j, transitionUnitOfCover M Wc e i j ∈
      sectionUnits (baseChangeZero (modelEllipticCurve W).π (modelEllipticCurve W).zero
        (modelEllipticCurve W).zero_π (𝟙 (Spec (CommRingCat.of K)))) (Wc i ⊓ Wc j))
    (h : ∀ i, Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))),
      mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i)ˣ)
    (hn : ∀ i, h i ∈ sectionUnits (baseChangeZero (modelEllipticCurve W).π
        (modelEllipticCurve W).zero (modelEllipticCurve W).zero_π
        (𝟙 (Spec (CommRingCat.of K))))
      (mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i))
    (hsplit : ∀ i j, Units.map ((mulByN (modelEllipticCurve W)
          (𝟙 (Spec (CommRingCat.of K))) N).app (Wc i ⊓ Wc j)).hom.toMonoidHom
        (transitionUnitOfCover M Wc e i j) =
      Scheme.resUnit (inf_le_left : mulByN (modelEllipticCurve W)
          (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i ⊓
          mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc j ≤
          mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i)
        (h i) *
        (Scheme.resUnit (inf_le_right : mulByN (modelEllipticCurve W)
            (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc i ⊓
            mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc j ≤
            mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc j)
          (h j))⁻¹)
    (c₀ : ι')
    [Nonempty (mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc c₀ :
      (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).Opens)]
    (P' : ((modelEllipticCurve W).baseChange
      (𝟙 (Spec (CommRingCat.of K)))).Point (𝟙 (Spec (CommRingCat.of K))))
    (hP' : P' ∈ torsionPoints (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N)
    [IsDominant (translateByPoint (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) P')]
    (p pS : SpecPoints (projModel W) (projModelπ W) K)
    (hxp : (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q ≫
      baseChangeIdFstOver (modelEllipticCurve W)).left = p.1)
    (hxpS : (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
      baseChangeIdFstOver (modelEllipticCurve W)).left = pS.1)
    (hT : (N : ℤ) • EllipticCurve.basePointCast W (projModelPointsEquiv W K p) = 0)
    (hS : (N : ℤ) • EllipticCurve.basePointCast W (projModelPointsEquiv W K pS) = 0) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        ((torsionSplittingEval (modelEllipticCurve W) hsm
          (𝟙 (Spec (CommRingCat.of K))) N Q hQ M hM Wc hWc e hnorm P' hP' :
            Γ(Spec (CommRingCat.of K), ⊤)ˣ) : Γ(Spec (CommRingCat.of K), ⊤)) =
      HasseWeil.WeilPairing.weilPairing W (N : ℤ) hNZ
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K pS))
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hS hT := by
  haveI hIntE : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
  haveI hInt : AlgebraicGeometry.IsIntegral
      (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    isIntegral_pullback_id (modelEllipticCurve W)
  haveI hIrr : IrreducibleSpace
      ↥(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    inferInstance
  -- the crossed translation on the model and its dominance
  have hsq : translateByPoint (modelEllipticCurve W)
        (𝟙 (Spec (CommRingCat.of K))) P' ≫
        pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))
      = pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) ≫
        ((modelEllipticCurve W).translateBy
          (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
            baseChangeIdFstOver (modelEllipticCurve W))).left :=
    translateByPoint_id_comp_fst (modelEllipticCurve W) P'
  have hτp_eq : ((modelEllipticCurve W).translateBy
        (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
          baseChangeIdFstOver (modelEllipticCurve W))).left =
      inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ≫
        (translateByPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
          pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [hsq, IsIso.inv_hom_id_assoc]
  haveI hτdom : IsDominant (((modelEllipticCurve W).translateBy
      (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
        baseChangeIdFstOver (modelEllipticCurve W))).left) := by
    rw [hτp_eq]
    infer_instance
  -- 1. the scheme-side eigen-equation (U5-L2e at the anchor chart)
  have hL2e := functionFieldMap_translateByPoint_germ (modelEllipticCurve W) hsm
    N Q hQ M hM Wc hWc e hnorm h hn hsplit P' hP' c₀
  -- 2. transport through the function-field equivalence
  have h2 := congrArg (pullbackCurveFunctionFieldEquiv W) hL2e
  rw [map_mul] at h2
  rw [pullbackCurveFunctionFieldEquiv_translateByPoint W P' pS hxpS
    (((modelEllipticCurve W).translateBy
      (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) P' ≫
        baseChangeIdFstOver (modelEllipticCurve W))).left) rfl] at h2
  rw [pullbackCurveFunctionFieldEquiv_germ_globalTwist W
    (mulByN (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) N ⁻¹ᵁ Wc c₀)
    (torsionSplittingEval (modelEllipticCurve W) hsm
      (𝟙 (Spec (CommRingCat.of K))) N Q hQ M hM Wc hWc e hnorm P' hP')] at h2
  -- 3. the divisor factorisation ([L1])
  obtain ⟨c, r, hc, hr, hfact⟩ := exists_const_mul_weilFunction W hsm N hNZ Q hQ
    M hM Wc hWc e hnorm h hn hsplit c₀ p hxp hT
  -- 4. translate the factorisation and evaluate each factor
  have h7 := congrArg (HasseWeil.translateAlgEquivOfPoint W
    (EllipticCurve.basePointCast W (projModelPointsEquiv W K pS))) hfact
  rw [map_mul, map_mul] at h7
  rw [translateAlgEquivOfPoint_mulByInt_pullbackAlgHom W
    (EllipticCurve.basePointCast W (projModelPointsEquiv W K pS))
    (N : ℤ) hNZ (by exact_mod_cast NeZero.ne' N |>.symm) hS r] at h7
  rw [AlgEquiv.commutes] at h7
  rw [HasseWeil.WeilPairing.weilPairing_translate W (N : ℤ) hNZ
    (EllipticCurve.basePointCast W (projModelPointsEquiv W K pS))
    (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hS hT] at h7
  -- 5. substitute the eigen-equation into the translated factorisation
  rw [h2] at h7
  -- h7 : (H_HW * algebraMap (ΓSpec val)) * [N]^*r
  --    = algebraMap c * (algebraMap e * g_T)
  -- 6. cancellation against the untranslated factorisation
  have hgne : HasseWeil.WeilPairing.weilFunction W (N : ℤ) hNZ
      (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hT ≠ 0 :=
    HasseWeil.WeilPairing.weilFunction_ne_zero W (N : ℤ) hNZ _ hT
  have hcne : algebraMap K W.toAffine.FunctionField c ≠ 0 := by
    simpa using (map_ne_zero (algebraMap K W.toAffine.FunctionField)).mpr hc
  have hkey : algebraMap K W.toAffine.FunctionField
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        ((torsionSplittingEval (modelEllipticCurve W) hsm
          (𝟙 (Spec (CommRingCat.of K))) N Q hQ M hM Wc hWc e hnorm P' hP' :
            Γ(Spec (CommRingCat.of K), ⊤)ˣ) : Γ(Spec (CommRingCat.of K), ⊤))) *
        (algebraMap K W.toAffine.FunctionField c *
          HasseWeil.WeilPairing.weilFunction W (N : ℤ) hNZ
            (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hT) =
      algebraMap K W.toAffine.FunctionField
        (HasseWeil.WeilPairing.weilPairing W (N : ℤ) hNZ
          (EllipticCurve.basePointCast W (projModelPointsEquiv W K pS))
          (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hS hT) *
        (algebraMap K W.toAffine.FunctionField c *
          HasseWeil.WeilPairing.weilFunction W (N : ℤ) hNZ
            (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hT) := by
    rw [← hfact]
    linear_combination h7 - algebraMap K W.toAffine.FunctionField
      (HasseWeil.WeilPairing.weilPairing W (N : ℤ) hNZ
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K pS))
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hS hT) * hfact
  have hcanc := mul_right_cancel₀ (mul_ne_zero hcne hgne) hkey
  exact (algebraMap K W.toAffine.FunctionField).injective hcanc

end L3

end ModularCurves
