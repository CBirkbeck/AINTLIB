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

attribute [local instance] MvPolynomial.gradedAlgebra

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
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : Nontrivial W.toAffine.CoordinateRing := inferInstance
  haveI : Nontrivial Γ(projModel W, EllipticCurve.zChart W) :=
    (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNeZ : Nonempty (EllipticCurve.zChart W) :=
    ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI : IsFractionRing Γ(projModel W, EllipticCurve.zChart W)
      (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W)
      (EllipticCurve.zChart W) hZaff
  simp only [EllipticCurve.projModelFunctionFieldEquiv]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ t

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
  have hcancel : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom Cv) = Cv := by
    have h := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id Cv
    simpa using h
  have h4 := structure_section_square_apply W
    ((projIdeal W).quotientGradingHom (MvPolynomial.X 2))
    (mk_X_mem_quotientGrading_one W 2) one_pos
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom Cv)
  rw [hcancel] at h4
  exact (congrArg (fun z => (chartZRingEquiv W) z) h4).trans
    (chartZRingEquiv_fromZero W _)

/-- **([SEC-ORD D-MEM])** Basic-open membership of the `zChart` point is
non-membership of `s` in the transported maximal ideal. -/
private theorem secOrd_s_notMem_zChartMaximalIdeal
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (s : Γ(projModel W, EllipticCurve.zChart W))
    (hPs : zChartPoint W P ∈ (projModel W).basicOpen s) :
    s ∉ zChartMaximalIdeal W P := by
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  have h2 : (⟨zChartMaximalIdeal W P,
      (zChartMaximalIdeal_isMaximal W P).isPrime⟩ :
      PrimeSpectrum Γ(projModel W, EllipticCurve.zChart W)) ∈
      hZaff.fromSpec ⁻¹ᵁ (projModel W).basicOpen s := hPs
  rw [hZaff.fromSpec_preimage_basicOpen] at h2
  exact (PrimeSpectrum.mem_basicOpen _ _).mp h2

/-- **([SEC-ORD D-MEM-IFF])** The iff-form of D-MEM: basic-open membership of the
`zChart` point is exactly non-membership in the transported maximal ideal. -/
private theorem secOrd_mem_basicOpen_iff_notMem
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (r : Γ(projModel W, EllipticCurve.zChart W)) :
    zChartPoint W P ∈ (projModel W).basicOpen r ↔ r ∉ zChartMaximalIdeal W P := by
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  constructor
  · intro hPr
    have h2 : (⟨zChartMaximalIdeal W P,
        (zChartMaximalIdeal_isMaximal W P).isPrime⟩ :
        PrimeSpectrum Γ(projModel W, EllipticCurve.zChart W)) ∈
        hZaff.fromSpec ⁻¹ᵁ (projModel W).basicOpen r := hPr
    rw [hZaff.fromSpec_preimage_basicOpen] at h2
    exact (PrimeSpectrum.mem_basicOpen _ _).mp h2
  · intro hnot
    have h2 : (⟨zChartMaximalIdeal W P,
        (zChartMaximalIdeal_isMaximal W P).isPrime⟩ :
        PrimeSpectrum Γ(projModel W, EllipticCurve.zChart W)) ∈
        hZaff.fromSpec ⁻¹ᵁ (projModel W).basicOpen r := by
      rw [hZaff.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr hnot
    exact h2

open scoped Classical in
/-- **([SEC-ORD s-unit])** The shrink denominator has order zero at the point: the
basic-open membership of the `zChart` point is exactly non-membership of `s` in the
transported maximal ideal, and non-members have order zero. -/
private theorem secOrd_sPrime_ord_zero
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (s : Γ(projModel W, EllipticCurve.zChart W))
    (hPs : zChartPoint W P ∈ (projModel W).basicOpen s) :
    (⟨W⟩ : SmoothPlaneCurve K).ord_P P
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField)
        ((coordRingToZSection W).symm s)) = 0 := by
  have hsnotmem : s ∉ zChartMaximalIdeal W P :=
    secOrd_s_notMem_zChartMaximalIdeal W P s hPs
  have hs0 : s ≠ 0 := fun h0 => hsnotmem (by rw [h0]; exact Ideal.zero_mem _)
  have hs'notmem : (coordRingToZSection W).symm s ∉
      (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P := fun hmem => by
    have h3 := Ideal.mem_map_of_mem (coordRingToZSection W) hmem
    rw [show (coordRingToZSection W) ((coordRingToZSection W).symm s) = s from
      (coordRingToZSection W).apply_symm_apply s] at h3
    exact hsnotmem h3
  have hs'0 : (coordRingToZSection W).symm s ≠ 0 := fun h0 => by
    have h4 := congrArg (coordRingToZSection W) h0
    rw [(coordRingToZSection W).apply_symm_apply s, map_zero] at h4
    exact hs0 h4
  exact ord_P_algebraMap_eq_zero_of_notMem W P _ hs'0 hs'notmem

/-- **([SEC-ORD BO-CHAIN])** The numerator's basic-open membership at the point is
exactly the point being off the section: transport the fraction relation through the
basic-open algebra to the chart, then read the section-kernel support. -/
private theorem secOrd_f0_mem_basicOpen_iff
    (z : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))
    [QuasiCompact z] [IsClosedImmersion z]
    (V : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).affineOpens)
    (f : Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))), V.1))
    (hspan : (Scheme.Hom.ker z).ideal V = Ideal.span {f})
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (hPV : (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).base (zChartPoint W P) ∈ V.1)
    (s : Γ(projModel W, EllipticCurve.zChart W))
    (hsle : (projModel W).basicOpen s ≤
      (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ V.1 ⊓ EllipticCurve.zChart W)
    (hPs : zChartPoint W P ∈ (projModel W).basicOpen s)
    (n : ℕ) (f₀ : Γ(projModel W, EllipticCurve.zChart W))
    (hrep : (projModel W).presheaf.map (homOfLE (hsle.trans inf_le_left)).op
        ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f) *
        (projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le s)).op
          (s ^ n) =
      (projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le s)).op f₀) :
    zChartPoint W P ∈ (projModel W).basicOpen f₀ ↔
      (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).base (zChartPoint W P) ≠ z.base default := by
  -- the basic-open form of the fraction relation
  have hbo := congrArg (projModel W).basicOpen hrep
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res,
    Scheme.basicOpen_res] at hbo
  -- the point lies in every power's basic open (n = 0 gives the whole chart)
  have hpow : zChartPoint W P ∈ (projModel W).basicOpen (s ^ n) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, pow_zero, Scheme.basicOpen_one]
      exact (projModel W).basicOpen_le s hPs
    · have he := Scheme.basicOpen_pow (X := projModel W) (f := s) (h := hn)
      rw [he]
      exact hPs
  -- membership transfer at the point (which lies in D(s) and in basicOpen s)
  have hmem : zChartPoint W P ∈ (projModel W).basicOpen f₀ ↔
      zChartPoint W P ∈ (projModel W).basicOpen ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f) := by
    constructor
    · intro h
      have h2 : zChartPoint W P ∈ (projModel W).basicOpen s ⊓
          (projModel W).basicOpen f₀ := ⟨hPs, h⟩
      rw [← hbo] at h2
      exact h2.1.2
    · intro h
      have h2 : zChartPoint W P ∈
          ((projModel W).basicOpen s ⊓
            (projModel W).basicOpen ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f)) ⊓
          ((projModel W).basicOpen s ⊓ (projModel W).basicOpen (s ^ n)) :=
        ⟨⟨hPs, h⟩, ⟨hPs, hpow⟩⟩
      rw [hbo] at h2
      exact h2.2
  rw [hmem]
  have hpre : (projModel W).basicOpen ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f) =
      (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ ((pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).basicOpen f) :=
    (Scheme.preimage_basicOpen (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) f).symm
  rw [hpre]
  -- the chart-level support read: supportSet = range of the section
  have h6 := Scheme.Hom.support_ker z
  have h5 : ∀ q, q ∈ (Scheme.Hom.ker z).supportSet ↔ q ∈ Set.range z.base := by
    intro q
    show q ∈ ((Scheme.Hom.ker z).support : Set _) ↔ q ∈ Set.range z.base
    rw [h6, z.isClosedEmbedding.isClosed_range.closure_eq]
  constructor
  · intro hbo hqe
    have hqr : (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).base (zChartPoint W P) ∈ Set.range z.base :=
      ⟨default, hqe.symm⟩
    have hsup := (h5 _).mpr hqr
    have hzl := (Scheme.IdealSheafData.mem_supportSet_iff_of_mem hPV).mp hsup
    rw [hspan, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hzl
    exact hzl f rfl hbo
  · intro hne
    by_contra hnbo
    have hzl : (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).base (zChartPoint W P) ∈
        (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).zeroLocus (U := V.1) {f} := by
      rw [Scheme.mem_zeroLocus_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hnbo
    have hzl2 : (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).base (zChartPoint W P) ∈
        (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).zeroLocus (U := V.1) ((Scheme.Hom.ker z).ideal V : Set _) := by
      rw [hspan, Scheme.zeroLocus_span]
      exact hzl
    have hsup := (Scheme.IdealSheafData.mem_supportSet_iff_of_mem hPV).mpr hzl2
    obtain ⟨y, hy⟩ := (h5 _).mp hsup
    exact hne (by
      rw [← hy]
      exact congrArg z.base (Subsingleton.elim y default))

/-- The `appLE`-at-identity crossing: an endomorphism propositionally equal to the
identity has identity `appLE` on `⊤` (subst then unfold). -/
private theorem appLE_top_top_of_eq_id {X : Scheme} {h : X ⟶ X} (he : h = 𝟙 X)
    (e : (⊤ : X.Opens) ≤ h ⁻¹ᵁ (⊤ : X.Opens)) :
    Scheme.Hom.appLE h ⊤ ⊤ e = 𝟙 Γ(X, ⊤) := by
  subst he
  simp [Scheme.Hom.appLE]

/-- **([SEC-ORD K-MAX])** The section-kernel span is a maximal ideal of the chart ring
when the chart contains the section point: the section identity `z ≫ snd = 𝟙` splits
`z`'s `appLE` to `⊤`, so the chart ring surjects onto `Γ(Spec K, ⊤) ≅ K` with kernel
exactly the span — the K-valued evaluation at the section point. -/
private theorem secOrd_span_isMaximal
    (z : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))
    [QuasiCompact z]
    (hz : z ≫ pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) = 𝟙 (Spec (CommRingCat.of K)))
    (V : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).affineOpens)
    (f : Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))), V.1))
    (hspan : (Scheme.Hom.ker z).ideal V = Ideal.span {f})
    (hzd : z.base default ∈ V.1) :
    (Ideal.span {f}).IsMaximal := by
  have e₂ : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ z ⁻¹ᵁ V.1 := by
    intro x _
    rw [Subsingleton.elim x default]
    exact hzd
  have e₁ : V.1 ≤ (pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := by simp
  have hcomp : Scheme.Hom.appLE (pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⊤ V.1 e₁ ≫ Scheme.Hom.appLE z V.1 ⊤ e₂ =
      𝟙 Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.Hom.appLE_comp_appLE z (pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⊤ V.1 ⊤ e₁ e₂).trans
      (appLE_top_top_of_eq_id hz _)
  have hsurj : Function.Surjective (Scheme.Hom.appLE z V.1 ⊤ e₂).hom := fun y =>
    ⟨(Scheme.Hom.appLE (pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) ⊤ V.1 e₁).hom y, by
      simpa using ConcreteCategory.congr_hom hcomp y⟩
  have hκbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  -- the kernel of the `⊤`-level evaluation is the kernel of the chart-level one
  have heq : z ⁻¹ᵁ V.1 = (⊤ : (Spec (CommRingCat.of K)).Opens) := le_antisymm le_top e₂
  have hresinj : Function.Injective
      ((Spec (CommRingCat.of K)).presheaf.map (homOfLE e₂).op).hom := by
    rw [Subsingleton.elim (homOfLE e₂) (eqToHom heq.symm)]
    exact (ConcreteCategory.bijective_of_isIso _).1
  have hker : RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom.comp
      ((Scheme.Hom.appLE z V.1 ⊤ e₂).hom)) = Ideal.span {f} := by
    rw [RingHom.ker_comp_of_injective _ hκbij.1]
    have hsplit : (Scheme.Hom.appLE z V.1 ⊤ e₂).hom =
        (((Spec (CommRingCat.of K)).presheaf.map (homOfLE e₂).op).hom).comp ((z.app V.1).hom) := rfl
    rw [hsplit, RingHom.ker_comp_of_injective _ hresinj, ← Scheme.Hom.ker_apply, hspan]
  have hmax := RingHom.ker_isMaximal_of_surjective
    (((Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom.comp ((Scheme.Hom.appLE z V.1 ⊤ e₂).hom))
    (hκbij.2.comp hsurj)
  rw [hker] at hmax
  exact hmax

open scoped Classical in
/-- **([SEC-ORD], statement)** The pointwise order of a section-kernel chart
generator: for a `Spec K`-section `z` of the base-changed curve and a chart `V` on
which `z.ker` is principal with generator `f`, the `ord_P` of the transported
function-field germ of `f` is `1` at the section's point and `0` at every other
place lying over `V`. The chart-local half of `div f = [P_z]`; the `ORD-G`
pointwise computation consumes exactly this dichotomy (cont.30x/30y). -/
theorem ord_P_germ_sectionKer_generator
    [AlgebraicGeometry.IsIntegral (projModel W)]
    (z : Spec (CommRingCat.of K) ⟶ pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))
    (hz : z ≫ pullback.snd (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))) =
      𝟙 (Spec (CommRingCat.of K)))
    [QuasiCompact z]
    (V : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).affineOpens)
    (f : Γ(pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))), V.1))
    (hspan : (Scheme.Hom.ker z).ideal V = Ideal.span {f})
    (hf : f ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (hPV : (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).base (zChartPoint W P) ∈ V.1)
    [Nonempty V.1] :
    haveI : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
      inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
    haveI : AlgebraicGeometry.IsIntegral (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
      isIntegral_pullback_id (modelEllipticCurve W)
    (⟨W⟩ : SmoothPlaneCurve K).ord_P P
      (pullbackCurveFunctionFieldEquiv W
        ((pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).germToFunctionField V.1 f)) =
    (if (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).base (zChartPoint W P) = z.base default then 1 else 0) := by
  haveI hIntE : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
  haveI hInt : AlgebraicGeometry.IsIntegral (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))) :=
    isIntegral_pullback_id (modelEllipticCurve W)
  haveI hNeV' : Nonempty ↥((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ (V : (pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).Opens)) :=
    ⟨⟨zChartPoint W P, hPV⟩⟩
  -- [S1] the fst-hop: the pullback function-field image is the projModel
  -- function-field image of the transported germ
  have h1 : pullbackCurveFunctionFieldEquiv W
      ((pullback (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K)))).germToFunctionField V.1 f) =
      EllipticCurve.projModelFunctionFieldEquiv W
        ((@Scheme.germToFunctionField (projModel W) _
          ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ V.1)
          hNeV')
          ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f)) :=
    congrArg (⇑(EllipticCurve.projModelFunctionFieldEquiv W))
      (functionFieldMap_germToFunctionField
        (inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) V.1 f)
  -- [S2] shrink to a basic open of the zChart around the point
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  have hPz : zChartPoint W P ∈ EllipticCurve.zChart W := by
    rw [← SetLike.mem_coe, ← hZaff.range_fromSpec]
    exact Set.mem_range_self _
  obtain ⟨s, hsle, hPs⟩ := hZaff.exists_basicOpen_le
    (V := (inv (pullback.fst (modelEllipticCurve W).π
      (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ V.1 ⊓ EllipticCurve.zChart W)
    ⟨zChartPoint W P, ⟨hPV, hPz⟩⟩ hPz
  haveI hNeD : Nonempty ↥((projModel W).basicOpen s).toScheme :=
    ⟨⟨zChartPoint W P, hPs⟩⟩
  haveI hNeV'sch : Nonempty ↥((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ V.1).toScheme :=
    ⟨⟨zChartPoint W P, hPV⟩⟩
  -- [S2c] restrict the germ to the basic open
  have h2 : (projModel W).germToFunctionField ((projModel W).basicOpen s)
      ((projModel W).presheaf.map (homOfLE (hsle.trans inf_le_left)).op
        ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f)) =
      @Scheme.germToFunctionField (projModel W) _
        ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))) ⁻¹ᵁ V.1) hNeV'
        ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f) :=
    (projModel W).presheaf.germ_res_apply
      (homOfLE (hsle.trans inf_le_left)) _ _
      ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f)
  -- [S3] the Away-fraction representation of the restricted section
  haveI hAway : IsLocalization.Away s Γ(projModel W, (projModel W).basicOpen s) :=
    hZaff.isLocalization_basicOpen s
  set xD : Γ(projModel W, (projModel W).basicOpen s) :=
    (projModel W).presheaf.map (homOfLE (hsle.trans inf_le_left)).op
      ((inv (pullback.fst (modelEllipticCurve W).π (𝟙 (Spec (CommRingCat.of K))))).app V.1 f) with hxD
  have hrep := IsLocalization.Away.sec_spec
    (S := Γ(projModel W, (projModel W).basicOpen s)) s xD
  -- [S3b] the Away algebra map is the restriction map
  have halg : ∀ r : Γ(projModel W, EllipticCurve.zChart W),
      (algebraMap Γ(projModel W, EllipticCurve.zChart W)
        Γ(projModel W, (projModel W).basicOpen s)) r =
      (projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le s)).op r := fun r => rfl
  haveI hNeZ : Nonempty (EllipticCurve.zChart W) := ⟨⟨zChartPoint W P, hPz⟩⟩
  -- [S3c] the function-field equation from the fraction representation
  have hFFeq : EllipticCurve.projModelFunctionFieldEquiv W
        ((projModel W).germToFunctionField ((projModel W).basicOpen s) xD) *
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        ((coordRingToZSection W).symm s)) ^ (IsLocalization.Away.sec s xD).2 =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        ((coordRingToZSection W).symm (IsLocalization.Away.sec s xD).1) := by
    have h := congrArg (fun t =>
      EllipticCurve.projModelFunctionFieldEquiv W
        ((projModel W).germToFunctionField ((projModel W).basicOpen s) t)) hrep
    simp only [map_mul, map_pow] at h
    rw [halg, halg] at h
    rw [show (projModel W).germToFunctionField ((projModel W).basicOpen s)
        ((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le s)).op s) =
      (projModel W).germToFunctionField (EllipticCurve.zChart W) s from
      (projModel W).presheaf.germ_res_apply
        (homOfLE ((projModel W).basicOpen_le s)) _ _ s] at h
    rw [show (projModel W).germToFunctionField ((projModel W).basicOpen s)
        ((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le s)).op
          (IsLocalization.Away.sec s xD).1) =
      (projModel W).germToFunctionField (EllipticCurve.zChart W)
        (IsLocalization.Away.sec s xD).1 from
      (projModel W).presheaf.germ_res_apply
        (homOfLE ((projModel W).basicOpen_le s)) _ _
        (IsLocalization.Away.sec s xD).1] at h
    rw [projModelFunctionFieldEquiv_germToFunctionField_zChart W s,
      projModelFunctionFieldEquiv_germToFunctionField_zChart W
        (IsLocalization.Away.sec s xD).1] at h
    exact h
  -- [S4] take orders in the fraction equation
  have hordeq := congrArg ((⟨W⟩ : SmoothPlaneCurve K).ord_P P) hFFeq
  rw [SmoothPlaneCurve.ord_P_mul, SmoothPlaneCurve.ord_P_pow,
    secOrd_sPrime_ord_zero W P s hPs, smul_zero, add_zero] at hordeq
  refine Eq.trans (congrArg ((⟨W⟩ : SmoothPlaneCurve K).ord_P P)
    (h1.trans (congrArg (⇑(EllipticCurve.projModelFunctionFieldEquiv W))
      h2.symm))) ?_
  refine hordeq.trans ?_
  trace_state
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

/-- **([L5], the diagonal)** The Katz–Mazur torsion-splitting value at the diagonal is
`1`: instantiate `[L3]` at `P' := Q` and import HasseWeil's alternation
`weilPairing_self` (Silverman III.8.1a). This is the field-leaf shape of
`weilPairingEval_self` (AP-E4a / U5). -/
theorem torsionSplittingEval_self_eq_one
    [AlgebraicGeometry.IsIntegral (projModel W)]
    [IsDedekindDomain (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve K).CoordinateRing]
    [(W.baseChange K).toAffine.IsElliptic]
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
    [IsDominant (translateByPoint (modelEllipticCurve W)
      (𝟙 (Spec (CommRingCat.of K))) Q)]
    (p : SpecPoints (projModel W) (projModelπ W) K)
    (hxp : (overPoint (modelEllipticCurve W) (𝟙 (Spec (CommRingCat.of K))) Q ≫
      baseChangeIdFstOver (modelEllipticCurve W)).left = p.1)
    (hT : (N : ℤ) • EllipticCurve.basePointCast W (projModelPointsEquiv W K p) = 0) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        ((torsionSplittingEval (modelEllipticCurve W) hsm
          (𝟙 (Spec (CommRingCat.of K))) N Q hQ M hM Wc hWc e hnorm Q hQ :
            Γ(Spec (CommRingCat.of K), ⊤)ˣ) : Γ(Spec (CommRingCat.of K), ⊤)) = 1 := by
  rw [torsionSplittingEval_eq_weilPairing W hsm N hNZ hN0 Q hQ M hM Wc hWc e hnorm
    h hn hsplit c₀ Q hQ p p hxp hxp hT hT]
  exact HasseWeil.WeilPairing.weilPairing_self W (N : ℤ) hNZ
    (EllipticCurve.basePointCast W (projModelPointsEquiv W K p)) hT

end L3


end ModularCurves
