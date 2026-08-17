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

end ModularCurves
