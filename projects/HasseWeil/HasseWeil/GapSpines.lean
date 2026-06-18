/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback.Differential
import HasseWeil.AdditionPullback.SilvermanIV14
import HasseWeil.Curves.FintypeProjectiveSmoothPoint
import HasseWeil.DualIsogeny
import HasseWeil.EC.IsogenyKernel
import HasseWeil.GapQfKernel
import HasseWeil.Hasse.L6ViaPoleDivisor
import HasseWeil.Hasse.L6Witnesses
import HasseWeil.Hasse.PointFix
import HasseWeil.Hasse.PoleDivisor2Tor
import HasseWeil.Verschiebung.Cascade
import HasseWeil.Verschiebung.QthRootRouteB

/-!
# Middle spines of the Hasse skeleton (GAP-QF dual chain + GAP-L6 point count)

The two keystone MIDDLE leaves of the proof, plus the connected GAP-L6 leaf:

* **GAP-QF keystone** `verschiebung_dual_exists` (Silverman III.6.1 Case 2) — the Verschiebung
  `V` dual to the `q`-power Frobenius `π`, PROVED via Route B's
  `qth_root_witness_general` (`Verschiebung/QthRootRouteB.lean`).
* **GAP-L6 keystone** `sepDegree_oneSub_eq_pointCount` (Silverman V.1.1) — `sepDeg(1−π)=#E(F_q)`.
* **`ker_deg_skeleton`** (GAP-L6 top leaf) — now PROVED from the keystone via the existing
  `hole_d_of_hom_and_sepDegree` + `card_kernel_eq_degree_of_separable_witness` chain.

(2026-06-11 sweep: the legacy skeleton chain `genuineIsogSmulSub_degree_eq_signed` →
`degree_quadratic_exists_edge` → `degree_quadratic_exists_skeleton_nonzero` →
`qf_nonneg_skeleton` → `HasseWeilSkeleton.hasse_bound_skeleton` was RETIRED, together with
the refuted char-divisible edge stubs (B2-logged) and the dead `l6_computationA`; III.6.3
non-negativity is proven on the live route via
`WeilPairing/HasseAssembly.lean`'s `qf_nonneg_skeleton_of_weil_det_data`, feeding the
proven bound `WeilPairing.hasse_bound_unconditional`.)
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

/-- **Pillar B bottom leaf** (the genuine GAP-DUAL kernel): every `[q]`-pullback is a `q`-th
power, `∀ z, ∃ g, g^q = [q]* z`. PROVED by Route B's general `q`-th-root witness
`qth_root_witness_general` (`Verschiebung/QthRootRouteB.lean`). -/
theorem mulByInt_q_pullback_qth_root (hq : 2 ≤ Fintype.card K) :
    ∀ z : W.toAffine.FunctionField, ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z :=
  qth_root_witness_general W

/-- **Inclusion, CONNECTED** (Silverman II.2.11/III.6.2): `Im([q]*) ⊆ Im(π*) = K(E)^q`. PROVED
from the `q`-th-root leaf via the shipped
`mulByInt_q_pullback_image_subset_frobenius_of_element_witness`. -/
theorem mulByInt_q_pullback_subset_frobenius (hq : 2 ≤ Fintype.card K) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
      (frobeniusIsog W).pullback.range :=
  mulByInt_q_pullback_image_subset_frobenius_of_element_witness W
    (mulByInt_q_pullback_qth_root W hq)

/-- **Pillar B, CONNECTED** (Silverman II.2.12, p. 26): `[q]` factors through Frobenius,
`∃ ψ, ψ ∘ π = [q]`. PROVED from the inclusion leaf via the shipped
`mulByInt_q_factor_isog_of_subset_witness`. -/
theorem mulByInt_q_factors_through_frobenius (hq : 2 ≤ Fintype.card K) :
    ∃ ψ : Isogeny W.toAffine W.toAffine,
      ψ.comp (frobeniusIsog W) = mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) :=
  mulByInt_q_factor_isog_of_subset_witness W (mulByInt_q_pullback_subset_frobenius W hq)

/-- **GAP-QF keystone, CONNECTED** (Silverman III.6.1 Case 2, p. 82): the Verschiebung exists —
an isogeny `V` dual to the `q`-power Frobenius `π`. PROVED from the II.2.12 factorization leaf via
the shipped `verschiebungIsog_isDualOf_frobenius_of_factor`. -/
theorem verschiebung_dual_exists (hq : 2 ≤ Fintype.card K) :
    ∃ V : Isogeny W.toAffine W.toAffine, IsDualOf W.toAffine V (frobeniusIsog W) :=
  ⟨_, verschiebungIsog_isDualOf_frobenius_of_factor W
    (mulByInt_q_factors_through_frobenius W hq)⟩

omit [Fintype W.toAffine.Point] in
/-- **GAP-L6 sub-leaf B3, LOWER step** (Silverman V.1.1): the relative degree
`[γ.pullback.fieldRange : K⟮γ*x⟯] = 2`, the transfer of `[K(E):K(x)] = 2` along the
ring-equivs `e_f : FractionRing K[X] ≃ₐ K⟮f⟯` and `gammaBar : K(E) ≃ₐ γ.pullback.fieldRange`
(`Algebra.finrank_eq_of_equiv_equiv`). The relevant `↥K⟮f⟯`-algebra structure on `↥fieldRange`
is the (non-canonical) `inclusion h_le` one, passed explicitly as `algInst` and pinned in the
`finrank`; this lets the heavy `e_f`/`gammaBar`/`inclusion` machinery elaborate in isolation
(the combined tower step otherwise hit an instance-diamond synthesis wall). -/
theorem finrank_fieldRange_over_adjoin_pullback_x_eq_two (hq : 2 ≤ Fintype.card K)
    (h_le :
      IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField) ≤
        (isogOneSub_negFrobenius W hq).pullback.fieldRange)
    (h_f : Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    (algInst : Algebra
        ↥(IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
        ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange)
    (h_amap : (@algebraMap _ _ _ _ algInst) =
        (IntermediateField.inclusion h_le).toRingHom) :
    @Module.finrank
        ↥(IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
        ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange _ _ algInst.toModule = 2 := by
  letI := algInst
  let f : W.toAffine.FunctionField := (isogOneSub_negFrobenius W hq).pullback (x_gen W)
  let gammaBar : W.toAffine.FunctionField ≃ₐ[K]
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange :=
    AlgEquiv.ofInjectiveField (isogOneSub_negFrobenius W hq).pullback
  let e_f : FractionRing (Polynomial K) ≃ₐ[K]
      ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)) :=
    (RatFunc.toFractionRingAlgEquiv K K).symm.trans
      (RatFunc.algEquivOfTranscendental (K := K) f h_f)
  let lhs_alg : FractionRing (Polynomial K) →ₐ[K]
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange :=
    (IntermediateField.inclusion h_le).comp e_f.toAlgHom
  let rhs_alg : FractionRing (Polynomial K) →ₐ[K]
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange :=
    gammaBar.toAlgHom.comp
      (IsScalarTower.toAlgHom K (FractionRing (Polynomial K)) W.toAffine.FunctionField)
  have h_eq : lhs_alg = rhs_alg := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    apply Subtype.ext
    change ((lhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X)) : W.toAffine.FunctionField) =
      ((rhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X)) : W.toAffine.FunctionField)
    have h_LHS : ((lhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X)) : W.toAffine.FunctionField) = f := by
      change ((IntermediateField.inclusion h_le)
          (e_f (algebraMap (Polynomial K) (FractionRing (Polynomial K))
            Polynomial.X)) : W.toAffine.FunctionField) = f
      rw [IntermediateField.coe_inclusion]
      change (e_f (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X)).val = f
      change (((RatFunc.toFractionRingAlgEquiv K K).symm.trans
          (RatFunc.algEquivOfTranscendental (K := K) f h_f))
          (algebraMap (Polynomial K) (FractionRing (Polynomial K))
            Polynomial.X)).val = f
      rw [AlgEquiv.trans_apply]
      have h_e3_symm_X :
          (RatFunc.toFractionRingAlgEquiv K K).symm
            (algebraMap (Polynomial K) (FractionRing (Polynomial K))
              Polynomial.X) = (RatFunc.X : RatFunc K) := by
        have h_e3_X :
            RatFunc.toFractionRingAlgEquiv K K (RatFunc.X : RatFunc K) =
            algebraMap (Polynomial K) (FractionRing (Polynomial K))
              Polynomial.X := by
          show (RatFunc.toFractionRingAlgEquiv K K) RatFunc.X = _
          simp only [RatFunc.toFractionRingAlgEquiv_apply]
          change ((algebraMap (Polynomial K) (RatFunc K)) Polynomial.X).toFractionRing = _
          rw [← RatFunc.ofFractionRing_algebraMap (K := K)]
        rw [← h_e3_X, AlgEquiv.symm_apply_apply]
      rw [h_e3_symm_X]
      change ((RatFunc.algEquivOfTranscendental (K := K) f h_f)
          (RatFunc.X : RatFunc K)).val = f
      rw [RatFunc.algEquivOfTranscendental_X]
    have h_RHS : ((rhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
        Polynomial.X)) : W.toAffine.FunctionField) = f := by
      change ((gammaBar (algebraMap (FractionRing (Polynomial K))
          W.toAffine.FunctionField
          (algebraMap (Polynomial K) (FractionRing (Polynomial K))
            Polynomial.X))) : W.toAffine.FunctionField) = f
      rw [← IsScalarTower.algebraMap_apply (Polynomial K)
        (FractionRing (Polynomial K)) W.toAffine.FunctionField]
      change ((gammaBar (x_gen W)) : W.toAffine.FunctionField) = f
      rfl
    rw [h_LHS, h_RHS]
  have hc : (algebraMap
        ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
        ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange).comp
          e_f.toRingEquiv.toRingHom =
      gammaBar.toRingEquiv.toRingHom.comp
        (algebraMap (FractionRing (Polynomial K)) W.toAffine.FunctionField) := by
    refine RingHom.ext fun r ↦ ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, h_amap]
    exact DFunLike.congr_fun h_eq r
  rw [← finrank_functionField_eq_two K W]
  exact (Algebra.finrank_eq_of_equiv_equiv e_f.toRingEquiv gammaBar.toRingEquiv hc).symm

set_option backward.isDefEq.respectTransparency false in
omit [Fintype W.toAffine.Point] in
/-- **GAP-L6 sub-leaf B3** (Silverman V.1.1 tower step): the function field is degree
`2·deg(1−π)` over `K⟮(1−π)*x⟯`. Proved via the tower `K⟮γ*x⟯ ⊆ γ.pullback.fieldRange ⊆ K(E)`:
UPPER `[K(E):γ.pullback.fieldRange] = γ.degree` (`finrank_pullback_fieldRange_eq_degree`), LOWER
`[γ.pullback.fieldRange : K⟮γ*x⟯] = 2` (`finrank_fieldRange_over_adjoin_pullback_x_eq_two`,
the `e_f`/`gammaBar` transfer), combined by `Module.finrank_mul_finrank`. -/
theorem l6_B3_tower (hq : 2 ≤ Fintype.card K) :
    Module.finrank
        (IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
        W.toAffine.FunctionField =
      2 * (isogOneSub_negFrobenius W hq).degree := by
  have h_f : Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) := by
    have hx : Transcendental K (x_gen W) := x_gen_transcendental W
    rw [Transcendental] at hx ⊢
    intro h_alg
    apply hx
    obtain ⟨q, hq_ne, hq_aeval⟩ := h_alg
    refine ⟨q, hq_ne, (isogOneSub_negFrobenius W hq).pullback_injective ?_⟩
    rwa [map_zero, ← Polynomial.aeval_algHom_apply (isogOneSub_negFrobenius W hq).pullback]
  have h_le :
      IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField) ≤
        (isogOneSub_negFrobenius W hq).pullback.fieldRange := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact ⟨x_gen W, rfl⟩
  -- TOWER: K⟮γ*x⟯ ⊆ γ.pullback.fieldRange ⊆ K(E) via the inclusion algebra
  -- (mirrors `finrank_over_frobenius_image`).  The `K⟮γ*x⟯ → fieldRange` inclusion algebra is
  -- NON-canonical; register it (`letI`) together with the derived `Module` / `Module.Free`
  -- (free over a field) and the `IsScalarTower` as concrete instances, so `finrank_mul_finrank`
  -- finds them by lookup rather than re-searching the `Algebra ↥K⟮γ*x⟯ ↥fieldRange` diamond
  -- (that search overran the default `synthInstance` budget).
  letI algInc := (IntermediateField.inclusion h_le).toRingHom.toAlgebra
  -- Register the non-canonical inclusion `Module ↥K⟮γ*x⟯ ↥fieldRange` concretely (from `algInc`)
  -- so the later `rw [← h_tower]` finds it by lookup instead of re-searching the diamond.
  letI moduleInc : Module
      ↥(IntermediateField.adjoin K
        ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
          Set W.toAffine.FunctionField))
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange := algInc.toModule
  haveI towerInst : @IsScalarTower
      ↥(IntermediateField.adjoin K
        ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
          Set W.toAffine.FunctionField))
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange W.toAffine.FunctionField
      moduleInc.toSMul _ _ :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Pin every `finrank_mul_finrank` instance over the non-canonical inclusion algebra
  -- (`algInc`) by hand (`@`), so the elaborator performs *no* instance search for the
  -- `Algebra/Module/Free ↥K⟮γ*x⟯ ↥fieldRange` diamond (which otherwise needs a raised
  -- `synthInstance` budget); `Module.Free` over a field is `of_divisionRing`.
  have h_tower := @Module.finrank_mul_finrank
      ↥(IntermediateField.adjoin K
        ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
          Set W.toAffine.FunctionField))
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange W.toAffine.FunctionField
      _ _ _ moduleInc _ _ towerInst _ _
      (Module.Free.of_divisionRing _ _) _
  rw [← h_tower, finrank_pullback_fieldRange_eq_degree W (isogOneSub_negFrobenius W hq)]
  -- Goal: finrank K⟮γ*x⟯ fieldRange * γ.degree = 2 * γ.degree. Reduce to LOWER.
  congr 1
  -- LOWER: finrank K⟮f⟯ fieldRange = 2 via the extracted `e_f`/`gammaBar` transfer; pass the
  -- registered inclusion algebra `algInc` and its compatibility (`rfl` by construction).
  convert finrank_fieldRange_over_adjoin_pullback_x_eq_two W hq h_le h_f algInc rfl using 2

/-- **SK-L6CA-HYPS `Module.Finite`** — the last HYPS hypothesis for
`finrank_gamma_pullback_x_eq_weightedPoleDegree` / `Sinf.ofIntegralClosure`: `K(E)` is
module-finite over `FractionRing K[X]` in the `LinfAt (γ*x)` (`X ↦ (γ*x)⁻¹`) framing.

The framing-bridge `Conditional.finrank_adjoin_eq_finrank_LinfAt` identifies
`finrank (FractionRing) (LinfAt (γ*x)) = finrank K⟮γ*x⟯ K(E)`, which `l6_B3_tower` evaluates to
`2·γ.degree > 0`; then `Module.finite_of_finrank_pos`. -/
theorem moduleFinite_linfAt_gamma_pullback_x (hq : 2 ≤ Fintype.card K)
    [Fact (Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)] :
    @Module.Finite (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule := by
  haveI hfreeL : @Module.Free (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule :=
    @Module.Free.of_divisionRing (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule
  have hpos : 0 < @Module.finrank (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule := by
    rw [← Conditional.finrank_adjoin_eq_finrank_LinfAt W hq, l6_B3_tower W hq]
    have hdeg : 0 < (isogOneSub_negFrobenius W hq).degree := by
      haveI hroot := isogOneSub_negFrobenius_finiteDimensional W hq
      haveI hfree : @Module.Free W.toAffine.FunctionField W.toAffine.FunctionField _ _
          (isogOneSub_negFrobenius W hq).toAlgebra.toModule :=
        @Module.Free.of_divisionRing W.toAffine.FunctionField W.toAffine.FunctionField _ _
          (isogOneSub_negFrobenius W hq).toAlgebra.toModule
      exact @Module.finrank_pos W.toAffine.FunctionField W.toAffine.FunctionField _ _
        (isogOneSub_negFrobenius W hq).toAlgebra.toModule _ hroot _ inferInstance _
    lia
  exact Module.finite_of_finrank_pos hpos


/-- **L3 pointwise witness** (Silverman V.1.1 proof, pole-order per K-rational projective
smooth point): given a 2-torsion witness, every K-rational `P : ProjectiveSmoothPoint`
satisfies `(projectiveDivisorOf((1−π)*x_gen)) P = -2` (as an integer). Three branches:
* `P = ∞`: shipped `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`
  (`PoleDivisorFallback.lean:95`).
* `P = (xT, yT)` non-2-torsion: shipped `lemma3_pole_at_T_unconditional`
  (`PoleDivisorFallback.lean:2608`).
* `P = (xT, yT)` 2-torsion: the witness hypothesis (substantive — addition-formula degeneracy). -/
theorem projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness
    (hq : 2 ≤ Fintype.card K)
    (h_two_torsion_witness : ∀ (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT),
        yT = W.toAffine.negY xT yT →
        (W_smooth W).ord_P ⟨xT, yT, h_ns⟩
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
          ((-2 : ℤ) : WithTop ℤ))
    (P : Curves.ProjectiveSmoothPoint (W_smooth W)) :
    (Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P = -2 := by
  rcases P with ⟨xT, yT, h_ns⟩ | _
  · rw [Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_affine]
    by_cases h_2tor : yT = W.toAffine.negY xT yT
    · rw [h_two_torsion_witness xT yT h_ns h_2tor]
      rfl
    · rw [Conditional.lemma3_pole_at_T_unconditional W xT yT h_ns h_2tor hq]
      rfl
  · rw [Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_infinity,
        ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen W hq]
    rfl

/-- **L3 witness-parametric** (Silverman V.1.1 proof, pole-order per K-rational point):
given a 2-torsion witness `h_two_torsion_witness` discharging `ord_T (γ.pullback x_gen) = -2`
at every K-rational 2-torsion point `T = (xT, yT)` (where `yT = negY xT yT`), conclude L3.

All three branches give `ord_P (γ.pullback x_gen) = -2`, hence the divisor value at `P`
(which is `ord_P f .untopD 0 = -2 : ℤ`) yields `(D P).toNat = 0` and `(-(D P)).toNat = 2`. -/
theorem l6_pole_orders_of_two_torsion_witness (hq : 2 ≤ Fintype.card K)
    (h_two_torsion_witness : ∀ (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT),
        yT = W.toAffine.negY xT yT →
        (W_smooth W).ord_P ⟨xT, yT, h_ns⟩
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
          ((-2 : ℤ) : WithTop ℤ)) :
    ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P).toNat = 0 ∧
      (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat = 2 := by
  intro P _hP_in_support
  rw [projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness
      W hq h_two_torsion_witness P]
  exact ⟨rfl, rfl⟩

/- NOTE: L4 (support cardinality) witness-parametric version: the inline support = univ
argument requires reconciling the project's `W_smooth W` synonym with the shipped
`Fintype.card_projectiveSmoothPoint_eq_pointCount` lemma's `(⟨W.toAffine⟩ : SmoothPlaneCurve K)`
form. The two are definitionally equal but instance unification hits a heartbeat wall
inside this proof. Deferred to the `L6Witnesses` layer where the `⟨W.toAffine⟩` form is
already adopted (`support_card_eq_pointCount_of_per_point_witness` at
`L6Witnesses.lean:129` is the analogous shipped composer). -/

/-- **GAP-L6 Lemma-5 witness (a): uniform pole orders** — every point in the pole-divisor support
of `(1−π)*x` has zero-order 0 and pole-order 2 (the F_q-rational kernel points are double poles).

Discharged via `l6_pole_orders_of_two_torsion_witness` + the shipped 2-tor witness
`lemma3_pole_at_T_at_2tor` (`PoleDivisor2Tor.lean`). -/
theorem l6_pole_orders (hq : 2 ≤ Fintype.card K) :
    ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P).toNat = 0 ∧
      (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat = 2 :=
  l6_pole_orders_of_two_torsion_witness W hq
    (fun xT yT h_ns h_2_tor ↦
      lemma3_pole_at_T_at_2tor W xT yT h_ns h_2_tor hq)

/-- **GAP-L6 Lemma-5 witness (b): support cardinality** — the pole-divisor support has exactly
`#E(F_q)` points.

Discharged via `Conditional.l6_support_card_of_two_torsion_witness` + the shipped
2-tor witness `lemma3_pole_at_T_at_2tor`. -/
theorem l6_support_card (hq : 2 ≤ Fintype.card K) :
    ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.card =
      pointCount W.toAffine :=
  Conditional.l6_support_card_of_two_torsion_witness W hq
    (fun xT yT h_ns h_2_tor ↦
      lemma3_pole_at_T_at_2tor W xT yT h_ns h_2_tor hq)

/-- **GAP-L6 sub-leaf Lemma 5** (pole-divisor sum = `2·#E`), now wired to the shipped closer
`Conditional.lemma5_of_pole_orders_and_support_card` from the two pole-order/support witnesses. -/
theorem l6_lemma5 (hq : 2 ≤ Fintype.card K) :
    ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
      (fun P ↦ (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) =
      2 * pointCount W.toAffine :=
  Conditional.lemma5_of_pole_orders_and_support_card W hq
    (l6_pole_orders W hq) (l6_support_card W hq)

/-- **V.1.3 EASY INEQUALITY — `#E(F_q) ≤ deg(1−π)`** (deep pass 2026-05-29, Option-B residual
split; AXIOM-CLEAN, NON-CIRCULAR).

The *easy half* of the V.1.3 sharp residual `isogOneSub_negFrobenius_degree_eq_pointCount`
(`deg(1−π) = pointCount`), proved **independently of the deep place↔point bijection** (the
sorried `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount` cone was deleted 2026-06-11; the
clean closure is `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower` below). It
reduced the open residual to the reverse inequality `deg(1−π) ≤ pointCount` (the "no extra
primes over `(X)`" direction, since closed via the embeddings classification).

**Proof (pure monotonicity over the fundamental ramification identity):**
* TOTAL weighted sum `Σ_{P ∈ primesOverFinset (X)} e_P · f_P = [K(E):K((1−π)*x)] = 2·deg(1−π)`
  — the fundamental identity (`finrank_gamma_pullback_x_eq_weightedPoleDegree` ∘
  `finrank_adjoin_eq_finrank_LinfAt`) composed with the tower step `l6_B3_tower`, all
  axiom-clean.
* IMAGE weighted sum: the kernel-to-prime map `T ↦ P_T := bridge_Bi_kernelToPrime_v2` injects
  `ker(1−π)` into `primesOverFinset (X)` (backward inclusion
  `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, injectivity
  `Sinf_kernelToPrime_v2_injective`), each kernel-prime contributes `e_{P_T}·f_{P_T} = 2·1 = 2`
  (`bridge_Biii_ord_eq_neg_two_v2` + `bridge_Biv_inertia_eq_one_v2`), and `#ker(1−π) = pointCount`
  (`kernel_eq_top_of_hom_eq_id_sub_frobenius`). So `Σ_{image} e·f = 2·pointCount`.
* MONOTONICITY: `image ⊆ primesOverFinset` with all terms `≥ 0` gives `2·pointCount ≤ 2·deg`,
  hence `pointCount ≤ deg`.

**Why the reverse inequality is NOT extractable this way (and Option B does not close it).**
The kernel primes have ramification index **`e = 2`** (the double pole of `x` at `O`,
`bridge_Biii_ord_eq_neg_two_v2`), because `primesOverFinset (X)` lives in the tower over
`K((1−π)*x)` (degree `2·deg`), *not* over the isogeny `1−π` itself; so "separable ⇒ unramified
⇒ `e = 1`" does not apply to THIS `Σ e_P·f_P`. The reverse bound `Σ_{total} e·f ≤ 2·pointCount`
needs `image = primesOverFinset` (the complement empty), i.e. the prime-over-`(X)`
surjectivity (the now-deleted `bridge_Bii_surjective_v2` /
`Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem` cone) — the genuinely-deep "no extra
primes over `(X)`" content (the K-rationality/inertia-1 of an arbitrary bare prime over
`(X)`), which over a non-algebraically-closed finite `K` requires `[IsAlgClosed]`/Galois-
descent infrastructure absent from the project; V.1.3 instead closed via the embeddings
classification (`emb_le_card_kernel`). -/
theorem isogOneSub_negFrobenius_pointCount_le_degree (hq : 2 ≤ Fintype.card K) :
    pointCount W.toAffine ≤ (isogOneSub_negFrobenius W hq).degree := by
  obtain ⟨p, _, ⟨_, _⟩, hp_prime, _⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI hfact := Conditional.fact_transcendental_gamma_pullback_x_inv W hq
  haveI hmf := moduleFinite_linfAt_gamma_pullback_x W hq
  haveI hsep := Conditional.K_E_separable_over_LinfAt_gamma_pullback_x_gen W p hq
  -- Build the `Sinf` data (the function-field place machinery at infinity for `f = (1−π)*x`).
  let data : Curves.RamificationAtInfinity.Sinf (k := K)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :=
    @Curves.RamificationAtInfinity.Sinf.ofIntegralClosure K _ W.toAffine.FunctionField _ _
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) hfact hmf hsep
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algPoly
  letI := data.isTorsionFree
  letI := data.moduleFinite
  haveI : Finite W.toAffine.Point := Finite.of_fintype _
  haveI : Finite (isogOneSub_negFrobenius W hq).kernel := inferInstance
  haveI : Fintype (isogOneSub_negFrobenius W hq).kernel := Fintype.ofFinite _
  haveI hmax : (Curves.RamificationAtInfinity.xIdeal (k := K)).IsMaximal :=
    Curves.RamificationAtInfinity.xIdeal_isMaximal
  -- TOTAL weighted sum = 2 · deg (fundamental identity ∘ `l6_B3_tower`, axiom-clean).
  have h_total :
      ∑ P ∈ primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        (-(data.ordAt P)).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P =
        2 * (isogOneSub_negFrobenius W hq).degree := by
    rw [← Conditional.finrank_gamma_pullback_x_eq_weightedPoleDegree W hq hmf data,
        ← Conditional.finrank_adjoin_eq_finrank_LinfAt W hq, l6_B3_tower W hq]
  -- IMAGE of the kernel-to-prime map `T ↦ P_T`.
  set image : Finset (Ideal data.carrier) :=
    (Finset.univ : Finset (isogOneSub_negFrobenius W hq).kernel).image
      (fun T ↦ bridge_Bi_kernelToPrime_v2 W hq data T) with himage_def
  have h_image_sub : image ⊆
      primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier := by
    intro Q hQ
    rw [himage_def, Finset.mem_image] at hQ
    obtain ⟨T, _, rfl⟩ := hQ
    exact bridge_Bii_kernelToPrime_mem_primesOverFinset_v2 W hq data T
  have h_card_kernel :
      Nat.card (isogOneSub_negFrobenius W hq).kernel = pointCount W.toAffine := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W
      (isogOneSub_negFrobenius W hq) rfl, AddSubgroup.card_top]
    exact Nat.card_eq_fintype_card
  -- IMAGE weighted sum = 2 · pointCount (each kernel-prime contributes `e·f = 2·1 = 2`).
  have h_image_sum :
      ∑ Q ∈ image, (-(data.ordAt Q)).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q =
        2 * pointCount W.toAffine := by
    rw [himage_def,
      Finset.sum_image (fun T₁ _ T₂ _ h_eq ↦
        Sinf_kernelToPrime_v2_injective W hq data h_eq)]
    have h_each : ∀ T : (isogOneSub_negFrobenius W hq).kernel,
        (-(data.ordAt (bridge_Bi_kernelToPrime_v2 W hq data T))).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K))
            (bridge_Bi_kernelToPrime_v2 W hq data T) = 2 := by
      intro T
      rw [bridge_Biii_ord_eq_neg_two_v2 W hq data T,
          bridge_Biv_inertia_eq_one_v2 W hq data T]
      decide
    simp only [h_each]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ,
      ← Nat.card_eq_fintype_card, h_card_kernel]
    ring
  -- MONOTONICITY over `image ⊆ primesOverFinset` (all terms ≥ 0): `Σ_image ≤ Σ_total`.
  have h_mono :
      ∑ Q ∈ image, (-(data.ordAt Q)).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q ≤
        ∑ P ∈ primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
          (-(data.ordAt P)).toNat *
            Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P :=
    Finset.sum_le_sum_of_subset_of_nonneg h_image_sub (fun _ _ _ ↦ Nat.zero_le _)
  -- Combine: `2·pointCount ≤ 2·deg`, cancel the `2`.
  rw [h_image_sum, h_total] at h_mono
  lia

/- V.1.3 sharp residual — `degree = pointCount` (deep pass 2026-05-28; updated 2026-05-28
round-5 expert review)

The DEEP pass closure isolates the V.1.3 obligation as the **single sharp sub-fact**
`(1−π).degree = pointCount` (Silverman III.4.10c, "separable isogeny degree = kernel size"
for our specific γ = 1−π). All three V.1.3 targets —
the sum-of-inertia identity (the sorried L6Witnesses form was deleted 2026-06-11; the live
form is `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower` below),
`sepDegree_oneSub_eq_pointCount`, `ker_deg_skeleton` — reduce to this single statement, via:

* `sepDegree γ = degree γ` (separable + finite-dim, `isSeparable_iff_sepDegree_eq_degree`, shipped).
* `Nat.card γ.kernel = pointCount` (kernel = ⊤ from `kernel_eq_top_of_hom_eq_id_sub_frobenius`,
  axiom-clean).
* The fundamental identity `Σ e_P · f_P = [K(E):K(γ*x)] = 2·γ.degree`
  (`l6_B3_tower` + `finrank_adjoin_eq_finrank_LinfAt` +
  `finrank_gamma_pullback_x_eq_weightedPoleDegree`, all shipped axiom-clean) combined with
  kernel-prime inertia/ramification (`bridge_Biii_ord_eq_neg_two_v2`,
  `bridge_Biv_inertia_eq_one_v2`, shipped) and the kernel-to-prime injection
  (`bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_kernelToPrime_v2_injective`, shipped)
  to squeeze `image = primesOverFinset` and hence `Σ f_P = pointCount`.

**[2026-05-28 ROUND-5 expert-review update.]** The WireUpPrep
`WireUpPrep.RouteB.degree_isogOneSub_negFrobenius_eq_pointCount`
route is **NOT a viable closure path** — it consumes `oneSubFrob_baseChange_coordHom` which
requires the impossible `CoordHom : R → R` for `1 − π` (see the B2 annotation on
`HasseWeil.RouteB.nReduced_R_div_D_sq` in `AdditionPullback/PointMap.lean` for the
counterexample). That route is superseded.

**The L6_B3_tower path remains live and is now the canonical reduction.** Concretely:

  Σ e_P · f_P over primes of `Sinf` over `(X)`  =  [K(E) : K(f)]  =  2 · deg(1−π)

(first equality: Mathlib's `Ideal.sum_ramification_inertia` for Dedekind domains; second
equality: `l6_B3_tower`, axiom-clean). Combined with the SQUEEZE composer
`Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness` (axiom-clean), V.1.3's
`degree = pointCount` is **equivalent** to the IDENTITY

  Σ e_P · f_P over primes of `Sinf` over `(X)`  =  2 · pointCount

proved **independently** (i.e. not via `degree = pointCount`). And by the kernel-prime
contribution analysis (each kernel prime contributes `e · f = 2 · 1 = 2`, shipped axiom-clean
via the bridge lemmas), this identity is in turn equivalent to:

  **(V.1.3 sharp residual, round-5 form):**
  every prime `P` of `Sinf` over `(X)` is in the image of `bridge_Bi_kernelToPrime_v2`,
  i.e. is the kernel-prime of some `T ∈ ker(1−π)`. Equivalently: there are no "extra" primes
  over `(X)` beyond the kernel primes.

Mathematical content (Silverman II.2.4 — the function-field ↔ closed-point dictionary over a
non-closed base field): every prime `P` over `(X)` in `Sinf` corresponds to a place of `K(E)`
where `f = (1−π)*x` has a pole. Such a place corresponds (by II.2.4) to a closed point of the
projective curve `E` where `f` has a pole. Since the only pole of `x : E → P¹` is `O`, a closed
point where `f = x∘(1−π)` has a pole satisfies `(1−π)(P) = O`, i.e. `P ∈ ker(1−π)`. Over `K`,
closed points of the kernel are the `K`-rational kernel points = `E(F_q)` (= `pointCount`).

Formalization residual: the place-vs-closed-point dictionary over `K` (not `K̄`), restricted to
the pole-locus of `f`. The project's `smoothPointEquivHeightOneSpectrum` is currently shipped
only over algebraically closed `L`; the analog over `K` needs a Galois-descent argument or
direct construction (all closed points where `f` has a pole are `K`-rational since the kernel
is `K`-rational).
-/

/- V.1.3 sharp residual via the R2 embeddings-classification route
(deep pass 2026-05-29, reviewer round 9)

The dead/circular L6_B3_tower place↔point route (which required the impossible `CoordHom`
for `1 − π`, see the casualty note below) is **superseded** by the R2 route. Set
`γ := 1 − π = isogOneSub_negFrobenius W hq`, `L := K(E) = W.toAffine.FunctionField`,
`M := γ*K(E)` (the source field acting through `γ.pullback`), `Ω := AlgebraicClosure L`.
Then `γ` is separable (`isogOneSub_negFrobenius_isSeparable`) and finite
(`isogOneSub_negFrobenius_finiteDimensional`), so by Mathlib's *definition* of
`Field.finSepDegree` together with `Field.finSepDegree_eq_finrank_of_isSeparable`:

  `deg γ = sepDegree γ = #(L →ₐ[M] Ω)`     -- the embedding count (FREE, mathlib).

So `deg γ = pointCount` reduces — axiom-clean, via `Isogeny.sepDegree_eq_card_emb`,
`Isogeny.card_kernel_eq_degree_of_sepDegree_eq_card_kernel`, and the shipped structural
facts `isogOneSub_negFrobenius_toAddMonoidHom` (γ's point map is `id − π`) +
`degree_eq_pointCount_of_card_kernel_eq_degree` (`#ker γ = pointCount` from `ker γ = ⊤`) —
to the **single clean embedding↔kernel count**

  `#(L →ₐ[M] Ω) = #ker γ`,   i.e.   `sepDegree γ = Nat.card γ.kernel`,

which is `isogOneSub_negFrobenius_sepDegree_eq_card_kernel` below.

**Why this is the right residual (NOT circular, NOT IsGalois-first).** The count step
`deg = #Emb` is pure mathlib and does NOT presuppose `IsGalois`/normality; only the *bijection*
`Emb ≃ ker γ` remains. That bijection is the classical embedding-classification (Silverman
III.4.10c): each `σ : L →ₐ[M] Ω` is the translation `τ_T` by `T = (σ x_gen, σ y_gen) − P_gen`,
which lies in `ker γ` because `σ` fixes `M = γ*K(E)` (so `γ(Q_σ) = γ(P_gen)`); over `K` the
geometric kernel points are exactly the `F_q`-rational ones (`FrobeniusFixedPoint`). The
asset `translateAlgEquivOfPoint` (axiom-clean) realises the reverse map `T ↦ τ_T*`.

OPEN sub-fact: the bijection's **surjectivity** — every `M`-embedding is a translation `τ_T`
(equivalently `#Emb ≤ #ker`, the reverse of the shipped `pointCount ≤ degree`). Building it
needs the generic point placed into `Ω`, the curve group law over `Ω`, the covariance
`τ_T ∘ γ* = γ*` for `T ∈ ker γ` (Step 2, absent), and the over-`Ω` Frobenius-fixed = K-rational
identification (Step 4) — none currently in the project. -/

/- V.1.3 sharp residual — embedding↔kernel count (R2 route, reviewer round 9)

The number of `γ*K(E)`-algebra embeddings of `K(E)` into `AlgebraicClosure K(E)` equals the
size of `ker γ`, for `γ = 1 − π`. By `Isogeny.sepDegree_eq_card_emb` this is *definitionally*

  `#(K(E) →ₐ[γ*K(E)] AlgebraicClosure K(E)) = #ker γ`.

This is the **sole** remaining gap of V.1.3: `isogOneSub_negFrobenius_degree_eq_pointCount`
closes from it axiom-clean (separability ⇒ `sepDegree = degree`; `ker γ = ⊤` ⇒
`#ker γ = pointCount`). The count `deg γ = #Emb` is free from mathlib (`AlgHom.card` /
`finSepDegree_eq_finrank_of_isSeparable`); the residual is the classification bijection
`Emb ≃ ker γ` (Silverman III.4.10c), whose open half is surjectivity ("every embedding is a
translation `τ_T`"). The reverse-map asset `translateAlgEquivOfPoint` is shipped axiom-clean.

NOT to be proved via `IsGalois` first (circular if done by cardinality): count embeddings
`Hom_M(L, Ω)`, not automorphisms.

#### Closeable bricks for the embedding↔kernel count (deep pass 2026-05-29, round 9)

The residual `isogOneSub_negFrobenius_sepDegree_eq_card_kernel` is `#Emb = #ker` with
`Emb := (K(E) →ₐ[γ*K(E)] AlgebraicClosure K(E))`. It splits into two inequalities:

* **EASY half `#ker ≤ #Emb`** — `isogOneSub_negFrobenius_card_kernel_le_sepDegree` below,
  proved axiom-clean from the *shipped* `isogOneSub_negFrobenius_pointCount_le_degree`
  (`pointCount ≤ deg`) together with separability (`sepDegree = deg`) and `ker γ = ⊤`
  (`#ker = pointCount`). This is the classification's injective direction
  (`ker ↪ Emb`, `T ↦ τ_T`) in counting form.
* **HARD half `#Emb ≤ #ker`** — equivalently `deg γ ≤ pointCount` (since `#Emb = sepDegree
  = deg` and `#ker = pointCount`), i.e. the classification's surjectivity ("every
  `γ*K(E)`-embedding is a translation `τ_T`"). This is the SOLE remaining content and it is
  genuinely equivalent to the full theorem `deg γ = pointCount`; see the precise gap analysis
  in `isogOneSub_negFrobenius_emb_le_card_kernel_gap` below.

The bricks `isogOneSub_negFrobenius_sepDegree_eq_card_emb` (explicit `#Emb` form) and
`isogOneSub_negFrobenius_embToPointOmega` (the forward coordinate map `σ ↦ (σ x_gen, σ y_gen)`
as an `Ω`-point of `E`) make the reduction and the classification's forward leg concrete and
reusable. All are axiom-clean. -/

/-- **Brick (explicit embedding form).** The separable degree of `γ = 1 − π` is the number of
`γ*K(E)`-algebra embeddings of `K(E)` into `AlgebraicClosure K(E)` — a *definitional* unfold of
`Field.finSepDegree` (re-export of the shipped `Isogeny.sepDegree_eq_card_emb` specialised to
`γ`). Here the base algebra is `γ.toAlgebra` (`K(E)` acting on `K(E)` through `γ.pullback`), so
`Emb` is exactly the embeddings fixing `M = γ*K(E)`. Axiom-clean. -/
theorem isogOneSub_negFrobenius_sepDegree_eq_card_emb (hq : 2 ≤ Fintype.card K) :
    letI := (isogOneSub_negFrobenius W hq).toAlgebra
    (isogOneSub_negFrobenius W hq).sepDegree =
      Nat.card (W.toAffine.FunctionField →ₐ[W.toAffine.FunctionField]
        AlgebraicClosure W.toAffine.FunctionField) :=
  Isogeny.sepDegree_eq_card_emb (isogOneSub_negFrobenius W hq)

/-- **Brick (EASY half — `#ker ≤ #Emb`).** The kernel of `γ = 1 − π` injects into the
`γ*K(E)`-embedding set, in counting form: `#ker γ ≤ sepDegree γ` (`= #Emb`). PROVED axiom-clean
from the **shipped** easy inequality `isogOneSub_negFrobenius_pointCount_le_degree`
(`pointCount ≤ deg`, the kernel-prime monotonicity over the fundamental ramification identity),
combined with separability (`sepDegree = deg`, via `isSeparable_iff_sepDegree_eq_degree`) and
`ker γ = ⊤` (`#ker = pointCount`, via `kernel_eq_top_of_hom_eq_id_sub_frobenius`).

This is the classification's injective leg `ker ↪ Emb` (`T ↦ τ_T`, the shipped axiom-clean
`translateAlgEquivOfPoint`, which is injective by `translateAlgEquivOfPoint_injective`) recast
as a cardinality bound. It reduces `isogOneSub_negFrobenius_sepDegree_eq_card_kernel` to the
single reverse bound `#Emb ≤ #ker`. -/
theorem isogOneSub_negFrobenius_card_kernel_le_sepDegree (hq : 2 ≤ Fintype.card K) :
    Nat.card (isogOneSub_negFrobenius W hq).kernel ≤
      (isogOneSub_negFrobenius W hq).sepDegree := by
  obtain ⟨p, _, ⟨_, _⟩, hp_prime, _⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  -- `#ker γ = pointCount` (kernel = ⊤, rational-point shape).
  have h_ker_pc :
      Nat.card (isogOneSub_negFrobenius W hq).kernel = pointCount W.toAffine := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W
      (isogOneSub_negFrobenius W hq) rfl, AddSubgroup.card_top]
    exact Nat.card_eq_fintype_card
  -- `sepDegree γ = deg γ` (separable + finite-dimensional).
  have h_sep_deg :
      (isogOneSub_negFrobenius W hq).sepDegree =
        (isogOneSub_negFrobenius W hq).degree :=
    (Isogeny.isSeparable_iff_sepDegree_eq_degree (isogOneSub_negFrobenius W hq)
      (isogOneSub_negFrobenius_finiteDimensional W hq)).mp
      (isogOneSub_negFrobenius_isSeparable W p hq)
  rw [h_ker_pc, h_sep_deg]
  exact isogOneSub_negFrobenius_pointCount_le_degree W hq

/-- **Brick (classification forward leg — `σ ↦ Q_σ`).** Each `K`-algebra embedding
`σ : K(E) →ₐ[K] AlgebraicClosure K(E)` determines the `Ω`-point of `E` (`Ω` the chosen
algebraic closure) with coordinates `(σ x_gen, σ y_gen)`, namely the image of the generic
point `(x_gen, y_gen) ∈ (W_KE).Point` under `Affine.Point.map σ`. Together with
`algHom_ext_x_y_gen` (an `F`-embedding of `K(E)` is *determined* by its values on `x_gen`,
`y_gen`) this is the curve-side half of the embeddings↔points dictionary (Silverman III.4.2):
`σ ↦ Q_σ` is injective on coordinates, and the Weierstrass equation holds at `Q_σ` by
construction (`map_nonsingular`). Axiom-clean.

This is the forward map of the classification bijection. Landing `Q_σ − P_gen` in `ker γ`
(hence descending to `E(F_q)`) is the missing over-`Ω` content — see
`isogOneSub_negFrobenius_emb_le_card_kernel_gap`. -/
noncomputable def isogOneSub_negFrobenius_embToPointOmega (hq : 2 ≤ Fintype.card K)
    (σ : W.toAffine.FunctionField →ₐ[K] AlgebraicClosure W.toAffine.FunctionField) :
    ((W_KE W).map σ.toRingHom).toAffine.Point :=
  Affine.Point.map σ.toRingHom σ.toRingHom.injective (genericPoint W)

@[simp] theorem isogOneSub_negFrobenius_embToPointOmega_eq (hq : 2 ≤ Fintype.card K)
    (σ : W.toAffine.FunctionField →ₐ[K] AlgebraicClosure W.toAffine.FunctionField) :
    isogOneSub_negFrobenius_embToPointOmega W hq σ =
      Affine.Point.some (σ (x_gen W)) (σ (y_gen W))
        ((WeierstrassCurve.Affine.map_nonsingular (W_KE W).toAffine σ.toRingHom.injective
          (x_gen W) (y_gen W)).mpr
          (generic_nonsingular W)) :=
  rfl

/- Closeable bricks for the surjectivity residual (deep pass 2026-05-29)

The HARD half `#Emb ≤ #ker` (surjectivity of `T ↦ τ_T`, Silverman III.4.10c) is assembled
from the following AXIOM-CLEAN bricks, each of which closes the corresponding step (A)–(E) of
the embeddings↔points dictionary. They are stated standalone so the remaining assembly gap is
explicit and the proved content is reusable.

These bricks **sharpen and partially refute** the earlier round-9 gap note: step (E) (the
over-`Ω` Frobenius descent) does **not** need `[IsAlgClosed Ω]` — it holds over *any* field
extension `L/K` of the finite base (`frobenius_fixedPoint_iff_mem_baseField_gen`), and the
fibre precondition of step (C) is *free* from `σ.commutes` (`embFixesPullbackRange`). The
remaining gap is the point-level assembly (B)+(D)+(F): forming `T_σ := Q_σ − ι(P_gen)` in the
common group `E(Ω) = (W.baseChange Ω).Point` via `embCurveBaseChange`, proving its
Frobenius-fixedness (so step (E) lands it in `E(F_q) = ker γ`), and matching `σ = τ_{T_σ}`. -/

/-- **Brick (E) — Frobenius fixed-locus over an arbitrary extension.** For a finite field `K`
with `q = #K`, an element `a` of *any* field extension `L/K` satisfies `a ^ q = a` iff it lies
in the image of `K`. (Generalises `HasseWeil.frobenius_fixed_iff_mem_baseField`, which is keyed
to `L = AlgebraicClosure K`, to an arbitrary `[Algebra K L]` field `L`; the proof needs no
`[IsAlgClosed L]` since the `q` images of `K` are already `q` distinct roots of the degree-`q`
polynomial `X^q − X`, forcing equality of the two finsets by cardinality.)

This is the coordinate engine of the over-`Ω` descent "Frobenius-fixed ⟹ `F_q`-rational"
(Silverman V.1.1 / the kernel-over-`Ω` step), now available for `L = AlgebraicClosure K(E)`. -/
theorem frobenius_fixedPoint_iff_mem_baseField_gen {L : Type*} [Field L] [Algebra K L]
    (a : L) :
    a ^ Fintype.card K = a ↔ a ∈ Set.range (algebraMap K L) := by
  classical
  set q := Fintype.card K with hq_def
  set f : Polynomial L := Polynomial.X ^ q - Polynomial.X with hf_def
  have hf_ne : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card
  have hf_deg : f.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq L Fintype.one_lt_card
  have mem_roots_iff : ∀ b : L, b ∈ f.roots.toFinset ↔ b ^ q = b := by
    intro b
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def]
    simp only [hf_def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  have mem_base_iff : ∀ b : L,
      b ∈ Finset.univ.image (algebraMap K L) ↔ b ∈ Set.range (algebraMap K L) := by
    intro b
    simp [Set.mem_range]
  have base_sub : Finset.univ.image (algebraMap K L) ⊆ f.roots.toFinset := by
    intro b hb
    rw [mem_base_iff] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [mem_roots_iff, ← map_pow, FiniteField.pow_card]
  have card_base : (Finset.univ.image (algebraMap K L)).card = q := by
    rw [Finset.card_image_of_injective _ (algebraMap K L).injective, Finset.card_univ]
  have card_roots : f.roots.toFinset.card = q := by
    apply le_antisymm
    · calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
        _ ≤ f.natDegree := Polynomial.card_roots' _
        _ = q := hf_deg
    · rw [← card_base]
      exact Finset.card_le_card base_sub
  have heq : Finset.univ.image (algebraMap K L) = f.roots.toFinset :=
    Finset.eq_of_subset_of_card_le base_sub (le_of_eq (by rw [card_roots, card_base]))
  rw [← mem_roots_iff, ← mem_base_iff, heq]

/-- **Brick (A) — embeddings into `Ω` are determined by `x_gen, y_gen`.** Two `K`-algebra
embeddings of `K(E)` into *any* `K`-algebra field `Ω` agreeing on `x_gen` and `y_gen` are
equal. (Generalises the shipped `algHom_ext_x_y_gen`, whose codomain is `K(E)`, to an arbitrary
codomain `Ω`; same reduction chain `IsLocalization.algHom_ext` → `AdjoinRoot.algHom_ext'` →
`Polynomial.algHom_ext`.) This is the injectivity of the forward map `σ ↦ Q_σ`
(`isogOneSub_negFrobenius_embToPointOmega`): if `Q_{σ₁} = Q_{σ₂}` then `σ₁ = σ₂`. -/
theorem algHom_ext_x_y_gen_omega {Ω : Type*} [Field Ω] [Algebra K Ω]
    {ψ₁ ψ₂ : W.toAffine.FunctionField →ₐ[K] Ω}
    (hx : ψ₁ (x_gen W) = ψ₂ (x_gen W)) (hy : ψ₁ (y_gen W) = ψ₂ (y_gen W)) :
    ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W.toAffine.CoordinateRing)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ψ₁ (algebraMap _ W.toAffine.FunctionField (algebraMap _ _ Polynomial.X)) =
      ψ₂ (algebraMap _ W.toAffine.FunctionField (algebraMap _ _ Polynomial.X))
    exact hx
  · change ψ₁ (algebraMap _ W.toAffine.FunctionField (AdjoinRoot.root W.toAffine.polynomial)) =
      ψ₂ (algebraMap _ W.toAffine.FunctionField (AdjoinRoot.root W.toAffine.polynomial))
    exact hy

/-- **Brick (B-base) — the curve over `Ω` is the base change of `W`.** For any `K`-algebra
embedding `σ : K(E) →ₐ[K] Ω`, mapping `W_KE = W.baseChange K(E)` along `σ` returns
`W.baseChange Ω`. (Direct from `WeierstrassCurve.map_map` and `σ.commutes`: the composite
`σ ∘ algebraMap K K(E) = algebraMap K Ω`.) This resolves the σ-dependent codomain of the
forward map: every `Q_σ = (σ x_gen, σ y_gen)` lands in the *common* group
`E(Ω) = (W.baseChange Ω).toAffine.Point`, the prerequisite for forming the torsor
`T_σ := Q_σ − ι(P_gen)` and applying the curve group law over `Ω`. -/
theorem embCurveBaseChange {Ω : Type*} [Field Ω] [Algebra K Ω] [DecidableEq Ω]
    (σ : W.toAffine.FunctionField →ₐ[K] Ω) :
    (W_KE W).map σ.toRingHom = W.baseChange Ω := by
  unfold W_KE
  rw [WeierstrassCurve.map_map]
  congr 1
  ext x
  change σ.toRingHom (algebraMap K W.toAffine.FunctionField x) = algebraMap K Ω x
  rw [show (algebraMap K W.toAffine.FunctionField) =
    (Algebra.ofId K W.toAffine.FunctionField).toRingHom from rfl]
  exact σ.commutes x

/-- **Brick (C) — every `M`-embedding fixes `M = γ*K(E)`.** For `γ = 1 − π`, an
`M`-algebra embedding `σ : K(E) →ₐ[M] Ω` (`M = γ.pullback K(E)`, `Ω = AlgebraicClosure K(E)`)
agrees with the canonical inclusion `ι : K(E) → Ω` on the image of `γ.pullback`: for every `z`,
`σ (γ.pullback z) = ι z` (here `ι z = algebraMap_M Ω z`, the `M`-structure map of `Ω`). This is
*free* from `σ.commutes` — the defining property of an `M`-algebra hom — and is the fibre
precondition of the classification: it forces `γ(Q_σ) = γ(P_gen)` in `E(Ω)` (equivalently the
torsor `T_σ ∈ ker γ` over `Ω`). -/
theorem embFixesPullbackRange (hq : 2 ≤ Fintype.card K)
    (σ : letI := (isogOneSub_negFrobenius W hq).toAlgebra
      (W.toAffine.FunctionField →ₐ[W.toAffine.FunctionField]
        AlgebraicClosure W.toAffine.FunctionField))
    (z : W.toAffine.FunctionField) :
    letI _alg := (isogOneSub_negFrobenius W hq).toAlgebra
    σ ((isogOneSub_negFrobenius W hq).pullback z) =
      (algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)) z := by
  letI := (isogOneSub_negFrobenius W hq).toAlgebra
  exact σ.commutes z

/-- **Brick (C, agreement form).** All `M`-embeddings agree on `M = γ*K(E)`: for any two
`σ₁, σ₂` and any `z`, `σ₁ (γ.pullback z) = σ₂ (γ.pullback z)`. (Both equal the canonical
`ι (γ.pullback z)` by `embFixesPullbackRange`.) The classification's well-definedness:
embeddings are distinguished only by their behaviour off `M`. -/
theorem embAgreeOnPullbackRange (hq : 2 ≤ Fintype.card K)
    (σ₁ σ₂ : letI := (isogOneSub_negFrobenius W hq).toAlgebra
      (W.toAffine.FunctionField →ₐ[W.toAffine.FunctionField]
        AlgebraicClosure W.toAffine.FunctionField))
    (z : W.toAffine.FunctionField) :
    σ₁ ((isogOneSub_negFrobenius W hq).pullback z) =
      σ₂ ((isogOneSub_negFrobenius W hq).pullback z) := by
  letI := (isogOneSub_negFrobenius W hq).toAlgebra
  exact (σ₁.commutes z).trans (σ₂.commutes z).symm

/-- **Brick (A→K view) — an `M`-embedding restricts to a `K`-algebra hom.** The underlying
ring hom of an `M`-embedding `σ : K(E) →ₐ[M] Ω` (`M = γ*K(E)`) packages as a `K`-algebra hom
`K(E) →ₐ[K] Ω`, via the scalar tower `K → M → Ω` (`γ.pullback` fixes `algebraMap K K(E)`). This
is the bridge that lets the `K`-typed forward map `isogOneSub_negFrobenius_embToPointOmega` and
the determinacy brick `algHom_ext_x_y_gen_omega` apply to the `M`-typed embeddings counted by
`sepDegree`. Axiom-clean. -/
noncomputable def embRestrictScalarsK (hq : 2 ≤ Fintype.card K)
    (σ : letI := (isogOneSub_negFrobenius W hq).toAlgebra
      (W.toAffine.FunctionField →ₐ[W.toAffine.FunctionField]
        AlgebraicClosure W.toAffine.FunctionField)) :
    W.toAffine.FunctionField →ₐ[K] AlgebraicClosure W.toAffine.FunctionField :=
  letI := (isogOneSub_negFrobenius W hq).toAlgebra
  { toRingHom := σ.toRingHom
    commutes' := fun c ↦ by
      change σ (algebraMap K W.toAffine.FunctionField c) =
        algebraMap K (AlgebraicClosure W.toAffine.FunctionField) c
      calc σ (algebraMap K W.toAffine.FunctionField c)
          = σ ((isogOneSub_negFrobenius W hq).pullback
              (algebraMap K W.toAffine.FunctionField c)) := by rw [AlgHom.commutes]
        _ = algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)
              (algebraMap K W.toAffine.FunctionField c) := σ.commutes _
        _ = algebraMap K (AlgebraicClosure W.toAffine.FunctionField) c := by
            rw [← IsScalarTower.algebraMap_apply] }

/-- **Precise remaining gap — HARD half `#Emb ≤ #ker` (surjectivity of the classification).**

After `isogOneSub_negFrobenius_card_kernel_le_sepDegree` (the easy half, axiom-clean), the
residual `isogOneSub_negFrobenius_sepDegree_eq_card_kernel` is *exactly* the reverse bound

  `#(K(E) →ₐ[γ*K(E)] AlgebraicClosure K(E))  ≤  #ker γ`.

Because `#Emb = sepDegree γ = deg γ` (separability) and `#ker γ = pointCount` (`ker γ = ⊤`),
this bound is **equivalent to `deg γ ≤ pointCount`** — the genuinely sharp half of
`isogOneSub_negFrobenius_degree_eq_pointCount`. It is the classification's *surjectivity*:
every `γ*K(E)`-embedding `σ` is a translation `τ_T` (`T ∈ ker γ`).

**[2026-05-29 deep pass — sharpened gap.]** The bricks above now supply, AXIOM-CLEAN, the
algebraic content of four of the five classification steps, and *refute* the round-9 claim that
they need `[IsAlgClosed]`/Galois-descent:
* (A) injectivity of `σ ↦ Q_σ` — `algHom_ext_x_y_gen_omega` (embeddings into `Ω` determined by
  `x_gen, y_gen`), with the `M`→`K` view `embRestrictScalarsK`;
* (B-base) the common group `E(Ω) = (W.baseChange Ω).Point` for the torsor — `embCurveBaseChange`
  (`(W_KE).map σ = W.baseChange Ω`), removing the σ-dependent codomain obstruction;
* (C) the fibre precondition `σ` fixes `M = γ*K(E)` — `embFixesPullbackRange` /
  `embAgreeOnPullbackRange`,
  *free* from `σ.commutes` (no isogeny `Ω`-point map / impossible `CoordHom` needed);
* (E) the descent "Frobenius-fixed ⟹ `F_q`-rational" — `frobenius_fixedPoint_iff_mem_baseField_gen`,
  which holds over *any* extension `L/K` of the finite base (NOT only `AlgebraicClosure K`).

The genuinely remaining gap is the **point-level assembly** (B)+(D)+(F): place `Q_σ` (via
`embCurveBaseChange`) and `ι(P_gen)` into `E(Ω)`, form `T_σ := Q_σ − ι(P_gen)`, prove
`frob_Ω(T_σ) = T_σ` (the linchpin: `Q_σ − frob_Ω(Q_σ) = (Affine.Point.map σ)(P_gen −
frobeniusW_KE P_gen)` by `Affine.Point.map_map` + `map_pow`, and the RHS coordinates are
`σ(γ.pullback x_gen) = ι(γ.pullback x_gen)` by brick (C), matching `ι(P_gen) − frob_Ω(ι P_gen)`
via `genericPoint_sub_frobeniusW_KE_apply`), then by brick (E) `T_σ` is `K`-rational hence in
`ker γ`, and `σ = τ_{T_σ}` (matching `translateAlgEquivOfPoint`, restricted to `Ω`-embeddings).
This is purely curve-group-law geometry over `Ω` threaded through the `γ.toAlgebra` /
Ore-localization instance diamonds — substantial but no longer blocked by a missing principle.
This statement records the gap as a hypothesis-free `Prop` so the residual's content is explicit
and unfabricated. -/
def isogOneSub_negFrobenius_emb_le_card_kernel_gap (hq : 2 ≤ Fintype.card K) : Prop :=
    (isogOneSub_negFrobenius W hq).sepDegree ≤
      Nat.card (isogOneSub_negFrobenius W hq).kernel

/- Embedding↔kernel surjectivity (HARD half `#Emb ≤ #ker`) — point-level assembly

The classification's surjectivity, assembled at the point level over
`Ω = AlgebraicClosure K(E)` from the shipped bricks (A)–(E) plus the generic-point
linchpin. All AXIOM-CLEAN. The torsor argument: every `M`-embedding `σ` gives the
`Ω`-point `Q_σ = (σ x_gen, σ y_gen) ∈ E(Ω)`; all `Q_σ` lie in the single fibre
`γ_Ω⁻¹(P_gen)`, because `Q_σ − π(Q_σ)` is the σ-independent constant
`ι·(generic − π generic)` (brick C `embAgreeOnPullbackRange`). Hence `Q_σ − Q_{σ₀}` is
geometric-Frobenius-fixed, descends (brick E,
`frobenius_fixedPoint_iff_mem_baseField_gen`) to a `K`-point, and `σ ↦ Q_σ − Q_{σ₀}` is
injective (brick A `algHom_ext_x_y_gen_omega`). Since `ker γ = ⊤`, this injects
`Emb ↪ ker γ`, giving `#Emb ≤ #ker γ`. -/

local notation "Ω" => AlgebraicClosure W.toAffine.FunctionField

noncomputable def includePtOmega [DecidableEq Ω] :
    W.toAffine.Point → (W.baseChange Ω).toAffine.Point :=
  HasseWeil.Affine.Point.map (W := W) (algebraMap K Ω)
    (FaithfulSMul.algebraMap_injective K Ω)

theorem includePtOmega_injective [DecidableEq Ω] :
    Function.Injective (includePtOmega W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP
  · rfl
  · change (Affine.Point.zero : (W.baseChange Ω).toAffine.Point) = Affine.Point.some _ _ _ at hP
    exact absurd hP (by simp)
  · change (Affine.Point.some _ _ _ : (W.baseChange Ω).toAffine.Point) = Affine.Point.zero at hP
    exact absurd hP (by simp)
  · change (HasseWeil.Affine.Point.map (algebraMap K Ω) _ (Affine.Point.some x₁ y₁ h₁)) =
      HasseWeil.Affine.Point.map (algebraMap K Ω) _ (Affine.Point.some x₂ y₂ h₂) at hP
    rw [HasseWeil.Affine.Point.map_some, HasseWeil.Affine.Point.map_some,
      Affine.Point.some.injEq] at hP
    obtain ⟨hx, hy⟩ := hP
    have hx' : x₁ = x₂ := FaithfulSMul.algebraMap_injective K Ω hx
    have hy' : y₁ = y₂ := FaithfulSMul.algebraMap_injective K Ω hy
    subst hx' hy'
    rfl

@[simp] theorem includePtOmega_some [DecidableEq Ω] {x y : K} (h : W.toAffine.Nonsingular x y) :
    includePtOmega W (.some x y h) =
      .some (algebraMap K Ω x) (algebraMap K Ω y)
        ((WeierstrassCurve.Affine.map_nonsingular W.toAffine
          (FaithfulSMul.algebraMap_injective K Ω) x y).mpr h) := rfl

noncomputable def geomFrobOmega [DecidableEq Ω] :
    (W.baseChange Ω).toAffine.Point →+ (W.baseChange Ω).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom K Ω)

theorem geomFrobOmega_some [DecidableEq Ω]
    {x y : Ω} (h : (W.baseChange Ω).toAffine.Nonsingular x y) :
    geomFrobOmega W (Affine.Point.some x y h) =
      Affine.Point.some
        ((FiniteField.frobeniusAlgHom K Ω) x) ((FiniteField.frobeniusAlgHom K Ω) y)
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          (RingHom.injective (FiniteField.frobeniusAlgHom K Ω).toRingHom) x y).mpr h) := by
  change WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom K Ω)
    (Affine.Point.some x y h) = _
  exact WeierstrassCurve.Affine.Point.map_some (f := FiniteField.frobeniusAlgHom K Ω) h

theorem geomFrobOmega_fixed_iff_mem_range [DecidableEq Ω]
    (P : (W.baseChange Ω).toAffine.Point) :
    geomFrobOmega W P = P ↔ P ∈ Set.range (includePtOmega W) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true rfl ⟨0, rfl⟩
  · rw [geomFrobOmega_some, Affine.Point.some.injEq]
    show (FiniteField.frobeniusAlgHom K Ω) x = x ∧ (FiniteField.frobeniusAlgHom K Ω) y = y ↔ _
    rw [FiniteField.coe_frobeniusAlgHom]
    change x ^ Fintype.card K = x ∧ y ^ Fintype.card K = y ↔ _
    rw [frobenius_fixedPoint_iff_mem_baseField_gen, frobenius_fixedPoint_iff_mem_baseField_gen]
    constructor
    · rintro ⟨⟨x₀, rfl⟩, ⟨y₀, rfl⟩⟩
      refine ⟨.some x₀ y₀ ?_, ?_⟩
      · exact (WeierstrassCurve.Affine.map_nonsingular W.toAffine (f := algebraMap K Ω)
          (FaithfulSMul.algebraMap_injective K Ω) x₀ y₀).mp h
      · rw [includePtOmega_some]
    · rintro ⟨Q, hQ⟩
      rcases Q with _ | ⟨x₀, y₀, h₀⟩
      · rw [show includePtOmega W Affine.Point.zero
            = (0 : (W.baseChange Ω).toAffine.Point) from rfl] at hQ
        exact absurd hQ (by simp)
      · rw [includePtOmega_some, Affine.Point.some.injEq] at hQ
        exact ⟨⟨x₀, hQ.1⟩, ⟨y₀, hQ.2⟩⟩

theorem map_sigma_frob_comm [DecidableEq Ω]
    (σ : W.toAffine.FunctionField →ₐ[K] Ω) (P : (W_KE W).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W) σ (frobeniusW_KE W P) =
      geomFrobOmega W (WeierstrassCurve.Affine.Point.map (W' := W) σ P) := by
  have hcomp : σ.comp (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) =
      (FiniteField.frobeniusAlgHom K Ω).comp σ := by
    apply AlgHom.ext
    intro z
    change σ ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) z) =
      (FiniteField.frobeniusAlgHom K Ω) (σ z)
    rw [FiniteField.coe_frobeniusAlgHom, FiniteField.coe_frobeniusAlgHom, map_pow]
  change WeierstrassCurve.Affine.Point.map (W' := W) σ
      (WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) P) = _
  calc WeierstrassCurve.Affine.Point.map (W' := W) σ
        (WeierstrassCurve.Affine.Point.map (W' := W)
          (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) P)
      = WeierstrassCurve.Affine.Point.map (W' := W)
          (σ.comp (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField)) P :=
        WeierstrassCurve.Affine.Point.map_map _ _ P
    _ = WeierstrassCurve.Affine.Point.map (W' := W)
          ((FiniteField.frobeniusAlgHom K Ω).comp σ) P := by rw [hcomp]
    _ = geomFrobOmega W (WeierstrassCurve.Affine.Point.map (W' := W) σ P) :=
        (WeierstrassCurve.Affine.Point.map_map _ _ P).symm

theorem Qσ_sub_frob_eq_map [DecidableEq Ω]
    (σ : W.toAffine.FunctionField →ₐ[K] Ω) :
    WeierstrassCurve.Affine.Point.map (W' := W) σ (genericPoint W) -
      geomFrobOmega W (WeierstrassCurve.Affine.Point.map (W' := W) σ (genericPoint W)) =
      WeierstrassCurve.Affine.Point.map (W' := W) σ
        (genericPoint W - frobeniusW_KE W (genericPoint W)) := by
  rw [← map_sigma_frob_comm W σ (genericPoint W)]
  exact (map_sub (WeierstrassCurve.Affine.Point.map (W' := W) σ) _ _).symm

theorem map_emb_generic_sub_frob_eq_of_agree (hq : 2 ≤ Fintype.card K) [DecidableEq Ω]
    (σ τ : W.toAffine.FunctionField →ₐ[K] Ω)
    (hx : σ ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      τ ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    (hy : σ ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) =
      τ ((isogOneSub_negFrobenius W hq).pullback (y_gen W))) :
    WeierstrassCurve.Affine.Point.map (W' := W) σ
        (genericPoint W - frobeniusW_KE W (genericPoint W)) =
      WeierstrassCurve.Affine.Point.map (W' := W) τ
        (genericPoint W - frobeniusW_KE W (genericPoint W)) := by
  rw [genericPoint_sub_frobeniusW_KE_apply W]
  refine (WeierstrassCurve.Affine.Point.map_some (f := σ) _).trans ?_
  refine Eq.trans ?_ (WeierstrassCurve.Affine.Point.map_some (f := τ) _).symm
  rw [Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [show addPullback_x W (negFrobeniusIsog W)
          = (isogOneSub_negFrobenius W hq).pullback (x_gen W) by
        rw [isogOneSub_negFrobenius_pullback, addPullbackAlgHom_negFrobenius_x_gen_eq]]
    exact hx
  · rw [show addPullback_y W (negFrobeniusIsog W)
          = (isogOneSub_negFrobenius W hq).pullback (y_gen W) by
        rw [isogOneSub_negFrobenius_pullback, addPullbackAlgHom_negFrobenius_y_gen_eq]]
    exact hy

-- Qσ as some (σ x_gen)(σ y_gen)
theorem map_genericPoint_eq_some [DecidableEq Ω]
    (σ : W.toAffine.FunctionField →ₐ[K] Ω) :
    WeierstrassCurve.Affine.Point.map (W' := W) σ (genericPoint W) =
      Affine.Point.some (σ (x_gen W)) (σ (y_gen W))
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine σ.injective
          (x_gen W) (y_gen W)).mpr
          (generic_nonsingular W)) := by
  rw [genericPoint_xOf_some]
  exact WeierstrassCurve.Affine.Point.map_some (f := σ) (generic_nonsingular W)

/-- **HARD half `#Emb ≤ #ker γ`** (Silverman III.4.10c surjectivity), the point-level
torsor assembly. Every `γ*K(E)`-embedding `σ` gives `Q_σ = (σ x_gen, σ y_gen) ∈ E(Ω)`;
the differences `Q_σ − Q_{σ₀}` are geometric-Frobenius-fixed (all `Q_σ` share the
σ-independent value `Q_σ − π(Q_σ)`, brick C), descend to `K`-points (brick E), and
`σ ↦ Q_σ − Q_{σ₀}` is injective (brick A); `ker γ = ⊤` lands the descended points in
`ker γ`. This is the sole remaining content of
`isogOneSub_negFrobenius_sepDegree_eq_card_kernel`. Axiom-clean. -/
theorem emb_le_card_kernel (hq : 2 ≤ Fintype.card K) [DecidableEq Ω] :
    (isogOneSub_negFrobenius W hq).sepDegree ≤
      Nat.card (isogOneSub_negFrobenius W hq).kernel := by
  letI := (isogOneSub_negFrobenius W hq).toAlgebra
  rw [isogOneSub_negFrobenius_sepDegree_eq_card_emb W hq]
  set Emb := (W.toAffine.FunctionField →ₐ[W.toAffine.FunctionField] Ω) with hEmb
  -- `σK`: the `K`-restricted view of an `M`-embedding (`embRestrictScalarsK`, brick A→K).
  let σK : Emb → (W.toAffine.FunctionField →ₐ[K] Ω) := embRestrictScalarsK W hq
  -- `Q_σ = (σ x_gen, σ y_gen) ∈ E(Ω)`, the forward map placed via `embCurveBaseChange`.
  let Qσ : Emb → (W.baseChange Ω).toAffine.Point := fun σ ↦
    WeierstrassCurve.Affine.Point.map (W' := W) (σK σ) (genericPoint W)
  -- Frobenius-fixedness of `Q_σ − Q_τ` (the torsor difference lands in `ker γ_Ω`).
  have hfixed : ∀ σ τ : Emb, geomFrobOmega W (Qσ σ - Qσ τ) = Qσ σ - Qσ τ := by
    intro σ τ
    have hagree_x : (σK σ) ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
        (σK τ) ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :=
      embAgreeOnPullbackRange W hq σ τ (x_gen W)
    have hagree_y : (σK σ) ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) =
        (σK τ) ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) :=
      embAgreeOnPullbackRange W hq σ τ (y_gen W)
    have hconst : Qσ σ - geomFrobOmega W (Qσ σ) = Qσ τ - geomFrobOmega W (Qσ τ) := by
      rw [Qσ_sub_frob_eq_map W (σK σ), Qσ_sub_frob_eq_map W (σK τ)]
      exact map_emb_generic_sub_frob_eq_of_agree W hq _ _ hagree_x hagree_y
    rw [map_sub]
    have h0 : Qσ σ - geomFrobOmega W (Qσ σ) - (Qσ τ - geomFrobOmega W (Qσ τ)) = 0 := by
      rw [hconst, sub_self]
    have : (Qσ σ - Qσ τ) - (geomFrobOmega W (Qσ σ) - geomFrobOmega W (Qσ τ)) = 0 := by
      rw [← h0]
      abel
    exact (sub_eq_zero.mp this).symm
  rcases isEmpty_or_nonempty Emb with hE | hE
  · rw [Nat.card_eq_zero.mpr (Or.inl hE)]
    exact Nat.zero_le _
  · obtain ⟨σ₀⟩ := hE
    have hktop : (isogOneSub_negFrobenius W hq).kernel = ⊤ :=
      kernel_eq_top_of_hom_eq_id_sub_frobenius W (isogOneSub_negFrobenius W hq)
        (isogOneSub_negFrobenius_toAddMonoidHom W hq)
    have hmem : ∀ σ : Emb, Qσ σ - Qσ σ₀ ∈ Set.range (includePtOmega W) :=
      fun σ ↦ (geomFrobOmega_fixed_iff_mem_range W (Qσ σ - Qσ σ₀)).mp (hfixed σ σ₀)
    let Φ : Emb → (isogOneSub_negFrobenius W hq).kernel := fun σ ↦
      ⟨(hmem σ).choose, hktop ▸ AddSubgroup.mem_top _⟩
    have hΦinj : Function.Injective Φ := by
      intro σ τ hσ
      have hchoose : (hmem σ).choose = (hmem τ).choose := Subtype.ext_iff.mp hσ
      have hQeq : Qσ σ - Qσ σ₀ = Qσ τ - Qσ σ₀ := by
        rw [← (hmem σ).choose_spec, ← (hmem τ).choose_spec, hchoose]
      -- `Q_σ = Q_τ` ⟹ coordinates agree ⟹ `σK σ = σK τ` (brick A).
      have hQ' : WeierstrassCurve.Affine.Point.map (W' := W) (σK σ) (genericPoint W) =
          WeierstrassCurve.Affine.Point.map (W' := W) (σK τ) (genericPoint W) :=
        sub_left_inj.mp hQeq
      have hcoords : (σK σ) (x_gen W) = (σK τ) (x_gen W) ∧
          (σK σ) (y_gen W) = (σK τ) (y_gen W) := by
        rw [map_genericPoint_eq_some W (σK σ), map_genericPoint_eq_some W (σK τ),
            Affine.Point.some.injEq] at hQ'
        exact hQ'
      -- `σK` is injective on `Emb` (it preserves `toRingHom`): `σK σ = σK τ` ⟹ `σ = τ`.
      exact DFunLike.ext _ _ fun z ↦
        DFunLike.congr_fun (algHom_ext_x_y_gen_omega W hcoords.1 hcoords.2) z
    exact Nat.card_le_card_of_injective Φ hΦinj

theorem isogOneSub_negFrobenius_sepDegree_eq_card_kernel (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).sepDegree =
      Nat.card (isogOneSub_negFrobenius W hq).kernel := by
  -- EASY half (axiom-clean): `#ker ≤ #Emb = sepDegree`.
  have h_le : Nat.card (isogOneSub_negFrobenius W hq).kernel ≤
      (isogOneSub_negFrobenius W hq).sepDegree :=
    isogOneSub_negFrobenius_card_kernel_le_sepDegree W hq
  -- HARD half (classification surjectivity = `deg ≤ pointCount`): `sepDegree = #Emb ≤ #ker`,
  -- the point-level torsor assembly `emb_le_card_kernel` (Silverman III.4.10c). Provide the
  -- `DecidableEq Ω` instance locally (scoped, to protect the global build per the prior pass).
  have h_ge : (isogOneSub_negFrobenius W hq).sepDegree ≤
      Nat.card (isogOneSub_negFrobenius W hq).kernel := by
    classical
    exact emb_le_card_kernel W hq
  exact le_antisymm h_ge h_le

/-- **V.1.3 sharp residual** (Silverman III.4.10c): the degree of the
isogeny `1 − π` equals the number of `F_q`-rational points of `E`.

**[2026-05-29 ROUND-9 rewire — R2 embeddings-classification.]** Now PROVED axiom-clean
*modulo the single embedding↔kernel count* `isogOneSub_negFrobenius_sepDegree_eq_card_kernel`
(see the block comment above). The proof is pure composition:
`#ker γ = sepDegree γ` (the residual) `= degree γ` (separability) and `#ker γ = pointCount`
(`ker γ = ⊤`). The dead L6_B3_tower / place↔point / `CoordHom` route is superseded.

This is the **sole** sharp sub-fact gating V.1.3. All three V.1.3 targets close from it
(plus axiom-clean shipped lemmas): `sepDegree_oneSub_eq_pointCount`, `ker_deg_skeleton`,
and `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower` (via the cardinality squeeze
of the fundamental ramification identity).

**[2026-05-28 ROUND-5 reduction.]** Per the block-comment above, this statement is
equivalent — via `l6_B3_tower` (axiom-clean), Mathlib's `Ideal.sum_ramification_inertia`,
the shipped bridge lemmas (`bridge_Biii_ord_eq_neg_two_v2`, `bridge_Biv_inertia_eq_one_v2`,
`Sinf_kernelToPrime_v2_injective`), and the axiom-clean squeeze composer
`Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness` — to:

> Every prime `P` of `Sinf` over `(X)` is the kernel-prime of some `T ∈ ker(1 − π)` (i.e.
> is in the image of `bridge_Bi_kernelToPrime_v2`).

Mathematical content: function-field place ↔ closed-point dictionary over `K` (Silverman
II.2.4), specialised to the pole locus of `f = (1−π)*x`. Since `x` has its only pole at `O`,
a closed point of `E` where `f` has a pole satisfies `(1−π)(P) = O`, i.e. `P ∈ ker(1−π)`;
over `K`, these are the `K`-rational kernel points = `E(F_q)`.

**Casualties (round-5).** The WireUpPrep route (`degree_isogOneSub_negFrobenius_eq_pointCount`
+ `oneSubFrob_baseChange_coordHom`) is **dead** — relies on an impossible `CoordHom : R → R`
for `1 − π`. See the B2 annotation on `HasseWeil.RouteB.nReduced_R_div_D_sq`. -/
theorem isogOneSub_negFrobenius_degree_eq_pointCount (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).degree = pointCount W.toAffine := by
  -- ROUND-9 PATH (R2 embeddings-classification): reduce to the single embedding↔kernel
  -- count `sepDegree γ = #ker γ` (`isogOneSub_negFrobenius_sepDegree_eq_card_kernel`),
  -- then compose axiom-clean.
  obtain ⟨p, _, ⟨_, _⟩, hp_prime, _⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  -- `#ker γ = deg γ`, from the embedding↔kernel count + separability + finiteness.
  have h_ker_deg :
      Nat.card (isogOneSub_negFrobenius W hq).kernel =
        (isogOneSub_negFrobenius W hq).degree :=
    Isogeny.card_kernel_eq_degree_of_sepDegree_eq_card_kernel
      (isogOneSub_negFrobenius W hq)
      (isogOneSub_negFrobenius_isSeparable W p hq)
      (isogOneSub_negFrobenius_finiteDimensional W hq)
      (isogOneSub_negFrobenius_sepDegree_eq_card_kernel W hq)
  -- `deg γ = pointCount`, from `#ker γ = deg γ` + `ker γ = ⊤` (γ's point map is `id − π`).
  exact degree_eq_pointCount_of_card_kernel_eq_degree W (isogOneSub_negFrobenius W hq)
    (isogOneSub_negFrobenius_toAddMonoidHom W hq) h_ker_deg

/-- **GAP-L6 keystone, CONNECTED** (Silverman V.1.1, p. 138): `sepDeg(1−π) = #E(F_q)`,
**PROVED** axiom-clean over the V.1.3 sharp residual
`isogOneSub_negFrobenius_degree_eq_pointCount`.

Pure composition (deep pass 2026-05-28): `sepDegree γ = degree γ` for separable `γ` (via
`isSeparable_iff_sepDegree_eq_degree`, mathlib + project), and `degree γ = pointCount`
(the sharp residual). No dependence on the (now-deleted) `l6_computationA` / L6Witnesses
sum-of-inertia sorry — the keystone closes via the sharp residual alone. -/
theorem sepDegree_oneSub_eq_pointCount (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine := by
  obtain ⟨p, _, ⟨_, _⟩, hp_prime, _⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have h_sep := isogOneSub_negFrobenius_isSeparable W p hq
  have h_fin := isogOneSub_negFrobenius_finiteDimensional W hq
  -- separable ⇒ sepDegree = degree
  rw [(Isogeny.isSeparable_iff_sepDegree_eq_degree _ h_fin).mp h_sep]
  -- degree = pointCount via the sharp residual
  exact isogOneSub_negFrobenius_degree_eq_pointCount W hq

/-- **GAP-L6 top leaf, CONNECTED** (Silverman V.1.1 / III.4.10c): `#ker(1−π) = deg(1−π)`,
**PROVED** axiom-clean over the V.1.3 sharp residual
`isogOneSub_negFrobenius_degree_eq_pointCount`.

Pure composition (deep pass 2026-05-28): `Nat.card γ.kernel = pointCount`
(`kernel_eq_top_of_hom_eq_id_sub_frobenius` + `AddSubgroup.card_top`, axiom-clean) combined
with `degree γ = pointCount` (the sharp residual) gives the identity. No dependence on
`sepDegree_oneSub_eq_pointCount` (nor the now-deleted `l6_computationA` chain) — the top
leaf closes via the sharp residual alone. -/
theorem ker_deg_skeleton (hq : 2 ≤ Fintype.card K) :
    Nat.card (isogOneSub_negFrobenius W hq).kernel =
      (isogOneSub_negFrobenius W hq).degree := by
  -- `kernel = ⊤` (rational-point shape) ⇒ `Nat.card kernel = pointCount`.
  have h_ker_card : Nat.card (isogOneSub_negFrobenius W hq).kernel = pointCount W.toAffine := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W
      (isogOneSub_negFrobenius W hq) rfl, AddSubgroup.card_top]
    exact Nat.card_eq_fintype_card
  -- degree = pointCount (sharp residual) ⇒ pointCount = degree, transitive close.
  rw [h_ker_card, isogOneSub_negFrobenius_degree_eq_pointCount W hq]

/-- **Phase B — V.1.3 LHS finrank witness** (deep pass 2026-05-28; downstream of L6Witnesses).
Combines the tower computation `l6_B3_tower` (`[K(E):K(γ*x)] = 2·γ.degree`, axiom-clean) with
the V.1.3 sharp residual `isogOneSub_negFrobenius_degree_eq_pointCount`
(`γ.degree = pointCount`) and the framing bridges `finrank_adjoin_eq_finrank_LinfAt`
(axiom-clean) + `finrank_gamma_pullback_x_eq_weightedPoleDegree` (the fundamental identity,
axiom-clean) to give the sharp LHS witness `Σ e_P · f_P = 2 · pointCount` consumed by the
L6Witnesses squeeze composer `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`. -/
theorem Sinf_finrank_witness_via_B3_tower (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField)) :
    letI := data.commRing
    letI := data.isDedekindDomain
    letI := data.algPoly
    ∑ P ∈ primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      (-(data.ordAt P)).toNat *
        Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P =
      2 * pointCount W.toAffine := by
  letI := data.commRing
  letI := data.isDedekindDomain
  letI := data.algPoly
  haveI hfact := Conditional.fact_transcendental_gamma_pullback_x_inv W hq
  haveI hmf := moduleFinite_linfAt_gamma_pullback_x W hq
  -- Apply the framing chain:
  --   Σ e_P · f_P = finrank (FractionRing K[X]) (LinfAt f)  (fundamental, shipped)
  --              = finrank K⟮f⟯ K(E)               (`finrank_adjoin_eq_finrank_LinfAt`)
  --              = 2 · γ.degree                    (`l6_B3_tower`)
  --              = 2 · pointCount                  (sharp residual)
  rw [← Conditional.finrank_gamma_pullback_x_eq_weightedPoleDegree W hq hmf data,
      ← Conditional.finrank_adjoin_eq_finrank_LinfAt W hq, l6_B3_tower W hq,
      isogOneSub_negFrobenius_degree_eq_pointCount W hq]

/-- **Phase B — V.1.3 squeeze closure** (deep pass 2026-05-28; AXIOM-CLEAN). The
sum-of-inertia identity `Σ f_P = #E(F_q)`, via the squeeze composer
`Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness` (L6Witnesses,
axiom-clean Finset arithmetic) applied to the LHS finrank witness
`Sinf_finrank_witness_via_B3_tower` (above). (The sorried L6Witnesses statement of the
same proposition — forward-reference blocked from this proof — was deleted with its dead
cone on 2026-06-11; this fresh-name theorem is the closure the downstream chain consumes.) -/
theorem Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField)) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algPoly
    ∑ P ∈ primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      (Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P) =
        pointCount W.toAffine :=
  Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness W hq data
    (Sinf_finrank_witness_via_B3_tower W hq data)

/-- **Cayley-Hamilton at AddMonoidHom level for the genuine family** (witness-parametric):
given `β_dual` with the right AddMonoidHom and the III.6 witnesses (dual composition + sum
trace), the composition `(β_dual.comp (genuineIsogSmulSub W r s)).toAddMonoidHom` equals
`(mulByInt N).toAddMonoidHom`.

This is the AddMonoidHom-level chunk of SUB-PIV-C2 (the FULL isogeny composition is
required for SUB-PIV-D's signed extraction, but this AddMonoidHom-level identity is the
forced algebraic consequence of `V∘π = [q]` (from IsDualOf) + `π + V = [t]` (from sum
trace witness)).  Composes the existing `comp_toAddMonoidHom_eq_mulByInt_of_quadratic`
with the genuine isogeny family's structural form. -/
theorem genuine_dual_comp_toAddMonoidHom_eq_mulByInt
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _)) :
    (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).toAddMonoidHom =
      (mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
      ).toAddMonoidHom := by
  -- α = frobeniusIsog, α_dual = V; β has the genuine isogeny toAddMonoidHom shape.
  have h_dual_comp : ∀ P : W.toAffine.Point,
      V.toAddMonoidHom ((frobeniusIsog W).toAddMonoidHom P) =
        ((frobeniusIsog W).degree : ℤ) • P := by
    intro P
    have h_app := DFunLike.congr_fun (congrArg Isogeny.toAddMonoidHom h_isDual.1) P
    rw [Isogeny.comp_apply] at h_app
    rw [h_app, mulByInt_apply]
  have h_beta_hom : (genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom =
      r • (frobeniusIsog W).toAddMonoidHom - s • (AddMonoidHom.id _) := by
    rw [genuineIsogSmulSub_toAddMonoidHom]
    ext P
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.smul_apply, AddMonoidHom.id_apply, Isogeny.zsmul_apply,
      mulByInt_apply]
    rw [neg_smul, sub_eq_add_neg]
  have h_main := comp_toAddMonoidHom_eq_mulByInt_of_quadratic
    (frobeniusIsog W) V
    (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))
    r s (genuineIsogSmulSub W r s hr hs hrK hsK) β_dual
    h_beta_hom h_beta_dual_hom h_dual_comp h_sum_trace
  rw [frobeniusIsog_degree] at h_main
  exact h_main

/- Genuine-isogeny extensionality (the "Wall-B killer")

`HasseWeil.Isogeny` stores `pullback` and `toAddMonoidHom` as **independent** fields, so a
point-map (`toAddMonoidHom`) identity does **not** by itself imply a pullback identity — this is
the obstruction recorded in the placeholder lesson (`AlgHom.id` with a non-identity point map
gives a *false* degree-1 isogeny).

The honest fix is the **generic point**.  By `algHom_ext_x_y_gen` (`EC/TranslationOrd`), an
`F`-algebra endomorphism of `K(E)` is determined by its values on the two generators
`x_gen, y_gen`.  For an isogeny that arises from a *genuine* geometric morphism, the pair
`(φ.pullback x_gen, φ.pullback y_gen)` is exactly the coordinate pair of "the geometric
point-map applied to the generic point".  We encode this directly:

`IsGenuineWith φ g` says the group homomorphism `g : E(K(E)) →+ E(K(E))` (the geometric action
of `φ` on `K(E)`-points) sends the generic point `P_gen = (x_gen, y_gen)` to the point whose
coordinates are `(φ.pullback x_gen, φ.pullback y_gen)`.  This is a **genuine, non-vacuous**
condition: it forces the pullback's value on the generators to be the *actual* geometric image
of `P_gen` under `g` (a placeholder `pullback = AlgHom.id` paired with a non-identity geometric
`g` fails it, since then `g P_gen ≠ P_gen = (x_gen, y_gen)`).

The extensionality lemma `genuine_isogeny_ext` then reads: two isogenies that are genuine **with
the same geometric action `g`** have equal pullbacks (hence are equal isogenies once their
`toAddMonoidHom` agree). -/

/-- An isogeny `φ` is **genuine with geometric action `g`** when the group homomorphism `g` on
`K(E)`-points (the geometric action of `φ` base-changed to the function field) carries the generic
point `P_gen = (x_gen, y_gen)` to a finite point whose coordinates are exactly the pullback values
`(φ.pullback x_gen, φ.pullback y_gen)`.

This is the precise sense in which "`φ.pullback` is the comorphism of `φ`'s geometric map": the
pullback's effect on the two generators is read off from the geometric image of the generic
point.  It is non-vacuous — it equates the pullback values with the genuine geometric coordinates
of `g P_gen` (a placeholder `pullback = AlgHom.id` paired with a non-identity geometric `g` fails
it, since then `g P_gen ≠ P_gen = (x_gen, y_gen)`).

We phrase the geometric image with *abstract* coordinates `X, Y` plus the two equations
`X = φ.pullback x_gen`, `Y = φ.pullback y_gen`, so that the substantive content stays at the level
of `K(E)`-element equalities (no comparison of dependent nonsingularity proofs). -/
def IsGenuineWith (φ : Isogeny W.toAffine W.toAffine)
    (g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point) : Prop :=
  ∃ (X Y : W.toAffine.FunctionField) (h : (W_KE W).toAffine.Nonsingular X Y),
    g (genericPoint W) = Affine.Point.some X Y h ∧
      X = φ.pullback (x_gen W) ∧ Y = φ.pullback (y_gen W)

/-- An isogeny is **genuine** if there is *some* geometric action `g` making it genuine in the
sense of `IsGenuineWith`.  (The witness `g` is the geometric point map of `φ` over `K(E)`.) -/
def IsGenuine (φ : Isogeny W.toAffine W.toAffine) : Prop :=
  ∃ g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point, IsGenuineWith W φ g

/-- **Genuine-isogeny extensionality (Wall-B killer), pullback form.** Two isogenies that are
genuine **with the same geometric action `g`** have the same pullback.

Proof: both pullbacks send the generic-point coordinates `(x_gen, y_gen)` to the coordinates of
the common geometric image `g P_gen`; agreement on the two generators upgrades to full pullback
equality by `algHom_ext_x_y_gen`. -/
theorem genuine_isogeny_ext_pullback
    {φ ψ : Isogeny W.toAffine W.toAffine}
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hφ : IsGenuineWith W φ g) (hψ : IsGenuineWith W ψ g) :
    φ.pullback = ψ.pullback := by
  obtain ⟨Xφ, Yφ, hφns, hφg, hφx, hφy⟩ := hφ
  obtain ⟨Xψ, Yψ, hψns, hψg, hψx, hψy⟩ := hψ
  -- The two geometric images are both `g (genericPoint W)`, hence equal as points.
  have hpts : Affine.Point.some Xφ Yφ hφns = Affine.Point.some Xψ Yψ hψns := by
    rw [← hφg, ← hψg]
  rw [Affine.Point.some.injEq] at hpts
  -- Transport through the pullback-value equations: `φ*x_gen = Xφ = Xψ = ψ*x_gen`, etc.
  refine algHom_ext_x_y_gen W ?_ ?_
  · rw [← hφx, ← hψx, hpts.1]
  · rw [← hφy, ← hψy, hpts.2]

/-- **Genuine-isogeny extensionality (Wall-B killer), full-isogeny form.** Two isogenies that are
genuine with the same geometric action **and** have the same `toAddMonoidHom` are equal as full
isogenies.  This is the lemma that upgrades a shipped point-map identity to a comorphism (pullback)
identity, feeding the Wall-C signed-degree extraction. -/
theorem genuine_isogeny_ext
    {φ ψ : Isogeny W.toAffine W.toAffine}
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hφ : IsGenuineWith W φ g) (hψ : IsGenuineWith W ψ g)
    (h_hom : φ.toAddMonoidHom = ψ.toAddMonoidHom) :
    φ = ψ :=
  Isogeny.eq_of_components (genuine_isogeny_ext_pullback W hφ hψ) h_hom

/- `IsGenuine` is non-vacuous: discharge for `[N]` and the genuine sum isogenies. -/

/-- The geometric action of `[N]` on `K(E)`-points is the zsmul-by-`N` group homomorphism
`P ↦ N • P` on `E(K(E)) = (W_KE).Point`.  We use Mathlib's `zsmulAddGroupHom` so the underlying
`•` matches the one appearing in `zsmul_genericPoint_eq`. -/
noncomputable abbrev zsmulPointHom (N : ℤ) :
    (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point :=
  zsmulAddGroupHom N

theorem zsmulPointHom_apply (N : ℤ) (P : (W_KE W).toAffine.Point) :
    zsmulPointHom W N P = N • P := rfl

/-- **`[N]` is genuine** (`N ≠ 0`), with geometric action `P ↦ N • P`.  This is the basic
non-vacuity check: the pullback of `[N]` on the generators `(x_gen, y_gen)` is exactly the
coordinate pair of `N • P_gen` (the geometric multiplication-by-`N` image of the generic point),
by `zsmul_genericPoint_eq` and `mulByInt_pullback_x` / `mulByInt_pullback_y`. -/
theorem mulByInt_isGenuineWith (N : ℤ) (hN : N ≠ 0) :
    IsGenuineWith W (mulByInt W.toAffine N) (zsmulPointHom W N) := by
  obtain ⟨hns, hsmul⟩ := zsmul_genericPoint_eq W N hN
  -- Geometric image of `P_gen` is `N • P_gen = some (mulByInt_x N) (mulByInt_y N)`.
  refine ⟨mulByInt_x W N, mulByInt_y W N, hns, ?_, ?_, ?_⟩
  · -- `zsmulPointHom W N (genericPoint W) = N • genericPoint W` is `rfl` (unfolds only the hom,
    -- not the heavy `genericPoint`).  The remaining gap between `hsmul` and the goal is only the
    -- `DecidableEq K(E)` instance feeding `Affine.Point.instAddCommGroup` (a `Subsingleton`).
    rw [show zsmulPointHom W N (genericPoint W) = N • genericPoint W from rfl]
    -- Align the `DecidableEq` instance used by the ambient point-group with the one in `hsmul`.
    exact Subsingleton.elim (instDecidableEqFunctionField W) FractionRing.instDecidableEq ▸ hsmul
  · exact (mulByInt_pullback_x W N hN).symm
  · exact (mulByInt_pullback_y W N hN).symm

/-- **`[N]` is genuine** (`N ≠ 0`). -/
theorem mulByInt_isGenuine (N : ℤ) (hN : N ≠ 0) :
    IsGenuine W (mulByInt W.toAffine N) :=
  ⟨zsmulPointHom W N, mulByInt_isGenuineWith W N hN⟩

/-- **The Frobenius isogeny is genuine**, with geometric action the curve Frobenius
`frobeniusW_KE` on `K(E)`-points.  The pullback of `π` on the generators is `x_gen^q, y_gen^q`
(`frobeniusIsog_pullback_apply`), which is exactly the coordinate pair of
`frobeniusW_KE (genericPoint) = (x_gen^q, y_gen^q)` (`frobeniusW_KE_some`). -/
theorem frobeniusIsog_isGenuineWith :
    IsGenuineWith W (frobeniusIsog W) (frobeniusW_KE W) := by
  -- `frobeniusW_KE (genericPoint) = some (frob x_gen) (frob y_gen)`.
  have hgen : frobeniusW_KE W (genericPoint W) =
      Affine.Point.some
        ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (x_gen W))
        ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (y_gen W))
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          (RingHom.injective
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom)
          (x_gen W) (y_gen W)).mpr
          (generic_nonsingular W)) := by
    rw [genericPoint_xOf_some, frobeniusW_KE_some]
  -- `frob g = g^q = π.pullback g` on both generators.
  refine ⟨_, _, _, hgen, ?_, ?_⟩ <;>
    rw [frobeniusIsog_pullback_apply, FiniteField.coe_frobeniusAlgHom]

/-- **`r·π` is genuine** (the integer scalar multiple of Frobenius `(frobeniusIsog W).zsmul r`),
with geometric action `P ↦ r • frobeniusW_KE P`.

Key point: `r • frobeniusW_KE (genericPoint) = frobeniusW_KE (r • genericPoint)` (because
`frobeniusW_KE` is an `AddMonoidHom`, `map_zsmul`), and `r • genericPoint = some (mulByInt_x r)
(mulByInt_y r)` (`zsmul_genericPoint_eq`), so the geometric image is `some ((mulByInt_x r)^q)
((mulByInt_y r)^q)`.  On the pullback side, `(r·π).pullback x_gen = π.pullback (mulByInt_x r) =
(mulByInt_x r)^q` (Frobenius is `f ↦ f^q`), matching exactly. -/
theorem zsmul_frobeniusIsog_isGenuineWith (r : ℤ) (hr : r ≠ 0) :
    IsGenuineWith W ((frobeniusIsog W).zsmul r)
      ((zsmulPointHom W r).comp (frobeniusW_KE W)) := by
  obtain ⟨hns, hsmul⟩ := zsmul_genericPoint_eq W r hr
  -- Geometric image: `r • frobeniusW_KE gen = frobeniusW_KE (r • gen) = some ((mx)^q) ((my)^q)`.
  have hgeo : (zsmulPointHom W r).comp (frobeniusW_KE W) (genericPoint W) =
      frobeniusW_KE W (r • genericPoint W) := by
    rw [AddMonoidHom.comp_apply]
    rw [show zsmulPointHom W r (frobeniusW_KE W (genericPoint W))
        = r • frobeniusW_KE W (genericPoint W) from rfl]
    exact ((frobeniusW_KE W).map_zsmul r (genericPoint W)).symm
  -- Align the `DecidableEq K(E)` instance between `hsmul` and the ambient point-group.
  have hsmul' : r • genericPoint W =
      Affine.Point.some (mulByInt_x W r) (mulByInt_y W r) hns :=
    Subsingleton.elim (instDecidableEqFunctionField W) FractionRing.instDecidableEq ▸ hsmul
  have himg : (zsmulPointHom W r).comp (frobeniusW_KE W) (genericPoint W) =
      Affine.Point.some
        ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (mulByInt_x W r))
        ((FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (mulByInt_y W r))
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          (RingHom.injective
            (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField).toRingHom)
          (mulByInt_x W r) (mulByInt_y W r)).mpr hns) := by
    rw [hgeo, hsmul', frobeniusW_KE_some]
  -- Pullback side: `(r·π).pullback g = π.pullback ((mulByInt r).pullback g) = (mulByInt_? r)^q`.
  -- The inner `(mulByInt r)`-pullback of the generators is `mulByInt_x/y r`.
  have hmx : (mulByInt W.toAffine r).pullback (x_gen W) = mulByInt_x W r :=
    mulByInt_pullback_x W r hr
  have hmy : (mulByInt W.toAffine r).pullback (y_gen W) = mulByInt_y W r :=
    mulByInt_pullback_y W r hr
  refine ⟨_, _, _, himg, ?_, ?_⟩
  · show (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (mulByInt_x W r) =
      ((frobeniusIsog W).zsmul r).pullback (x_gen W)
    rw [Isogeny.zsmul, Isogeny.comp_algebraMap_eq, hmx,
      frobeniusIsog_pullback_apply, FiniteField.coe_frobeniusAlgHom]
  · show (FiniteField.frobeniusAlgHom K W.toAffine.FunctionField) (mulByInt_y W r) =
      ((frobeniusIsog W).zsmul r).pullback (y_gen W)
    rw [Isogeny.zsmul, Isogeny.comp_algebraMap_eq, hmy,
      frobeniusIsog_pullback_apply, FiniteField.coe_frobeniusAlgHom]

/-- **Genuineness is closed under the genuine sum (`addIsog`).** If `α₁` is genuine with geometric
action `g₁` and `α₂` with `g₂`, then their genuine sum `addIsog hxy hinj` (the isogeny with
pullback `P ↦ α₁(P) + α₂(P)` on `K(E)`) is genuine with geometric action `g₁ + g₂`.

This is the structural heart of the non-vacuity for `genuineIsogSmulSub = (r·π) ⊞ (−s)`: the
addition formula `addPullback_x/y_pair` (which *is* `addIsog`'s pullback on the generators, by
`addPullbackAlgHomPair_x/y_gen_eq`) coincides with the group-law `addX/addY` of the two component
geometric images of the generic point (`Affine.Point.add_some`). -/
theorem addIsog_isGenuineWith {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂)
    (hinj : Function.Injective (addCoordAlgHomPair hxy))
    {g₁ g₂ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (h₁ : IsGenuineWith W α₁ g₁) (h₂ : IsGenuineWith W α₂ g₂) :
    IsGenuineWith W (addIsog hxy hinj) (g₁ + g₂) := by
  obtain ⟨X₁, Y₁, hns₁, hg₁, hx₁, hy₁⟩ := h₁
  obtain ⟨X₂, Y₂, hns₂, hg₂, hx₂, hy₂⟩ := h₂
  -- The non-inverse hypothesis, restated at the component image coordinates `(X₁,Y₁), (X₂,Y₂)`.
  have hxy' : ¬(X₁ = X₂ ∧ Y₁ = (W_KE W).toAffine.negY X₂ Y₂) := by
    rwa [hx₁, hx₂, hy₁, hy₂]
  -- Sum of the two geometric images is `some (addX..) (addY..)`.
  have hsum : (g₁ + g₂) (genericPoint W) =
      Affine.Point.some
        ((W_KE W).toAffine.addX X₁ X₂ ((W_KE W).toAffine.slope X₁ X₂ Y₁ Y₂))
        ((W_KE W).toAffine.addY X₁ X₂ Y₁ ((W_KE W).toAffine.slope X₁ X₂ Y₁ Y₂))
        (WeierstrassCurve.Affine.nonsingular_add hns₁ hns₂ hxy') := by
    rw [AddMonoidHom.add_apply, hg₁, hg₂, WeierstrassCurve.Affine.Point.add_some hxy']
  -- The pullback of `addIsog` on the generators is `addPullback_x/y_pair` = `addX/addY`.
  refine ⟨_, _, _, hsum, ?_, ?_⟩
  · -- `addX X₁ X₂ slope = addPullback_x_pair α₁ α₂ = (addIsog).pullback x_gen`.
    rw [addIsog_pullback, OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq]
    unfold addPullback_x_pair addSlopePair
    rw [hx₁, hx₂, hy₁, hy₂]
  · rw [addIsog_pullback, OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq]
    unfold addPullback_y_pair addSlopePair
    rw [hx₁, hx₂, hy₁, hy₂]

/-- **The genuine `r·π − s` isogeny is genuine** (in the technical `IsGenuine` sense), with
geometric action `P ↦ r • frobeniusW_KE P + (−s) • P` on `K(E)`-points.

This is the substantive non-vacuity statement for the application: `genuineIsogSmulSub` is the
`addIsog` of the genuine pair `(r·π, −s·id)`, and both components are genuine
(`zsmul_frobeniusIsog_isGenuineWith`, `mulByInt_isGenuineWith`), so the genuine-sum combinator
`addIsog_isGenuineWith` delivers genuineness of the whole.  It confirms `IsGenuine` is a real,
non-vacuous predicate satisfied by the actual isogeny appearing in Leaf 1's generic case. -/
theorem genuineIsogSmulSub_isGenuineWith
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    IsGenuineWith W (genuineIsogSmulSub W r s hr hs hrK hsK)
      (((zsmulPointHom W r).comp (frobeniusW_KE W)) + zsmulPointHom W (-s)) := by
  -- `genuineIsogSmulSub = addIsog (r·π, −s)`; apply the genuine-sum combinator.  The
  -- `AddNonInverse` and injectivity witnesses are propositions (proof-irrelevant), so
  -- `addIsog_isGenuineWith` applies to the unfolded `addIsog` form regardless of the witnesses.
  unfold genuineIsogSmulSub genuineIsogSmulSub_of_pole
  exact addIsog_isGenuineWith W _ _
    (zsmul_frobeniusIsog_isGenuineWith W r hr)
    (mulByInt_isGenuineWith W (-s) (neg_ne_zero.mpr hs))

/-- **The genuine `r·π − s` isogeny is genuine** (existential form). -/
theorem genuineIsogSmulSub_isGenuine
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    IsGenuine W (genuineIsogSmulSub W r s hr hs hrK hsK) :=
  ⟨_, genuineIsogSmulSub_isGenuineWith W r s hr hs hrK hsK⟩

/- Separability of the genuine `r·π − s` isogeny (Silverman III.5.5 / Theorem 5.6)

For `p ∤ s`, the genuine `r·π − s` isogeny is **separable**: its invariant-differential pullback
coefficient is `a_{rπ − s} = r·a_π − s = r·0 − s = −s ≠ 0` (Silverman III.5.2 additivity + III.5.3
`a_{[m]} = m` + III.5.5 `a_π = 0`).  This is a *composition* of the shipped omega-coefficient facts:

* `omegaPullbackCoeff_addIsog_pair` — the general-pair III.5.2 additivity (built above);
* `omegaPullbackCoeff_comp_of_base` + `omegaPullbackCoeff_frobenius = 0` — `a_{r·π} = r·0 = 0`;
* `omegaPullbackCoeff_mulByInt_routeB` — `a_{[−s]} = −s`;
* `isSeparable_iff_omegaPullbackCoeff_ne_zero` — the separability criterion (T-II-4-004). -/

/-- **`a_{r·π − s} = −s`** (Silverman III.5.2/III.5.3/III.5.5): the omega-pullback coefficient
of the genuine `r·π − s` isogeny is `algebraMap K KE (−s)`.  Pure composition of the shipped
omega facts via the general-pair additivity `omegaPullbackCoeff_addIsog_pair`. -/
theorem genuineIsogSmulSub_omegaPullbackCoeff
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    omegaPullbackCoeff W (genuineIsogSmulSub W r s hr hs hrK hsK) =
      algebraMap K W.toAffine.FunctionField (-s) := by
  -- `a_{r·π} = a_{[r] ∘ π} = (r : K)·a_π = (r : K)·0 = 0` (chain rule + Frobenius differential).
  have h_frob : omegaPullbackCoeff W ((frobeniusIsog W).zsmul r) = 0 := by
    change omegaPullbackCoeff W ((mulByInt W.toAffine r).comp (frobeniusIsog W)) = 0
    rw [omegaPullbackCoeff_comp_of_base W (mulByInt W.toAffine r) (frobeniusIsog W)
        ((r : K)) (omegaPullbackCoeff_mulByInt_routeB W r hr),
      omegaPullbackCoeff_frobenius, mul_zero]
  -- `a_{[−s]} = (−s : K)`.
  have h_neg : omegaPullbackCoeff W (mulByInt W.toAffine (-s)) =
      algebraMap K W.toAffine.FunctionField (-s) := by
    rw [omegaPullbackCoeff_mulByInt_routeB W (-s) (neg_ne_zero.mpr hs)]
    push_cast
    ring
  -- `r·π − s = addIsog (r·π) (−s)`; apply general-pair additivity.
  unfold genuineIsogSmulSub genuineIsogSmulSub_of_pole
  rw [omegaPullbackCoeff_addIsog_pair W _ _
      (zsmul_frobenius_pullback_x_ne_mulByInt_neg_pullback_x W r s hr hs hrK hsK),
    h_frob, h_neg, zero_add]

/-- **The genuine `r·π − s` isogeny is separable** (Silverman III.5.5, `p ∤ s`).  From
`a_{r·π − s} = −s ≠ 0` (which holds since `(s : K) ≠ 0`, i.e. `p ∤ s`) via the separability
criterion `isSeparable_iff_omegaPullbackCoeff_ne_zero` (T-II-4-004).  This discharges the
`hsep` hypothesis of the pencil `#ker = deg` witness (`pencil_hkerdeg_of_separable_witnesses`)
at the K-field level; the K̄-level separability follows by base-change stability
(`omegaPullbackCoeff_baseChangePullback`). -/
theorem genuineIsogSmulSub_isSeparable
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (genuineIsogSmulSub W r s hr hs hrK hsK).IsSeparable := by
  rw [isSeparable_iff_omegaPullbackCoeff_ne_zero,
    genuineIsogSmulSub_omegaPullbackCoeff W r s hr hs hrK hsK]
  -- `algebraMap K KE (−s) ≠ 0` since `(−s : K) ≠ 0` (`p ∤ s`).
  rw [Ne, map_eq_zero]
  exact neg_ne_zero.mpr hsK

/- Composition-genuineness (the "functorial at the image point" residual)

`IsGenuineWith φ g` constrains the geometric action `g` **only at the single generic point**
`P_gen = (x_gen, y_gen)`.  To upgrade a composition `ψ.comp φ` to a genuine isogeny we need to
know the action of `ψ` not at `P_gen` but at the *image point* `g_φ(P_gen)` — a "second-order
generic point".  Concretely, `(ψ.comp φ).pullback x_gen = φ.pullback (ψ.pullback x_gen)`
(`comp_algebraMap_eq`), and the generic-point genuineness of `φ` gives
`g_φ(P_gen) = some (φ.pullback x_gen) (φ.pullback y_gen)`; closing the gap to
`(g_ψ ∘ g_φ)(P_gen) = some ((ψ.comp φ).pullback x_gen) (…)` requires `g_ψ` to be **functorial
at `g_φ(P_gen)`**, landing on exactly the composite-pullback coordinates.

Crucially this functoriality is *not* derivable from `IsGenuineWith ψ g_ψ` alone: the library's
`Isogeny.comp` stores `pullback := φ.pullback.comp ψ.pullback` (contravariant) while the geometric
actions compose covariantly (`g_ψ ∘ g_φ`), so no single `Affine.Point.map`-of-an-`AlgHom` model
of the action is preserved by `comp` (unless the two pullbacks commute — e.g. iterated Frobenius).
Hence we take the functoriality of `g_ψ` at the image point as an explicit hypothesis: this is
exactly the content a genuine *geometric* isogeny `ψ` supplies (its action on `K(E)`-points is the
comorphism `ψ.pullback` applied along the substitution at the relevant point), and for the
application it is what the V-side (Wall A) construction of `r·V − s` delivers. -/

/-- **`g_ψ` is functorial at the image point `(A, B)`** for the composite `ψ.comp φ`: the action
`g_ψ` sends the point with coordinates `(A, B) = (φ.pullback x_gen, φ.pullback y_gen)` (the
generic-point image under `φ`) to the point whose coordinates are the composite pullback values
`((ψ.comp φ).pullback x_gen, (ψ.comp φ).pullback y_gen)`.

This is the precise "second-order generic point" functoriality the composition-genuineness needs;
it is a *real* condition (it equates a geometric image with the contravariant composite comorphism
evaluated on the generators), not a vacuous one.  For a genuine geometric isogeny `ψ` it holds
because `g_ψ` is the comorphism of `ψ` and `φ.pullback x_gen` is, by genuineness of `φ`, the
`x`-coordinate of a genuine point of `W_KE` on which `ψ`'s comorphism acts by `ψ.pullback`. -/
def FunctorialAtImage (φ ψ : Isogeny W.toAffine W.toAffine)
    (g_ψ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point) : Prop :=
  ∀ (A B : W.toAffine.FunctionField) (h : (W_KE W).toAffine.Nonsingular A B),
    A = φ.pullback (x_gen W) → B = φ.pullback (y_gen W) →
      ∃ (h' : (W_KE W).toAffine.Nonsingular
          ((ψ.comp φ).pullback (x_gen W)) ((ψ.comp φ).pullback (y_gen W))),
        g_ψ (Affine.Point.some A B h) =
          Affine.Point.some
            ((ψ.comp φ).pullback (x_gen W)) ((ψ.comp φ).pullback (y_gen W)) h'

omit [Fintype K] [Fintype W.toAffine.Point] in
/-- **Composition-genuineness (general form).** If `φ` is genuine with geometric action `g_φ`,
the abstract action `g_ψ` of `ψ` is functorial at the image point `g_φ(P_gen)` (lands on the
composite-pullback coordinates), and the composite action `g_ψ ∘ g_φ` carries the generic point to
`N • P_gen` (the curve-side Cayley–Hamilton at the generic point), then the composition `ψ.comp φ`
is **genuine with the multiplication-by-`N` action** `zsmulPointHom N`.

This is the structural lemma that discharges the `h_comp_genuine` hypothesis of
`genuine_dual_comp_eq_mulByInt_of_isGenuineWith` from (i) the already-shipped generic-point
genuineness of `φ = r·π − s`, (ii) the End-relation `(r·V − s)(r·π − s) = [N]` at the generic
point, and (iii) the V-side functoriality at the image point (the honest Wall-A residue). -/
theorem genuine_comp_isGenuineWith_of_functorial
    {φ ψ : Isogeny W.toAffine W.toAffine}
    {g_φ g_ψ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (N : ℤ)
    (hφ : IsGenuineWith W φ g_φ)
    (h_func : FunctorialAtImage W φ ψ g_ψ)
    (h_end : g_ψ (g_φ (genericPoint W)) = N • genericPoint W) :
    IsGenuineWith W (ψ.comp φ) (zsmulPointHom W N) := by
  -- Generic-point image under `φ`: `g_φ P_gen = some (φ.pullback x_gen) (φ.pullback y_gen)`.
  obtain ⟨A, B, hAB, hgφ, hAx, hBy⟩ := hφ
  -- Functoriality of `g_ψ` at that image point: lands on the composite-pullback coordinates.
  obtain ⟨h', hψimg⟩ := h_func A B hAB hAx hBy
  -- Assemble: `N • P_gen = g_ψ (g_φ P_gen) = some ((ψ∘φ)*x_gen) ((ψ∘φ)*y_gen)`.
  refine ⟨(ψ.comp φ).pullback (x_gen W), (ψ.comp φ).pullback (y_gen W), h', ?_, rfl, rfl⟩
  rw [show zsmulPointHom W N (genericPoint W) = N • genericPoint W from rfl,
    ← h_end, hgφ, hψimg]

/-- **Composition-genuineness for the genuine `r·π − s` family (witness-parametric on the V-side).**

Specialises `genuine_comp_isGenuineWith_of_functorial` to `φ = genuineIsogSmulSub W r s = r·π − s`
(whose generic-point genuineness is the shipped `genuineIsogSmulSub_isGenuineWith`) and an abstract
V-side action `g_V` of `β_dual` (the `r·V − s` isogeny).  It discharges exactly the
`h_comp_genuine` hypothesis consumed by `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`, **modulo
two honest V-side inputs** that the Wall-A construction of `r·V − s` supplies:

* `h_V_func`: `g_V` is functorial at the image point `(r·π − s)(P_gen)` (the comorphism property of
  the genuine geometric isogeny `r·V − s`);
* `h_end`: the curve-side Cayley–Hamilton `(r·V − s)(r·π − s) = [N]` evaluated at the generic
  point, i.e. `g_V ((r·π − s)-action (P_gen)) = N • P_gen` with
  `N = q·r² − t·r·s + s²`.

No new generic-point genuineness for `r·π − s` is assumed — it is the shipped
`genuineIsogSmulSub_isGenuineWith`. -/
theorem genuineIsogSmulSub_comp_isGenuineWith_mulByInt
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (β_dual : Isogeny W.toAffine W.toAffine)
    (g_V : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point)
    (h_V_func : FunctorialAtImage W (genuineIsogSmulSub W r s hr hs hrK hsK) β_dual g_V)
    (h_end : g_V ((((zsmulPointHom W r).comp (frobeniusW_KE W)) + zsmulPointHom W (-s))
        (genericPoint W)) =
      ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
        • genericPoint W) :
    IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK))
      (zsmulPointHom W
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)) :=
  genuine_comp_isGenuineWith_of_functorial W _
    (genuineIsogSmulSub_isGenuineWith W r s hr hs hrK hsK) h_V_func h_end

/-- **Pivot lift to FULL isogeny composition (witness-parametric)**: given the AddMonoidHom-level
Cayley-Hamilton (from `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`) AND a pullback-level
identity (the "double-Vieta match"), conclude the FULL isogeny equality
`β_dual.comp β = mulByInt N`.

This combines `Isogeny_eq_of_components` (structural extensionality) with the two
component-level equalities. The pullback-level identity `h_pullback_eq` is the substantive
SUB-PIV-C2 Wall B remaining content (~hundreds of LOC of double-Vieta match polynomial
algebra). -/
theorem genuine_dual_comp_eq_mulByInt_of_components
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (h_pullback_eq :
      (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).pullback =
      (mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)).pullback) :
    β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK) =
      mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) :=
  Isogeny.eq_of_components h_pullback_eq
    (genuine_dual_comp_toAddMonoidHom_eq_mulByInt W hq r s hr hs hrK hsK V β_dual
      h_isDual h_sum_trace h_beta_dual_hom)

/-- **Wall-B killer applied: full-isogeny composition identity from the genuine-action witness.**

This replaces the raw pullback-level hypothesis `h_pullback_eq` of
`genuine_dual_comp_eq_mulByInt_of_components` (the "double-Vieta match", hundreds of LOC) with the
*structural* hypothesis that the composition `β_dual ∘ (rπ − s)` is **genuine with the same
geometric action as `[N]`** — namely `P ↦ N • P` (`zsmulPointHom W N`).  Given that, the
extensionality lemma `genuine_isogeny_ext` (combining `mulByInt_isGenuineWith` with the shipped
AddMonoidHom identity `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`) upgrades the shipped
point-map identity to the full isogeny equality `β_dual ∘ (rπ − s) = [N]`.

The remaining content is now isolated to a single clean statement: that the composition's
*geometric action on `K(E)`-points* is `[N]` (equivalently, that the curve-side Cayley–Hamilton
`(rV − s) ∘ (rπ − s) = [N]` holds at the level of `(W_KE).Point`).  This is the honest residue of
Wall B, with the pullback/comorphism bookkeeping fully discharged. -/
theorem genuine_dual_comp_eq_mulByInt_of_isGenuineWith
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    (h_comp_genuine :
      IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK))
        (zsmulPointHom W
          ((Fintype.card K : ℤ) * r ^ 2 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2))) :
    β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK) =
      mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) := by
  -- The AddMonoidHom side is the shipped Cayley–Hamilton; the pullback side is the Wall-B killer.
  refine Isogeny.eq_of_components ?_
    (genuine_dual_comp_toAddMonoidHom_eq_mulByInt W hq r s hr hs hrK hsK V β_dual
      h_isDual h_sum_trace h_beta_dual_hom)
  -- Both `β_dual ∘ (rπ−s)` and `[N]` are genuine with the SAME geometric action `zsmulPointHom N`.
  exact genuine_isogeny_ext_pullback W h_comp_genuine (mulByInt_isGenuineWith W _ hN_ne)

/-- **Wall-B killer, fully wired from the V-side residue.** This is
`genuine_dual_comp_eq_mulByInt_of_isGenuineWith` with its single structural hypothesis
`h_comp_genuine` *discharged* via `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`: instead of
assuming the composite `β_dual ∘ (r·π − s)` is genuine with the `[N]`-action, it takes the two
honest V-side inputs that the Wall-A construction of `r·V − s` supplies and produces the full
isogeny identity `β_dual ∘ (r·π − s) = [N]`.

The remaining content is now exactly the V-side residue — *no* generic-point genuineness of
`r·π − s` is assumed (it is the shipped `genuineIsogSmulSub_isGenuineWith`), and the pullback /
comorphism bookkeeping is fully discharged:

* `h_V_func`: `g_V` (the action of `r·V − s`) is functorial at the image point `(r·π − s)(P_gen)`;
* `h_end`: the curve-side Cayley–Hamilton `(r·V − s)(r·π − s) = [N]` at the generic point. -/
theorem genuine_dual_comp_eq_mulByInt_of_V_functorial
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (g_V : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point)
    (h_isDual : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    (h_V_func : FunctorialAtImage W (genuineIsogSmulSub W r s hr hs hrK hsK) β_dual g_V)
    (h_end : g_V ((((zsmulPointHom W r).comp (frobeniusW_KE W)) + zsmulPointHom W (-s))
        (genericPoint W)) =
      ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
        • genericPoint W) :
    β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK) =
      mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) :=
  genuine_dual_comp_eq_mulByInt_of_isGenuineWith W hq r s hr hs hrK hsK V β_dual
    h_isDual h_sum_trace h_beta_dual_hom hN_ne
    (genuineIsogSmulSub_comp_isGenuineWith_mulByInt W hq r s hr hs hrK hsK β_dual g_V
      h_V_func h_end)

/-- **GAP-QF SIGNED L1 from pivot components (composer)**: takes the V-side witnesses
(IsDualOf V π + sum_trace π+V=[t] + the V-side β_dual) AND the substantive Vieta match
at the pullback level, concludes the SIGNED III.6.3 identity
`((genuineIsogSmulSub W r s).degree : ℤ) = N`.

This is the all-witness-parametric form: every substantive piece is a hypothesis,
the conclusion is the SIGNED L1 (Silverman III.6.3 non-circular). (The unconditional
sorried form `genuineIsogSmulSub_degree_eq_signed` was retired 2026-06-11 with the legacy
skeleton chain; the witness-parametric forms here and `_via_walls` below are the shipped
results.)

Composes (1) `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`, (2)
`genuine_dual_comp_eq_mulByInt_of_components`, and (3) `signed_degree_of_genuine_dual_pair`. -/
theorem genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (h_pullback_eq :
      (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).pullback =
      (mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)).pullback)
    (h_isDual_pair :
      IsDualOf W.toAffine β_dual (genuineIsogSmulSub W r s hr hs hrK hsK))
    (h_beta_pos : 0 < (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (h_N_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  have h_comp := genuine_dual_comp_eq_mulByInt_of_components W hq r s hr hs hrK hsK
    V β_dual h_isDual_V_pi h_sum_trace h_beta_dual_hom h_pullback_eq
  exact signed_degree_of_genuine_dual_pair _ β_dual _ h_N_ne h_isDual_pair h_beta_pos h_comp

/-- **Nonconstancy of the genuine `r·π − s` isogeny (axiom-clean, unconditional)**:
`0 < (genuineIsogSmulSub W r s).degree`.

This discharges the structural `h_beta_pos` hypothesis of the III.6.3 degree bridges.
It is a direct specialization of the unconditional `isogeny_degree_pos` (every isogeny's
pullback is an injective field hom, so `K(E)` is a nonzero finite-dimensional extension of
its image, hence `degree = Module.finrank > 0`).  No dual/pivot input is needed. -/
theorem genuineIsogSmulSub_degree_pos
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    0 < (genuineIsogSmulSub W r s hr hs hrK hsK).degree :=
  isogeny_degree_pos W (genuineIsogSmulSub W r s hr hs hrK hsK)

/-- **GAP-QF non-circular III.6.3, generic case, witness-parametric** (Silverman III.6.3, p. 99):
the degree of the genuine `r·π − s` isogeny EQUALS the quadratic-form value
`q·r² − t·r·s + s²` as a SIGNED integer, derived via SUB-PIV-D from the pivot witnesses
`IsDualOf (rV-s) (rπ-s)` + `(rV-s).comp (rπ-s) = mulByInt N`.

This is the NON-CIRCULAR form — once the pivot's substantive content (full isogeny dual
relationship for the `(rV-s, rπ-s)` pair) ships, the SIGNED III.6.3 identity follows
algebraically via Wall C. -/
theorem genuineIsogSmulSub_degree_eq_signed_of_pivot_witness (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual : IsDualOf W.toAffine β_dual (genuineIsogSmulSub W r s hr hs hrK hsK))
    (h_beta_pos : 0 < (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (h_N_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    (h_comp_eq : β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK) =
      mulByInt W.toAffine ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 :=
  signed_degree_of_genuine_dual_pair _ β_dual _ h_N_ne h_isDual h_beta_pos h_comp_eq

/-- **GAP-QF SIGNED L1 via the Wall-A bridge (consolidated single-deep-gap route).**

This is the *Wall-A-routed* form of the signed III.6.3 identity (whose unconditional
sorried form `genuineIsogSmulSub_degree_eq_signed` was retired 2026-06-11): it derives the SIGNED
III.6.3 degree identity by routing the substantive composition equality
`β_dual ∘ (r·π − s) = [N]` through the **shipped, axiom-clean**
`genuine_dual_comp_eq_mulByInt_of_V_functorial` bridge (Wall B-killer fed by the V-side genuine
`r·V − s`), then extracting the degree via Wall C (`signed_degree_of_genuine_dual_pair`).

**Why this consolidates the route to a single deep gap.**  The previous (now-deleted)
sorried forms `genuineIsogSmulSub_degree_eq_signed` (here) and `genuineIsogSmulSub_pivot_witness`
(`Hasse/QuadraticForm.lean`) carried their *own* deep `sorry` — the Pic⁰ pivot's full-isogeny dual
relationship — *separate* from the Wall-A bridge.  Routing through
`genuine_dual_comp_eq_mulByInt_of_V_functorial` instead means the composition equality `β_dual ∘ β
= [N]` is no longer an independent assumption: it is produced by the shipped bridge from the
V-side inputs, whose *only* deep dependency is the genuine `r·V − s` construction
(`genuineIsogSmulSubV_universal_unconditional`) — which bottoms out at **Wall A**
(`addPullback_x_pair_sum_reduces_to_O`, `Verschiebung/Genuine.lean`) → **BRIDGE-003**
(`formalIsogenySeries_add`).  The two remaining hypotheses here, `h_isDual` (the III.6.1 dual
relation `IsDualOf β_dual β`) and `h_beta_pos` (nonconstancy `0 < deg β`), are *structural* pivot
facts present identically in *both* routes — they are NOT the BRIDGE-003 deep gap, and they are the
same inputs the Pic⁰-pivot route bundles.  Hence the genuine-case degree identity now has a single
deep gap on the Wall-A/BRIDGE-003 axis, replacing the previous two independent deep routes.

The all-substantive-V-side inputs `(V, g_V, h_isDual_V_pi, h_sum_trace, h_beta_dual_hom, h_V_func,
h_end)` are exactly the hypotheses of `genuine_dual_comp_eq_mulByInt_of_V_functorial`; the
`h_isDual`/`h_beta_pos` pair are the Wall-C inputs.  See that bridge's docstring for the precise
V-side residue. -/
theorem genuineIsogSmulSub_degree_eq_signed_via_walls (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (g_V : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    (h_V_func : FunctorialAtImage W (genuineIsogSmulSub W r s hr hs hrK hsK) β_dual g_V)
    (h_end : g_V ((((zsmulPointHom W r).comp (frobeniusW_KE W)) + zsmulPointHom W (-s))
        (genericPoint W)) =
      ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
        • genericPoint W)
    (h_isDual : IsDualOf W.toAffine β_dual (genuineIsogSmulSub W r s hr hs hrK hsK))
    (h_beta_pos : 0 < (genuineIsogSmulSub W r s hr hs hrK hsK).degree) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- Wall-A bridge: the substantive composition equality `β_dual ∘ (r·π − s) = [N]`, produced from
  -- the V-side genuine `r·V − s` inputs (no independent Pic⁰ pivot).
  have h_comp_eq := genuine_dual_comp_eq_mulByInt_of_V_functorial W hq r s hr hs hrK hsK
    V β_dual g_V h_isDual_V_pi h_sum_trace h_beta_dual_hom hN_ne h_V_func h_end
  -- Wall C: extract the SIGNED degree from `[deg β] = β_dual ∘ β = [N]` (mulByInt injectivity).
  exact signed_degree_of_genuine_dual_pair
    (genuineIsogSmulSub W r s hr hs hrK hsK) β_dual _ hN_ne h_isDual h_beta_pos h_comp_eq

/-- **GAP-QF SIGNED L1 via the Wall-A bridge, with `h_beta_pos` discharged internally.**

Identical to `genuineIsogSmulSub_degree_eq_signed_via_walls` but DROPS the `h_beta_pos`
(`0 < deg β`) hypothesis: nonconstancy of `r·π − s` is *unconditionally true*
(`genuineIsogSmulSub_degree_pos`, an `#print axioms`-clean specialization of `isogeny_degree_pos`),
so it is supplied internally rather than assumed.

All OTHER hypotheses are retained verbatim — in particular `h_isDual`
(`IsDualOf β_dual (r·π−s)`) remains parametric, as it is a genuine deep residual (general dual
existence) outside the scope of this discharge.  The substantive composition equality is still
produced by the shipped, axiom-clean Wall-A bridge `genuine_dual_comp_eq_mulByInt_of_V_functorial`
from the V-side inputs, exactly as in the un-primed form. -/
theorem genuineIsogSmulSub_degree_eq_signed_via_walls' (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (g_V : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    (h_V_func : FunctorialAtImage W (genuineIsogSmulSub W r s hr hs hrK hsK) β_dual g_V)
    (h_end : g_V ((((zsmulPointHom W r).comp (frobeniusW_KE W)) + zsmulPointHom W (-s))
        (genericPoint W)) =
      ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
        • genericPoint W)
    (h_isDual : IsDualOf W.toAffine β_dual (genuineIsogSmulSub W r s hr hs hrK hsK)) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 :=
  genuineIsogSmulSub_degree_eq_signed_via_walls W hq r s hr hs hrK hsK V β_dual g_V
    h_isDual_V_pi h_sum_trace h_beta_dual_hom hN_ne h_V_func h_end h_isDual
    (genuineIsogSmulSub_degree_pos W r s hr hs hrK hsK)

/-- **GAP-QF edge case, witness-parametric** (III.6.3 at the degenerate `(r,s)`): when `r`
or `s` vanishes in `K` and both are nonzero in ℤ (char-divisible sub-case), supplied an
explicit witness isogeny realizing the QF value yields the existence statement.

This is the witness-parametric form of the SUB-L2C/D leaf. The substantive content is
the explicit construction of β (either via the inseparable `r·π − s` chain through
Frobenius/Verschiebung factorization, or via the Pic⁰ pivot). -/
theorem degree_quadratic_exists_edge_of_witness (hq : 2 ≤ Fintype.card K) (r s : ℤ)
    (β : Isogeny W.toAffine W.toAffine)
    (h_beta_deg : (β.degree : ℤ) = (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) :
    ∃ β' : Isogeny W.toAffine W.toAffine,
      (β'.degree : ℤ) = (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 :=
  ⟨β, h_beta_deg⟩

/- Easy edge-case discharges of the III.6.3 boundary (the L2 edge case).

The edge case `(r:K) = 0 ∨ (s:K) = 0` splits into "trivial" sub-cases
(`r = 0 ∈ ℤ` or `s = 0 ∈ ℤ`, where the natural β is `[s]` or `[r]∘π` with
known degree) and "char-divisible" sub-cases (`p ∣ r ∨ p ∣ s` with both
`r, s ≠ 0 ∈ ℤ`). The lemmas below dispatch the trivial sub-cases; the
char-divisible stubs (`degree_quadratic_exists_edge_*_char_divisible`) were
REFUTED as stated (B2-logged, supersingular `t² = 4q` null pairs) and deleted
2026-06-11 together with their consumer `degree_quadratic_exists_edge`. -/

omit [Fintype W.toAffine.Point] in
/-- **L2 easy: `r = 0 ∈ ℤ` case, `s ≠ 0 ∈ ℤ`** (Silverman III.6.3 boundary):
take `β := [s]` (multiplication-by-`s`). Then `β.degree = s²` matches the
quadratic-form value `q·0² − t·0·s + s² = s²`. -/
theorem degree_quadratic_exists_edge_r_int_zero
    (hq : 2 ≤ Fintype.card K) (s : ℤ) (hs : s ≠ 0) :
    ∃ β : Isogeny W.toAffine W.toAffine,
      (β.degree : ℤ) = (Fintype.card K : ℤ) * (0 : ℤ) ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * 0 * s + s ^ 2 := by
  refine ⟨mulByInt W.toAffine s, ?_⟩
  rw [mulByInt_degree W.toAffine s hs]
  push_cast
  rw [Int.toNat_of_nonneg (sq_nonneg s)]
  ring

omit [Fintype W.toAffine.Point] in
/-- **L2 easy: `s = 0 ∈ ℤ` case, `r ≠ 0 ∈ ℤ`** (Silverman III.6.3 boundary):
take `β := π ∘ [r]` (Frobenius after multiplication-by-`r`). Then
`β.degree = deg([r]) · deg(π) = r² · q` matches the quadratic-form value
`q·r² − t·r·0 + 0² = q·r²`. -/
theorem degree_quadratic_exists_edge_s_int_zero
    (hq : 2 ≤ Fintype.card K) (r : ℤ) (hr : r ≠ 0) :
    ∃ β : Isogeny W.toAffine W.toAffine,
      (β.degree : ℤ) = (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * 0 +
          (0 : ℤ) ^ 2 := by
  refine ⟨(frobeniusIsog W).comp (mulByInt W.toAffine r), ?_⟩
  rw [Isogeny.comp_degree, mulByInt_degree W.toAffine r hr, frobeniusIsog_degree]
  push_cast
  rw [Int.toNat_of_nonneg (sq_nonneg r)]
  ring

/-- **GAP-QF top leaf, ALL-WITNESS-PARAMETRIC CHAIN** (Silverman III.6.3 via Pic⁰ pivot):
takes the FULL chain of pivot witnesses for every `(r, s)` (generic case via Wall A/B/C + edge
cases via explicit isogeny witnesses), yields `qf_nonneg` for every `(r, s)`.

This is the all-witness-parametric form; the sorried unconditional chain
(`qf_nonneg_skeleton` ← `degree_quadratic_exists_skeleton_nonzero` ←
`degree_quadratic_exists_edge` / `genuineIsogSmulSub_degree_eq_signed`) was retired
2026-06-11 — III.6.3 non-negativity is proven on the live route via
`WeilPairing/HasseAssembly.lean`'s `qf_nonneg_skeleton_of_weil_det_data`. -/
theorem qf_nonneg_skeleton_of_pivot_chain
    (hq : 2 ≤ Fintype.card K)
    (h_realization :
      ∀ r s : ℤ, ¬ (r = 0 ∧ s = 0) →
        ∃ β : Isogeny W.toAffine W.toAffine,
          (β.degree : ℤ) = (Fintype.card K : ℤ) * r ^ 2 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) :
    ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  intro r s
  by_cases h_zero : r = 0 ∧ s = 0
  · obtain ⟨hr0, hs0⟩ := h_zero
    subst hr0 hs0
    simp
  obtain ⟨β, hβ⟩ := h_realization r s h_zero
  rw [← hβ]
  exact Int.natCast_nonneg _

end HasseWeil
