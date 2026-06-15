import BernoulliRegular.FLT37.Eichler.CaseIICor823SecondOrderEndpoint
import BernoulliRegular.FLT37.Eichler.CaseIICor823Omega32Collapse

/-!
# `Prop812DescentCoeff37` reduced to the single-column second-order coefficient
`Prop812SecondOrderCoeff37`

This file discharges the descent-unit second-order leading-coefficient residual
`Prop812DescentCoeff37` (`CaseIICor823SecondOrderEndpoint.lean`) — Washington Proposition 8.12 at
the irregular index `i = 32`, on the descent unit — **down to the single-column second-order
coefficient value** `Prop812SecondOrderCoeff37` (`CaseIICor823SecondOrderMatrix.lean`).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The reduction (everything but the single-column coefficient value is proven here)

`Prop812DescentCoeff37` asks, for `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u − c`, for a lift
`D : ZMod (37²)` of the `j = 15` free-part eigencomponent `c₁₅ = decomp (φ u) 15` with
`detector(u) = (B₃₂/32 mod 37²)·D`.

The **proven** second-order detector vanishing `caseIICor823SecondOrder_detector_descent_eq_zero`
makes `detector(u) = 0`.  So, with `factor = 37·r` (`r` a unit mod `37`,
`caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul`), the lift `D` exists **iff**
`c₁₅ = 0`: if `c₁₅ = 0` take `D = 0`; conversely `factor·D = 0` with `castHom D = c₁₅` forces
`c₁₅ = 0` (the proven `cor823Omega32SecondOrderCollapse37_of_prop812`).

So the genuine content of `Prop812DescentCoeff37` is `c₁₅ = 0`
(`Cor823Omega32SecondOrderCollapse37`).  We **prove** that from the single-column second-order
coefficient value `Prop812SecondOrderCoeff37` (the genuine `p`-adic-`L` content — the level-`68`
mod-`37²` Dwork coefficient of the `i = 32` cyclotomic column equals `B₃₂/32 mod 37²` times the
Teichmüller-Vandermonde row), via:

* **the `p`-saturation split** `u = v_C · w^{37}` (`37 ∤ h⁺`,
  `caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup`), `v_C = CPlusExponentProduct s e`,
  giving `completedLog(u^{36}) = ∑_a e_a • kummerLogCompletedColumn a + 37 • Y`
  (`Y = completedLog(EPlus_…PowPred w)`);
* **the second-order detector additivity**: `detector(u) = D_vC + 37 · coeff_Y`, where `D_vC` is
  the `varpi^{32}` mod-`37²` coordinate of the cyclotomic-column sum and `coeff_Y` is that of `Y`;
* **the single-column coefficient value** `Prop812SecondOrderCoeff37`: `D_vC = factor · V₁₅` with
  `V₁₅ = ∑_a (((a+2)²)^{16} − 1) (e_a : ZMod 37²)` the mod-`37²` Vandermonde row;
* **the `37`-th-power-correction first-order vanishing** (`§1`, proven): the `varpi^{32}` mod-`37`
  coordinate of *any* real unit's completed log vanishes (the first-order row-`15` factor
  `kummerLogDetRowFactor 15 = B₃₂/32 mod 37 = 0` is `0`), so `castHom coeff_Y = 0`;
* **the proven `j = 15` second-Vandermonde inversion**
  `caseIIEx811Eigen_vandermonde_eq_nine_smul` (value `9 ≠ 0`): `V₁₅ mod 37 = 9·c₁₅`.

Combining: `0 = detector(u) = 37·(r·V₁₅ + coeff_Y)`, so `castHom(r·V₁₅ + coeff_Y) = 0`, i.e.
`r·(9·c₁₅) + 0 = 0`; as `9r` is a unit mod `37`, `c₁₅ = 0`.

The single-column coefficient value `Prop812SecondOrderCoeff37` is the one undischarged ingredient
— the genuine `p`-adic-`L` content of Proposition 8.12, the **second-order analog of the proven
first-order** `concreteKummerLogMatrix = diag(B mod 37)·V`.  It is strictly smaller than
`Prop812DescentCoeff37` (single cyclotomic column, no descent unit, no `D` existential), sound, and
non-circular (its conclusion is the explicit `B₃₂ mod 37²`-factored coefficient value, with `c₁₅`
entering only via the *separately proven* `9·c₁₅` inversion — not `c₁₅ = 0`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField
open scoped NumberField BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter
open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 0. The `castHom` compatibility `castHom ∘ toZModSq = toZMod`

The mod-`37` reduction of the mod-`37²` residue map on the rational completed integer ring is the
mod-`37` residue map:
`ZMod.castHom (p ∣ p²) ∘ rationalPadicIntegerToZModSq = rationalPadicIntegerToZMod`.
Both are transported from mathlib's `PadicInt` residue maps through the same `ℤ_[p] ≃ R₀` equiv, and
the tower `ZMod.castHom (p ∣ p²) ∘ toZModPow 2 = toZModPow 1` (`zmod_cast_comp_toZModPow`) together
with `toZMod = toZModPow 1` gives it. -/

/-- At the `PadicInt` level: `castHom (p ∣ p²) ∘ toZModPow 2 = toZMod` as ring homs `ℤ_[p] → ZMod p`
(both have kernel `span {(p : ℤ_[p])}`, the maximal ideal): `ker toZMod = maximalIdeal = span {p}`,
and `castHom (1 ≤ 2) ∘ toZModPow 2 = toZModPow 1` has kernel `span {(p:ℤ_[p])^1} = span {p}`. -/
theorem padicInt_castHom_comp_toZModPow_two (h : (p : ℕ) ∣ p ^ 2) :
    (ZMod.castHom h (ZMod p)).comp (PadicInt.toZModPow (p := lambdaPadicPrime p) 2) =
      PadicInt.toZMod (p := lambdaPadicPrime p) := by
  haveI : Fact (Nat.Prime (lambdaPadicPrime p : ℕ)) := ⟨(lambdaPadicPrime p).2⟩
  refine ZMod.ringHom_eq_of_ker_eq _ _ ?_
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  -- `ker (castHom ∘ toZModPow 2) = span {(p : ℤ_[p])}`, by double inclusion (local ring).
  apply le_antisymm
  · -- `ker ⊆ span {p}`: contrapositive — a non-`p`-multiple `z` is a unit, so
    -- `castHom (toZModPow z)` is a unit, hence `≠ 0`.
    intro z hz
    rw [RingHom.mem_ker, RingHom.comp_apply] at hz
    by_contra hzns
    -- `z ∉ span {p} = maximalIdeal`, so `z` is a unit in the local ring `ℤ_[p]`.
    rw [← PadicInt.maximalIdeal_eq_span_p] at hzns
    have hunit : IsUnit z := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hzns
      exact hzns
    have : IsUnit ((ZMod.castHom h (ZMod p)) (PadicInt.toZModPow (p := lambdaPadicPrime p) 2 z)) :=
      (hunit.map (PadicInt.toZModPow (p := lambdaPadicPrime p) 2)).map (ZMod.castHom h (ZMod p))
    rw [hz] at this
    exact not_isUnit_zero this
  · -- `span {p} ⊆ ker`: `castHom (toZModPow (p·w)) = (p : ZMod p)·... = 0`.
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      RingHom.comp_apply]
    rw [map_natCast, map_natCast]
    rw [show ((lambdaPadicPrime p : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) from rfl, ZMod.natCast_self]

/-- `castHom (p ∣ p²) ∘ rationalPadicIntegerToZModSq = rationalPadicIntegerToZMod` (per element).
Transport `padicInt_castHom_comp_toZModPow_two` through the `ℤ_[p] ≃ RationalPadicIntegerRing p`
equiv: both residue maps are the corresponding `PadicInt` map applied to `e.symm x`. -/
theorem rationalPadicIntegerToZMod_eq_castHom_toZModSq
    (h : (p : ℕ) ∣ p ^ 2) (x : RationalPadicIntegerRing p) :
    rationalPadicIntegerToZMod p x =
      (ZMod.castHom h (ZMod p)) (rationalPadicIntegerToZModSq p x) := by
  have hfun := RingHom.congr_fun (padicInt_castHom_comp_toZModPow_two p h)
    ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x)
  simp only [RingHom.comp_apply] at hfun
  -- `rationalPadicIntegerToZMod p x = toZMod (e.symm x)`,
  -- `rationalPadicIntegerToZModSq p x = toZModPow 2 (e.symm x)`.
  change PadicInt.toZMod (p := lambdaPadicPrime p)
      ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x) =
    (ZMod.castHom h (ZMod p)) (PadicInt.toZModPow (p := lambdaPadicPrime p) 2
      ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm x))
  rw [← hfun]

omit [NumberField.IsCMField K] in
/-- **The mod-`37` reduction of the second-order `varpi^i` coefficient is the first-order
coefficient** (proven).  Both `valuedLambdaQuotientDworkCoeffModSq i (evalₐ (λ) (2(p-1)) x)` and
`valuedLambdaQuotientDworkCoeffModP i (evalₐ (λ) (p-1) x)` read the *same* Dwork coordinate
`repr x i` (the proven `_evalₐ` lemmas), differing only by the residue map `toZModSq` vs `toZMod`;
the `castHom` compatibility `castHom_comp_rationalPadicIntegerToZModSq` then identifies them. -/
theorem valuedLambdaQuotientDworkCoeffModP_eq_castHom_modSq
    (h : (p : ℕ) ∣ p ^ 2) (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1) x) =
      (ZMod.castHom h (ZMod p))
        (valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
          (AdicCompletion.evalₐ (lambdaIdeal p K) (2 * (p - 1)) x)) := by
  rw [valuedLambdaQuotientDworkCoeffModP_evalₐ, valuedLambdaQuotientDworkCoeffModSq_evalₐ]
  exact rationalPadicIntegerToZMod_eq_castHom_toZModSq p h
    ((dworkParameterPowerBasis p K).repr x i)

end CyclotomicUnits
end BernoulliRegular

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The first-order `varpi^{32}` (row `15`) coefficient of any real unit's log vanishes

For **any** real unit `w : (𝓞 K⁺)ˣ`, the first-order (mod-`37`) `varpi^{32}` Dwork coordinate of
`completedLog(w^{36})` at `λ`-level `36` is `0` — the first-order row `j = 15` of the Kummer-log
matrix is `kummerLogDetRowFactor 15 · (V·ē)_15 = 0·… = 0` (the irregularity `37 ∣ B₃₂`).  This is
the first-order degeneracy that the `37`-th-power saturation correction inherits, and it is what
makes the saturation correction `37 · coeff_Y` reduce to `0` mod `37`. -/

set_option maxHeartbeats 1600000 in
-- The completed-log-column sum lives in the heavy `DworkCompleteIntegerRing`; unifying the
-- `evalₐ`-of-coerced-sum with the column sum exceeds the default heartbeat budget (as in the
-- first-order analog `caseIIEx811Core_mulVec_eq_zero_of_evalₐ_eq_zero`).
theorem caseIIDescentReduction_firstOrder_coeff15_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) :
    valuedLambdaQuotientDworkCoeffModP (p := 37) (K := CyclotomicField 37 ℚ)
        (⟨32, by norm_num⟩ : Fin (37 - 1))
        (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1)
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) w))) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  classical
  -- p-saturate `w = v_C · (37th power)`.
  obtain ⟨v, hvCPlus, hdiv⟩ :=
    caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup w
  obtain ⟨s, e, hse⟩ :=
    exists_CPlusExponentProduct_of_mem_CPlus (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) hvCPlus
  -- The level-`36` log coordinate of `w` equals that of the cyclotomic-column sum.
  set S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ) :=
    ∑ a : Fin (kummerLogRank 37),
      e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a
    with hS
  have hScoe :
      (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        ∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a := by
    rw [hS]
    rw [show (↑(∑ a : Fin (kummerLogRank 37),
          e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a) :
          DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        (Subalgebra.val (dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ)))
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
        from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_zsmul]
    rfl
  -- `evalₐ 36 (completedLog(w^36)) = evalₐ 36 (∑ e_a column_a)` (the `37`-th-power correction
  -- vanishes through level `36`, via `caseIIEx811Bridge_completedLog_evalₐ_eq_of_div_mem_…`).
  have hlogeq :
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1)
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) w)) =
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1)
          (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) := by
    rw [hScoe]
    -- `completedLog(v_C^36) = ∑ e_a column_a` (`§2`), and `w`, `v_C` differ by a `37`-th power.
    have hvlog :
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1)
            (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
              (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v)) =
          AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1)
            (∑ a : Fin (kummerLogRank 37),
              e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
                (by decide) a) := by
      have hsum := completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
        (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) s e
      rw [hse] at hsum
      rw [hsum]
    rw [← hvlog]
    exact caseIIEx811Bridge_completedLog_evalₐ_eq_of_div_mem_pPowerSubgroup hdiv (by norm_num)
  rw [hlogeq]
  -- The coordinate is the matrix row `15`, which is `rowFactor 15 · (V·ē)_15 = 0`.
  rw [show (⟨32, by norm_num⟩ : Fin (37 - 1)) =
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1 from rfl]
  rw [← caseIIEx811Core_coeffModP_eq_evalₐ S (15 : Fin (kummerLogRank 37))]
  rw [hS]
  rw [← concreteKummerLogMatrix_mulVec_exponents_eq_coeff (p := 37) (K := CyclotomicField 37 ℚ)
    (by norm_num) (by norm_num) e (15 : Fin (kummerLogRank 37))]
  -- `mulVec ē 15 = rowFactor 15 · (V·ē)_15 = 0`.
  rw [concreteKummerLogMatrix_mulVec_apply (K := CyclotomicField 37 ℚ)
    (fun a => (e a : ZMod 37)) (15 : Fin (kummerLogRank 37))]
  rw [caseIICor823_rowFactor_fifteen_eq_zero, zero_mul]

/-! ## 2. The descent detector splits as `D_vC + 37 · coeff_Y` under `p`-saturation

For `u = w^{37} · v` (`v ∈ C⁺`), the second-order detector `caseIICor823DescentDetectorSq u`
splits as the `varpi^{32}` mod-`37²` coordinate of the cyclotomic-column sum
`completedLog(v^{36})` plus `37` times the `varpi^{32}` mod-`37²` coordinate of
`Y = completedLog(w^{36})` (the `37`-th-power correction's log being `37 • Y`). -/

/-- The mod-`37²` `varpi^{32}` Dwork coordinate of a completed Dwork log element, at level `72`.
A named functional so the descent detector `caseIICor823DescentDetectorSq` is *definitionally*
`caseIICor823DetSqLog (completedLog(u^{36}))`, letting the additive split be proved on it
(additive + `37`-scaling) rather than through the heavy `whnf` of the detector definition. -/
def caseIICor823DetSqLog
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (X : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) : ZMod (37 ^ 2) :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
    (⟨32, by norm_num⟩ : Fin (37 - 1))
    (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1)) X)

set_option maxHeartbeats 800000 in
-- `map_add` on the `evalₐ` `AlgHom` over the heavy `adicCompletionIntegers` types makes the
-- `AddHomClass` instance synthesis (and the elaboration) expensive; raise both budgets.
set_option synthInstance.maxHeartbeats 800000 in
theorem caseIICor823DetSqLog_add
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (X Y : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) :
    caseIICor823DetSqLog (X + Y) = caseIICor823DetSqLog X + caseIICor823DetSqLog Y := by
  unfold caseIICor823DetSqLog
  rw [map_add, valuedLambdaQuotientDworkCoeffModSq_add]

set_option maxHeartbeats 800000 in
-- As above, the `map_mul` / `map_natCast` on the `evalₐ` `AlgHom` need raised elaboration and
-- instance-synthesis budgets over the heavy `adicCompletionIntegers` types.
set_option synthInstance.maxHeartbeats 800000 in
theorem caseIICor823DetSqLog_nsmul_thirtyseven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (Y : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) :
    caseIICor823DetSqLog ((37 : ℕ) • Y) = (37 : ZMod (37 ^ 2)) * caseIICor823DetSqLog Y := by
  unfold caseIICor823DetSqLog
  -- Convert `nsmul` to a ring multiplication first, then push the `(37 : _)` natCast through
  -- `evalₐ` (a `RingHom`) and use the second-order coefficient's natCast-scaling law.
  rw [nsmul_eq_mul]
  rw [map_mul, map_natCast]
  rw [valuedLambdaQuotientDworkCoeffModSq_natCast_mul, Nat.cast_ofNat]

/-- `caseIICor823DescentDetectorSq u = caseIICor823DetSqLog (completedLog(u^{36}))` (definitional;
both unfold to `valuedLambdaQuotientDworkCoeffModSq ⟨32,_⟩ (evalₐ 72 (completedLog …))`). -/
theorem caseIICor823DescentDetectorSq_eq_detSqLog
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) :
    caseIICor823DescentDetectorSq u =
      caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
        (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) := by
  unfold caseIICor823DescentDetectorSq caseIICor823DetSqLog
  -- The two sides differ only in the (proof-irrelevant) `Fin` membership proof of `⟨32, _⟩`.
  congr 1

set_option maxHeartbeats 1600000 in
-- The heavy `DworkCompleteIntegerRing` `completedLog` additivity / power identities exceed the
-- default heartbeat budget.
theorem caseIICor823DescentDetectorSq_split
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u v w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hu : u = w ^ 37 * v) :
    caseIICor823DescentDetectorSq u =
      caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
          (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v)) +
        (37 : ZMod (37 ^ 2)) *
          caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) w)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [caseIICor823DescentDetectorSq_eq_detSqLog]
  -- `completedLog(PowPred u) = 37 • completedLog(PowPred w) + completedLog(PowPred v)`.
  have hlog :
      completedLog (p := 37) (K := CyclotomicField 37 ℚ)
          (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u) =
        (37 : ℕ) • completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) w) +
          completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v) := by
    rw [hu, EPlus_completedLogDomainPowPred_mul, completedLog_mul,
      EPlus_completedLogDomainPowPred_pow, completedLog_pow_p_eq_p_smul]
  rw [hlog, caseIICor823DetSqLog_add, caseIICor823DetSqLog_nsmul_thirtyseven]
  ring

set_option maxHeartbeats 1600000 in
-- The `ϖ ↔ λ` bridge over the heavy `adicCompletionIntegers` `evalₐ` exceeds the default budget.
/-- `caseIICor823DetSqLog (S : Dwork)` for a *fixed-subalgebra* element `S` is the even-power Dwork
coefficient `rationalPadicIntegerToZModSq (repr S (kummerLogEvenPowerIndex 15))` — the
`ϖ ↔ λ` filtration identity `caseIICor823SecondOrder_coeffModSq_eq_evalₐ` at `j = 15`, with the
heavy `evalₐ`-of-coercion kept opaque (`generalize`) to dodge the `whnf` wall. -/
theorem caseIICor823DetSqLog_coe_fixedSubalgebra_eq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ)) :
    caseIICor823DetSqLog (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
      rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr S
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37)))) := by
  -- Rewrite the RHS `rationalPadicIntegerToZModSq (repr …)` into the `evalₐ` form via the bridge;
  -- then both sides are `valuedLambdaQuotientDworkCoeffModSq (idx).1 (evalₐ 72 (S:Dwork))`.
  rw [caseIICor823SecondOrder_coeffModSq_eq_evalₐ S (15 : Fin (kummerLogRank 37))]
  unfold caseIICor823DetSqLog
  rw [show (⟨32, by norm_num⟩ : Fin (37 - 1)) =
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1 from rfl]

set_option maxHeartbeats 1600000 in
-- The `castHom`/level compatibility over the heavy `adicCompletionIntegers` `evalₐ` is slow.
/-- The mod-`37` reduction of `caseIICor823DetSqLog X` (the level-`72` `varpi^{32}` coordinate) is
the first-order level-`36` `varpi^{32}` coordinate `valuedLambdaQuotientDworkCoeffModP ⟨32,_⟩
(evalₐ 36 X)` — the `castHom`/level compatibility, isolated so the heavy step is in its own unit. -/
theorem castHom_caseIICor823DetSqLog
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (X : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) :
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) (caseIICor823DetSqLog X) =
      valuedLambdaQuotientDworkCoeffModP (p := 37) (K := CyclotomicField 37 ℚ)
        (⟨32, by norm_num⟩ : Fin (37 - 1))
        (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1) X) := by
  unfold caseIICor823DetSqLog
  rw [valuedLambdaQuotientDworkCoeffModP_eq_castHom_modSq (p := 37) (K := CyclotomicField 37 ℚ)
    (by norm_num) (⟨32, by norm_num⟩ : Fin (37 - 1)) X]

/-! ## 3. `Cor823Omega32SecondOrderCollapse37` from the single-column coefficient value -/

set_option maxHeartbeats 4000000 in
-- The p-saturation assembly threads several heavy `adicCompletionIntegers` `evalₐ`/`completedLog`
-- terms; the cumulative elaboration is well above the default budget (below the `whnf` wall).
/-- **`Cor823Omega32SecondOrderCollapse37` from the single-column second-order coefficient value
`Prop812SecondOrderCoeff37`** (proven, axiom-clean given that residual).

For `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u − c`, the `j = 15` free-part eigencomponent
`decomp (φ u) 15` vanishes.  Proof: `p`-saturate `u = w^{37}·v` (`v = CPlusExponentProduct s e`);
the detector splits as `D_vC + 37·coeff_Y` (`§2`); the proven detector vanishing makes it `0`; the
coefficient value `Prop812SecondOrderCoeff37` writes `D_vC = factor·V₁₅` (`factor = 37·r`), so
`37·(r·V₁₅ + coeff_Y) = 0`, whence `castHom(r·V₁₅ + coeff_Y) = 0`; `castHom coeff_Y = 0` (`§1`,
first-order vanishing + the `castHom`/level compatibility) and `castHom V₁₅ = (V·ē)_15 = 9·c₁₅`
(proven `caseIIEx811Eigen_vandermonde_eq_nine_smul`) give `9·r·c₁₅ = 0`, hence `c₁₅ = 0`; the proven
free-part-class bridge identifies that with `decomp (φ u) 15`. -/
theorem cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCoeff : Prop812SecondOrderCoeff37) :
    Cor823Omega32SecondOrderCollapse37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  classical
  intro u c hc
  -- (1) p-saturation: `u = w^37 · v`, `v ∈ C⁺`, `v = CPlusExponentProduct s e`.
  obtain ⟨v, hvCPlus, hdiv⟩ :=
    caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup u
  obtain ⟨w, _hwmem, hwpow⟩ := id hdiv
  -- `u * v⁻¹ = w^37`, so `u = w^37 * v`.
  have hu : u = w ^ 37 * v := by rw [hwpow]; group
  obtain ⟨s, e, hse⟩ :=
    exists_CPlusExponentProduct_of_mem_CPlus (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) hvCPlus
  -- (2) detector vanishing.
  have hdet0 : caseIICor823DescentDetectorSq u = 0 :=
    caseIICor823SecondOrder_detector_descent_eq_zero u c hc
  -- (3) the split: `detector(u) = D_vC + 37 · coeff_Y`.
  have hsplit := caseIICor823DescentDetectorSq_split u v w hu
  -- (4) `D_vC = coeffModSq 32 (evalₐ 72 (completedLog(v^36)))`, the column-sum even-power coeff.
  set DvC : ZMod (37 ^ 2) :=
    caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v))
    with hDvC
  set coeffY : ZMod (37 ^ 2) :=
    caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) w))
    with hcoeffY
  -- `completedLog(v^36) = (S : Dwork)`, the cyclotomic-column sum (`§2`).
  set S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ) :=
    ∑ a : Fin (kummerLogRank 37),
      e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a
    with hS
  have hScoe :
      (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        ∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a := by
    rw [hS]
    rw [show (↑(∑ a : Fin (kummerLogRank 37),
          e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a) :
          DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        (Subalgebra.val (dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ)))
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
        from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_zsmul]
    rfl
  have hcompletedLog_eq :
      completedLog (p := 37) (K := CyclotomicField 37 ℚ)
          (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v) =
        (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) := by
    have hsum := completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) s e
    rw [hse] at hsum
    rw [hScoe]; exact hsum
  -- (5) `D_vC = factor · V₁₅` (`DetSqLog`-on-`(S:Dwork)` + `Prop812SecondOrderCoeff37`).
  have hDvC_factor :
      DvC = caseIICor823SecondOrderBernoulliFactorModSq *
        (∑ a : Fin (kummerLogRank 37),
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
            ((e a : ℤ) : ZMod (37 ^ 2))) := by
    rw [hDvC, hcompletedLog_eq, caseIICor823DetSqLog_coe_fixedSubalgebra_eq, hS]
    exact hCoeff e
  -- (6) `factor = 37·r`, `r` a unit mod 37.
  obtain ⟨r, hrfac, hr_ne⟩ := caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul
  -- (7) `0 = detector(u) = D_vC + 37·coeffY = 37·(r·V₁₅ + coeffY)`.
  rw [hdet0] at hsplit
  rw [hDvC_factor, hrfac] at hsplit
  -- `0 = 37·r·V₁₅ + 37·coeffY`.
  set V₁₅ : ZMod (37 ^ 2) :=
    ∑ a : Fin (kummerLogRank 37),
      (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
        ((e a : ℤ) : ZMod (37 ^ 2))
    with hV₁₅
  have h37 : (37 : ZMod (37 ^ 2)) * (r * V₁₅ + coeffY) = 0 := by
    linear_combination -hsplit
  -- (8) `castHom(r·V₁₅ + coeffY) = 0` (the `37·x = 0 ⟹ castHom x = 0` precision step).
  have hkey : ∀ x : ZMod (37 ^ 2), (37 : ZMod (37 ^ 2)) * x = 0 →
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) x = 0 := by
    intro x hx
    have hval : (37 ^ 2 : ℕ) ∣ 37 * x.val := by
      have h0 : ((37 * x.val : ℕ) : ZMod (37 ^ 2)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id, Nat.cast_ofNat]
        exact hx
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hdvd : (37 : ℕ) ∣ x.val := by
      obtain ⟨t, ht⟩ := hval
      refine ⟨t, ?_⟩
      have h37' : (37 : ℕ) * x.val = 37 * (37 * t) := by rw [ht]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h37'
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hcast0 : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) (r * V₁₅ + coeffY) = 0 :=
    hkey _ h37
  -- (9) `castHom coeffY = 0` (first-order vanishing + level compatibility).
  have hcoeffY0 : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) coeffY = 0 := by
    rw [hcoeffY, castHom_caseIICor823DetSqLog]
    -- `convert … using 2` peels the application so the differing (proof-irrelevant) `Fin` index
    -- proof never forces a full `isDefEq` of the heavy `evalₐ` argument.
    convert caseIIDescentReduction_firstOrder_coeff15_eq_zero w using 2
  -- (10) `r_mod · castHom V₁₅ = 0`, with `castHom V₁₅ = (V·ē)_15 = 9·c₁₅`.
  rw [map_add, map_mul, hcoeffY0, add_zero] at hcast0
  -- `castHom V₁₅ = (V·ē)_15`: both expand to `∑_a (((a+2)²)^16 - 1)·(e a)` over `ZMod 37`.
  have h15val : ((15 : Fin (kummerLogRank 37)) : ℕ) = 15 := rfl
  have hmulVec_eq :
      (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
          (fun a : Fin (kummerLogRank 37) => (e a : ZMod 37)) (15 : Fin (kummerLogRank 37)) =
        ∑ a : Fin (kummerLogRank 37),
          (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((15 : ℕ) + 1) - 1) * ((e a : ℤ) : ZMod 37) := by
    rw [Matrix.mulVec]
    simp only [dotProduct, vandermondeTeichmullerEvenSubOneMatrix, teichmullerEvenNode,
      kummerLogColumnIndex, BernoulliRegular.CPlusGeneratorIndex, h15val]
  have hV₁₅cast : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) V₁₅ =
      (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
        (fun a : Fin (kummerLogRank 37) => (e a : ZMod 37)) (15 : Fin (kummerLogRank 37)) := by
    rw [hmulVec_eq, hV₁₅, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, map_sub, map_one, map_pow, map_pow, map_natCast, map_intCast]
  rw [hV₁₅cast] at hcast0
  -- (11) `(V·ē)_15 = 9 · decomp (∑ e_a g_a) 15`, `9 ≠ 0`.
  have hcollapse := caseIIEx811Eigen_vandermonde_eq_nine_smul e (15 : Fin (kummerLogRank 37))
  rw [hcollapse] at hcast0
  -- `r_mod · (9 · c₁₅) = 0`, `r_mod ≠ 0`, `9 ≠ 0` ⟹ `c₁₅ = 0`.
  have h9 : (9 : ZMod 37) ≠ 0 := by
    rw [show (9 : ZMod 37) = ((9 : ℕ) : ZMod 37) from by push_cast; ring,
      show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
      ZMod.natCast_eq_natCast_iff]
    decide
  have hc15 : caseIIResidueProvenance_decomp
      (∑ a : Fin (kummerLogRank 37),
        e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
          (Additive.ofMul
            (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)))
      ⟨(15 : Fin (kummerLogRank 37)).1, by
        have := (15 : Fin (kummerLogRank 37)).isLt
        simp only [kummerLogRank] at this; omega⟩ = 0 := by
    have hprod : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) r *
        ((9 : ZMod 37) * caseIIResidueProvenance_decomp
          (∑ a : Fin (kummerLogRank 37),
            e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
              (Additive.ofMul
                (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)))
          ⟨(15 : Fin (kummerLogRank 37)).1, by
            have := (15 : Fin (kummerLogRank 37)).isLt
            simp only [kummerLogRank] at this; omega⟩) = 0 := hcast0
    have h2 := (mul_eq_zero.mp hprod).resolve_left hr_ne
    exact (mul_eq_zero.mp h2).resolve_left h9
  -- (12) free-part-class bridge: `∑ e_a g_a = realUnitToFreePartModP u`, and index `⟨15.1,_⟩ = 15`.
  have hcls := caseIIEx811Bridge_freePartClass_eq hse hdiv
  rw [hcls] at hc15
  -- `decomp (φ u) ⟨15.1, _⟩ = decomp (φ u) 15` (same Nat value).
  exact hc15

/-! ## 4. `Prop812DescentCoeff37` from the collapse, and from the single-column coefficient value

`Prop812DescentCoeff37` asks for `D` with `detector(u) = factor·D` and `castHom D = c₁₅`.  The
proven detector vanishing makes `detector(u) = 0`; once `c₁₅ = 0` (the collapse), `D = 0` works
(`factor·0 = 0`, `castHom 0 = 0 = c₁₅`).  So `Prop812DescentCoeff37` follows from
`Cor823Omega32SecondOrderCollapse37`, hence from `Prop812SecondOrderCoeff37`. -/

/-- **`Prop812DescentCoeff37` from the `i = 32` collapse** (proven, axiom-clean given
`Cor823Omega32SecondOrderCollapse37`).  With `c₁₅ = decomp (φ u) 15 = 0` (the collapse) and the
proven detector vanishing `detector(u) = 0`, the witness `D = 0` discharges the residual:
`detector(u) = 0 = factor·0` and `castHom 0 = 0 = c₁₅`. -/
theorem prop812DescentCoeff37_of_omega32Collapse
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCollapse : Cor823Omega32SecondOrderCollapse37) :
    Prop812DescentCoeff37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro u c hc
  refine ⟨0, ?_, ?_⟩
  · -- `detector(u) = 0 = factor·0`.
    rw [mul_zero]
    exact caseIICor823SecondOrder_detector_descent_eq_zero u c hc
  · -- `castHom 0 = 0 = c₁₅`, using the collapse `c₁₅ = 0`.
    rw [map_zero]
    exact (hCollapse u c hc).symm

/-- **`Prop812DescentCoeff37` from the single-column second-order coefficient value** (proven,
axiom-clean given `Prop812SecondOrderCoeff37`).  Composes
`prop812DescentCoeff37_of_omega32Collapse` with
`cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff`. -/
theorem prop812DescentCoeff37_of_secondOrderCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCoeff : Prop812SecondOrderCoeff37) :
    Prop812DescentCoeff37 :=
  prop812DescentCoeff37_of_omega32Collapse
    (cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff hCoeff)

/-! ## 5. The FLT37 endpoint with `R4` reduced to the single-column second-order coefficient -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the single-column second-order
coefficient value `Prop812SecondOrderCoeff37`** (proven, axiom-clean given the genuine residuals +
the carried Kellner Prop).

Supplies the descent residual `Prop812DescentCoeff37` to
`fermatLastTheoremFor_thirtyseven_of_prop812Descent` via
`prop812DescentCoeff37_of_secondOrderCoeff` from the strictly-smaller single-cyclotomic-column
coefficient value `Prop812SecondOrderCoeff37` — Washington Proposition 8.12 at `i = 32` reduced to
the genuine level-`68` mod-`37²` Dwork coefficient of the `i = 32` cyclotomic column equalling
`B₃₂/32 mod 37²`.  All the Theorem-8.22 plumbing, the second-order detector machinery, the
**proven** detector vanishing, the first-order row-`15` vanishing, and the `9·c₁₅` inversion
are proven; only the single-column coefficient value remains. -/
theorem fermatLastTheoremFor_thirtyseven_of_prop812SecondOrderCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_secondOrderCoeff : Prop812SecondOrderCoeff37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_prop812Descent
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (prop812DescentCoeff37_of_secondOrderCoeff caseII_secondOrderCoeff)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
