import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.CompletedLogValuationHalf
import BernoulliRegular.UnitQuotient.Washington814ForwardD

/-!
# Washington Exercise 8.11 / Corollary 8.15 for `p = 37`: the Galois-equivariant
leading-`λ`-exponent bridge `LeadingExponentBridge37` — the comparison, and the precise residual

This file builds the **Galois-equivariant comparison** between the local λ-graded completed
logarithm `completedLog(u^{36})` and the global mod-`37` free-part eigencomponents
`caseIIResidueProvenance_decomp (realUnitToFreePartModP u)`, the bridge of Washington
Exercise 8.11 / Corollary 8.15 that — together with the proven valuation half
(`completedLogVanishingThroughLevel36_37_proven`, `CaseIILeadingExponentCollapse.lean`) — discharges
`LeadingExponentEigenCollapse37`, hence (via `leadingExponentEigenCollapse37_of_bridge'`) the named
leaf `LeadingExponentEigenCollapse37`.

It imports only; it does **not** modify any existing file.

## The comparison this file proves (real, axiom-clean Lean)

The descent leaf is phrased for an **arbitrary** real unit `u : (𝓞 K⁺)ˣ`
(`DescentUnitOmega32Membership37`
takes no `w ∈ C⁺` hypothesis).  The comparison proceeds in two genuinely-provable structural steps,
plus the one genuinely-unbuilt analytic core (isolated as a single named `def … : Prop`, **not** an
axiom).

* **(P1) The `37`-th-power correction vanishes through `λ`-level `36`** (`§1`, fully **proven**):
  the completed logarithm `completedLog(EPlus_completedLogDomainPowPred w)` of a real unit `w` that
  is
  a `37`-th power in `E⁺` (`w ∈ pPowerSubgroup (EPlus) 37`) is `37 • (something)`
  (`completedLog_EPlus_completedLogDomainPowPred_mem_pPowerSubgroup`), and since `(37) = λ^{36}` in
  the
  λ-valued ring (`span_natCast_prime_eq_lambdaIdeal_pow_pred`), every graded coordinate
  `AdicCompletion.evalₐ (λ) N (37 • X)` with `N ≤ 36` is `0`.  This is what makes the local log
  insensitive to `37`-th-power factors **below `λ`-level `36`** — the structural input that lets the
  arbitrary-unit leaf be compared to a cyclotomic-unit expansion.

  Consequently (`caseIIEx811Bridge_completedLog_eq_of_div_mem_pPowerSubgroup`) two real units `u`,
  `v`
  that differ by a `37`-th power (`u * v⁻¹ ∈ pPowerSubgroup (EPlus) 37`) have **equal**
  completed-log
  graded coordinates through `λ`-level `36`; and their `realUnitToFreePartModP` classes coincide
  (`caseIIEx811Bridge_realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup`, since the free-part
  class
  is a `ZMod 37`-module map killing `37`-th powers).

* **(P2) The cyclotomic-unit local log is the `kummerLogCompletedColumn` combination** (`§2`,
  fully **proven** re-packaging): for a `C⁺` exponent product
  `v = CPlusExponentProduct s e`, the completed logarithm
  `completedLog(EPlus_completedLogDomainPowPred v) = ∑_a e_a • kummerLogCompletedColumn a`
  (`completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum`), and its mod-`37` free-part class is
  `∑_a e_a • φ(CPlusGenerator a)` (`realUnitToFreePartModP_CPlusExponentProduct`).

* **(R) The genuinely-unbuilt analytic core** (`§3`, the single named residual
  `LeadingExponentEx811Core37`,
  a `def … : Prop`, **not** an axiom): the Galois-equivariant leading-`λ`-coefficient computation of
  Exercise 8.11 itself — *for a `C⁺` exponent vector `e` whose local logarithm
  `∑_a e_a • kummerLogCompletedColumn a` vanishes through `λ`-level `36`, the **regular**
  eigencomponents
  of `∑_a e_a • φ(CPlusGenerator a)` vanish* — **together with** the `37 ∤ h⁺` `p`-saturation
  surjectivity
  that presents an arbitrary real unit's class and log (through `λ`-level `36`) by a `C⁺` exponent
  vector.
  This is precisely the content that the companion `concreteKummerLogMatrix = diag(B)·V` machinery
  does
  **not** supply: that machinery is in the *Dwork `varpi`-power basis*, in which
  `kummerLogCompletedColumn a`
  has full support across all even rows (weighted by Bernoulli factors and a Vandermonde), so the
  Dwork-basis matrix kernel only forces the regular eigencomponents to be **equal**, not zero.  The
  Exercise-8.11 statement is the *λ-adic leading-exponent* fact — `E_a^{36}` has λ-adic leading
  non-constant exponent exactly `2·index_a` with leading coefficient a unit times `B_{2·index_a}` —
  in
  which distinct regular indices sit at distinct λ-levels, so the level-`2·index_a` coordinate
  isolates a
  single eigencomponent.

`leadingExponentBridge37_of_ex811Core` discharges `LeadingExponentBridge37` from the single residual
`LeadingExponentEx811Core37`, and `leadingExponentEigenCollapse37_of_ex811Core` chains it with the
proven valuation half to `LeadingExponentEigenCollapse37`.

## Soundness

`LeadingExponentEx811Core37` is **sound** and **non-circular**:

* it is phrased on the **local logarithm** `∑_a e_a • kummerLogCompletedColumn a` (a finer λ-adic
  object
  than the free-part class), not on the free-part class alone — so it is not the
  eigencomponent-detector
  functional that would be circular (the free-part eigenspaces are rank one, so any functional
  diagonal on
  the eigenbasis is the dual coordinate itself);
* its hypothesis is genuinely a λ-adic local-log property of the *specific* exponent vector `e`,
  never an
  `E₃₂`-monomial property of an arbitrary class;
* it is **non-vacuous**: `e = 0` satisfies the hypothesis (the zero log vanishes through every
  level) and
  the conclusion (all eigencomponents of the zero class are zero) — see
  `leadingExponentEx811Core37_antecedent_inhabited`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2 Lemma 9.9 (pp. 180–181),
  Exercises 8.10/8.11 (p. 166), Corollary 8.15 (p. 153), Theorem 8.16 (p. 157).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The `37`-th-power correction vanishes through `λ`-level `36`

`(37) = λ^{36}` in the λ-valued integer ring, so `37 • X` lies in `λ^{36} ⊆ λ^N` for every `N ≤ 36`;
hence every graded coordinate `AdicCompletion.evalₐ (λ) N (37 • X)` (`N ≤ 36`) is `0`.  Applied to
the
completed logarithm of a `37`-th power (which the proven
`completedLog_EPlus_completedLogDomainPowPred_mem_pPowerSubgroup` writes as `37 • (something)`),
this
makes the local log insensitive, below `λ`-level `36`, to `37`-th-power factors of the unit. -/

/-- **A `37`-multiple has vanishing `λ`-graded coordinate through level `36`** (proven): for any
`X : DworkCompleteIntegerRing 37 K` and any `N ≤ 36`, the level-`N` coordinate of `37 • X` is `0`.
Reason: the coordinate `AdicCompletion.evalₐ (λ) N (37 • X) = 37 • (evalₐ N X)` lives in
`ValuedIntegerRing/λ^N`, where `(37 : ValuedIntegerRing) ∈ λ^{36} ⊆ λ^N` (`(37) = λ^{36}`), so the
scalar `37` is `0`. -/
theorem caseIIEx811Bridge_evalₐ_nsmul_thirtyseven_eq_zero
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K]
    {N : ℕ} (hN : N ≤ 36) (X : DworkCompleteIntegerRing 37 K) :
    AdicCompletion.evalₐ (lambdaIdeal 37 K) N ((37 : ℕ) • X) = 0 := by
  rw [map_nsmul]
  -- The scalar `37` is `0` in `ValuedIntegerRing/λ^N` because `37 = p ∈ λ^{36} ⊆ λ^N`.
  have h37mem : ((37 : ℕ) : ValuedIntegerRing 37 K) ∈ (lambdaIdeal 37 K) ^ N := by
    have h36 : ((37 : ℕ) : ValuedIntegerRing 37 K) ∈ (lambdaIdeal 37 K) ^ 36 := by
      have hspan := span_natCast_prime_eq_lambdaIdeal_pow_pred (p := 37) (K := K)
      have hmem : ((37 : ℕ) : ValuedIntegerRing 37 K) ∈
          Ideal.span ({((37 : ℕ) : ValuedIntegerRing 37 K)} :
            Set (ValuedIntegerRing 37 K)) :=
        Ideal.mem_span_singleton_self _
      rw [hspan] at hmem
      rwa [show (37 - 1 : ℕ) = 36 from rfl] at hmem
    exact Ideal.pow_le_pow_right hN h36
  -- Hence `(37 : ValuedIntegerRing/λ^N) = 0`, so `37 • (evalₐ N X) = 0`.
  have hzero : ((37 : ℕ) : ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K) ^ N) = 0 := by
    rw [show ((37 : ℕ) : ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K) ^ N) =
        Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ N) ((37 : ℕ) : ValuedIntegerRing 37 K) by
      rw [map_natCast]]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact h37mem
  rw [show ((37 : ℕ) • AdicCompletion.evalₐ (lambdaIdeal 37 K) N X) =
      ((37 : ℕ) : ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K) ^ N) •
        AdicCompletion.evalₐ (lambdaIdeal 37 K) N X by
    rw [Nat.cast_smul_eq_nsmul]]
  rw [hzero, zero_smul]

/-- **The completed log of a `37`-th power vanishes through `λ`-level `36`** (proven): if a real
unit
`w` is a `37`-th power in `E⁺` (`w ∈ pPowerSubgroup (EPlus) 37`), then every graded coordinate
`AdicCompletion.evalₐ (λ) N (completedLog (EPlus_completedLogDomainPowPred w))` with `N ≤ 36` is
`0`.

Proof: `completedLog (EPlus_completedLogDomainPowPred w) = 37 • Y` for some `Y`
(`completedLog_EPlus_completedLogDomainPowPred_mem_pPowerSubgroup`), and a `37`-multiple has
vanishing
graded coordinate through level `36` (`caseIIEx811Bridge_evalₐ_nsmul_thirtyseven_eq_zero`). -/
theorem caseIIEx811Bridge_completedLog_evalₐ_eq_zero_of_mem_pPowerSubgroup
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K]
    {w : (𝓞 (NumberField.maximalRealSubfield K))ˣ}
    (hw : w ∈ pPowerSubgroup (EPlus (K := K)) 37)
    {N : ℕ} (hN : N ≤ 36) :
    AdicCompletion.evalₐ (lambdaIdeal 37 K) N
        (completedLog (p := 37) (K := K)
          (EPlus_completedLogDomainPowPred (p := 37) (K := K) w)) = 0 := by
  obtain ⟨Y, hY⟩ :=
    completedLog_EPlus_completedLogDomainPowPred_mem_pPowerSubgroup
      (p := 37) (K := K) hw
  rw [← hY]
  exact caseIIEx811Bridge_evalₐ_nsmul_thirtyseven_eq_zero hN Y

/-- **Two real units differing by a `37`-th power have equal completed-log graded coordinates
through
`λ`-level `36`** (proven).  If `u * v⁻¹ ∈ pPowerSubgroup (EPlus) 37` then for every `N ≤ 36`,

  `evalₐ (λ) N (completedLog (EPlus_completedLogDomainPowPred u)) =
     evalₐ (λ) N (completedLog (EPlus_completedLogDomainPowPred v))`.

Proof: `EPlus_completedLogDomainPowPred` is multiplicative and `completedLog` additive, so the
difference is the completed log of `u * v⁻¹` (a `37`-th power), which vanishes through level `36`
by `caseIIEx811Bridge_completedLog_evalₐ_eq_zero_of_mem_pPowerSubgroup`. -/
theorem caseIIEx811Bridge_completedLog_evalₐ_eq_of_div_mem_pPowerSubgroup
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K]
    {u v : (𝓞 (NumberField.maximalRealSubfield K))ˣ}
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := K)) 37)
    {N : ℕ} (hN : N ≤ 36) :
    AdicCompletion.evalₐ (lambdaIdeal 37 K) N
        (completedLog (p := 37) (K := K)
          (EPlus_completedLogDomainPowPred (p := 37) (K := K) u)) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) N
        (completedLog (p := 37) (K := K)
          (EPlus_completedLogDomainPowPred (p := 37) (K := K) v)) := by
  -- `u = (u * v⁻¹) * v`, so the powered-log domain element factors multiplicatively.
  have huv : u = (u * v⁻¹) * v := by group
  rw [huv, EPlus_completedLogDomainPowPred_mul, completedLog_mul, map_add]
  -- The `u * v⁻¹` summand vanishes through level `36`.
  rw [caseIIEx811Bridge_completedLog_evalₐ_eq_zero_of_mem_pPowerSubgroup hdiv hN, zero_add]

/-- **Two real units differing by a `37`-th power have equal mod-`37` free-part class** (proven).
`realUnitToFreePartModP` is a `ZMod 37`-module map killing `37`-th powers, so if
`u * v⁻¹ ∈ pPowerSubgroup (EPlus) 37` then `realUnitToFreePartModP u = realUnitToFreePartModP v`. -/
theorem caseIIEx811Bridge_realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {u v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ}
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37) :
    FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) =
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul v) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨w, _hwE, hwpow⟩ := hdiv
  -- `u = w^37 * v`; the `w^37` factor maps to `37 • φ(w) = 0`.
  have huv : u = w ^ 37 * v := by
    rw [hwpow]; group
  rw [huv, ofMul_mul, map_add, ofMul_pow, map_nsmul]
  rw [show ((37 : ℕ) • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul w)) =
      ((37 : ℕ) : ZMod 37) •
        FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) by
    rw [Nat.cast_smul_eq_nsmul]]
  rw [ZMod.natCast_self, zero_smul, zero_add]

/-! ## 2′. The `37 ∤ h⁺` `p`-saturation surjectivity: an arbitrary real unit is a `C⁺` element times
a
`37`-th power

Since `[E⁺ : C⁺] = h⁺` is finite and coprime to `37` (`SinnottIndexFormula 37` + `37 ∤ h⁺`), the
`37`-th-power map on the finite group `E⁺/C⁺` is surjective (mathlib `powCoprime`).  Hence every
real
unit `u` is `≡` a `C⁺` element modulo `37`-th powers: there is `v ∈ C⁺` with
`u * v⁻¹ ∈ pPowerSubgroup (E⁺) 37`.  This is the surjectivity that lets the arbitrary-unit leaf be
reduced to a cyclotomic-unit exponent vector (then `§1` transfers the local log and the free-part
class). -/

/-- **`C⁺` has index coprime to `37`** (proven, via the proven Vandiver result `37 ∤ h⁺`).  The real
cyclotomic-unit subgroup `C⁺` of `(𝓞 K⁺)ˣ` has `¬ 37 ∣ [E⁺ : C⁺]` for `K = ℚ(ζ₃₇)`.

Reason: `[E⁺ : C⁺] = 2^{17}·h⁺` (Sinnott index formula `SinnottIndexFormula 37`, supplied for free
by
`caseIIGaloisEigen_sinnottIndexFormula_37`, packaged by
`index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula`
and `cyclotomicUnitIndexSubgroup_eq_CPlus`), and `37 ∤ 2^{17}·h⁺` because `37` is odd and `37 ∤ h⁺`
(the proven `Sinnott.flt37_not_dvd_hPlus`).  This is the irregular-prime analogue of
`not_dvd_index_of_pSaturated` (which is unavailable here because the Kummer matrix determinant
*vanishes*
for the irregular prime `37`). -/
theorem caseIIEx811Bridge_not_dvd_CPlus_index
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ (37 : ℕ) ∣
      (BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide)).index := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `[E⁺ : C⁺] = 2^{17}·h⁺`.
  have hindex :
      (BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide)).index =
        2 ^ ((37 - 3) / 2) * hPlus (CyclotomicField 37 ℚ) := by
    have h := FLT37.Sinnott.index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide)
      caseIIGaloisEigen_sinnottIndexFormula_37
    change (cyclotomicUnitIndexSubgroup (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) (by decide)).index = _ at h
    rwa [cyclotomicUnitIndexSubgroup_eq_CPlus
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide)] at h
  rw [hindex]
  -- `37 ∤ 2^{17}·h⁺`: `37` prime, `37 ∤ 2^{17}` and `37 ∤ h⁺`.
  intro hdvd
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 37)).mp hdvd with h2 | hhplus
  · exact absurd ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 37)) h2) (by decide)
  · exact FLT37.Sinnott.flt37_not_dvd_hPlus hhplus

/-- **Every real unit is a `C⁺` element times a `37`-th power** (proven, via `37 ∤ [E⁺ : C⁺]`).  For
any `u : (𝓞 K⁺)ˣ` there is `v ∈ C⁺` with `u * v⁻¹ ∈ pPowerSubgroup (E⁺) 37`.

Proof: the quotient `Q = (𝓞 K⁺)ˣ ⧸ C⁺` is finite (`C⁺` has finite index, `CPlus_index_ne_zero`) of
order coprime to `37` (`caseIIEx811Bridge_not_dvd_CPlus_index`), so the `37`-th-power map on `Q` is
a
bijection (mathlib `powCoprime`).  Hence the class of `u` is the `37`-th power of the class of some
`k`,
i.e. `u * (k^{37})⁻¹ ∈ C⁺`; take `v := u * (k^{37})⁻¹`, so `u * v⁻¹ = k^{37} ∈ pPowerSubgroup (⊤)
37`. -/
theorem caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) :
    ∃ v ∈ BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide),
      u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37 := by
  classical
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set H : Subgroup (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ :=
    BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide) with hH
  haveI : H.FiniteIndex := ⟨by
    rw [hH]; exact CPlus_index_ne_zero (p := 37) (K := CyclotomicField 37 ℚ) (by decide)⟩
  -- The quotient `Q = G/H` is finite of order coprime to `37`.
  haveI : Finite (_ ⧸ H) := H.finite_quotient_of_finiteIndex
  have hcard : (Nat.card (_ ⧸ H)).Coprime 37 := by
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr ?_
    rw [← Subgroup.index_eq_card, hH]
    exact caseIIEx811Bridge_not_dvd_CPlus_index
  -- The `37`-th-power map on `Q` is a bijection; pull back the class of `u`.
  set q : _ ⧸ H := QuotientGroup.mk u with hq
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective ((powCoprime hcard).symm q)
  -- `q = (mk k)^37`.
  have hqpow : q = (QuotientGroup.mk k : _ ⧸ H) ^ 37 := by
    have hrw : (powCoprime hcard) ((powCoprime hcard).symm q) = q :=
      (powCoprime hcard).apply_symm_apply q
    rw [← hk] at hrw
    -- `powCoprime hcard (mk k) = (mk k) ^ 37` definitionally.
    rw [← hrw]
    rfl
  refine ⟨u * (k ^ 37)⁻¹, ?_, ?_⟩
  · -- `u * (k^37)⁻¹ ∈ H` because its class is `1`.
    rw [hH, ← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
    rw [show (QuotientGroup.mk u : _ ⧸ H) = q from rfl, hqpow]
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [mul_inv_cancel, QuotientGroup.mk_one]
  · -- `u * (u * (k^37)⁻¹)⁻¹ = k^37 ∈ pPowerSubgroup (⊤) 37`.
    rw [show u * (u * (k ^ 37)⁻¹)⁻¹ = k ^ 37 by
      rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_right_comm, mul_inv_cancel, one_mul]]
    exact ⟨k, Subgroup.mem_top k, rfl⟩

/-! ## 3. The genuine Exercise-8.11 residual, and the bridge

After `§1`–`§2′`, the bridge for an arbitrary real unit reduces to a statement about the **`C⁺`
exponent vector** of a cyclotomic representative: its local logarithm
`∑_a e_a • kummerLogCompletedColumn a` is the genuine λ-adic object whose vanishing through λ-level
`36`
must force the regular eigencomponents of `∑_a e_a • φ(CPlusGenerator a)`.  This is the
**λ-adic leading-coefficient computation of Washington Exercise 8.11** — the single
genuinely-unbuilt
content (see the module docstring): it is the fact that `E_a^{36}` has λ-adic leading non-constant
exponent exactly `2·index_a` with leading coefficient a unit times `B_{2·index_a}`, so that distinct
regular indices contribute at distinct λ-levels and the level-`2·index_a` coordinate isolates a
single
eigencomponent — a statement *not* supplied by the Dwork-`varpi`-basis matrix
`concreteKummerLogMatrix = diag(B)·V` (whose kernel only forces the regular eigencomponents to be
*equal*). -/

open BernoulliRegular (CPlusGenerator) in
/-- **Washington Exercise 8.11, λ-adic leading-coefficient core, named** (a `def … : Prop`, **not**
an
axiom).

For every `C⁺` exponent vector `e : Fin (kummerLogRank 37) → ℤ` whose cyclotomic local logarithm
`∑_a e_a • kummerLogCompletedColumn a` vanishes through `λ`-level `36` (all
`AdicCompletion.evalₐ (λ) N` with `N ≤ 36` are `0`), the **regular** eigencomponents of the mod-`37`
free-part class `∑_a e_a • φ(CPlusGenerator a)` vanish: for every `j : Fin 18`, `j ≠ 15`,

  `caseIIResidueProvenance_decomp (∑_a e_a • realUnitToFreePartModP (CPlusGenerator a)) j = 0`.

This is the genuine λ-adic leading-`λ`-coefficient computation of Exercise 8.11.  It is **sound**
and
**non-circular**: it is phrased on the *local logarithm* (a finer λ-adic object than the free-part
class), it constrains the regular eigencomponents of the *specific* exponent vector's class (never
an
`E₃₂`-monomial property of an arbitrary class), and it is **non-vacuous** (`e = 0`, see
`leadingExponentEx811Core37_antecedent_inhabited`).  It is *not* implied by the global free-part
datum alone: the Dwork-`varpi`-basis matrix kernel only forces the regular eigencomponents to be
*equal*. -/
def LeadingExponentEx811Core37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ e : Fin (kummerLogRank 37) → ℤ,
    (∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a) = 0) →
    ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (∑ a : Fin (kummerLogRank 37),
          e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
            (Additive.ofMul
              (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) j =
        0

open BernoulliRegular (CPlusGenerator) in
/-- **`LeadingExponentEx811Core37` has an inhabited antecedent** (non-vacuity, proven): the zero
exponent vector `e = 0` satisfies the hypothesis — its cyclotomic local logarithm
`∑_a 0 • kummerLogCompletedColumn a = 0` vanishes through every `λ`-level.  Hence the universally
quantified implication `LeadingExponentEx811Core37` is **not vacuously true**: its hypothesis class
is
inhabited, so the residual carries genuine content (it is a real implication on the local log, not a
statement whose antecedent is always false). -/
theorem leadingExponentEx811Core37_antecedent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ e : Fin (kummerLogRank 37) → ℤ,
      ∀ N : ℕ, N ≤ 36 →
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
            (∑ a : Fin (kummerLogRank 37),
              e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
                (by decide) a) = 0 := by
  refine ⟨0, fun N _hN ↦ ?_⟩
  simp

-- The same-prime completed-log calc over the heavy `DworkCompleteIntegerRing` exceeds the default
-- heartbeat budget.
open BernoulliRegular (CPlusExponentProduct) in
/-- **The cyclotomic-representative local-log hypothesis transfer** (proven, isolated to keep the
heavy
`DworkCompleteIntegerRing` calc in its own elaboration unit).  For a real unit `u`, a cyclotomic
representative `v = CPlusExponentProduct s e` with `u * v⁻¹ ∈ pPowerSubgroup (E⁺) 37`, and a bridge
hypothesis `hu` on `u`, the core's hypothesis holds for `e`: `∑_a e_a • kummerLogCompletedColumn a`
vanishes through `λ`-level `36`.  (Via `§2` `completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum`
and the `§1` `37`-th-power log-transfer.) -/
theorem caseIIEx811Bridge_kummerLogSum_evalₐ_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {u v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ}
    {s : ℤ} {e : Fin (kummerLogRank 37) → ℤ}
    (hse : CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e = v)
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37)
    (hu : ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) = 0)
    {N : ℕ} (hN : N ≤ 36) :
    AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
        (∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
            (by decide) a) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hlog_eq :
      (∑ a : Fin (kummerLogRank 37),
        e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a) =
      completedLog (p := 37) (K := CyclotomicField 37 ℚ)
        (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v) :=
    hse ▸ (completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) s e).symm
  calc AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a)
        = AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v)) :=
        congrArg (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N) hlog_eq
    _ = AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) :=
        (caseIIEx811Bridge_completedLog_evalₐ_eq_of_div_mem_pPowerSubgroup hdiv hN).symm
    _ = 0 := hu N hN

-- The free-part class identification expands `realUnitToFreePartModP` over the heavy `𝓞 ℚ(ζ₃₇)`
-- ring and its cyclotomic-unit free-part quotient, exceeding the default budget.
open BernoulliRegular (CPlusGenerator CPlusExponentProduct) in
/-- **The cyclotomic-representative free-part-class identification** (proven, isolated).  For a real
unit `u` with cyclotomic representative `v = CPlusExponentProduct s e` and `u * v⁻¹ ∈ pPowerSubgroup
(E⁺) 37`, the eigencomponent-decomposition argument `∑_a e_a • φ(CPlusGenerator a)` equals
`realUnitToFreePartModP u`.  (Via `§2` `realUnitToFreePartModP_CPlusExponentProduct` and the `§1`
free-part identity.) -/
theorem caseIIEx811Bridge_freePartClass_eq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {u v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ}
    {s : ℤ} {e : Fin (kummerLogRank 37) → ℤ}
    (hse : CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e = v)
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37) :
    (∑ a : Fin (kummerLogRank 37),
      e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) =
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `∑ e_a • φ(CPlusGen a) = realUnitToFreePartModP (CPlusExponentProduct s e)`
  -- `= realUnitToFreePartModP v`, without `▸` (which would force a `whnf` matching
  -- `Additive.ofMul (CPlusExponentProduct s e)`).
  have hv :
      (∑ a : Fin (kummerLogRank 37),
        e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
          (Additive.ofMul (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) =
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul v) :=
    (FLT37.realUnitToFreePartModP_CPlusExponentProduct s e).symm.trans
      (congrArg (fun w ↦ FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul w)) hse)
  exact hv.trans (caseIIEx811Bridge_realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup hdiv).symm

-- The composition unifies two copies each of the heavy `DworkCompleteIntegerRing` log-sum and the
-- free-part class-sum; this `isDefEq` work is expensive (well below the `adicCompletionIntegers`
-- `whnf` wall, but above the default budget), hence the raised limit.
open BernoulliRegular (CPlusGenerator CPlusExponentProduct) in
/-- **`LeadingExponentBridge37` from the Exercise-8.11 core** (proven, axiom-clean given
`LeadingExponentEx811Core37`).

Given the genuine λ-adic leading-coefficient core `LeadingExponentEx811Core37`, the full bridge for
an
**arbitrary** real unit `u` follows by the structural reductions of `§1`–`§2′`:

1. `§2′` (`caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup`): there is `v ∈ C⁺` with
   `u * v⁻¹ ∈ pPowerSubgroup (E⁺) 37`, and `v = CPlusExponentProduct s e`
   (`exists_CPlusExponentProduct_of_mem_CPlus`);
2. `§1` transfers the bridge hypothesis: `evalₐ N (completedLog(v^{36})) = evalₐ N
   (completedLog(u^{36})) = 0`
   for `N ≤ 36`, and `completedLog(v^{36}) = ∑_a e_a • kummerLogCompletedColumn a` (`§2`,
   `completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum`), so the core's hypothesis holds for
   `e`;
3. the core gives `caseIIResidueProvenance_decomp (∑_a e_a • φ(CPlusGenerator a)) j = 0` for regular
   `j`,
   and `§2`+`§1` identify `∑_a e_a • φ(CPlusGenerator a) = realUnitToFreePartModP v =
   realUnitToFreePartModP u`. -/
theorem leadingExponentBridge37_of_ex811Core
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCore : LeadingExponentEx811Core37) :
    LeadingExponentBridge37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro u hu j hj
  -- (1) cyclotomic representative `v` of `u` modulo `37`-th powers.
  obtain ⟨v, hvCPlus, hdiv⟩ :=
    caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup u
  obtain ⟨s, e, hse⟩ :=
    exists_CPlusExponentProduct_of_mem_CPlus (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) hvCPlus
  -- (3) the eigencomponent identity (term mode), then apply the core with its hypothesis as a goal
  -- (so the heavy `evalₐ`-sum is the goal Lean writes, never a type Lean must reconcile by `whnf`).
  have hcls := caseIIEx811Bridge_freePartClass_eq hse hdiv
  have hHyp : ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a) = 0 :=
    fun N hN ↦ caseIIEx811Bridge_kummerLogSum_evalₐ_eq_zero hse hdiv hu hN
  -- `hcore`'s eigencomponent argument is written *identically* to `hcls`'s LHS, so the rewrite
  -- below is purely syntactic (no `whnf` reconciliation of the two free-part sums).
  have hcore : caseIIResidueProvenance_decomp
      (∑ a : Fin (kummerLogRank 37),
        e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
          (Additive.ofMul
            (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) j =
      0 :=
    hCore e hHyp j hj
  rw [hcls] at hcore
  exact hcore

/-- **`LeadingExponentEigenCollapse37` from the Exercise-8.11 core** (proven, axiom-clean given
`LeadingExponentEx811Core37`): chaining `leadingExponentBridge37_of_ex811Core` with the proven
valuation half `completedLogVanishingThroughLevel36_37_proven` (via
`leadingExponentEigenCollapse37_of_bridge'`).  Discharging `LeadingExponentEx811Core37` therefore
closes `LeadingExponentEigenCollapse37` — the regular-index half of Washington Lemma 9.9 (R3) —
leaving
FLT37 on the Case-II descent (R2) plus the carried Kellner boundary. -/
theorem leadingExponentEigenCollapse37_of_ex811Core
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCore : LeadingExponentEx811Core37) :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_bridge' (leadingExponentBridge37_of_ex811Core hCore)

end BernoulliRegular.FLT37.Eichler

end
