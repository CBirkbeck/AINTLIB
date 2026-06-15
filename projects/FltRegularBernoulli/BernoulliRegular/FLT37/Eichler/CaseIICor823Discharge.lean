import BernoulliRegular.FLT37.Eichler.CaseIIEx811EigenVandermonde
import BernoulliRegular.FLT37.Eichler.CaseIIAssumptionIIAssembled
import BernoulliRegular.FLT37.Eichler.CaseIICor823SecondOrder
import BernoulliRegular.FLT37.Eichler.CaseIICor823Endpoint
import BernoulliRegular.FLT37.KummerUnits
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealPthPower

/-!
# Washington Theorem 8.22 / Corollary 8.23 for `p = 37`: discharging
`Cor823PthPowerOfRationalModSq37`

This file discharges the `R4` core `Cor823PthPowerOfRationalModSq37`
(`CaseIICor823SecondOrder.lean`) — Washington *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
Theorem 8.22 / Corollary 8.23 for `p = 37`: under the proven non-degeneracy `M ≤ 1`, **every** unit
`η : (𝓞 K)ˣ` congruent to a rational integer modulo `37²` is a `37`-th power — down to a single,
sharply-isolated **second-order** residual at the irregular index `i = 32`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The reduction (everything but the second-order `i = 32` collapse is proven here)

Washington's Theorem 8.22 has four moving parts; for `p = 37` all but one are **proven**, by reusing
the fully-developed R3 (Lemma 9.9 regular-index) machinery:

1. **WLOG real** (Washington's "as in Theorem 5.35, we may assume `η` real").  By Proposition 1.5
   (`exists_zeta_pow_mul_real_eq_unit`), `η = ζ^m · algebraMap v` with `v : (𝓞 K⁺)ˣ` real.  The
   congruence `η ≡ c (mod 37²)` lies in `(ζ−1)²` (since `37 ∈ (ζ−1)²`), and `ζ^m ≡ 1 + m(ζ−1)
   (mod (ζ−1)²)` against the rational-mod-`(ζ−1)²` real factor forces `p ∣ m`, so `ζ^m = 1` and
   `η = algebraMap v`.  Then `η` is a `37`-th power iff `v` is (`isPthPower_image_iff`).

2. **`p`-saturation**: `v = v_C · w^{37}` with `v_C ∈ C⁺` cyclotomic
   (`caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup`, `37 ∤ h⁺`); `v` is a `37`-th power
   iff `v_C` is; and the mod-`37` free-part classes agree
   (`caseIIEx811Bridge_realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup`).

3. **Regular collapse (R3, proven)**: `v ≡ c (mod 37²)` ⟹ `v ≡ c (mod 37)`, so the proven R3
   `caseII_leadingExponentEigenCollapse37_proven` (via the proven local reduction
   `caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`) kills the **regular**
   eigencomponents `caseIIResidueProvenance_decomp (realUnitToFreePartModP v) j` (`j ≠ 15`).

4. **Irregular collapse (the genuine second-order residual)**: under the **mod-`37²`** congruence
   the single `j = 15` (`i = 32`) eigencomponent also vanishes.  This is Washington's Proposition
   8.12 at `i = 32` made explicit at the second-order coefficient — the only piece **not** supplied
   by the first-order Kummer-log matrix `concreteKummerLogMatrix = diag(B mod 37)·V` (which is
   degenerate at the row `i = 32` since `37 ∣ B₃₂`).  It is isolated below as
   `Cor823Omega32SecondOrderCollapse37`,
   a `def … : Prop` (**not** an axiom), with the proven non-degeneracy `37³ ∤ B₃₂`
   (`kellner_at_zero_not_dvd`, the `M ≤ 1` input) recorded as its sound second-order input.

With (3)+(4) all seventeen eigencomponents of `realUnitToFreePartModP v_C =
realUnitToFreePartModP v` vanish, so the class is `0` (the seventeen even Pollaczek eigenvectors
form a basis); and the
**proven** linear independence `caseIIEx811Eigen_genImg_linearIndependent` then forces every `C⁺`
exponent of `v_C` to vanish mod `37`, so `v_C` is a `37`-th power (`−1 = (−1)^{37}` since `37` is
odd) — hence `v`, hence `η`.

## The `c₃₂ = 68` second-order bookkeeping

Washington works in the real uniformizer `λ_W = (ζ−1)(ζ⁻¹−1) = 2−(ζ+ζ⁻¹)`, with `(p) = λ_W^{(p−1)/2}
= λ_W^{18}`.  The repo's `lambdaIdeal` is the *cyclotomic* uniformizer `λ = ζ−1` with `(p) =
λ^{36}`, so `λ_W = λ²` in `λ`-valuation.  Washington's leading non-constant `λ_W`-exponent of
`E_i^{(N)}` is
`c_i = i/2 + (p−1)/2 · v_p(L_p(1,ω^i))` (p. 160).  For `i = 32`, `p = 37`, with the proven sharp
valuation `v₃₇(L_p(1,ω³²)) = 1` (`M = 1`), this is `c₃₂ = 16 + 18·1 = 34` in `λ_W`, i.e. **repo
`λ`-level `2·34 = 68`** — the level at which `completedLog E₃₂`'s leading coefficient is `≡ B₃₂
(mod 37²) ≠ 0`, the second-order non-degeneracy the residual records.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Theorem 8.22, Corollary
  8.23, Proposition 8.12, p. 171; Lemma 8.21, Proposition 8.20), §5.6 (Theorem 5.36, Proposition
  1.5), §9.2 (Theorem 9.4, Lemma 9.9).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007),
  Proposition 2.7.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField IsCyclotomicExtension
open scoped NumberField BigOperators

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits

/-! ## 1. Step D: a cyclotomic unit with vanishing mod-`37` free-part class is a `37`-th power

If `v ∈ C⁺` has `realUnitToFreePartModP v = 0`, then writing `v = CPlusExponentProduct s e` the
**proven** linear independence of the generator images forces `(e a : ZMod 37) = 0` for all `a`; the
sign factor `(−1)^s` is a `37`-th power (`−1 = (−1)^{37}`, `37` odd), and each `CPlusGenerator a ^
e a` is a `37`-th power because `37 ∣ e a`.  Hence `v ∈ pPowerSubgroup (EPlus) 37`. -/

/-- **`−1` is a global `37`-th power** (proven): `(−1 : (𝓞 K⁺)ˣ) = (−1)^{37}` since `37` is odd, so
`−1 ∈ pPowerSubgroup (EPlus) 37`. -/
theorem caseIICor823_neg_one_mem_pPowerSubgroup
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (-1 : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) ∈
      pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37 :=
  ⟨-1, Subgroup.mem_top _, by rw [show (37 : ℕ) = 2 * 18 + 1 from rfl, pow_succ, pow_mul,
    neg_one_sq, one_pow, one_mul]⟩

/-- **A `37`-divisible-exponent `C⁺` product is a `37`-th power** (proven).  If `37 ∣ e a` for every
`a` (as integers), then `CPlusExponentProduct 37 s e ∈ pPowerSubgroup (EPlus) 37`.

Proof: `(−1)^s` is a `37`-th power (`caseIICor823_neg_one_mem_pPowerSubgroup`, `37` odd), and each
`CPlusGenerator a ^ e a = (CPlusGenerator a ^ (e a / 37))^{37}` is a `37`-th power; the subgroup
`pPowerSubgroup` is closed under products. -/
theorem caseIICor823_CPlusExponentProduct_mem_pPowerSubgroup_of_dvd
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (s : ℤ) (e : Fin ((37 - 3) / 2) → ℤ) (he : ∀ a, (37 : ℤ) ∣ e a) :
    CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e ∈
      pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37 := by
  classical
  unfold CPlusExponentProduct
  -- The sign factor `(−1)^s` is a `37`-th power.
  refine Subgroup.mul_mem _
    ((pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37).zpow_mem
      caseIICor823_neg_one_mem_pPowerSubgroup s) ?_
  -- Each generator power is a `37`-th power because `37 ∣ e a`.
  refine Subgroup.prod_mem _ (fun a _ => ?_)
  obtain ⟨k, hk⟩ := he a
  refine ⟨CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a ^ k,
    Subgroup.mem_top _, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, hk]
  congr 1
  push_cast
  ring

/-- **Step D** (proven, axiom-clean): a cyclotomic unit `v ∈ C⁺` (here, an explicit
`CPlusExponentProduct s e`) whose mod-`37` free-part class vanishes is a `37`-th power in
`(𝓞 K⁺)ˣ`.

From `realUnitToFreePartModP v = 0` and `v = CPlusExponentProduct s e`, the free-part class is
`∑_a (e a : ZMod 37) • φ(CPlusGenerator a) = 0`; the **proven** linear independence
`caseIIEx811Eigen_genImg_linearIndependent` forces `(e a : ZMod 37) = 0`, i.e. `37 ∣ e a`; then
`caseIICor823_CPlusExponentProduct_mem_pPowerSubgroup_of_dvd` gives the `37`-th power. -/
theorem caseIICor823_mem_pPowerSubgroup_of_freePartClass_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (s : ℤ) (e : Fin ((37 - 3) / 2) → ℤ)
    (hzero : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
      (Additive.ofMul (CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e))
        = 0) :
    CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e ∈
      pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Expand the free-part class as a generator combination.
  rw [FLT37.realUnitToFreePartModP_CPlusExponentProduct] at hzero
  simp_rw [← Int.cast_smul_eq_zsmul (ZMod 37)] at hzero
  -- Linear independence forces each `(e a : ZMod 37) = 0`.
  have hcoeff : ∀ a, ((e a : ℤ) : ZMod 37) = 0 :=
    Fintype.linearIndependent_iff.mp caseIIEx811Eigen_genImg_linearIndependent
      (fun a => ((e a : ℤ) : ZMod 37)) hzero
  -- `(e a : ZMod 37) = 0 ↔ 37 ∣ e a`.
  have hdvd : ∀ a, (37 : ℤ) ∣ e a := fun a =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd (e a) 37).mp (hcoeff a)
  exact caseIICor823_CPlusExponentProduct_mem_pPowerSubgroup_of_dvd s e hdvd

/-! ## 2. The genuine second-order residual: the `i = 32` eigencomponent collapse

This is the **only** undischarged piece of Theorem 8.22 for `p = 37`: Washington's Proposition 8.12
at the irregular index `i = 32`, made explicit at the **second-order** coefficient.  For a real unit
`u : (𝓞 K⁺)ˣ` whose `K`-image `algebraMap u` is congruent to a rational integer modulo `37²` (the
genuine Corollary-8.23 input class), the single irregular eigencomponent
`caseIIResidueProvenance_decomp (realUnitToFreePartModP u) 15` (`j = 15`, `i = 2(15+1) = 32`)
vanishes.

Why this is the residual, and why the first-order matrix does not supply it: the proven
`concreteKummerLogMatrix = diag(B mod 37)·V` reads, at row `j`, the factor `B_{2(j+1)} mod 37`.  At
`j = 15` (`i = 32`) this factor is `B₃₂/32 mod 37 = 0` (`37 ∣ B₃₂`, the irregularity of `37`), so
the first-order matrix row is identically zero and carries **no** information about the `j = 15`
eigencomponent — exactly the degeneracy R3 routes around (it kills only `j ≠ 15`).  Recovering the
`j = 15` component requires the **second-order** leading coefficient of `completedLog E₃₂`, which by
Proposition 8.12 sits at repo `λ`-level `c₃₂ = 2·(16 + 18·1) = 68` and equals `B₃₂ mod 37² ≠ 0` (the
proven non-degeneracy `M ≤ 1`).  This is genuine `p`-adic-`L` content not present in the repo's
first-order Kummer-log infrastructure.

It is **sound** — it constrains the irregular eigencomponent of a unit satisfying the *sharp
second-order* congruence `algebraMap u ≡ c (mod 37²)`, never an `E₃₂`-monomial property of an
arbitrary class; **non-circular** — the mod-`37²` hypothesis is strictly stronger than the mod-`37`
one R3 consumes, and is the genuine valuation-theoretic content of Proposition 8.12 at `i = 32`,
phrased on the actual congruence datum; and **non-vacuous** — the antecedent holds for `u = 1`
(`c = 1`) and for every real `37`-th power (see
`cor823Omega32SecondOrderCollapse37_antecedent_inhabited`). -/
def Cor823Omega32SecondOrderCollapse37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
    ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) →
    caseIIResidueProvenance_decomp
      (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) 15 = 0

/-- **The second-order residual has an inhabited antecedent** (non-vacuity, proven): the unit
`u = 1` with `c = 1` satisfies `37² ∣ algebraMap 1 - 1 = 0`.  So
`Cor823Omega32SecondOrderCollapse37` is a real implication on a satisfiable hypothesis (the
Corollary-8.23 input class), not vacuously true. -/
theorem cor823Omega32SecondOrderCollapse37_antecedent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
      ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
        ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
            (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
          (c : 𝓞 (CyclotomicField 37 ℚ))) :=
  ⟨1, 1, by simp⟩

/-! ## 3. The real-unit Theorem 8.22 (proven from R3 + the residual + Step D + saturation)

For a **real** unit `u : (𝓞 K⁺)ˣ` with `algebraMap u ≡ c (mod 37²)`, `u` is a `37`-th power in
`(𝓞 K⁺)ˣ`.  This is Theorem 8.22 after the WLOG-real reduction.  Composition: R3 kills the regular
eigencomponents, the residual kills the `j = 15` one, so the whole free-part class is `0`; Step D
(applied to the `p`-saturated cyclotomic representative `v_C ∈ C⁺`) then gives the `37`-th power. -/

/-- **Theorem 8.22 for a real unit** (proven, axiom-clean given the residual
`Cor823Omega32SecondOrderCollapse37`).

For `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u − c` (`c : ℤ`), there is `ε : (𝓞 K⁺)ˣ` with `u = ε^{37}`.

Proof:
* `p`-saturate `u = v_C · w^{37}` with `v_C ∈ C⁺` (`…exists_cyclotomic_div_mem_pPowerSubgroup`);
* their free-part classes agree (`…realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup`);
* R3 (`caseII_leadingExponentEigenCollapse37_proven` via the proven local reduction, using `37 ∣
  algebraMap u − c` from the mod-`37²` hypothesis) kills `decomp (φ u) j` for `j ≠ 15`;
* the residual `hCollapse` kills `decomp (φ u) 15`;
* so `φ u = ∑_j 0 • E_{2(j+1)} = 0 = φ v_C`, and Step D
  (`caseIICor823_mem_pPowerSubgroup_of_freePartClass_zero`, after writing `v_C =
  CPlusExponentProduct s e`) gives `v_C ∈ pPowerSubgroup`, i.e. `v_C = ε₀^{37}`; then `u = v_C ·
  w^{37} = (ε₀ · w)^{37}`. -/
theorem caseIICor823_real_isPthPower_of_omega32Collapse
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCollapse : Cor823Omega32SecondOrderCollapse37)
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ)))) :
    ∃ ε : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ, u = ε ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The mod-`37` congruence (weaker), needed for R3.
  have hc1 : (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) :=
    dvd_trans (dvd_pow_self (37 : 𝓞 (CyclotomicField 37 ℚ)) (by norm_num)) hc
  -- (1) p-saturation: a cyclotomic representative `v_C ∈ C⁺`.
  obtain ⟨vC, hvC_mem, hdiv⟩ :=
    caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup u
  -- The free-part classes of `u` and `v_C` agree.
  have hcls :
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) =
        FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul vC) :=
    caseIIEx811Bridge_realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup hdiv
  -- (3) R3: regular eigencomponents of `φ u` vanish.
  have hreg : ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) j = 0 :=
    caseIILeadingExponent_regular_components_zero
      caseII_leadingExponentEigenCollapse37_proven u c hc1
  -- (4) The residual: the `j = 15` eigencomponent of `φ u` vanishes.
  have h15 : caseIIResidueProvenance_decomp
      (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) 15 = 0 :=
    hCollapse u c hc
  -- All eigencomponents of `φ u` vanish, so `φ u = 0`.
  have hall : ∀ j : Fin 18,
      caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) j = 0 := by
    intro j
    by_cases hj : j = 15
    · rw [hj]; exact h15
    · exact hreg j hj
  have hφu0 :
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) = 0 := by
    rw [caseIIResidueProvenance_decomp_spec
      (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u))]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [hall j, zero_smul]
  -- (6) Step D: `v_C = CPlusExponentProduct s e` with vanishing free-part class is a `37`-th power.
  obtain ⟨s, e, hse⟩ :=
    BernoulliRegular.exists_CPlusExponentProduct_of_mem_CPlus
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) hvC_mem
  have hφvC0 :
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul (CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ)
          (by decide) s e)) = 0 := by
    rw [hse, ← hcls]; exact hφu0
  have hvCpow : vC ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37 := by
    rw [← hse]
    exact caseIICor823_mem_pPowerSubgroup_of_freePartClass_zero s e hφvC0
  -- `v_C = ε₀^{37}`.
  obtain ⟨ε₀, _, hε₀⟩ := hvCpow
  -- `u = v_C · w^{37}` from the saturation: extract `w` with `u * v_C⁻¹ = w^{37}`.
  obtain ⟨w, _, hw⟩ := hdiv
  -- `u = ε₀^{37} · w^{37} = (ε₀ · w)^{37}`.
  refine ⟨ε₀ * w, ?_⟩
  rw [mul_pow, hε₀, hw, mul_comm, mul_assoc, inv_mul_cancel, mul_one]

/-! ## 4. The WLOG-real reduction and the full Theorem 8.22 / Corollary 8.23

Washington's "as in the proof of Theorem 5.35, we may assume `η` real" (p. 171; the argument is in
the proof of Theorem 5.36, pp. 79–80).  By Proposition 1.5 (`exists_zeta_pow_mul_real_eq_unit`),
`η = ζ^m · algebraMap v` with `v : (𝓞 K⁺)ˣ` real.  Applying complex conjugation `σ`
(`ringOfIntegersComplexConj`, which fixes `algebraMap v` and the rational integer `c`, and inverts
`ζ`) to `η ≡ c (mod 37²)` gives `37² ∣ ↑η − ↑(σ η) = ↑η · (1 − ↑(ζ^{−2m}))`, and since `↑η` is a
unit, `37² ∣ ↑(ζ^{2m}) − 1`.  The norm/valuation of `ζ^{2m} − 1` then forces `ζ^{2m} = 1`, whence
`p ∣ m` (`p` odd) and `ζ^m = 1`, so `η = algebraMap v`. -/

/-- **`37² ∣ ζ^n − 1` forces `ζ^n = 1`** (proven).  In `𝓞 K`, if `37²` divides `↑(ζU^n) − 1` (with
`ζU = (zeta_spec).unit'` the standard primitive `37`-th root), then `ζU^n = 1`.

Proof: `ζU^n` is a power of `ζ`, hence `ζU^n = ζU^{n mod 37}` with `n mod 37 < 37`.  If `n mod 37 ≠
0`, it is coprime to `37`, so `↑ζU^{n mod 37} − 1` is associated to the prime `ζ − 1`
(`associated_zeta_sub_one_zeta_pow_sub_one`); but `(ζ−1)^{72} ∣ 37² ∣ ↑ζU^n − 1`, forcing
`(ζ−1)^{72}` to divide a prime-times-unit — impossible.  So `n mod 37 = 0` and `ζU^n = 1`. -/
theorem caseIICor823_zeta_pow_eq_one_of_dvd
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (n : ℕ)
    (hdvd : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      (((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit' : (𝓞 (CyclotomicField 37 ℚ))ˣ) ^ n : _) - 1) :
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit' : (𝓞 (CyclotomicField 37 ℚ))ˣ) ^ n = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set ζU : (𝓞 (CyclotomicField 37 ℚ))ˣ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit' with hζU
  -- `ζm1 = ζ − 1`, the uniformizer at the prime above `37`.
  set ζm1 : 𝓞 (CyclotomicField 37 ℚ) := (ζU : 𝓞 (CyclotomicField 37 ℚ)) - 1 with hζm1
  -- `ζU ^ n = ζU ^ (n % 37)` since `ζU ^ 37 = 1`.
  have hζ37 : ζU ^ 37 = 1 := by
    rw [hζU]; exact (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit'_pow
  have hred : ζU ^ n = ζU ^ (n % 37) := by
    conv_lhs => rw [← Nat.div_add_mod n 37, pow_add, pow_mul, hζ37, one_pow, one_mul]
  -- Reduce to `n % 37 = 0`.
  by_contra hne
  -- `ζU ^ (n % 37) = 1` would follow if `n % 37 = 0`; so `n % 37 ≠ 0`.
  have hmod_ne : n % 37 ≠ 0 := fun h0 => hne (by rw [hred, h0, pow_zero])
  have hmod_lt : n % 37 < 37 := Nat.mod_lt n (by norm_num)
  -- `n % 37 < 37` is coprime to the prime `37` (it is positive and below `37`).
  have hcop : (n % 37).Coprime 37 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr
      (fun hdvd' => by have := Nat.le_of_dvd (by omega) hdvd'; omega))
  -- `↑(ζU ^ (n % 37)) − 1` is associated to `ζ − 1`, hence prime.
  have hassoc : Associated ζm1
      ((ζU : 𝓞 (CyclotomicField 37 ℚ)) ^ (n % 37) - 1) :=
    associated_zeta_sub_one_zeta_pow_sub_one 37 (CyclotomicField 37 ℚ) (n % 37) hcop (by norm_num)
  -- `↑(ζU ^ n) − 1 = ↑ζU ^ (n % 37) − 1` (push the unit power through the coercion).
  have hcoe : (((ζU ^ n : (𝓞 (CyclotomicField 37 ℚ))ˣ)) : 𝓞 (CyclotomicField 37 ℚ)) - 1 =
      (ζU : 𝓞 (CyclotomicField 37 ℚ)) ^ (n % 37) - 1 := by
    rw [hred, Units.val_pow_eq_pow_val]
  rw [hcoe] at hdvd
  -- `(ζ−1)^{36} ~ 37`, so `(ζ−1)^{72} ∣ 37²`.
  have hzp : Associated (ζm1 ^ 36) (37 : 𝓞 (CyclotomicField 37 ℚ)) := by
    have := associated_zeta_sub_one_pow_prime (zeta_spec 37 ℚ (CyclotomicField 37 ℚ))
    rwa [show (37 - 1 : ℕ) = 36 from rfl] at this
  have hpow72 : (ζm1 ^ 72) ∣ (37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2 := by
    have h2 : (ζm1 ^ 36) ^ 2 ∣ (37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2 := pow_dvd_pow_of_dvd hzp.dvd 2
    rwa [← pow_mul, show 36 * 2 = 72 from rfl] at h2
  -- So `(ζ−1)^{72} ∣ ↑ζU^{n%37} − 1`, but the latter is `(ζ−1) · unit`.
  have hdvd72 : (ζm1 ^ 72) ∣ ((ζU : 𝓞 (CyclotomicField 37 ℚ)) ^ (n % 37) - 1) :=
    dvd_trans hpow72 hdvd
  -- `↑ζU^{n%37} − 1 = (ζ−1) · u` for a unit `u`; then `(ζ−1)^{72} ∣ (ζ−1)·u` forces
  -- `(ζ−1)^{71} ∣ u`.
  obtain ⟨u, hu⟩ := hassoc
  rw [← hu] at hdvd72
  -- Cancel `(ζ − 1)`: `(ζ−1)^{72} = (ζ−1)^{71} · (ζ−1)`, and `(ζ−1) ≠ 0`.
  have hζne : ζm1 ≠ 0 := by
    rw [hζm1, hζU]; exact BernoulliRegular.FLT37.zetaSubOne_ne_zero 37 (CyclotomicField 37 ℚ)
  rw [show (ζm1 ^ 72) = ζm1 ^ 71 * ζm1 from by rw [← pow_succ], mul_comm] at hdvd72
  have hdvd71 : (ζm1 ^ 71) ∣ (u : 𝓞 (CyclotomicField 37 ℚ)) :=
    (mul_dvd_mul_iff_left hζne).mp hdvd72
  -- But `u` is a unit, so `ζ − 1` (a non-unit) cannot divide it.
  have hunit : IsUnit ζm1 :=
    isUnit_of_dvd_unit (dvd_trans (dvd_pow_self _ (by norm_num)) hdvd71) u.isUnit
  rw [hζm1, hζU] at hunit
  exact BernoulliRegular.FLT37.zetaSubOne_not_isUnit 37 (CyclotomicField 37 ℚ) hunit

/-- **The WLOG-real reduction: every unit `≡ rational mod 37²` is `ζ^m` times a real unit, with
`ζ^m = 1`** (proven, axiom-clean).

For `η : (𝓞 K)ˣ` with `37² ∣ ↑η − c` (`c : ℤ`), there is a **real** unit `v : (𝓞 K⁺)ˣ` with
`η = algebraMap v`.

Proof: by Proposition 1.5 (`exists_zeta_pow_mul_real_eq_unit`), `η = ζU^m · algebraMap v` with `v`
real.  Complex conjugation `σ` fixes `algebraMap v` and `c`, and `σ(ζU) = ζU⁻¹`, so `σ(η) =
ζU^{−m}·algebraMap v = η · (ζU^{2m})⁻¹`.  From `37² ∣ ↑η − c`, applying the ring hom `σ` gives
`37² ∣ ↑(σ η) − c`; subtracting, `37² ∣ ↑η − ↑(σ η) = ↑η·(1 − ↑(ζU^{2m})⁻¹)`.  As `↑η` is a unit,
`37² ∣ 1
− ↑(ζU^{2m})⁻¹`; multiplying by the unit `↑ζU^{2m}` gives `37² ∣ ↑(ζU^{2m}) − 1`, so by
`caseIICor823_zeta_pow_eq_one_of_dvd`, `ζU^{2m} = 1`, hence `ζU^m = 1` (as `(ζU^m)² = 1` and `ζU^m`
has odd order `∣ 37`), and `η = algebraMap v`. -/
theorem caseIICor823_exists_real_eq_of_dvd
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (η : (𝓞 (CyclotomicField 37 ℚ))ˣ) (c : ℤ)
    (hc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((η : 𝓞 (CyclotomicField 37 ℚ)) - (c : 𝓞 (CyclotomicField 37 ℚ)))) :
    ∃ v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      η = Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom v := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Prop 1.5: `η = ζU^m · map v`, `v` real.
  obtain ⟨m, v, hmv⟩ :=
    FLT37.exists_zeta_pow_mul_real_eq_unit (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) η
  set ζU : (𝓞 (CyclotomicField 37 ℚ))ˣ := (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit' with hζU
  set mapv : (𝓞 (CyclotomicField 37 ℚ))ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
      (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom v with hmapv
  -- `mapv` is real (σ-fixed) at the unit level.
  have hmapv_real : NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) mapv = mapv :=
    (NumberField.IsCMField.unitsComplexConj_eq_self_iff (K := CyclotomicField 37 ℚ) mapv).mpr
      ⟨v, rfl⟩
  -- `σ(ζU) = ζU⁻¹`.
  have hζtor : ζU ∈ NumberField.Units.torsion (CyclotomicField 37 ℚ) :=
    (CommGroup.mem_torsion _ _).2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨37, by norm_num, (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit'_pow⟩)
  have hσζ : NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) ζU = ζU⁻¹ :=
    NumberField.IsCMField.unitsComplexConj_torsion (K := CyclotomicField 37 ℚ) ⟨ζU, hζtor⟩
  -- `σ(η) = ζU⁻ᵐ · mapv`, so `η · σ(η)⁻¹ = ζU^{2m}`.
  have hση : NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) η = ζU⁻¹ ^ m * mapv := by
    rw [hmv, map_mul, map_pow, hσζ, hmapv_real]
  have hdiv_eq : η * (NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) η)⁻¹ =
      ζU ^ (2 * m) := by
    rw [hση]
    conv_lhs => rw [hmv]
    -- `(ζU⁻¹^m)⁻¹ = ζU^m`, and `mapv·mapv⁻¹ = 1`.
    rw [mul_inv_rev, inv_pow, inv_inv, mul_assoc, ← mul_assoc mapv, mul_inv_cancel, one_mul,
      ← pow_add, two_mul]
  -- The mod-`37²` divisibility for `↑(ζU^{2m}) − 1`.
  -- Apply `σ` to `37² ∣ ↑η − c`.
  have hσc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      (((NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) η :
          (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) -
        (c : 𝓞 (CyclotomicField 37 ℚ)) := by
    -- Apply the ring equiv `σ`; `σ(↑η) = ↑(unitsComplexConj η)` (rfl) and `σ(37²)=37²`, `σ(c)=c`.
    have hσdvd := map_dvd
      (NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ)) hc
    rw [map_sub, map_pow, map_ofNat,
      FLT37.LehmerVandiver.CaseII.ringOfIntegersComplexConj_intCast_eq] at hσdvd
    -- `ringOfIntegersComplexConj K ↑η = ↑(unitsComplexConj K η)` definitionally.
    have hηconj : NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
        (η : 𝓞 (CyclotomicField 37 ℚ)) =
        ((NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) η :
          (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) := rfl
    rwa [hηconj] at hσdvd
  -- Subtract: `37² ∣ ↑η − ↑(σ η)`.
  have hsub : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((η : 𝓞 (CyclotomicField 37 ℚ)) -
        ((NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) η :
          (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) := by
    have := dvd_sub hc hσc
    rwa [sub_sub_sub_cancel_right] at this
  -- `↑η − ↑(σ η) = ↑η · (1 − ↑(ζU^{2m})⁻¹)`, and `↑η` is a unit ⟹ `37² ∣ 1 − ↑(ζU^{2m})⁻¹`.
  -- Then multiply by the unit `↑ζU^{2m}` to get `37² ∣ ↑(ζU^{2m}) − 1`.
  have hση_eq : NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) η =
      η * (ζU ^ (2 * m))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← hdiv_eq, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  have hsub2 : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((((ζU ^ (2 * m) : (𝓞 (CyclotomicField 37 ℚ))ˣ)) : 𝓞 (CyclotomicField 37 ℚ))) - 1 := by
    rw [hση_eq] at hsub
    -- `↑η − ↑(η · (ζU^{2m})⁻¹) = ↑η · (1 − ↑(ζU^{2m})⁻¹)`.
    have hfac : (η : 𝓞 (CyclotomicField 37 ℚ)) -
        ((η * (ζU ^ (2 * m))⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) =
          (η : 𝓞 (CyclotomicField 37 ℚ)) *
            (1 - (((ζU ^ (2 * m))⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
              𝓞 (CyclotomicField 37 ℚ))) := by
      rw [Units.val_mul]; ring
    rw [hfac] at hsub
    -- `↑η` is a unit; cancel it.
    have h1 : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
        (1 - (((ζU ^ (2 * m))⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
          𝓞 (CyclotomicField 37 ℚ))) :=
      (Units.isUnit η).dvd_mul_left.mp hsub
    -- Multiply by the unit `↑(ζU^{2m})`: `↑(ζU^{2m}) · (1 − ↑(ζU^{2m})⁻¹) = ↑(ζU^{2m}) − 1`.
    have h2 := h1.mul_left ((ζU ^ (2 * m) : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
      𝓞 (CyclotomicField 37 ℚ))
    rwa [mul_sub, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one] at h2
  -- `ζU^{2m} = 1`.
  have hpow1 : ζU ^ (2 * m) = 1 := by
    have := caseIICor823_zeta_pow_eq_one_of_dvd (2 * m) (by rw [hζU] at hsub2; exact hsub2)
    rw [hζU]; exact this
  -- `ζU^m = 1` from `(ζU^m)² = 1` and `ζU^m` of odd order dividing `37`.
  have hmsq : (ζU ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm m 2]; exact hpow1
  have hm1 : ζU ^ m = 1 := by
    -- `(ζU^m)^37 = 1` (order `∣ 37`), and `(ζU^m)^2 = 1`; `37 = 1 + 2·18` ⟹
    -- `ζU^m = (ζU^m)^37 · (((ζU^m)^2)⁻¹)^18`, whose two factors are both `1`.
    set y : (𝓞 (CyclotomicField 37 ℚ))ˣ := ζU ^ m with hy
    have h37 : y ^ 37 = 1 := by
      rw [hy, ← pow_mul, mul_comm, pow_mul, hζU,
        (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit'_pow, one_pow]
    have hsplit : y = y ^ 37 * ((y ^ 2) ^ 18)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, ← pow_mul]
      nth_rewrite 1 [← pow_one y]
      rw [← pow_add]
    rw [hsplit, h37, hmsq, one_pow, inv_one, mul_one]
  -- Conclude `η = mapv`.
  refine ⟨v, ?_⟩
  rw [hmv, hm1, one_mul]

/-! ## 5. `Cor823PthPowerOfRationalModSq37` (Theorem 8.22 / Corollary 8.23) discharged from the
single second-order residual

Assembling: WLOG-real (`caseIICor823_exists_real_eq_of_dvd`) presents `η = algebraMap v`; the real
Theorem 8.22 (`caseIICor823_real_isPthPower_of_omega32Collapse`, from R3 + the residual + Step D)
makes `v` a `37`-th power `ε^{37}`; and `η = algebraMap v = (algebraMap ε)^{37}`. -/

/-- **Washington Theorem 8.22 / Corollary 8.23 for `p = 37`, discharged from the second-order
residual** (proven, axiom-clean given `Cor823Omega32SecondOrderCollapse37`).

`Cor823PthPowerOfRationalModSq37` follows from the single second-order `i = 32` collapse residual:
WLOG `η` is real, `η = algebraMap v`; the real-unit Theorem 8.22
(`caseIICor823_real_isPthPower_of_omega32Collapse`) makes `v = ε^{37}`; hence
`η = (Units.map (algebraMap _) ε)^{37}`.  The proven `M ≤ 1` non-degeneracy
(`caseII_cor823_valuation_input_proven`) is consumed by the target's antecedent; everything except
the residual is proven (R3, Step D, `p`-saturation, WLOG-real, K↔K⁺). -/
theorem cor823PthPowerOfRationalModSq37_of_omega32Collapse
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCollapse : Cor823Omega32SecondOrderCollapse37) :
    Cor823PthPowerOfRationalModSq37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro _hM η hη
  obtain ⟨c, hc⟩ := hη
  -- WLOG-real: `η = algebraMap v`.
  obtain ⟨v, hv⟩ := caseIICor823_exists_real_eq_of_dvd η c hc
  -- The mod-`37²` congruence transfers to `algebraMap v`.
  have hcv : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom v : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) := by
    rwa [← hv]
  -- The real Theorem 8.22: `v = ε^{37}`.
  obtain ⟨ε, hε⟩ := caseIICor823_real_isPthPower_of_omega32Collapse hCollapse v c hcv
  -- `η = algebraMap v = (algebraMap ε)^{37}`.
  refine ⟨Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
    (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom ε, ?_⟩
  rw [hv, hε, map_pow]

/-! ## 6. The FLT37 endpoint with `R4` discharged down to the second-order residual

`fermatLastTheoremFor_thirtyseven_of_cor823_firstOrder` (`CaseIICor823Endpoint.lean`) takes
`Cor823PthPowerOfRationalModSq37` (R4) as a hypothesis; supplying it via
`cor823PthPowerOfRationalModSq37_of_omega32Collapse` replaces R4 with the strictly-smaller
second-order residual `Cor823Omega32SecondOrderCollapse37`, leaving FLT37 on R2 + the first-order
producer + the carried Kellner boundary + the single second-order `i = 32` collapse. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37` with `R4` reduced to the second-order `i = 32` collapse**
(proven, axiom-clean given the genuine residuals + the carried Kellner Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_cor823_firstOrder`, but Washington Theorem 8.22 /
Corollary 8.23 (`Cor823PthPowerOfRationalModSq37`, R4) is supplied by
`cor823PthPowerOfRationalModSq37_of_omega32Collapse` from the single second-order residual
`Cor823Omega32SecondOrderCollapse37` — Proposition 8.12 at the irregular index `i = 32`.  All of the
Theorem-8.22 plumbing (WLOG-real, `p`-saturation, the proven R3 regular collapse, Step D, the K↔K⁺
descent) is proven; only the second-order `i = 32` leading coefficient remains. -/
theorem fermatLastTheoremFor_thirtyseven_of_omega32Collapse
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_omega32 : Cor823Omega32SecondOrderCollapse37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_cor823_firstOrder
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (cor823PthPowerOfRationalModSq37_of_omega32Collapse caseII_omega32)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
