import BernoulliRegular.FLT37.Eichler.CaseIIRealStep6
import BernoulliRegular.FLT37.Eichler.CaseIIRootClassConjFixedClosed
import BernoulliRegular.FLT37.Eichler.CaseIIIdealKummerUnramified

/-!
# Washington Lemma 9.8 step 6 `ρ_a`-reality, fully discharged (R4, the irregular-index local power)

This file **proves** Washington *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Lemma 9.8
**step 6** — the `ρ_a`-reality `γ`-ratio congruence — over `RealCaseIIData37`, and re-derives the
step-6 congruence form `CaseIIMirimanoffStep6CongReal37` from it.  This was the last analytic
residual of R4 (the irregular-index local power); everything else in R4 is already proven.

## Soundness correction (B2): the prior residual was over-stated at `37 ∣ a`

`CaseIIRealStep6GammaRatioPthPower37` (`CaseIIRealStep6.lean`) quantifies over **all** `a` with
`¬37∣(a-j)`, `¬37∣(a+j)`, and asserts the existence of `γ` with
`D.x + ζ^a·D.y = (1 - ζ^a)·γ`.  Those two side-conditions do **not** exclude `37 ∣ a` (at `a ≡ 0`
they read `-j ≢ 0`, `j ≢ 0`, both true since `η = ζ^j ≠ 1`).  But for `37 ∣ a`,
`zetaPow 37 K a = 1`, so `1 - ζ^a = 0` and the equation forces `D.x + D.y = 0` — impossible over a
descent datum (`D.x + D.y = 0 ⟹ D.x^37 + D.y^37 = 0 ⟹ D.z = 0`, contradicting the `𝔭`-unit `D.z`).
So the prior form is **false** at `37 ∣ a` (it is genuinely consumed there:
`caseIIMirimanoffStep6CongReal37_of_gammaRatio` invokes it at every `a`, including the reachable
`a = (b+i).val` with `b ≡ -i mod 37`).  See `.mathlib-quality/b2_log.jsonl`, ticket
`R4-step6-gammaRatio`.

The **corrected** residual `CaseIIRealStep6GammaRatioPthPowerNZ37` adds the side-condition
`¬(37:ℤ)∣a` (Washington's implicit `a ≢ 0 mod p`: the denominator `1 - ζ^a` of his normalization
`γ_a = (ω + ζ^aθ)/(1 - ζ^a)` must be nonzero).  It is **fully proven** here — *not* a named
hypothesis.

## The proof (Washington §9.1–9.2, via the proven Lemma 9.2 element form)

Fix `¬37∣a`.  Then `η_a := ζ^a` is a `37`-th root `≠ 1 = D.etaZero`
(`caseII_etaZero_eq_one`).  Set `γ := (D.x + ζ^a·D.y)/(1 - ζ^a) ∈ 𝓞 K` (the quotient exists, since
`ζ - 1 ∣ D.x + D.y·η_a` and `1 - ζ^a` is associate to `ζ - 1` for `a ≢ 0`); then
`σγ = (D.x + ζ^{-a}·D.y)/(1 - ζ^{-a})` (apply `σ`).  The key field identity (proven below) is

  `γ/σγ = caseII_correctedRadical D η_a (caseII_correctionUnit η_a)`,

the **anti-fixed corrected radical** `-ζ^{-a}·(D.x + ζ^a y)/(D.x + ζ^{-a} y)` of Washington §9.1.
By the **proven Washington Lemma 9.2 element form** `flt37_antiFixed_radical_isPthPower` (which uses
`¬37∣h⁺ = Sinnott.flt37_not_dvd_hPlus` and the **proven** unramifiedness
`caseIIIdealKummerUnramified37_proven`), this radical is a `37`-th power `β^{37}` in `K` (the `α²=1`
root-of-unity case is handled directly).  Hence `γ/σγ = β^{37}`, and putting `δ := β·σγ` gives
`δ^{37} = γ·σγ^{36} ∈ 𝓞 K`, so `δ ∈ 𝓞 K` (integrally closed) and
`v := Q(δ)·Q(σγ)⁻¹` satisfies `Q(γ)·Q(σγ)⁻¹ = v^{37}` in `𝓞 K / lv149`.  This is exactly the
`ρ_a`-reality conclusion: the root-of-unity part of the descent unit is trivial **because** the
anti-fixed radical is a genuine `p`-th power (Lemma 9.2 / `¬37∣h⁺`), *not* by a mod-`𝔩` congruence
(which does not hold as a pure roots-of-unity identity).

`CaseIIMirimanoffStep6CongReal37` (Washington step 6) is then re-derived from the corrected
residual: the `37∣a` case is trivial (`ζ^a = 1` makes both sides of the congruence equal), and the
`¬37∣a` case feeds the proven `caseII_realStep6_sigma_of_gammaRatio` + `caseII_realStep6_iff_sigma`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–9.2 (Lemma 9.2, Lemma 9.8
  pp. 178–179).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-- Local shorthand for the structure map `𝓞 K → K` of `K = CyclotomicField 37 ℚ`.  Purely
notational (`notation3`), so terms written with `AM` are the literal `algebraMap` and `simp`/`rw`
match transparently. -/
local notation3 "AM" =>
  algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)

/-! ## 0. `ζ^a` as a `37`-th root, and basic non-membership facts -/

/-- `(zetaPow 37 K a)^37 = 1`: the integer `ζ`-power is a `37`-th root of unity. -/
theorem caseII_zetaPow_pow37 (a : ℤ) :
    (zetaPow 37 (CyclotomicField 37 ℚ) a) ^ 37 = 1 := by
  have hz : (zetaU 37 (CyclotomicField 37 ℚ)) ^ (a * (37 : ℕ)) = 1 := by
    rw [unit'_zpow_congr 37 (CyclotomicField 37 ℚ) (b := 0) ⟨a, by ring⟩, zpow_zero]
  rw [zetaPow, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, hz, Units.val_one]

/-- `zetaPow 37 K a` packaged as an element of `nthRootsFinset 37 1`. -/
def caseII_zetaPowRoot (a : ℤ) : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
  ⟨zetaPow 37 (CyclotomicField 37 ℚ) a,
    (mem_nthRootsFinset (by decide : 0 < 37) (1 : 𝓞 (CyclotomicField 37 ℚ))).mpr
      (caseII_zetaPow_pow37 a)⟩

@[simp] theorem caseII_zetaPowRoot_coe (a : ℤ) :
    (caseII_zetaPowRoot a : 𝓞 (CyclotomicField 37 ℚ)) = zetaPow 37 (CyclotomicField 37 ℚ) a :=
  rfl

/-- `(ζ^a)^36 = ζ^{-a}` (since `36a ≡ -a mod 37`). -/
theorem caseII_zetaPow_pow36 (a : ℤ) :
    (zetaPow 37 (CyclotomicField 37 ℚ) a) ^ 36 = zetaPow 37 (CyclotomicField 37 ℚ) (-a) := by
  rw [zetaPow, zetaPow, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  congr 1
  rw [unit'_zpow_congr 37 (CyclotomicField 37 ℚ) (b := -a) ⟨a, by push_cast; ring⟩]

/-- For `¬37∣a`, `(zetaPowRoot a)^36 = ζ^{-a}` (the inverse root, since `36a ≡ -a mod 37`). -/
theorem caseII_zetaPowRoot_pow36 (a : ℤ) :
    (caseII_zetaPowRoot a : 𝓞 (CyclotomicField 37 ℚ)) ^ 36 =
      zetaPow 37 (CyclotomicField 37 ℚ) (-a) := by
  rw [caseII_zetaPowRoot_coe, caseII_zetaPow_pow36]

/-! ## 1. The element `γ = (D.x + ζ^a·D.y)/(1 - ζ^a)` over `𝓞 K`, for `¬37∣a` -/

variable {m : ℕ}

/-- **`1 - ζ^a` is associate to `ζ - 1`** for `¬37∣a` (so `1 - ζ^a ∣ x + ζ^a·y`).  Both `1` and
`ζ^a` are `37`-th roots and `ζ^a ≠ 1`, so `1 - ζ^a` is associate to `ζ - 1`
(`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`). -/
theorem caseII_one_sub_zetaPow_associated_zeta_sub_one
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ} (ha : ¬ (37 : ℤ) ∣ a) :
    Associated (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) (D.hζ.toInteger - 1) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hzmem : zetaPow 37 (CyclotomicField 37 ℚ) a ∈
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) := (caseII_zetaPowRoot a).2
  have h1mem : (1 : 𝓞 (CyclotomicField 37 ℚ)) ∈
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    one_mem_nthRootsFinset (by decide : 0 < 37)
  have hne : zetaPow 37 (CyclotomicField 37 ℚ) a ≠ (1 : 𝓞 (CyclotomicField 37 ℚ)) := by
    intro hcoe
    apply caseII_one_sub_zetaPow_notMem_lv149 ha
    rw [hcoe, sub_self]; exact lv149.zero_mem
  -- `Set.Pairwise`: `Associated (ζ - 1) (ζ^a - 1)`.
  have hassoc : Associated (D.hζ.toInteger - 1) (zetaPow 37 (CyclotomicField 37 ℚ) a - 1) :=
    D.hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 37) hzmem h1mem hne
  have hneg : Associated (1 - zetaPow 37 (CyclotomicField 37 ℚ) a)
      (zetaPow 37 (CyclotomicField 37 ℚ) a - 1) :=
    ⟨-1, by rw [Units.val_neg, Units.val_one]; ring⟩
  exact hneg.trans hassoc.symm

/-- **`(1 - ζ^a) ∣ (D.x + ζ^a·D.y)` in `𝓞 K`**, for `¬37∣a`.  Since `1 - ζ^a` is associate to
`ζ - 1` (`caseII_one_sub_zetaPow_associated_zeta_sub_one`) and `ζ - 1 ∣ D.x + D.y·ζ^a`
(`caseII_K_zeta_sub_one_dvd_x_add_y_times_root` at the root `ζ^a`). -/
theorem caseII_one_sub_zetaPow_dvd_x_add_zetaPow_y
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ} (ha : ¬ (37 : ℤ) ∣ a) :
    (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) ∣
      D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hdvd : (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      D.x + D.y * (caseII_zetaPowRoot a : 𝓞 (CyclotomicField 37 ℚ)) :=
    caseII_K_zeta_sub_one_dvd_x_add_y_times_root D (by decide : (37 : ℕ) ≠ 2) (caseII_zetaPowRoot a)
  rw [caseII_zetaPowRoot_coe, mul_comm (D.y)] at hdvd
  exact ((caseII_one_sub_zetaPow_associated_zeta_sub_one D ha).dvd).trans hdvd

/-- The Washington-normalized element `γ_a := (D.x + ζ^a·D.y)/(1 - ζ^a) ∈ 𝓞 K` (the chosen witness
of the divisibility), for `¬37∣a`. -/
def caseII_gammaA (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ} (ha : ¬ (37 : ℤ) ∣ a) :
    𝓞 (CyclotomicField 37 ℚ) :=
  (caseII_one_sub_zetaPow_dvd_x_add_zetaPow_y D ha).choose

theorem caseII_gammaA_spec (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ}
    (ha : ¬ (37 : ℤ) ∣ a) :
    D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y =
      (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * caseII_gammaA D ha :=
  (caseII_one_sub_zetaPow_dvd_x_add_zetaPow_y D ha).choose_spec

/-- **`σ(γ_a)` satisfies the conjugate equation**: `D.x + ζ^{-a}·D.y = (1 - ζ^{-a})·σγ_a`.
Apply `σ` (`ringOfIntegersComplexConj`) to `caseII_gammaA_spec` and use `σ(ζ^a) = ζ^{-a}`,
`σ D.x = D.x`, `σ D.y = D.y`. -/
theorem caseII_gammaA_conj_spec (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ}
    (ha : ¬ (37 : ℤ) ∣ a) :
    D.x + zetaPow 37 (CyclotomicField 37 ℚ) (-a) * D.y =
      (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a)) *
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (caseII_gammaA D ha) := by
  have h := congrArg (ringOfIntegersComplexConj (CyclotomicField 37 ℚ)) (caseII_gammaA_spec D ha)
  rw [map_add, map_mul, caseII_complexConj_zetaPow, D.x_real, D.y_real, map_mul, map_sub, map_one,
    caseII_complexConj_zetaPow] at h
  exact h

/-- `γ_a ∉ lv149` for `¬37∣(a-j)` (the factor index), given `D.x + ζ^j·D.y ∈ lv149`, `lv149 ∤ D.y`.
Since `(1-ζ^a)·γ_a = D.x + ζ^a·D.y ∉ lv149` (`caseII_real_x_add_zetaPow_y_notMem`), so
`γ_a ∉ lv149`. -/
theorem caseII_gammaA_notMem (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a j : ℤ}
    (ha : ¬ (37 : ℤ) ∣ a)
    (hfac : D.x + zetaPow 37 (CyclotomicField 37 ℚ) j * D.y ∈ lv149)
    (hy : D.y ∉ lv149) (haj : ¬ (37 : ℤ) ∣ (a - j)) :
    caseII_gammaA D ha ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hmem
  have hβ : D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y ∈ lv149 := by
    rw [caseII_gammaA_spec D ha]
    exact Ideal.mul_mem_left _ _ hmem
  exact caseII_real_x_add_zetaPow_y_notMem D hfac hy haj hβ

/-- `σγ_a ∉ lv149` for `¬37∣(a+j)`.  Since `(1-ζ^{-a})·σγ_a = D.x + ζ^{-a}·D.y ∉ lv149`
(`caseII_real_x_add_zetaPow_y_notMem` at exponent `-a`, needing `¬37∣(-a-j) ⟺ ¬37∣(a+j)`). -/
theorem caseII_gammaA_conj_notMem (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a j : ℤ}
    (ha : ¬ (37 : ℤ) ∣ a)
    (hfac : D.x + zetaPow 37 (CyclotomicField 37 ℚ) j * D.y ∈ lv149)
    (hy : D.y ∉ lv149) (haj' : ¬ (37 : ℤ) ∣ (a + j)) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (caseII_gammaA D ha) ∉ lv149 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hmem
  have hβ : D.x + zetaPow 37 (CyclotomicField 37 ℚ) (-a) * D.y ∈ lv149 := by
    rw [caseII_gammaA_conj_spec D ha]
    exact Ideal.mul_mem_left _ _ hmem
  -- `¬37∣(-a - j)` from `¬37∣(a+j)`.
  have hmaj : ¬ (37 : ℤ) ∣ (-a - j) := by
    intro hd; exact haj' (by rw [show (a + j) = -(-a - j) from by ring]; exact dvd_neg.mpr hd)
  exact caseII_real_x_add_zetaPow_y_notMem D hfac hy hmaj hβ

/-! ## 2. The key field identity: `γ_a/σγ_a = caseII_correctedRadical D ζ^a (correctionUnit ζ^a)`

This identifies the conjugate `γ`-ratio with Washington's **anti-fixed corrected radical** for the
root `η_a = ζ^a`, whose `37`-th-power-ness is the proven Lemma 9.2. -/

/-- The integer identity `(-ζ^{-a})·(1 - ζ^a) = 1 - ζ^{-a}` in `𝓞 K` (from `ζ^a·ζ^{-a} = 1`). -/
theorem caseII_neg_zetaPow_one_sub (a : ℤ) :
    (-(zetaPow 37 (CyclotomicField 37 ℚ) (-a))) * (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) =
      1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a) := by
  have hmul : zetaPow 37 (CyclotomicField 37 ℚ) (-a) * zetaPow 37 (CyclotomicField 37 ℚ) a = 1 := by
    rw [← zetaPow_add, neg_add_cancel]; simp [zetaPow]
  linear_combination hmul

/-- **The key field identity** (`¬37∣a`):
`γ_a / σγ_a = caseII_correctedRadical D (ζ^a-root) (correctionUnit (ζ^a-root))` (in `K`).

Both sides equal `-ζ^{-a}·(D.x + ζ^a y)/(D.x + ζ^{-a} y)`.  Proof: clear denominators against the
integral specs `D.x + ζ^a y = (1-ζ^a)·γ`, `D.x + ζ^{-a} y = (1-ζ^{-a})·σγ`, the root identity
`(ζ^a-root)^36 = ζ^{-a}` (`caseII_zetaPowRoot_pow36`), and `(-ζ^{-a})(1-ζ^a) = 1-ζ^{-a}`. -/
theorem caseII_gammaA_ratio_eq_correctedRadical
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ} (ha : ¬ (37 : ℤ) ∣ a)
    (hγ : caseII_gammaA D ha ∉ lv149)
    (hσγ : ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (caseII_gammaA D ha) ∉ lv149) :
    AM (caseII_gammaA D ha) /
        AM (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (caseII_gammaA D ha)) =
      caseII_correctedRadical D (caseII_zetaPowRoot a)
        (caseII_correctionUnit (caseII_zetaPowRoot a)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set γ := caseII_gammaA D ha
  set σγ := ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ
  have hinj : Function.Injective AM :=
    FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
  have hγ0 : AM γ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; intro h; exact hγ (h ▸ lv149.zero_mem)
  have hσγ0 : AM σγ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; intro h; exact hσγ (h ▸ lv149.zero_mem)
  have hmaj : ¬ (37 : ℤ) ∣ (-a) := fun hd ↦ ha (by simpa using (dvd_neg.mpr hd))
  -- Map the integer specs into `K` (with `D.y * ζ` commuted to `ζ * D.y`).
  have hγK : AM (D.x + D.y * zetaPow 37 (CyclotomicField 37 ℚ) a) =
      AM (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * AM γ := by
    rw [← map_mul,
      show D.x + D.y * zetaPow 37 (CyclotomicField 37 ℚ) a =
        D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y from by ring, caseII_gammaA_spec D ha]
  have hσγK : AM (D.x + D.y * zetaPow 37 (CyclotomicField 37 ℚ) (-a)) =
      AM (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a)) * AM σγ := by
    rw [← map_mul,
      show D.x + D.y * zetaPow 37 (CyclotomicField 37 ℚ) (-a) =
        D.x + zetaPow 37 (CyclotomicField 37 ℚ) (-a) * D.y from by ring,
      caseII_gammaA_conj_spec D ha]
  -- `AM(ζ^a) ≠ 0`, `AM(1-ζ^{-a}) ≠ 0` (needed by `field_simp` to clear denominators).
  have hzeta0 : AM (zetaPow 37 (CyclotomicField 37 ℚ) a) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact zetaPow_ne_zero 37 (CyclotomicField 37 ℚ) a
  have h1ma0 : AM (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; intro h
    exact caseII_one_sub_zetaPow_notMem_lv149 hmaj (h ▸ lv149.zero_mem)
  -- The relation `AM(ζ^a)·AM(1-ζ^{-a}) = -AM(1-ζ^a)` (from `ζ^a·ζ^{-a} = 1`).
  have hDrel : AM (zetaPow 37 (CyclotomicField 37 ℚ) a) *
        AM (1 - zetaPow 37 (CyclotomicField 37 ℚ) (-a)) =
      -AM (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) := by
    rw [← map_mul, ← map_neg]
    congr 1
    have hmul : zetaPow 37 (CyclotomicField 37 ℚ) a *
        zetaPow 37 (CyclotomicField 37 ℚ) (-a) = 1 := by
      rw [← zetaPow_add, add_neg_cancel]; simp [zetaPow]
    linear_combination -hmul
  -- Unfold the corrected radical and root ratio; normalize coes and substitute the specs.
  simp only [caseII_correctedRadical, caseII_rootRatioK, caseII_correctionUnit_val,
    caseII_zetaPowRoot_coe, caseII_zetaPow_pow36, map_neg, hγK, hσγK]
  -- Clear all denominators and finish by the ring identity.
  rw [div_eq_iff hσγ0]
  field_simp
  linear_combination hDrel

/-! ## 3. `γ_a/σγ_a` is a `37`-th power in `K` (Washington Lemma 9.2, via the proven unramifiedness)

`η_a = ζ^a ≠ 1 = D.etaZero` for `¬37∣a`, so the **proven** `CaseIICorrectedRadicalUnramified37`
(`caseII_correctedRadicalUnramified37_of_idealKummer caseIIIdealKummerUnramified37_proven`) gives
the corrected radical's anti-fixed correction unit and unramifiedness;
`flt37_antiFixed_radical_isPthPower` (using `¬37∣h⁺`) then makes it a `37`-th power. -/

/-- `ζ^a ≠ D.etaZero` for `¬37∣a` (since `D.etaZero = 1` and `ζ^a ≠ 1`). -/
theorem caseII_zetaPowRoot_ne_etaZero (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ}
    (ha : ¬ (37 : ℤ) ∣ a) : caseII_zetaPowRoot a ≠ D.etaZero := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro h
  apply caseII_one_sub_zetaPow_notMem_lv149 ha
  have hcoe : zetaPow 37 (CyclotomicField 37 ℚ) a = (D.etaZero : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← caseII_zetaPowRoot_coe a, h]
  rw [hcoe, caseII_etaZero_eq_one D (by decide : (37 : ℕ) ≠ 2), sub_self]
  exact lv149.zero_mem

/-- **The corrected radical `α_a = γ_a/σγ_a` is a `37`-th power in `K`** (`¬37∣a`).

Washington Lemma 9.2: the anti-fixed corrected radical for the root `η_a = ζ^a ≠ η₀`, with the
**canonical** correction unit `caseII_correctionUnit η_a = -η_a`, whose Kummer extension is
unramified (the proven ideal-form Lemma 9.1 `caseIIIdealKummerUnramified37_proven` applied to the
unconditional primarity `caseII_correctedRadical_primary_witness` and ideal-`p`-th-power
`caseII_correctedRadical_fractionalIdeal_eq`), is a `37`-th power in `K`
(`flt37_antiFixed_radical_isPthPower` using `¬37∣h⁺`).  The `α² = 1` (root-of-unity) case is handled
directly. -/
theorem caseII_correctedRadical_zetaPowRoot_isPthPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a : ℤ} (ha : ¬ (37 : ℤ) ∣ a) :
    ∃ β : CyclotomicField 37 ℚ,
      β ^ 37 = caseII_correctedRadical D (caseII_zetaPowRoot a)
        (caseII_correctionUnit (caseII_zetaPowRoot a)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set η := caseII_zetaPowRoot a with hη_def
  have hη_ne : η ≠ D.etaZero := caseII_zetaPowRoot_ne_etaZero D ha
  set α := caseII_correctedRadical D η (caseII_correctionUnit η) with hα_def
  have hα_ne : α ≠ 0 :=
    caseII_correctedRadical_ne_zero D (by decide : (37 : ℕ) ≠ 2) η (caseII_correctionUnit η)
  have hα_anti : NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ) α = α⁻¹ :=
    caseII_correctedRadical_complexConj D (by decide : (37 : ℕ) ≠ 2) η (caseII_correctionUnit η)
      (caseII_correctionUnit_anti η)
  -- The unramifiedness for the canonical corrected radical (proven ideal Lemma 9.1 + the
  -- unconditional primarity / ideal-`p`-th-power of `α`).
  have h_unram : Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
      (𝓞 (FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift (p := 37)
        (CyclotomicField 37 ℚ) α hα_ne)) := by
    obtain ⟨N, c, hc_not_dvd, hc_eq⟩ :=
      caseII_correctedRadical_primary_witness D (by decide : (37 : ℕ) ≠ 2) η hη_ne
    have hideal : FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰ α =
        ((rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η :
            FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ)) /
          (rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy
              (caseII_etaInv η) :
            FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ))) ^ 37 :=
      caseII_correctedRadical_fractionalIdeal_eq D (by decide : (37 : ℕ) ≠ 2) η
    exact caseIIIdealKummerUnramified37_proven α hα_ne
      ⟨D.ζ, D.hζ, N, c, hc_not_dvd, hc_eq⟩ ⟨_, hideal⟩
  rcases eq_or_ne (α ^ 2) 1 with hsq | hsq
  · -- `α = ±1` (37 odd ⟹ `α = α^{37}`); take `β = α`.
    have hpm : α = 1 ∨ α = -1 := by
      have hfac : (α - 1) * (α + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact Or.inl (by linear_combination h1)
      · exact Or.inr (by linear_combination h1)
    refine ⟨α, ?_⟩
    rcases hpm with h1 | h1
    · rw [h1, one_pow]
    · rw [h1]; norm_num
  · -- `α² ≠ 1`: Hilbert 94 (`¬37∣h⁺`) forces `α = β^{37}`.
    exact flt37_antiFixed_radical_isPthPower (K := CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus hα_ne hα_anti hsq h_unram

/-! ## 4. The integral `δ` with `δ^{37} = γ_a·σγ_a^{36}`, and the `37`-th-power residue `v` -/

/-- **The conjugate `γ`-ratio is a `37`-th power mod `lv149`** (`¬37∣a`): there is
`v : 𝓞 K / lv149` with `Q(γ_a)·Q(σγ_a)⁻¹ = v^{37}`.

`γ_a/σγ_a = β^{37}` in `K` (`caseII_gammaA_ratio_eq_correctedRadical` +
`caseII_correctedRadical_zetaPowRoot_isPthPower`); set `δ := β·σγ_a`.  Then
`δ^{37} = γ_a·σγ_a^{36} ∈ 𝓞 K`, so `δ ∈ 𝓞 K` (`𝓞 K` integrally closed), and
`v := Q(δ)·Q(σγ_a)⁻¹` satisfies `v^{37} = Q(γ_a)·Q(σγ_a)⁻¹` (cancelling `Q(σγ_a)^{37}`,
a unit since `σγ_a ∉ lv149`). -/
theorem caseII_gammaA_ratio_isPthPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) {a j : ℤ} (ha : ¬ (37 : ℤ) ∣ a)
    (hfac : D.x + zetaPow 37 (CyclotomicField 37 ℚ) j * D.y ∈ lv149)
    (hy : D.y ∉ lv149) (haj : ¬ (37 : ℤ) ∣ (a - j)) (haj' : ¬ (37 : ℤ) ∣ (a + j)) :
    ∃ v : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149,
      (Ideal.Quotient.mk lv149 (caseII_gammaA D ha)) *
        (Ideal.Quotient.mk lv149
          (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (caseII_gammaA D ha)))⁻¹ = v ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ
  set am := algebraMap (𝓞 K) K with ham
  set γ := caseII_gammaA D ha with hγ_def
  set σγ := ringOfIntegersComplexConj K γ with hσγ_def
  have hinj : Function.Injective am := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hγ : γ ∉ lv149 := caseII_gammaA_notMem D ha hfac hy haj
  have hσγ : σγ ∉ lv149 := caseII_gammaA_conj_notMem D ha hfac hy haj'
  -- `γ/σγ = β^{37}` in `K`.
  obtain ⟨β, hβ⟩ := caseII_correctedRadical_zetaPowRoot_isPthPower D ha
  have hratio : am γ / am σγ = β ^ 37 := by
    rw [caseII_gammaA_ratio_eq_correctedRadical D ha hγ hσγ, ← hβ]
  -- `am σγ ≠ 0`.
  have hσγ0 : am σγ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; intro h; exact hσγ (h ▸ lv149.zero_mem)
  -- `δ_K := β·am σγ` satisfies `δ_K^{37} = am(γ·σγ^{36})`.
  have hδK37 : (β * am σγ) ^ 37 = am (γ * σγ ^ 36) := by
    rw [mul_pow, ← hratio, map_mul, map_pow]
    field_simp
  -- So `δ_K` is integral over `𝓞 K`; pull back to `δ ∈ 𝓞 K`.
  obtain ⟨δ, hδ⟩ : ∃ δ : 𝓞 K, am δ = β * am σγ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := 𝓞 K) (K := K)
      (by decide : 0 < 37) (by rw [hδK37]; exact isIntegral_algebraMap)
  -- `δ^{37} = γ·σγ^{36}` in `𝓞 K`.
  have hδ37 : δ ^ 37 = γ * σγ ^ 36 := by
    apply hinj; rw [map_pow, hδ, hδK37]
  -- Mod `lv149`: `Q(δ)^{37} = Q(γ)·Q(σγ)^{36}`.
  set Q := Ideal.Quotient.mk lv149 with hQ
  have hQσγ0 : Q σγ ≠ 0 := fun h ↦ hσγ ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  refine ⟨Q δ * (Q σγ)⁻¹, ?_⟩
  have hQδ37 : (Q δ) ^ 37 = Q γ * (Q σγ) ^ 36 := by
    rw [← map_pow, hδ37, map_mul, map_pow]
  -- `(Q δ·(Q σγ)⁻¹)^{37} = Q(γ)·Q(σγ)^{36}·(Q σγ)⁻³⁷ = Q(γ)·(Q σγ)⁻¹`.
  rw [mul_pow, hQδ37, inv_pow]
  rw [show (Q σγ) ^ 37 = (Q σγ) ^ 36 * Q σγ from by rw [← pow_succ], mul_inv,
    ← mul_assoc, mul_assoc (Q γ), mul_inv_cancel₀ (pow_ne_zero 36 hQσγ0), mul_one]

/-! ## 5. The corrected residual `CaseIIRealStep6GammaRatioPthPowerNZ37`, fully proven

The corrected form of `CaseIIRealStep6GammaRatioPthPower37` (`CaseIIRealStep6.lean`): the same
statement with the side-condition `¬(37:ℤ)∣a` (Washington's implicit `a ≢ 0 mod p`, so the
denominator `1 - ζ^a` of his `γ_a = (ω + ζ^aθ)/(1 - ζ^a)` is nonzero).  The prior unrestricted form
is **false** at `37∣a` (where `1 - ζ^a = 0` forces `D.x + D.y = 0`); see the module docstring and
`.mathlib-quality/b2_log.jsonl`.  This corrected form is **fully proven** (not a hypothesis). -/

open FLT37.LehmerVandiver.CaseII in
/-- **[FLT37-CASEII-REAL-STEP6-NZ] Washington Lemma 9.8 `ρ_a`-reality, over real data,
fully proven** (`¬37∣a`).

The corrected `CaseIIRealStep6GammaRatioPthPower37` with the side-condition `¬(37:ℤ)∣a`.  For every
real Case-II configuration with a nontrivial conjugate factor `D.x + η·D.y ∈ lv149` (`η = ζ^j ≠ 1`,
`lv149 ∤ D.x, D.y`) and every `a ≢ ±j (mod 37)` with `a ≢ 0 (mod 37)`, the conjugate factor
`β = D.x + ζ^a·D.y` factors as `β = (1 - ζ^a)·γ` (the Washington normalization `γ = γ_a`), with
`γ, σγ ∉ lv149`, and the conjugate ratio is a `37`-th power mod `lv149`: `Q(γ)·Q(σγ)⁻¹ = v^{37}`.

PROVEN, not a hypothesis: `γ_a := (D.x + ζ^a·D.y)/(1 - ζ^a)` (`caseII_gammaA`); `γ/σγ` equals the
**anti-fixed corrected radical** `caseII_correctedRadical D (ζ^a) (correctionUnit (ζ^a))`
(`caseII_gammaA_ratio_eq_correctedRadical`), which by the proven Washington Lemma 9.2 element form
(`flt37_antiFixed_radical_isPthPower` + the proven unramifiedness
`caseIIIdealKummerUnramified37_proven`, using `¬37∣h⁺ = Sinnott.flt37_not_dvd_hPlus`) is a `37`-th
power, whence `v` (`caseII_gammaA_ratio_isPthPower`). -/
theorem caseII_realStep6_gammaRatio_pthPower_nz
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)}
    (_hη_mem : η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (_hη_ne : η ≠ 1)
    (_hx : D.x ∉ lv149) (hy : D.y ∉ lv149)
    (hsum : D.x + η * D.y ∈ lv149)
    (j : ℤ) (hj : zetaPow 37 (CyclotomicField 37 ℚ) j = η)
    (a : ℤ) (haj : ¬ (37 : ℤ) ∣ (a - j)) (haj' : ¬ (37 : ℤ) ∣ (a + j))
    (ha : ¬ (37 : ℤ) ∣ a) :
    ∃ (γ : 𝓞 (CyclotomicField 37 ℚ)),
      D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y =
          (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * γ ∧
        γ ∉ lv149 ∧
        ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ ∉ lv149 ∧
        ∃ (v : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149),
          (Ideal.Quotient.mk lv149 γ) *
              (Ideal.Quotient.mk lv149
                (ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ))⁻¹ = v ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The factor hypothesis in `ζ^j`-form.
  have hfac : D.x + zetaPow 37 (CyclotomicField 37 ℚ) j * D.y ∈ lv149 := by rwa [hj]
  refine ⟨caseII_gammaA D ha, caseII_gammaA_spec D ha,
    caseII_gammaA_notMem D ha hfac hy haj,
    caseII_gammaA_conj_notMem D ha hfac hy haj', ?_⟩
  exact caseII_gammaA_ratio_isPthPower D ha hfac hy haj haj'

/-! ## 6. Washington Lemma 9.8 step 6 `CaseIIMirimanoffStep6CongReal37`, fully proven

The downstream consumer form (`CaseIIRealStep6.lean`): the step-6 cyclic-power congruence
`Q(D.x + ζ^a·D.y)^4 = Q(ζ^a·D.x + D.y)^4` over real data.  Proven by splitting on `37∣a`:
* `37∣a`: `ζ^a = 1`, so `D.x + ζ^a·D.y = D.x + D.y = ζ^a·D.x + D.y` and both sides coincide
  (trivial — this is the configuration where the prior `γ`-ratio residual was false, but step 6
  itself holds trivially);
* `¬37∣a`: the proven corrected residual `caseII_realStep6_gammaRatio_pthPower_nz` gives the
  `γ`-ratio data, from which `caseII_realStep6_sigma_of_gammaRatio` (the proven
  + cyclic-group descent) and `caseII_realStep6_iff_sigma` yield step 6. -/

/-- `zetaPow 37 K a = 1` when `37 ∣ a` (`ζ^a = ζ^0 = 1`). -/
theorem caseII_zetaPow_eq_one_of_dvd {a : ℤ} (ha : (37 : ℤ) ∣ a) :
    zetaPow 37 (CyclotomicField 37 ℚ) a = 1 := by
  rw [zetaPow_congr 37 (CyclotomicField 37 ℚ) (e₂ := 0) (by simpa using ha)]
  simp [zetaPow]

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.8 step 6 over `RealCaseIIData37`, fully proven** (`p = 37`).

Discharges `CaseIIMirimanoffStep6CongReal37` (`CaseIIRealStep6.lean`) — the last analytic
R4 (the irregular-index local power).  The `37∣a` case is trivial; the `¬37∣a` case uses the proven
corrected `γ`-ratio residual `caseII_realStep6_gammaRatio_pthPower_nz`. -/
theorem caseIIMirimanoffStep6CongReal37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)] :
    CaseIIMirimanoffStep6CongReal37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D η hη_mem hη_ne hx hy hsum j hj a haj haj'
  by_cases ha : (37 : ℤ) ∣ a
  · -- `ζ^a = 1`: both step-6 factors equal `D.x + D.y`.
    have hz1 : zetaPow 37 (CyclotomicField 37 ℚ) a = 1 := caseII_zetaPow_eq_one_of_dvd ha
    rw [hz1, one_mul, one_mul]
  · -- `¬37∣a`: the proven corrected `γ`-ratio residual + the σ-bookkeeping.
    obtain ⟨γ, hβ, hγ, hσγ, v, hv⟩ :=
      caseII_realStep6_gammaRatio_pthPower_nz D hη_mem hη_ne hx hy hsum j hj a haj haj' ha
    rw [caseII_realStep6_iff_sigma D a]
    exact caseII_realStep6_sigma_of_gammaRatio D a hγ hσγ hβ hv

end BernoulliRegular.FLT37.Eichler

end
