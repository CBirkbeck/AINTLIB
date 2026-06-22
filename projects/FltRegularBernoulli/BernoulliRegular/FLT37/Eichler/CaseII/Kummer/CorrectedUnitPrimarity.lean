import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.KummerUnramifiedToConjFixed

/-!
# [FLT37-CASEII-R1] The finite local `(ζ-1)`-adic primarity congruence (Washington Lemma 9.1)

This file proves **R1** — the reviewer-reclassified *finite local congruence* for the Case-II
anti-Kummer radical primarity.  R1 is **not** a conceptual bottleneck; it is a `(ζ-1)`-adic
congruence read straight off the descent equation (Washington, GTM 83, §9.1, Lemma 9.1).  The
correcting exponent `a` is **forced**: the root index whose `-ζ^a` inverts the raw anti-ratio's
residue.

## The core integer identity

For a real Case-II datum `D : RealCaseIIData37 K m` and a `37`-th root `η` (`η⁻¹ = η^{36}`):

> `(x + yη) - (-η)·(x + yη^{36}) = (x + y)·(1 + η)`     (an **exact** identity in `𝓞 K`).

Verification: `η·(x + yη^{36}) = ηx + yη^{37} = ηx + y`, so the left side is
`(x+yη) + (ηx + y) = (x+y) + η(x+y) = (x+y)(1+η)`.  Since the descent gives
`(ζ-1)^{37m+1} ∣ (x+y)` (`caseII_K_zeta_sub_one_pow_dvd_x_add_y`), the identity yields

> `(ζ-1)^{37m+1} ∣ (x + yη) - (-η)·(x + yη^{36})`,

i.e. the **raw numerator congruence** `x + yη ≡ -η·(x + yη^{36}) (mod (ζ-1)^{37m+1})`.  Dividing
by the denominator `x + yη^{36}` (whose `𝔭`-valuation is exactly `1`,
`caseII_zeta_sub_one_sq_not_dvd_x_add_y_root`) gives the field-level **raw-ratio congruence**

> `R_a = (x+yη)/(x+yη^{36}) ≡ -η (mod (ζ-1)^{37m})`,

hence (multiplying by the unit `-η⁻¹`) the **primarity**

> `-η⁻¹·R_a ≡ 1 (mod (ζ-1)^{37m})`.

For `m ≥ 1` (always, `RealCaseIIData37.one_le_m`) we have `37m ≥ 37`, so both congruences hold
`(mod (ζ-1)^{37})` — the primarity level of Washington Lemma 9.1 (one above `mod 37 = (ζ-1)^{36}`),
which is exactly the depth the **unramified** conclusion needs.

## Valuation bookkeeping (verified)

π = ζ-1; `v_p(π) = 1/36`, `(π)^{36} = (37)` (`associated_zeta_sub_one_pow_prime`).  The raw-ratio
difference `R_a + η` equals `(x+y)(1+η)/(x+yη^{36})`, whose `𝔭`-valuation is
`v_𝔭(x+y) + v_𝔭(1+η) - v_𝔭(x+yη^{36}) ≥ (37m+1) + 0 - 1 = 37m`.  The numerator gains the full
`37m+1` from `(x+y)` (NOT `37m`), and the `v=1` denominator subtracts only `1`, leaving `37m` —
**one power of slack** above the required `37`.  So `m ≥ 1` ⟹ `mod (ζ-1)^{37}` rigorously (no need
for `m ≥ 2`; that `π^{72}` threshold is the *separate* R3/R4 Kummer-lemma issue, not R1).

Everything stays in `π = ζ-1` powers (never the real uniformizer `Λ = (1-ζ)(1-ζ⁻¹) ~ -π²`).

This file imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

variable {m : ℕ} {ζ : K}

/-! ## 1. The exact integer identity and the raw numerator congruence -/

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **The exact anti-ratio numerator identity** in `𝓞 K`:
`(x + yη) - (-η)·(x + yη^{36}) = (x + y)·(1 + η)`.

This is the algebraic heart of Washington Lemma 9.1's congruence: it isolates the difference
between the raw numerator `x+yη` and `-η` times the denominator `x+yη^{36}` as a multiple of the
descent-divisible anchor `x+y`.  Proof: `η·(x + yη^{36}) = ηx + yη^{37} = ηx + y` (using
`η^{37} = 1`), so the left side is `(x+yη) + (ηx + y) = (x+y)(1+η)`. -/
theorem caseII_raw_ratio_numerator_identity (x y : 𝓞 K)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (x + y * (η : 𝓞 K)) - (-(η : 𝓞 K)) * (x + y * (η : 𝓞 K) ^ 36) =
      (x + y) * (1 + (η : 𝓞 K)) := by
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have h37' : (η : 𝓞 K) * (η : 𝓞 K) ^ 36 = 1 := by
    rw [← pow_succ']; exact h37
  linear_combination y * h37'

/-- **The raw numerator congruence** `(ζ-1)^{37m+1} ∣ (x + yη) - (-η)·(x + yη^{36})`.

Immediate from the exact identity `caseII_raw_ratio_numerator_identity` and the descent
divisibility `(ζ-1)^{37m+1} ∣ (x+y)` (`caseII_K_zeta_sub_one_pow_dvd_x_add_y`): the difference is
`(x+y)·(1+η)`, a multiple of `x+y`. -/
theorem caseII_raw_ratio_numerator_congr (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ (37 * m + 1) ∣
      (D.x + D.y * (η : 𝓞 K)) - (-(η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) := by
  rw [caseII_raw_ratio_numerator_identity D.x D.y η]
  exact (caseII_K_zeta_sub_one_pow_dvd_x_add_y D hp).mul_right _

/-! ## 2. Frobenius primarity: `γ ≡ 1 mod (ζ-1)` lifts to `γ^{37} ≡ 1 mod (ζ-1)^{37}`

This is the residue-field normalisation half of Washington Lemma 9.1: a `𝔭`-unit congruent to a
rational (here `1`) mod `(ζ-1)` has its `37`-th power congruent mod `(ζ-1)^{37}`.  The single extra
factor of `37 ~ (ζ-1)^{36}` in the linear binomial term `37·(γ-1)` supplies the full depth. -/

section Frobenius

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K]

/-- `(ζ-1)^{36} ∣ 37` in `𝓞 K` (from `associated_zeta_sub_one_pow_prime`, `p-1 = 36`). -/
theorem caseII_zeta_sub_one_pow36_dvd_p (hζ : IsPrimitiveRoot (ζ : K) 37) :
    (hζ.toInteger - 1 : 𝓞 K) ^ 36 ∣ (37 : 𝓞 K) := by
  simpa using (associated_zeta_sub_one_pow_prime (p := 37) hζ).dvd

/-- **Frobenius primarity lift.** If `(ζ-1) ∣ γ - 1` then `(ζ-1)^{37} ∣ γ^{37} - 1`.

Proof via `Nat.Prime.dvd_add_pow_sub_pow_of_dvd` with `x = γ-1`, `y = 1`, `r = (ζ-1)^{37}`:
`γ^{37} - 1 = ((γ-1)+1)^{37} - 1^{37}`, and the two hypotheses are
`(ζ-1)^{37} ∣ (γ-1)^{37}` (raise `(ζ-1)∣γ-1` to the 37th) and
`(ζ-1)^{37} ∣ 37·(γ-1)` (since `(ζ-1)^{36} ∣ 37` and `(ζ-1) ∣ γ-1`). -/
theorem caseII_gamma_pow37_congr_one (hζ : IsPrimitiveRoot (ζ : K) 37) {γ : 𝓞 K}
    (hγ : (hζ.toInteger - 1 : 𝓞 K) ∣ γ - 1) :
    (hζ.toInteger - 1 : 𝓞 K) ^ 37 ∣ γ ^ 37 - 1 := by
  have h₂ : (hζ.toInteger - 1 : 𝓞 K) ^ 37 ∣ (37 : 𝓞 K) * (γ - 1) := by
    have : (hζ.toInteger - 1 : 𝓞 K) ^ 37 =
        (hζ.toInteger - 1 : 𝓞 K) ^ 36 * (hζ.toInteger - 1 : 𝓞 K) := by rw [← pow_succ]
    rw [this]
    exact mul_dvd_mul (caseII_zeta_sub_one_pow36_dvd_p hζ) hγ
  have key := Nat.Prime.dvd_add_pow_sub_pow_of_dvd (R := 𝓞 K) (p := 37) (x := γ - 1) (y := 1)
    (by decide : Nat.Prime 37) (r := (hζ.toInteger - 1 : 𝓞 K) ^ 37)
    (pow_dvd_pow_of_dvd hγ 37) h₂
  have hsimp : ((γ - 1) + 1) ^ 37 - (1 : 𝓞 K) ^ 37 = γ ^ 37 - 1 := by ring
  rwa [hsimp] at key

end Frobenius

/-! ## 3. The R1 primarity: `(ζ-1)^{37} ∣ u - 1` for the corrected unit form

Given the **integer** corrected unit form `x + yη = (-η)·u·γ^{37}·(x + yη^{36})` (the cleared-
denominator shape of `α_corrected = (-η)⁻¹·R_a = u·γ^{37}`, with Washington's correction
`u₀ = -η = -ζ^a`), a `γ`-residue normalisation `(ζ-1) ∣ γ-1`, and `η ≠ η₀`, the unit `u` is
**primary**: `(ζ-1)^{37} ∣ u - 1`.  This is exactly the `hcong` input that
`flt37_antiKummerLift_isUnramified_of_primaryUnitForm` (flt-regular's `KummersLemma.isUnramified`)
requires.

The proof is the valuation accounting of the file header, carried out entirely with integer
divisibility:

* substitute the exact identity into the unit form to get
  `-η·(x+yη^{36})·(u·γ^{37} - 1) = (x+y)·(1+η)`;
* the RHS is divisible by `(ζ-1)^{37m+1}` (descent), and `-η` is a unit, so
  `(ζ-1)^{37m+1} ∣ (x+yη^{36})·(u·γ^{37} - 1)`;
* `v_𝔭(x+yη^{36}) = 1` exactly (`caseII_zeta_sub_one_sq_not_dvd_x_add_y_root` on `η^{36} ≠ 1`):
  write `x+yη^{36} = (ζ-1)·c`, `¬(ζ-1) ∣ c`; cancel one `(ζ-1)` and apply
  `Prime.pow_dvd_of_dvd_mul_left` to land `(ζ-1)^{37m} ∣ u·γ^{37} - 1`;
* `m ≥ 1` ⟹ `(ζ-1)^{37} ∣ u·γ^{37} - 1`; combine with the Frobenius lift
  `(ζ-1)^{37} ∣ γ^{37} - 1` (so `(ζ-1)^{37} ∣ u·γ^{37} - u`) to get `(ζ-1)^{37} ∣ u - 1`. -/

/-- `caseII_etaInv η ≠ η₀` for `η ≠ η₀` (the inverse-root map fixes only `η₀`). -/
theorem caseII_etaInv_ne_etaZero (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero) :
    caseII_etaInv η ≠ D.etaZero := by
  intro heq
  exact hη (by
    have := congrArg caseII_etaInv heq
    rwa [caseII_etaInv_etaInv, caseII_etaInv_etaZero_eq_etaZero D hp] at this)

/-- **Sharp `(ζ-1)`-factorisation of the denominator** for `η ≠ η₀`:
`x + yη^{36} = (ζ-1)·c` with `¬(ζ-1) ∣ c`, i.e. `v_𝔭(x + yη^{36}) = 1` exactly.  Combines
`(ζ-1) ∣ x + yη^{36}` (`caseII_K_zeta_sub_one_dvd_x_add_y_times_root`) with the sharpness
`(ζ-1)² ∤ x + yη^{36}` (`caseII_zeta_sub_one_sq_not_dvd_x_add_y_root` on `η^{36} = η₀⁻¹ ≠ η₀`). -/
theorem caseII_etaInv_denom_factor (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero) :
    ∃ c : 𝓞 K, D.x + D.y * (η : 𝓞 K) ^ 36 = (D.hζ.toInteger - 1 : 𝓞 K) * c ∧
      ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ c := by
  obtain ⟨c, hc⟩ : (D.hζ.toInteger - 1 : 𝓞 K) ∣ D.x + D.y * (η : 𝓞 K) ^ 36 := by
    have := caseII_K_zeta_sub_one_dvd_x_add_y_times_root D hp (caseII_etaInv η)
    rwa [caseII_etaInv_coe] at this
  refine ⟨c, hc, fun hdvd_c => ?_⟩
  have hsharp := caseII_zeta_sub_one_sq_not_dvd_x_add_y_root D hp (caseII_etaInv η)
    (caseII_etaInv_ne_etaZero D hp η hη)
  rw [caseII_etaInv_coe] at hsharp
  exact hsharp (by rw [hc, sq]; exact mul_dvd_mul_left _ hdvd_c)

theorem caseII_corrected_unit_primary (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero)
    (u γ : (𝓞 K)ˣ) (hγ : (D.hζ.toInteger - 1 : 𝓞 K) ∣ (γ : 𝓞 K) - 1)
    (h_unit_form : D.x + D.y * (η : 𝓞 K) =
      (-(η : 𝓞 K)) * (u : 𝓞 K) * (γ : 𝓞 K) ^ 37 * (D.x + D.y * (η : 𝓞 K) ^ 36)) :
    (D.hζ.toInteger - 1 : 𝓞 K) ^ 37 ∣ (u : 𝓞 K) - 1 := by
  set π : 𝓞 K := (D.hζ.toInteger - 1 : 𝓞 K)
  have hπ_prime : Prime π := D.hζ.zeta_sub_one_prime'
  have hπ_ne : π ≠ 0 := hπ_prime.ne_zero
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have hη_unit : IsUnit (η : 𝓞 K) :=
    IsUnit.of_mul_eq_one ((η : 𝓞 K) ^ 36) (by rw [← pow_succ']; exact h37)
  have h_iso : (-(η : 𝓞 K)) * (D.x + D.y * (η : 𝓞 K) ^ 36) * ((u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - 1) =
      (D.x + D.y) * (1 + (η : 𝓞 K)) := by
    rw [← caseII_raw_ratio_numerator_identity (K := K) D.x D.y η, h_unit_form]; ring
  have hdvd_no_unit : π ^ (37 * m + 1) ∣
      (D.x + D.y * (η : 𝓞 K) ^ 36) * ((u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - 1) := by
    have hdvd_rhs : π ^ (37 * m + 1) ∣
        (-(η : 𝓞 K)) * ((D.x + D.y * (η : 𝓞 K) ^ 36) * ((u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - 1)) := by
      rw [← mul_assoc, h_iso]
      exact (caseII_K_zeta_sub_one_pow_dvd_x_add_y D hp).mul_right _
    exact (IsUnit.dvd_mul_left hη_unit.neg).mp hdvd_rhs
  obtain ⟨c, hc, hπ_not_dvd_c⟩ := caseII_etaInv_denom_factor D hp η hη
  have hdvd_cK : π ^ (37 * m) ∣ c * ((u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - 1) := by
    rw [hc, mul_assoc, pow_succ, mul_comm (π ^ (37 * m)) π] at hdvd_no_unit
    exact (mul_dvd_mul_iff_left hπ_ne).mp hdvd_no_unit
  have hdvd_K : π ^ (37 * m) ∣ (u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - 1 :=
    hπ_prime.pow_dvd_of_dvd_mul_left (37 * m) hπ_not_dvd_c hdvd_cK
  have hdvd_uγ : π ^ 37 ∣ (u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - 1 :=
    (pow_dvd_pow π (Nat.le_mul_of_pos_right 37 D.toCaseIIData37.one_le_m)).trans hdvd_K
  have hγ37 : π ^ 37 ∣ (γ : 𝓞 K) ^ 37 - 1 := caseII_gamma_pow37_congr_one D.hζ hγ
  have hdvd_uγ_minus_u : π ^ 37 ∣ (u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - (u : 𝓞 K) := by
    have : (u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - (u : 𝓞 K) = (u : 𝓞 K) * ((γ : 𝓞 K) ^ 37 - 1) := by ring
    rw [this]; exact hγ37.mul_left _
  have hfinal := dvd_sub hdvd_uγ hdvd_uγ_minus_u
  have hsimp : ((u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - 1) -
      ((u : 𝓞 K) * (γ : 𝓞 K) ^ 37 - (u : 𝓞 K)) = (u : 𝓞 K) - 1 := by ring
  rwa [hsimp] at hfinal

/-! ## 4. The Washington correction unit `u₀ = -η = -ζ^a` and the field unit form

The correction unit is `u₀ := -η` as an element of `(𝓞 K)ˣ` (Washington's `-ζ^a`).  It is
anti-fixed: `σ(-η) = -η⁻¹ = (-η)⁻¹`, exactly the `hu₀` hypothesis of
`CaseIICorrectedRadicalUnramified37`. -/

/-- `η` as a unit of `𝓞 K` (it satisfies `η^{37} = 1`, hence `η·η^{36} = 1`). -/
noncomputable def caseII_rootUnit (η : nthRootsFinset 37 (1 : 𝓞 K)) : (𝓞 K)ˣ where
  val := (η : 𝓞 K)
  inv := (η : 𝓞 K) ^ 36
  val_inv := by
    have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
    rw [← pow_succ']; exact h37
  inv_val := by
    have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
    rw [← pow_succ]; exact h37

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
@[simp] theorem caseII_rootUnit_val (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_rootUnit η : 𝓞 K) = (η : 𝓞 K) := rfl

/-- **The Washington correction unit** `u₀ = -η = -ζ^a`. -/
noncomputable def caseII_correctionUnit (η : nthRootsFinset 37 (1 : 𝓞 K)) : (𝓞 K)ˣ :=
  -caseII_rootUnit η

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
@[simp] theorem caseII_correctionUnit_val (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (caseII_correctionUnit η : 𝓞 K) = -(η : 𝓞 K) := rfl

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- The `𝓞 K`-value of the correction unit's inverse is `-(η^{36})`. -/
theorem caseII_correctionUnit_inv_val (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = -((η : 𝓞 K) ^ 36) := by
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have hmul : (caseII_correctionUnit η : 𝓞 K) * (((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [caseII_correctionUnit_val] at hmul
  have hηη : (-(η : 𝓞 K)) * (-((η : 𝓞 K) ^ 36)) = 1 := by
    rw [neg_mul_neg, ← pow_succ']; exact h37
  have hneg_ne : (-(η : 𝓞 K)) ≠ 0 := by
    have hη_unit : IsUnit (η : 𝓞 K) :=
      IsUnit.of_mul_eq_one ((η : 𝓞 K) ^ 36) (by rw [← pow_succ']; exact h37)
    exact neg_ne_zero.mpr hη_unit.ne_zero
  exact mul_left_cancel₀ hneg_ne (hmul.trans hηη.symm)

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Anti-fixedness of the correction unit** `σ(-η) = (-η)⁻¹`, the `hu₀` input of the residual. -/
theorem caseII_correctionUnit_anti
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (caseII_correctionUnit η : 𝓞 K) =
      (((caseII_correctionUnit η)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  have hση : NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) = (η : 𝓞 K) ^ 36 :=
    caseII_ringOfIntegersComplexConj_root_of_unity h37
  rw [caseII_correctionUnit_val, map_neg, hση, caseII_correctionUnit_inv_val]

/-! ## 5. From the integer unit form to the field unit form, and the R1 discharge

`caseII_correctedRadical_unitForm_of_integer` upgrades the **integer** Washington unit form
`x + yη = (-η)·u·γ^{37}·(x + yη^{36})` to the **field** unit form
`α_corrected = algebraMap u · (algebraMap γ)^{37}` that
`flt37_antiKummerLift_isUnramified_of_primaryUnitForm` consumes (with `u₀ = -η`, the
`caseII_correctionUnit`).  The two are equivalent after dividing by the nonzero denominator
`algebraMap (x + yη^{36})` and undoing the `(algebraMap u₀)⁻¹` correction. -/

/-- **Integer unit form ⟹ field unit form** for the corrected radical with `u₀ = -η`. -/
theorem caseII_correctedRadical_unitForm_of_integer (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K)) (u γ : (𝓞 K)ˣ)
    (h_unit_form : D.x + D.y * (η : 𝓞 K) =
      (-(η : 𝓞 K)) * (u : 𝓞 K) * (γ : 𝓞 K) ^ 37 * (D.x + D.y * (η : 𝓞 K) ^ 36)) :
    caseII_correctedRadical D η (caseII_correctionUnit η) =
      algebraMap (𝓞 K) K (u : 𝓞 K) * (algebraMap (𝓞 K) K (γ : 𝓞 K)) ^ 37 := by
  have hden_ne := caseII_algebraMap_x_add_y_etaInv_ne_zero D hp η
  have hη_ne : algebraMap (𝓞 K) K (η : 𝓞 K) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    exact (caseII_rootUnit η).ne_zero
  have hK := congrArg (algebraMap (𝓞 K) K) h_unit_form
  rw [map_mul, map_mul, map_mul, map_pow, map_neg] at hK
  have hRa : caseII_rootRatioK D η =
      (-algebraMap (𝓞 K) K (η : 𝓞 K)) * algebraMap (𝓞 K) K (u : 𝓞 K) *
        (algebraMap (𝓞 K) K (γ : 𝓞 K)) ^ 37 := by
    rw [caseII_rootRatioK, div_eq_iff hden_ne]
    linear_combination hK
  rw [caseII_correctedRadical, caseII_correctionUnit_val, map_neg, hRa]
  field_simp

/-! ## 6. The R1 discharge of `CaseIICorrectedRadicalUnramified37`

`caseII_correctedRadicalUnramified37_of_R1` discharges the residual
`CaseIICorrectedRadicalUnramified37` from the **reduced** per-datum input

> anti-fixed correction `u₀ = -η` (built here, no longer assumed), and for the corrected radical
> `α = u₀⁻¹·R_a`: the **integer Washington unit form** `x + yη = (-η)·u·γ^{37}·(x + yη^{36})`
> (with `u γ : (𝓞 K)ˣ`), a `γ`-residue normalisation `(ζ-1) ∣ γ-1`, irreducibility of
> `X^{37} - C α`, and `α` not a `37`-th power (`hu_no_root` on `u`).

The **primarity** `hcong : (ζ-1)^{37} ∣ u - 1` — the `hcong` input of
`caseII_correctedRadicalUnramified37_of_primaryData` — is **no longer a hypothesis**; it is
**proved** here by R1 (`caseII_corrected_unit_primary`).  So this discharge is strictly weaker
in its hypotheses than `_of_primaryData`: it eliminates the primarity congruence, which is exactly
R1's job.  The remaining inputs (the integer unit form + non-`37`-th-power + irreducibility) are the
genuinely separate Lemma-9.2 / class-principality content (the unit form being the cleared-
denominator shape of "`(α) = 𝔞(η)^{37}/𝔞(η⁻¹)^{37}` is a `37`-th power of a principal ideal"),
which R1 does not — and is not meant to — supply. -/
theorem caseII_correctedRadicalUnramified37_of_R1
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_data : ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))), η ≠ D.etaZero →
      ∃ (u γ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ (γ : 𝓞 _) - 1 ∧
        D.x + D.y * (η : 𝓞 _) =
          (-(η : 𝓞 _)) * (u : 𝓞 _) * (γ : 𝓞 _) ^ 37 * (D.x + D.y * (η : 𝓞 _) ^ 36) ∧
        Irreducible (Polynomial.X ^ 37 -
          Polynomial.C (caseII_correctedRadical D η (caseII_correctionUnit η)) :
          Polynomial (CyclotomicField 37 ℚ)) ∧
        (∀ v : CyclotomicField 37 ℚ, v ^ 37 ≠ u)) :
    CaseIICorrectedRadicalUnramified37 := by
  intro m D η hη
  obtain ⟨u, γ, hγ, h_unit_form, h_irr, hu_no_root⟩ := h_data D η hη
  refine ⟨caseII_correctionUnit η, caseII_correctionUnit_anti η, ?_⟩
  have hcong : (D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ (u : 𝓞 _) - 1 :=
    caseII_corrected_unit_primary D (by decide : (37 : ℕ) ≠ 2) η hη u γ hγ h_unit_form
  have hUF : caseII_correctedRadical D η (caseII_correctionUnit η) =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (γ : 𝓞 _)) ^ 37 :=
    caseII_correctedRadical_unitForm_of_integer D (by decide : (37 : ℕ) ≠ 2) η u γ h_unit_form
  exact flt37_antiKummerLift_isUnramified_of_primaryUnitForm
    (K := CyclotomicField 37 ℚ)
    (caseII_correctedRadical_ne_zero D (by decide : (37 : ℕ) ≠ 2) η (caseII_correctionUnit η))
    h_irr
    (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (γ : 𝓞 _))
    (by
      rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]; exact γ.ne_zero)
    D.hζ u hUF.symm hcong hu_no_root

end BernoulliRegular.FLT37.Eichler

end
