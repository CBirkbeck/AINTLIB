import BernoulliRegular.FLT37.Eichler.CaseII.Section91.AnchoredClassPrincipal
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.RealGenerator

/-!
# [FLT37-CASEII-REAL-ANCHORED] The anchored class is trivial over `RealCaseIIData37`

This file makes the FLT37 Case-II endpoint **genuinely non-vacuous**.  The prior endpoint
(`CaseIISingleRootDescent.lean`) reduced Case-II II1 to the *anchored class*
`c = [𝔞(η)]·[𝔞(η₀)]⁻¹` being trivial (`CaseIIAdjacentAnchoredClassTrivial37`,
`CaseIIAdjacentAnchoredClassTwoTorsion37`), but those predicates are quantified over the **general**
`CaseIIData37`, where `c` can have full order `37` (the class `c ∈ Cl⁻(𝓞 K)[37]` is genuinely
nonzero for the irregular prime `37`, and `37 ∤ h⁺` alone only gives `c·σc = 1`).

The genuine fix is over `RealCaseIIData37` (the reality-restricted datum `σx = x`, `σy = y`).  There
the **Washington Lemma 9.2** mechanism applies: the anti-fixed radical
`α₀ = (x + yη)/(x + yη⁻¹)` (anti-fixed because `σ(x + yη) = x + yη⁻¹` for real `x, y`) generates,
through its `37`-th power, exactly the root-ideal ratio `(𝔞(η)/𝔞(η⁻¹))^37`.  Under `37 ∤ h⁺`
(proven `Sinnott.flt37_not_dvd_hPlus`) Lemma 9.2 forces `α₀` to be a `37`-th power, which gives
`[𝔞(η)] = [𝔞(η⁻¹)]` (the *conjugate-fixedness of the root class*) — and hence `σc = c`.  Combined
with the **proven** `c·σc = 1` (`caseII_anchored_classGroup_mul_conj_eq_one`) this gives `c² = 1`,
and with the **proven** `c³⁷ = 1` (`caseII_anchored_class_pow_eq_one`), `c = 1`.

The residual is isolated as a single named `def … : Prop` **over real data**:
`CaseIIRootRatioPthPower37` — the integral cross-multiplied form of "`α₀` is a `37`-th power", i.e.
the Lemma 9.2 conclusion.  This is genuinely true over real data (Washington §9.1, Lemma 9.2) and is
the analytic content (the unramifiedness `α₀ ≡ 1 mod (1-ζ)^p`).  Everything else — the reduction
`(𝔞(η)/𝔞(η⁻¹))^37 = (α₀)`, the `p`-th-root extraction giving the class equality, the assembly
`c² = 1 ⟹ c = 1`, and the non-vacuous endpoint — is **proved** here.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1, Lemma 9.2), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-- **[FLT37-CASEII-LEMMA-9.2-RESIDUAL] The anti-fixed radical `α₀ = (x+yη)/(x+yη⁻¹)` is a
`37`-th power in `K`** — the integral cross-multiplied form.

For every **real** Case-II datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` and every adjacent
root `η ≠ η₀`, there exist `a, b ∈ 𝓞 K` (both nonzero) with
`(x + yη)·b^37 = (x + yη⁻¹)·a^37`, i.e. `α₀ = (x+yη)/(x+yη⁻¹) = (a/b)^37` is a `37`-th power.

This is **Washington Lemma 9.2** specialised to the Case-II radical: over real data `α₀` is
anti-fixed (`σα₀ = α₀⁻¹`), and the Kummer extension `K(α₀^{1/37})/K` is unramified
(`α₀ ≡ 1 mod (1-ζ)^{37}`, Lemma 9.1); since `37 ∤ h⁺`
(`Sinnott.flt37_not_dvd_hPlus`) there is no unramified cyclic degree-`37` extension of `K⁺`
(Hilbert 94), so `α₀` must already be a `37`-th power.  This is the genuine analytic content of the
Case-II II1 leaf, isolated as a named hypothesis **over real data** (`def`, not `axiom`).  It is the
SAME Lemma-9.2 mechanism Case-I uses for its anti-Kummer radical `(a+ζb)/(a+ζ⁻¹b)`. -/
def CaseIIRootRatioPthPower37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
    η ≠ D.etaZero →
    ∃ a b : 𝓞 (CyclotomicField 37 ℚ), a ≠ 0 ∧ b ≠ 0 ∧
      (D.x + D.y * (η : 𝓞 (CyclotomicField 37 ℚ))) * b ^ 37 =
        (D.x + D.y * ((η : 𝓞 (CyclotomicField 37 ℚ)) ^ 36)) * a ^ 37

set_option maxRecDepth 4000 in
/-- **`𝔞(η)·(b) = 𝔞(η⁻¹)·(a)` from the `37`-th-power radical identity.**

The integral heart of Lemma 9.2.  Given `(x+yη)·b^37 = (x+yη⁻¹)·a^37` (`α₀ = (a/b)^37`), substitute
the Washington factorisations `𝔪·𝔠(η)·𝔭 = (x+yη)` and `𝔪·𝔠(η⁻¹)·𝔭 = (x+yη⁻¹)`, cancel `𝔪·𝔭`, use
`𝔠(η) = 𝔞(η)^37`, and apply integral `p`-th-root uniqueness to
`(𝔞(η)·(b))^37 = (𝔞(η⁻¹)·(a))^37`. -/
theorem caseII_rootIdeal_mul_span_eq_of_pthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {a b : 𝓞 K} (hab : (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
      (D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η * Ideal.span {b} =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span {a} := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `(x+yη) = 𝔪·𝔠(η)·𝔭` and `(x+yη⁻¹) = 𝔪·𝔠(η⁻¹)·𝔭` (beta-reduced out of the local notation).
  have hkey : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} = Ideal.span {D.x + D.y * (η : 𝓞 K)} :=
    m_mul_c_mul_p hp D.hζ D.equation D.hy η
  have hkeyinv : gcd (Ideal.span {D.x}) (Ideal.span {D.y}) *
        divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} =
      Ideal.span {D.x + D.y * ((η : 𝓞 K) ^ 36)} := by
    have h := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
    rwa [caseII_etaInv_coe] at h
  -- The principal-ideal identity from `hab`, split into a product of spans.
  have hspan :
      Ideal.span ({(D.x + D.y * (η : 𝓞 K))} : Set (𝓞 K)) * Ideal.span {b ^ 37} =
        Ideal.span ({(D.x + D.y * ((η : 𝓞 K) ^ 36))} : Set (𝓞 K)) * Ideal.span {a ^ 37} := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, hab]
  -- `𝔠 = 𝔞^37` at both roots (beta-reduced out of the local notation).
  have hspecη : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η).symm
  have hspecinv : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)).symm
  -- Substitute the Washington factorisations, `𝔠 = 𝔞^37`, and `span{b^37} = span{b}^37`.
  rw [← hkey, ← hkeyinv, hspecη, hspecinv,
    ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow] at hspan
  -- `hspan` now reads `(𝔪 · 𝔞(η)^37 · 𝔭) · (b)^37 = (𝔪 · 𝔞(η⁻¹)^37 · 𝔭) · (a)^37`.
  -- Reshape into `𝔪 · ((𝔞(η)·(b))^37 · 𝔭) = 𝔪 · ((𝔞(η⁻¹)·(a))^37 · 𝔭)` for cancellation.
  set 𝔪 := gcd (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K))) with h𝔪
  set 𝔭 := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭
  set X := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η with hX
  set Y := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) with hY
  have hreshape : 𝔪 * ((X * Ideal.span {b}) ^ 37 * 𝔭) =
      𝔪 * ((Y * Ideal.span {a}) ^ 37 * 𝔭) := by
    rw [mul_pow, mul_pow]
    calc 𝔪 * (X ^ 37 * Ideal.span {b} ^ 37 * 𝔭)
        = 𝔪 * X ^ 37 * 𝔭 * Ideal.span {b} ^ 37 := by ring
      _ = 𝔪 * Y ^ 37 * 𝔭 * Ideal.span {a} ^ 37 := hspan
      _ = 𝔪 * (Y ^ 37 * Ideal.span {a} ^ 37 * 𝔭) := by ring
  -- Cancel `𝔪` (nonzero, left) then `𝔭` (nonzero, right).
  have hmne : 𝔪 ≠ 0 := by rw [h𝔪, Ideal.zero_eq_bot]; exact m_ne_zero D.hζ D.hy
  have hpne : 𝔭 ≠ 0 := by rw [h𝔭, Ideal.zero_eq_bot]; exact p_ne_zero D.hζ
  have hcancel : (X * Ideal.span {b}) ^ 37 = (Y * Ideal.span {a}) ^ 37 :=
    mul_right_cancel₀ hpne (mul_left_cancel₀ hmne hreshape)
  -- `p`-th-root uniqueness on integral ideals: `U^37 = V^37 ⟹ U = V`.
  have hAB := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp
    hcancel.dvd
  have hBA := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp
    hcancel.symm.dvd
  exact le_antisymm (Ideal.dvd_iff_le.mp hBA) (Ideal.dvd_iff_le.mp hAB)

/-- **`[𝔞(η)] = [𝔞(η⁻¹)]` (conjugate-fixedness of the root class) from the `p`-th-power radical.**

This is the Lemma-9.2 output: the radical-`p`-th-power identity
(`caseII_rootIdeal_mul_span_eq_of_pthPower`)
gives `(b)·𝔞(η) = (a)·𝔞(η⁻¹)`, which is exactly the `ClassGroup.mk0_eq_mk0_iff` witness for
`[𝔞(η)] = [𝔞(η⁻¹)]`.  Geometrically: over real data `σ[𝔞(η)] = [𝔞(η⁻¹)]`, so this says `σ` fixes the
root class — the missing conj-fixedness that, with the proven `c·σc = 1`, collapses `c` to `1`. -/
theorem caseII_rootClass_eq_etaInv_of_pthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
      (D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hideal := caseII_rootIdeal_mul_span_eq_of_pthPower D hp η hab
  rw [ClassGroup.mk0_eq_mk0_iff]
  -- `(b)·𝔞(η) = (a)·𝔞(η⁻¹)` from `𝔞(η)·(b) = 𝔞(η⁻¹)·(a)` (commute the span factors).
  refine ⟨b, a, hb, ha, ?_⟩
  rw [mul_comm (Ideal.span {b}), mul_comm (Ideal.span {a})]
  exact hideal

/-- **The anchor root is conjugation-stable: `caseII_etaInv η₀ = η₀`.**

Over real data `σ` fixes the prime `𝔭 = (ζ-1)` and `σ(𝔞(η₀)) = 𝔞(η₀⁻¹)`, so `𝔭 ∣ 𝔞(η₀)`
(`p_dvd_a_iff`, since `η₀ = zetaSubOneDvdRoot`) transports to `𝔭 ∣ 𝔞(η₀⁻¹)` — using `m ≥ 1`
(`CaseIIData37.one_le_m`) via `𝔭^m ∣ 𝔞(η₀⁻¹)` (`caseII_p_pow_dvd_a_caseII_etaInv_etaZero`).  By
uniqueness of the `𝔭`-divisible root (`p_dvd_a_iff` again) `caseII_etaInv η₀ = η₀`.  Hence the
anchor root class is automatically conjugate-fixed (`A(η₀) = A(η₀⁻¹)`), with no Lemma-9.2 input. -/
theorem caseII_etaInv_etaZero_eq {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_etaInv D.etaZero = D.etaZero := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `𝔭 ∣ 𝔞(η₀⁻¹)`: from `𝔭^m ∣ 𝔞(η₀⁻¹)` and `m ≥ 1`.
  have hm : 1 ≤ m := D.toCaseIIData37.one_le_m
  have hpm := caseII_p_pow_dvd_a_caseII_etaInv_etaZero D hp
  have hpdvd : Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) ∣
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero) := by
    refine dvd_trans ?_ hpm
    conv_lhs => rw [← pow_one (Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)))]
    exact pow_dvd_pow _ hm
  -- `𝔭 ∣ 𝔞(ν) ↔ ν = η₀` (the prime `𝔭 = span{ζ-1}` divides the root ideal iff `ν` is the anchor).
  exact (p_dvd_a_iff hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)).mp hpdvd

set_option maxRecDepth 4000 in
/-- **The anchored class squares to `1`: `c² = 1` over `RealCaseIIData37`, from the Lemma-9.2
`p`-th-power radical residual at the adjacent root.**

Let `c = [𝔞(η)]·[𝔞(η₀)]⁻¹` be the anchored class for an adjacent root `η ≠ η₀`.  Combining:

* the **proven** `[𝔞(η)]·[𝔞(η⁻¹)] = [𝔞(η₀)]·[𝔞(η₀⁻¹)]` (`caseII_anchored_mul_conj_mk0_eq`, from
  `c·σc = 1` under `37 ∤ h⁺`),
* `[𝔞(η)] = [𝔞(η⁻¹)]` (`caseII_rootClass_eq_etaInv_of_pthPower`, the Lemma-9.2 output at `η`),
* `caseII_etaInv η₀ = η₀` (`caseII_etaInv_etaZero_eq`, so `[𝔞(η₀⁻¹)] = [𝔞(η₀)]`),

gives `[𝔞(η)]² = [𝔞(η₀)]²`, i.e. `c² = 1`.  The `η₀` class is conjugate-fixed for free; only the
adjacent root needs the genuine Lemma-9.2 `p`-th-power input. -/
theorem caseII_anchored_class_sq_eq_one_of_pthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
      (D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37) :
    (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ *
      (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩)⁻¹) ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Proven: `A·Ainv = A0·A0inv` (the `c·σc = 1` reassembly under Vandiver `37 ∤ h⁺`).
  have hmul := caseII_anchored_mul_conj_mk0_eq D hp h_VC η
  -- Lemma-9.2 output at the adjacent root: `A = Ainv`.
  have hAeq := caseII_rootClass_eq_etaInv_of_pthPower D hp η ha hb hab
  -- The anchor root is conjugate-stable: `[𝔞(η₀⁻¹)] = [𝔞(η₀)]` (since `caseII_etaInv η₀ = η₀`).
  have hroot0 : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
      (caseII_etaInv D.etaZero) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero := by
    rw [caseII_etaInv_etaZero_eq D hp]
  have hclass0 : ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
        (caseII_etaInv D.etaZero),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv D.etaZero))⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩ :=
    congrArg ClassGroup.mk0 (Subtype.ext hroot0)
  -- Rewrite `Ainv → A` and `A0inv → A0` in `hmul` to get `A·A = A0·A0`.
  rw [← hAeq, hclass0] at hmul
  -- Now `hmul : A·A = A0·A0`, i.e. `A² = A0²`.  Hence `(A·A0⁻¹)² = 1`.
  rw [← sq, ← sq] at hmul
  rw [mul_pow, inv_pow, mul_inv_eq_one]
  exact hmul

set_option maxRecDepth 4000 in
/-- **`c = 1`: the anchored class is trivial over `RealCaseIIData37`, from the Lemma-9.2 residual.**

The genuine non-vacuous form.  For the adjacent root `η` the anchored class
`c = [𝔞(η)]·[𝔞(η₀)]⁻¹` is **trivial**.  Combining the **proven** `c³⁷ = 1`
(`caseII_anchored_class_pow_eq_one`) with `c² = 1`
(`caseII_anchored_class_sq_eq_one_of_pthPower`,
the Lemma-9.2 output over real data), the order of `c` divides `gcd(2, 37) = 1`, so `c = 1`, i.e.
`[𝔞(η)] = [𝔞(η₀)]`.  Unlike general-data `CaseIIAdjacentAnchoredClassTwoTorsion37` (where `c` can
have full order `37`), this is genuinely true: over real data `σc = c` (Lemma 9.2) plus the proven
`c·σc = 1` (Vandiver) forces `c = 1`. -/
theorem caseII_anchored_class_eq_one_of_pthPower {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (_hη : η ≠ D.etaZero)
    {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
      (D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hpow37 := caseII_anchored_class_pow_eq_one D.toCaseIIData37 hp η
  have hpow2 := caseII_anchored_class_sq_eq_one_of_pthPower D hp h_VC η ha hb hab
  -- order of `c` divides `gcd(2, 37) = 1`, so `c = 1`.
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow2)
    (orderOf_dvd_of_pow_eq_one hpow37)
  rw [show Nat.gcd 2 37 = 1 by decide] at hdvd
  exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

/-- **[FLT37-CASEII-REAL-PER-DATUM] `[𝔞(η)] = [𝔞(η₀)]` for every real datum and adjacent root.**

The genuine, non-vacuous Case-II II1 statement.  Quantified over all
`D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` and adjacent roots `η ≠ η₀`, the anchored class is
trivial: `[𝔞(η)] = [𝔞(η₀)]` in `Cl(𝓞 K)`.

This follows from the Lemma-9.2 `p`-th-power radical residual `CaseIIRootRatioPthPower37` by
`caseII_anchored_class_eq_one_of_pthPower`; `¬ 37 ∣ h⁺` is supplied internally by the proven
`Sinnott.flt37_not_dvd_hPlus`.  Unlike `CaseIIAdjacentAnchoredClassTrivial37` (over **general**
data, where the class can have full order `37`), this holds genuinely. -/
theorem caseII_real_anchored_class_trivial_of_pthPower
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_radical : CaseIIRootRatioPthPower37)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη : η ≠ D.etaZero) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 (by decide : (37 : ℕ) ≠ 2) η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 (by decide : (37 : ℕ) ≠ 2)
                D.etaZero)⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))))) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr Sinnott.flt37_not_dvd_hPlus
  obtain ⟨a, b, ha, hb, hab⟩ := h_radical D η hη
  exact caseII_anchored_class_eq_one_of_pthPower D (by decide : (37 : ℕ) ≠ 2) h_VC η hη ha hb hab

/- Real-data principalization from the Lemma-9.2 residual.  The class equality `[𝔞(η)] = [𝔞(η₀)]`
over real data feeds the codebase's `CaseIIPrincipalizationAgainstEtaZero` predicate, exactly as
`caseIIPrincipalizationAgainstEtaZero_of_anchoredClassTrivial37` does for general data — only now
the principalization holds **genuinely** (over real data, via Lemma 9.2), not parametrically. -/

/-- **Real-data `η₀`-principalization from the Lemma-9.2 residual.**

For a real datum `D` and the Lemma-9.2 `p`-th-power radical residual `CaseIIRootRatioPthPower37`,
the codebase's `CaseIIPrincipalizationAgainstEtaZero` holds at `D`: each anchored quotient
`𝔞(η)/𝔞₀` (`η ≠ η₀`) is a principal fractional ideal.  Mirrors
`caseIIPrincipalizationAgainstEtaZero_of_anchoredClassTrivial37`, but the class equality is now the
genuinely-true real-data `caseII_real_anchored_class_trivial_of_pthPower` rather than a parametric
predicate. -/
theorem caseII_real_etaZeroPrincipalization_of_pthPower
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_radical : CaseIIRootRatioPthPower37)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro η hη
  -- `D.etaZero = zetaSubOneDvdRoot …`; the class equality `[𝔞(η)] = [𝔞(η₀)]` over real data.
  have hη' : η ≠ D.etaZero := hη
  have h_classEq := caseII_real_anchored_class_trivial_of_pthPower h_radical D η hη'
  -- `[𝔞(η)] = [𝔞(η₀)] ⟹ 𝔞(η)/𝔞(η₀) principal ⟹ 𝔞(η)/𝔞₀ principal`.
  have h_root := caseII_rootQuotientPrincipal_of_classEq D.toCaseIIData37
    (by decide : (37 : ℕ) ≠ 2) η h_classEq
  exact caseII_isPrincipal_aDivAEtaZero_of_rootQuotientPrincipal
    (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η h_root

/- The reality-preserving descent step and the non-vacuous endpoint.

Task (1) above gives, **genuinely** (over real data, from the Lemma-9.2 residual), the
`η₀`-principalization at every real datum.  Together with Assumption II
(`WashingtonCaseIIExactQuotientUnitPower37Source`, the proven descent-unit `37`-th-power) the
single-root Washington descent produces a `CaseIIData37` at `m' < m`.  The one remaining gap to a
fully non-vacuous endpoint is that this constructed datum can be taken **real**
(`RealCaseIIData37`), so the descent iterates and Task (1)'s `c = 1` applies at every level.

This reality-preservation of the *construction* is the genuine remaining residual.  The descent's
new base variables are `x' = a₁b₂·u₁`, `y' = a₂b₁·u₂` (with `u_i` the root-of-unity associate units
`(η_i - 1)/(η₀ - 1)`); they are not real even when `a_i, b_i` are, so reality is not automatic.  We
isolate it as a single named `def … : Prop` **over real data** and assemble everything else. -/

/-- **[FLT37-CASEII-REAL-DESCENT-RESIDUAL] The single-root descent preserves reality.**

For every real Case-II datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m`, given (i) the genuine
`η₀`-principalization at `D` (`CaseIIPrincipalizationAgainstEtaZero`, discharged over real data by
Task (1)'s `caseII_real_etaZeroPrincipalization_of_pthPower`) and (ii) Assumption II
(`WashingtonCaseIIExactQuotientUnitPower37Source`), there is a **real** descent datum at strictly
smaller anchor exponent: `∃ m' < m, Nonempty (RealCaseIIData37 K m')`.

This is the reality-preserving form of `caseII_descent_step_of_singleRootPrincipal`.  The genuine
content beyond the (already-discharged) principalization and the proven Assumption II is exactly the
**reality of the constructed base variables** `x', y'` of the next descent equation — the
norm-form / symmetric-Vandermonde reassembly that recovers a real solution from the real `x, y`
after dividing out the non-real root-of-unity associate twists.  Stated as a named hypothesis
(`def`, not `axiom`), it carries no false content: over real data it is genuinely the content of
Washington §9.1 / Thm 9.4 (the descent runs entirely on real data). -/
def CaseIIRealSingleRootDescentPreservesReality37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  WashingtonCaseIIExactQuotientUnitPower37Source →
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    ∃ m' : ℕ, m' < m ∧ Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m')

/-- **No real Case-II descent datum exists, given the reality-preserving descent step.**

Well-founded minimality on the anchor exponent `m`: pick the minimal `m` with a real datum, then
apply the reality-preserving step (whose principalization input is Task (1)'s real-data result, and
whose unit-power input is Assumption II) to land at `m' < m` — contradicting minimality.  Mirror of
`no_caseIIData37_of_descent_step`, but on `RealCaseIIData37`. -/
theorem no_realCaseIIData37_of_pthPower_and_realDescent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_radical : CaseIIRootRatioPthPower37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (h_realDescent : CaseIIRealSingleRootDescentPreservesReality37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  classical
  rintro ⟨m, D⟩
  let P : ℕ → Prop := fun n ↦ Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) n)
  have hP : ∃ n, P n := ⟨m, D⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨Dmin⟩
  -- Task (1): the genuine `η₀`-principalization holds at the minimal real datum.
  have hprinc := caseII_real_etaZeroPrincipalization_of_pthPower h_radical Dmin
  -- The reality-preserving descent step gives a strictly smaller real datum.
  obtain ⟨m', hm', D'⟩ := h_realDescent h_exactUnit Dmin hprinc
  exact (Nat.find_min hP hm') D'

/-- **The public Case-II bridge from the Lemma-9.2 residual + the reality-preserving descent +
Assumption II.**

`CaseIIBridge 37 K 32` (no Case-II FLT solution) from:

* `h_radical` (`CaseIIRootRatioPthPower37`): the Lemma-9.2 `p`-th-power radical residual over
  **real** data — Task (1)'s genuine, non-vacuous input (replacing the provably-false
  `CaseIIRealIdealDescent37` and the vacuous-prone general-data `CaseIIAdjacentAnchoredClass…37`);
* `h_realDescent` (`CaseIIRealSingleRootDescentPreservesReality37`): the reality-preserving descent
  construction;
* `h_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): Assumption II (proven
  membership-free in the Eichler module).

The integer FLT solution is turned into a **real** datum by the proven producer
`exists_realCaseIIData37_of_caseII_int_solution`, then the no-infinite-descent on real data closes
it.  No part of the chain is vacuous: every step lives over `RealCaseIIData37`, where Task (1)'s
`c = 1` is genuinely true. -/
theorem caseIIBridge_thirtyseven_of_pthPower_and_realDescent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_radical : CaseIIRootRatioPthPower37)
    (h_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  -- No real Case-II descent datum exists (Task (1) + reality-preserving descent + Assumption II).
  have hNoData := no_realCaseIIData37_of_pthPower_and_realDescent
    h_radical h_exactUnit h_realDescent
  -- But the integer Case-II solution produces a real datum (the proven producer).
  exact hNoData
    (exists_realCaseIIData37_of_caseII_int_solution hprod hgcd hcase hEq)

/-- **Fermat's Last Theorem for `37`, from the non-vacuous real-data Case-II II1 input.**

`FermatLastTheoremFor 37` from:

* `caseII_radical` (`CaseIIRootRatioPthPower37`): **Case-II II1**, the Lemma-9.2 `p`-th-power
  radical residual over **real** data.  This is genuinely true (Washington Lemma 9.2: the
  anti-fixed, unramified radical `α₀ = (x+yη)/(x+yη⁻¹)` is a `37`-th power under `37 ∤ h⁺`) and
  **non-vacuous** —
  it forces `c = 1` over real data (`caseII_anchored_class_eq_one_of_pthPower`), unlike the
  vacuous-prone general-data anchored-class predicates;
* `caseII_realDescent` (`CaseIIRealSingleRootDescentPreservesReality37`): the reality-preserving
  single-root descent construction (the only genuine residual beyond Lemma 9.2 + Assumption II);
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): **Case-II II2**, Assumption
  II (proven membership-free in the Eichler module);
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the second-order Bernoulli input.

Case I is discharged unconditionally by the Eichler first-case proof
(`caseIBridge_thirtyseven_eichler`); `¬ 37 ∣ h⁺` is the proven `Sinnott.flt37_not_dvd_hPlus`
(supplied through `cor8_19Bridge_of_not_dvd_hPlus`).  Every Case-II step lives over
`RealCaseIIData37`, entered through the proven real producer
`exists_realCaseIIData37_of_caseII_int_solution`. -/
theorem fermatLastTheoremFor_thirtyseven_of_realAnchoredClass
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_radical : CaseIIRootRatioPthPower37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_pthPower_and_realDescent
      caseII_radical caseII_realDescent caseII_exactUnit)

end BernoulliRegular.FLT37.Eichler

end
