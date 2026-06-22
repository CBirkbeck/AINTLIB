import BernoulliRegular.FLT37.Eichler.CaseII.Section91.ConjugateFactorEquations
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.RealGenerator
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.B0Principalization
import BernoulliRegular.FLT37.PrimaryUnits.IsPrimaryPlusAndCyclotomicUnits
import BernoulliRegular.UnitQuotient.Washington83UnitForward

/-!
# [FLT37-CASEII-R2] Washington §9.1 product half (`X·X̄ = η'·γ³⁷`, B₀ real-generator argument)

This file **discharges** the named residual `CaseIISection91ProductHalf37`
(`CaseIISection91FactorProducer.lean`) — Washington's B₀-style real-subfield principalization for
the conjugate norm `X·X̄ = N_{K/K⁺}(X)` of the adjacent factor `X = (x+yη)/(1−η)`.

## The mathematics (Washington GTM 83, 2nd ed., §9.1, p. 170–171, "by the same reasoning as B₀")

Write `Num = (x+yη)·(x+yη³⁶)` and `Den = (1−η)·(1−η³⁶)` in `𝓞 K`, so `X·X̄ = algebraMap Num /
algebraMap Den`.  As **integral ideals** of `𝓞 K`:

* `span{x+yη} = 𝔪·𝔠(η)·𝔭` and `span{x+yη³⁶} = 𝔪·𝔠(η⁻¹)·𝔭` (`m_mul_c_mul_p`), with
  `𝔠(η) = 𝔞(η)³⁷` (`root_div_zeta_sub_one_dvd_gcd_spec`).  Coprimality `IsCoprime ((x)) ((y))` makes
  `𝔪 = gcd((x),(y)) = ⊤` (`isCoprime_iff_gcd`), so `span{x+yη} = 𝔭·𝔞(η)³⁷`.
* `span{1−η} = 𝔭` and `span{1−η³⁶} = 𝔭` (`caseII_root_sub_one_associated`: `1−η ~ ζ−1`).

Hence `span{Num} = 𝔭²·(𝔞(η)·𝔞(η³⁶))³⁷ = C³⁷·span{Den}` with `C = 𝔞(η)·𝔞(η³⁶)` (the σ-fixed,
`𝔭`-coprime conjugate-paired root product).  Both `span{Num}`, `span{Den}` are **principal**, so in
`Cl(𝓞 K)` the class of `C³⁷` is trivial: `[C³⁷] = [span{Num}]·[span{Den}]⁻¹ = 1`.

`C` **descends** from `𝓞 K⁺` (`caseII_sigma_stable_ideal_descends`: `C = J.map _`, valid for
`η, η³⁶ ≠ η₀`, σ-stable + `𝔭`-coprime ⟹ unramified-support descent).  With `(J.map)³⁷ = C³⁷`
principal and `¬ 37 ∣ h⁺` (`Sinnott.flt37_not_dvd_hPlus`),
`map_isPrincipal_of_pow_principal_of_not_dvd_hPlus` forces `C = J.map _` **principal with a real
generator** `γ₀ = algebraMap (𝓞 K⁺) (𝓞 K) a`.  Then `(γ₀³⁷) = C³⁷` and
`span{Num} = (γ₀³⁷)·span{Den}`, so `Num`, `γ₀³⁷·Den` are associates: `Num = u·γ₀³⁷·Den`
(`u : (𝓞 K)ˣ`).  Cancelling `Den`,
`X·X̄ = (algebraMap u)·(algebraMap γ₀)³⁷ = η'·γ³⁷`.  `X·X̄` is a **norm** hence real
(`caseII_section91_product_real`) and `γ = algebraMap γ₀` is real
(`ringOfIntegersComplexConj_algebraMap_eq`), so `η' = (X·X̄)/γ³⁷` is **real** — exactly the
product-half conclusion.

## What this file proves (real, axiom-clean Lean — no `sorry`, no `axiom`)

* `caseIISection91ProductHalf37_proven : CaseIISection91ProductHalf37` — the named residual, fully
  discharged.  This removes the only non-proven input of `caseII_section91_factorEquations`
  (`CaseIISection91FactorProducer.lean`), so the §9.1 factor equations become unconditional given
  the proven quotient half.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 169–171 (the squared
  form; the B₀ real-generator argument for the conjugate norm).
* Diekmann (2023), Proposition 55 (`classGroupMap_injective`, underlying the K⁺-principalization).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The integral ideal identity `span{Num} = C³⁷ · span{Den}` -/

/-- **`span{1 − η} = 𝔭`** (`= span{ζ − 1}`) for an adjacent root `η ≠ η₀ = 1`.
From `Associated (η − 1) (ζ − 1)` (`caseII_root_sub_one_associated`), `1 − η ~ −(η−1) ~ ζ−1`. -/
theorem caseII_productHalf_span_one_sub_eta
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero) :
    Ideal.span ({1 - (η : 𝓞 (CyclotomicField 37 ℚ))} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} :
        Set (𝓞 (CyclotomicField 37 ℚ))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hη1 : (η : 𝓞 (CyclotomicField 37 ℚ)) ≠ 1 := caseII_section91_eta_ne_one D η hη
  rw [Ideal.span_singleton_eq_span_singleton]
  -- `1 - η = (-1)·(η - 1)`, and `Associated (η - 1) (ζ - 1)`.
  have hassoc : Associated ((η : 𝓞 (CyclotomicField 37 ℚ)) - 1)
      (D.hζ.toInteger - 1) := caseII_root_sub_one_associated D η hη1
  -- `Associated (1 - η) (η - 1)` via the unit `-1` (`(1-η)·(-1) = η-1`), then chain.
  have hneg : Associated ((1 : 𝓞 (CyclotomicField 37 ℚ)) - (η : 𝓞 _))
      ((η : 𝓞 (CyclotomicField 37 ℚ)) - 1) :=
    ⟨-1, by rw [Units.val_neg, Units.val_one]; ring⟩
  exact hneg.trans hassoc

set_option maxRecDepth 4000 in
/-- **The integral ideal identity** `span{x+yη}·span{x+yη³⁶} = (𝔞(η)·𝔞(η³⁶))³⁷ · (span{1−η}·
span{1−η³⁶})` for an adjacent root `η ≠ η₀`, given the coprimality `𝔪 = gcd((x),(y)) = ⊤`.

This is Washington's `(Num) = C³⁷·(Den)` (ideals).  Proof: `span{x+yη} = 𝔪·𝔠(η)·𝔭 = 𝔭·𝔞(η)³⁷`
(`m_mul_c_mul_p` + `root_div_zeta_sub_one_dvd_gcd_spec` + `𝔪 = ⊤`); same for `η³⁶`; `span{1−η} = 𝔭`
(`caseII_productHalf_span_one_sub_eta`); regroup. -/
theorem caseII_productHalf_ideal_identity
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    Ideal.span ({D.x + D.y * (η : 𝓞 _)} : Set (𝓞 (CyclotomicField 37 ℚ))) *
        Ideal.span ({D.x + D.y * ((η : 𝓞 _) ^ 36)} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy
            (caseII_etaInv η)) ^ 37 *
        (Ideal.span ({1 - (η : 𝓞 _)} : Set (𝓞 (CyclotomicField 37 ℚ))) *
          Ideal.span ({1 - (η : 𝓞 _) ^ 36} : Set (𝓞 (CyclotomicField 37 ℚ)))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `𝔪 = gcd((x),(y)) = ⊤`.
  have hm_top : gcd (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) = 1 :=
    Ideal.isCoprime_iff_gcd.mp hcop
  -- `span{x+yη} = 𝔪·𝔠(η)·𝔭 = 𝔠(η)·𝔭` (using `𝔪 = ⊤`).
  have hspan_eta : Ideal.span ({D.x + D.y * (η : 𝓞 _)} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} :
          Set (𝓞 (CyclotomicField 37 ℚ))) := by
    have h := m_mul_c_mul_p hp D.hζ D.equation D.hy η
    rw [hm_top, one_mul] at h
    exact h.symm
  have hspan_etaInv : Ideal.span ({D.x + D.y * ((η : 𝓞 _) ^ 36)} :
        Set (𝓞 (CyclotomicField 37 ℚ))) =
      divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} :
          Set (𝓞 (CyclotomicField 37 ℚ))) := by
    have h := m_mul_c_mul_p hp D.hζ D.equation D.hy (caseII_etaInv η)
    rw [hm_top, one_mul, caseII_etaInv_coe] at h
    exact h.symm
  -- `𝔠(η) = 𝔞(η)³⁷`.
  have hc_eta : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy η =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy η).symm
  have hc_etaInv : divZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ^ 37 :=
    (root_div_zeta_sub_one_dvd_gcd_spec hp D.hζ D.equation D.hy (caseII_etaInv η)).symm
  -- `span{1−η} = 𝔭`, `span{1−η³⁶} = 𝔭`.
  have hden_eta : Ideal.span ({1 - (η : 𝓞 _)} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} :
        Set (𝓞 (CyclotomicField 37 ℚ))) :=
    caseII_productHalf_span_one_sub_eta D η hη
  have hden_etaInv : Ideal.span ({1 - (η : 𝓞 _) ^ 36} : Set (𝓞 (CyclotomicField 37 ℚ))) =
      Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} :
        Set (𝓞 (CyclotomicField 37 ℚ))) :=
    caseII_productHalf_span_one_sub_eta D (caseII_etaInv η) (caseII_etaInv_ne_etaZero D hp η hη)
  -- Assemble: rewrite both sides, then abbreviate the heavy ideals before the monoid rearrange.
  rw [hspan_eta, hspan_etaInv, hc_eta, hc_etaInv, hden_eta, hden_etaInv, mul_pow]
  set A := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ^ 37 with hA_def
  set B := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ^ 37 with hB_def
  set P := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ))} :
    Set (𝓞 (CyclotomicField 37 ℚ))) with hP_def
  -- Goal: `(A·P)·(B·P) = (A·B)·(P·P)`.
  exact mul_mul_mul_comm A P B P

/-! ## 2. Class-group triviality of `C³⁷`: `C³⁷` is principal -/

/-- **`C = 𝔞(η)·𝔞(η³⁶) ≠ ⊥`** (both root-ideal factors are nonzero). -/
theorem caseII_productHalf_C_ne_bot
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact mul_ne_zero
    (caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)
    (caseII_rootIdeal_ne_bot D.toCaseIIData37 hp (caseII_etaInv η))

set_option maxRecDepth 4000 in
/-- **`C³⁷` is principal** (Washington's `[C³⁷] = 1`).

From the integral ideal identity `span{Num} = C³⁷·span{Den}` (`caseII_productHalf_ideal_identity`),
with both `span{Num} = span{x+yη}·span{x+yη³⁶}` and `span{Den} = span{1−η}·span{1−η³⁶}` principal,
the class of `C³⁷` is trivial in `Cl(𝓞 K)`: `mk0(C³⁷)·mk0(span{Den}) = mk0(span{Num}) = 1` and
`mk0(span{Den}) = 1`, so `mk0(C³⁷) = 1`, i.e. `C³⁷` is principal. -/
theorem caseII_productHalf_C_pow_isPrincipal
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37).IsPrincipal
      := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set C := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) with hC_def
  set Den := Ideal.span ({1 - (η : 𝓞 _)} : Set (𝓞 (CyclotomicField 37 ℚ))) *
    Ideal.span ({1 - (η : 𝓞 _) ^ 36} : Set (𝓞 (CyclotomicField 37 ℚ))) with hDen_def
  set Num := Ideal.span ({D.x + D.y * (η : 𝓞 _)} : Set (𝓞 (CyclotomicField 37 ℚ))) *
    Ideal.span ({D.x + D.y * ((η : 𝓞 _) ^ 36)} : Set (𝓞 (CyclotomicField 37 ℚ))) with hNum_def
  -- The integral identity `Num = C³⁷·Den`.
  have hid : Num = C ^ 37 * Den :=
    caseII_productHalf_ideal_identity D hp η hη hcop
  -- Nonzero facts.
  have hC_ne : C ≠ ⊥ := caseII_productHalf_C_ne_bot D hp η
  have hCpow_ne : C ^ 37 ≠ ⊥ := pow_ne_zero 37 hC_ne
  have hDen_ne : Den ≠ ⊥ := by
    rw [hDen_def, Ne, Ideal.mul_eq_bot]
    push Not
    constructor
    · rw [Ne, Ideal.span_singleton_eq_bot]
      have hη1 : (η : 𝓞 (CyclotomicField 37 ℚ)) ≠ 1 := caseII_section91_eta_ne_one D η hη
      intro h0; exact hη1 (by linear_combination -h0)
    · rw [Ne, Ideal.span_singleton_eq_bot]
      have hη36 : (η : 𝓞 (CyclotomicField 37 ℚ)) ^ 36 ≠ 1 := by
        have hη1 := caseII_section91_eta_ne_one D (caseII_etaInv η)
          (caseII_etaInv_ne_etaZero D hp η hη)
        rw [caseII_etaInv_coe] at hη1; exact hη1
      intro h0; exact hη36 (by linear_combination -h0)
  have hNum_ne : Num ≠ ⊥ := by rw [hid]; exact mul_ne_zero hCpow_ne hDen_ne
  -- `mk0(Num) = mk0(C³⁷)·mk0(Den)`.
  have hmk_mul : ClassGroup.mk0 ⟨Num, mem_nonZeroDivisors_iff_ne_zero.mpr hNum_ne⟩ =
      ClassGroup.mk0 ⟨C ^ 37, mem_nonZeroDivisors_iff_ne_zero.mpr hCpow_ne⟩ *
        ClassGroup.mk0 ⟨Den, mem_nonZeroDivisors_iff_ne_zero.mpr hDen_ne⟩ := by
    rw [← map_mul]
    exact congrArg ClassGroup.mk0 (Subtype.ext hid)
  -- `mk0(Num) = 1` and `mk0(Den) = 1` (both principal).
  have hNum_one : ClassGroup.mk0 ⟨Num, mem_nonZeroDivisors_iff_ne_zero.mpr hNum_ne⟩ = 1 := by
    rw [ClassGroup.mk0_eq_one_iff, hNum_def, Ideal.span_singleton_mul_span_singleton]
    exact ⟨⟨_, rfl⟩⟩
  have hDen_one : ClassGroup.mk0 ⟨Den, mem_nonZeroDivisors_iff_ne_zero.mpr hDen_ne⟩ = 1 := by
    rw [ClassGroup.mk0_eq_one_iff, hDen_def, Ideal.span_singleton_mul_span_singleton]
    exact ⟨⟨_, rfl⟩⟩
  -- ⟹ `mk0(C³⁷) = 1`.
  have hCpow_one : ClassGroup.mk0 ⟨C ^ 37, mem_nonZeroDivisors_iff_ne_zero.mpr hCpow_ne⟩ = 1 := by
    have := hmk_mul
    rw [hNum_one, hDen_one, mul_one] at this
    exact this.symm
  rwa [ClassGroup.mk0_eq_one_iff] at hCpow_one

/-! ## 3. K⁺-principalization with a real generator (the B₀ argument) -/

set_option maxRecDepth 4000 in
/-- **A real ideal `J ⊆ 𝓞 K⁺` whose `37`-th power maps to a principal ideal of `𝓞 K` is itself
principal** (Diekmann Prop 55 + `¬ 37 ∣ h⁺`).

From `(J.map _)^37 = (J^37).map _` principal we get `J^37` principal in `𝓞 K⁺`
(`isPrincipal_of_isPrincipal_map_Kplus`), so `[J]^37 = 1` in `Cl(𝓞 K⁺)`; with `¬ 37 ∣ h⁺`
(`Sinnott.flt37_not_dvd_hPlus`) and `class_eq_one_of_pow_eq_one_of_not_dvd_hPlus`, `[J] = 1`, hence
`J` is principal.  (This is the `J`-level half of
`map_isPrincipal_of_pow_principal_of_not_dvd_hPlus`, kept so the generator can be exhibited in
`𝓞 K⁺` and pushed to a *real* generator of `J.map _`.) -/
theorem caseII_productHalf_J_isPrincipal
    {J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))} (hJ_ne : J ≠ ⊥)
    (hJ_pow : ((J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ)))) ^ 37).IsPrincipal) :
    J.IsPrincipal := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp_odd : (37 : ℕ) ≠ 2 := by decide
  -- `(J.map _)^37 = (J^37).map _`.
  rw [show ((J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
      (𝓞 (CyclotomicField 37 ℚ)))) ^ 37) =
      (J ^ 37).map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))) from
    (Ideal.map_pow _ J 37).symm] at hJ_pow
  -- `J^37` principal in `𝓞 K⁺`.
  have hJp_principal : (J ^ 37).IsPrincipal :=
    isPrincipal_of_isPrincipal_map_Kplus (p := 37) (hp_odd := hp_odd)
      (K := CyclotomicField 37 ℚ) (J ^ 37) hJ_pow
  -- Translate to the class group.
  have hJp_ne : J ^ 37 ≠ ⊥ := pow_ne_zero 37 hJ_ne
  have hJ_ne0 : J ∈ (Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne
  have hJp_ne0 : J ^ 37 ∈ (Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJp_ne
  have hJpow_class : (ClassGroup.mk0 ⟨J, hJ_ne0⟩) ^ 37 = 1 := by
    have hsub : ClassGroup.mk0 ⟨J ^ 37, hJp_ne0⟩ = (ClassGroup.mk0 ⟨J, hJ_ne0⟩) ^ 37 := by
      rw [← map_pow]; rfl
    rw [← hsub]
    exact (ClassGroup.mk0_eq_one_iff hJp_ne0).mpr hJp_principal
  have hJ_class : ClassGroup.mk0 ⟨J, hJ_ne0⟩ = 1 :=
    class_eq_one_of_pow_eq_one_of_not_dvd_hPlus (p := 37) (K := CyclotomicField 37 ℚ) hp_odd
      Sinnott.flt37_not_dvd_hPlus _ hJpow_class
  exact (ClassGroup.mk0_eq_one_iff hJ_ne0).mp hJ_class

/-- **The σ-fixed conjugate-paired product `C = 𝔞(η)·𝔞(η³⁶)` has a real generator** (Wash. B₀).

For an adjacent root `η ≠ η₀` with coprimality `IsCoprime ((x)) ((y))`, the σ-fixed `𝔭`-coprime
ideal `C = 𝔞(η)·𝔞(η³⁶)` descends from `𝓞 K⁺` (`caseII_sigma_stable_ideal_descends`, valid since
`η, η³⁶ ≠ η₀`), and `C³⁷` is principal (`caseII_productHalf_C_pow_isPrincipal`).  By
`caseII_productHalf_J_isPrincipal` the descent `J` is principal, `J = span{a}` (`a ∈ 𝓞 K⁺`), so
`C = J.map _ = span{algebraMap a}` with `algebraMap a` **real**
(`ringOfIntegersComplexConj_algebraMap_eq`).  Output: a real `γ₀ ∈ 𝓞 K` with `span{γ₀} = C`. -/
theorem caseII_productHalf_C_real_generator
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ γ₀ : 𝓞 (CyclotomicField 37 ℚ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ₀ = γ₀ ∧
      Ideal.span ({γ₀} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set C := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) with hC_def
  -- `C` descends: `J.map _ = C`.
  obtain ⟨J, hJ⟩ := caseII_sigma_stable_ideal_descends D hp η hη
    (caseII_etaInv_ne_etaZero D hp η hη)
  -- `J ≠ ⊥` (else `J.map = ⊥ = C`, but `C ≠ ⊥`).
  have hC_ne : C ≠ ⊥ := caseII_productHalf_C_ne_bot D hp η
  have hJ_ne : J ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.map_bot] at hJ
    exact hC_ne hJ.symm
  -- `(J.map _)^37 = C^37` principal.
  have hJpow_principal : ((J.map (algebraMap
      (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
      (𝓞 (CyclotomicField 37 ℚ)))) ^ 37).IsPrincipal := by
    rw [hJ]
    exact caseII_productHalf_C_pow_isPrincipal D hp η hη hcop
  -- `J` principal.
  have hJ_principal : J.IsPrincipal := caseII_productHalf_J_isPrincipal hJ_ne hJpow_principal
  obtain ⟨a, ha⟩ := hJ_principal
  have ha' : J = Ideal.span ({a} : Set _) := ha
  -- `J.map _ = span{algebraMap a}`.
  have hmap_span : J.map (algebraMap
      (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
      (𝓞 (CyclotomicField 37 ℚ))) =
      Ideal.span ({algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ)) a} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
    rw [ha', Ideal.map_span, Set.image_singleton]
  -- `C = J.map _ = span{algebraMap a}`.
  refine ⟨algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
    (𝓞 (CyclotomicField 37 ℚ)) a, ?_, ?_⟩
  · -- reality of `algebraMap a`.
    exact ringOfIntegersComplexConj_algebraMap_eq (K := CyclotomicField 37 ℚ) a
  · -- `span{algebraMap a} = J.map _ = C`.
    rw [← hmap_span, hJ]

/-! ## 4. The field equation `X·X̄ = (algebraMap u)·γ³⁷` and the product half -/

set_option maxRecDepth 4000 in
/-- **The field equation `X·X̄ = (algebraMap u)·(algebraMap γ₀)³⁷`** for a unit `u : (𝓞 K)ˣ` and the
real generator `γ₀` of `C = 𝔞(η)·𝔞(η³⁶)`.

From `span{γ₀} = C` (`caseII_productHalf_C_real_generator`) and the integral identity
`span{(x+yη)(x+yη³⁶)} = C³⁷·span{(1−η)(1−η³⁶)}` (`caseII_productHalf_ideal_identity`),
`span{(x+yη)(x+yη³⁶)} = span{γ₀³⁷·(1−η)(1−η³⁶)}`, so `Associated (γ₀³⁷·Den) Num` gives a unit `u`
with `γ₀³⁷·Den·u = Num` (`Num = (x+yη)(x+yη³⁶)`, `Den = (1−η)(1−η³⁶)`).  Mapping to `K` and
cancelling `algebraMap Den ≠ 0` yields `X·X̄ = (algebraMap u)·(algebraMap γ₀)³⁷`. -/
theorem caseII_productHalf_field_eq
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (u : (𝓞 (CyclotomicField 37 ℚ))ˣ) (γ₀ : 𝓞 (CyclotomicField 37 ℚ)),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) γ₀ = γ₀ ∧
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y * (η : 𝓞 _)) /
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _))) *
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (D.x + D.y * ((η : 𝓞 _) ^ 36)) /
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (1 - (η : 𝓞 _) ^ 36)) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) γ₀ ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ with hK
  -- The real generator `γ₀` of `C`.
  obtain ⟨γ₀, hγ₀_real, hγ₀_span⟩ := caseII_productHalf_C_real_generator D hp η hη hcop
  -- The integral identity, with `C³⁷ = span{γ₀}³⁷ = span{γ₀³⁷}`.
  have hid := caseII_productHalf_ideal_identity D hp η hη hcop
  -- Fold the spans into single-element spans.
  have hNum_span : Ideal.span ({D.x + D.y * (η : 𝓞 K)} : Set (𝓞 K)) *
        Ideal.span ({D.x + D.y * ((η : 𝓞 K) ^ 36)} : Set (𝓞 K)) =
      Ideal.span ({(D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * ((η : 𝓞 K) ^ 36))} : Set (𝓞 K)) :=
    Ideal.span_singleton_mul_span_singleton _ _
  have hDen_span : Ideal.span ({1 - (η : 𝓞 K)} : Set (𝓞 K)) *
        Ideal.span ({1 - (η : 𝓞 K) ^ 36} : Set (𝓞 K)) =
      Ideal.span ({(1 - (η : 𝓞 K)) * (1 - (η : 𝓞 K) ^ 36)} : Set (𝓞 K)) :=
    Ideal.span_singleton_mul_span_singleton _ _
  have hCpow_span : (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) ^ 37 =
      Ideal.span ({γ₀ ^ 37} : Set (𝓞 K)) := by
    rw [← hγ₀_span, Ideal.span_singleton_pow]
  -- `span{Num} = span{γ₀³⁷·Den}`.
  rw [hNum_span, hCpow_span, hDen_span, Ideal.span_singleton_mul_span_singleton] at hid
  -- `Associated (γ₀³⁷·Den) Num`, so `∃ u, γ₀³⁷·Den·u = Num`.
  have hassoc : Associated ((γ₀ ^ 37) * ((1 - (η : 𝓞 K)) * (1 - (η : 𝓞 K) ^ 36)))
      ((D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * ((η : 𝓞 K) ^ 36))) := by
    rw [← Ideal.span_singleton_eq_span_singleton]
    exact hid.symm
  obtain ⟨u, hu⟩ := hassoc
  refine ⟨u, γ₀, hγ₀_real, ?_⟩
  -- Field algebra: `X·X̄ = algebraMap(Num)/algebraMap(Den) = algebraMap(u)·algebraMap(γ₀)³⁷`.
  have hDen_ne : algebraMap (𝓞 K) K ((1 - (η : 𝓞 K)) * (1 - (η : 𝓞 K) ^ 36)) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero (caseII_section91_one_sub_eta_ne_zero D η hη)
      (caseII_section91_one_sub_etaPow_ne_zero D η hη)
  -- `Num = γ₀³⁷·Den·u` (from `hu : γ₀³⁷·Den·u = Num`), pushed to `K`.
  have hNumK : algebraMap (𝓞 K) K ((D.x + D.y * (η : 𝓞 K)) * (D.x + D.y * ((η : 𝓞 K) ^ 36))) =
      algebraMap (𝓞 K) K (u : 𝓞 K) * algebraMap (𝓞 K) K γ₀ ^ 37 *
        algebraMap (𝓞 K) K ((1 - (η : 𝓞 K)) * (1 - (η : 𝓞 K) ^ 36)) := by
    rw [← hu]
    push_cast [map_mul, map_pow]
    ring
  -- Assemble the quotient form: combine to `algebraMap(Num)/algebraMap(Den)`, substitute, cancel.
  rw [div_mul_div_comm, ← map_mul, ← map_mul, hNumK, mul_div_assoc, div_self hDen_ne, mul_one]

/-! ## 5. The product half, fully discharged -/

set_option maxRecDepth 4000 in
/-- **[PRODUCT HALF — PROVEN] Washington's B₀ argument `X·X̄ = η'·γ³⁷` with `η'` a real unit.**

The named residual `CaseIISection91ProductHalf37` (`CaseIISection91FactorProducer.lean`), fully
discharged.  From the field equation `X·X̄ = (algebraMap u)·(algebraMap γ₀)³⁷`
(`caseII_productHalf_field_eq`, `u : (𝓞 K)ˣ`, `γ₀` real) set `η' = Units.map algebraMap u` (so
`(η' : K) = algebraMap u`) and `γ = algebraMap γ₀`.  `η'` is **real**: `X·X̄` is a norm hence real
(`caseII_section91_product_real`) and `γ³⁷ = (algebraMap γ₀)³⁷` is real (`γ₀` real,
`coe_ringOfIntegersComplexConj`), so `(η' : K) = (X·X̄)/γ³⁷` is a quotient of reals.  This removes
the only non-proven input of `caseII_section91_factorEquations`. -/
theorem caseIISection91ProductHalf37_proven : CaseIISection91ProductHalf37 := by
  intro m D η hη hcop
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  set K := CyclotomicField 37 ℚ with hK
  -- The field equation `X·X̄ = (algebraMap u)·(algebraMap γ₀)³⁷`.
  obtain ⟨u, γ₀, hγ₀_real, hfield⟩ := caseII_productHalf_field_eq D hp η hη hcop
  -- The unit `η' : Kˣ` with `(η' : K) = algebraMap u`.
  set η' : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u with hη'_def
  have hη'_val : (η' : K) = algebraMap (𝓞 K) K (u : 𝓞 K) := by
    rw [hη'_def, Units.coe_map]; rfl
  set γ : K := algebraMap (𝓞 K) K γ₀ with hγ_def
  refine ⟨η', γ, ?_, ?_⟩
  · -- Reality of `η'`: `(η':K) = (X·X̄)/γ³⁷`, both real.
    -- `X·X̄` is real.
    have hreal_prod : complexConj K (caseII_section91_factor D η *
        caseII_section91_factorConj D η) =
        caseII_section91_factor D η * caseII_section91_factorConj D η :=
      caseII_section91_product_real D η
    -- `γ³⁷` is real and nonzero.
    have hγ_real : complexConj K γ = γ := by
      rw [hγ_def, ← coe_ringOfIntegersComplexConj, hγ₀_real]
    -- `X·X̄ ≠ 0` (product of the two nonzero adjacent factors).
    have hprod_ne : caseII_section91_factor D η * caseII_section91_factorConj D η ≠ 0 :=
      mul_ne_zero (caseII_section91_factor_ne_zero D η hη)
        (caseII_section91_factorConj_ne_zero D η hη)
    -- `γ ≠ 0`: else `hfield`'s RHS is `0`, contradicting `X·X̄ ≠ 0`.
    have hγ_ne : γ ≠ 0 := by
      intro h0
      apply hprod_ne
      have hf : caseII_section91_factor D η * caseII_section91_factorConj D η =
          algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ 37 := hfield
      rw [hf, h0, zero_pow (by decide : (37 : ℕ) ≠ 0), mul_zero]
    have hγ37_real : complexConj K (γ ^ 37) = γ ^ 37 := by rw [map_pow, hγ_real]
    have hγ37_ne : γ ^ 37 ≠ 0 := pow_ne_zero 37 hγ_ne
    -- `(η':K) = (X·X̄)/γ³⁷`.
    have hη'_eq : (η' : K) = (caseII_section91_factor D η * caseII_section91_factorConj D η)
        / γ ^ 37 := by
      rw [hη'_val]
      -- `hfield : X·X̄ = algebraMap u · γ³⁷` (with the factor/factorConj defs).
      have hf : caseII_section91_factor D η * caseII_section91_factorConj D η =
          algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ 37 := hfield
      rw [hf, mul_div_assoc, div_self hγ37_ne, mul_one]
    rw [hη'_eq, map_div₀, hreal_prod, hγ37_real]
  · -- The factor-equation form: `X·X̄ = (η':K)·γ³⁷`.
    rw [hη'_val, hγ_def]
    -- This is exactly `hfield`.
    exact hfield

end BernoulliRegular.FLT37.Eichler

end

end
