import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ClassEqDischarge
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IsPrincipal
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Main
import BernoulliRegular.FLT37.CaseI

/-!
# LV010-D: case-I bridge under `¬ p ∣ h⁺` (parametric on class equality)

Mirror of flt-regular's `caseI_easier` / `ex_fin_div` / `caseI`
(`FltRegular.CaseI.Statement`), but with `IsRegularPrime p` replaced by
`¬ p ∣ h⁺(K)` and a `CaseIClassEqDischarge p K` parameter.

The Mirimanoff-style integer-coefficient analysis after `is_principal`
doesn't depend on regularity — only on the conclusion
`∃ u, α : u·α^p = a + ζ b`. The `aux0k₁`, `aux0k₂`, `aux1k₁`, `aux1k₂`,
`auxk₁k₂` lemmas in flt-regular are regularity-free; we re-use them
verbatim. The `MayAssume` step (gcd normalization, `a ≢ b` reduction) is
also regularity-free; we re-use it from flt-regular as well.

Once the Vandiver class equality `[σI] = [I]` is discharged unconditionally
(via Stages 1 + 2 — primary normalization + Kummer's lemma), this
parametric bridge becomes an unconditional `CaseIBridge p K`.

## References

* flt-regular's `FltRegular.caseI` (`FltRegular/CaseI/Statement.lean:247`).
* `caseI_is_principal_of_not_dvd_hPlus` (LV010-C).
* Vandiver 1934, Theorem 1.
-/

@[expose] public section

noncomputable section

open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI
open NumberField NumberField.IsCMField

open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable {p : ℕ} [hpri : Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- **LV010-D principal extraction (general).** Given the class-equality
discharge plus `¬ p ∣ h⁺`, produces `∃ u, α : u·α^p = a + ζ b` for any
case-I scenario. -/
theorem caseI_principal_of_not_dvd_hPlus
    (hp5 : 5 ≤ p) (hp_odd : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_class_eq : CaseIClassEqDischarge p (CyclotomicField p ℚ))
    {a b c : ℤ} {ζ : 𝓞 (CyclotomicField p ℚ)}
    (hζ : IsPrimitiveRoot ζ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    (heq : a ^ p + b ^ p = c ^ p) :
    ∃ (u : (𝓞 (CyclotomicField p ℚ))ˣ) (α : 𝓞 (CyclotomicField p ℚ)),
      ↑u * α ^ p =
        (a : 𝓞 (CyclotomicField p ℚ)) +
          ζ * (b : 𝓞 (CyclotomicField p ℚ)) := by
  by_cases h_factor_ne :
    (a : 𝓞 (CyclotomicField p ℚ)) + ζ * (b : 𝓞 (CyclotomicField p ℚ)) = 0
  · refine ⟨1, 0, ?_⟩
    rw [h_factor_ne, Units.val_one, one_mul, zero_pow]
    exact hpri.out.ne_zero
  · refine caseI_is_principal_of_not_dvd_hPlus hp5 hp_odd h_not_dvd
      hgcd hcaseI heq hζ h_factor_ne ?_
    intro I hI_nz hI
    exact h_class_eq hgcd hcaseI heq hζ hI_nz hI

set_option backward.isDefEq.respectTransparency false in
/-- **LV010-D ex_fin_div under `¬ p ∣ h⁺`.** Mirror of flt-regular's
`ex_fin_div`, with `IsRegularPrime p` replaced by `¬ p ∣ h⁺(K)` and a
`CaseIClassEqDischarge p K` parameter. -/
theorem caseI_ex_fin_div_of_not_dvd_hPlus
    (hp5 : 5 ≤ p) (hp_odd : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_class_eq : CaseIClassEqDischarge p (CyclotomicField p ℚ))
    {a b c : ℤ} {ζ : 𝓞 (CyclotomicField p ℚ)}
    (hζ : IsPrimitiveRoot ζ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    (heq : a ^ p + b ^ p = c ^ p) :
    ∃ k₁ k₂ : Fin p,
      k₂ ≡ k₁ - 1 [ZMOD p] ∧
        ((p : ℤ) : 𝓞 (CyclotomicField p ℚ)) ∣
          (a : 𝓞 (CyclotomicField p ℚ)) +
          (b : 𝓞 (CyclotomicField p ℚ)) * ζ -
          (a : 𝓞 (CyclotomicField p ℚ)) * ζ ^ (k₁ : ℕ) -
          (b : 𝓞 (CyclotomicField p ℚ)) * ζ ^ (k₂ : ℕ) := by
  set K := CyclotomicField p ℚ with hK_def
  let ζ' := (ζ : K)
  have hζ' : IsPrimitiveRoot ζ' p := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let zetaUnit := (hζ'.toInteger_isPrimitiveRoot.isUnit hpri.out.ne_zero).unit
  have hζ_unit_eq : ζ = (zetaUnit : 𝓞 K) := rfl
  obtain ⟨u, α, hu⟩ :=
    caseI_principal_of_not_dvd_hPlus hp5 hp_odd h_not_dvd h_class_eq
      hζ hgcd hcaseI heq
  rw [hζ_unit_eq, mul_comm _ (↑b : 𝓞 K), ← pow_one zetaUnit] at hu
  obtain ⟨k, hk⟩ :=
    FltRegular.CaseI.exists_int_sum_eq_zero hζ' a b 1 hu.symm (by linarith)
  simp only [zpow_one, zpow_neg, mem_span_singleton] at hk
  have hpcoe : (p : ℤ) ≠ 0 := by exact_mod_cast hpri.out.ne_zero
  refine ⟨⟨(2 * k % p).natAbs, ?_⟩, ⟨((2 * k - 1) % p).natAbs, ?_⟩, ?_, ?_⟩
  repeat'
    rw [← natAbs_natCast p]
    refine natAbs_lt_natAbs_of_nonneg_of_lt (emod_nonneg _ hpcoe) ?_
    rw [natAbs_natCast]
    exact emod_lt_of_pos _ (by exact_mod_cast hpri.out.pos)
  · simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_eq_intCast_iff,
      ZMod.intCast_mod, Int.cast_sub, Int.cast_mul, Int.cast_one]
  simp only [add_sub_assoc, sub_sub] at hk ⊢
  convert! hk using 3
  rw [mul_add, mul_comm (↑a : 𝓞 K), ← mul_assoc _ (↑b : 𝓞 K),
      mul_comm _ (↑b : 𝓞 K), mul_assoc (↑b : 𝓞 K)]
  congr 2
  · ext
    simp only [map_pow, NumberField.Units.coe_zpow]
    change ζ' ^ ↑(2 * k % ↑p).natAbs = ζ' ^ (2 * k)
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, sub_self]
  · ext
    simp only [map_pow, _root_.map_mul, NumberField.Units.coe_zpow, map_units_inv]
    change ζ' ^ ↑((2 * k - 1) % ↑p).natAbs = ζ' ^ (2 * k) * ζ'⁻¹
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub_one₀ (hζ'.ne_zero hpri.out.ne_zero), ←
      zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, Int.cast_one, sub_self]

set_option backward.isDefEq.respectTransparency false in
/-- **LV010-D caseI_easier under `¬ p ∣ h⁺`.** Mirror of flt-regular's
`caseI_easier`, with `IsRegularPrime p` replaced by `¬ p ∣ h⁺(K)` and a
`CaseIClassEqDischarge p K` parameter.

Under the reduced FLT case-I hypotheses (`gcd(a,b,c) = 1`,
`¬ a ≡ b [ZMOD p]`, `¬ p ∣ abc`), no FLT case-I solution exists for the
exponent `p`. -/
theorem caseI_easier_of_not_dvd_hPlus
    (hp5 : 5 ≤ p) (hp_odd : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_class_eq : CaseIClassEqDischarge p (CyclotomicField p ℚ))
    {a b c : ℤ}
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hab : ¬ a ≡ b [ZMOD p])
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  set K := CyclotomicField p ℚ
  set ζ := zeta p ℤ (𝓞 K)
  have hζ : IsPrimitiveRoot ζ p := zeta_spec p ℤ (𝓞 K)
  intro H
  obtain ⟨k₁, k₂, hcong, hdiv⟩ :=
    caseI_ex_fin_div_of_not_dvd_hPlus hp5 hp_odd h_not_dvd h_class_eq hζ hgcd hcaseI H
  have key : ((p : ℤ) : 𝓞 K) ∣ ∑ j ∈ range p, FltRegular.f a b k₁ k₂ j • ζ ^ j := by
    convert hdiv using 1
    have h01 : 0 ≠ 1 := zero_ne_one
    have h0k₁ := aux0k₁ hpri.out hp5 hζ hcaseI hcong hdiv
    have h0k₂ := aux0k₂ hpri.out hp5 hζ hab hcong hdiv
    have h1k₁ := aux1k₁ hpri.out hp5 hζ hab hcong hdiv
    have h1k₂ := aux1k₂ hpri.out hp5 hζ hcaseI hcong hdiv
    have hk₁k₂ : (k₁ : ℕ) ≠ (k₂ : ℕ) := auxk₁k₂ hpri.out hcong
    simp_rw [FltRegular.f, ite_smul, sum_ite, filter_filter, ← Ne.eq_def,
      ne_and_eq_iff_right h01, and_assoc,
      ne_and_eq_iff_right h1k₁, ne_and_eq_iff_right h0k₁, ne_and_eq_iff_right hk₁k₂,
      ne_and_eq_iff_right h1k₂, ne_and_eq_iff_right h0k₂, Finset.range_filter_eq]
    simp only [hpri.out.pos, hpri.out.one_lt, if_true, zsmul_eq_mul, sum_singleton, _root_.pow_zero,
      mul_one, pow_one, Fin.is_lt, neg_smul, sum_neg_distrib, Ne, zero_smul, sum_const_zero,
      add_zero]
    ring
  rw [sum_range] at key
  refine hcaseI (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _)
  simpa [FltRegular.f] using
    dvd_coeff_cycl_integer hpri.out hζ (FltRegular.auxf hp5 a b k₁ k₂) key
    ⟨0, hpri.out.pos⟩

set_option backward.isDefEq.respectTransparency false in
/-- **LV010-D case I under `¬ p ∣ h⁺` (full statement).** Mirror of
flt-regular's `FltRegular.caseI`, with `IsRegularPrime p` replaced by
`¬ p ∣ h⁺(K)` and a `CaseIClassEqDischarge p K` parameter. -/
theorem caseI_of_not_dvd_hPlus
    (hp_odd : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_class_eq : CaseIClassEqDischarge p (CyclotomicField p ℚ))
    {a b c : ℤ}
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro H
  have hprod : a * b * c ≠ 0 := by
    intro h; simp [h] at hcaseI
  have hp5 : 5 ≤ p := by
    by_contra! habs
    have hp2lt : 2 < p := Nat.lt_of_le_of_ne hpri.out.two_le hp_odd.symm
    interval_cases p
    · exact fermatLastTheoremFor_iff_int.1 fermatLastTheoremThree a b c
        (fun ha ↦ hprod <| by simp [ha]) (fun hb ↦ hprod <| by simp [hb])
        (fun hc ↦ hprod <| by simp [hc]) H
    · exact Nat.not_prime_mul one_lt_two.ne' one_lt_two.ne' hpri.out
  let d := ({a, b, c} : Finset ℤ).gcd id
  have hd : d ≠ 0 :=
    Finset.gcd_ne_zero_iff.mpr ⟨c, by simp, fun hc ↦ hprod <| by simp_all⟩
  have hdiv : ¬ (p : ℤ) ∣ a / d * (b / d) * (c / d) := by
    contrapose! hcaseI with hdiv
    have hadiv : d ∣ a := Finset.gcd_dvd (by simp)
    have hbdiv : d ∣ b := Finset.gcd_dvd (by simp)
    have hcdiv : d ∣ c := Finset.gcd_dvd (by simp)
    rw [← Int.ediv_mul_cancel hadiv, ← Int.ediv_mul_cancel hbdiv, ← Int.ediv_mul_cancel hcdiv]
    have heq : a / d * d * (b / d * d) * (c / d * d) =
        a / d * (b / d) * (c / d) * (d * d * d) := by ring
    rw [heq]
    exact hdiv.mul_right (d * d * d)
  rcases FltRegular.MayAssume.coprime H hprod with ⟨Hxyz, hunit, hprodxyx⟩
  obtain ⟨X, Y, Z, H1, H2, H3, _, H5⟩ :=
    FltRegular.a_not_cong_b hpri.out hp5 hprodxyx Hxyz hunit hdiv
  exact caseI_easier_of_not_dvd_hPlus hp5 hp_odd h_not_dvd h_class_eq H2 H3 H5 H1

set_option backward.isDefEq.respectTransparency false in
/-- **LV010-D CaseIBridge constructor (parametric).** From a
`CaseIClassEqDischarge p K`, builds a `CaseIBridge p (CyclotomicField p ℚ)`
term. -/
theorem caseIBridge_of_classEqDischarge
    (hp_odd : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    (h_class_eq : CaseIClassEqDischarge p (CyclotomicField p ℚ)) :
    CaseIBridge p (CyclotomicField p ℚ) where
  no_caseI_solution := by
    intro h_not_dvd a b c hcaseI
    exact caseI_of_not_dvd_hPlus hp_odd h_not_dvd h_class_eq hcaseI

set_option backward.isDefEq.respectTransparency false in
/-- **CaseIBridge from regularity (compatibility check).** For a regular
prime, builds a `CaseIBridge p (CyclotomicField p ℚ)` term. -/
theorem caseIBridge_of_regular
    (hp_odd : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    [Fintype (ClassGroup (𝓞 (CyclotomicField p ℚ)))]
    (hreg : p.Coprime <|
      Fintype.card <| ClassGroup (𝓞 (CyclotomicField p ℚ))) :
    CaseIBridge p (CyclotomicField p ℚ) :=
  caseIBridge_of_classEqDischarge hp_odd
    (caseIClassEqDischarge_of_regular hreg)

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
