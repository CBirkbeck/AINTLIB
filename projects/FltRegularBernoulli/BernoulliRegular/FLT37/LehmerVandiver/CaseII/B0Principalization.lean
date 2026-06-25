import BernoulliRegular.FLT37.LehmerVandiver.CaseII.Main
import BernoulliRegular.TotallyRealSubfield.ClassGroup


/-!
# LV009-CTOR-a: B₀ principalization under `p ∤ h⁺`

Foundational class-group input to the case-II bridge: under `¬ p ∣ h⁺(K)`,
any ideal `B ⊆ 𝓞 K` that descends from `𝓞 K⁺` (i.e. `B = J.map _` for
some `J ⊆ 𝓞 K⁺`) and whose `p`-th power is principal is itself
principal.

Proof. From `[B^p] = 1` in `Cl(K)` and the injectivity of
`classGroupMap : Cl(𝓞 K⁺) → Cl(𝓞 K)` (Diekmann Prop 55,
`classGroupMap_injective`), we lift to `[J]^p = 1` in `Cl(𝓞 K⁺)`.
Lagrange gives `[J]^{h⁺} = 1`. Bezout `gcd(p, h⁺) = 1` from
`¬ p ∣ h⁺` then forces `[J] = 1`, so `J` is principal in `𝓞 K⁺`, hence
`B = J.map _` is principal in `𝓞 K`.

This input is needed for Washington Theorem 9.4 / case II case II:
the auxiliary ideal `B₀ = (1 - ζ)^{-m} · (ω^p + θ^p) · 𝓞 K` (Eq. 9.1.0,
real-form) must be made principal under `p ∤ h⁺` to begin the descent.

## References

* Washington, *Introduction to Cyclotomic Fields*, §9.1, Eq. 9.1.0;
  Theorem 9.4 (p. 174).
* Diekmann (2023), Proposition 55.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Class triviality from p-torsion + `¬ p ∣ h⁺`.** A class
`c : ClassGroup (𝓞 K⁺)` with `c^p = 1` is trivial provided `p ∤ h⁺(K)`.
Proof: Lagrange's theorem gives `orderOf c ∣ h⁺`; combined with
`orderOf c ∣ p` (from `c^p = 1`) and `gcd(p, h⁺) = 1` (from `p` prime
and `¬ p ∣ h⁺`), we get `orderOf c ∣ 1`, so `c = 1`. -/
theorem class_eq_one_of_pow_eq_one_of_not_dvd_hPlus
    (_hp_odd : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (c : ClassGroup (𝓞 (K⁺))) (hc : c ^ p = 1) :
    c = 1 := by
  have hcop : Nat.Coprime p (hPlus K) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd).mpr h_not_dvd
  have h_ord_p : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hc
  have h_ord_h : orderOf c ∣ hPlus K := orderOf_dvd_card
  have h_ord_one : orderOf c ∣ 1 :=
    hcop.gcd_eq_one ▸ Nat.dvd_gcd h_ord_p h_ord_h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h_ord_one)

/-- **B₀ principalization, ideal form.** A real ideal `J.map _` whose
`p`-th power is principal in `𝓞 K` is itself principal in `𝓞 K`,
provided `p ∤ h⁺(K)`.

Threading: from `(J.map _)^p` principal we use Diekmann Prop 55
(`isPrincipal_of_isPrincipal_map_Kplus`) to get `J^p` principal in
`𝓞 K⁺`. Hence `[J]^p = 1` in `Cl(𝓞 K⁺)`; combined with `p ∤ h⁺`
and `class_eq_one_of_pow_eq_one_of_not_dvd_hPlus`, this gives `[J] = 1`,
so `J` is principal in `𝓞 K⁺`, hence `J.map _` is principal in `𝓞 K`. -/
theorem map_isPrincipal_of_pow_principal_of_not_dvd_hPlus (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {J : Ideal (𝓞 (K⁺))} (hJ_ne : J ≠ ⊥)
    (hJ_pow : ((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p).IsPrincipal) :
    (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))).IsPrincipal := by
  rw [← Ideal.map_pow] at hJ_pow
  have hJp_principal : (J ^ p).IsPrincipal :=
    isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_odd) (K := K)
      (J ^ p) hJ_pow
  have hJp_ne : J ^ p ≠ ⊥ := pow_ne_zero p hJ_ne
  have hJ_ne0 : J ∈ nonZeroDivisors (Ideal (𝓞 (K⁺))) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne
  have hJp_ne0 : J ^ p ∈ nonZeroDivisors (Ideal (𝓞 (K⁺))) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJp_ne
  have hJpow_class : ClassGroup.mk0 ⟨J, hJ_ne0⟩ ^ p = 1 := by
    rw [← map_pow]
    exact (ClassGroup.mk0_eq_one_iff hJp_ne0).mpr hJp_principal
  have hJ_principal : J.IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff hJ_ne0).mp
      (class_eq_one_of_pow_eq_one_of_not_dvd_hPlus hp_odd h_not_dvd _ hJpow_class)
  exact Submodule.IsPrincipal.map_ringHom (algebraMap (𝓞 (K⁺)) (𝓞 K)) hJ_principal

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

end
