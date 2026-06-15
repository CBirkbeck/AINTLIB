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

open NumberField IsCyclotomicExtension Ideal
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

set_option backward.isDefEq.respectTransparency false in
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
  have hp_prime : Nat.Prime p := Fact.out
  have hcop : Nat.Coprime p (hPlus K) :=
    (Nat.Prime.coprime_iff_not_dvd hp_prime).mpr h_not_dvd
  -- orderOf c ∣ p (from c^p = 1)
  have h_ord_p : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hc
  -- orderOf c ∣ h⁺ (Lagrange)
  have h_ord_h : orderOf c ∣ hPlus K := by
    unfold hPlus
    exact orderOf_dvd_card
  -- orderOf c ∣ gcd(p, h⁺) = 1
  have h_ord_one : orderOf c ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h_ord_p h_ord_h
  -- So orderOf c = 1, i.e. c = 1.
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h_ord_one)

set_option backward.isDefEq.respectTransparency false in
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
  -- (J.map _)^p = (J^p).map _.
  rw [show ((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p) =
      (J ^ p).map (algebraMap (𝓞 (K⁺)) (𝓞 K)) from
    (Ideal.map_pow (algebraMap (𝓞 (K⁺)) (𝓞 K)) J p).symm] at hJ_pow
  -- (J^p).map _ principal ⟹ J^p principal in K⁺ (Diekmann Prop 55).
  have hJp_principal : (J ^ p).IsPrincipal :=
    isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_odd) (K := K)
      (J ^ p) hJ_pow
  -- Now translate to ClassGroup level.
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hJp_ne : J ^ p ≠ ⊥ := by
    intro h
    -- J^p = ⊥ in a Dedekind domain forces J = ⊥ (since J ≠ ⊥ implies J ^ p ≠ ⊥
    -- by integral domain on the fraction-ideal level).
    apply hJ_ne
    rcases pow_eq_zero_iff hp_pos.ne' |>.mp h with rfl
    rfl
  have hJ_ne0 : J ∈ nonZeroDivisors (Ideal (𝓞 (K⁺))) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne
  have hJp_ne0 : J ^ p ∈ nonZeroDivisors (Ideal (𝓞 (K⁺))) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJp_ne
  -- Class of J^p equals (Class of J)^p.
  have hJpow_class : (ClassGroup.mk0 ⟨J, hJ_ne0⟩) ^ p = 1 := by
    have : ClassGroup.mk0 ⟨J ^ p, hJp_ne0⟩ = (ClassGroup.mk0 ⟨J, hJ_ne0⟩) ^ p := by
      rw [← map_pow]
      rfl
    rw [← this]
    exact (ClassGroup.mk0_eq_one_iff hJp_ne0).mpr hJp_principal
  -- Apply triviality lemma.
  have hJ_class : ClassGroup.mk0 ⟨J, hJ_ne0⟩ = 1 :=
    class_eq_one_of_pow_eq_one_of_not_dvd_hPlus hp_odd h_not_dvd _ hJpow_class
  have hJ_principal : J.IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff hJ_ne0).mp hJ_class
  -- Map of principal ideal is principal.
  obtain ⟨a, ha⟩ := hJ_principal
  refine ⟨⟨algebraMap _ _ a, ?_⟩⟩
  -- ha : J = Ideal.span {a} (as Submodule); J.map _ = (span{a}).map _ = span{algebraMap _ _ a}.
  have h_map_span : J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) =
      Ideal.span {algebraMap (𝓞 (K⁺)) (𝓞 K) a} := by
    rw [show J = Ideal.span {a} by exact ha]
    exact Ideal.map_span _ _ |>.trans (by rw [Set.image_singleton])
  rw [h_map_span]

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

end
