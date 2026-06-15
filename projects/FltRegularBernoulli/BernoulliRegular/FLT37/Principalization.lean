module

public import BernoulliRegular.TotallyRealSubfield

/-!
# Vandiver Lemma 1 — descent-based principalization (ticket FLT37b1)

This module proves the **descent skeleton** for Vandiver's Lemma 1: under
Vandiver's conjecture for a prime `p` (i.e. `p` coprime to the class number of
`K⁺ = ℚ(ζ_p + ζ_p⁻¹)`), an ideal of `𝒪_{K⁺}` whose extension to `𝒪_K` becomes
the `p`-th power of a principal ideal is itself principal.

The full classical Vandiver Lemma 1 — *primary `α ∈ 𝒪_K` with `(α) = 𝔞^p`
forces `𝔞` principal* — splits into:

1. (this file, `FLT37b1`) the descent step, which closes the question once
   `[𝔞]` has been located in the image of `Cl(𝒪_{K⁺}) → Cl(𝒪_K)`; and
2. a separate `FLT37b2` file that defines `IsPrimary`, proves primary
   elements force `[𝔞]` to be `σ`-fixed in `Cl(K)`, and descends the class
   to `Cl(𝒪_{K⁺})`.

Vandiver's conjecture is computationally verified for `p = 37` via
`h(K⁺_{37}) = 1`, but the formal verification of `h(K⁺_{37}) = 1` is left to a
later companion ticket.

## References

* Washington, *Introduction to Cyclotomic Fields*, Theorem 6.16.
* Borevich–Shafarevich, *Number Theory*, §4.9.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

/-! ## Ideal-form principalization under coprime class-group order

`flt-regular`'s `isPrincipal_of_isPrincipal_pow_of_Coprime'` is stated for
fractional ideals; we package its `Ideal` analogue here. -/

/-- If `n` is coprime to `|Cl(A)|`, then a non-zero ideal `I` of a Dedekind
domain `A` whose `n`-th power is principal is itself principal. -/
theorem isPrincipal_of_isPrincipal_pow_of_coprime
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Fintype (ClassGroup A)] {n : ℕ}
    (hcop : n.Coprime (Fintype.card (ClassGroup A)))
    {I : Ideal A} (hI_nz : I ≠ ⊥) (hpow : (I ^ n).IsPrincipal) :
    I.IsPrincipal := by
  have hI_mem : I ∈ (Ideal A)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hI_nz
  have hIp_mem : I ^ n ∈ (Ideal A)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hI_nz)
  rw [← ClassGroup.mk0_eq_one_iff hI_mem, ← orderOf_eq_one_iff,
      ← Nat.dvd_one, ← hcop, Nat.dvd_gcd_iff]
  refine ⟨?_, orderOf_dvd_card⟩
  rw [orderOf_dvd_iff_pow_eq_one]
  have heq : ClassGroup.mk0 (⟨I, hI_mem⟩ : (Ideal A)⁰) ^ n =
      ClassGroup.mk0 ⟨I ^ n, hIp_mem⟩ := by
    rw [← map_pow]
    rfl
  rw [heq, ClassGroup.mk0_eq_one_iff hIp_mem]
  exact hpow

/-! ## Vandiver Lemma 1 descent skeleton -/

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

include hp_odd in
/-- **Vandiver Lemma 1, descent form (FLT37b1).**

Suppose Vandiver's conjecture holds for `p` (`p` coprime to `h(K⁺)`) and the
extension to `𝒪_K` of an ideal `aPlus` of `𝒪_{K⁺}` has its `p`-th power
principal in `𝒪_K`. Then `aPlus` is principal in `𝒪_{K⁺}`.

The proof combines:

* `BernoulliRegular.isPrincipal_of_isPrincipal_map_Kplus` (Diekmann Prop 55,
  axiom-free), which descends principal ideals from `𝒪_K` to `𝒪_{K⁺}`; and
* `isPrincipal_of_isPrincipal_pow_of_coprime` applied in `𝒪_{K⁺}`. -/
theorem isPrincipal_of_isPrincipal_pow_map_Kplus [IsCMField K]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (K⁺)))))
    {aPlus : Ideal (𝓞 (K⁺))} (haPlus_nz : aPlus ≠ ⊥)
    (hpow : ((aPlus.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p).IsPrincipal) :
    aPlus.IsPrincipal := by
  have hpow_descend : (aPlus ^ p).IsPrincipal := by
    apply isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_odd) (K := K)
    rw [Ideal.map_pow]
    exact hpow
  exact isPrincipal_of_isPrincipal_pow_of_coprime h_VC haPlus_nz hpow_descend

include hp_odd in
/-- Companion form of `isPrincipal_of_isPrincipal_pow_map_Kplus`: under the
same hypotheses, the *extended* ideal `aPlus · 𝒪_K` is principal in `𝒪_K`. -/
theorem isPrincipal_map_of_isPrincipal_pow_map_Kplus [IsCMField K]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (K⁺)))))
    {aPlus : Ideal (𝓞 (K⁺))} (haPlus_nz : aPlus ≠ ⊥)
    (hpow : ((aPlus.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p).IsPrincipal) :
    (aPlus.map (algebraMap (𝓞 (K⁺)) (𝓞 K))).IsPrincipal :=
  Submodule.IsPrincipal.map_ringHom (algebraMap (𝓞 (K⁺)) (𝓞 K))
    (isPrincipal_of_isPrincipal_pow_map_Kplus
      (p := p) (hp_odd := hp_odd) (K := K) h_VC haPlus_nz hpow)

include hp_odd in
/-- **Vandiver Lemma 1, K-side form (FLT37b3 with descent hypothesis).**

If `𝔞 : Ideal (𝓞 K)` admits a descent to `𝓞 K⁺` (i.e. `𝔞 = aPlus · 𝓞 K`
for some `aPlus`), and its `p`-th power is principal in `𝓞 K`, then under
Vandiver's conjecture for `p` (`p` coprime to `h(K⁺)`), `𝔞` itself is
principal in `𝓞 K`.

This is the user-facing form of `isPrincipal_map_of_isPrincipal_pow_map_Kplus`,
phrased in terms of an ideal `𝔞 : Ideal (𝓞 K)` together with a descent
hypothesis. It composes `Submodule.IsPrincipal.map_ringHom` with the K⁺-side
descent skeleton, and is the natural target of the FLT37b2b2 ⇒ b3
combination once primary descent is in place. -/
theorem isPrincipal_of_descent_of_isPrincipal_pow [IsCMField K]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (K⁺)))))
    {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h_pow : (𝔞 ^ p).IsPrincipal)
    (h_descent : ∃ aPlus : Ideal (𝓞 (K⁺)),
        aPlus.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) = 𝔞) :
    𝔞.IsPrincipal := by
  obtain ⟨aPlus, hap⟩ := h_descent
  have haPlus_nz : aPlus ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.map_bot] at hap
    exact h𝔞_nz hap.symm
  rw [← hap]
  exact isPrincipal_map_of_isPrincipal_pow_map_Kplus
    (p := p) (hp_odd := hp_odd) (K := K) h_VC haPlus_nz (by rw [hap]; exact h_pow)

end CyclotomicSetup

end FLT37

end BernoulliRegular

end
