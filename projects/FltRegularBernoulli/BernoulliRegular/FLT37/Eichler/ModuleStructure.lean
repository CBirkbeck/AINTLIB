import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IdealFactorisation
import BernoulliRegular.Reflection.ClassGroupModP.GalAction

/-!
# Eichler module structure: `p`-torsion of the case-I factor ideal class

The case-I cyclotomic factorisation produces, for each `p`-th root of
unity `ζ`, an ideal `I` with

  `Ideal.span ({a + ζ * b} : Set (𝓞 K)) = I ^ p`

(`BernoulliRegular.FLT37.LehmerVandiver.CaseI.caseI_factor_idealSpan_eq_pow`).
Since the right-hand side is `I ^ p` and the left-hand side is a principal
ideal, the class `[I] ∈ ClassGroup (𝓞 K)` satisfies

  `[I] ^ p = [I ^ p] = [span {a + ζ b}] = 1`.

That is, the class of the `p`-th-root ideal is `p`-torsion. This is the
foundational module-theoretic input to the Eichler/Stickelberger descent:
the case-I obstruction lives in `ClassGroup (𝓞 K)[p]`.

The ideal `I` is genuinely nonzero (it lies in `(Ideal (𝓞 K))⁰`) because
`a + ζ * b ≠ 0`: if it vanished, the product factorisation
`a^p + b^p = ∏_{ζ} (a + ζ b)` would force `c^p = 0`, contradicting
`c ≠ 0` (which follows from `p ∤ a · b · c`).

## References

* `BernoulliRegular.FLT37.LehmerVandiver.CaseI.caseI_factor_idealSpan_eq_pow`.
* Washington, *Introduction to Cyclotomic Fields*, §9.1.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Ideal Polynomial

open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace Eichler

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The class of the `p`-th-root ideal `I` (with `span {a + ζ b} = I ^ p`)
is `p`-torsion:
`[I] ^ p = [I ^ p] = [span {a + ζ b}] = 1`, since `span {a + ζ b}` is
principal. The ideal `I` is nonzero (`I ∈ (Ideal (𝓞 K))⁰`) because
`a + ζ * b ≠ 0`. -/
theorem caseI_factor_class_pow_eq_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 (CyclotomicField p ℚ)}
    (hζ : ζ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) :
    ∃ (I : Ideal (𝓞 (CyclotomicField p ℚ)))
      (hI : I ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰),
      Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) + ζ *
        (b : 𝓞 (CyclotomicField p ℚ))} :
          Set (𝓞 (CyclotomicField p ℚ))) = I ^ p ∧
      ClassGroup.mk0 ⟨I, hI⟩ ^ p = 1 := by
  obtain ⟨I, hI_eq⟩ :=
    LehmerVandiver.CaseI.caseI_factor_idealSpan_eq_pow hp5 heq hgcd hcaseI hζ
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := (Fact.out (p := p.Prime)).eq_two_or_odd'.resolve_left hp2
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hcaseI (by simp)
  have hfac_ne : (a : 𝓞 (CyclotomicField p ℚ)) + ζ * (b : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := by
    intro hfac0
    have hμ : IsPrimitiveRoot
        ((IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger) p :=
      (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)).toInteger_isPrimitiveRoot
    have hprod := hμ.pow_add_pow_eq_prod_add_mul (a : 𝓞 (CyclotomicField p ℚ))
      (b : 𝓞 (CyclotomicField p ℚ)) hpodd
    have hzero : (∏ η ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        ((a : 𝓞 (CyclotomicField p ℚ)) + η * (b : 𝓞 (CyclotomicField p ℚ)))) = 0 :=
      Finset.prod_eq_zero hζ hfac0
    have hcast : (a : 𝓞 (CyclotomicField p ℚ)) ^ p + (b : 𝓞 (CyclotomicField p ℚ)) ^ p
        = (c : 𝓞 (CyclotomicField p ℚ)) ^ p := by
      rw [← Int.cast_pow, ← Int.cast_pow, ← Int.cast_add, heq, Int.cast_pow]
    rw [hprod, hzero] at hcast
    have hcp0 : (c : 𝓞 (CyclotomicField p ℚ)) ^ p = 0 := hcast.symm
    have : (c : 𝓞 (CyclotomicField p ℚ)) = 0 := by
      simpa using pow_eq_zero_iff (Fact.out (p := p.Prime)).pos.ne' |>.mp hcp0
    exact hc0 (by exact_mod_cast this)
  have hspan_ne : Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) + ζ *
      (b : 𝓞 (CyclotomicField p ℚ))} : Set (𝓞 (CyclotomicField p ℚ))) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hfac_ne
  have hIp_ne : I ^ p ≠ ⊥ := hI_eq ▸ hspan_ne
  have hI_ne : I ≠ ⊥ := fun h ↦ hIp_ne (by rw [h, Ideal.bot_pow (Fact.out (p := p.Prime)).ne_zero])
  have hI_mem : I ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne
  refine ⟨I, hI_mem, hI_eq, ?_⟩
  have hIp_mem : I ^ p ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hIp_ne
  have hcoe : (⟨I, hI_mem⟩ : (Ideal (𝓞 (CyclotomicField p ℚ)))⁰) ^ p
      = ⟨I ^ p, hIp_mem⟩ := by
    ext
    simp
  calc ClassGroup.mk0 ⟨I, hI_mem⟩ ^ p
      = ClassGroup.mk0 (⟨I, hI_mem⟩ ^ p) := by rw [map_pow]
    _ = ClassGroup.mk0 ⟨I ^ p, hIp_mem⟩ := by rw [hcoe]
    _ = 1 := by
        rw [ClassGroup.mk0_eq_one_iff, ← hI_eq]
        exact ⟨_, rfl⟩

/-- **`p`-th-root ideal uniqueness.** In the Dedekind domain
`𝓞 (CyclotomicField p ℚ)`, taking `n`-th powers of ideals is injective
for `n ≠ 0`: `I ^ n = J ^ n → I = J`. -/
theorem ideal_pow_right_injective_ordIntegers {p : ℕ} [Fact p.Prime] {n : ℕ}
    (hn : n ≠ 0) {I J : Ideal (𝓞 (CyclotomicField p ℚ))} (h : I ^ n = J ^ n) :
    I = J := by
  have hIJ : I ∣ J := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn).mp (by rw [h])
  have hJI : J ∣ I := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn).mp (by rw [h])
  exact dvd_antisymm hIJ hJI

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- **Galois equivariance of the case-I factor class family.** The
cyclotomic Galois automorphism `σ_g` (indexed by `g : (ZMod p)ˣ`, with
`σ_g ζ = ζ ^ g`) sends the class `[I_ζ]` of the `p`-th-root ideal of
`a + ζ b` (`span {a + ζ b} = I_ζ ^ p`) to the class `[I_{σ_g ζ}]` of the
`p`-th-root ideal of `a + (σ_g ζ) b` (`span {a + (σ_g ζ) b} = J ^ p`).

Here `σ_g ζ` is `cyclotomicRingOfIntegersEquiv (CyclotomicField p ℚ) g ζ`,
the image of `ζ` under the ring-of-integers automorphism induced by `σ_g`.
Both `I` and `J` arise from
`BernoulliRegular.FLT37.LehmerVandiver.CaseI.caseI_factor_idealSpan_eq_pow`
(at the roots `ζ` and `σ_g ζ` respectively). -/
theorem caseI_factor_class_galAction_eq {p : ℕ} [Fact p.Prime]
    {a b : ℤ}
    (g : CyclotomicUnitDelta p)
    {ζ : 𝓞 (CyclotomicField p ℚ)}
    {I J : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hI_ne : I ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰)
    (hJ_ne : J ∈ (Ideal (𝓞 (CyclotomicField p ℚ)))⁰)
    (hI : Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) +
        ζ * (b : 𝓞 (CyclotomicField p ℚ))} : Set _) = I ^ p)
    (hJ : Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) +
        (cyclotomicRingOfIntegersEquiv (p := p) (CyclotomicField p ℚ) g ζ) *
          (b : 𝓞 (CyclotomicField p ℚ))} : Set _) = J ^ p) :
    cyclotomicGalActionOnClassGroup g (ClassGroup.mk0 ⟨I, hI_ne⟩) =
      ClassGroup.mk0 ⟨J, hJ_ne⟩ := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hmap : Furtwaengler.cyclotomicGaloisConjugate (p := p)
      (K := CyclotomicField p ℚ) g I = J := by
    apply ideal_pow_right_injective_ordIntegers (Fact.out (p := p.Prime)).ne_zero
    rw [← Furtwaengler.cyclotomicGaloisConjugate_pow_ideal, ← hI, ← hJ]
    unfold Furtwaengler.cyclotomicGaloisConjugate
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    rw [map_add, map_mul, map_intCast, map_intCast]
  rw [cyclotomicGalActionOnClassGroup_mk0]
  unfold cyclotomicGaloisShiftedClass cyclotomicGaloisConjugateNonZeroDivisors
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  exact hmap

end Eichler

end FLT37

end BernoulliRegular

end
