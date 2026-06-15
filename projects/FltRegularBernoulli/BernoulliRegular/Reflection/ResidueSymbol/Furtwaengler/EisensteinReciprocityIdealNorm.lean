module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicConjugateNorm
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.EisensteinReciprocityBasic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdealElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolIdealGaloisAction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerPrincipalGen

/-!
# Ideal-norm denominator computations

This file contains the formal denominator computations used in the
ideal-norm form of Eisenstein reciprocity.  The principal ideal `(NB)` is the
product of all cyclotomic conjugates of `B`, and the ideal-level Galois action
converts that product into the Stickelberger principal generator.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- If `B` is coprime to `(p)`, every normalized prime factor of `B` avoids
`p`. -/
theorem natCast_notMem_of_isCoprime_span_natCast_of_mem_normalizedFactors
    {B P : Ideal (𝓞 K)}
    (hBp : IsCoprime B (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hP : P ∈ normalizedFactors B) :
    (p : 𝓞 K) ∉ P := by
  intro hp_mem
  obtain ⟨_, _hP_ne, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  have hB_le_P : B ≤ P := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hp_le_P : Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hp_mem
  have htop_le : ⊤ ≤ P := by
    rw [← hBp.sup_eq]
    exact sup_le hB_le_P hp_le_P
  exact hP_max.ne_top (top_le_iff.mp htop_le)

/-- The norm-principal coprimality condition says that no normalized prime
factor of `A` can contain the absolute norm of `B`. -/
theorem absNorm_notMem_of_idealNormPrincipal_coprime
    {A B P : Ideal (𝓞 K)}
    (hcop : IsCoprime (idealNormPrincipalIdeal (K := K) B) A)
    (hP : P ∈ normalizedFactors A) :
    algebraMap ℤ (𝓞 K) (B.absNorm : ℤ) ∉ P := by
  intro hmem
  obtain ⟨_, _hP_ne, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  have hnorm_le : idealNormPrincipalIdeal (K := K) B ≤ P := by
    rw [idealNormPrincipalIdeal, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hA_le : A ≤ P := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have htop_le : ⊤ ≤ P := by
    rw [← hcop.sup_eq]
    exact sup_le hnorm_le hA_le
  exact hP_max.ne_top (top_le_iff.mp htop_le)

/-- A prime factor of `A` also avoids the absolute norm of every normalized
prime factor of `B`, if `(NB)` is coprime to `A`. -/
theorem absNorm_factor_notMem_of_idealNormPrincipal_coprime
    {A B P Q : Ideal (𝓞 K)}
    (hcop : IsCoprime (idealNormPrincipalIdeal (K := K) B) A)
    (hP : P ∈ normalizedFactors A) (hQ : Q ∈ normalizedFactors B) :
    algebraMap ℤ (𝓞 K) (Q.absNorm : ℤ) ∉ P := by
  intro hmem
  have hnorm_not :
      algebraMap ℤ (𝓞 K) (B.absNorm : ℤ) ∉ P :=
    absNorm_notMem_of_idealNormPrincipal_coprime
      (K := K) hcop hP
  have hQ_dvd_B : Q ∣ B :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
  have hnorm_dvd : Q.absNorm ∣ B.absNorm :=
    map_dvd (Ideal.absNorm (S := 𝓞 K)) hQ_dvd_B
  obtain ⟨c, hc⟩ := hnorm_dvd
  apply hnorm_not
  rw [hc]
  have hcast :
      algebraMap ℤ (𝓞 K) ((Q.absNorm * c : ℕ) : ℤ) =
        algebraMap ℤ (𝓞 K) (Q.absNorm : ℤ) *
          algebraMap ℤ (𝓞 K) (c : ℤ) := by
    norm_num
  rw [hcast]
  exact P.mul_mem_right _ hmem

/-- The symbol of the absolute norm of `B` expands as the sum of the symbols
of the absolute norms of the prime factors of `B`, using the theorem's actual
norm-principal coprimality hypothesis. -/
theorem pthSymbolAtIdeal_canonical_absNorm_eq_sum_of_idealNormPrincipal_coprime
    {A B : Ideal (𝓞 K)} (hB : B ≠ ⊥)
    (hcop : IsCoprime (idealNormPrincipalIdeal (K := K) B) A) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (((B.absNorm : ℤ) : 𝓞 K)) A =
      ((normalizedFactors B).map fun Q =>
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          (((Ideal.absNorm Q : ℤ) : 𝓞 K)) A).sum := by
  rw [← PhiPrimeElement.PhiIdealElement.idealNormFactorElement_eq_absNorm
    (p := p) (K := K) hB]
  unfold PhiPrimeElement.PhiIdealElement.idealNormFactorElement
  rw [show
      ((normalizedFactors B).map fun Q : Ideal (𝓞 K) =>
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          (((Ideal.absNorm Q : ℤ) : 𝓞 K)) A) =
      (((normalizedFactors B).map fun Q : Ideal (𝓞 K) =>
        (((Ideal.absNorm Q : ℤ) : 𝓞 K))).map fun γ =>
          pthSymbolAtIdeal_canonical (p := p) (K := K) γ A) by
        simp [Multiset.map_map]]
  apply PhiPrimeElement.pthSymbolAtIdeal_canonical_multiset_prod_α
    (p := p) (K := K)
    ((normalizedFactors B).map fun Q : Ideal (𝓞 K) => (((Ideal.absNorm Q : ℤ) : 𝓞 K)))
    (I := A)
  intro γ hγ P hP
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hγ
  exact absNorm_factor_notMem_of_idealNormPrincipal_coprime
    (K := K) hcop hP hQ

/-- Denominator computation: `(α / NB)_p` is the same as
`(α^Θ / B)_p`, where `α^Θ` is the Stickelberger principal generator. -/
theorem pthSymbolAtIdeal_canonical_idealNormPrincipal_eq_principalGen
    {α : 𝓞 K} {B : Ideal (𝓞 K)} (hB : B ≠ ⊥)
    (hcop :
      IsCoprime (idealNormPrincipalIdeal (K := K) B)
        (Ideal.span ({α} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (idealNormPrincipalIdeal (K := K) B) =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B := by
  classical
  have hcop_span :
      IsCoprime
        (Ideal.span ({algebraMap ℤ (𝓞 K) (B.absNorm : ℤ)} : Set (𝓞 K)))
        (Ideal.span ({α} : Set (𝓞 K))) := by
    simpa [idealNormPrincipalIdeal] using hcop
  have h_coprime :
      ∀ (a : CyclotomicUnitDelta p) (P : Ideal (𝓞 K)),
        P ∈ normalizedFactors B →
          cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P := fun a P hP =>
    cyclotomicRingOfIntegersEquiv_inv_notMem_of_absNorm_span_coprime
      (p := p) (K := K) hB hcop_span a hP
  calc
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (idealNormPrincipalIdeal (K := K) B)
        =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (cyclotomicConjugateProductIdeal (p := p) (K := K) B) := by
          rw [idealNormPrincipalIdeal,
            ← cyclotomicConjugateProductIdeal_eq_absNorm_span
              (p := p) (K := K) hB]
    _ = ∑ a : CyclotomicUnitDelta p,
        pthSymbolAtIdeal_canonical (p := p) (K := K) α
          (cyclotomicGaloisConjugate (p := p) (K := K) a B) := by
          unfold cyclotomicConjugateProductIdeal
          rw [pthSymbolAtIdeal_canonical_finset_prod (p := p) Finset.univ
            (fun a : CyclotomicUnitDelta p =>
              cyclotomicGaloisConjugate (p := p) (K := K) a B) α]
          intro a _
          exact cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a hB
    _ = ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have hact :=
            pthSymbolAtIdeal_canonical_galoisAction_unconditional
              (p := p) (K := K) a
              (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) hB
          have hα :
              cyclotomicRingOfIntegersEquiv (p := p) K a
                  (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) = α := by
            rw [← cyclotomicRingOfIntegersEquiv_mul_apply
                (p := p) (K := K) a a⁻¹ α,
              mul_inv_cancel, cyclotomicRingOfIntegersEquiv_one_apply]
          have hval : ((a : ZMod p).val : ZMod p) = (a : ZMod p) :=
            ZMod.natCast_zmod_val (a : ZMod p)
          simpa [hα, hval] using hact
    _ =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B :=
          (pthSymbolAtIdeal_canonical_principalGen_left_eq_galois_sum
            (p := p) (K := K) α B h_coprime).symm

end Furtwaengler

end BernoulliRegular

end
