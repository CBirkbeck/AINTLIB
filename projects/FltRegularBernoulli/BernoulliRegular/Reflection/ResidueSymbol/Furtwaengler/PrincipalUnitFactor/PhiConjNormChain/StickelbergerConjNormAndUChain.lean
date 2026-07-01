module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.PhiConjNormChain.PhiProductConjNormAndSemiPrimary

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- If each actual prime Φ factor is semi-primary, then the actual
multiplicative ideal Φ element is semi-primary. -/
theorem PhiPrimeElement.PhiIdealElement.gamma_isSemiPrimary_of_primePhi_gamma_isSemiPrimary
    {A : Ideal (𝓞 K)}
    (ΦA : PhiPrimeElement.PhiIdealElement (p := p) (K := K) A)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors A),
        FLT37.IsSemiPrimary p (K := K) (ΦA.primePhi P hP).gamma) :
    FLT37.IsSemiPrimary p (K := K) ΦA.gamma := by
  rw [ΦA.gamma_eq_prod]
  apply isSemiPrimary_multiset_prod (p := p) (K := K)
  intro γ hγ
  obtain ⟨P, _, rfl⟩ := Multiset.mem_map.mp hγ
  exact h_prime_semi P.1 P.2

/-- Principal-ideal version: the actual principal Φ product is semi-primary
as soon as each of its actual prime Φ factors is semi-primary. -/
theorem phiPrincipalGamma_isSemiPrimary_of_prime_semi
    {α : 𝓞 K}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma) :
    FLT37.IsSemiPrimary p (K := K) Φα.gamma :=
  PhiPrimeElement.PhiIdealElement.gamma_isSemiPrimary_of_primePhi_gamma_isSemiPrimary
    (p := p) (K := K) Φα h_prime_semi

/-! ### Conjugation norm of the actual Φ product -/

/-- A multiset product of powers is the power of the multiset product. -/
theorem multiset_prod_map_pow_eq_prod_pow
    {ι M : Type*} [CommMonoid M] (m : Multiset ι) (f : ι → M) (n : ℕ) :
    (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons i m ih =>
      simp [ih, mul_pow]

/-- Complex conjugation norm of a multiset product. -/
theorem ringOfIntegersComplexConj_multiset_prod_mul_self
    [IsCMField K] (m : Multiset (𝓞 K)) :
    ringOfIntegersComplexConj K m.prod * m.prod =
      (m.map fun x => ringOfIntegersComplexConj K x * x).prod := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons x m ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, map_mul, ← ih]
      ring

/-- If each actual prime Φ factor has the expected conjugation norm, then the
actual ideal-level Φ product has conjugation norm `(NA)^p`.

This is the multiplicative U4 norm step: it uses the actual prime Φ factors,
not an arbitrary generator of the same Stickelberger ideal. -/
theorem PhiPrimeElement.PhiIdealElement.conj_mul_self_eq_absNorm_pow_of_prime_conj_norm
    [IsCMField K]
    {A : Ideal (𝓞 K)} (ΦA : PhiPrimeElement.PhiIdealElement (p := p) (K := K) A)
    (hA : A ≠ ⊥)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors A),
        ringOfIntegersComplexConj K (ΦA.primePhi P hP).gamma *
            (ΦA.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    ringOfIntegersComplexConj K ΦA.gamma * ΦA.gamma =
      (((Ideal.absNorm A : ℤ) : 𝓞 K)) ^ p := by
  classical
  calc
    ringOfIntegersComplexConj K ΦA.gamma * ΦA.gamma =
        (((normalizedFactors A).attach.map fun P =>
          ringOfIntegersComplexConj K (ΦA.primePhi P.1 P.2).gamma *
            (ΦA.primePhi P.1 P.2).gamma).prod) := by
          rw [ΦA.gamma_eq_prod]
          rw [ringOfIntegersComplexConj_multiset_prod_mul_self (K := K)]
          simp [Multiset.map_map]
    _ = (((normalizedFactors A).attach.map fun P =>
          (((Ideal.absNorm P.1 : ℤ) : 𝓞 K)) ^ p).prod) := by
          congr 1
          refine Multiset.map_congr rfl fun P _ => ?_
          exact h_prime_norm P.1 P.2
    _ = ((((normalizedFactors A).attach.map fun P =>
          (((Ideal.absNorm P.1 : ℤ) : 𝓞 K))).prod) ^ p) :=
          multiset_prod_map_pow_eq_prod_pow
            ((normalizedFactors A).attach)
            (fun P : { P // P ∈ normalizedFactors A } =>
              (((Ideal.absNorm P.1 : ℤ) : 𝓞 K))) p
    _ =
        (PhiPrimeElement.PhiIdealElement.idealNormFactorElement
          (p := p) (K := K) A) ^ p := by
          congr 1
          unfold PhiPrimeElement.PhiIdealElement.idealNormFactorElement
          exact congrArg Multiset.prod
            (Multiset.attach_map_val' (normalizedFactors A)
              (fun P : Ideal (𝓞 K) => (((Ideal.absNorm P : ℤ) : 𝓞 K))))
    _ = (((Ideal.absNorm A : ℤ) : 𝓞 K)) ^ p := by
          rw [PhiPrimeElement.PhiIdealElement.idealNormFactorElement_eq_absNorm
            (p := p) (K := K) hA]

/-- Principal-ideal version of the actual Φ conjugation-norm product theorem. -/
theorem phiPrincipal_conj_mul_self_eq_absNorm_pow_of_prime_conj_norm
    [IsCMField K]
    {α : 𝓞 K} (hα : α ≠ 0)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
      (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
        𝓞 K)) ^ p := by
  have hA : Ideal.span ({α} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hα
  exact Φα.conj_mul_self_eq_absNorm_pow_of_prime_conj_norm
    (p := p) (K := K) hA h_prime_norm

/-- If `α` is semi-primary, then the Stickelberger principal generator
`α^Θ` is semi-primary. -/
theorem isSemiPrimary_stickelbergerPrincipalGen
    (hp_two : 2 ≤ p) {α : 𝓞 K}
    (hα : FLT37.IsSemiPrimary p (K := K) α) :
    FLT37.IsSemiPrimary p (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) α) := by
  unfold stickelbergerPrincipalGen
  refine isSemiPrimary_finset_prod
    (p := p) (K := K) (Finset.univ : Finset (CyclotomicUnitDelta p))
    (fun a =>
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^
        ((a : ZMod p).val)) ?_
  intro a _
  exact isSemiPrimary_pow
    (p := p) (K := K)
    (isSemiPrimary_cyclotomicRingOfIntegersEquiv
      (p := p) (K := K) hp_two a⁻¹ hα)
    ((a : ZMod p).val)

/-- If `α` is prime to `ζ - 1`, then so is the Stickelberger principal
generator `α^Θ`. -/
theorem not_zetaSubOne_dvd_stickelbergerPrincipalGen
    (hp_two : 2 ≤ p) {α : 𝓞 K}
    (hα : ¬ FLT37.zetaSubOne p K ∣ α) :
    ¬ FLT37.zetaSubOne p K ∣
      stickelbergerPrincipalGen (p := p) (K := K) α := by
  classical
  unfold stickelbergerPrincipalGen
  refine (FLT37.zetaSubOne_prime (p := p) (K := K)).not_dvd_finsetProd ?_
  intro a _
  have ha :
      ¬ FLT37.zetaSubOne p K ∣
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α :=
    not_zetaSubOne_dvd_cyclotomicRingOfIntegersEquiv
      (p := p) (K := K) hp_two a⁻¹ hα
  intro hpow
  exact ha ((FLT37.zetaSubOne_prime (p := p) (K := K)).dvd_of_dvd_pow hpow)

/-- If `α` is coprime to the rational prime `p` in the REF-18 sense
`Ideal.span {α, p} = ⊤`, then `α` is prime to the unique prime above `p`,
generated by `ζ_p - 1`. -/
theorem not_zetaSubOne_dvd_of_span_pair_p_eq_top
    (hp_three : 3 ≤ p) {α : 𝓞 K}
    (h_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤) :
    ¬ FLT37.zetaSubOne p K ∣ α := by
  intro hα_dvd
  let ε : 𝓞 K := FLT37.zetaSubOne p K
  have hε_sq_dvd_p_nat : ε ^ 2 ∣ ((p : ℕ) : 𝓞 K) := by
    simpa [ε] using FLT37.zetaSubOne_sq_dvd_p (p := p) (K := K) hp_three
  have hε_dvd_p : ε ∣ (p : 𝓞 K) :=
    (show ε ∣ ε ^ 2 from ⟨ε, by ring⟩).trans hε_sq_dvd_p_nat
  have hspan_le :
      Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) ≤
        Ideal.span ({ε} : Set (𝓞 K)) := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr (by simpa [ε] using hα_dvd)
    · exact Ideal.mem_span_singleton.mpr hε_dvd_p
  have h_one_mem : (1 : 𝓞 K) ∈ Ideal.span ({ε} : Set (𝓞 K)) :=
    hspan_le (by rw [h_top]; exact Submodule.mem_top)
  rw [Ideal.mem_span_singleton] at h_one_mem
  obtain ⟨w, hw⟩ := h_one_mem
  have hε_unit : IsUnit ε := by
    have hprod : IsUnit (ε * w) := by
      rw [← hw]
      exact isUnit_one
    exact isUnit_of_mul_isUnit_left hprod
  exact FLT37.zetaSubOne_not_isUnit (p := p) (K := K) (by simpa [ε] using hε_unit)

/-! ### Stickelberger principal generator under complex conjugation -/

/-- In an odd cyclotomic field, complex conjugation on `𝓞 K` is the
cyclotomic automorphism indexed by `-1`.

The proof compares the two rational Galois automorphisms on the field and
then restricts to the ring of integers. -/
theorem ringOfIntegersComplexConj_eq_cyclotomicRingOfIntegersEquiv_neg_one
    [IsCMField K] (hp_gt_two : 2 < p) (x : 𝓞 K) :
    ringOfIntegersComplexConj K x =
      cyclotomicRingOfIntegersEquiv (p := p) K (-1) x := by
  symm
  apply RingOfIntegers.ext
  change cyclotomicSigmaOfUnit (p := p) K (-1) (x : K) =
    complexConj K (x : K)
  rw [cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal (p := p) (K := K) hp_gt_two]
  rfl

/-- If complex conjugation is identified with the cyclotomic automorphism
indexed by `-1`, then conjugating the Stickelberger principal generator
reindexes the exponent in the expected way.

The separate identification hypothesis keeps this lemma independent of the
particular `IsCMField` instance used by downstream consumers. -/
theorem ringOfIntegersComplexConj_stickelbergerPrincipalGen_of_eq_sigma_neg_one
    [IsCMField K] {α : 𝓞 K}
    (hconj : ∀ x : 𝓞 K, ringOfIntegersComplexConj K x =
      cyclotomicRingOfIntegersEquiv (p := p) K (-1) x) :
    ringOfIntegersComplexConj K
        (stickelbergerPrincipalGen (p := p) (K := K) α) =
      ∏ a : CyclotomicUnitDelta p,
        (cyclotomicRingOfIntegersEquiv (p := p) K ((-a)⁻¹) α) ^
          ((a : ZMod p).val) := by
  unfold stickelbergerPrincipalGen
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_pow, hconj, ← cyclotomicRingOfIntegersEquiv_mul_apply]
  congr 2
  ext
  simp

/-- Product form of the conjugation calculation for the Stickelberger
principal generator.

After reindexing `a ↦ -a`, the two exponents add to `p`, so
`conj(α^Θ) * α^Θ` is the product of the `p`-th powers of all cyclotomic
conjugates of `α`. -/
theorem ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self_of_eq_sigma_neg_one
    [IsCMField K] {α : 𝓞 K}
    (hconj : ∀ x : 𝓞 K, ringOfIntegersComplexConj K x =
      cyclotomicRingOfIntegersEquiv (p := p) K (-1) x) :
    ringOfIntegersComplexConj K
        (stickelbergerPrincipalGen (p := p) (K := K) α) *
        stickelbergerPrincipalGen (p := p) (K := K) α =
      ∏ a : CyclotomicUnitDelta p,
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ p := by
  classical
  rw [ringOfIntegersComplexConj_stickelbergerPrincipalGen_of_eq_sigma_neg_one
    (p := p) (K := K) hconj]
  unfold stickelbergerPrincipalGen
  have h_reindex :
      (∏ a : CyclotomicUnitDelta p,
          (cyclotomicRingOfIntegersEquiv (p := p) K ((-a)⁻¹) α) ^
            ((a : ZMod p).val)) =
        ∏ a : CyclotomicUnitDelta p,
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^
            (((-a : CyclotomicUnitDelta p) : ZMod p).val) := by
    let e : CyclotomicUnitDelta p ≃ CyclotomicUnitDelta p := Equiv.neg _
    exact Fintype.prod_equiv e
      (fun a : CyclotomicUnitDelta p =>
        (cyclotomicRingOfIntegersEquiv (p := p) K ((-a)⁻¹) α) ^
          ((a : ZMod p).val))
      (fun a : CyclotomicUnitDelta p =>
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^
          (((-a : CyclotomicUnitDelta p) : ZMod p).val))
      (by
        intro a
        dsimp [e]
        simp)
  rw [h_reindex, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have ha_ne : (a : ZMod p) ≠ 0 := a.isUnit.ne_zero
  have hval_sum :
      (((-a : CyclotomicUnitDelta p) : ZMod p).val) + ((a : ZMod p).val) = p := by
    rw [show ((-a : CyclotomicUnitDelta p) : ZMod p) = -(a : ZMod p) by rfl]
    rw [ZMod.neg_val, if_neg ha_ne]
    have hpos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr ha_ne
    have hlt : (a : ZMod p).val < p := ZMod.val_lt _
    omega
  rw [← pow_add, hval_sum]

/-- In an odd cyclotomic field, conjugating the Stickelberger principal
generator reindexes the exponent in the expected way. -/
theorem ringOfIntegersComplexConj_stickelbergerPrincipalGen
    [IsCMField K] (hp_gt_two : 2 < p) {α : 𝓞 K} :
    ringOfIntegersComplexConj K
        (stickelbergerPrincipalGen (p := p) (K := K) α) =
      ∏ a : CyclotomicUnitDelta p,
        (cyclotomicRingOfIntegersEquiv (p := p) K ((-a)⁻¹) α) ^
          ((a : ZMod p).val) :=
  ringOfIntegersComplexConj_stickelbergerPrincipalGen_of_eq_sigma_neg_one
    (p := p) (K := K)
    (ringOfIntegersComplexConj_eq_cyclotomicRingOfIntegersEquiv_neg_one
      (p := p) (K := K) hp_gt_two)

/-- In an odd cyclotomic field,
`conj(α^Θ) * α^Θ` is the product of the `p`-th powers of all cyclotomic
conjugates of `α`. -/
theorem ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self
    [IsCMField K] (hp_gt_two : 2 < p) {α : 𝓞 K} :
    ringOfIntegersComplexConj K
        (stickelbergerPrincipalGen (p := p) (K := K) α) *
        stickelbergerPrincipalGen (p := p) (K := K) α =
      ∏ a : CyclotomicUnitDelta p,
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ p :=
  ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self_of_eq_sigma_neg_one
    (p := p) (K := K)
    (ringOfIntegersComplexConj_eq_cyclotomicRingOfIntegersEquiv_neg_one
      (p := p) (K := K) hp_gt_two)

/-! ### Stickelberger norm as the integer norm -/

end Furtwaengler

end BernoulliRegular

end

end
