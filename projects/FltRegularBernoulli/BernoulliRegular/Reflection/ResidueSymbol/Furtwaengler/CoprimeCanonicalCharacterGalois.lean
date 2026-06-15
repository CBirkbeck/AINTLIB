module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CoprimeCanonicalCharacter
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolIdealGaloisAction
public import BernoulliRegular.Reflection.ClassGroupModP.GalAction

/-!
# Galois covariance for coprime canonical class characters

This file connects the bad-set-coprime class character to the already proved
ideal-level Galois action of the canonical residue symbol.

The statements deliberately keep the representative-avoidance hypotheses
explicit.  They do not use `Ref19UniversalHypothesis`; the only class
character involved is the coprime representative character built from
`pthSymbolAtIdeal_canonical`.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open UniqueFactorizationMonoid

namespace BernoulliRegular
namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace GaloisCovarianceAvoidance

/-- Galois conjugation distributes over ideal suprema. -/
theorem cyclotomicGaloisConjugate_sup
    (a : CyclotomicUnitDelta p) (I J : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (I ⊔ J) =
      cyclotomicGaloisConjugate (p := p) (K := K) a I ⊔
        cyclotomicGaloisConjugate (p := p) (K := K) a J := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_sup _ I J

/-- Coprimality is transported by Galois conjugation.  The input is stated
against the inverse-conjugate prime because this is the form produced by
finite ideal avoidance. -/
theorem isCoprime_cyclotomicGaloisConjugate_of_isCoprime_inv
    (a : CyclotomicUnitDelta p) {I P : Ideal (𝓞 K)}
    (hcop :
      IsCoprime I (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P)) :
    IsCoprime (cyclotomicGaloisConjugate (p := p) (K := K) a I) P := by
  rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
  have hmap := congrArg (cyclotomicGaloisConjugate (p := p) (K := K) a) hcop
  have hinv :
      cyclotomicGaloisConjugate (p := p) (K := K) a
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P) = P := by
    rw [← cyclotomicGaloisConjugate_mul, mul_inv_cancel,
      cyclotomicGaloisConjugate_one]
  simpa [cyclotomicGaloisConjugate_sup, hinv, cyclotomicGaloisConjugate_top] using hmap

/-- If an ideal is coprime to every normalized prime factor of a nonzero ideal
`J`, then it is coprime to `J`.  This local copy avoids making covariance
depend on the OSKR file. -/
theorem isCoprime_of_isCoprime_normalizedFactors_right
    {I J : Ideal (𝓞 K)} (hJ_ne : J ≠ ⊥)
    (hcop : ∀ P ∈ normalizedFactors J, IsCoprime I P) :
    IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  rw [← Ideal.prod_normalizedFactors_eq_self hJ_ne]
  exact Ideal.sup_multiset_prod_eq_top (by
    intro P hP
    exact Ideal.isCoprime_iff_sup_eq.mp (hcop P hP))

/-- If `I` is coprime to `(u)`, then no normalized prime factor of `I`
contains `u`. -/
theorem not_mem_of_normalizedFactor_of_isCoprime_span_singleton
    {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥) {u : 𝓞 K}
    (hcop : IsCoprime I (Ideal.span ({u} : Set (𝓞 K))))
    {Q : Ideal (𝓞 K)} (hQ : Q ∈ normalizedFactors I) :
    u ∉ Q := by
  intro huQ
  have hQ_fac := (Ideal.mem_normalizedFactors_iff hI_ne).mp hQ
  have htop_le : (⊤ : Ideal (𝓞 K)) ≤ Q := by
    rw [← Ideal.isCoprime_iff_sup_eq.mp hcop]
    exact sup_le hQ_fac.2 (by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      simpa [hx] using huQ)
  exact hQ_fac.1.ne_top (top_le_iff.mp htop_le)

/-- Build the representative-avoidance input for global Galois covariance from
one enlarged finite bad set.

The finite set `T` must contain:
* the original bad set `S`;
* inverse Galois transforms of primes in `S`;
* inverse Galois transforms of primes dividing `(u)`.

Choosing a representative coprime to `T` then gives exactly the three
avoidance hypotheses consumed by the class-level covariance theorem. -/
theorem exists_galois_covariance_representative
    (a : CyclotomicUnitDelta p) {u : 𝓞 K} (hu_ne : u ≠ 0)
    (S T : Finset (Ideal (𝓞 K)))
    (hTprime : ∀ P ∈ T, P.IsPrime)
    (hT_ne : ∀ P ∈ T, P ≠ ⊥)
    (hT_S : ∀ P ∈ S, P ∈ T)
    (hT_invS : ∀ P ∈ S,
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ∈ T)
    (hT_invu : ∀ Q ∈ normalizedFactors (Ideal.span ({u} : Set (𝓞 K))),
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈ T)
    (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = c ∧
      (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
      (∀ P ∈ S,
        IsCoprime
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
      (∀ Q ∈ normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
          u ∉ Q) := by
  obtain ⟨I, hI_class, hI_T⟩ :=
    Reflection.ResidueSymbol.IdealAvoidance.exists_class_representative_coprime_prime_finset
      (R := 𝓞 K) c T hTprime hT_ne
  refine ⟨I, hI_class, ?_, ?_, ?_⟩
  · intro P hP
    exact hI_T P (hT_S P hP)
  · intro P hP
    exact isCoprime_cyclotomicGaloisConjugate_of_isCoprime_inv
      (p := p) (K := K) a (hI_T _ (hT_invS P hP))
  · have hσI_ne :
        cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)) ≠ ⊥ :=
      cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a
        (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
    have hu_span_ne : Ideal.span ({u} : Set (𝓞 K)) ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hu_ne
    have hσI_coprime_u :
        IsCoprime
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)))
          (Ideal.span ({u} : Set (𝓞 K))) :=
      isCoprime_of_isCoprime_normalizedFactors_right
        (K := K) hu_span_ne (by
          intro Q hQ
          exact isCoprime_cyclotomicGaloisConjugate_of_isCoprime_inv
            (p := p) (K := K) a (hI_T _ (hT_invu Q hQ)))
    intro Q hQ
    exact not_mem_of_normalizedFactor_of_isCoprime_span_singleton
      (K := K) hσI_ne hσI_coprime_u hQ

/-- Build the representative-avoidance input for denominator-cleared global
Galois covariance.

This is the two-auxiliary-element variant of
`exists_galois_covariance_representative`: the enlarged finite set must also
contain inverse Galois transforms of the normalized prime factors of `(z)` and
`(w)`.  The chosen representative then makes both `z` and `w` avoid every
prime factor of the conjugated denominator. -/
theorem exists_galois_covariance_representative_two
    (a : CyclotomicUnitDelta p) {z w : 𝓞 K} (hz_ne : z ≠ 0) (hw_ne : w ≠ 0)
    (S T : Finset (Ideal (𝓞 K)))
    (hTprime : ∀ P ∈ T, P.IsPrime)
    (hT_ne : ∀ P ∈ T, P ≠ ⊥)
    (hT_S : ∀ P ∈ S, P ∈ T)
    (hT_invS : ∀ P ∈ S,
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ∈ T)
    (hT_invz : ∀ Q ∈ normalizedFactors (Ideal.span ({z} : Set (𝓞 K))),
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈ T)
    (hT_invw : ∀ Q ∈ normalizedFactors (Ideal.span ({w} : Set (𝓞 K))),
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈ T)
    (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = c ∧
      (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
      (∀ P ∈ S,
        IsCoprime
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
      (∀ Q ∈ normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
          z ∉ Q) ∧
      (∀ Q ∈ normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
          w ∉ Q) := by
  obtain ⟨I, hI_class, hI_T⟩ :=
    Reflection.ResidueSymbol.IdealAvoidance.exists_class_representative_coprime_prime_finset
      (R := 𝓞 K) c T hTprime hT_ne
  refine ⟨I, hI_class, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact hI_T P (hT_S P hP)
  · intro P hP
    exact isCoprime_cyclotomicGaloisConjugate_of_isCoprime_inv
      (p := p) (K := K) a (hI_T _ (hT_invS P hP))
  · have hσI_ne :
        cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)) ≠ ⊥ :=
      cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a
        (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
    have hz_span_ne : Ideal.span ({z} : Set (𝓞 K)) ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hz_ne
    have hσI_coprime_z :
        IsCoprime
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)))
          (Ideal.span ({z} : Set (𝓞 K))) :=
      isCoprime_of_isCoprime_normalizedFactors_right
        (K := K) hz_span_ne (by
          intro Q hQ
          exact isCoprime_cyclotomicGaloisConjugate_of_isCoprime_inv
            (p := p) (K := K) a (hI_T _ (hT_invz Q hQ)))
    intro Q hQ
    exact not_mem_of_normalizedFactor_of_isCoprime_span_singleton
      (K := K) hσI_ne hσI_coprime_z hQ
  · have hσI_ne :
        cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)) ≠ ⊥ :=
      cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a
        (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
    have hw_span_ne : Ideal.span ({w} : Set (𝓞 K)) ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hw_ne
    have hσI_coprime_w :
        IsCoprime
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)))
          (Ideal.span ({w} : Set (𝓞 K))) :=
      isCoprime_of_isCoprime_normalizedFactors_right
        (K := K) hw_span_ne (by
          intro Q hQ
          exact isCoprime_cyclotomicGaloisConjugate_of_isCoprime_inv
            (p := p) (K := K) a (hI_T _ (hT_invw Q hQ)))
    intro Q hQ
    exact not_mem_of_normalizedFactor_of_isCoprime_span_singleton
      (K := K) hσI_ne hσI_coprime_w hQ

end GaloisCovarianceAvoidance

/-- Prime-level numerator transform for an eigenspace relation
`σ_a η = η^(a^i) * u^p`, at primes avoiding both `η` and `u`. -/
theorem pthSymbolAtPrime_canonical_galois_numerator_of_pow_mul_pow_p
    {η u : 𝓞 K} {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    {Q : Ideal (𝓞 K)} (hbot : Q ≠ ⊥) (hmax : Q.IsMaximal)
    (hη : η ∉ Q) (huQ : u ∉ Q) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) Q =
      ((a : ZMod p).val ^ i : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K) η Q := by
  rw [hu]
  haveI hQ_prime : Q.IsPrime := hmax.isPrime
  have hη_pow : η ^ ((a : ZMod p).val ^ i : ℕ) ∉ Q := fun h =>
    hη (hQ_prime.mem_of_pow_mem _ h)
  have hu_pow : u ^ p ∉ Q := fun h =>
    huQ (hQ_prime.mem_of_pow_mem _ h)
  rw [pthSymbolAtPrime_canonical_mul hbot hmax hη_pow hu_pow,
    pthSymbolAtPrime_canonical_pow hbot hmax hη _,
    pthSymbolAtPrime_canonical_pow_p_eq_zero hbot hmax huQ, add_zero,
    Nat.cast_pow]

/-- Ideal-level numerator transform for an eigenspace relation
`σ_a η = η^(a^i) * u^p`, assuming `u` avoids every prime factor of the
denominator ideal. -/
theorem pthSymbolAtIdeal_canonical_galois_numerator_of_pow_mul_pow_p
    {η u : 𝓞 K} {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (I : Ideal (𝓞 K))
    (h_u_coprime : ∀ Q ∈ normalizedFactors I, u ∉ Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) I =
      ((a : ZMod p).val ^ i : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  unfold pthSymbolAtIdeal_canonical
  rw [show
      ((normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a η) P)).sum =
      ((normalizedFactors I).map
        (fun P => ((a : ZMod p).val ^ i : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K) η P)).sum from ?_]
  · rw [← Multiset.sum_map_mul_left]
  · apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro Q hQ
    obtain ⟨_, hQ_ne_bot, hQ_max⟩ := isPrime_of_mem_normalizedFactors hQ
    by_cases hη : η ∈ Q
    · have hη_pow : η ^ ((a : ZMod p).val ^ i : ℕ) ∈ Q := by
        haveI : Q.IsPrime := hQ_max.isPrime
        have ha_val_pos : 0 < (a : ZMod p).val :=
          ZMod.val_pos.mpr (Units.ne_zero a)
        have h_pos : 0 < (a : ZMod p).val ^ i :=
          pow_pos ha_val_pos i
        exact Q.pow_mem_of_mem hη _ h_pos
      have hσ_in : cyclotomicRingOfIntegersEquiv (p := p) K a η ∈ Q := by
        rw [hu]
        exact Q.mul_mem_right _ hη_pow
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hQ_ne_bot hQ_max hσ_in,
        pthSymbolAtPrime_canonical_eq_zero_of_mem hQ_ne_bot hQ_max hη, mul_zero]
    · exact pthSymbolAtPrime_canonical_galois_numerator_of_pow_mul_pow_p
        (p := p) (K := K) a hu hQ_ne_bot hQ_max hη (h_u_coprime Q hQ)

/-- Prime-level numerator transform for a denominator-cleared eigenspace
relation

`σ_a η * w^p = η^n * z^p`.

At primes avoiding `z` and `w`, the two auxiliary pth powers vanish in the
residue symbol, leaving the scalar `n`.  No integrality of a field quotient
is required. -/
theorem pthSymbolAtPrime_canonical_galois_numerator_of_clear_denominators
    {η z w : 𝓞 K} {n : ℕ} (a : CyclotomicUnitDelta p)
    (hn_pos : 0 < n)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    {Q : Ideal (𝓞 K)} (hbot : Q ≠ ⊥) (hmax : Q.IsMaximal)
    (hzQ : z ∉ Q) (hwQ : w ∉ Q) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) Q =
      (n : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K) η Q := by
  classical
  haveI hQ_prime : Q.IsPrime := hmax.isPrime
  have hz_pow : z ^ p ∉ Q := fun h =>
    hzQ (hQ_prime.mem_of_pow_mem p h)
  have hw_pow : w ^ p ∉ Q := fun h =>
    hwQ (hQ_prime.mem_of_pow_mem p h)
  by_cases hη : η ∈ Q
  · have hη_pow : η ^ n ∈ Q := Q.pow_mem_of_mem hη n hn_pos
    have hleft_mem :
        cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p ∈ Q := by
      rw [hclear]
      exact Q.mul_mem_right _ hη_pow
    have hση : cyclotomicRingOfIntegersEquiv (p := p) K a η ∈ Q :=
      (hQ_prime.mem_or_mem hleft_mem).resolve_right hw_pow
    rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hση,
      pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hη, mul_zero]
  · have hη_pow : η ^ n ∉ Q := fun h =>
      hη (hQ_prime.mem_of_pow_mem n h)
    have hright_not : η ^ n * z ^ p ∉ Q := fun h =>
      (hQ_prime.mem_or_mem h).elim hη_pow hz_pow
    have hση :
        cyclotomicRingOfIntegersEquiv (p := p) K a η ∉ Q := by
      intro hσ
      apply hright_not
      rw [← hclear]
      exact Q.mul_mem_right _ hσ
    have heq :=
      congrArg
        (fun x => pthSymbolAtPrime_canonical (p := p) (K := K) x Q)
        hclear
    change
      pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p) Q =
        pthSymbolAtPrime_canonical (p := p) (K := K) (η ^ n * z ^ p) Q at heq
    rw [pthSymbolAtPrime_canonical_mul (p := p) (K := K) hbot hmax hση hw_pow,
      pthSymbolAtPrime_canonical_pow_p_eq_zero (p := p) (K := K) hbot hmax hwQ,
      pthSymbolAtPrime_canonical_mul (p := p) (K := K) hbot hmax hη_pow hz_pow,
      pthSymbolAtPrime_canonical_pow (p := p) (K := K) hbot hmax hη n,
      pthSymbolAtPrime_canonical_pow_p_eq_zero (p := p) (K := K) hbot hmax hzQ,
      add_zero] at heq
    simpa [add_zero] using heq

/-- Ideal-level denominator-cleared numerator transform. -/
theorem pthSymbolAtIdeal_canonical_galois_numerator_of_clear_denominators
    {η z w : 𝓞 K} {n : ℕ} (a : CyclotomicUnitDelta p)
    (hn_pos : 0 < n)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    (I : Ideal (𝓞 K))
    (h_z_coprime : ∀ Q ∈ normalizedFactors I, z ∉ Q)
    (h_w_coprime : ∀ Q ∈ normalizedFactors I, w ∉ Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) I =
      (n : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  unfold pthSymbolAtIdeal_canonical
  rw [show
      ((normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a η) P)).sum =
      ((normalizedFactors I).map
        (fun P => (n : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K) η P)).sum from ?_]
  · rw [← Multiset.sum_map_mul_left]
  · apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro Q hQ
    obtain ⟨_, hQ_ne_bot, hQ_max⟩ := isPrime_of_mem_normalizedFactors hQ
    exact pthSymbolAtPrime_canonical_galois_numerator_of_clear_denominators
      (p := p) (K := K) (η := η) (z := z) (w := w) (n := n)
      a hn_pos hclear hQ_ne_bot hQ_max (h_z_coprime Q hQ) (h_w_coprime Q hQ)

/-- Pre-divided ideal-level reflected-weight formula for the canonical residue
symbol. -/
theorem pthSymbolAtIdeal_canonical_galois_weight_one_minus_i_coprime
    {η u : 𝓞 K} {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h_u_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a I), u ∉ Q) :
    ((a : ZMod p).val ^ i : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (cyclotomicGaloisConjugate (p := p) (K := K) a I) =
      (a : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  rw [← pthSymbolAtIdeal_canonical_galois_numerator_of_pow_mul_pow_p
    (p := p) (K := K) a hu
    (cyclotomicGaloisConjugate (p := p) (K := K) a I) h_u_coprime_σ]
  exact pthSymbolAtIdeal_canonical_galoisAction_unconditional
    (p := p) (K := K) a η hI

/-- Representative-level Galois covariance for the bad-set-coprime canonical
character, in pre-divided reflected-weight form.

If `σ_a η = η^(a^i) * u^p`, then ideal-level covariance gives

`a^i * (η / σ_a I) = a * (η / I)`.

The hypotheses say that both representatives needed to evaluate the coprime
class character are admissible for the chosen bad set, and that the auxiliary
factor `u` is coprime to the conjugated denominator so that the numerator
`u^p` vanishes in the residue symbol. -/
theorem coprimeCanonicalClassGroupModPHom_galois_weight_one_minus_i_mk0
    (η u : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hσI : ∀ P ∈ S,
      IsCoprime (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P)
    (h_u_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))), u ∉ Q) :
    ((a : ZMod p).val ^ i : ZMod p) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
            (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p))).toAdd =
      (a : ZMod p) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd := by
  let σI : (Ideal (𝓞 K))⁰ :=
    ⟨cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)),
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩
  have hgal :
      cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
          (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) =
        (QuotientGroup.mk (ClassGroup.mk0 σI) : ClassGroupModP K p) := by
    change QuotientGroup.map _ _
        (cyclotomicGalActionMonoidHom (p := p) (K := K) a) _
        (QuotientGroup.mk (ClassGroup.mk0 I)) =
      QuotientGroup.mk (ClassGroup.mk0 σI)
    rw [QuotientGroup.map_mk]
    congr 1
    change cyclotomicGalActionOnClassGroup (p := p) (K := K) a (ClassGroup.mk0 I) =
      ClassGroup.mk0 σI
    rw [cyclotomicGalActionOnClassGroup_mk0]
    rfl
  have hσI' : ∀ P ∈ S, IsCoprime (σI : Ideal (𝓞 K)) P := by
    simpa [σI] using hσI
  have hσ_eval :=
    coprimeCanonicalClassGroupModPHom_mk0
      (p := p) (K := K) η S hSprime hS_ne hclass σI hσI'
  have hI_eval :=
    coprimeCanonicalClassGroupModPHom_mk0
      (p := p) (K := K) η S hSprime hS_ne hclass I hI
  have hI_ne : (I : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hweight :=
    pthSymbolAtIdeal_canonical_galois_weight_one_minus_i_coprime
      (p := p) (K := K) (η := η) (u := u) (i := i) a hu hI_ne
      h_u_coprime_σ
  rw [hgal, hσ_eval, hI_eval]
  exact hweight

/-- Divided form of
`coprimeCanonicalClassGroupModPHom_galois_weight_one_minus_i_mk0`.

The pre-divided covariance is the form naturally produced by the residue
symbol calculation.  Since `a^i` is nonzero in `ZMod p`, it can be cancelled,
leaving the reflected scalar `a / a^i`. -/
theorem coprimeCanonicalClassGroupModPHom_galois_divided_weight_mk0
    (η u : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hσI : ∀ P ∈ S,
      IsCoprime (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P)
    (h_u_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))), u ∉ Q) :
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p))).toAdd =
      ((a : ZMod p) / (((a : ZMod p).val : ZMod p) ^ i)) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd := by
  let c : ZMod p := ((a : ZMod p).val : ZMod p) ^ i
  let χσ : ZMod p :=
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p))).toAdd
  let χ : ZMod p :=
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd
  have hc : c ≠ 0 := by
    dsimp [c]
    exact pow_ne_zero i (by
      rw [ZMod.natCast_zmod_val]
      exact Units.ne_zero a)
  have hpre :
      c * χσ = (a : ZMod p) * χ := by
    dsimp [c, χσ, χ]
    exact coprimeCanonicalClassGroupModPHom_galois_weight_one_minus_i_mk0
      (p := p) (K := K) η u S hSprime hS_ne hclass a hu I
      hI hσI h_u_coprime_σ
  calc
    χσ = c⁻¹ * (c * χσ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = c⁻¹ * ((a : ZMod p) * χ) := by rw [hpre]
    _ = ((a : ZMod p) / c) * χ := by
      rw [div_eq_mul_inv]
      ring

/-- ClassGroupModP-level Galois covariance for the bad-set-coprime canonical
character, with the representative-avoidance obligation kept explicit.

The input `hrep` is the concrete avoidance statement needed to apply the
representative-level theorem to every class: for each class `c`, choose an
integral representative `I` of `c` such that `I`, its Galois conjugate, and
the auxiliary `p`-power factor `u` all avoid the required primes. -/
theorem coprimeCanonicalClassGroupModPHom_galois_divided_weight
    (η u : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            u ∉ Q))
    (v : Additive (ClassGroupModP K p)) :
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionInstance (p := p) (K := K) a v).toMul).toAdd =
      ((a : ZMod p) / (((a : ZMod p).val : ZMod p) ^ i)) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass v.toMul).toAdd := by
  obtain ⟨x, rfl⟩ :
      ∃ x : ClassGroupModP K p, Additive.ofMul x = v := ⟨v.toMul, rfl⟩
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨I, hI_class, hI, hσI, h_u_coprime_σ⟩ := hrep c
  change
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk c : ClassGroupModP K p))).toAdd =
      ((a : ZMod p) / (((a : ZMod p).val : ZMod p) ^ i)) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (QuotientGroup.mk c : ClassGroupModP K p)).toAdd
  rw [← hI_class]
  exact coprimeCanonicalClassGroupModPHom_galois_divided_weight_mk0
    (p := p) (K := K) η u S hSprime hS_ne hclass a hu I hI hσI h_u_coprime_σ

/-- Linear form of
`coprimeCanonicalClassGroupModPHom_galois_divided_weight`. -/
theorem coprimeCanonicalClassGroupModPLinear_galois_divided_weight
    (η u : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            u ∉ Q))
    (v : Additive (ClassGroupModP K p)) :
    coprimeCanonicalClassGroupModPLinear
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) / (((a : ZMod p).val : ZMod p) ^ i)) *
        coprimeCanonicalClassGroupModPLinear
          (p := p) (K := K) η S hSprime hS_ne hclass v :=
  coprimeCanonicalClassGroupModPHom_galois_divided_weight
    (p := p) (K := K) η u S hSprime hS_ne hclass a hu hrep v

/-- Scalar conversion for the divided covariance factor:
`a / a^i = a^(p-i)` in `ZMod p`, for `i <= p`. -/
theorem zmod_div_val_pow_eq_pow_p_sub_i
    (a : CyclotomicUnitDelta p) {i : ℕ} (hi : i ≤ p) :
    ((a : ZMod p) / (((a : ZMod p).val : ZMod p) ^ i)) =
      (a : ZMod p) ^ (p - i) := by
  have h_fermat : (a : ZMod p) ^ p = (a : ZMod p) := ZMod.pow_card _
  have h_a_unit : IsUnit ((a : ZMod p) ^ i) := (Units.isUnit a).pow i
  have h_a_ne : (a : ZMod p) ^ i ≠ 0 := h_a_unit.ne_zero
  have hpow :
      (a : ZMod p) ^ (p - i) = (a : ZMod p) * ((a : ZMod p) ^ i)⁻¹ := by
    apply mul_right_cancel₀ h_a_ne
    rw [mul_assoc, IsUnit.inv_mul_cancel h_a_unit, mul_one, ← pow_add,
      Nat.sub_add_cancel hi]
    exact h_fermat
  rw [ZMod.natCast_zmod_val, hpow, div_eq_mul_inv]

/-- Linear Galois covariance with the reflected scalar written as
`(a : ZMod p)^(p-i)`. -/
theorem coprimeCanonicalClassGroupModPLinear_galois_pow_p_sub_i
    (η u : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {i : ℕ} (hi : i ≤ p) (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            u ∉ Q))
    (v : Additive (ClassGroupModP K p)) :
    coprimeCanonicalClassGroupModPLinear
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) ^ (p - i)) *
        coprimeCanonicalClassGroupModPLinear
          (p := p) (K := K) η S hSprime hS_ne hclass v := by
  rw [← zmod_div_val_pow_eq_pow_p_sub_i (p := p) a hi]
  exact coprimeCanonicalClassGroupModPLinear_galois_divided_weight
    (p := p) (K := K) η u S hSprime hS_ne hclass a hu hrep v

/-- Pre-divided ideal-level reflected-weight formula with denominator clearing. -/
theorem pthSymbolAtIdeal_canonical_galois_weight_one_minus_i_clear_denominators
    {η z w : 𝓞 K} {n : ℕ} (a : CyclotomicUnitDelta p)
    (hn_pos : 0 < n)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h_z_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a I), z ∉ Q)
    (h_w_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a I), w ∉ Q) :
    (n : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (cyclotomicGaloisConjugate (p := p) (K := K) a I) =
      (a : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  rw [← pthSymbolAtIdeal_canonical_galois_numerator_of_clear_denominators
    (p := p) (K := K) a hn_pos hclear
    (cyclotomicGaloisConjugate (p := p) (K := K) a I)
    h_z_coprime_σ h_w_coprime_σ]
  exact pthSymbolAtIdeal_canonical_galoisAction_unconditional
    (p := p) (K := K) a η hI

/-- Representative-level Galois covariance for the bad-set-coprime canonical
character from a denominator-cleared numerator relation. -/
theorem coprimeCanonicalClassGroupModPHom_galois_weight_one_minus_i_mk0_clear_denominators
    (η z w : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {n : ℕ} (a : CyclotomicUnitDelta p)
    (hn_pos : 0 < n)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hσI : ∀ P ∈ S,
      IsCoprime (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P)
    (h_z_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))), z ∉ Q)
    (h_w_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))), w ∉ Q) :
    (n : ZMod p) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
            (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p))).toAdd =
      (a : ZMod p) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd := by
  let σI : (Ideal (𝓞 K))⁰ :=
    ⟨cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K)),
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩
  have hgal :
      cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
          (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) =
        (QuotientGroup.mk (ClassGroup.mk0 σI) : ClassGroupModP K p) := by
    change QuotientGroup.map _ _
        (cyclotomicGalActionMonoidHom (p := p) (K := K) a) _
        (QuotientGroup.mk (ClassGroup.mk0 I)) =
      QuotientGroup.mk (ClassGroup.mk0 σI)
    rw [QuotientGroup.map_mk]
    congr 1
    change cyclotomicGalActionOnClassGroup (p := p) (K := K) a (ClassGroup.mk0 I) =
      ClassGroup.mk0 σI
    rw [cyclotomicGalActionOnClassGroup_mk0]
    rfl
  have hσI' : ∀ P ∈ S, IsCoprime (σI : Ideal (𝓞 K)) P := by
    simpa [σI] using hσI
  have hσ_eval :=
    coprimeCanonicalClassGroupModPHom_mk0
      (p := p) (K := K) η S hSprime hS_ne hclass σI hσI'
  have hI_eval :=
    coprimeCanonicalClassGroupModPHom_mk0
      (p := p) (K := K) η S hSprime hS_ne hclass I hI
  have hI_ne : (I : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hweight :=
    pthSymbolAtIdeal_canonical_galois_weight_one_minus_i_clear_denominators
      (p := p) (K := K) (η := η) (z := z) (w := w) (n := n) a
      hn_pos hclear hI_ne h_z_coprime_σ h_w_coprime_σ
  rw [hgal, hσ_eval, hI_eval]
  exact hweight

/-- Divided representative-level denominator-cleared covariance. -/
theorem coprimeCanonicalClassGroupModPHom_galois_divided_weight_mk0_clear_denominators
    (η z w : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {n : ℕ} (a : CyclotomicUnitDelta p)
    (hn_pos : 0 < n) (hn_ne : (n : ZMod p) ≠ 0)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hσI : ∀ P ∈ S,
      IsCoprime (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P)
    (h_z_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))), z ∉ Q)
    (h_w_coprime_σ : ∀ Q ∈ normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))), w ∉ Q) :
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p))).toAdd =
      ((a : ZMod p) / (n : ZMod p)) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd := by
  let c : ZMod p := n
  let χσ : ZMod p :=
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p))).toAdd
  let χ : ZMod p :=
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd
  have hpre :
      c * χσ = (a : ZMod p) * χ := by
    dsimp [c, χσ, χ]
    exact coprimeCanonicalClassGroupModPHom_galois_weight_one_minus_i_mk0_clear_denominators
      (p := p) (K := K) η z w S hSprime hS_ne hclass a hn_pos hclear I
      hI hσI h_z_coprime_σ h_w_coprime_σ
  calc
    χσ = c⁻¹ * (c * χσ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]
    _ = c⁻¹ * ((a : ZMod p) * χ) := by rw [hpre]
    _ = ((a : ZMod p) / c) * χ := by
      rw [div_eq_mul_inv]
      ring

/-- ClassGroupModP-level denominator-cleared covariance. -/
theorem coprimeCanonicalClassGroupModPHom_galois_divided_weight_clear_denominators
    (η z w : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {n : ℕ} (a : CyclotomicUnitDelta p)
    (hn_pos : 0 < n) (hn_ne : (n : ZMod p) ≠ 0)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    (hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            z ∉ Q) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            w ∉ Q))
    (v : Additive (ClassGroupModP K p)) :
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionInstance (p := p) (K := K) a v).toMul).toAdd =
      ((a : ZMod p) / (n : ZMod p)) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass v.toMul).toAdd := by
  obtain ⟨x, rfl⟩ :
      ∃ x : ClassGroupModP K p, Additive.ofMul x = v := ⟨v.toMul, rfl⟩
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨I, hI_class, hI, hσI, h_z_coprime_σ, h_w_coprime_σ⟩ := hrep c
  change
    (coprimeCanonicalClassGroupModPHom
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk c : ClassGroupModP K p))).toAdd =
      ((a : ZMod p) / (n : ZMod p)) *
        (coprimeCanonicalClassGroupModPHom
            (p := p) (K := K) η S hSprime hS_ne hclass
          (QuotientGroup.mk c : ClassGroupModP K p)).toAdd
  rw [← hI_class]
  exact coprimeCanonicalClassGroupModPHom_galois_divided_weight_mk0_clear_denominators
    (p := p) (K := K) η z w S hSprime hS_ne hclass a hn_pos hn_ne hclear I
    hI hσI h_z_coprime_σ h_w_coprime_σ

/-- Linear form of denominator-cleared divided covariance. -/
theorem coprimeCanonicalClassGroupModPLinear_galois_divided_weight_clear_denominators
    (η z w : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {n : ℕ} (a : CyclotomicUnitDelta p)
    (hn_pos : 0 < n) (hn_ne : (n : ZMod p) ≠ 0)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    (hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            z ∉ Q) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            w ∉ Q))
    (v : Additive (ClassGroupModP K p)) :
    coprimeCanonicalClassGroupModPLinear
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) / (n : ZMod p)) *
        coprimeCanonicalClassGroupModPLinear
          (p := p) (K := K) η S hSprime hS_ne hclass v :=
  coprimeCanonicalClassGroupModPHom_galois_divided_weight_clear_denominators
    (p := p) (K := K) η z w S hSprime hS_ne hclass a hn_pos hn_ne hclear hrep v

/-- Linear denominator-cleared Galois covariance with the reflected scalar
written as `(a : ZMod p)^(p-i)`. -/
theorem coprimeCanonicalClassGroupModPLinear_galois_pow_p_sub_i_clear_denominators
    (η z w : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    {i n : ℕ} (hi : i ≤ p) (a : CyclotomicUnitDelta p)
    (hn : (n : ZMod p) = (a : ZMod p) ^ i)
    (hn_pos : 0 < n)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    (hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            z ∉ Q) ∧
        (∀ Q ∈ normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a (I : Ideal (𝓞 K))),
            w ∉ Q))
    (v : Additive (ClassGroupModP K p)) :
    coprimeCanonicalClassGroupModPLinear
        (p := p) (K := K) η S hSprime hS_ne hclass
      (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) ^ (p - i)) *
        coprimeCanonicalClassGroupModPLinear
          (p := p) (K := K) η S hSprime hS_ne hclass v := by
  have hn_ne : (n : ZMod p) ≠ 0 := by
    rw [hn]
    exact pow_ne_zero i (Units.ne_zero a)
  have hfactor :
      ((a : ZMod p) / (n : ZMod p)) = (a : ZMod p) ^ (p - i) := by
    rw [hn]
    simpa [ZMod.natCast_zmod_val] using
      zmod_div_val_pow_eq_pow_p_sub_i (p := p) a hi
  rw [← hfactor]
  exact coprimeCanonicalClassGroupModPLinear_galois_divided_weight_clear_denominators
    (p := p) (K := K) η z w S hSprime hS_ne hclass a hn_pos hn_ne hclear hrep v

end Furtwaengler
end BernoulliRegular

end
