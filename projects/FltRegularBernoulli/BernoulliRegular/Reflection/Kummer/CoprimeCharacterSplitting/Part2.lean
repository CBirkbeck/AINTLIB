module

public import BernoulliRegular.Reflection.Kummer.CoprimeCharacterSplitting.Part1

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open Polynomial UniqueFactorizationMonoid

namespace BernoulliRegular
namespace Reflection
namespace Kummer

open BernoulliRegular.Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

attribute [local instance] splittingFieldNumberField_coprimeCharacterSplitting
attribute [local instance] quotientField_coprimeCharacterSplitting
attribute [local instance] quotientDecidableEq_coprimeCharacterSplitting
attribute [local instance] quotientNormalizationMonoid_coprimeCharacterSplitting
attribute [local instance] quotientUniqueFactorizationMonoid_coprimeCharacterSplitting
attribute [local instance] quotientPolynomialNormalizationMonoid_coprimeCharacterSplitting
attribute [local instance] quotientPolynomialDecidableEq_coprimeCharacterSplitting
attribute [local instance] quotientPolynomialUniqueFactorizationMonoid_coprimeCharacterSplitting

theorem locallyPrimaryCoprimeCanonicalClassGroupModPHom_ne_one_of_not_isPow_badSet
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @Furtwaengler.IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p) :
    Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPHom
        (p := p) (K := K) hp_odd η B
        (kummerCharacterBadSet (p := p) (K := K) η)
        (kummerCharacterBadSet_isPrime (p := p) (K := K) η hη_ne
          (splittingFieldRootConductorComap_ne_bot
            (p := p) (K := K) hp_ne_two η hη_not_pow))
        (kummerCharacterBadSet_ne_bot (p := p) (K := K) η hη_ne
          (splittingFieldRootConductorComap_ne_bot
            (p := p) (K := K) hp_ne_two η hη_not_pow))
        hη_ne hη_prime_to_p hη_local hsing
        (by intro P hP; simp [kummerCharacterBadSet, hP])
        (by intro P hP; simp [kummerCharacterBadSet, hP]) ≠ 1 := by
  haveI : NumberField (SplittingField (X ^ p - C (η : K))) :=
    splittingField_X_pow_sub_C_numberField (p := p) (K := K) (η := (η : K))
  exact
    coprimeCanonicalClassGroupModPHom_ne_one_of_not_isPow_badSet
      (p := p) (K := K) hp_ne_two η hη_ne hη_not_pow
      (fun {_ _} hI hJ hmk ↦
        Furtwaengler.pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_locallyPrimaryPseudoUnit
          (p := p) (K := K) hp_odd η B
          (kummerCharacterBadSet (p := p) (K := K) η)
          (kummerCharacterBadSet_isPrime (p := p) (K := K) η hη_ne
            (splittingFieldRootConductorComap_ne_bot
              (p := p) (K := K) hp_ne_two η hη_not_pow))
          (kummerCharacterBadSet_ne_bot (p := p) (K := K) η hη_ne
            (splittingFieldRootConductorComap_ne_bot
              (p := p) (K := K) hp_ne_two η hη_not_pow))
          hη_ne hη_prime_to_p hη_local hsing
          (by intro P hP; simp [kummerCharacterBadSet, hP])
          (by intro P hP; simp [kummerCharacterBadSet, hP])
          hI hJ hmk)

/-- Linear-form version of
`locallyPrimaryCoprimeCanonicalClassGroupModPHom_ne_one_of_not_isPow_badSet`.

The produced `ZMod p`-linear form is nonzero on some class in
`ClassGroupModP`. -/
theorem locallyPrimaryCoprimeCanonicalClassGroupModPLinear_nontrivial_of_not_isPow_badSet
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @Furtwaengler.IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p) :
    ∃ v : Additive (ClassGroupModP K p),
      Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPLinear
        (p := p) (K := K) hp_odd η B
        (kummerCharacterBadSet (p := p) (K := K) η)
        (kummerCharacterBadSet_isPrime (p := p) (K := K) η hη_ne
          (splittingFieldRootConductorComap_ne_bot
            (p := p) (K := K) hp_ne_two η hη_not_pow))
        (kummerCharacterBadSet_ne_bot (p := p) (K := K) η hη_ne
          (splittingFieldRootConductorComap_ne_bot
            (p := p) (K := K) hp_ne_two η hη_not_pow))
        hη_ne hη_prime_to_p hη_local hsing
        (by intro P hP; simp [kummerCharacterBadSet, hP])
        (by intro P hP; simp [kummerCharacterBadSet, hP]) v ≠ 0 := by
  haveI : NumberField (SplittingField (X ^ p - C (η : K))) :=
    splittingField_X_pow_sub_C_numberField (p := p) (K := K) (η := (η : K))
  let S := kummerCharacterBadSet (p := p) (K := K) η
  let hSprime :=
    kummerCharacterBadSet_isPrime (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow)
  let hS_ne :=
    kummerCharacterBadSet_ne_bot (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow)
  let hS_eta :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({η} : Set (𝓞 K))), P ∈ S := by
    intro P hP
    simp [S, kummerCharacterBadSet, hP]
  let hS_p :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S := by
    intro P hP
    simp [S, kummerCharacterBadSet, hP]
  let χ :=
    Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPHom
      (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
      hη_prime_to_p hη_local hsing hS_eta hS_p
  let φ :=
    Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPLinear
      (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
      hη_prime_to_p hη_local hsing hS_eta hS_p
  have hχ : χ ≠ 1 := by
    simpa [χ, S, hSprime, hS_ne, hS_eta, hS_p] using
      locallyPrimaryCoprimeCanonicalClassGroupModPHom_ne_one_of_not_isPow_badSet
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hsing
  by_contra hφ_zero
  push Not at hφ_zero
  apply hχ
  ext x
  have hx := hφ_zero (Additive.ofMul x)
  change (χ x).toAdd = 0 at hx
  exact Multiplicative.ext hx

/-- The canonical Kummer-bad-set residue-symbol character attached to a
locally-primary pseudo-unit, in linear form.

The parameters `hη_ne` and `hη_not_pow` are used only to prove that the
canonical Kummer bad set consists of nonzero prime ideals. -/
noncomputable def locallyPrimaryKummerBadSetClassGroupModPLinear
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @Furtwaengler.IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p) :
    Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p :=
  Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPLinear
    (p := p) (K := K) hp_odd η B
    (kummerCharacterBadSet (p := p) (K := K) η)
    (kummerCharacterBadSet_isPrime (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow))
    (kummerCharacterBadSet_ne_bot (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow))
    hη_ne hη_prime_to_p hη_local hsing
    (by intro P hP; simp [kummerCharacterBadSet, hP])
    (by intro P hP; simp [kummerCharacterBadSet, hP])

/-- Galois covariance of the WR-05 Kummer bad-set character.

This is the WR-06 globalization step for the concrete pseudo-unit character:
the enlarged avoidance set is built from the Kummer bad set, its inverse
Galois translate, and the inverse translates of the prime factors of the
auxiliary `p`-th-power witness `(u)`. -/
theorem locallyPrimaryKummerBadSetClassGroupModPLinear_galois_pow_p_sub_i
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @Furtwaengler.IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    {i : ℕ} (hi : i ≤ p) (a : CyclotomicUnitDelta p)
    (u : 𝓞 K)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (v : Additive (ClassGroupModP K p)) :
    locallyPrimaryKummerBadSetClassGroupModPLinear
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hsing
      (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) ^ (p - i)) *
        locallyPrimaryKummerBadSetClassGroupModPLinear
          (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
          hη_prime_to_p hη_local hsing v := by
  classical
  let S := kummerCharacterBadSet (p := p) (K := K) η
  let hSprime :=
    kummerCharacterBadSet_isPrime (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow)
  let hS_ne :=
    kummerCharacterBadSet_ne_bot (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow)
  let hS_eta :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({η} : Set (𝓞 K))), P ∈ S := by
    intro P hP
    simp [S, kummerCharacterBadSet, hP]
  let hS_p :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S := by
    intro P hP
    simp [S, kummerCharacterBadSet, hP]
  let hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        Furtwaengler.pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (I : Ideal (𝓞 K)) =
          Furtwaengler.pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (J : Ideal (𝓞 K)) :=
    fun hI hJ hmk ↦
      Furtwaengler.pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_locallyPrimaryPseudoUnit
        (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
        hη_prime_to_p hη_local hsing hS_eta hS_p hI hJ hmk
  have hση_ne :
      cyclotomicRingOfIntegersEquiv (p := p) K a η ≠ 0 := fun hzero ↦
    hη_ne <| (cyclotomicRingOfIntegersEquiv (p := p) K a).injective
      (hzero.trans (map_zero _).symm)
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    apply hση_ne
    rw [hu, hu_zero, zero_pow (Fact.out : Nat.Prime p).ne_zero, mul_zero]
  let Sinv : Finset (Ideal (𝓞 K)) :=
    S.image (fun P ↦ cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P)
  let Uinv : Finset (Ideal (𝓞 K)) :=
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({u} : Set (𝓞 K)))).toFinset.image
      (fun P ↦ cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P)
  let T : Finset (Ideal (𝓞 K)) := (S ∪ Sinv) ∪ Uinv
  have hTprime : ∀ P ∈ T, P.IsPrime := by
    intro P hP
    change P ∈ (S ∪ Sinv) ∪ Uinv at hP
    rw [Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Finset.mem_union] at hP
      rcases hP with hP | hP
      · exact hSprime P hP
      · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
        rw [← hQeq]
        haveI : Q.IsPrime := hSprime Q hQ
        exact cyclotomicGaloisConjugate_isPrime (p := p) (K := K) a⁻¹ Q
    · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
      rw [← hQeq]
      have hQ_nf :
          Q ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({u} : Set (𝓞 K))) := by
        simpa using hQ
      obtain ⟨hQ_prime, _hQ_ne, _hQ_max⟩ :=
        Furtwaengler.isPrime_of_mem_normalizedFactors (K := K) hQ_nf
      haveI : Q.IsPrime := hQ_prime
      exact cyclotomicGaloisConjugate_isPrime (p := p) (K := K) a⁻¹ Q
  have hT_ne : ∀ P ∈ T, P ≠ ⊥ := by
    intro P hP
    change P ∈ (S ∪ Sinv) ∪ Uinv at hP
    rw [Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Finset.mem_union] at hP
      rcases hP with hP | hP
      · exact hS_ne P hP
      · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
        rw [← hQeq]
        exact cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a⁻¹
          (hS_ne Q hQ)
    · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
      rw [← hQeq]
      have hQ_nf :
          Q ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({u} : Set (𝓞 K))) := by
        simpa using hQ
      obtain ⟨_hQ_prime, hQ_ne, _hQ_max⟩ :=
        Furtwaengler.isPrime_of_mem_normalizedFactors (K := K) hQ_nf
      exact cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a⁻¹ hQ_ne
  have hT_S : ∀ P ∈ S, P ∈ T := by
    intro P hP
    change P ∈ (S ∪ Sinv) ∪ Uinv
    rw [Finset.mem_union, Finset.mem_union]
    exact Or.inl (Or.inl hP)
  have hT_invS : ∀ P ∈ S,
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ∈ T := by
    intro P hP
    change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ∈
      (S ∪ Sinv) ∪ Uinv
    rw [Finset.mem_union, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨P, hP, rfl⟩))
  have hT_invu :
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({u} : Set (𝓞 K))),
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈ T := by
    intro Q hQ
    change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈
      (S ∪ Sinv) ∪ Uinv
    rw [Finset.mem_union]
    refine Or.inr ?_
    exact Finset.mem_image.mpr ⟨Q, by simpa using hQ, rfl⟩
  have hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a
              (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a
            (I : Ideal (𝓞 K))),
            u ∉ Q) := fun c ↦
    Furtwaengler.GaloisCovarianceAvoidance.exists_galois_covariance_representative
      (p := p) (K := K) a hu_ne S T hTprime hT_ne hT_S hT_invS hT_invu c
  have hcov :=
    Furtwaengler.coprimeCanonicalClassGroupModPLinear_galois_pow_p_sub_i
      (p := p) (K := K) η u S hSprime hS_ne hclass hi a hu hrep v
  simpa [locallyPrimaryKummerBadSetClassGroupModPLinear,
    Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPLinear,
    Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPHom,
    Furtwaengler.locallyPrimaryCoprimeCanonicalIdealSymbolData,
    Furtwaengler.coprimeCanonicalClassGroupModPLinear,
    Furtwaengler.coprimeCanonicalClassGroupModPHom,
    hclass, S, hSprime, hS_ne, hS_eta, hS_p] using hcov

/-- Galois covariance of the WR-05 Kummer bad-set character from a
denominator-cleared eigenspace relation.

This is the same concrete covariance as
`locallyPrimaryKummerBadSetClassGroupModPLinear_galois_pow_p_sub_i`, but it
accepts the natural singular-pair output
`σ_a η * w^p = η^n * z^p` rather than requiring the quotient `z / w` to be
integral. -/
theorem locallyPrimaryKummerBadSetClassGroupModPLinear_galois_pow_p_sub_i_clear_denominators
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @Furtwaengler.IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    {i n : ℕ} (hi : i ≤ p) (a : CyclotomicUnitDelta p)
    (z w : 𝓞 K)
    (hn : (n : ZMod p) = (a : ZMod p) ^ i)
    (hn_pos : 0 < n) (hz_ne : z ≠ 0) (hw_ne : w ≠ 0)
    (hclear :
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p)
    (v : Additive (ClassGroupModP K p)) :
    locallyPrimaryKummerBadSetClassGroupModPLinear
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hsing
      (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) ^ (p - i)) *
        locallyPrimaryKummerBadSetClassGroupModPLinear
          (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
          hη_prime_to_p hη_local hsing v := by
  classical
  let S := kummerCharacterBadSet (p := p) (K := K) η
  let hSprime :=
    kummerCharacterBadSet_isPrime (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow)
  let hS_ne :=
    kummerCharacterBadSet_ne_bot (p := p) (K := K) η hη_ne
      (splittingFieldRootConductorComap_ne_bot
        (p := p) (K := K) hp_ne_two η hη_not_pow)
  let hS_eta :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({η} : Set (𝓞 K))), P ∈ S := by
    intro P hP
    simp [S, kummerCharacterBadSet, hP]
  let hS_p :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S := by
    intro P hP
    simp [S, kummerCharacterBadSet, hP]
  let hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        Furtwaengler.pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (I : Ideal (𝓞 K)) =
          Furtwaengler.pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (J : Ideal (𝓞 K)) :=
    fun hI hJ hmk ↦
      Furtwaengler.pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_locallyPrimaryPseudoUnit
        (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
        hη_prime_to_p hη_local hsing hS_eta hS_p hI hJ hmk
  let Sinv : Finset (Ideal (𝓞 K)) :=
    S.image (fun P ↦ cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P)
  let Zinv : Finset (Ideal (𝓞 K)) :=
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({z} : Set (𝓞 K)))).toFinset.image
      (fun P ↦ cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P)
  let Winv : Finset (Ideal (𝓞 K)) :=
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({w} : Set (𝓞 K)))).toFinset.image
      (fun P ↦ cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P)
  let T : Finset (Ideal (𝓞 K)) := ((S ∪ Sinv) ∪ Zinv) ∪ Winv
  have hTprime : ∀ P ∈ T, P.IsPrime := by
    intro P hP
    change P ∈ ((S ∪ Sinv) ∪ Zinv) ∪ Winv at hP
    rw [Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Finset.mem_union] at hP
      rcases hP with hP | hP
      · rw [Finset.mem_union] at hP
        rcases hP with hP | hP
        · exact hSprime P hP
        · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
          rw [← hQeq]
          haveI : Q.IsPrime := hSprime Q hQ
          exact cyclotomicGaloisConjugate_isPrime (p := p) (K := K) a⁻¹ Q
      · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
        rw [← hQeq]
        have hQ_nf :
            Q ∈ UniqueFactorizationMonoid.normalizedFactors
                (Ideal.span ({z} : Set (𝓞 K))) := by
          simpa using hQ
        obtain ⟨hQ_prime, _hQ_ne, _hQ_max⟩ :=
          Furtwaengler.isPrime_of_mem_normalizedFactors (K := K) hQ_nf
        haveI : Q.IsPrime := hQ_prime
        exact cyclotomicGaloisConjugate_isPrime (p := p) (K := K) a⁻¹ Q
    · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
      rw [← hQeq]
      have hQ_nf :
          Q ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({w} : Set (𝓞 K))) := by
        simpa using hQ
      obtain ⟨hQ_prime, _hQ_ne, _hQ_max⟩ :=
        Furtwaengler.isPrime_of_mem_normalizedFactors (K := K) hQ_nf
      haveI : Q.IsPrime := hQ_prime
      exact cyclotomicGaloisConjugate_isPrime (p := p) (K := K) a⁻¹ Q
  have hT_ne : ∀ P ∈ T, P ≠ ⊥ := by
    intro P hP
    change P ∈ ((S ∪ Sinv) ∪ Zinv) ∪ Winv at hP
    rw [Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Finset.mem_union] at hP
      rcases hP with hP | hP
      · rw [Finset.mem_union] at hP
        rcases hP with hP | hP
        · exact hS_ne P hP
        · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
          rw [← hQeq]
          exact cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a⁻¹
            (hS_ne Q hQ)
      · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
        rw [← hQeq]
        have hQ_nf :
            Q ∈ UniqueFactorizationMonoid.normalizedFactors
                (Ideal.span ({z} : Set (𝓞 K))) := by
          simpa using hQ
        obtain ⟨_hQ_prime, hQ_ne, _hQ_max⟩ :=
          Furtwaengler.isPrime_of_mem_normalizedFactors (K := K) hQ_nf
        exact cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a⁻¹ hQ_ne
    · obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_image.mp hP
      rw [← hQeq]
      have hQ_nf :
          Q ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({w} : Set (𝓞 K))) := by
        simpa using hQ
      obtain ⟨_hQ_prime, hQ_ne, _hQ_max⟩ :=
        Furtwaengler.isPrime_of_mem_normalizedFactors (K := K) hQ_nf
      exact cyclotomicGaloisConjugate_ne_bot (p := p) (K := K) a⁻¹ hQ_ne
  have hT_S : ∀ P ∈ S, P ∈ T := by
    intro P hP
    change P ∈ ((S ∪ Sinv) ∪ Zinv) ∪ Winv
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hP))
  have hT_invS : ∀ P ∈ S,
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ∈ T := by
    intro P hP
    change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ∈
      ((S ∪ Sinv) ∪ Zinv) ∪ Winv
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr ⟨P, hP, rfl⟩)))
  have hT_invz :
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({z} : Set (𝓞 K))),
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈ T := by
    intro Q hQ
    change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈
      ((S ∪ Sinv) ∪ Zinv) ∪ Winv
    rw [Finset.mem_union, Finset.mem_union]
    refine Or.inl (Or.inr ?_)
    exact Finset.mem_image.mpr ⟨Q, by simpa using hQ, rfl⟩
  have hT_invw :
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({w} : Set (𝓞 K))),
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈ T := by
    intro Q hQ
    change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ Q ∈
      ((S ∪ Sinv) ∪ Zinv) ∪ Winv
    rw [Finset.mem_union]
    refine Or.inr ?_
    exact Finset.mem_image.mpr ⟨Q, by simpa using hQ, rfl⟩
  have hrep : ∀ c : ClassGroup (𝓞 K),
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧
        (∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) ∧
        (∀ P ∈ S,
          IsCoprime
            (cyclotomicGaloisConjugate (p := p) (K := K) a
              (I : Ideal (𝓞 K))) P) ∧
        (∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a
            (I : Ideal (𝓞 K))),
            z ∉ Q) ∧
        (∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
          (cyclotomicGaloisConjugate (p := p) (K := K) a
            (I : Ideal (𝓞 K))),
            w ∉ Q) := fun c ↦
    Furtwaengler.GaloisCovarianceAvoidance.exists_galois_covariance_representative_two
      (p := p) (K := K) a hz_ne hw_ne S T hTprime hT_ne hT_S hT_invS
      hT_invz hT_invw c
  have hcov :=
    Furtwaengler.coprimeCanonicalClassGroupModPLinear_galois_pow_p_sub_i_clear_denominators
      (p := p) (K := K) η z w S hSprime hS_ne hclass hi a hn hn_pos hclear hrep v
  simpa [locallyPrimaryKummerBadSetClassGroupModPLinear,
    Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPLinear,
    Furtwaengler.locallyPrimaryCoprimeCanonicalClassGroupModPHom,
    Furtwaengler.locallyPrimaryCoprimeCanonicalIdealSymbolData,
    Furtwaengler.coprimeCanonicalClassGroupModPLinear,
    Furtwaengler.coprimeCanonicalClassGroupModPHom,
    hclass, S, hSprime, hS_ne, hS_eta, hS_p] using hcov

/-- WR-05 nondegeneracy in the clean linear-map wrapper form. -/
theorem locallyPrimaryKummerBadSetClassGroupModPLinear_nontrivial_of_not_isPow
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @Furtwaengler.IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p) :
    ∃ v : Additive (ClassGroupModP K p),
      locallyPrimaryKummerBadSetClassGroupModPLinear
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hsing v ≠ 0 := by
  simpa [locallyPrimaryKummerBadSetClassGroupModPLinear] using
    locallyPrimaryCoprimeCanonicalClassGroupModPLinear_nontrivial_of_not_isPow_badSet
      (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
      hη_prime_to_p hη_local hsing

end Kummer
end Reflection
end BernoulliRegular

end
