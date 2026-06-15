module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KellyPrime
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdealElement

/-!
# Principal Φ to Stickelberger bridge

This file contains the K2-5/K2-6 bridge in the corrected REF-18 K-chain.

K2-4 gives the norm-symbol identity for the **actual** principal Φ element
`Φ((α))`.  K2-5 identifies the symbol of the explicit Stickelberger
principal generator `α^Θ = stickelbergerPrincipalGen α` with the weighted
Galois sum.  K2-6 is the conditional unit-stripping step:
if the actual Φ element differs from `α^Θ` by a unit whose residue symbols
vanish, then the weighted Galois sum satisfies the norm-symbol identity.

The sign is intentionally the sign currently produced by the formal K2-2
Frobenius chain: the result is a negative-convention norm relation.  A future
orientation lemma, if needed, should translate this convention explicitly.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### K2-5: Stickelberger principal generator as weighted Galois sum -/

/-- **K2-5, ideal form.**

The symbol of the explicit Stickelberger principal generator
`α^Θ = stickelbergerPrincipalGen α` is the weighted left-slot Galois sum.
This is a caller-facing wrapper around the K1 theorem already proved in
`KellyPrime.lean`. -/
theorem k2_5_principalGen_symbol_eq_weighted_galois_sum
    (α : 𝓞 K) (B : Ideal (𝓞 K))
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B :=
  pthSymbolAtIdeal_canonical_principalGen_eq_galois_sum α B h_coprime

/-- **K2-5, prime form.**

At a single nonzero prime `P'`, the ideal-level weighted Galois sum becomes
the expected sum of prime symbols. -/
theorem k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (α : 𝓞 K) {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P' :=
  pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum α hP'_ne
    h_coprime

/-! ### K2-6: conditional unit stripping -/

/-- Negative-convention form of the Stickelberger norm relation.

This matches the current formal K2-2/K2-4 orientation.  It is deliberately
separate from the older positive-convention `StickelbergerNormRelation`. -/
def StickelbergerNormRelationNeg (α : 𝓞 K) (P' : Ideal (𝓞 K)) : Prop :=
  (∑ a : CyclotomicUnitDelta p,
      ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
    -pthSymbolAtIdeal_canonical (p := p) (K := K)
      ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))

/-- **K2-6, unit stripping for the principal generator, right-unit form.**

If the actual principal Φ element satisfies `Φ((α)) = α^Θ * u` and the
unit-symbol contribution of `u` vanishes at every prime, then K2-4 transfers
from `Φ((α))` to `α^Θ`. -/
theorem k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_mul_unit
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = stickelbergerPrincipalGen (p := p) (K := K) α * u) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  have h_phi :=
    PhiPrimeElement.PhiIdealElement.principal_symbol_eq_neg_norm_principal_of_absNorm_coprime
      (p := p) (K := K) Φα hB hcop h_prime
  rw [hΦ] at h_phi
  rw [pthSymbolAtIdeal_canonical_mul_unit_α_eq_self
    (p := p) (K := K)
    (stickelbergerPrincipalGen (p := p) (K := K) α) hu hu_zero B] at h_phi
  exact h_phi

/-- **K2-6, unit stripping for the principal generator, left-unit form.**

This is the form usually produced by the principal unit-factor theorem:
`Φ((α)) = u * α^Θ`. -/
theorem k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  refine k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_mul_unit
    (p := p) (K := K) Φα hB hcop h_prime hu hu_zero ?_
  rw [hΦ, mul_comm]

/-- **K2-6, weighted Galois-sum form over an arbitrary ideal.**

Combines K2-5 with the right-unit form of the unit-stripped K2-4 theorem. -/
theorem k2_6_weighted_galois_sum_eq_neg_norm_principal_of_eq_mul_unit
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = stickelbergerPrincipalGen (p := p) (K := K) α * u)
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B) =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_eq_weighted_galois_sum
    (p := p) (K := K) α B h_coprime]
  exact k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_mul_unit
    (p := p) (K := K) Φα hB hcop h_prime hu hu_zero hΦ

/-- **K2-6, weighted Galois-sum form over an arbitrary ideal, left-unit form.** -/
theorem k2_6_weighted_galois_sum_eq_neg_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B) =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_eq_weighted_galois_sum
    (p := p) (K := K) α B h_coprime]
  exact k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hB hcop h_prime hu hu_zero hΦ

/-- **K2-6, prime weighted Galois-sum form.**

This is the prime-level negative-convention norm relation that follows from
the actual principal Φ theorem plus a symbol-trivial unit factor. -/
theorem k2_6_weighted_galois_sum_at_prime_eq_neg_norm_principal_of_eq_mul_unit
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = stickelbergerPrincipalGen (p := p) (K := K) α * u)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((P'.absNorm : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (p := p) (K := K) α hP'_ne h_coprime]
  exact k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_mul_unit
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ

/-- **K2-6, prime weighted Galois-sum form, left-unit version.** -/
theorem k2_6_weighted_galois_sum_at_prime_eq_neg_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((P'.absNorm : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (p := p) (K := K) α hP'_ne h_coprime]
  exact k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ

/-- **K2-6 packaged as a prime negative-convention norm relation.** -/
theorem StickelbergerNormRelationNeg_of_phi_unit_factor
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    StickelbergerNormRelationNeg (p := p) (K := K) α P' := by
  unfold StickelbergerNormRelationNeg
  exact k2_6_weighted_galois_sum_at_prime_eq_neg_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ h_coprime

/-! ### Positive-orientation K2-6 for reciprocal Φ data -/

/-- **K2-6, positive unit stripping for the principal generator, right-unit
form.**

This is the reciprocal-orientation analogue of
`k2_6_principalGen_symbol_eq_neg_norm_principal_of_eq_mul_unit`: the
prime Φ-symbol hypotheses already have the positive norm orientation, so no
separate sign-orientation hypothesis is needed. -/
theorem k2_6_principalGen_symbol_eq_norm_principal_of_eq_mul_unit
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = stickelbergerPrincipalGen (p := p) (K := K) α * u) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  have h_phi :=
    PhiPrimeElement.PhiIdealElement.principal_symbol_eq_norm_principal_of_absNorm_coprime
      (p := p) (K := K) Φα hB hcop h_prime
  rw [hΦ] at h_phi
  rw [pthSymbolAtIdeal_canonical_mul_unit_α_eq_self
    (p := p) (K := K)
    (stickelbergerPrincipalGen (p := p) (K := K) α) hu hu_zero B] at h_phi
  exact h_phi

/-- **K2-6, positive unit stripping for the principal generator, left-unit
form.** -/
theorem k2_6_principalGen_symbol_eq_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  refine k2_6_principalGen_symbol_eq_norm_principal_of_eq_mul_unit
    (p := p) (K := K) Φα hB hcop h_prime hu hu_zero ?_
  rw [hΦ, mul_comm]

/-- **K2-6, positive weighted Galois-sum form over an arbitrary ideal.** -/
theorem k2_6_weighted_galois_sum_eq_norm_principal_of_eq_mul_unit
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = stickelbergerPrincipalGen (p := p) (K := K) α * u)
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B) =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_eq_weighted_galois_sum
    (p := p) (K := K) α B h_coprime]
  exact k2_6_principalGen_symbol_eq_norm_principal_of_eq_mul_unit
    (p := p) (K := K) Φα hB hcop h_prime hu hu_zero hΦ

/-- **K2-6, positive weighted Galois-sum form over an arbitrary ideal,
left-unit form.** -/
theorem k2_6_weighted_galois_sum_eq_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B) =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_eq_weighted_galois_sum
    (p := p) (K := K) α B h_coprime]
  exact k2_6_principalGen_symbol_eq_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hB hcop h_prime hu hu_zero hΦ

/-- **K2-6, positive prime weighted Galois-sum form.** -/
theorem k2_6_weighted_galois_sum_at_prime_eq_norm_principal_of_eq_mul_unit
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = stickelbergerPrincipalGen (p := p) (K := K) α * u)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((P'.absNorm : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (p := p) (K := K) α hP'_ne h_coprime]
  exact k2_6_principalGen_symbol_eq_norm_principal_of_eq_mul_unit
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ

/-- **K2-6, positive prime weighted Galois-sum form, left-unit version.** -/
theorem k2_6_weighted_galois_sum_at_prime_eq_norm_principal_of_eq_unit_mul
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    (∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((P'.absNorm : ℤ) : 𝓞 K)) α := by
  rw [← k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (p := p) (K := K) α hP'_ne h_coprime]
  exact k2_6_principalGen_symbol_eq_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ

/-- **K2-6 packaged as the positive Stickelberger norm relation.** -/
theorem StickelbergerNormRelation_of_phi_unit_factor
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    StickelbergerNormRelation (p := p) (K := K) α P' := by
  unfold StickelbergerNormRelation
  exact k2_6_weighted_galois_sum_at_prime_eq_norm_principal_of_eq_unit_mul
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ h_coprime

/-- **Terminal K-chain, positive prime form.** -/
theorem kellyPrimeEquality_of_phi_unit_factor
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  refine kellyPrimeEquality_of_StickelbergerNormRelation
    (p := p) (K := K) α hP'_ne h_coprime ?_
  exact StickelbergerNormRelation_of_phi_unit_factor
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ h_coprime

/-! ### Terminal signed K-chain endpoint -/

/-- **Signed K3.** A negative-convention Stickelberger norm relation gives
the signed Kelly prime identity. -/
theorem kellyPrimeNegEquality_of_StickelbergerNormRelationNeg
    (α : 𝓞 K) {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (h_norm : StickelbergerNormRelationNeg (p := p) (K := K) α P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  rw [k2_5_principalGen_symbol_at_prime_eq_weighted_galois_sum
    (p := p) (K := K) α hP'_ne h_coprime]
  exact h_norm

/-- Universal signed K-chain from universal negative-convention norm
relations. -/
theorem kellyPrimeNegEquality_all_of_StickelbergerNormRelationNeg
    {α : 𝓞 K}
    (h_coprime : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (h_norm : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      StickelbergerNormRelationNeg (p := p) (K := K) α P') :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := fun P' hP'_inst hP'_ne =>
  kellyPrimeNegEquality_of_StickelbergerNormRelationNeg α hP'_ne
    (h_coprime P' hP'_inst hP'_ne) (h_norm P' hP'_inst hP'_ne)

/-- Convert the signed Kelly prime identity to the positive concrete equality
when the norm-symbol side has the required orientation. -/
theorem kellyPrimeEquality_of_neg_of_signOrientation
    {α : 𝓞 K} {P' : Ideal (𝓞 K)}
    (h_neg :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))))
    (h_orient :
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  rw [h_neg, h_orient]

/-- Universal conversion from signed to positive concrete Kelly equalities
under a universal sign-orientation hypothesis. -/
theorem kellyPrimeEquality_all_of_neg_all_of_signOrientation_all
    {α : 𝓞 K}
    (h_neg : ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))))
    (h_orient : ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  intro P' hP'_inst hP'_ne
  exact kellyPrimeEquality_of_neg_of_signOrientation
      (h_neg P' hP'_ne) (h_orient P' hP'_ne)

/-- If singular `η` satisfies positive Kelly away from primes above `p` and
away from the support of `η`, then the target symbol of `η^Θ` vanishes at
every nonzero prime. At primes containing `η`, the numerator `η^Θ` itself
lies in the prime because the Stickelberger product has the `a = 1` factor. -/
theorem stickelbergerPrincipalGen_symbol_eq_zero_of_singular_Kelly_awayFromP_eta
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (h_kelly_away : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      (p : 𝓞 K) ∉ P' → η ∉ P' →
        pthSymbolAtIdeal_canonical (p := p) (K := K)
            (stickelbergerPrincipalGen (p := p) (K := K) η) P' =
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({η} : Set (𝓞 K)))) :
    ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) η) P' = 0 := by
  intro P' hP'_prime hP'_ne
  haveI : P'.IsPrime := hP'_prime
  by_cases hp_in : (p : 𝓞 K) ∈ P'
  · exact kellyPrimeEquality_lhs_eq_zero_of_p_mem hP'_ne hp_in
  · by_cases hη_in : η ∈ P'
    · haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_ne
      rw [pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
        (p := p) (K := K) (stickelbergerPrincipalGen (p := p) (K := K) η)
        hP'_ne]
      exact pthSymbolAtPrime_canonical_eq_zero_of_mem hP'_ne ‹P'.IsMaximal›
        (stickelbergerPrincipalGen_mem_of_mem (p := p) (K := K) hη_in)
    · exact kellyPrimeEquality_lhs_eq_zero_of_singular h_eta
        (h_kelly_away P' hP'_prime hP'_ne hp_in hη_in)

/-! ### Signed Kelly is enough for singular numerators -/

/-- For singular `η`, the signed Kelly prime identity also forces the target
symbol of `η^Θ = stickelbergerPrincipalGen η` to vanish. The sign disappears
because the right-hand norm symbol is already zero from `(η) = b^p`. -/
theorem kellyPrimeNegEquality_lhs_eq_zero_of_singular
    {η : 𝓞 K} {b P' : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (h_kelly :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) η) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({η} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) η) P' = 0 := by
  rw [h_kelly, kellyPrimeEquality_rhs_eq_zero_of_singular h_eta, neg_zero]

/-- If singular `η` satisfies signed Kelly away from primes above `p`, then the
target symbol of `η^Θ` vanishes at every nonzero prime. This is the endpoint
needed by the signed K-chain: no separate sign-orientation hypothesis is
needed in the singular case. -/
theorem stickelbergerPrincipalGen_symbol_eq_zero_of_singular_KellyNeg_awayFromP
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (h_kelly_away : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      (p : 𝓞 K) ∉ P' →
        pthSymbolAtIdeal_canonical (p := p) (K := K)
            (stickelbergerPrincipalGen (p := p) (K := K) η) P' =
          -pthSymbolAtIdeal_canonical (p := p) (K := K)
            ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({η} : Set (𝓞 K)))) :
    ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) η) P' = 0 := by
  intro P' hP'_prime hP'_ne
  haveI : P'.IsPrime := hP'_prime
  by_cases hp_in : (p : 𝓞 K) ∈ P'
  · exact kellyPrimeEquality_lhs_eq_zero_of_p_mem hP'_ne hp_in
  · exact kellyPrimeNegEquality_lhs_eq_zero_of_singular h_eta
      (h_kelly_away P' hP'_prime hP'_ne hp_in)

/-- If singular `η` satisfies signed Kelly away from primes above `p` and
away from the support of `η`, then the target symbol of `η^Θ` vanishes at
every nonzero prime. At primes containing `η`, the numerator `η^Θ` itself
lies in the prime because the Stickelberger product has the `a = 1` factor. -/
theorem stickelbergerPrincipalGen_symbol_eq_zero_of_singular_KellyNeg_awayFromP_eta
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (h_kelly_away : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      (p : 𝓞 K) ∉ P' → η ∉ P' →
        pthSymbolAtIdeal_canonical (p := p) (K := K)
            (stickelbergerPrincipalGen (p := p) (K := K) η) P' =
          -pthSymbolAtIdeal_canonical (p := p) (K := K)
            ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({η} : Set (𝓞 K)))) :
    ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) η) P' = 0 := by
  intro P' hP'_prime hP'_ne
  haveI : P'.IsPrime := hP'_prime
  by_cases hp_in : (p : 𝓞 K) ∈ P'
  · exact kellyPrimeEquality_lhs_eq_zero_of_p_mem hP'_ne hp_in
  · by_cases hη_in : η ∈ P'
    · haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_ne
      rw [pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
        (p := p) (K := K) (stickelbergerPrincipalGen (p := p) (K := K) η)
        hP'_ne]
      exact pthSymbolAtPrime_canonical_eq_zero_of_mem hP'_ne ‹P'.IsMaximal›
        (stickelbergerPrincipalGen_mem_of_mem (p := p) (K := K) hη_in)
    · exact kellyPrimeNegEquality_lhs_eq_zero_of_singular h_eta
        (h_kelly_away P' hP'_prime hP'_ne hp_in hη_in)

/-- **Terminal K-chain, signed prime form.**

This composes the corrected actual-Φ K2-2/K2-4 theorem, the K2-5 Galois
sum expansion, and K2-6 unit stripping into the signed Kelly endpoint.
The remaining hypotheses are precisely the non-K inputs:
* actual principal Φ data and prime Φ-symbol identities,
* the principal unit-factor equation with symbol-trivial unit,
* coprimality/nonvanishing side conditions. -/
theorem kellyPrimeNegEquality_of_phi_unit_factor
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  refine kellyPrimeNegEquality_of_StickelbergerNormRelationNeg
    (p := p) (K := K) α hP'_ne h_coprime ?_
  exact StickelbergerNormRelationNeg_of_phi_unit_factor
    (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ h_coprime

/-- **Terminal K-chain, positive prime form under explicit orientation.** -/
theorem kellyPrimeEquality_of_phi_unit_factor_of_signOrientation
    {α u : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hΦ : Φα.gamma = u * stickelbergerPrincipalGen (p := p) (K := K) α)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (h_orient :
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeEquality_of_neg_of_signOrientation
    (kellyPrimeNegEquality_of_phi_unit_factor
      (p := p) (K := K) Φα hP'_ne hcop h_prime hu hu_zero hΦ h_coprime)
    h_orient

end Furtwaengler

end BernoulliRegular

end
