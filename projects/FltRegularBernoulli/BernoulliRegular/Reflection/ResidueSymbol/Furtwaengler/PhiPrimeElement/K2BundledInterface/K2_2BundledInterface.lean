module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement.PhiPrimeElementAPI

/-!
# Data-carrying prime Φ-elements

The ideal-theoretic predicate `StickelbergerIdealEquality P` only says that
`stickelbergerIdeal P` is principal. Its extracted generator is therefore an
arbitrary generator, determined only up to a unit.

For K2-2 we need the actual Gauss-sum Φ element, not an arbitrary generator of
the same ideal. This file introduces a non-`Prop` object whose `gamma` field is
the element used in the residue-symbol theorem. The current constructor wires
in the existing `phiPrimeGenDescent S a` route from `CrossRingBridge.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement

/-- **K2-2 for the actual descended Φ element, with nonmembership derived
from coprime rational norms**.  This is the caller-facing version of
`K2_2_of_canonical_zeta_choices_ofDescent` matching the corrected K2-2
coprimality condition. -/
theorem K2_2_of_canonical_zeta_choices_ofDescent_of_absNorm_coprime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    (h_span : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (ofDescent S ha₁ ha₂ h_ne_zero h_span).gamma P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : P.IsPrime := hP_max.isPrime
  haveI : P'.IsPrime := hP'_max.isPrime
  have h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P' := by
    have h_notin := gamma_notMem_of_absNorm_coprime
      (ofDescent S ha₁ ha₂ h_ne_zero h_span) hP_bot hP'_bot hcop
    simpa [ofDescent] using h_notin
  exact K2_2_of_canonical_zeta_choices_ofDescent
    hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq h_zeta_p_int_eq
    ha₁ ha₂ h_ne_zero h_span
    hP'_bot hp_in_P' h_phi_notin_P'
    h_over hℓ_ne_ℓ'

/-- **K2-2 for the index-one actual Φ element from descent**.  This is the
form closest to Kelly's prime Φ-symbol identity in the current path-a
convention: the target has no index factor, only the sign convention already
present in the formal chain. -/
theorem K2_2_index_one_of_canonical_zeta_choices_ofDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_span : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (ofDescentIndexOne S h_ne_zero h_span).gamma P' =
      -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_apex := K2_2_of_canonical_zeta_choices_ofDescent
    hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq h_zeta_p_int_eq
    (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero h_span
    hP'_bot hp_in_P' h_phi_notin_P'
    h_over hℓ_ne_ℓ'
  change BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K)
      (ofDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero h_span).gamma P' =
    -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P
  rw [h_apex]
  push_cast
  ring

/-- **Index-one K2-2 for the actual descended Φ element, with nonmembership
derived from coprime rational norms**. -/
theorem K2_2_index_one_of_canonical_zeta_choices_ofDescent_of_absNorm_coprime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_span : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (ofDescentIndexOne S h_ne_zero h_span).gamma P' =
      -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_apex := K2_2_of_canonical_zeta_choices_ofDescent_of_absNorm_coprime
    hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq h_zeta_p_int_eq
    (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero h_span
    hP'_bot hp_in_P' hcop
    h_over hℓ_ne_ℓ'
  change BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K)
      (ofDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero h_span).gamma P' =
    -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P
  rw [h_apex]
  push_cast
  ring

/-- **K2-2 for the reciprocal-index actual Φ element, with nonmembership
derived from coprime rational norms**.

For index `p - 1`, the generic K2-2 factor
`-((p - 1 : ZMod p) * s)` simplifies to the positive norm symbol `s`. This is
the sign orientation forced by the reciprocal descended Gauss-sum convention
used by the REF-18 exact-exponent theorem. -/
theorem K2_2_sub_one_of_canonical_zeta_choices_ofDescent_of_absNorm_coprime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_span : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      Ideal.span ({phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
          Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (ofDescentSubOne S h_ne_zero h_span).gamma P' =
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_apex := K2_2_of_canonical_zeta_choices_ofDescent_of_absNorm_coprime
    hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq h_zeta_p_int_eq
    (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero h_span
    hP'_bot hp_in_P' hcop
    h_over hℓ_ne_ℓ'
  change BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K)
      (ofDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero h_span).gamma P' =
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P
  rw [h_apex]
  have hp_sub_one_cast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
    rw [Nat.cast_sub hp_one, Nat.cast_one]
    simp
  rw [hp_sub_one_cast]
  ring

/-! ### Bundled K2-2 interface -/

/-- Source-side data for the corrected K2-2 theorem.

This bundles the data saying that the source prime `P` is represented by the
actual descended Gauss-sum element `phiPrimeGenDescent S 1`.  The span field is
the mathematically substantive assertion that this concrete descended element,
not merely some arbitrary generator, generates the Stickelberger ideal. -/
structure K2_2SourceData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R') where
  /-- The source ideal is nonzero. -/
  hP_bot : P ≠ ⊥
  /-- The rational prime `ℓ` lies below `P`. -/
  hℓ_in_P : (ℓ : 𝓞 K) ∈ P
  /-- The Kummer prime `p` is not the residue characteristic at `P`. -/
  hp_notin_P : (p : 𝓞 K) ∉ P
  /-- The residue-side root in the Dwork setup is the canonical residue
  `p`-th root of unity at `P`. -/
  h_zeta_k_eq :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P
  /-- The integral `p`-th root of unity in the Dwork setup is the chosen
  cyclotomic integer of `K`, mapped into `R'`. -/
  h_zeta_p_int_eq :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_p_int =
      (algebraMap (𝓞 K) (𝓞 R'))
        (BernoulliRegular.cyclotomicZetaInteger (p := p) K)
  /-- The index-one Gauss sum has nonzero `p`-th power. -/
  h_ne_zero :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.gaussSumInt 1 ^ p ≠ 0
  /-- The descended index-one Φ element generates the Stickelberger ideal. -/
  h_span :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    Ideal.span ({phiPrimeGenDescent S
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P

/-- The actual index-one Φ element associated to bundled source-side K2-2
data. -/
noncomputable def K2_2SourceData.phi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S) :
    PhiPrimeElement (p := p) (K := K) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact ofDescentIndexOne S D.h_ne_zero D.h_span

@[simp] theorem K2_2SourceData_phi_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    D.phi.gamma =
      phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) D.h_ne_zero := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rfl

/-- Target-side data for the corrected K2-2 theorem.

The over-prime and its residue characteristic are kept as data because the
cross-ring Frobenius theorem is proved in a finite cyclotomic extension `R'`
above `K`.  This object is the honest interface for applying K2-2 at a target
prime `P'`. -/
structure K2_2TargetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (P' : Ideal (𝓞 K)) [P'.IsMaximal] where
  /-- The target ideal is nonzero. -/
  hP'_bot : P' ≠ ⊥
  /-- The Kummer prime `p` is not the residue characteristic at `P'`. -/
  hp_notin_P' : (p : 𝓞 K) ∉ P'
  /-- A chosen prime of `𝓞 R'` over `P'`. -/
  overPrime : Ideal (𝓞 R')
  /-- The chosen over-prime is maximal. -/
  overPrime_max : overPrime.IsMaximal
  /-- The residue characteristic at the chosen over-prime. -/
  ell' : ℕ
  /-- The residue characteristic is prime. -/
  ell'_prime : Fact ell'.Prime
  /-- The residue quotient over the chosen over-prime has characteristic
  `ell'`. -/
  char_over : CharP (𝓞 R' ⧸ overPrime) ell'
  /-- The chosen over-prime lies over `P'`. -/
  h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P'
  /-- The source and target residue characteristics are distinct. -/
  hℓ_ne_ℓ' : ℓ ≠ ell'

/-- **Completed corrected K2-2, bundled form.**

For the actual index-one descended Φ element attached to `P`, its residue
symbol at a rational-norm-coprime target prime `P'` is the norm symbol in the
opposite direction, with the sign convention produced by the current
cross-ring Frobenius chain. -/
theorem K2_2SourceData.index_one_symbol_eq_norm_symbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (T : K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) D.phi.gamma P' =
      -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : T.overPrime.IsMaximal := T.overPrime_max
  letI : Fact T.ell'.Prime := T.ell'_prime
  letI : CharP (𝓞 R' ⧸ T.overPrime) T.ell' := T.char_over
  simpa [K2_2SourceData.phi] using
    K2_2_index_one_of_canonical_zeta_choices_ofDescent_of_absNorm_coprime
      D.hP_bot D.hℓ_in_P D.hp_notin_P
      S D.h_zeta_k_eq D.h_zeta_p_int_eq D.h_ne_zero D.h_span
      T.hP'_bot T.hp_notin_P' hcop T.h_over T.hℓ_ne_ℓ'

/-- Source-side data for the reciprocal-index K2-2 theorem.

This is the exact analogue of `K2_2SourceData`, but for the actual descended
Gauss-sum element `phiPrimeGenDescent S (p - 1)`. Its K2-2 symbol identity has
the positive norm-symbol sign, because the reciprocal index contributes the
factor `-((p - 1 : ZMod p) * s) = s`. -/
structure K2_2ReciprocalSourceData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R') where
  /-- The source ideal is nonzero. -/
  hP_bot : P ≠ ⊥
  /-- The rational prime `ℓ` lies below `P`. -/
  hℓ_in_P : (ℓ : 𝓞 K) ∈ P
  /-- The Kummer prime `p` is not the residue characteristic at `P`. -/
  hp_notin_P : (p : 𝓞 K) ∉ P
  /-- The residue-side root in the Dwork setup is the canonical residue
  `p`-th root of unity at `P`. -/
  h_zeta_k_eq :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P
  /-- The integral `p`-th root of unity in the Dwork setup is the chosen
  cyclotomic integer of `K`, mapped into `R'`. -/
  h_zeta_p_int_eq :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_p_int =
      (algebraMap (𝓞 K) (𝓞 R'))
        (BernoulliRegular.cyclotomicZetaInteger (p := p) K)
  /-- The reciprocal-index Gauss sum has nonzero `p`-th power. -/
  h_ne_zero :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.gaussSumInt (p - 1) ^ p ≠ 0
  /-- The descended reciprocal-index Φ element generates the Stickelberger ideal. -/
  h_span :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    Ideal.span ({phiPrimeGenDescent S
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
        Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P

/-- The actual reciprocal-index Φ element associated to bundled source-side
K2-2 data. -/
noncomputable def K2_2ReciprocalSourceData.phi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S) :
    PhiPrimeElement (p := p) (K := K) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact ofDescentSubOne S D.h_ne_zero D.h_span

@[simp] theorem K2_2ReciprocalSourceData_phi_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    D.phi.gamma =
      phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) D.h_ne_zero := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rfl

/-- Bundled K2-2 for the reciprocal-index source data. -/
theorem K2_2ReciprocalSourceData.symbol_eq_norm_symbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (T : K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) D.phi.gamma P' =
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : T.overPrime.IsMaximal := T.overPrime_max
  letI : Fact T.ell'.Prime := T.ell'_prime
  letI : CharP (𝓞 R' ⧸ T.overPrime) T.ell' := T.char_over
  simpa [K2_2ReciprocalSourceData.phi] using
    K2_2_sub_one_of_canonical_zeta_choices_ofDescent_of_absNorm_coprime
      D.hP_bot D.hℓ_in_P D.hp_notin_P
      S D.h_zeta_k_eq D.h_zeta_p_int_eq D.h_ne_zero D.h_span
      T.hP'_bot T.hp_notin_P' hcop T.h_over T.hℓ_ne_ℓ'

/-! ### Conductor-flexible source data -/

/-- Index-one constructor for the actual Φ-prime element from a
conductor-flexible Dwork descent. -/
noncomputable def ofFlexibleDescentIndexOne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span :
      Ideal.span ({S.phiPrimeGenDescent h_psi
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} :
            Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P) :
    PhiPrimeElement (p := p) (K := K) P where
  gamma :=
    S.phiPrimeGenDescent h_psi
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero
  gamma_ne_zero :=
    S.phiPrimeGenDescent_ne_zero h_psi
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero
  span_gamma := h_span

/-- Source-side data for the conductor-flexible index-one K2-2 theorem.

This is the signed/product-side flexible counterpart of
`K2_2FlexibleReciprocalSourceData`: its K2 symbol identity has the negative
norm-symbol orientation needed by the principal Φ product cancellation. -/
structure K2_2FlexibleSourceData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R') where
  /-- The source ideal is nonzero. -/
  hP_bot : P ≠ ⊥
  /-- The rational prime `ℓ` lies below `P`. -/
  hℓ_in_P : (ℓ : 𝓞 K) ∈ P
  /-- The Kummer prime `p` is not the residue characteristic at `P`. -/
  hp_notin_P : (p : 𝓞 K) ∉ P
  /-- The trace-form/Galois psi-shift compatibility needed for flexible
  descent to `𝓞 K`. -/
  h_psi :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.concrete.IsGalPsiShiftCompatible
  /-- The residue-side root in the Dwork setup is the canonical residue
  `p`-th root of unity at `P`. -/
  h_zeta_k_eq :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P
  /-- The integral `p`-th root of unity in the Dwork setup is the chosen
  cyclotomic integer of `K`, mapped into `R'`. -/
  h_zeta_p_int_eq :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_p_int =
      (algebraMap (𝓞 K) (𝓞 R'))
        (BernoulliRegular.cyclotomicZetaInteger (p := p) K)
  /-- The index-one Gauss sum has nonzero `p`-th power. -/
  h_ne_zero :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.gaussSumInt 1 ^ p ≠ 0
  /-- The descended index-one Φ element generates the Stickelberger ideal. -/
  h_span :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    Ideal.span ({S.phiPrimeGenDescent h_psi
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} :
        Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P

/-- The actual index-one Φ element associated to bundled
conductor-flexible source-side data. -/
noncomputable def K2_2FlexibleSourceData.phi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S) :
    PhiPrimeElement (p := p) (K := K) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact ofFlexibleDescentIndexOne S D.h_psi D.h_ne_zero D.h_span

@[simp] theorem K2_2FlexibleSourceData_phi_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    D.phi.gamma =
      S.phiPrimeGenDescent D.h_psi
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) D.h_ne_zero := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rfl

/-! ### Conductor-flexible reciprocal source data -/

/-- Reciprocal-index constructor for the actual Φ-prime element from a
conductor-flexible Dwork descent. -/
noncomputable def ofFlexibleDescentSubOne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span :
      Ideal.span ({S.phiPrimeGenDescent h_psi
          (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
            Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P) :
    PhiPrimeElement (p := p) (K := K) P where
  gamma :=
    S.phiPrimeGenDescent h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero
  gamma_ne_zero :=
    S.phiPrimeGenDescent_ne_zero h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero
  span_gamma := h_span

/-- The actual reciprocal-index conductor-flexible Φ candidate. -/
noncomputable def flexibleReciprocalPhiCandidate
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    𝓞 K :=
  S.phiPrimeGenDescent h_psi
    (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero

@[simp] theorem flexibleReciprocalPhiCandidate_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero =
      S.phiPrimeGenDescent h_psi
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero :=
  rfl

/-- The flexible reciprocal Φ candidate is nonzero. -/
theorem flexibleReciprocalPhiCandidate_ne_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    flexibleReciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero ≠ 0 := by
  simpa [flexibleReciprocalPhiCandidate] using
    S.phiPrimeGenDescent_ne_zero h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero

/-- The flexible reciprocal Φ candidate descends the upstairs reciprocal
Gauss-sum p-th power. -/
theorem algebraMap_flexibleReciprocalPhiCandidate
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    algebraMap (𝓞 K) (𝓞 R')
        (flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero) =
      S.gaussSumInt (p - 1) ^ p := by
  simpa [flexibleReciprocalPhiCandidate] using
    S.algebraMap_phiPrimeGenDescent h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero

/-- The flexible reciprocal Φ candidate generates the requested Stickelberger
ideal under the flexible atomic exponent and split-orbit hypotheses. -/
theorem flexibleReciprocalPhiCandidate_span_of_atomic_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {P : Ideal (𝓞 K)}
    (h_descentPrime : S.concrete.descentPrime = P)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      S.StickelbergerExactConjugateExponents
        (flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero))
    (he : (S.concrete.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf : (S.concrete.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    Ideal.span ({flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P := by
  set γ : 𝓞 K :=
    flexibleReciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  have hγ_ne : γ ≠ 0 := by
    simpa [γ] using
      flexibleReciprocalPhiCandidate_ne_zero
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  have hγ_alg : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt (p - 1) ^ p := by
    simpa [γ] using
      algebraMap_flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  have h_expγ : S.StickelbergerExactConjugateExponents γ := by
    simpa [γ] using h_exp
  have h_sup : S.StickelbergerSupportInOrbit γ :=
    S.stickelbergerSupportInOrbit_of_descentGaussSum
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) hγ_ne hγ_alg
  have h_faithful : S.StickelbergerOrbitFaithful :=
    S.stickelbergerOrbitFaithful_of_split he hf
  have h_stickMul : S.StickelbergerIdealConjugateMultiplicity :=
    S.stickelbergerIdealConjugateMultiplicity_of_orbitFaithful h_faithful
  have h_eq := S.span_eq_stickelbergerIdeal_of_atomic hγ_ne h_expγ h_sup h_stickMul
  rw [h_descentPrime] at h_eq
  simpa [γ] using h_eq

/-- The flexible reciprocal Φ candidate generates the Stickelberger ideal from
repeated exact exponents, with no split/orbit-faithfulness hypothesis. -/
theorem flexibleReciprocalPhiCandidate_span_of_repeatedExact
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {P : Ideal (𝓞 K)}
    (h_descentPrime : S.concrete.descentPrime = P)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      S.StickelbergerRepeatedExactExponents
        (flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero)) :
    Ideal.span ({flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P := by
  set γ : 𝓞 K :=
    flexibleReciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  have hγ_ne : γ ≠ 0 := by
    simpa [γ] using
      flexibleReciprocalPhiCandidate_ne_zero
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  have h_expγ : S.StickelbergerRepeatedExactExponents γ := by
    simpa [γ] using h_exp
  have h_eq := S.span_eq_stickelbergerIdeal_of_repeatedExactExponents hγ_ne h_expγ
  rw [h_descentPrime] at h_eq
  simpa [γ] using h_eq

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
