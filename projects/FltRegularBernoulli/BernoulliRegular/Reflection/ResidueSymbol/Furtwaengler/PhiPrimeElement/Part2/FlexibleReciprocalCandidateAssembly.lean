module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement.Part2.K2_2BundledInterface

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement

theorem flexibleReciprocalPhiCandidate_span_of_repeatedExactOnOrbit
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
      S.StickelbergerRepeatedExactExponentsOnOrbit
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
  have hγ_alg : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt (p - 1) ^ p := by
    simpa [γ] using
      algebraMap_flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  have h_sup : S.StickelbergerSupportInOrbit γ :=
    S.stickelbergerSupportInOrbit_of_descentGaussSum
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) hγ_ne hγ_alg
  have h_expγ : S.StickelbergerRepeatedExactExponentsOnOrbit γ := by
    simpa [γ] using h_exp
  have h_eq :=
    S.span_eq_stickelbergerIdeal_of_supportInOrbit_of_repeatedExactOnOrbit
      hγ_ne h_sup h_expγ
  rw [h_descentPrime] at h_eq
  simpa [γ] using h_eq

/-- Assemble the flexible reciprocal candidate into a Φ-prime element under the
flexible atomic exponent and split-orbit hypotheses. -/
noncomputable def ofFlexibleReciprocalPhiCandidateAtomicSplit
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
    PhiPrimeElement (p := p) (K := K) P where
  gamma :=
    flexibleReciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  gamma_ne_zero :=
    flexibleReciprocalPhiCandidate_ne_zero
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  span_gamma :=
    flexibleReciprocalPhiCandidate_span_of_atomic_split
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi
      h_descentPrime h_ne_zero h_exp he hf

/-- Assemble the flexible reciprocal candidate into a Φ-prime element from
repeated exact exponents, with no split/orbit-faithfulness hypothesis. -/
noncomputable def ofFlexibleReciprocalPhiCandidateRepeatedExact
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
    PhiPrimeElement (p := p) (K := K) P where
  gamma :=
    flexibleReciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  gamma_ne_zero :=
    flexibleReciprocalPhiCandidate_ne_zero
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  span_gamma :=
    flexibleReciprocalPhiCandidate_span_of_repeatedExact
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi
      h_descentPrime h_ne_zero h_exp

/-- Assemble the flexible reciprocal candidate into a Φ-prime element from
orbit-indexed repeated exact exponents, with no split/orbit-faithfulness
hypothesis. -/
noncomputable def ofFlexibleReciprocalPhiCandidateRepeatedExactOnOrbit
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
      S.StickelbergerRepeatedExactExponentsOnOrbit
        (flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero)) :
    PhiPrimeElement (p := p) (K := K) P where
  gamma :=
    flexibleReciprocalPhiCandidate
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  gamma_ne_zero :=
    flexibleReciprocalPhiCandidate_ne_zero
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero
  span_gamma :=
    flexibleReciprocalPhiCandidate_span_of_repeatedExactOnOrbit
      (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi
      h_descentPrime h_ne_zero h_exp

@[simp] theorem ofFlexibleReciprocalPhiCandidateAtomicSplit_gamma
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
    (ofFlexibleReciprocalPhiCandidateAtomicSplit
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi
        h_descentPrime h_ne_zero h_exp he hf).gamma =
      flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero :=
  rfl

@[simp] theorem ofFlexibleReciprocalPhiCandidateRepeatedExact_gamma
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
    (ofFlexibleReciprocalPhiCandidateRepeatedExact
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi
        h_descentPrime h_ne_zero h_exp).gamma =
      flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := k) (K := K) (R' := R') S h_psi h_ne_zero :=
  rfl

/-- Source-side data for the conductor-flexible reciprocal-index K2-2
interface.

This is the flexible counterpart of `K2_2ReciprocalSourceData`: its `phi`
constructor is the actual descended reciprocal Gauss-sum element produced by
`ConductorFlexibleFullTeichDworkSetup.phiPrimeGenDescent`.  The K2 symbol
identity is intentionally ported separately, because the old proof still
uses the pair-cyclotomic `FullTeichDworkSetup` interface. -/
structure K2_2FlexibleReciprocalSourceData
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
  /-- The reciprocal-index Gauss sum has nonzero `p`-th power. -/
  h_ne_zero :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.gaussSumInt (p - 1) ^ p ≠ 0
  /-- The descended reciprocal-index Φ element generates the Stickelberger
  ideal. -/
  h_span :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    Ideal.span ({S.phiPrimeGenDescent h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
        Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P

/-- The actual reciprocal-index Φ element associated to bundled
conductor-flexible source-side data. -/
noncomputable def K2_2FlexibleReciprocalSourceData.phi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S) :
    PhiPrimeElement (p := p) (K := K) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact ofFlexibleDescentSubOne S D.h_psi D.h_ne_zero D.h_span

@[simp] theorem K2_2FlexibleReciprocalSourceData_phi_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    D.phi.gamma =
      S.phiPrimeGenDescent D.h_psi
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) D.h_ne_zero := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rfl

/-- Target-side data for the conductor-flexible K2-2 theorem.

This is the target counterpart of `K2_2FlexibleReciprocalSourceData`: it
keeps the chosen over-prime and its residue characteristic, but does not ask
for the old pair-cyclotomic typeclass on `R'`. -/
structure K2_2FlexibleTargetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
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

/-- Bundled flexible K2-2 for index-one source data. -/
theorem K2_2FlexibleSourceData.symbol_eq_neg_norm_symbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (T : K2_2FlexibleTargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P')
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
  haveI : P.IsPrime := inferInstance
  haveI : P'.IsPrime := inferInstance
  have h_phi_notin_P' :
      S.phiPrimeGenDescent D.h_psi
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) D.h_ne_zero ∉ P' := by
    have h_notin := gamma_notMem_of_absNorm_coprime
      (D.phi) D.hP_bot T.hP'_bot hcop
    simpa [K2_2FlexibleSourceData_phi_gamma] using h_notin
  have h_apex := S.K2_2_path_a_pthSymbol_of_zeta_choices
    D.hP_bot D.hℓ_in_P D.hp_notin_P D.h_psi
    D.h_zeta_k_eq D.h_zeta_p_int_eq
    (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
    D.h_ne_zero T.hP'_bot T.hp_notin_P' h_phi_notin_P'
    T.h_over T.hℓ_ne_ℓ'
  rw [K2_2FlexibleSourceData_phi_gamma, h_apex]
  simp

/-- Bundled flexible K2-2 for reciprocal-index source data. -/
theorem K2_2FlexibleReciprocalSourceData.symbol_eq_norm_symbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (T : K2_2FlexibleTargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P')
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
  haveI : P.IsPrime := inferInstance
  haveI : P'.IsPrime := inferInstance
  have h_phi_notin_P' :
      S.phiPrimeGenDescent D.h_psi
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) D.h_ne_zero ∉ P' := by
    have h_notin := gamma_notMem_of_absNorm_coprime
      (D.phi) D.hP_bot T.hP'_bot hcop
    simpa [K2_2FlexibleReciprocalSourceData_phi_gamma] using h_notin
  have h_apex := S.K2_2_path_a_pthSymbol_of_zeta_choices
    D.hP_bot D.hℓ_in_P D.hp_notin_P D.h_psi
    D.h_zeta_k_eq D.h_zeta_p_int_eq
    (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
    D.h_ne_zero T.hP'_bot T.hp_notin_P' h_phi_notin_P'
    T.h_over T.hℓ_ne_ℓ'
  rw [K2_2FlexibleReciprocalSourceData_phi_gamma, h_apex]
  have hp_sub_one_cast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
    rw [Nat.cast_sub hp_one, Nat.cast_one]
    simp
  rw [hp_sub_one_cast]
  ring

/-- Build conductor-flexible reciprocal source data from an orbit-indexed
repeated exact exponent certificate, without any split/order-one hypothesis. -/
noncomputable def K2_2FlexibleReciprocalSourceData.ofRepeatedExactOnOrbit
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (hP_bot : P ≠ ⊥)
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.StickelbergerRepeatedExactExponentsOnOrbit
        (flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
          S h_psi h_ne_zero)) :
    K2_2FlexibleReciprocalSourceData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  refine
    { hP_bot := hP_bot
      hℓ_in_P := hℓ_in_P
      hp_notin_P := hp_notin_P
      h_psi := h_psi
      h_zeta_k_eq := h_zeta_k_eq
      h_zeta_p_int_eq := h_zeta_p_int_eq
      h_ne_zero := h_ne_zero
      h_span := ?_ }
  simpa [flexibleReciprocalPhiCandidate] using
    flexibleReciprocalPhiCandidate_span_of_repeatedExactOnOrbit
      (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
      h_psi h_descentPrime h_ne_zero h_exp

/-- Build conductor-flexible reciprocal source data from a repeated exact
exponent certificate, without any split/order-one hypothesis. -/
noncomputable def K2_2FlexibleReciprocalSourceData.ofRepeatedExact
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (hP_bot : P ≠ ⊥)
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.StickelbergerRepeatedExactExponents
        (flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
          S h_psi h_ne_zero)) :
    K2_2FlexibleReciprocalSourceData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  refine
    { hP_bot := hP_bot
      hℓ_in_P := hℓ_in_P
      hp_notin_P := hp_notin_P
      h_psi := h_psi
      h_zeta_k_eq := h_zeta_k_eq
      h_zeta_p_int_eq := h_zeta_p_int_eq
      h_ne_zero := h_ne_zero
      h_span := ?_ }
  simpa [flexibleReciprocalPhiCandidate] using
    flexibleReciprocalPhiCandidate_span_of_repeatedExact
      (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
      h_psi h_descentPrime h_ne_zero h_exp

/-- Build conductor-flexible reciprocal source data from the source-conductor
covariance/exact-exponent package and split-orbit hypotheses. -/
noncomputable def K2_2FlexibleReciprocalSourceData.ofSourceConductorSigmaSplit
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (hP_bot : P ≠ ⊥)
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (hcop : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = 1)
    (hE :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1)
    (h_ram :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.concrete.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (h_inertia :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.concrete.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0) :
    K2_2FlexibleReciprocalSourceData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_exp :
      S.StickelbergerExactConjugateExponents
        (flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
          S h_psi h_ne_zero) := by
    simpa [flexibleReciprocalPhiCandidate] using
      S.exactExponents_phiPrimeGenDescent_sub_one_sourceConductorSigma_split
        h_psi hcop hf hE h_ne_zero
  refine
    { hP_bot := hP_bot
      hℓ_in_P := hℓ_in_P
      hp_notin_P := hp_notin_P
      h_psi := h_psi
      h_zeta_k_eq := h_zeta_k_eq
      h_zeta_p_int_eq := h_zeta_p_int_eq
      h_ne_zero := h_ne_zero
      h_span := ?_ }
  simpa [flexibleReciprocalPhiCandidate] using
    flexibleReciprocalPhiCandidate_span_of_atomic_split
      (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
      h_psi h_descentPrime h_ne_zero h_exp h_ram h_inertia

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
