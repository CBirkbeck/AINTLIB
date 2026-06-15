module

public import Mathlib.RingTheory.Ideal.Int
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdeal
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical

/-!
# Data-carrying ideal Φ-elements

K2-2 proves the prime Φ-symbol identity for the actual descended Gauss-sum
element attached to a prime ideal.  K2-3 is the multiplicative ideal-level
extension: for a nonzero ideal `A`, define `Φ(A)` as the product of the
actual prime Φ-elements over `normalizedFactors A`, counted with
multiplicity.

The key point is the same as in `PhiPrimeElement.lean`: this file never
replaces the actual Gauss-sum element by an arbitrary generator of the same
Stickelberger ideal.  Arbitrary generators carry the explicit unit correction
proved in K2-2c.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement

/-- Prime-level Φ-symbol identity used as the input to the multiplicative
K2-3 extension.

The sign is the sign convention currently produced by the formal K2-2
cross-ring Frobenius chain. -/
def PhiPrimeSymbolIdentity
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)} (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (Q : Ideal (𝓞 K)) : Prop :=
  pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma Q =
    -pthSymbolAtPrime_canonical (p := p) (K := K)
      (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P

/-- K2-2 supplies the prime-level Φ-symbol identity used by K2-3. -/
theorem PhiPrimeSymbolIdentity.of_K2_2SourceData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    PhiPrimeSymbolIdentity (p := p) (K := K) D.phi Q := by
  unfold PhiPrimeSymbolIdentity
  have h := K2_2SourceData.index_one_symbol_eq_norm_symbol D T hcop
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    using h

/-- Prime-level Φ-symbol identity with the positive norm-symbol orientation.

This is the orientation produced by the reciprocal-index source data
`K2_2ReciprocalSourceData`. -/
def PhiPrimeSymbolIdentityPos
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)} (ΦP : PhiPrimeElement (p := p) (K := K) P)
    (Q : Ideal (𝓞 K)) : Prop :=
  pthSymbolAtPrime_canonical (p := p) (K := K) ΦP.gamma Q =
    pthSymbolAtPrime_canonical (p := p) (K := K)
      (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P

/-- Reciprocal K2-2 source data supplies the positive prime-level Φ-symbol
identity. -/
theorem PhiPrimeSymbolIdentityPos.of_K2_2ReciprocalSourceData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    PhiPrimeSymbolIdentityPos (p := p) (K := K) D.phi Q := by
  unfold PhiPrimeSymbolIdentityPos
  have h := K2_2ReciprocalSourceData.symbol_eq_norm_symbol D T hcop
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    using h

/-- Conductor-flexible reciprocal K2-2 source data supplies the positive
prime-level Φ-symbol identity. -/
theorem PhiPrimeSymbolIdentityPos.of_K2_2FlexibleReciprocalSourceData
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
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : K2_2FlexibleTargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    PhiPrimeSymbolIdentityPos (p := p) (K := K) D.phi Q := by
  unfold PhiPrimeSymbolIdentityPos
  have h := K2_2FlexibleReciprocalSourceData.symbol_eq_norm_symbol D T hcop
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    using h

/-- Conductor-flexible index-one K2-2 source data supplies the negative
prime-level Φ-symbol identity used by the principal product cancellation. -/
theorem PhiPrimeSymbolIdentity.of_K2_2FlexibleSourceData
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
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : K2_2FlexibleTargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    PhiPrimeSymbolIdentity (p := p) (K := K) D.phi Q := by
  unfold PhiPrimeSymbolIdentity
  have h := K2_2FlexibleSourceData.symbol_eq_neg_norm_symbol D T hcop
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    using h

/-- Product of a multiset of elements outside a maximal ideal remains outside
that ideal. -/
theorem multiset_prod_notMem_of_forall_notMem
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {m : Multiset (𝓞 K)} {P : Ideal (𝓞 K)}
    (hP_max : P.IsMaximal) (hm : ∀ x ∈ m, x ∉ P) :
    m.prod ∉ P := by
  haveI : P.IsPrime := hP_max.isPrime
  induction m using Multiset.induction_on with
  | empty =>
      simpa using (hP_max.isPrime.one_notMem : (1 : 𝓞 K) ∉ P)
  | cons x m ih =>
      rw [Multiset.prod_cons]
      intro hmem
      rcases hP_max.isPrime.mem_or_mem hmem with hx | hmprod
      · exact (hm x (by simp)) hx
      · exact ih (fun y hy => hm y (by simp [hy])) hmprod

/-- Multiset-product version of numerator multiplicativity for
`pthSymbolAtIdeal_canonical`. -/
theorem pthSymbolAtIdeal_canonical_multiset_prod_α
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (m : Multiset (𝓞 K)) {I : Ideal (𝓞 K)}
    (hm : ∀ x ∈ m, ∀ P ∈ normalizedFactors I, x ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) m.prod I =
      (m.map fun x => pthSymbolAtIdeal_canonical (p := p) (K := K) x I).sum := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | cons x m ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      have hx : ∀ P ∈ normalizedFactors I, x ∉ P := fun P hP =>
        hm x (by simp) P hP
      have hmprod : ∀ P ∈ normalizedFactors I, m.prod ∉ P := by
        intro P hP
        obtain ⟨_, _, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
        exact multiset_prod_notMem_of_forall_notMem (p := p) hP_max
          (fun y hy => hm y (by simp [hy]) P hP)
      rw [pthSymbolAtIdeal_canonical_mul_α (p := p) hx hmprod]
      rw [ih (fun y hy P hP => hm y (by simp [hy]) P hP)]

/-- **Data-carrying ideal Φ element**.

`gamma` is the actual product of actual prime Φ elements over the normalized
prime factorisation of `A`. The `primePhi` field keeps the prime-level data
available, with multiplicities represented by repeated entries in
`normalizedFactors A`. -/
structure PhiIdealElement
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (A : Ideal (𝓞 K)) where
  /-- The actual multiplicative Φ element attached to `A`. -/
  gamma : 𝓞 K
  /-- The actual prime Φ element attached to each normalized prime factor of
  `A`, counted with multiplicity. -/
  primePhi :
    ∀ P : Ideal (𝓞 K), P ∈ normalizedFactors A →
      PhiPrimeElement (p := p) (K := K) P
  /-- `gamma` is the product of those actual prime Φ elements. -/
  gamma_eq_prod :
    gamma =
      ((normalizedFactors A).attach.map
        fun P => (primePhi P.1 P.2).gamma).prod

namespace PhiIdealElement

/-! ### Span of the actual multiplicative Φ element -/

/-- `stickelbergerIdeal` distributes over a multiset product of ideals. -/
theorem stickelbergerIdeal_multiset_prod
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (m : Multiset (Ideal (𝓞 K))) :
    stickelbergerIdeal (p := p) (K := K) m.prod =
      (m.map fun A => stickelbergerIdeal (p := p) (K := K) A).prod := by
  induction m using Multiset.induction_on with
  | empty =>
      change stickelbergerIdeal (p := p) (K := K) (1 : Ideal (𝓞 K)) =
        (1 : Ideal (𝓞 K))
      exact stickelbergerIdeal_one
  | cons A m ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        stickelbergerIdeal_mul, ih]

/-- **Span of the actual multiplicative Φ element.**

For a nonzero ideal `A`, the actual ideal-level Φ element, defined as the
product of actual prime Φ elements over `normalizedFactors A`, generates
`A^Θ`. -/
theorem span_gamma
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A : Ideal (𝓞 K)} (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hA : A ≠ ⊥) :
    Ideal.span ({ΦA.gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) A := by
  rw [ΦA.gamma_eq_prod]
  rw [← Ideal.multiset_prod_span_singleton]
  simp only [Multiset.map_map, Function.comp_apply]
  have h_spans_map :
      ((normalizedFactors A).attach.map
        fun P => Ideal.span ({(ΦA.primePhi P.1 P.2).gamma} : Set (𝓞 K))) =
        ((normalizedFactors A).attach.map
          fun P => stickelbergerIdeal (p := p) (K := K) P.1) := by
    refine Multiset.map_congr rfl fun P _ => ?_
    exact (ΦA.primePhi P.1 P.2).span_gamma
  have h_spans := congrArg Multiset.prod h_spans_map
  rw [h_spans]
  have h_attach :
      (((normalizedFactors A).attach.map
        fun P => stickelbergerIdeal (p := p) (K := K) P.1).prod) =
        ((normalizedFactors A).map
          fun P => stickelbergerIdeal (p := p) (K := K) P).prod := by
    simp
  rw [h_attach]
  have h_stick :=
    stickelbergerIdeal_multiset_prod (p := p) (K := K) (normalizedFactors A)
  rw [Ideal.prod_normalizedFactors_eq_self hA] at h_stick
  exact h_stick.symm

/-- Constructor for the actual multiplicative Φ element from prime-factor
data. -/
noncomputable def ofPrimeFactors
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (A : Ideal (𝓞 K))
    (primePhi :
      ∀ P : Ideal (𝓞 K), P ∈ normalizedFactors A →
        PhiPrimeElement (p := p) (K := K) P) :
    PhiIdealElement (p := p) (K := K) A where
  gamma :=
    ((normalizedFactors A).attach.map
      fun P => (primePhi P.1 P.2).gamma).prod
  primePhi := primePhi
  gamma_eq_prod := rfl

@[simp] theorem ofPrimeFactors_gamma
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (A : Ideal (𝓞 K))
    (primePhi :
      ∀ P : Ideal (𝓞 K), P ∈ normalizedFactors A →
        PhiPrimeElement (p := p) (K := K) P) :
    (ofPrimeFactors (p := p) (K := K) A primePhi).gamma =
      ((normalizedFactors A).attach.map
        fun P => (primePhi P.1 P.2).gamma).prod :=
  rfl

/-- Unit-twist each prime factor of an ideal-level Φ element.

This preserves the Stickelberger span of every prime factor, hence still
produces a valid `PhiIdealElement`. It also shows why the U4 sign statement
cannot follow from span data alone: the ideal-level API permits independent
unit twists at the prime-factor level unless the Gauss-sum normalization is
carried as extra data. -/
noncomputable def twistPrimeFactors
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (u : ∀ P : Ideal (𝓞 K), P ∈ normalizedFactors A → (𝓞 K)ˣ) :
    PhiIdealElement (p := p) (K := K) A :=
  ofPrimeFactors (p := p) (K := K) A
    fun P hP => (ΦA.primePhi P hP).twistByUnit (p := p) (K := K) (u P hP)

@[simp]
theorem twistPrimeFactors_primePhi_gamma
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (u : ∀ P : Ideal (𝓞 K), P ∈ normalizedFactors A → (𝓞 K)ˣ)
    (P : Ideal (𝓞 K)) (hP : P ∈ normalizedFactors A) :
    ((ΦA.twistPrimeFactors (p := p) (K := K) u).primePhi P hP).gamma =
      (u P hP : 𝓞 K) * (ΦA.primePhi P hP).gamma :=
  rfl

/-- Product of the rational norms of the prime factors of an ideal, viewed as
an element of `𝓞 K`. This is the multiplicative numerator produced by the
prime-by-prime K2-2 identity before it is compressed to `Ideal.absNorm B`. -/
noncomputable def idealNormFactorElement
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (B : Ideal (𝓞 K)) : 𝓞 K :=
  ((normalizedFactors B).map fun Q => (((Ideal.absNorm Q : ℤ) : 𝓞 K))).prod

/-- The multiplicative norm-factor numerator is the absolute norm of the
whole ideal when the ideal is nonzero. -/
theorem idealNormFactorElement_eq_absNorm
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) :
    idealNormFactorElement (p := p) (K := K) B =
      (((Ideal.absNorm B : ℤ) : 𝓞 K)) := by
  unfold idealNormFactorElement
  let m := normalizedFactors B
  have hcast :
      (m.map fun Q : Ideal (𝓞 K) => (((Ideal.absNorm Q : ℤ) : 𝓞 K))).prod =
        ((((m.map fun Q : Ideal (𝓞 K) => Ideal.absNorm Q).prod : ℤ) : 𝓞 K)) := by
    induction m using Multiset.induction_on with
    | empty =>
        simp
    | cons Q m ih =>
        simp
  have hnorm :
      (m.map fun Q : Ideal (𝓞 K) => Ideal.absNorm Q).prod = Ideal.absNorm B := by
    have hmap :
        Ideal.absNorm m.prod =
          (m.map fun Q : Ideal (𝓞 K) => Ideal.absNorm Q).prod := by
      simpa using (map_multiset_prod (Ideal.absNorm (S := 𝓞 K)) m)
    rw [← hmap]
    simp [m, Ideal.prod_normalizedFactors_eq_self hB]
  rw [hcast, hnorm]

/-- If the rational norms of prime ideals `P` and `Q` are coprime, then the
integer `NQ` is nonzero modulo `P`. -/
theorem natCast_absNorm_notMem_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P Q : Ideal (𝓞 K)} [P.IsPrime] [NeZero P]
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    (((Ideal.absNorm Q : ℤ) : 𝓞 K)) ∉ P := by
  intro hmem
  have hunder_prime : (Ideal.absNorm (Ideal.under ℤ P)).Prime :=
    Nat.absNorm_under_prime P
  have hunder_dvd_Q : Ideal.absNorm (Ideal.under ℤ P) ∣ Ideal.absNorm Q :=
    Int.natCast_dvd_natCast.mp
      ((Int.cast_mem_ideal_iff (R := 𝓞 K) (I := P)
        (d := (Ideal.absNorm Q : ℤ))).mp hmem)
  have hunder_dvd_P : Ideal.absNorm (Ideal.under ℤ P) ∣ Ideal.absNorm P :=
    Int.absNorm_under_dvd_absNorm P
  have hcop_under : (Ideal.absNorm (Ideal.under ℤ P)).Coprime (Ideal.absNorm Q) :=
    Nat.Coprime.of_dvd_left hunder_dvd_P hcop
  have hunder_eq_one : Ideal.absNorm (Ideal.under ℤ P) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_under (dvd_refl _) hunder_dvd_Q
  exact hunder_prime.ne_one hunder_eq_one

/-- Coprime rational norms for `A` and `B` imply each rational norm factor of
`B` is nonzero modulo each prime factor of `A`. -/
theorem norm_factor_notMem_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    {P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors A)
    {Q : Ideal (𝓞 K)} (hQ : Q ∈ normalizedFactors B) :
    (((Ideal.absNorm Q : ℤ) : 𝓞 K)) ∉ P := by
  obtain ⟨_, hP_ne, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  obtain ⟨_, _, _⟩ := isPrime_of_mem_normalizedFactors hQ
  haveI : P.IsPrime := hP_max.isPrime
  haveI : NeZero P := ⟨by simpa [Ideal.zero_eq_bot] using hP_ne⟩
  have hA_le_P : A ≤ P := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hB_le_Q : B ≤ Q := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
  have hP_dvd_A : Ideal.absNorm P ∣ Ideal.absNorm A :=
    Ideal.absNorm_dvd_absNorm_of_le hA_le_P
  have hQ_dvd_B : Ideal.absNorm Q ∣ Ideal.absNorm B :=
    Ideal.absNorm_dvd_absNorm_of_le hB_le_Q
  exact natCast_absNorm_notMem_of_absNorm_coprime (p := p) (K := K)
    (Nat.Coprime.of_dvd hP_dvd_A hQ_dvd_B hcop)

/-- Coprime rational norms for `A` and `B` imply each source prime Φ factor is
nonzero modulo each target prime factor. -/
theorem gamma_factor_notMem_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    {P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors A)
    {Q : Ideal (𝓞 K)} (hQ : Q ∈ normalizedFactors B) :
    (ΦA.primePhi P hP).gamma ∉ Q := by
  obtain ⟨_, hP_ne, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  obtain ⟨_, hQ_ne, hQ_max⟩ := isPrime_of_mem_normalizedFactors hQ
  haveI : P.IsPrime := hP_max.isPrime
  haveI : Q.IsPrime := hQ_max.isPrime
  have hA_le_P : A ≤ P := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hB_le_Q : B ≤ Q := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
  have hP_dvd_A : Ideal.absNorm P ∣ Ideal.absNorm A :=
    Ideal.absNorm_dvd_absNorm_of_le hA_le_P
  have hQ_dvd_B : Ideal.absNorm Q ∣ Ideal.absNorm B :=
    Ideal.absNorm_dvd_absNorm_of_le hB_le_Q
  have hcopPQ : (Ideal.absNorm P).Coprime (Ideal.absNorm Q) :=
    Nat.Coprime.of_dvd hP_dvd_A hQ_dvd_B hcop
  exact gamma_notMem_of_absNorm_coprime (p := p) (K := K)
    (ΦA.primePhi P hP) hP_ne hQ_ne hcopPQ

/-- **K2-3, multiplicative actual-Φ ideal version, double-sum form.**

If K2-2 is available for every pair consisting of a prime factor of `A` and a
prime factor of `B`, then the symbol of the actual multiplicative Φ element
`Φ(A)` at `B` is the corresponding double sum of integer-norm symbols.

The target is deliberately stated as a normalized-factor double sum. This is
the exact multiplicative output of K2-2 and keeps the current negative sign
convention explicit. The later K2-4 compression rewrites the inner product of
the target norms as `Ideal.absNorm B`. -/
theorem symbol_eq_double_sum_of_prime_symbol_identities
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (h_gamma_notin :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        (ΦA.primePhi P hP).gamma ∉ Q)
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentity (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      -(((normalizedFactors A).attach.map fun P =>
        ((normalizedFactors B).map fun Q =>
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum).sum) := by
  classical
  rw [ΦA.gamma_eq_prod]
  rw [pthSymbolAtIdeal_canonical_multiset_prod_α (p := p)
    (((normalizedFactors A).attach.map fun P => (ΦA.primePhi P.1 P.2).gamma))
    (I := B)]
  · rw [show
      ((((normalizedFactors A).attach.map
        fun P => (ΦA.primePhi P.1 P.2).gamma).map
          fun γ => pthSymbolAtIdeal_canonical (p := p) (K := K) γ B).sum) =
        (((normalizedFactors A).attach.map fun P =>
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (ΦA.primePhi P.1 P.2).gamma B).sum) by
          simp [Multiset.map_map]]
    have h_outer :
        ((normalizedFactors A).attach.map fun P =>
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (ΦA.primePhi P.1 P.2).gamma B) =
        ((normalizedFactors A).attach.map fun P =>
          -((normalizedFactors B).map fun Q =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum) := by
      refine Multiset.map_congr rfl fun P _ => ?_
      unfold pthSymbolAtIdeal_canonical
      have h_inner :
          ((normalizedFactors B).map fun Q =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (ΦA.primePhi P.1 P.2).gamma Q) =
          ((normalizedFactors B).map fun Q =>
            -pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1) := by
        refine Multiset.map_congr rfl fun Q hQ => ?_
        exact h_prime P.1 P.2 Q hQ
      rw [h_inner]
      simp
    rw [h_outer]
    simp
  · intro γ hγ Q hQ
    obtain ⟨P, _, rfl⟩ := Multiset.mem_map.mp hγ
    exact h_gamma_notin P.1 P.2 Q hQ

/-- K2-3 with the nonmembership hypotheses discharged from coprime rational
norms of `A` and `B`. -/
theorem symbol_eq_double_sum_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentity (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      -(((normalizedFactors A).attach.map fun P =>
        ((normalizedFactors B).map fun Q =>
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum).sum) :=
  symbol_eq_double_sum_of_prime_symbol_identities ΦA
    (fun _P hP _Q hQ => gamma_factor_notMem_of_absNorm_coprime ΦA hcop hP hQ)
    h_prime

/-- The symbol of the norm-factor numerator at `A` expands as the sum of the
symbols of the prime norm factors of `B`. -/
theorem pthSymbolAtIdeal_canonical_idealNormFactorElement
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
      (idealNormFactorElement (p := p) (K := K) B) A =
      ((normalizedFactors B).map fun Q =>
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          (((Ideal.absNorm Q : ℤ) : 𝓞 K)) A).sum := by
  unfold idealNormFactorElement
  rw [show
      ((normalizedFactors B).map fun Q : Ideal (𝓞 K) =>
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          (((Ideal.absNorm Q : ℤ) : 𝓞 K)) A) =
      (((normalizedFactors B).map fun Q : Ideal (𝓞 K) =>
        (((Ideal.absNorm Q : ℤ) : 𝓞 K))).map fun γ =>
          pthSymbolAtIdeal_canonical (p := p) (K := K) γ A) by
        simp [Multiset.map_map]]
  apply pthSymbolAtIdeal_canonical_multiset_prod_α (p := p) (K := K)
    ((normalizedFactors B).map fun Q : Ideal (𝓞 K) => (((Ideal.absNorm Q : ℤ) : 𝓞 K)))
    (I := A)
  intro γ hγ P hP
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hγ
  exact norm_factor_notMem_of_absNorm_coprime (p := p) (K := K) hcop hP hQ

/-- Finite double sums over multisets commute. -/
theorem multiset_sum_map_sum_comm
    {α β M : Type*} [AddCommMonoid M]
    (s : Multiset α) (t : Multiset β) (f : α → β → M) :
    ((s.map fun a => (t.map fun b => f a b).sum).sum) =
      ((t.map fun b => (s.map fun a => f a b).sum).sum) := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      simp [ih, Multiset.sum_map_add]

/-- The norm-factor numerator expansion written as the same double sum as
K2-3, up to the order of the two finite sums. -/
theorem pthSymbolAtIdeal_canonical_idealNormFactorElement_eq_double_sum
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
      (idealNormFactorElement (p := p) (K := K) B) A =
      ((normalizedFactors B).map fun Q =>
        ((normalizedFactors A).map fun P =>
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P).sum).sum := by
  rw [pthSymbolAtIdeal_canonical_idealNormFactorElement (p := p) (K := K) hcop]
  rfl

/-- **K2-3, multiplicative actual-Φ ideal version, norm-factor form.**

This is the usual ideal-level K2-3 statement before compressing the product
of prime norm factors to the single integer `Ideal.absNorm B`. -/
theorem symbol_eq_neg_idealNormFactorElement_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentity (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        (idealNormFactorElement (p := p) (K := K) B) A := by
  rw [symbol_eq_double_sum_of_absNorm_coprime ΦA hcop h_prime]
  rw [pthSymbolAtIdeal_canonical_idealNormFactorElement_eq_double_sum (p := p) (K := K)
    (A := A) (B := B) hcop]
  congr 1
  calc
    (((normalizedFactors A).attach.map fun P =>
      ((normalizedFactors B).map fun Q =>
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum).sum)
        =
        ((normalizedFactors B).map fun Q =>
          (((normalizedFactors A).attach.map fun P =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum)).sum :=
          multiset_sum_map_sum_comm
            ((normalizedFactors A).attach) (normalizedFactors B)
            (fun P Q =>
              pthSymbolAtPrime_canonical (p := p) (K := K)
                (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1)
    _ =
        ((normalizedFactors B).map fun Q =>
          ((normalizedFactors A).map fun P =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P).sum).sum := by
          simp

/-- **K2-3, multiplicative actual-Φ ideal version, absolute-norm form.**

For nonzero `B`, the norm-factor numerator is `Ideal.absNorm B`, giving the
standard ideal-level statement with the current formal sign convention. -/
theorem symbol_eq_neg_absNorm_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hB : B ≠ ⊥)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentity (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) A := by
  rw [symbol_eq_neg_idealNormFactorElement_of_absNorm_coprime ΦA hcop h_prime]
  rw [idealNormFactorElement_eq_absNorm (p := p) (K := K) hB]

/-- **K2-3 prime-target form**: when `B` is a prime ideal (and ≠ ⊥), the
inner `Q`-sum in `symbol_eq_neg_absNorm_of_absNorm_coprime` collapses
to a single term `Q = B`. This delivers a simpler form for the common
case where the target is a single prime. -/
theorem symbol_eq_neg_absNorm_of_absNorm_coprime_primeTarget
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hB_prime : B.IsPrime) (hB_ne : B ≠ ⊥)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    (h_prime_at_B :
      ∀ P (hP : P ∈ normalizedFactors A),
        PhiPrimeSymbolIdentity (p := p) (K := K) (ΦA.primePhi P hP) B) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) A := by
  refine symbol_eq_neg_absNorm_of_absNorm_coprime ΦA hB_ne hcop ?_
  intro P hP Q hQ
  have hB_irr : Irreducible B :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.isPrime_iff_bot_or_prime.mp hB_prime |>.resolve_left hB_ne)
  have h_factors : normalizedFactors B = {B} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hB_irr,
        normalize_eq]
  rw [h_factors, Multiset.mem_singleton] at hQ
  subst hQ
  exact h_prime_at_B P hP

/-! ### Principal actual-Φ corollary (K2-4) -/

/-- The actual multiplicative Φ element of the principal ideal `(α)`.

This is only an abbreviation for the ideal-level actual Φ object. It is
deliberately not an arbitrary generator of a Stickelberger ideal. -/
abbrev PhiPrincipalElement
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (α : 𝓞 K) : Type _ :=
  PhiIdealElement (p := p) (K := K) (Ideal.span ({α} : Set (𝓞 K)))

/-- Constructor for the actual principal Φ element from prime-factor data for
the principal ideal `(α)`. -/
noncomputable def PhiPrincipalElement.ofPrimeFactors
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (α : 𝓞 K)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P) :
    PhiPrincipalElement (p := p) (K := K) α :=
  PhiIdealElement.ofPrimeFactors (p := p) (K := K)
    (Ideal.span ({α} : Set (𝓞 K))) primePhi

/-- **K2-4, principal actual-Φ corollary, canonical sign convention.**

Specialising K2-3 to the principal ideal `(α)`, the symbol of the actual
principal Φ element at `B` is the negative of the principal symbol
`(NB / α)_p`, where `NB = Ideal.absNorm B`.

The negative sign is the sign convention currently produced by the formal
K2-2 Frobenius chain. -/
theorem principal_symbol_eq_neg_norm_principal_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrincipalElement (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentity (p := p) (K := K) (Φα.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) Φα.gamma B =
      -pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  rw [symbol_eq_neg_absNorm_of_absNorm_coprime Φα hB hcop h_prime]
  rfl

/-! ### Positive-orientation principal actual-Φ corollary -/

/-- K2-3 double-sum form with positive prime-symbol orientation. -/
theorem symbol_eq_double_sum_pos_of_prime_symbol_identities
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (h_gamma_notin :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        (ΦA.primePhi P hP).gamma ∉ Q)
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentityPos (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      (((normalizedFactors A).attach.map fun P =>
        ((normalizedFactors B).map fun Q =>
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum).sum) := by
  classical
  rw [ΦA.gamma_eq_prod]
  rw [pthSymbolAtIdeal_canonical_multiset_prod_α (p := p)
    (((normalizedFactors A).attach.map fun P => (ΦA.primePhi P.1 P.2).gamma))
    (I := B)]
  · rw [show
      ((((normalizedFactors A).attach.map
        fun P => (ΦA.primePhi P.1 P.2).gamma).map
          fun γ => pthSymbolAtIdeal_canonical (p := p) (K := K) γ B).sum) =
        (((normalizedFactors A).attach.map fun P =>
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (ΦA.primePhi P.1 P.2).gamma B).sum) by
          simp [Multiset.map_map]]
    have h_outer :
        ((normalizedFactors A).attach.map fun P =>
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (ΦA.primePhi P.1 P.2).gamma B) =
        ((normalizedFactors A).attach.map fun P =>
          ((normalizedFactors B).map fun Q =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum) := by
      refine Multiset.map_congr rfl fun P _ => ?_
      unfold pthSymbolAtIdeal_canonical
      have h_inner :
          ((normalizedFactors B).map fun Q =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (ΦA.primePhi P.1 P.2).gamma Q) =
          ((normalizedFactors B).map fun Q =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1) := by
        refine Multiset.map_congr rfl fun Q hQ => ?_
        exact h_prime P.1 P.2 Q hQ
      rw [h_inner]
    rw [h_outer]
  · intro γ hγ Q hQ
    obtain ⟨P, _, rfl⟩ := Multiset.mem_map.mp hγ
    exact h_gamma_notin P.1 P.2 Q hQ

/-- Positive-orientation K2-3 with nonmembership discharged from coprime
rational norms. -/
theorem symbol_eq_double_sum_pos_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentityPos (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      (((normalizedFactors A).attach.map fun P =>
        ((normalizedFactors B).map fun Q =>
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum).sum) :=
  symbol_eq_double_sum_pos_of_prime_symbol_identities ΦA
    (fun _P hP _Q hQ => gamma_factor_notMem_of_absNorm_coprime ΦA hcop hP hQ)
    h_prime

/-- Positive-orientation K2-3, norm-factor form. -/
theorem symbol_eq_idealNormFactorElement_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentityPos (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (idealNormFactorElement (p := p) (K := K) B) A := by
  rw [symbol_eq_double_sum_pos_of_absNorm_coprime ΦA hcop h_prime]
  rw [pthSymbolAtIdeal_canonical_idealNormFactorElement_eq_double_sum (p := p) (K := K)
    (A := A) (B := B) hcop]
  calc
    (((normalizedFactors A).attach.map fun P =>
      ((normalizedFactors B).map fun Q =>
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum).sum)
        =
        ((normalizedFactors B).map fun Q =>
          (((normalizedFactors A).attach.map fun P =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1).sum)).sum :=
          multiset_sum_map_sum_comm
            ((normalizedFactors A).attach) (normalizedFactors B)
            (fun P Q =>
              pthSymbolAtPrime_canonical (p := p) (K := K)
                (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P.1)
    _ =
        ((normalizedFactors B).map fun Q =>
          ((normalizedFactors A).map fun P =>
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P).sum).sum := by
          simp

/-- Positive-orientation K2-3, absolute-norm form. -/
theorem symbol_eq_absNorm_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {A B : Ideal (𝓞 K)}
    (ΦA : PhiIdealElement (p := p) (K := K) A)
    (hB : B ≠ ⊥)
    (hcop : (Ideal.absNorm A).Coprime (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors A) Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentityPos (p := p) (K := K) (ΦA.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ΦA.gamma B =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) A := by
  rw [symbol_eq_idealNormFactorElement_of_absNorm_coprime ΦA hcop h_prime]
  rw [idealNormFactorElement_eq_absNorm (p := p) (K := K) hB]

/-- Positive-orientation K2-4 principal actual-Φ corollary. -/
theorem principal_symbol_eq_norm_principal_of_absNorm_coprime
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α : 𝓞 K} {B : Ideal (𝓞 K)}
    (Φα : PhiPrincipalElement (p := p) (K := K) α)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        PhiPrimeSymbolIdentityPos (p := p) (K := K) (Φα.primePhi P hP) Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) Φα.gamma B =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  rw [symbol_eq_absNorm_of_absNorm_coprime Φα hB hcop h_prime]
  rfl

end PhiIdealElement

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
