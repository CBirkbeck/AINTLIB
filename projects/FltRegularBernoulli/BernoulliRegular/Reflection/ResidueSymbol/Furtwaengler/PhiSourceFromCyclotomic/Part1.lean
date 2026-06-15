module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Prime Φ source data from cyclotomic split-prime bundles

This file connects the concrete cyclotomic bundle constructors from
`BundleFromCyclotomic.lean` to the corrected K2-2 source-data interface in
`PhiPrimeElement.lean`.

The constructor below is deliberately modest: it discharges the canonical
`zeta_k` and `zeta_p_int` fields from the canonical split-prime setup and
leaves the genuine arithmetic work as explicit inputs (`h_ne_zero` and
`h_span`).
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement

universe u v

/-- If one natural number lies in an ideal after nat-cast and another does not,
then the two natural numbers are distinct. -/
theorem natCast_ne_of_mem_notMem_ideal
    {A : Type u} [Semiring A] {I : Ideal A} {m n : ℕ}
    (hm : (m : A) ∈ I) (hn : (n : A) ∉ I) : m ≠ n := by
  intro hmn
  subst hmn
  exact hn hm

/-- Distinct natural primes do not divide each other. -/
theorem natPrime_not_dvd_of_ne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (hℓ_ne_p : ℓ ≠ p) :
    ¬ ℓ ∣ p := fun hdiv =>
  hℓ_ne_p ((Nat.prime_dvd_prime_iff_eq
    (Fact.out : Nat.Prime ℓ) (Fact.out : Nat.Prime p)).mp hdiv)

/-- In `ℚ(ζ_p)`, a rational prime `ℓ ≠ p` is unramified. -/
theorem ramificationIdxIn_span_natCast_eq_one_of_ne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hℓ_ne_p : ℓ ≠ p) :
    (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).ramificationIdxIn (𝓞 K) = 1 := by
  simpa using
    (IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
      (p := ℓ) (m := p) (K := K)
      (natPrime_not_dvd_of_ne (ℓ := ℓ) (p := p) hℓ_ne_p))

/-- In `ℚ(ζ_p)`, the inertia degree of `ℓ ≠ p` is the order of `ℓ` modulo
`p`. -/
theorem inertiaDegIn_span_natCast_eq_orderOf_of_ne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hℓ_ne_p : ℓ ≠ p) :
    (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDegIn (𝓞 K) =
      orderOf (ℓ : ZMod p) := by
  simpa using
    (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
      (p := ℓ) (m := p) (K := K)
      (natPrime_not_dvd_of_ne (ℓ := ℓ) (p := p) hℓ_ne_p))

/-- In `ℚ(ζ_p)`, any prime of `𝓞 K` above a rational prime `ℓ ≠ p` has
ramification index one. -/
theorem ramificationIdx_span_natCast_eq_one_of_ne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)} [P.IsPrime]
    [P.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ))]
    (hℓ_ne_p : ℓ ≠ p) :
    (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).ramificationIdx P = 1 := by
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois ({p} : Set ℕ) (K := ℚ) (L := K)
  have _ : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/ℚ)) ℤ (𝓞 K) ℚ K
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx
    (p := Ideal.span ({(ℓ : ℤ)} : Set ℤ)) (P := P) (G := Gal(K/ℚ))]
  exact ramificationIdxIn_span_natCast_eq_one_of_ne (K := K) hℓ_ne_p

/-- In `ℚ(ζ_p)`, any prime of `𝓞 K` above `ℓ ≠ p` has inertia degree equal
to the order of `ℓ` modulo `p`. -/
theorem inertiaDeg_span_natCast_eq_orderOf_of_ne
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {P : Ideal (𝓞 K)} [P.IsPrime]
    [P.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ))]
    (hℓ_ne_p : ℓ ≠ p) :
    (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDeg P =
      orderOf (ℓ : ZMod p) := by
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois ({p} : Set ℕ) (K := ℚ) (L := K)
  have _ : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/ℚ)) ℤ (𝓞 K) ℚ K
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg
    (p := Ideal.span ({(ℓ : ℤ)} : Set ℤ)) (P := P) (G := Gal(K/ℚ))]
  exact inertiaDegIn_span_natCast_eq_orderOf_of_ne (K := K) hℓ_ne_p

/-- If `ℓ` has order one modulo `p`, then `(ℓ)` has inertia degree one in
`ℚ(ζ_p)`. -/
theorem inertiaDegIn_span_natCast_eq_one_of_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hℓ_ne_p : ℓ ≠ p) (h_order : orderOf (ℓ : ZMod p) = 1) :
    (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDegIn (𝓞 K) = 1 := by
  rw [inertiaDegIn_span_natCast_eq_orderOf_of_ne (K := K) hℓ_ne_p, h_order]

/-- Maximal ideals of a ring of integers are nonzero. -/
theorem ringOfIntegers_maximal_ne_bot
    {K : Type u} [Field K] [NumberField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] :
    P ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField
    (show P.IsMaximal from inferInstance) (NumberField.RingOfIntegers.not_isField K)

/-- A normalized factor of a nonzero ideal in a ring of integers is prime. -/
theorem normalizedFactor_isPrime_of_ne_bot
    {K : Type u} [Field K] [NumberField K]
    {I P : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hP : P ∈ normalizedFactors I) :
    P.IsPrime :=
  ((Ideal.mem_normalizedFactors_iff hI).mp hP).1

/-- A normalized factor of a nonzero ideal in a ring of integers is maximal. -/
theorem normalizedFactor_isMaximal_of_ne_bot
    {K : Type u} [Field K] [NumberField K]
    {I P : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hP : P ∈ normalizedFactors I) :
    P.IsMaximal :=
  Ideal.IsPrime.isMaximal
    (normalizedFactor_isPrime_of_ne_bot (K := K) hI hP)
    (ne_zero_of_mem_normalizedFactors hP)

/-- A normalized factor of `(α)` is maximal when `α ≠ 0`. -/
theorem normalizedFactor_span_singleton_isMaximal
    {K : Type u} [Field K] [NumberField K]
    {α : 𝓞 K} (hα_ne : α ≠ 0) {P : Ideal (𝓞 K)}
    (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))) :
    P.IsMaximal :=
  normalizedFactor_isMaximal_of_ne_bot (K := K)
    ((Ideal.span_singleton_eq_bot.not).mpr hα_ne) hP

/-- If `P` is a normalized factor of `(α)` and `(α, p) = ⊤`, then `p ∉ P`. -/
theorem natCast_notMem_of_normalizedFactor_span_pair_eq_top
    {K : Type u} [Field K] [NumberField K]
    {p : ℕ} {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))) :
    (p : 𝓞 K) ∉ P := by
  intro hp_mem
  have hI_ne :
      Ideal.span ({α} : Set (𝓞 K)) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot.not).mpr hα_ne
  have hI_le_P :
      Ideal.span ({α} : Set (𝓞 K)) ≤ P :=
    ((Ideal.mem_normalizedFactors_iff hI_ne).mp hP).2
  have hα_mem : α ∈ P :=
    hI_le_P (Ideal.mem_span_singleton_self α)
  have hspan_le :
      Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) ≤ P := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hα_mem
    · exact hp_mem
  have hP_prime : P.IsPrime :=
    normalizedFactor_isPrime_of_ne_bot (K := K) hI_ne hP
  exact hP_prime.ne_top (by
    rw [hαp_top] at hspan_le
    exact top_le_iff.mp hspan_le)

/-- Dwork exact order gives nonvanishing of the integral Gauss sum power at
any valid ordinary-character index. -/
theorem gaussSumInt_pow_p_ne_zero_of_dwork
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p ≠ 0 := by
  have h_not :=
    (S.gaussSumInt_qadic_ord_at_prime_ord_dwork a ha₁ ha₂).2
  exact S.toConcreteStickelbergerSetup.gaussSumInt_pow_p_ne_zero_of_ne_zero
    (S.toConcreteStickelbergerSetup.gaussSumInt_ne_zero_of_not_mem_Q_pow_succ
      (a := a) (d := S.stickOrdOrd a) h_not)

/-- Build `K2_2SourceData` from a `FullTeichDworkSetup` whose underlying
concrete bundle is the canonical K-algebra-compatible split-prime setup.

The point of this constructor is to make the Stage 4 constructor chain usable by
the K/U source-data route: the canonical `zeta_k` and `zeta_p_int` fields are
discharged from the bundle identity, while the actual Gauss-sum non-vanishing
and descended-span equality remain as the substantive caller inputs. -/
noncomputable def K2_2SourceData.ofCanonicalConcrete
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_concrete :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toConcreteStickelbergerSetup =
        CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_span :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  refine
    { hP_bot := hP_ne_bot
      hℓ_in_P := hℓ_in_P
      hp_notin_P := hp_notin_P
      h_zeta_k_eq := ?_
      h_zeta_p_int_eq := ?_
      h_ne_zero := h_ne_zero
      h_span := h_span }
  · rw [h_concrete]
    simp [CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat,
      CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical]
  · rw [h_concrete]
    simp [CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat,
      CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical,
      CyclotomicLocalSetup.canonical_zeta_p_int]

/-- Trace-form variant of `K2_2SourceData.ofCanonicalConcrete`.

If the Dwork bundle's trace-form layer is the canonical compatible split-prime
trace-form constructor, the concrete-layer identity required by
`ofCanonicalConcrete` follows automatically. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_span :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_concrete :
      S.toConcreteStickelbergerSetup =
        CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat := by
    calc
      S.toConcreteStickelbergerSetup =
          S.toTraceFormStickelbergerSetup.toConcreteStickelbergerSetup := rfl
      _ =
          (CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
            (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
            Q hQ_in iso h_compat).toConcreteStickelbergerSetup := by
        rw [h_trace]
      _ =
          CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
            (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
            Q hQ_in iso h_compat := by
        simp
  exact K2_2SourceData.ofCanonicalConcrete
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat
    h_concrete h_ne_zero h_span

/-- **Constructor for `K2_2TargetData`** from an explicit choice of
over-prime `Q` and the residue characteristic data. Caller supplies
the over-prime, its CharP witness, and the side conditions. -/
def K2_2TargetData.mk_ofOverPrime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_bot : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (char_over : CharP (𝓞 R' ⧸ overPrime) ell')
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (hℓ_ne_ℓ' : ℓ ≠ ell') :
    K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P' :=
  { hP'_bot := hP'_bot
    hp_notin_P' := hp_notin_P'
    overPrime := overPrime
    overPrime_max := overPrime_max
    ell' := ell'
    ell'_prime := ell'_prime
    char_over := char_over
    h_over := h_over
    hℓ_ne_ℓ' := hℓ_ne_ℓ' }

/-- **`K2_2TargetData` constructor with auto-discharged `char_over`**.
Same as `mk_ofOverPrime` but takes `(ell' : 𝓞 R') ∈ overPrime` instead of an
explicit `CharP` witness. The CharP is derived via
`charP_residueField_of_natCast_mem` from `Uniformizer.lean`. -/
def K2_2TargetData.mk_ofOverPrime_natCast
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_bot : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (hell'_in_overPrime : (ell' : 𝓞 R') ∈ overPrime)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (hℓ_ne_ℓ' : ℓ ≠ ell') :
    K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P' :=
  letI : Fact ell'.Prime := ell'_prime
  letI : overPrime.IsMaximal := overPrime_max
  K2_2TargetData.mk_ofOverPrime
    (ℓ := ℓ) (p := p) (K := K) (R' := R')
    hP'_bot hp_notin_P' overPrime overPrime_max
    ell' ell'_prime
    (charP_residueField_of_natCast_mem (F := R') (ell := ell') overPrime
      hell'_in_overPrime)
    h_over hℓ_ne_ℓ'

/-- **`K2_2TargetData` constructor using the actual quotient characteristic**.

This removes the auxiliary residue-prime choice from callers: once an
over-prime of `𝓞 R'` over `P'` has been chosen, the target residue
characteristic is `ringChar (𝓞 R' ⧸ overPrime)`, with its `CharP` and
primality witnesses supplied by the finite residue field API. The only
remaining source-target characteristic condition is the honest one,
`ℓ ≠ ringChar (𝓞 R' ⧸ overPrime)`. -/
noncomputable def K2_2TargetData.mk_ofOverPrime_ringChar
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_bot : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (hℓ_ne_char : ℓ ≠ ringChar (𝓞 R' ⧸ overPrime)) :
    K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P' :=
  letI : overPrime.IsMaximal := overPrime_max
  letI : Field (𝓞 R' ⧸ overPrime) := Ideal.Quotient.field overPrime
  letI : Fact (Nat.Prime (ringChar (𝓞 R' ⧸ overPrime))) :=
    ⟨CharP.prime_ringChar (𝓞 R' ⧸ overPrime)⟩
  K2_2TargetData.mk_ofOverPrime
    (ℓ := ℓ) (p := p) (K := K) (R' := R')
    hP'_bot hp_notin_P' overPrime overPrime_max
    (ringChar (𝓞 R' ⧸ overPrime))
    (inferInstance : Fact (Nat.Prime (ringChar (𝓞 R' ⧸ overPrime))))
    (ringChar.charP (𝓞 R' ⧸ overPrime))
    h_over hℓ_ne_char

/-- **`K2_2TargetData` from a target prime using going-up and `ringChar`**.

For a maximal target `P'`, choose a maximal over-prime in `𝓞 R'` by the
finite-extension going-up theorem and use its actual quotient characteristic.
The caller only proves that every such over-prime has residue characteristic
different from the fixed source characteristic `ℓ`. -/
noncomputable def K2_2TargetData.mk_ofPrime_ringChar
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_bot : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (hℓ_ne_char :
      ∀ overPrime : Ideal (𝓞 R'), overPrime.IsMaximal →
        overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P' →
          ℓ ≠ ringChar (𝓞 R' ⧸ overPrime)) :
    K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P' :=
  let h_exists := exists_maximal_over_of_finite_extension (K := K) (R' := R') P'
  let overPrime : Ideal (𝓞 R') := Classical.choose h_exists
  let h_overPrime : overPrime.IsMaximal ∧
      overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P' :=
    Classical.choose_spec h_exists
  K2_2TargetData.mk_ofOverPrime_ringChar
    (ℓ := ℓ) (p := p) (K := K) (R' := R')
    hP'_bot hp_notin_P' overPrime h_overPrime.1 h_overPrime.2
    (hℓ_ne_char overPrime h_overPrime.1 h_overPrime.2)

/-- If `(ℓ : 𝓞 K)` is not in the target prime `P'`, then no over-prime above
`P'` can have quotient characteristic `ℓ`. -/
theorem ringChar_ne_of_natCast_notMem_comap
    {K : Type u} [Field K] [NumberField K]
    {R' : Type v} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} {overPrime : Ideal (𝓞 R')}
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ : ℕ} (hℓ_notin_P' : (ℓ : 𝓞 K) ∉ P') :
    ℓ ≠ ringChar (𝓞 R' ⧸ overPrime) := by
  intro hℓ_eq_char
  apply hℓ_notin_P'
  rw [← h_over, Ideal.mem_comap]
  have hmem_over : (ℓ : 𝓞 R') ∈ overPrime := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change ((ℓ : 𝓞 R' ⧸ overPrime)) = 0
    rw [hℓ_eq_char]
    exact ringChar.Nat.cast_ringChar
  simpa [map_natCast] using hmem_over

/-- If a source prime `P` contains `(ℓ : 𝓞 K)` and the rational norms of `P`
and `P'` are coprime, then the target prime `P'` cannot contain
`(ℓ : 𝓞 K)`. -/
theorem natCast_notMem_of_absNorm_coprime_of_natCast_mem
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    {K : Type u} [Field K] [NumberField K]
    {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime]
    (hP_ne : P ≠ ⊥) (hP'_ne : P' ≠ ⊥)
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    (ℓ : 𝓞 K) ∉ P' := by
  haveI : NeZero P := ⟨hP_ne⟩
  haveI : NeZero P' := ⟨hP'_ne⟩
  have h_under_P_prime : (Ideal.absNorm (P.under ℤ)).Prime :=
    Nat.absNorm_under_prime P
  have h_under_P'_prime : (Ideal.absNorm (P'.under ℤ)).Prime :=
    Nat.absNorm_under_prime P'
  have h_under_P_dvd_ell : Ideal.absNorm (P.under ℤ) ∣ ℓ := by
    have hmem_int : ((ℓ : ℤ) : 𝓞 K) ∈ P := by
      exact_mod_cast hℓ_in_P
    exact_mod_cast
      ((Int.cast_mem_ideal_iff (R := 𝓞 K) (I := P) (d := (ℓ : ℤ))).mp hmem_int)
  have h_under_P_eq_ell : Ideal.absNorm (P.under ℤ) = ℓ :=
    (Nat.prime_dvd_prime_iff_eq h_under_P_prime (Fact.out : ℓ.Prime)).mp
      h_under_P_dvd_ell
  have hℓ_dvd_P : ℓ ∣ Ideal.absNorm P := by
    simpa [h_under_P_eq_ell] using (Int.absNorm_under_dvd_absNorm P)
  intro hℓ_in_P'
  have h_under_P'_dvd_ell : Ideal.absNorm (P'.under ℤ) ∣ ℓ := by
    have hmem_int : ((ℓ : ℤ) : 𝓞 K) ∈ P' := by
      exact_mod_cast hℓ_in_P'
    exact_mod_cast
      ((Int.cast_mem_ideal_iff (R := 𝓞 K) (I := P') (d := (ℓ : ℤ))).mp hmem_int)
  have h_under_P'_eq_ell : Ideal.absNorm (P'.under ℤ) = ℓ :=
    (Nat.prime_dvd_prime_iff_eq h_under_P'_prime (Fact.out : ℓ.Prime)).mp
      h_under_P'_dvd_ell
  have hℓ_dvd_P' : ℓ ∣ Ideal.absNorm P' := by
    simpa [h_under_P'_eq_ell] using (Int.absNorm_under_dvd_absNorm P')
  have hcop_self : ℓ.Coprime ℓ := Nat.Coprime.of_dvd hℓ_dvd_P hℓ_dvd_P' hcop
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] at hcop_self
  exact (Fact.out : ℓ.Prime).ne_one hcop_self

/-- `K2_2TargetData` from a target prime whose residue characteristic is known
not to be the source characteristic by ordinary nonmembership in `P'`. -/
noncomputable def K2_2TargetData.mk_ofPrime_ringChar_notMem
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_bot : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (hℓ_notin_P' : (ℓ : 𝓞 K) ∉ P') :
    K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P' :=
  K2_2TargetData.mk_ofPrime_ringChar
    (ℓ := ℓ) (p := p) (K := K) (R' := R')
    hP'_bot hp_notin_P'
    (fun _overPrime _h_overPrime_max h_over =>
      ringChar_ne_of_natCast_notMem_comap h_over hℓ_notin_P')

/-- **Index-one symbol identity from inline over-prime data**: combines
`K2_2SourceData.index_one_symbol_eq_norm_symbol` with
`K2_2TargetData.mk_ofOverPrime_natCast`, allowing the caller to supply
the over-prime data directly without constructing a `K2_2TargetData`
record explicitly. The `CharP` field is auto-discharged from the
membership hypothesis. -/
theorem K2_2SourceData.index_one_symbol_eq_norm_symbol_natCast
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_bot : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (hell'_in_overPrime : (ell' : 𝓞 R') ∈ overPrime)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (hℓ_ne_ℓ' : ℓ ≠ ell')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) D.phi.gamma P' =
      -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P :=
  letI : Fact ell'.Prime := ell'_prime
  letI : overPrime.IsMaximal := overPrime_max
  K2_2SourceData.index_one_symbol_eq_norm_symbol
    (ℓ := ℓ) (p := p) (K := K) (R' := R') D
    (K2_2TargetData.mk_ofOverPrime_natCast
      hP'_bot hp_notin_P' overPrime overPrime_max
      ell' ell'_prime hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop

/-- **`PhiPrimeSymbolIdentity` from inline over-prime data**: combines
`PhiPrimeSymbolIdentity.of_K2_2SourceData` with
`K2_2TargetData.mk_ofOverPrime_natCast`, allowing the caller to supply
the over-prime data directly. The `CharP` field is auto-discharged. -/
theorem PhiPrimeSymbolIdentity.of_K2_2SourceData_natCast
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ_bot : Q ≠ ⊥)
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (hell'_in_overPrime : (ell' : 𝓞 R') ∈ overPrime)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    (hℓ_ne_ℓ' : ℓ ≠ ell')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    PhiPrimeSymbolIdentity (p := p) (K := K) D.phi Q :=
  letI : Fact ell'.Prime := ell'_prime
  letI : overPrime.IsMaximal := overPrime_max
  PhiPrimeSymbolIdentity.of_K2_2SourceData
    (ℓ := ℓ) (p := p) (K := K) (R' := R') D
    (K2_2TargetData.mk_ofOverPrime_natCast
      hQ_bot hp_notin_Q overPrime overPrime_max
      ell' ell'_prime hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop

/-- **Positive `PhiPrimeSymbolIdentity` from inline over-prime data**:
combines `PhiPrimeSymbolIdentityPos.of_K2_2ReciprocalSourceData` with
`K2_2TargetData.mk_ofOverPrime_natCast`, allowing reciprocal-index source
data to feed the positive K-chain without a separate target-data record. -/
theorem PhiPrimeSymbolIdentityPos.of_K2_2ReciprocalSourceData_natCast
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ_bot : Q ≠ ⊥)
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (hell'_in_overPrime : (ell' : 𝓞 R') ∈ overPrime)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    (hℓ_ne_ℓ' : ℓ ≠ ell')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    PhiPrimeSymbolIdentityPos (p := p) (K := K) D.phi Q :=
  letI : Fact ell'.Prime := ell'_prime
  letI : overPrime.IsMaximal := overPrime_max
  PhiPrimeSymbolIdentityPos.of_K2_2ReciprocalSourceData
    (ℓ := ℓ) (p := p) (K := K) (R' := R') D
    (K2_2TargetData.mk_ofOverPrime_natCast
      hQ_bot hp_notin_Q overPrime overPrime_max
      ell' ell'_prime hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop

/-- **Cyclotomic conjugation-norm**: for `K = ℚ(ζ_p)` (p > 2) and
`R' = ℚ(ζ_p, ζ_ℓ)` (p ≠ ℓ, both prime), the actual descended Φ
element from a `K2_2SourceData D` satisfies
`conj(D.phi.gamma) * D.phi.gamma = absNorm(P)^p`.

This wraps Riccardo's `K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_upstairsComplexConj`,
discharging the IsCMField R' instance and the upstairs-conj-lifts-conj
hypothesis automatically using the cyclotomic-pair structure. -/
theorem K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  haveI : NumberField.IsCMField R' :=
    isCMField_of_cyclotomicExtension_pair_primes (p := p) (ℓ := ℓ) hpℓ
  exact PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_upstairsComplexConj
    D (upstairsComplexConj_lifts_downstairs (p := p) (ℓ := ℓ) hpℓ hp_gt_two)

/-- **Reciprocal cyclotomic conjugation-norm**: the reciprocal-index actual
descended Φ element satisfies
`conj(D.phi.gamma) * D.phi.gamma = absNorm(P)^p` in the cyclotomic pair. -/
theorem
    K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  haveI : NumberField.IsCMField R' :=
    isCMField_of_cyclotomicExtension_pair_primes (p := p) (ℓ := ℓ) hpℓ
  exact
    PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_upstairsComplexConj
      D (upstairsComplexConj_lifts_downstairs (p := p) (ℓ := ℓ) hpℓ hp_gt_two)

/-- **Cyclotomic Kelly endpoint from K2_2SourceData family**: composes
the K-chain to deliver `kellyPrimeNegEquality` for `α` against `P'`,
given a `K2_2SourceData` family at every normalized prime factor of
`(α)` (with shared cyclotomic-pair structure on `R'`).

Caller supplies, for each `P ∈ normalizedFactors (α)`, the maximality
witness, the `Algebra (ZMod ℓ)` instance, and the K2_2SourceData. The
semi-primary and conj-norm facts on each `D P` are discharged
internally using `K2_2SourceData_phi_gamma_isSemiPrimary` and
`K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_cyclotomic`. -/
theorem kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (primePhi : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        PhiPrimeElement (p := p) (K := K) P)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        haveI : NumberField.IsCMField K :=
          IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
        NumberField.IsCMField.ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (primePhi P hP) Q)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hp_odd : p ≠ 2 := fun h => by rw [h] at hp_gt_two; omega
  have hp_two : 2 ≤ p := le_of_lt hp_gt_two
  exact kellyPrimeNegEquality_of_primary_primePhiFamilyFacts
    (K := K) (p := p) hp_odd hp_two hp_three hα_ne hαp_top
    primePhi hα_primary h_prime_semi h_prime_norm hP'_ne hcop
    h_prime_symbol h_coprime

/-- **Cyclotomic Kelly endpoint when target `P'` is prime**: simplifies the
existing `kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic` by
replacing the per-`Q ∈ normalizedFactors P'` hypothesis with the single
identity at `Q = P'`. Internally, since `P'` is prime,
`normalizedFactors P' = {P'}` (modulo `normalize P' = P'` which holds for
ideals), so the inner forall over `Q` becomes a single application. -/
theorem kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (primePhi : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        PhiPrimeElement (p := p) (K := K) P)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        haveI : NumberField.IsCMField K :=
          IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
        NumberField.IsCMField.ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol_at_P' :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (primePhi P hP) P')
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hP'_irr : Irreducible P' :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      ((Ideal.isPrime_iff_bot_or_prime.mp ‹P'.IsPrime›).resolve_left hP'_ne)
  have h_factors : normalizedFactors P' = {P'} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP'_irr,
        normalize_eq]
  refine kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic
    (ℓ := ℓ) (R' := R') hp_gt_two hp_three hα_ne hαp_top primePhi h_prime_semi
    h_prime_norm hα_primary hP'_ne hcop ?_ h_coprime
  intro P hP Q hQ
  rw [h_factors, Multiset.mem_singleton] at hQ
  subst hQ
  exact h_prime_symbol_at_P' P hP

/-- **Positive cyclotomic Kelly endpoint from reciprocal-oriented prime Φ
data**: same K/U handoff as
`kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic`, but the
prime-symbol hypotheses use the positive reciprocal orientation and the
conclusion is the ordinary `kellyPrimeEquality`. -/
theorem kellyPrimeEquality_of_K2_2ReciprocalSourceDataFamily_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (primePhi : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        PhiPrimeElement (p := p) (K := K) P)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        haveI : NumberField.IsCMField K :=
          IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
        NumberField.IsCMField.ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (primePhi P hP) Q)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hp_odd : p ≠ 2 := fun h => by rw [h] at hp_gt_two; omega
  have hp_two : 2 ≤ p := le_of_lt hp_gt_two
  exact kellyPrimeEquality_of_primary_primePhiFamilyFacts
    (K := K) (p := p) hp_odd hp_two hp_three hα_ne hαp_top
    primePhi hα_primary h_prime_semi h_prime_norm hP'_ne hcop
    h_prime_symbol h_coprime

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end
