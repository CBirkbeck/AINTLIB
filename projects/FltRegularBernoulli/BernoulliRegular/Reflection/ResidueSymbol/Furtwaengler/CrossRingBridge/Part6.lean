module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part5

/-!
# Cross-ring bridge: 𝓞 K / P' inside 𝓞 R' / 𝔭

For a prime ideal `P'` of `𝓞 K` and a prime `𝔭` of `𝓞 R'` lying over `P'`
(in a finite extension `R' / K`), the residue field `𝓞 R' / 𝔭` extends
the residue field `𝓞 K / P'`. This file builds the bridge:

* Existence of `𝔭` over a maximal `P'` (via going-up).
* Canonical injection `𝓞 K / P' → 𝓞 R' / 𝔭`.
* Compatible CharP transfer.

This is the first cross-ring atomic step toward K2-2 path (a):
applying the K2-1 atom in `𝓞 R' / 𝔭` (where `gaussSumInt` lives via
`algebraMap 𝓞 K 𝓞 R'`) and pulling back to `𝓞 K / P'`.

Per AI reviewer 2026-05-05 K2-2 plan: the descent atom requires this
bridge to apply K2-1 in the right ambient ring. Multi-week scope per
the plan; this file is the first chunk.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Existence of a prime above `P'` in an integral extension -/

/-- **K2-2 for the extracted `phiPrimeGen`, canonical setup form**.  This
combines the top canonical path-a theorem for `phiPrimeGenDescent` with the
unit-extraction transfer to the generator supplied by
`StickelbergerIdealEquality.of_phiPrimeGenDescent`.

The remaining non-structural inputs are exactly the current bridge gaps:
the two root-choice equalities, nonmembership of the descended generator at
`P'`, the principal-span equality with the Stickelberger ideal, nonmembership
of the extracted generator at `P'`, and vanishing of the local symbol of the
extracted unit. -/
theorem K2_2_phiPrimeGen_of_canonical_zeta_choices_via_extracted_unit
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
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ')
    (h_span : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P)
    (h_stick_gen_notin :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (StickelbergerIdealEquality.of_phiPrimeGenDescent
        S ha₁ ha₂ h_ne_zero h_span).gen ∉ P')
    (hu_symbol_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
        S ha₁ ha₂ h_ne_zero h_span
      letI h_phi_ne := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
      letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
        Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) := by
        rw [h_stick.span_gen, ← h_span]
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K)
        ((unitFactorOfSpanEq h_phi_ne h_span_eq : (𝓞 K)ˣ) : 𝓞 K) P' = 0) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen
          (StickelbergerIdealEquality.of_phiPrimeGenDescent
            S ha₁ ha₂ h_ne_zero h_span)) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_K_chain :=
    K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zeta_choices
      hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq h_zeta_p_int_eq
      ha₁ ha₂ h_ne_zero
      hP'_bot hp_in_P' h_phi_notin_P'
      h_over hℓ_ne_ℓ'
  exact K_chain_at_h_stick_gen_via_extracted_unit
    S ha₁ ha₂ h_ne_zero hP'_bot hP'_max h_phi_notin_P'
    h_span h_K_chain h_stick_gen_notin hu_symbol_zero

/-- **K2-2 for the extracted `phiPrimeGen`, index `1`**.  This is the
caller-facing specialization of
`K2_2_phiPrimeGen_of_canonical_zeta_choices_via_extracted_unit` in the form
closest to the prime Φ-symbol identity: the index factor disappears. -/
theorem K2_2_phiPrimeGen_of_canonical_zeta_choices_via_extracted_unit_index_one
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
    (h_one_le_p_minus_one : 1 ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt 1 ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S (le_refl 1) h_one_le_p_minus_one h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ')
    (h_span : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) h_one_le_p_minus_one h_ne_zero} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P)
    (h_stick_gen_notin :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (StickelbergerIdealEquality.of_phiPrimeGenDescent
        S (le_refl 1) h_one_le_p_minus_one h_ne_zero h_span).gen ∉ P')
    (hu_symbol_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
        S (le_refl 1) h_one_le_p_minus_one h_ne_zero h_span
      letI h_phi_ne := phiPrimeGenDescent_ne_zero S
        (le_refl 1) h_one_le_p_minus_one h_ne_zero
      letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
        Ideal.span ({phiPrimeGenDescent S
          (le_refl 1) h_one_le_p_minus_one h_ne_zero} : Set (𝓞 K)) := by
        rw [h_stick.span_gen, ← h_span]
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K)
        ((unitFactorOfSpanEq h_phi_ne h_span_eq : (𝓞 K)ˣ) : 𝓞 K) P' = 0) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen
          (StickelbergerIdealEquality.of_phiPrimeGenDescent
            S (le_refl 1) h_one_le_p_minus_one h_ne_zero h_span)) P' =
      -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_apex :=
    K2_2_phiPrimeGen_of_canonical_zeta_choices_via_extracted_unit
      hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq h_zeta_p_int_eq
      (le_refl 1) h_one_le_p_minus_one h_ne_zero
      hP'_bot hp_in_P' h_phi_notin_P'
      h_over hℓ_ne_ℓ' h_span h_stick_gen_notin hu_symbol_zero
  rw [h_apex]
  push_cast
  ring

end Furtwaengler

end BernoulliRegular

end
