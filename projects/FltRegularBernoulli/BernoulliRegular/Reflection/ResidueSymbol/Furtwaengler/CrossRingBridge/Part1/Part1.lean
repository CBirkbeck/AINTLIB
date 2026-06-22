module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp

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

/-- **Existence of a maximal prime `𝔭` of `𝓞 R'` over `P' ⊂ 𝓞 K`** when
`R'` is a finite (hence integral) extension of `K`. -/
theorem exists_maximal_over_of_finite_extension
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    (P : Ideal (𝓞 K)) [P.IsMaximal] :
    ∃ 𝔭 : Ideal (𝓞 R'), 𝔭.IsMaximal ∧
      𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P := by
  -- The kernel of algebraMap is 0 (injectivity of integers between number fields).
  have h_ker : RingHom.ker (algebraMap (𝓞 K) (𝓞 R')) ≤ P := by
    intro x hx
    have hx_zero : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 R')
      (by rw [map_zero]; simpa [RingHom.mem_ker] using hx)
    rw [hx_zero]
    exact P.zero_mem
  exact Ideal.exists_ideal_over_maximal_of_isIntegral P h_ker

/-! ### Residue field embedding `𝓞 K / P → 𝓞 R' / 𝔭`

For `𝔭 ⊂ 𝓞 R'` lying over `P ⊂ 𝓞 K` (i.e., `𝔭.comap algebraMap = P`),
the algebra map `𝓞 K → 𝓞 R'` factors through the residue fields,
giving an injection `𝓞 K / P → 𝓞 R' / 𝔭`. -/

/-- **Residue-field embedding** induced by a prime `𝔭` of `𝓞 R'` lying
over `P ⊂ 𝓞 K`. -/
def residueFieldEmbedding
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P) :
    𝓞 K ⧸ P →+* 𝓞 R' ⧸ 𝔭 :=
  Ideal.quotientMap 𝔭 (algebraMap (𝓞 K) (𝓞 R')) h_over.symm.le

@[simp] theorem residueFieldEmbedding_mk
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P)
    (x : 𝓞 K) :
    residueFieldEmbedding h_over (Ideal.Quotient.mk P x) =
      Ideal.Quotient.mk 𝔭 (algebraMap (𝓞 K) (𝓞 R') x) := by
  unfold residueFieldEmbedding
  exact Ideal.quotientMap_mk

/-- **Injectivity of the residue-field embedding**: `𝓞 K / P → 𝓞 R' / 𝔭`
is injective when `𝔭` lies over `P` (i.e., the comap is exactly `P`). -/
theorem residueFieldEmbedding_injective
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P) :
    Function.Injective (residueFieldEmbedding h_over) := by
  unfold residueFieldEmbedding
  -- Ideal.quotientMap is injective when the comap equals the source ideal.
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- Lift x to 𝓞 K, use that quotientMap_mk maps to algebraMap mod 𝔭.
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk] at hx
  -- hx: Ideal.Quotient.mk 𝔭 (algebraMap a) = 0, so algebraMap a ∈ 𝔭, so a ∈ comap = P.
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem, ← h_over]
  exact hx

/-! ### CharP transfer through the bridge

If `P ⊂ 𝓞 K` is maximal containing the rational prime `ℓ`, and `𝔭 ⊂ 𝓞 R'`
lies over `P`, then `𝔭` also contains `(ℓ : 𝓞 R')` and inherits CharP `ℓ`. -/

/-- **Rational prime transfer through `algebraMap`**: if `(ℓ : 𝓞 K) ∈ P`
and `𝔭` lies over `P`, then `(ℓ : 𝓞 R') ∈ 𝔭`. -/
theorem natCast_mem_of_lies_over
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P)
    {ℓ : ℕ} (h : (ℓ : 𝓞 K) ∈ P) :
    (ℓ : 𝓞 R') ∈ 𝔭 := by
  -- (ℓ : 𝓞 R') = algebraMap (ℓ : 𝓞 K). Then ℓ ∈ P ⟹ algebraMap ℓ ∈ algebraMap '' P ⊆ 𝔭.
  rw [← map_natCast (algebraMap (𝓞 K) (𝓞 R')) ℓ]
  -- Goal: algebraMap (ℓ : 𝓞 K) ∈ 𝔭
  rw [← Ideal.mem_comap, h_over]
  exact h

/-- **CharP transfer**: if `𝔭 ⊂ 𝓞 R'` lies over `P ⊂ 𝓞 K` and `P` contains
the rational prime `ℓ`, then `𝓞 R' ⧸ 𝔭` has characteristic `ℓ`. -/
theorem charP_quotient_of_lies_over
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P)
    {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : (ℓ : 𝓞 K) ∈ P) :
    CharP (𝓞 R' ⧸ 𝔭) ℓ :=
  charP_quotient_of_natPrime_mem 𝔭 hℓ
    (natCast_mem_of_lies_over h_over h)

/-! ### MulChar / AddChar reduction along ring hom

For `χ : MulChar R R'` with `χ^p = 1` and a ring hom `σ : R' →+* R''`,
the post-composition `χ.ringHomComp σ : MulChar R R''` also satisfies
`(χ.ringHomComp σ)^p = 1`. This is needed to apply K2-1 in `R'' = 𝓞 R' / 𝔭`. -/

/-- **`(χ.ringHomComp σ)^p = 1` from `χ^p = 1`**: the order property
descends through ring homs. -/
theorem mulChar_ringHomComp_pow_eq_one
    {R : Type*} [CommMonoid R]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    (χ : MulChar R R') (σ : R' →+* R'')
    {p : ℕ} (hχ_p : χ ^ p = 1) :
    (χ.ringHomComp σ) ^ p = 1 := by
  rw [MulChar.ringHomComp_pow, hχ_p, MulChar.ringHomComp_one]

/-! ### Constructive descent generator from `FullTeichDworkSetup`

For a `FullTeichDworkSetup S`, the existing chain provides
`exists_descentPrime_pow_mul_stickOrdOrd_div` which extracts a Galois-fixed
lift `γ ∈ 𝓞 K` of `S.gaussSumInt a ^ p ∈ 𝓞 R'`. We name this lift
`phiPrimeGenDescent S a` for use in the K2-2 chain. -/

/-- **Constructive descent generator**: for index `a`, the unique lift
`γ ∈ 𝓞 K` with `algebraMap γ = S.gaussSumInt a ^ p`, extracted from
`exists_descentPrime_pow_mul_stickOrdOrd_div`. -/
def phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) : 𝓞 K :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div ha₁ ha₂ h_ne_zero).choose

theorem phiPrimeGenDescent_ne_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ≠ 0 :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div ha₁ ha₂ h_ne_zero).choose_spec.1

/-- **Constructive descent property**: `algebraMap (phiPrimeGenDescent S a)
= S.gaussSumInt a ^ p` in `𝓞 R'`. -/
theorem algebraMap_phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    algebraMap (𝓞 K) (𝓞 R') (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) =
      S.gaussSumInt a ^ p :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div ha₁ ha₂ h_ne_zero).choose_spec.2.1

/-- **Exact descent-prime valuation of the actual descended Gauss-sum.**

This is the direct valuation statement for `phiPrimeGenDescent S a`: when
the ramification index divides the Dwork exponent, the principal ideal of the
actual descended element has exactly
`p * stickOrdOrd a / descentRamificationIdx` copies of `S.descentPrime`. -/
theorem emultiplicity_descentPrime_phiPrimeGenDescent_eq_of_dwork_exactOrder
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (h_div :
      S.toConcreteStickelbergerSetup.descentRamificationIdx ∣
        p * S.stickOrdOrd a) :
    emultiplicity S.toConcreteStickelbergerSetup.descentPrime
        (Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K))) =
      (((p * S.stickOrdOrd a) /
        S.toConcreteStickelbergerSetup.descentRamificationIdx : ℕ) : ℕ∞) :=
  S.descentPrime_emultiplicity_eq_of_dwork_exactOrder ha₁ ha₂
    (phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero)
    (algebraMap_phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)
    h_div

/-- **Exact conjugate Stickelberger exponents for a `phiPrimeGenDescent S c`.**

This is the REF-18-facing bridge from the selected-prime Dwork valuation to
the full per-conjugate exponent predicate needed by `PhiSourceFromCyclotomic`.
It uses the ordinary-character convention: the selected-prime valuation of
the `a`-conjugate is supplied by the Dwork exact-order theorem at index
`p - a.val`.

The remaining hypotheses are the two concrete mathematical facts still to be
proved for the canonical bundle:
* Galois covariance of the descended element under `σ_a`;
* the arithmetic identity
  `p * stickOrdOrd (p - a.val) / descentRamificationIdx = a.val`.
-/
theorem StickelbergerExactConjugateExponents_phiPrimeGenDescent_of_sub_val_conjugates
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    {c : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ p - 1)
    (h_ne_zero : S.gaussSumInt c ^ p ≠ 0)
    (h_conj :
      ∀ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) (𝓞 R')
          (cyclotomicRingOfIntegersEquiv (p := p) K a
            (phiPrimeGenDescent S hc₁ hc₂ h_ne_zero)) =
          S.gaussSumInt (p - (a : ZMod p).val) ^ p)
    (h_div :
      ∀ a : CyclotomicUnitDelta p,
        S.toConcreteStickelbergerSetup.descentRamificationIdx ∣
          p * S.stickOrdOrd (p - (a : ZMod p).val))
    (h_num :
      ∀ a : CyclotomicUnitDelta p,
        (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
            S.toConcreteStickelbergerSetup.descentRamificationIdx =
          (a : ZMod p).val) :
    S.StickelbergerExactConjugateExponents
      (phiPrimeGenDescent S hc₁ hc₂ h_ne_zero) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine S.stickelbergerExactConjugateExponents_of_conjugate_descentPrime_emultiplicity ?_
  intro a
  set γ := phiPrimeGenDescent S hc₁ hc₂ h_ne_zero with hγ_def
  set b : ℕ := p - (a : ZMod p).val with hb_def
  have ha_ne : (a : ZMod p) ≠ 0 := a.isUnit.ne_zero
  have ha_pos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr ha_ne
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have hb₁ : 1 ≤ b := by
    rw [hb_def]
    omega
  have hb₂ : b ≤ p - 1 := by
    rw [hb_def]
    omega
  have hσγ_ne :
      cyclotomicRingOfIntegersEquiv (p := p) K a γ ≠ 0 := by
    intro h_zero
    have hγ_ne : γ ≠ 0 := by
      rw [hγ_def]
      exact phiPrimeGenDescent_ne_zero S hc₁ hc₂ h_ne_zero
    apply hγ_ne
    have h_back :
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
            (cyclotomicRingOfIntegersEquiv (p := p) K a γ) = γ := by
      rw [← cyclotomicRingOfIntegersEquiv_mul_apply, inv_mul_cancel,
        cyclotomicRingOfIntegersEquiv_one_apply]
    rw [← h_back, h_zero, map_zero]
  have h_emult :=
    S.descentPrime_emultiplicity_eq_of_dwork_exactOrder
      hb₁ hb₂ hσγ_ne (by simpa [γ, b, hγ_def, hb_def] using h_conj a)
      (by simpa [b, hb_def] using h_div a)
  rw [h_num a] at h_emult
  simpa [γ, hγ_def] using h_emult

/-- Flexible exact-conjugate Stickelberger exponents for an actual descended
Gauss-sum element.

This is the conductor-flexible analogue of
`StickelbergerExactConjugateExponents_phiPrimeGenDescent_of_sub_val_conjugates`.
It keeps the same two mathematical inputs: covariance of the descended
element under cyclotomic conjugation, and the arithmetic normalization of the
flexible Dwork exact order. -/
theorem StickelbergerExactConjugateExponents_flexiblePhiPrimeGenDescent_of_sub_val_conjugates
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {c : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ p - 1)
    (h_ne_zero : S.gaussSumInt c ^ p ≠ 0)
    (h_conj :
      ∀ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) (𝓞 R')
          (cyclotomicRingOfIntegersEquiv (p := p) K a
            (S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero)) =
          S.gaussSumInt (p - (a : ZMod p).val) ^ p)
    (h_div :
      ∀ a : CyclotomicUnitDelta p,
        S.concrete.descentRamificationIdx ∣
          p * S.stickOrdOrd (p - (a : ZMod p).val))
    (h_num :
      ∀ a : CyclotomicUnitDelta p,
        (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
            S.concrete.descentRamificationIdx =
          (a : ZMod p).val) :
    S.StickelbergerExactConjugateExponents
      (S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine S.stickelbergerExactConjugateExponents_of_conjugate_descentPrime_emultiplicity ?_
  intro a
  set γ := S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero with hγ_def
  set b : ℕ := p - (a : ZMod p).val with hb_def
  have ha_ne : (a : ZMod p) ≠ 0 := a.isUnit.ne_zero
  have ha_pos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr ha_ne
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have hb₁ : 1 ≤ b := by
    rw [hb_def]
    omega
  have hb₂ : b ≤ p - 1 := by
    rw [hb_def]
    omega
  have hσγ_ne :
      cyclotomicRingOfIntegersEquiv (p := p) K a γ ≠ 0 := by
    intro h_zero
    have hγ_ne : γ ≠ 0 := by
      rw [hγ_def]
      exact S.phiPrimeGenDescent_ne_zero h_psi hc₁ hc₂ h_ne_zero
    apply hγ_ne
    have h_back :
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
            (cyclotomicRingOfIntegersEquiv (p := p) K a γ) = γ := by
      rw [← cyclotomicRingOfIntegersEquiv_mul_apply, inv_mul_cancel,
        cyclotomicRingOfIntegersEquiv_one_apply]
    rw [← h_back, h_zero, map_zero]
  have h_emult :=
    S.descentPrime_emultiplicity_eq_of_dwork_exactOrder
      hb₁ hb₂ hσγ_ne (by simpa [γ, b, hγ_def, hb_def] using h_conj a)
      (by simpa [b, hb_def] using h_div a)
  rw [h_num a] at h_emult
  simpa [γ, hγ_def] using h_emult

/-- **Exact conjugate Stickelberger exponents for the actual `phiPrimeGenDescent S 1`.**

Index-one specialization of
`StickelbergerExactConjugateExponents_phiPrimeGenDescent_of_sub_val_conjugates`.
-/
theorem StickelbergerExactConjugateExponents_phiPrimeGenDescent_one_of_sub_val_conjugates
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (h_conj :
      ∀ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) (𝓞 R')
          (cyclotomicRingOfIntegersEquiv (p := p) K a
            (phiPrimeGenDescent S
              (le_refl 1)
              (by
                have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
                omega)
              h_ne_zero)) =
          S.gaussSumInt (p - (a : ZMod p).val) ^ p)
    (h_div :
      ∀ a : CyclotomicUnitDelta p,
        S.toConcreteStickelbergerSetup.descentRamificationIdx ∣
          p * S.stickOrdOrd (p - (a : ZMod p).val))
    (h_num :
      ∀ a : CyclotomicUnitDelta p,
        (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
            S.toConcreteStickelbergerSetup.descentRamificationIdx =
          (a : ZMod p).val) :
    S.StickelbergerExactConjugateExponents
      (phiPrimeGenDescent S
        (le_refl 1)
        (by
          have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
          omega)
        h_ne_zero) :=
  StickelbergerExactConjugateExponents_phiPrimeGenDescent_of_sub_val_conjugates
    S (le_refl 1)
    (by
      have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      omega)
    h_ne_zero h_conj h_div h_num

/-- The descent prime of a concrete setup lies over `(ℓ)` in `ℤ`. -/
theorem ConcreteStickelbergerSetup.descentPrime_under_eq_span_ell
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    S.descentPrime.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ) := by
  classical
  haveI := S.descentPrime_isPrime
  have h_ell_in : (ℓ : 𝓞 K) ∈ S.descentPrime :=
    S.descentPrime_contains_ell
  have h_ell_in_under : (ℓ : ℤ) ∈ S.descentPrime.under ℤ := by
    rw [Ideal.mem_under,
      show (algebraMap ℤ (𝓞 K) (ℓ : ℤ)) = (ℓ : 𝓞 K) from by push_cast; rfl]
    exact h_ell_in
  have h_under_ne : S.descentPrime.under ℤ ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at h_ell_in_under
    exact (by exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero : (ℓ : ℤ) ≠ 0)
      h_ell_in_under
  haveI : (S.descentPrime.under ℤ).IsPrime :=
    Ideal.IsPrime.under ℤ (P := S.descentPrime)
  haveI : (S.descentPrime.under ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance h_under_ne
  haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime
      (by exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero)]
    exact Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime ℓ)
  haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero)
  have h_span_le :
      Ideal.span ({(ℓ : ℤ)} : Set ℤ) ≤ S.descentPrime.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem]; exact h_ell_in_under
  exact (Ideal.IsMaximal.eq_of_le inferInstance
    (Ideal.IsMaximal.ne_top inferInstance) h_span_le).symm

/-- Absolute ramification of `S.Q` over `(ℓ)` in the cyclotomic field
`R' = ℚ(ζ_p, ζ_ℓ)`. -/
theorem ConcreteStickelbergerSetup.ramificationIdx_span_ell_Q_eq_ell_sub_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    Ideal.ramificationIdx (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) S.Q = ℓ - 1 := by
  classical
  haveI : IsCyclotomicExtension {ℓ, p} ℚ R' := by
    have h_swap : ({ℓ, p} : Set ℕ) = {p, ℓ} := by
      ext x
      constructor <;> rintro (rfl | rfl) <;> simp
    rwa [h_swap]
  haveI : IsCyclotomicExtension {ℓ * p} ℚ R' :=
    isCyclotomicExtension_singleton_mul_of_pair (p := ℓ) (ℓ := p)
      S.hℓ_ne_p
  haveI := S.hQ_prime
  haveI : S.Q.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) :=
    liesOver_span_ell_of_ell_mem S.Q S.Q_ne_bot' S.hQ
  have h_ne_dvd : ¬ ℓ ∣ p := fun hdvd ↦ by
    have h_eq : ℓ = p :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime ℓ)
        (Fact.out : Nat.Prime p)).mp hdvd
    exact S.hℓ_ne_p h_eq
  have h_n : (ℓ * p : ℕ) = ℓ ^ (0 + 1) * p := by simp [pow_one]
  have h_ram :
      Ideal.ramificationIdx (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) S.Q =
        ℓ ^ 0 * (ℓ - 1) := by
    have hq_ne : (Ideal.span ({(ℓ : ℤ)} : Set ℤ) : Ideal ℤ) ≠ ⊥ := by
      simp [(Fact.out : Nat.Prime ℓ).ne_zero]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' _ S.Q hq_ne]
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq (n := ℓ * p) (p := ℓ)
      (k := 0) (m := p) (K := R') (P := S.Q) h_n h_ne_dvd
  simpa using h_ram

/-- If the chosen prime of `K = ℚ(ζ_p)` is unramified over `(ℓ)`, then the
relative ramification index from `K` to `R'` is exactly `ℓ - 1`. -/
theorem ConcreteStickelbergerSetup.descentRamificationIdx_eq_ell_sub_one_of_unramified_base
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
      [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConcreteStickelbergerSetup ℓ p k K R')
    (he : (S.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1) :
    S.descentRamificationIdx = ℓ - 1 := by
  classical
  haveI := S.hQ_prime
  haveI := S.descentPrime_isPrime
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ)) ℚ K
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) ℚ K
  have h_under := S.descentPrime_under_eq_span_ell
  haveI : S.descentPrime.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) :=
    ⟨h_under.symm⟩
  haveI := S.Q_liesOver_descentPrime
  have h_base' :
      Ideal.ramificationIdx (S.descentPrime.under ℤ) S.descentPrime = 1 := by
    have hd_ne : S.descentPrime.under ℤ ≠ ⊥ := by
      rw [h_under]; simp [(Fact.out : Nat.Prime ℓ).ne_zero]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' _ S.descentPrime hd_ne,
        ← Ideal.ramificationIdxIn_eq_ramificationIdx
          (p := S.descentPrime.under ℤ) (P := S.descentPrime) (G := Gal(K/ℚ))]
    exact he
  have h_base :
      Ideal.ramificationIdx (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) S.descentPrime = 1 := by
    simpa [h_under] using h_base'
  have h_abs := S.ramificationIdx_span_ell_Q_eq_ell_sub_one
  have h_tower :
      Ideal.ramificationIdx (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) S.Q =
        Ideal.ramificationIdx (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) S.descentPrime *
          Ideal.ramificationIdx S.descentPrime S.Q := by
    simpa using Ideal.ramificationIdx_algebra_tower'
      (p := Ideal.span ({(ℓ : ℤ)} : Set ℤ)) (P := S.descentPrime) (Q := S.Q)
  rw [h_abs, h_base, one_mul] at h_tower
  simpa [ConcreteStickelbergerSetup.descentRamificationIdx] using h_tower.symm

/-- In the cyclotomic pair extension `R' = ℚ(ζ_p, ζ_ℓ)` over
`K = ℚ(ζ_p)`, a source prime of `K` above `ℓ` has relative residue degree
one in `R'`.

This is the formal split-residue fact needed by the canonical trace-form
source: adjoining `ζ_ℓ` is totally ramified at primes over `ℓ`, so it does not
enlarge the residue field over the already chosen source prime of `K`. -/
theorem cyclotomicPair_relative_inertiaDeg_eq_one_of_liesOver_sourcePrime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (h_lies : Q.under (𝓞 K) = P) :
    P.inertiaDeg Q = 1 := by
  classical
  let q : Ideal ℤ := Ideal.span ({(ℓ : ℤ)} : Set ℤ)
  letI : P.IsPrime := (show P.IsMaximal from inferInstance).isPrime
  have h_under_P : P.under ℤ = q :=
    CyclotomicLocalSetup.under_eq_span_of_natCast_mem
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  letI : P.LiesOver q := ⟨h_under_P.symm⟩
  letI : Q.LiesOver P := ⟨h_lies.symm⟩
  haveI : Q.LiesOver q := Ideal.LiesOver.trans Q P q
  have hℓ_not_dvd_p : ¬ ℓ ∣ p := fun hdvd ↦ by
    have h_eq : ℓ = p :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime ℓ)
        (Fact.out : Nat.Prime p)).mp hdvd
    exact hℓ_ne_p h_eq
  haveI hq_max : q.IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  haveI hP_max : P.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal (p := q) (P := P)
  have h_abs_K :
      q.inertiaDeg P = orderOf (ℓ : ZMod p) := by
    rw [Ideal.inertiaDeg_eq_inertiaDeg']
    simpa [q] using
      (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        (p := ℓ) (m := p) (K := K) (P := P) hℓ_not_dvd_p)
  haveI : IsCyclotomicExtension {ℓ, p} ℚ R' := by
    have h_swap : ({ℓ, p} : Set ℕ) = {p, ℓ} := by
      ext x
      constructor <;> rintro (rfl | rfl) <;> simp
    rwa [h_swap]
  haveI : IsCyclotomicExtension {ℓ * p} ℚ R' :=
    isCyclotomicExtension_singleton_mul_of_pair (p := ℓ) (ℓ := p) hℓ_ne_p
  have h_n : (ℓ * p : ℕ) = ℓ ^ (0 + 1) * p := by simp [pow_one]
  haveI hQ_max : Q.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal (p := q) (P := Q)
  have h_abs_R :
      q.inertiaDeg Q = orderOf (ℓ : ZMod p) := by
    rw [Ideal.inertiaDeg_eq_inertiaDeg']
    simpa [q] using
      (IsCyclotomicExtension.Rat.inertiaDeg_eq
        (n := ℓ * p) (p := ℓ) (k := 0) (m := p)
        (K := R') (P := Q) h_n hℓ_not_dvd_p)
  have h_tower :
      q.inertiaDeg Q = q.inertiaDeg P * P.inertiaDeg Q :=
    Ideal.inertiaDeg_algebra_tower q P Q
  have h_order_pos : 0 < orderOf (ℓ : ZMod p) := by
    have hq_pos : 0 < q.inertiaDeg P := Ideal.inertiaDeg_pos q P
    rwa [h_abs_K] at hq_pos
  have h_cancel :
      orderOf (ℓ : ZMod p) * P.inertiaDeg Q =
        orderOf (ℓ : ZMod p) * 1 := by
    rw [mul_one]
    rw [h_abs_R, h_abs_K] at h_tower
    exact h_tower.symm
  exact Nat.eq_of_mul_eq_mul_left h_order_pos h_cancel

/-- Prime-over data for a source prime, including the split residue-field
condition needed by the canonical quotient map. -/
structure Ref18SourcePrimeOverData
    (ℓ p : ℕ)
    (K : Type*) [Field K] [NumberField K]
    (R' : Type*) [Field R'] [NumberField R'] [Algebra K R']
    (P : Ideal (𝓞 K)) [P.IsMaximal] where
  /-- A prime of `𝓞 R'` above the source prime `P`. -/
  Q : Ideal (𝓞 R')
  /-- The chosen over-prime is prime. -/
  Q_isPrime : Q.IsPrime
  /-- The source residue characteristic remains in the chosen over-prime. -/
  ell_mem : (ℓ : 𝓞 R') ∈ Q
  /-- The chosen over-prime lies over `P`. -/
  lies : Q.under (𝓞 K) = P
  /-- The relative residue degree is one. -/
  inertia_one :
    letI : Q.IsPrime := Q_isPrime
    P.inertiaDeg Q = 1
  /-- Hence the canonical residue quotient map is surjective. -/
  quotient_surjective :
    letI : Q.IsPrime := Q_isPrime
    Function.Surjective
      (CyclotomicLocalSetup.canonicalQuotientMap
        (K₀ := K) (R' := R') P Q lies)

namespace Ref18SourcePrimeOverData

/-- The inverse canonical residue-field isomorphism attached to residue-degree
one source prime-over data. -/
def quotientIso
    {ℓ p : ℕ}
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R']
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (D : Ref18SourcePrimeOverData ℓ p K R' P) :
    (𝓞 R' ⧸ D.Q) ≃+* (𝓞 K ⧸ P) := by
  letI : D.Q.IsPrime := D.Q_isPrime
  exact
    CyclotomicLocalSetup.canonicalSplittingIso
      (K₀ := K) (R' := R') P D.Q D.lies D.quotient_surjective

/-- The inverse canonical quotient isomorphism is compatible with the
`K`-algebra residue map. -/
theorem quotientIso_isKAlgebraCompatible
    {ℓ p : ℕ}
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R']
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (D : Ref18SourcePrimeOverData ℓ p K R' P) :
    CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso
      (K₀ := K) D.Q P D.quotientIso := by
  letI : D.Q.IsPrime := D.Q_isPrime
  exact
    CyclotomicLocalSetup.canonicalSplittingIso_isKAlgebraCompatible
      (K₀ := K) (R' := R') P D.Q D.lies D.quotient_surjective

/-- Choose the prime-over data for one source prime in the cyclotomic pair
extension.  The only source-side arithmetic inputs are the facts that `P` lies
over `ℓ` and not over `p`; the latter prevents the degenerate `ℓ = p` case. -/
def ofFiniteCyclotomicPair
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P) :
    Ref18SourcePrimeOverData ℓ p K R' P := by
  classical
  let h_exists := exists_maximal_over_of_finite_extension (K := K) (R' := R') P
  let Q : Ideal (𝓞 R') := Classical.choose h_exists
  have hQ_spec : Q.IsMaximal ∧
      Q.comap (algebraMap (𝓞 K) (𝓞 R')) = P :=
    Classical.choose_spec h_exists
  have hQ_prime : Q.IsPrime := hQ_spec.1.isPrime
  have h_lies : Q.under (𝓞 K) = P := hQ_spec.2
  have hℓ_ne_p : ℓ ≠ p := fun h ↦
    hp_notin_P (by simpa [h] using hℓ_in_P)
  have h_inertia : P.inertiaDeg Q = 1 := by
    letI : Q.IsPrime := hQ_prime
    exact
      cyclotomicPair_relative_inertiaDeg_eq_one_of_liesOver_sourcePrime
        (K := K) (R' := R') hℓ_in_P hℓ_ne_p h_lies
  exact
    { Q := Q
      Q_isPrime := hQ_prime
      ell_mem :=
        CyclotomicLocalSetup.natCast_mem_of_under_eq
          (K₀ := K) (R' := R') (ℓ₀ := ℓ) P Q h_lies hℓ_in_P
      lies := h_lies
      inertia_one := h_inertia
      quotient_surjective := by
        letI : Q.IsPrime := hQ_prime
        exact
          CyclotomicLocalSetup.canonicalQuotientMap_surjective_of_inertiaDeg_eq_one
            (K₀ := K) (R' := R') P Q h_lies h_inertia }

end Ref18SourcePrimeOverData

end Furtwaengler

end BernoulliRegular

end
