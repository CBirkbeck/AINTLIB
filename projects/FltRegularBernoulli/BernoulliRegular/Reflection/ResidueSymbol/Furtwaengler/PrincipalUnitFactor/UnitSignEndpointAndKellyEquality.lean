module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.ConjNormSemiPrimaryAndUnitFactorData

/-!
# Principal unit factor (REF-18 Phase 2, sub-piece U)

For a nonzero principal ideal `(α)`, the actual multiplicative Φ element
`Φ((α))` and the explicit Stickelberger principal generator
`α^Θ = stickelbergerPrincipalGen α` generate the same ideal. Hence they differ
by a unit:

```
Φ((α)) = u(α) · α^Θ.
```

This file formalizes the honest element-level U-chain interface:

* `PrincipalUnitFactorData α Φα` is the specific unit-factor equation for an
  actual principal Φ element `Φα`.
* `PrincipalUnitFactorData.nonempty_of_nonzero` proves existence of such a
  unit from the already formalized Φ-span theorem.
* If that specific unit is `±1`, its prime residue symbols vanish.
* `ChosenPrimaryUnitFactorProductSymbolZero α` is the reflection-facing
  chosen-object product condition: the same actual Φ element has locally
  trivial product symbols for `Φ((α)) · α` away from `α`.
* `ChosenPrimaryUnitFactorSymbolTrivial α` is the natural chosen-object
  downstream output from one normalized actual principal Φ element.
* `PrimaryUnitFactorSymbolTrivial α` is the stronger uniform downstream
  hypothesis over the current broad `PhiPrincipalElement` API.
* The concrete U4 endpoint is proved in
  `PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts` and
  `ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts`: for an
  actual principal Φ product, prime-level semi-primarity plus the prime
  conjugation-norm identities force the specific unit factor to be `±1`, hence
  its prime symbols vanish.

What remains outside this file is constructing the actual principal Φ product
from `K2_2SourceData` for every normalized prime factor and proving the
conjugation compatibility needed for those prime norm identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace PrincipalUnitFactorData

theorem unitUnit_conj_mul_self_eq_one_of_conj_gamma_mul_self_eq_conj_stick_mul_self
    [IsCMField K]
    {α : 𝓞 K} (hα : α ≠ 0)
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_conj_norm :
      ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
        ringOfIntegersComplexConj K
          (stickelbergerPrincipalGen (p := p) (K := K) α) *
            stickelbergerPrincipalGen (p := p) (K := K) α) :
    unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit = 1 := by
  let S : 𝓞 K := stickelbergerPrincipalGen (p := p) (K := K) α
  let u : (𝓞 K)ˣ := U.unit_isUnit.unit
  have hu_val : (u : 𝓞 K) = U.unit :=
    IsUnit.unit_spec U.unit_isUnit
  have hgamma : Φα.gamma = (u : 𝓞 K) * S := by
    rw [hu_val]
    exact U.gamma_eq_unit_mul
  have hu_conj :
      ringOfIntegersComplexConj K (u : 𝓞 K) =
        ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) := by
    rfl
  have hconj_gamma :
      ringOfIntegersComplexConj K Φα.gamma =
        ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) *
          ringOfIntegersComplexConj K S := by
    calc
      ringOfIntegersComplexConj K Φα.gamma =
          ringOfIntegersComplexConj K ((u : 𝓞 K) * S) := by
            rw [hgamma]
      _ = ringOfIntegersComplexConj K (u : 𝓞 K) *
          ringOfIntegersComplexConj K S := by
            rw [map_mul]
      _ = ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) *
          ringOfIntegersComplexConj K S := by
            rw [hu_conj]
  have hS_ne : S ≠ 0 := by
    simpa [S] using stickelbergerPrincipalGen_ne_zero (p := p) (K := K) hα
  have hconjS_ne : ringOfIntegersComplexConj K S ≠ 0 := by
    intro hzero
    have hcc : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K S) = S := by
      apply RingOfIntegers.ext
      simp [coe_ringOfIntegersComplexConj, complexConj_apply_apply]
    have hS_zero : S = 0 := by
      rw [← hcc, hzero, map_zero]
    exact hS_ne hS_zero
  have hprod_ne : ringOfIntegersComplexConj K S * S ≠ 0 :=
    mul_ne_zero hconjS_ne hS_ne
  have hprod :
      (((unitsComplexConj K u * u : (𝓞 K)ˣ) : 𝓞 K) *
          (ringOfIntegersComplexConj K S * S)) =
        ringOfIntegersComplexConj K S * S := by
    calc
      (((unitsComplexConj K u * u : (𝓞 K)ˣ) : 𝓞 K) *
          (ringOfIntegersComplexConj K S * S))
          =
          (((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) *
            ringOfIntegersComplexConj K S) * ((u : 𝓞 K) * S) := by
              simp [Units.val_mul]
              ring
      _ = ringOfIntegersComplexConj K Φα.gamma * Φα.gamma := by
              rw [hconj_gamma, hgamma]
      _ = ringOfIntegersComplexConj K S * S := by
              simpa [S] using h_conj_norm
  apply Units.ext
  apply mul_right_cancel₀ hprod_ne
  simpa [hu_val] using hprod

/-- The signed-norm version of the concrete Φ conjugation product formula
still forces the specific unit factor to be antisymmetric.

The formal Stickelberger calculation naturally gives the signed integer norm
`Algebra.norm ℤ α`, while the actual Φ product gives the absolute ideal norm.
If those signs differed, the unit would satisfy `conj(u) * u = -1`, impossible
after applying a complex embedding. -/
theorem unitUnit_conj_mul_self_eq_one_of_conj_gamma_absNorm_pow
    [IsCMField K] (hp_odd : p ≠ 2)
    {α : 𝓞 K} (hα : α ≠ 0)
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_phi_abs :
      ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
        (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
          𝓞 K)) ^ p)
    (h_stick_int :
      ringOfIntegersComplexConj K
          (stickelbergerPrincipalGen (p := p) (K := K) α) *
          stickelbergerPrincipalGen (p := p) (K := K) α =
        (((Algebra.norm ℤ α : ℤ) : 𝓞 K)) ^ p) :
    unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit = 1 := by
  let u : (𝓞 K)ˣ := U.unit_isUnit.unit
  let v : (𝓞 K)ˣ := unitsComplexConj K u * u
  let n : ℤ := Algebra.norm ℤ α
  let N : 𝓞 K := ((n : ℤ) : 𝓞 K)
  have hn_ne : n ≠ 0 := by
    simpa [n] using (Algebra.norm_ne_zero_iff.mpr hα :
      Algebra.norm ℤ α ≠ 0)
  have hN_ne : N ≠ 0 := fun hzero =>
    hn_ne ((FaithfulSMul.algebraMap_injective ℤ (𝓞 K)) (by
      simpa [N] using hzero))
  have hNpow_ne : N ^ p ≠ 0 :=
    pow_ne_zero p hN_ne
  have hfactor :=
    U.conj_gamma_mul_self_eq_unit_conj_mul_self_mul_conj_stick_mul_self
      (p := p) (K := K)
  have hv_eq_abs :
      (v : 𝓞 K) * N ^ p =
        (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
          𝓞 K)) ^ p := by
    have hfactor' := hfactor
    rw [h_phi_abs, h_stick_int] at hfactor'
    simpa [v, u, n, N] using hfactor'.symm
  by_cases hn_nonneg : 0 ≤ n
  · apply Units.ext
    apply mul_right_cancel₀ hNpow_ne
    have h_abs :
        (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
          𝓞 K)) = N := by
      rw [Ideal.absNorm_span_singleton]
      have hnatAbs : (n.natAbs : ℤ) = n :=
        Int.natAbs_of_nonneg hn_nonneg
      change (((n.natAbs : ℕ) : ℤ) : 𝓞 K) = N
      simpa [N] using congrArg (fun z : ℤ => ((z : ℤ) : 𝓞 K)) hnatAbs
    have hv_eq_one : (v : 𝓞 K) * N ^ p = 1 * N ^ p := by
      calc
        (v : 𝓞 K) * N ^ p =
            (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
              𝓞 K)) ^ p := hv_eq_abs
        _ = N ^ p := by rw [h_abs]
        _ = 1 * N ^ p := by ring
    simpa [v, u] using hv_eq_one
  · exfalso
    have hn_nonpos : n ≤ 0 := le_of_not_ge hn_nonneg
    have h_abs :
        (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
          𝓞 K)) = -N := by
      rw [Ideal.absNorm_span_singleton]
      have hnatAbs : (n.natAbs : ℤ) = -n := by
        have hneg : ((-n).natAbs : ℤ) = -n :=
          Int.natAbs_of_nonneg (neg_nonneg.mpr hn_nonpos)
        simpa [Int.natAbs_neg] using hneg
      change (((n.natAbs : ℕ) : ℤ) : 𝓞 K) = -N
      simpa [N] using congrArg (fun z : ℤ => ((z : ℤ) : 𝓞 K)) hnatAbs
    have hp_odd' : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp_odd
    have hv_eq_neg : (v : 𝓞 K) * N ^ p = -N ^ p := by
      calc
        (v : 𝓞 K) * N ^ p =
            (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
              𝓞 K)) ^ p := hv_eq_abs
        _ = (-N) ^ p := by rw [h_abs]
        _ = -N ^ p := hp_odd'.neg_pow N
    have hv_val_neg : (v : 𝓞 K) = -1 := by
      apply mul_right_cancel₀ hNpow_ne
      calc
        (v : 𝓞 K) * N ^ p = -N ^ p := hv_eq_neg
        _ = (-1 : 𝓞 K) * N ^ p := by ring
    have hv_neg : v = -1 := Units.ext hv_val_neg
    exact unitsComplexConj_mul_self_ne_neg_one (K := K) u hv_neg

end PrincipalUnitFactorData

/-! ### Symbols of `±1` -/

/-- The canonical prime symbol vanishes at `1`, with no side conditions on the
ideal because the bad cases are definitionally zero. -/
theorem pthSymbolAtPrime_canonical_one_all
    (P : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (1 : 𝓞 K) P = 0 := by
  by_cases hbot : P = ⊥
  · simp [pthSymbolAtPrime_canonical, hbot]
  by_cases hmax : P.IsMaximal
  · exact pthSymbolAtPrime_canonical_one (p := p) (K := K) hbot hmax
  · simp [pthSymbolAtPrime_canonical, hbot, hmax]

/-- The canonical prime symbol vanishes at `-1` for odd `p`, with no side
conditions on the ideal because the bad cases are definitionally zero. -/
theorem pthSymbolAtPrime_canonical_neg_one_of_odd
    (hp_odd : Odd p) (P : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (-1 : 𝓞 K) P = 0 := by
  by_cases hbot : P = ⊥
  · simp [pthSymbolAtPrime_canonical, hbot]
  by_cases hmax : P.IsMaximal
  · have h_pow :=
      pthSymbolAtPrime_canonical_pow (p := p) (K := K)
        (α := (-1 : 𝓞 K)) (q := P) hbot hmax
        (neg_one_notMem_of_isMaximal (K := K) hmax) p
    have h_pow_p : ((-1 : 𝓞 K) ^ p) = -1 := Odd.neg_one_pow hp_odd
    rwa [h_pow_p, ZMod.natCast_self, zero_mul] at h_pow
  · simp [pthSymbolAtPrime_canonical, hbot, hmax]

/-- If the specific principal unit factor is `±1`, its prime symbols vanish. -/
theorem PrincipalUnitFactorData.unit_prime_symbol_zero_of_isSign
    (hp_odd : Odd p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hU : U.IsSign (p := p) (K := K)) :
    ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0 := by
  intro P
  rcases hU with hU | hU
  · rw [hU]
    exact pthSymbolAtPrime_canonical_one_all (p := p) (K := K) P
  · rw [hU]
    exact pthSymbolAtPrime_canonical_neg_one_of_odd (p := p) (K := K) hp_odd P

/-- The ideal-level symbol of `-1` is trivial for odd `p`. -/
theorem pthSymbolAtIdeal_canonical_neg_one_of_odd
    (hp_odd : Odd p) (B : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (-1 : 𝓞 K) B = 0 := by
  have h_pow_p : ((-1 : 𝓞 K) ^ p) = -1 := Odd.neg_one_pow hp_odd
  have := pthSymbolAtIdeal_canonical_neg_one_pow_p_eq_zero (p := p) (K := K) B
  rwa [h_pow_p] at this

/-! ### Honest U-chain hypotheses and consumers -/

/-- **Symbol-trivial principal unit factor.**

This is the corrected consumable U-chain statement. For every actual
principal Φ element attached to `α`, there is a specific unit-factor equation
`Φ((α)) = u · α^Θ`, and that same unit has trivial prime symbols. -/
def PrimaryUnitFactorSymbolTrivial (α : 𝓞 K) : Prop :=
  ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α,
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
      ∀ P : Ideal (𝓞 K),
        pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0

/-- Chosen-object version of the symbol-trivial principal unit factor.

This is weaker than `PrimaryUnitFactorSymbolTrivial` and is the natural output
of constructing one normalized actual principal Φ element. -/
def ChosenPrimaryUnitFactorSymbolTrivial (α : 𝓞 K) : Prop :=
  ∃ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α,
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
      ∀ P : Ideal (𝓞 K),
        pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0

/-- Chosen-object U-chain data plus the exact product-power identity for the
same actual principal Φ element.

This is the reflection-facing product-side input that avoids quantifying over
all `PhiPrincipalElement`s, since that API intentionally admits unit twists. -/
def ChosenPrimaryUnitFactorProductPower (α : 𝓞 K) : Prop :=
  ∃ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α,
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
      (∀ P : Ideal (𝓞 K),
        pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0) ∧
        ∃ β : 𝓞 K, Φα.gamma * α = β ^ p

/-- Chosen-object U-chain data plus the exact local product-symbol vanishing
for the same actual principal Φ element.

This is weaker than `ChosenPrimaryUnitFactorProductPower` and is exactly what
the reflection transfer needs: at primes containing `α`, the canonical symbol
of `α` is zero by convention, so the product only has to be controlled away
from `α`. -/
def ChosenPrimaryUnitFactorProductSymbolZero (α : 𝓞 K) : Prop :=
  ∃ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α,
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
      (∀ P : Ideal (𝓞 K),
        pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0) ∧
        ∀ P : Ideal (𝓞 K), α ∉ P →
          pthSymbolAtPrime_canonical (p := p) (K := K) (Φα.gamma * α) P = 0

/-- A symbol-trivial principal Φ unit factor identifies the exact product unit
once the same actual Φ element has a `p`-power product with `α`.

This is the honest U-to-product bridge: the unit in the product presentation is
not chosen independently, but is the inverse of the specific unit relating
`Φ((α))` to `α^Θ`. -/
theorem PrincipalUnitFactorData.productUnit_zero_away_of_phi_mul_eq_pow
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hU_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0)
    (h_phi_product : ∃ β : 𝓞 K, Φα.gamma * α = β ^ p) :
    ∃ u : (𝓞 K)ˣ, ∃ β : 𝓞 K,
      stickelbergerPrincipalGen (p := p) (K := K) α * α =
          (u : 𝓞 K) * β ^ p ∧
        ∀ P : Ideal (𝓞 K), α ∉ P →
      pthSymbolAtPrime_canonical (p := p) (K := K) (u : 𝓞 K) P = 0 := by
  obtain ⟨β, hβ⟩ := h_phi_product
  let u : (𝓞 K)ˣ := U.unit_isUnit.unit⁻¹
  refine ⟨u, β, ?_, ?_⟩
  · have h_inv_mul : (u : 𝓞 K) * U.unit = 1 := by
      dsimp [u]
      simp [IsUnit.val_inv_mul U.unit_isUnit]
    calc
      stickelbergerPrincipalGen (p := p) (K := K) α * α =
          1 * (stickelbergerPrincipalGen (p := p) (K := K) α * α) := by
            ring
      _ = ((u : 𝓞 K) * U.unit) *
            (stickelbergerPrincipalGen (p := p) (K := K) α * α) := by
            rw [h_inv_mul]
      _ = (u : 𝓞 K) * ((U.unit *
            stickelbergerPrincipalGen (p := p) (K := K) α) * α) := by
            ring
      _ = (u : 𝓞 K) * (Φα.gamma * α) := by
            rw [← U.gamma_eq_unit_mul]
      _ = (u : 𝓞 K) * β ^ p := by
            rw [hβ]
  · intro P _hα_not
    dsimp [u]
    exact
      pthSymbolAtPrime_canonical_isUnit_inv_eq_zero
        (p := p) (K := K) U.unit_isUnit hU_zero P

/-- Chosen-object product-power data supplies the exact product-unit condition
used by the product-transfer endpoint. -/
theorem productUnit_zero_away_of_chosenPrimaryUnitFactorProductPower
    {α : 𝓞 K}
    (h_product : ChosenPrimaryUnitFactorProductPower (p := p) (K := K) α) :
    ∃ u : (𝓞 K)ˣ, ∃ β : 𝓞 K,
      stickelbergerPrincipalGen (p := p) (K := K) α * α =
          (u : 𝓞 K) * β ^ p ∧
        ∀ P : Ideal (𝓞 K), α ∉ P →
          pthSymbolAtPrime_canonical (p := p) (K := K) (u : 𝓞 K) P = 0 := by
  obtain ⟨Φα, U, hU_zero, h_phi_product⟩ := h_product
  exact
    PrincipalUnitFactorData.productUnit_zero_away_of_phi_mul_eq_pow
      (p := p) (K := K) U hU_zero h_phi_product

/-- A chosen actual-Φ product power gives the weaker chosen actual-Φ local
product-symbol condition. -/
theorem ChosenPrimaryUnitFactorProductSymbolZero_of_chosenPrimaryUnitFactorProductPower
    {α : 𝓞 K}
    (h_product : ChosenPrimaryUnitFactorProductPower (p := p) (K := K) α) :
    ChosenPrimaryUnitFactorProductSymbolZero (p := p) (K := K) α := by
  obtain ⟨Φα, U, hU_zero, h_phi_product⟩ := h_product
  obtain ⟨β, hβ⟩ := h_phi_product
  refine ⟨Φα, U, hU_zero, ?_⟩
  intro P _hα_not
  rw [hβ]
  exact pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond β P

/-- Chosen-object version of
`PrincipalUnitFactorData.productUnit_zero_away_of_phi_mul_eq_pow`.  The
product-power hypothesis is deliberately tied to every actual principal Φ
element, so it applies to the object selected by the chosen U-chain data. -/
theorem productUnit_zero_away_of_chosenPrimaryUnitFactor_of_phi_mul_eq_pow
    {α : 𝓞 K}
    (h_chosen : ChosenPrimaryUnitFactorSymbolTrivial (p := p) (K := K) α)
    (h_phi_product :
      ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
          (p := p) (K := K) α,
        ∃ β : 𝓞 K, Φα.gamma * α = β ^ p) :
    ∃ u : (𝓞 K)ˣ, ∃ β : 𝓞 K,
      stickelbergerPrincipalGen (p := p) (K := K) α * α =
          (u : 𝓞 K) * β ^ p ∧
        ∀ P : Ideal (𝓞 K), α ∉ P →
          pthSymbolAtPrime_canonical (p := p) (K := K) (u : 𝓞 K) P = 0 := by
  obtain ⟨Φα, U, hU_zero⟩ := h_chosen
  exact
    productUnit_zero_away_of_chosenPrimaryUnitFactorProductPower
      (p := p) (K := K)
      ⟨Φα, U, hU_zero, h_phi_product Φα⟩

/-- The classical primary sign statement, isolated as the genuine remaining
U4 arithmetic input. -/
def PrimaryUnitFactorSignHypothesis (α : 𝓞 K) : Prop :=
  FLT37.IsPrimary p (K := K) α → α ≠ 0 →
    ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
        (p := p) (K := K) α,
      ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
        U.IsSign (p := p) (K := K)

/-- The mathematically sharper U4 sign statement. The classical proof only
uses semi-primarity, i.e. congruence modulo `(ζ - 1)^2`, not the stronger
project-level `IsPrimary` congruence modulo `(ζ - 1)^{2p}`. -/
def SemiPrimaryUnitFactorSignHypothesis (α : 𝓞 K) : Prop :=
  FLT37.IsSemiPrimary p (K := K) α → α ≠ 0 →
    ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
        (p := p) (K := K) α,
      ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
        U.IsSign (p := p) (K := K)

/-- The precise normalization input needed to finish U4 from the formalized
torsion-unit calculation.

For the specific principal Φ element, the unit in
`Φ((α)) = u(α) · α^Θ` must be the normalized Gauss-sum unit: a torsion unit,
and semi-primary when `α` is semi-primary. This is strictly stronger than
knowing only that `Φ((α))` and `α^Θ` generate the same ideal. -/
def SemiPrimaryUnitFactorTorsionNormalizationHypothesis (α : 𝓞 K) : Prop :=
  FLT37.IsSemiPrimary p (K := K) α → α ≠ 0 →
    ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
        (p := p) (K := K) α,
      ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
        U.unit_isUnit.unit ∈ CyclotomicUnitTorsion K ∧
          FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K)

/-- Data-carrying normalized principal Φ-unit factor.

This is the Lean-facing form of the missing classical normalization theorem:
for the actual principal Φ element, the same unit appearing in
`Φ((α)) = u · α^Θ` is both cyclotomic torsion and semi-primary.  Packaging the
factor equation and the two normalization facts together prevents replacing
the actual Gauss-sum unit by an arbitrary unit coming from equality of
principal ideals. -/
structure NormalizedPrincipalPhiUnitData
    (α : 𝓞 K)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α) where
  /-- The actual Φ-to-Stickelberger principal unit factor. -/
  factor : PrincipalUnitFactorData (p := p) (K := K) α Φα
  /-- The associated global unit is cyclotomic torsion. -/
  factor_torsion : factor.unit_isUnit.unit ∈ CyclotomicUnitTorsion K
  /-- The associated global unit is semi-primary. -/
  factor_isSemiPrimary :
    FLT37.IsSemiPrimary p (K := K) (factor.unit_isUnit.unit : 𝓞 K)

namespace NormalizedPrincipalPhiUnitData

/-- A normalized principal Φ-unit factor is a sign. -/
theorem isSign
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (D : NormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα) :
    D.factor.IsSign (p := p) (K := K) := by
  have hsign :=
    torsion_unit_isSign_of_isSemiPrimary
      (p := p) (K := K) hp_odd hp_three D.factor.unit_isUnit.unit
      D.factor_torsion D.factor_isSemiPrimary
  rcases hsign with hsign | hsign
  · left
    simpa [IsUnit.unit_spec D.factor.unit_isUnit] using hsign
  · right
    simpa [IsUnit.unit_spec D.factor.unit_isUnit] using hsign

/-- A normalized principal Φ-unit factor has trivial prime symbols. -/
theorem unit_prime_symbol_zero
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (D : NormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα) :
    ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) D.factor.unit P = 0 :=
  D.factor.unit_prime_symbol_zero_of_isSign
    (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd)
    (D.isSign (p := p) (K := K) hp_odd hp_three)

/-- A normalized principal Φ-unit factor supplies the corrected U-chain output
for its specific actual principal Φ element. -/
theorem symbolTrivial
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (D : NormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα) :
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
      ∀ P : Ideal (𝓞 K),
        pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0 :=
  ⟨D.factor, D.unit_prime_symbol_zero (p := p) (K := K) hp_odd hp_three⟩

end NormalizedPrincipalPhiUnitData

/-- A chosen normalized actual principal Φ element.

This is the right data shape for the classical construction: build one actual
principal Φ product from the Gauss-sum/Dwork choices, and keep its normalized
unit factor. The current `PhiPrincipalElement` type is broader than this,
because it is stable under arbitrary unit twists. -/
structure NormalizedPrincipalPhiElement (α : 𝓞 K) where
  /-- The actual principal Φ element. -/
  phi : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement (p := p) (K := K) α
  /-- The normalized unit data for this actual Φ element. -/
  normalized : NormalizedPrincipalPhiUnitData (p := p) (K := K) α phi

namespace NormalizedPrincipalPhiElement

/-- A chosen normalized actual principal Φ element supplies a specific
symbol-trivial unit factor. -/
theorem symbolTrivial
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    (D : NormalizedPrincipalPhiElement (p := p) (K := K) α) :
    ∃ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
        (p := p) (K := K) α,
      ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
        ∀ P : Ideal (𝓞 K),
          pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0 :=
  ⟨D.phi, D.normalized.symbolTrivial (p := p) (K := K) hp_odd hp_three⟩

/-- A chosen normalized actual principal Φ element plugged directly into the
terminal signed K-chain endpoint. -/
theorem kellyPrimeNegEquality
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    (D : NormalizedPrincipalPhiElement (p := p) (K := K) α)
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (D.phi.primePhi P hP) Q)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeNegEquality_of_phi_unit_factor
    (p := p) (K := K) D.phi hP'_ne hcop h_prime D.normalized.factor.unit_isUnit
    (D.normalized.unit_prime_symbol_zero (p := p) (K := K) hp_odd hp_three)
    D.normalized.factor.gamma_eq_unit_mul h_coprime

end NormalizedPrincipalPhiElement

/-- The genuine chosen-object U4 normalization target for semi-primary
numerators. -/
def SemiPrimaryChosenNormalizedPrincipalPhiHypothesis (α : 𝓞 K) : Prop :=
  FLT37.IsSemiPrimary p (K := K) α → α ≠ 0 →
    Nonempty (NormalizedPrincipalPhiElement (p := p) (K := K) α)

/-- Uniform U4 normalization target over the current broad
`PhiPrincipalElement` API.

For every actual principal Φ element attached to a nonzero semi-primary `α`,
the Φ-to-`α^Θ` unit factor comes equipped with the torsion and semi-primary
normalizations needed to force it to be a sign. This is stronger than the
classical chosen-object construction, because `PhiPrincipalElement` also admits
unit-twisted representatives. -/
def SemiPrimaryUniformNormalizedPrincipalPhiUnitHypothesis (α : 𝓞 K) : Prop :=
  FLT37.IsSemiPrimary p (K := K) α → α ≠ 0 →
    ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
        (p := p) (K := K) α,
      Nonempty (NormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα)

/-- The data-carrying normalized principal Φ-unit theorem implies the
normalization hypothesis used by the rest of the U-chain. -/
theorem SemiPrimaryUnitFactorTorsionNormalizationHypothesis_of_uniformNormalized
    {α : 𝓞 K}
    (h_norm :
      SemiPrimaryUniformNormalizedPrincipalPhiUnitHypothesis (p := p) (K := K) α) :
    SemiPrimaryUnitFactorTorsionNormalizationHypothesis (p := p) (K := K) α := by
  intro hsemi hα Φα
  obtain ⟨D⟩ := h_norm hsemi hα Φα
  exact ⟨D.factor, D.factor_torsion, D.factor_isSemiPrimary⟩

/-- The data-carrying normalized principal Φ-unit theorem implies the
semi-primary sign hypothesis. -/
theorem SemiPrimaryUnitFactorSignHypothesis_of_uniformNormalized
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) {α : 𝓞 K}
    (h_norm :
      SemiPrimaryUniformNormalizedPrincipalPhiUnitHypothesis (p := p) (K := K) α) :
    SemiPrimaryUnitFactorSignHypothesis (p := p) (K := K) α := by
  intro hsemi hα Φα
  obtain ⟨D⟩ := h_norm hsemi hα Φα
  exact ⟨D.factor, D.isSign (p := p) (K := K) hp_odd hp_three⟩

/-- A specific principal unit factor is a sign as soon as its associated
global unit is torsion and semi-primary. This is the proved root-of-unity
part of the classical U4 argument. -/
theorem PrincipalUnitFactorData.isSign_of_unit_torsion_of_unit_isSemiPrimary
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_torsion : U.unit_isUnit.unit ∈ CyclotomicUnitTorsion K)
    (h_semi : FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K)) :
    U.IsSign (p := p) (K := K) := by
  have hsign :=
    torsion_unit_isSign_of_isSemiPrimary
      (p := p) (K := K) hp_odd hp_three U.unit_isUnit.unit h_torsion h_semi
  rcases hsign with hsign | hsign
  · left
    simpa [IsUnit.unit_spec U.unit_isUnit] using hsign
  · right
    simpa [IsUnit.unit_spec U.unit_isUnit] using hsign

/-- A specific principal unit factor is a sign as soon as its associated
global unit is antisymmetric under complex conjugation and semi-primary. This
is the sharper classical U4 endpoint: the torsion condition follows from
conjugation rather than being supplied as an abstract hypothesis. -/
theorem PrincipalUnitFactorData.isSign_of_unitsComplexConj_mul_self_eq_one_of_unit_isSemiPrimary
    [IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_conj : unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit = 1)
    (h_semi : FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K)) :
    U.IsSign (p := p) (K := K) :=
  U.isSign_of_unit_torsion_of_unit_isSemiPrimary
    (p := p) (K := K) hp_odd hp_three
    (unit_mem_cyclotomicUnitTorsion_of_unitsComplexConj_mul_self_eq_one
      (p := p) (K := K) hp_odd U.unit_isUnit.unit h_conj)
    h_semi

/-- Concrete U4 endpoint from the actual Φ congruence and conjugation
normalization.

If the concrete principal Φ element is semi-primary, the Stickelberger
principal generator is prime to `ζ - 1`, and the resulting unit satisfies the
classical conjugation identity `conj(u)u = 1`, then the unit is `±1`. -/
theorem PrincipalUnitFactorData.isSign_of_conj_of_gamma_isSemiPrimary
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_conj : unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit = 1)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hgamma_semi : FLT37.IsSemiPrimary p (K := K) Φα.gamma)
    (h_stick_not_dvd :
      ¬ FLT37.zetaSubOne p K ∣
        stickelbergerPrincipalGen (p := p) (K := K) α) :
    U.IsSign (p := p) (K := K) :=
  U.isSign_of_unitsComplexConj_mul_self_eq_one_of_unit_isSemiPrimary
    (p := p) (K := K) hp_odd hp_three h_conj
    (U.unitUnit_isSemiPrimary_of_gamma_isSemiPrimary
      (p := p) (K := K) hp_two hp_three
      hα_semi hgamma_semi h_stick_not_dvd)

/-- Concrete U4 endpoint with the natural prime-to-`ζ - 1` hypothesis on
`α`, rather than on the derived Stickelberger product. -/
theorem PrincipalUnitFactorData.isSign_of_conj_of_gamma_isSemiPrimary_of_not_zetaSubOne_dvd
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_conj : unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit = 1)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hα_not_dvd : ¬ FLT37.zetaSubOne p K ∣ α)
    (hgamma_semi : FLT37.IsSemiPrimary p (K := K) Φα.gamma) :
    U.IsSign (p := p) (K := K) :=
  U.isSign_of_conj_of_gamma_isSemiPrimary
    (p := p) (K := K) hp_odd hp_two hp_three h_conj hα_semi
    hgamma_semi
    (not_zetaSubOne_dvd_stickelbergerPrincipalGen
      (p := p) (K := K) hp_two hα_not_dvd)

/-- Direct U4 endpoint from prime-level Φ semi-primarity and the concrete
Φ conjugation product formula.

This is the current no-abstraction target for the remaining Gauss-sum
calculation: prove the prime Φ factors are semi-primary, prove the product
identity
`conj(Φ((α))) * Φ((α)) = conj(α^Θ) * α^Θ`, and the actual unit factor is
forced to be `±1`. -/
theorem PrincipalUnitFactorData.isSign_of_primePhiSemi_conjNorm
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_conj_norm :
      ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
        ringOfIntegersComplexConj K
          (stickelbergerPrincipalGen (p := p) (K := K) α) *
            stickelbergerPrincipalGen (p := p) (K := K) α)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hα_not_dvd : ¬ FLT37.zetaSubOne p K ∣ α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma) :
    U.IsSign (p := p) (K := K) := by
  have h_conj :
      unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit = 1 :=
    U.unitUnit_conj_mul_self_eq_one_of_conj_gamma_mul_self_eq_conj_stick_mul_self
      (p := p) (K := K) hα_ne h_conj_norm
  have hgamma_semi :
      FLT37.IsSemiPrimary p (K := K) Φα.gamma :=
    phiPrincipalGamma_isSemiPrimary_of_prime_semi
      (p := p) (K := K) Φα h_prime_semi
  exact U.isSign_of_conj_of_gamma_isSemiPrimary_of_not_zetaSubOne_dvd
    (p := p) (K := K) hp_odd hp_two hp_three
    h_conj hα_semi hα_not_dvd hgamma_semi

/-- REF-18-facing U4 endpoint from prime-level Φ semi-primarity and the
concrete Φ conjugation product formula.

This version uses the natural singular-recipient hypothesis
`Ideal.span {α, p} = ⊤` to prove the required nondivisibility by `ζ_p - 1`
internally. -/
theorem PrincipalUnitFactorData.isSign_of_primePhiSemi_conjNorm_of_span_pair_p_eq_top
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_conj_norm :
      ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
        ringOfIntegersComplexConj K
          (stickelbergerPrincipalGen (p := p) (K := K) α) *
            stickelbergerPrincipalGen (p := p) (K := K) α)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma) :
    U.IsSign (p := p) (K := K) :=
  U.isSign_of_primePhiSemi_conjNorm (p := p) (K := K)
    hp_odd hp_two hp_three hα_ne h_conj_norm hα_semi
    (not_zetaSubOne_dvd_of_span_pair_p_eq_top
      (p := p) (K := K) hp_three hαp_top)
    h_prime_semi

/-- Primary-version REF-18-facing U4 endpoint from prime-level Φ
semi-primarity and the concrete Φ conjugation product formula.

This is the same theorem as
`PrincipalUnitFactorData.isSign_of_primePhiSemi_conjNorm_of_span_pair_p_eq_top`,
but takes the project-level primary hypothesis and converts it internally to
the λ² semi-primary congruence used by the classical U4 argument. -/
theorem PrincipalUnitFactorData.isSign_of_primary_primePhiSemi_conjNorm_of_span_pair_p_eq_top
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (h_conj_norm :
      ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
        ringOfIntegersComplexConj K
          (stickelbergerPrincipalGen (p := p) (K := K) α) *
            stickelbergerPrincipalGen (p := p) (K := K) α)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma) :
    U.IsSign (p := p) (K := K) :=
  U.isSign_of_primePhiSemi_conjNorm_of_span_pair_p_eq_top
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top
    h_conj_norm
    (FLT37.IsPrimary.toIsSemiPrimary (p := p) (K := K) hα_primary)
    h_prime_semi

end Furtwaengler

end BernoulliRegular

end
