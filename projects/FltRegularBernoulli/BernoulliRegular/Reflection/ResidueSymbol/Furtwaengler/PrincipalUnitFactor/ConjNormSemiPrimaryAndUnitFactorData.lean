module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.ConductorFlexiblePhiFacts

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

/-- The product of all cyclotomic Galois conjugates of an algebraic integer is
its integer norm. -/
theorem prod_cyclotomicRingOfIntegersEquiv_eq_intNorm (α : 𝓞 K) :
    (∏ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a α) =
        ((Algebra.norm ℤ α : ℤ) : 𝓞 K) := by
  classical
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois ({p} : Set ℕ) ℚ K
  apply RingOfIntegers.ext
  change algebraMap (𝓞 K) K
      (∏ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a α) =
    algebraMap (𝓞 K) K (((Algebra.norm ℤ α : ℤ) : 𝓞 K))
  rw [map_prod]
  have hprod :
      (∏ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) K
          (cyclotomicRingOfIntegersEquiv (p := p) K a α)) =
        ∏ σ : Gal(K / ℚ), σ (α : K) := by
    symm
    refine Fintype.prod_equiv
      (cyclotomicGalEquivZMod (p := p) K)
      (fun σ : Gal(K / ℚ) => σ (α : K))
      (fun a : CyclotomicUnitDelta p =>
        algebraMap (𝓞 K) K
          (cyclotomicRingOfIntegersEquiv (p := p) K a α)) ?_
    intro σ
    have ha : cyclotomicSigmaOfUnit (p := p) K
        (cyclotomicGalEquivZMod (p := p) K σ) = σ := by
      unfold cyclotomicSigmaOfUnit
      exact (cyclotomicGalEquivZMod (p := p) K).symm_apply_apply σ
    unfold cyclotomicRingOfIntegersEquiv
    change σ (α : K) =
      algebraMap (𝓞 K) K
        ((MulSemiringAction.toRingEquiv (Gal(K / ℚ)) (𝓞 K)
          (cyclotomicSigmaOfUnit (p := p) K
            (cyclotomicGalEquivZMod (p := p) K σ))) α)
    rw [ha]
    change σ (α : K) = algebraMap (𝓞 K) K (σ • α)
    exact (algebraMap.coe_smul' σ α K).symm
  rw [hprod]
  rw [← Algebra.norm_eq_prod_automorphisms (K := ℚ) (L := K) (x := (α : K))]
  rw [← Algebra.coe_norm_int α]
  simp

/-- The product of all inverse-indexed cyclotomic Galois conjugates is still
the integer norm. -/
theorem prod_cyclotomicRingOfIntegersEquiv_inv_eq_intNorm (α : 𝓞 K) :
    (∏ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) =
        ((Algebra.norm ℤ α : ℤ) : 𝓞 K) := by
  classical
  calc
    (∏ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α)
        =
        ∏ a : CyclotomicUnitDelta p,
          cyclotomicRingOfIntegersEquiv (p := p) K a α := by
          let e : CyclotomicUnitDelta p ≃ CyclotomicUnitDelta p := Equiv.inv _
          exact Fintype.prod_equiv e
            (fun a : CyclotomicUnitDelta p =>
              cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α)
            (fun a : CyclotomicUnitDelta p =>
              cyclotomicRingOfIntegersEquiv (p := p) K a α)
            (by intro a; simp [e])
    _ = ((Algebra.norm ℤ α : ℤ) : 𝓞 K) :=
        prod_cyclotomicRingOfIntegersEquiv_eq_intNorm
          (p := p) (K := K) α

/-- The Stickelberger conjugation product is the `p`-th power of the signed
integer norm of `α`. -/
theorem ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self_eq_intNorm_pow
    [IsCMField K] (hp_gt_two : 2 < p) {α : 𝓞 K} :
    ringOfIntegersComplexConj K
        (stickelbergerPrincipalGen (p := p) (K := K) α) *
        stickelbergerPrincipalGen (p := p) (K := K) α =
      (((Algebra.norm ℤ α : ℤ) : 𝓞 K)) ^ p := by
  rw [ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self
    (p := p) (K := K) hp_gt_two]
  have hpow :
      (∏ a : CyclotomicUnitDelta p,
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ p) =
        (∏ a : CyclotomicUnitDelta p,
          cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ p := by
    simpa using
      (Finset.prod_pow (Finset.univ : Finset (CyclotomicUnitDelta p)) p
        (fun a : CyclotomicUnitDelta p =>
          cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α))
  rw [hpow]
  rw [prod_cyclotomicRingOfIntegersEquiv_inv_eq_intNorm (p := p) (K := K) α]

/-- If the integer norm of `α` is nonnegative, the Stickelberger conjugation
product is `(N(α))^p` with the ideal absolute norm convention. -/
theorem ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self_eq_absNorm_pow
    [IsCMField K] (hp_gt_two : 2 < p) {α : 𝓞 K}
    (h_norm_nonneg : 0 ≤ Algebra.norm ℤ α) :
    ringOfIntegersComplexConj K
        (stickelbergerPrincipalGen (p := p) (K := K) α) *
        stickelbergerPrincipalGen (p := p) (K := K) α =
      (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
        𝓞 K)) ^ p := by
  rw [ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self_eq_intNorm_pow
    (p := p) (K := K) hp_gt_two]
  rw [Ideal.absNorm_span_singleton]
  have hnatAbs : (Algebra.norm ℤ α).natAbs = Algebra.norm ℤ α :=
    Int.natAbs_of_nonneg h_norm_nonneg
  rw [hnatAbs]

/-- A semi-primary unit has a semi-primary inverse. -/
theorem isSemiPrimary_unit_inv
    (hp_three : 3 ≤ p) (u : (𝓞 K)ˣ)
    (hu : FLT37.IsSemiPrimary p (K := K) (u : 𝓞 K)) :
    FLT37.IsSemiPrimary p (K := K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
  let ε : 𝓞 K := FLT37.zetaSubOne p K
  obtain ⟨a, ha⟩ := hu
  have hε_sq_dvd_p_nat :
      ε ^ 2 ∣ ((p : ℕ) : 𝓞 K) := by
    simpa [ε] using FLT37.zetaSubOne_sq_dvd_p (p := p) (K := K) hp_three
  have hε_sq_dvd_p_int :
      ε ^ 2 ∣ ((p : ℤ) : 𝓞 K) := by
    simpa using hε_sq_dvd_p_nat
  have hε_dvd_sq : ε ∣ ε ^ 2 := ⟨ε, by ring⟩
  have hε_dvd_p : ε ∣ ((p : ℤ) : 𝓞 K) :=
    hε_dvd_sq.trans hε_sq_dvd_p_int
  have hp_not_dvd_a : ¬ (p : ℤ) ∣ a := by
    intro hp_dvd_a
    have hε_dvd_u_sub_a : ε ∣ (u : 𝓞 K) - (a : 𝓞 K) :=
      hε_dvd_sq.trans (by simpa [ε] using ha)
    have hε_dvd_a : ε ∣ (a : 𝓞 K) := by
      obtain ⟨c, hc⟩ := hp_dvd_a
      rw [hc]
      convert hε_dvd_p.mul_right (c : 𝓞 K) using 1
      push_cast
      ring
    have hε_dvd_u : ε ∣ (u : 𝓞 K) := by
      have h := dvd_add hε_dvd_u_sub_a hε_dvd_a
      convert h using 1
      ring
    have hε_unit : IsUnit ε := by
      obtain ⟨w, hw⟩ := hε_dvd_u
      have hprod : IsUnit (ε * w) := by
        rw [← hw]
        exact Units.isUnit u
      exact isUnit_of_mul_isUnit_left hprod
    exact FLT37.zetaSubOne_not_isUnit (p := p) (K := K) hε_unit
  have hcop_nat : Nat.Coprime a.natAbs p := by
    have hp_prime : Nat.Prime p := Fact.out
    rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
    intro hp_dvd_abs
    exact hp_not_dvd_a
      ((Int.natCast_dvd (m := p) (n := a)).mpr hp_dvd_abs)
  have hcop_int : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Int.natAbs_natCast] using hcop_nat
  obtain ⟨b, c, hbez⟩ := hcop_int
  refine ⟨b, ?_⟩
  have haεsq : ε ^ 2 ∣ (u : 𝓞 K) - (a : 𝓞 K) := by
    simpa [ε] using ha
  have hdiff : ε ^ 2 ∣ (a : 𝓞 K) - (u : 𝓞 K) := by
    have h := haεsq.neg_right
    convert h using 1
    ring
  have hterm₁ :
      ε ^ 2 ∣
        (b : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          ((a : 𝓞 K) - (u : 𝓞 K)) :=
    hdiff.mul_left ((b : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
  have hterm₂ :
      ε ^ 2 ∣
        (c : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          ((p : ℤ) : 𝓞 K) :=
    hε_sq_dvd_p_int.mul_left ((c : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
  have hsum := dvd_add hterm₁ hterm₂
  convert hsum using 1
  have hbez_cast :
      ((b * a + c * (p : ℤ) : ℤ) : 𝓞 K) = 1 := by
    rw [hbez]
    norm_num
  have hmul_inv : (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 :=
    Units.mul_inv u
  calc
    ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - (b : 𝓞 K)
        = ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
            ((b * a + c * (p : ℤ) : ℤ) : 𝓞 K) -
          (b : 𝓞 K) * ((u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) := by
            rw [hbez_cast, hmul_inv]
            ring
    _ = (b : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          ((a : 𝓞 K) - (u : 𝓞 K)) +
        (c : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((p : ℤ) : 𝓞 K) := by
            push_cast
            ring

/-- Right-cancelling a semi-primary unit preserves semi-primarity. -/
theorem isSemiPrimary_of_mul_right_unit
    (hp_three : 3 ≤ p) {x : 𝓞 K} (u : (𝓞 K)ˣ)
    (hxu : FLT37.IsSemiPrimary p (K := K) (x * (u : 𝓞 K)))
    (hu : FLT37.IsSemiPrimary p (K := K) (u : 𝓞 K)) :
    FLT37.IsSemiPrimary p (K := K) x := by
  have hinv := isSemiPrimary_unit_inv (p := p) (K := K) hp_three u hu
  have hprod := hxu.mul hinv
  have h_eq :
      (x * (u : 𝓞 K)) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = x := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  simpa [h_eq] using hprod

/-- Left-cancelling a semi-primary unit preserves semi-primarity. -/
theorem isSemiPrimary_of_mul_left_unit
    (hp_three : 3 ≤ p) (u : (𝓞 K)ˣ) {x : 𝓞 K}
    (hux : FLT37.IsSemiPrimary p (K := K) ((u : 𝓞 K) * x))
    (hu : FLT37.IsSemiPrimary p (K := K) (u : 𝓞 K)) :
    FLT37.IsSemiPrimary p (K := K) x := by
  rw [mul_comm] at hux
  exact isSemiPrimary_of_mul_right_unit (p := p) (K := K) hp_three u hux hu

/-- Right-cancelling a semi-primary element which is prime to `ζ - 1`
preserves semi-primarity.

This is the λ² modular-inverse calculation needed in U4.  If
`y ≡ a (mod (ζ - 1)^2)` and `ζ - 1 ∤ y`, then `p ∤ a`, so a Bezout inverse
of `a` modulo `p` gives an inverse of `y` modulo `(ζ - 1)^2`. -/
theorem isSemiPrimary_of_mul_right_of_not_zetaSubOne_dvd
    (hp_three : 3 ≤ p) {x y : 𝓞 K}
    (hxy : FLT37.IsSemiPrimary p (K := K) (x * y))
    (hy : FLT37.IsSemiPrimary p (K := K) y)
    (hy_not_dvd : ¬ FLT37.zetaSubOne p K ∣ y) :
    FLT37.IsSemiPrimary p (K := K) x := by
  let ε : 𝓞 K := FLT37.zetaSubOne p K
  obtain ⟨a, ha⟩ := hy
  obtain ⟨r, hr⟩ := hxy
  have hε_sq_dvd_p_nat :
      ε ^ 2 ∣ ((p : ℕ) : 𝓞 K) := by
    simpa [ε] using FLT37.zetaSubOne_sq_dvd_p (p := p) (K := K) hp_three
  have hε_sq_dvd_p_int :
      ε ^ 2 ∣ ((p : ℤ) : 𝓞 K) := by
    simpa using hε_sq_dvd_p_nat
  have hε_dvd_sq : ε ∣ ε ^ 2 := ⟨ε, by ring⟩
  have hε_dvd_p : ε ∣ ((p : ℤ) : 𝓞 K) :=
    hε_dvd_sq.trans hε_sq_dvd_p_int
  have hp_not_dvd_a : ¬ (p : ℤ) ∣ a := by
    intro hp_dvd_a
    have hε_dvd_y_sub_a : ε ∣ y - (a : 𝓞 K) :=
      hε_dvd_sq.trans (by simpa [ε] using ha)
    have hε_dvd_a : ε ∣ (a : 𝓞 K) := by
      obtain ⟨c, hc⟩ := hp_dvd_a
      rw [hc]
      convert hε_dvd_p.mul_right (c : 𝓞 K) using 1
      push_cast
      ring
    have hε_dvd_y : ε ∣ y := by
      have h := dvd_add hε_dvd_y_sub_a hε_dvd_a
      convert h using 1
      ring
    exact hy_not_dvd (by simpa [ε] using hε_dvd_y)
  have hcop_nat : Nat.Coprime a.natAbs p := by
    have hp_prime : Nat.Prime p := Fact.out
    rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
    intro hp_dvd_abs
    exact hp_not_dvd_a
      ((Int.natCast_dvd (m := p) (n := a)).mpr hp_dvd_abs)
  have hcop_int : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa [Int.natAbs_natCast] using hcop_nat
  obtain ⟨b, c, hbez⟩ := hcop_int
  refine ⟨b * r, ?_⟩
  have haεsq : ε ^ 2 ∣ y - (a : 𝓞 K) := by
    simpa [ε] using ha
  have hdiff_y : ε ^ 2 ∣ (a : 𝓞 K) - y := by
    have h := haεsq.neg_right
    convert h using 1
    ring
  have hone_sub_by :
      ε ^ 2 ∣ (1 : 𝓞 K) - (b : 𝓞 K) * y := by
    have hterm₁ : ε ^ 2 ∣ (b : 𝓞 K) * ((a : 𝓞 K) - y) :=
      hdiff_y.mul_left (b : 𝓞 K)
    have hterm₂ : ε ^ 2 ∣ (c : 𝓞 K) * ((p : ℤ) : 𝓞 K) :=
      hε_sq_dvd_p_int.mul_left (c : 𝓞 K)
    have hsum := dvd_add hterm₁ hterm₂
    convert hsum using 1
    have hbez_cast :
        ((b * a + c * (p : ℤ) : ℤ) : 𝓞 K) = 1 := by
      rw [hbez]
      norm_num
    calc
      (1 : 𝓞 K) - (b : 𝓞 K) * y
          = ((b * a + c * (p : ℤ) : ℤ) : 𝓞 K) - (b : 𝓞 K) * y := by
              rw [hbez_cast]
      _ = (b : 𝓞 K) * ((a : 𝓞 K) - y) +
          (c : 𝓞 K) * ((p : ℤ) : 𝓞 K) := by
              push_cast
              ring
  have hrεsq : ε ^ 2 ∣ x * y - (r : 𝓞 K) := by
    simpa [ε] using hr
  have hterm₁ : ε ^ 2 ∣ (b : 𝓞 K) * (x * y - (r : 𝓞 K)) :=
    hrεsq.mul_left (b : 𝓞 K)
  have hterm₂ : ε ^ 2 ∣ x * ((1 : 𝓞 K) - (b : 𝓞 K) * y) :=
    hone_sub_by.mul_left x
  have hsum := dvd_add hterm₁ hterm₂
  convert hsum using 1
  calc
    x - ((b * r : ℤ) : 𝓞 K)
        = (b : 𝓞 K) * (x * y - (r : 𝓞 K)) +
          x * ((1 : 𝓞 K) - (b : 𝓞 K) * y) := by
            push_cast
            ring

/-- Left-cancelling a semi-primary element which is prime to `ζ - 1`
preserves semi-primarity. -/
theorem isSemiPrimary_of_mul_left_of_not_zetaSubOne_dvd
    (hp_three : 3 ≤ p) {x y : 𝓞 K}
    (hyx : FLT37.IsSemiPrimary p (K := K) (y * x))
    (hy : FLT37.IsSemiPrimary p (K := K) y)
    (hy_not_dvd : ¬ FLT37.zetaSubOne p K ∣ y) :
    FLT37.IsSemiPrimary p (K := K) x := by
  rw [mul_comm] at hyx
  exact isSemiPrimary_of_mul_right_of_not_zetaSubOne_dvd
    (p := p) (K := K) hp_three hyx hy hy_not_dvd

/-! ### Semi-primary torsion units -/

/-- If a signed power `(-1)^k ζ^m` is semi-primary, then `p ∣ m`.

This is the λ² Taylor calculation behind the last classical U4 unit step.
Modulo `(ζ - 1)^2`, one has
`(-1)^k ζ^m ≡ (-1)^k + (-1)^k m(ζ - 1)`.  If this is congruent to an
integer, then the linear coefficient must vanish modulo `p`. -/
theorem dvd_exponent_of_neg_one_pow_mul_zeta_pow_isSemiPrimary
    (hp_three : 3 ≤ p) {k m : ℕ}
    (hsemi : FLT37.IsSemiPrimary p (K := K)
      (((-1 : 𝓞 K) ^ k) *
        (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m))) :
    p ∣ m := by
  let ζ : 𝓞 K := ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K)
  let ε : 𝓞 K := ζ - 1
  let s : 𝓞 K := (-1 : 𝓞 K) ^ k
  let sInt : ℤ := (-1 : ℤ) ^ k
  have hsInt_cast : (sInt : 𝓞 K) = s := by
    simp [sInt, s]
  have hε_ne : ε ≠ 0 := by
    simpa [ε, ζ, FLT37.zetaSubOne] using
      FLT37.zetaSubOne_ne_zero (p := p) (K := K)
  obtain ⟨a, ha⟩ := hsemi
  have ha' : ε ^ 2 ∣ s * ζ ^ m - (a : 𝓞 K) := by
    simpa [ε, ζ, s, FLT37.zetaSubOne] using ha
  have htaylor₀ :
      ε ^ 2 ∣ (ζ ^ m - 1) - (m : 𝓞 K) * ε := by
    simpa [ε, ζ, FLT37.zetaSubOne] using
      FLT37.zetaSubOne_sq_dvd_zeta_pow_sub_one_sub_natCast_mul
        (p := p) (K := K) m
  have htaylor :
      ε ^ 2 ∣ s * ζ ^ m - s - s * (m : 𝓞 K) * ε := by
    obtain ⟨w, hw⟩ := htaylor₀
    refine ⟨s * w, ?_⟩
    linear_combination s * hw
  have hlinear :
      ε ^ 2 ∣ s - (a : 𝓞 K) + s * (m : 𝓞 K) * ε := by
    have h := dvd_sub ha' htaylor
    convert h using 1
    ring
  have hε_dvd_sq : ε ∣ ε ^ 2 := ⟨ε, by ring⟩
  have hlinear₁ :
      ε ∣ s - (a : 𝓞 K) + s * (m : 𝓞 K) * ε :=
    hε_dvd_sq.trans hlinear
  have hsmε : ε ∣ s * (m : 𝓞 K) * ε := ⟨s * (m : 𝓞 K), by ring⟩
  have hconst : ε ∣ s - (a : 𝓞 K) := by
    have h := dvd_sub hlinear₁ hsmε
    convert h using 1
    ring
  have hconst_cast : s - (a : 𝓞 K) = ((sInt - a : ℤ) : 𝓞 K) := by
    rw [← hsInt_cast]
    push_cast
    ring
  have hp_dvd_const : (p : ℤ) ∣ sInt - a := by
    rw [hconst_cast] at hconst
    exact (FLT37.zetaSubOne_dvd_intCast_iff (p := p) (K := K) (sInt - a)).mp
      (by simpa [ε, ζ, FLT37.zetaSubOne] using hconst)
  have hε_sq_dvd_p_int : ε ^ 2 ∣ ((p : ℤ) : 𝓞 K) := by
    have hε_sq_dvd_p_nat :
        ε ^ 2 ∣ ((p : ℕ) : 𝓞 K) := by
      simpa [ε, ζ, FLT37.zetaSubOne] using
        FLT37.zetaSubOne_sq_dvd_p (p := p) (K := K) hp_three
    simpa using hε_sq_dvd_p_nat
  have hconst_sq : ε ^ 2 ∣ s - (a : 𝓞 K) := by
    obtain ⟨c, hc⟩ := hp_dvd_const
    rw [hconst_cast, hc]
    convert hε_sq_dvd_p_int.mul_right (c : 𝓞 K) using 1
    push_cast
    ring
  have hsmε_sq : ε ^ 2 ∣ s * (m : 𝓞 K) * ε := by
    have h := dvd_sub hlinear hconst_sq
    convert h using 1
    ring
  have hsm_dvd : ε ∣ s * (m : 𝓞 K) := by
    obtain ⟨w, hw⟩ := hsmε_sq
    refine ⟨w, ?_⟩
    apply mul_left_cancel₀ hε_ne
    calc
      ε * (s * (m : 𝓞 K)) = s * (m : 𝓞 K) * ε := by ring
      _ = ε ^ 2 * w := hw
      _ = ε * (ε * w) := by ring
  have hsm_cast : s * (m : 𝓞 K) = ((sInt * (m : ℤ) : ℤ) : 𝓞 K) := by
    rw [← hsInt_cast]
    push_cast
    ring
  have hp_dvd_sm : (p : ℤ) ∣ sInt * (m : ℤ) := by
    rw [hsm_cast] at hsm_dvd
    exact (FLT37.zetaSubOne_dvd_intCast_iff
      (p := p) (K := K) (sInt * (m : ℤ))).mp
      (by simpa [ε, ζ, FLT37.zetaSubOne] using hsm_dvd)
  have hp_dvd_m_int : (p : ℤ) ∣ (m : ℤ) := by
    rcases neg_one_pow_eq_or ℤ k with hs | hs
    · simpa [sInt, hs] using hp_dvd_sm
    · have hneg : (p : ℤ) ∣ -(m : ℤ) := by
        simpa [sInt, hs] using hp_dvd_sm
      exact dvd_neg.mp hneg
  exact Int.natCast_dvd_natCast.mp hp_dvd_m_int

/-- A semi-primary torsion unit in the `p`-th cyclotomic ring of integers is
a sign. This is the formalized root-of-unity part of U4. -/
theorem torsion_unit_isSign_of_isSemiPrimary
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (u : (𝓞 K)ˣ)
    (hu_torsion : u ∈ CyclotomicUnitTorsion K)
    (hu_semi : FLT37.IsSemiPrimary p (K := K) (u : 𝓞 K)) :
    (u : 𝓞 K) = 1 ∨ (u : 𝓞 K) = -1 := by
  let uT : CyclotomicUnitTorsion K := ⟨u, hu_torsion⟩
  obtain ⟨m, k, hu_eq⟩ :=
    cyclotomic_torsion_unit_eq_neg_one_pow_mul_zeta_pow
      (p := p) (K := K) hp_odd uT
  have hu_val :
      (u : 𝓞 K) =
        (((-1 : (𝓞 K)ˣ) ^ k * cyclotomicZetaUnit (p := p) K ^ m :
          (𝓞 K)ˣ) : 𝓞 K) :=
    congrArg (fun v : CyclotomicUnitGroup K => (v : 𝓞 K)) hu_eq
  have hsemi_signed :
      FLT37.IsSemiPrimary p (K := K)
        (((-1 : 𝓞 K) ^ k) *
          (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m)) := by
    rw [hu_val] at hu_semi
    simpa [cyclotomicZetaUnit, Units.val_mul, Units.val_pow_eq_pow_val] using hu_semi
  have hm_dvd :
      p ∣ m :=
    dvd_exponent_of_neg_one_pow_mul_zeta_pow_isSemiPrimary
      (p := p) (K := K) hp_three hsemi_signed
  obtain ⟨r, rfl⟩ := hm_dvd
  have hzeta_pow :
      cyclotomicZetaUnit (p := p) K ^ (p * r) = 1 := by
    have hpow_p : cyclotomicZetaUnit (p := p) K ^ p = 1 := by
      simpa [cyclotomicZetaUnit] using
        ((cyclotomicZetaInteger_isPrimitiveRoot (p := p) K).isUnit_unit
          (Fact.out : Nat.Prime p).ne_zero).pow_eq_one
    rw [pow_mul, hpow_p, one_pow]
  have hu_sign_unit :
      u = (-1 : (𝓞 K)ˣ) ^ k := by
    have hunit :
        u =
          (-1 : (𝓞 K)ˣ) ^ k * cyclotomicZetaUnit (p := p) K ^ (p * r) := by
      simpa [uT] using
        congrArg (fun v : CyclotomicUnitGroup K => (v : (𝓞 K)ˣ)) hu_eq
    rw [hunit, hzeta_pow, mul_one]
  rcases neg_one_pow_eq_or ((𝓞 K)ˣ) k with hk | hk
  · left
    have hval : (u : 𝓞 K) = (((-1 : (𝓞 K)ˣ) ^ k : (𝓞 K)ˣ) : 𝓞 K) :=
      congrArg (fun v : (𝓞 K)ˣ => (v : 𝓞 K)) hu_sign_unit
    simpa [hk] using hval
  · right
    have hval : (u : 𝓞 K) = (((-1 : (𝓞 K)ˣ) ^ k : (𝓞 K)ˣ) : 𝓞 K) :=
      congrArg (fun v : (𝓞 K)ˣ => (v : 𝓞 K)) hu_sign_unit
    simpa [hk] using hval

omit [NumberField K] in
/-- The unit `-1` belongs to the cyclotomic torsion subgroup. -/
theorem neg_one_mem_cyclotomicUnitTorsion :
    (-1 : (𝓞 K)ˣ) ∈ CyclotomicUnitTorsion K :=
  neg_one_mem_torsion

/-- Every signed power of the distinguished primitive root of unity is
cyclotomic torsion. -/
theorem neg_one_pow_mul_zeta_pow_mem_cyclotomicUnitTorsion
    (k m : ℕ) :
    (-1 : (𝓞 K)ˣ) ^ k * cyclotomicZetaUnit (p := p) K ^ m ∈
      CyclotomicUnitTorsion K :=
  (CyclotomicUnitTorsion K).mul_mem
    ((CyclotomicUnitTorsion K).pow_mem
      (neg_one_mem_cyclotomicUnitTorsion (K := K)) k)
    ((CyclotomicUnitTorsion K).pow_mem
      (cyclotomicZetaUnit_mem_torsion (p := p) K) m)

/-- An antisymmetric unit is cyclotomic torsion.

This packages the global conjugation part of the classical U4 proof:
`conj(u) * u = 1` puts `u` among the roots of unity in the cyclotomic field. -/
theorem unit_mem_cyclotomicUnitTorsion_of_unitsComplexConj_mul_self_eq_one
    [IsCMField K] (hp_odd : p ≠ 2) (u : (𝓞 K)ˣ)
    (hu : unitsComplexConj K u * u = 1) :
    u ∈ CyclotomicUnitTorsion K := by
  obtain ⟨n, k, hu_eq⟩ :=
    antisymmetric_unit_eq_neg_one_pow_mul_zeta_pow
      (p := p) (hp_odd := hp_odd) (K := K)
      (hζ := IsCyclotomicExtension.zeta_spec p ℚ K) u hu
  rw [hu_eq]
  simpa [cyclotomicZetaUnit] using
    neg_one_pow_mul_zeta_pow_mem_cyclotomicUnitTorsion
      (p := p) (K := K) k n

/-- An antisymmetric semi-primary unit is a sign. -/
theorem unit_isSign_of_unitsComplexConj_mul_self_eq_one_of_isSemiPrimary
    [IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (u : (𝓞 K)ˣ)
    (hu_conj : unitsComplexConj K u * u = 1)
    (hu_semi : FLT37.IsSemiPrimary p (K := K) (u : 𝓞 K)) :
    (u : 𝓞 K) = 1 ∨ (u : 𝓞 K) = -1 :=
  torsion_unit_isSign_of_isSemiPrimary
    (p := p) (K := K) hp_odd hp_three u
    (unit_mem_cyclotomicUnitTorsion_of_unitsComplexConj_mul_self_eq_one
      (p := p) (K := K) hp_odd u hu_conj)
    hu_semi

/-- A unit in a CM field cannot satisfy `conj(u) * u = -1`.

After applying any complex embedding, the left hand side is
`conj(z) * z = |z|²`, while the right hand side has real part `-1`. -/
theorem unitsComplexConj_mul_self_ne_neg_one
    [IsCMField K] (u : (𝓞 K)ˣ) :
    unitsComplexConj K u * u ≠ -1 := by
  intro h
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty (K →+* ℂ))
  have hK :
      complexConj K (u : K) * (u : K) = (-1 : K) := by
    have hval := congrArg (fun v : (𝓞 K)ˣ => ((v : 𝓞 K) : K)) h
    simpa [unitsComplexConj] using hval
  have hC := congrArg φ hK
  have hnorm :
      ((Complex.normSq (φ (u : K)) : ℝ) : ℂ) = (-1 : ℂ) := by
    simpa [map_mul, NumberField.IsCMField.complexEmbedding_complexConj,
      Complex.normSq_eq_conj_mul_self] using hC
  have hreal := congrArg Complex.re hnorm
  have hnonneg : 0 ≤ Complex.normSq (φ (u : K)) :=
    Complex.normSq_nonneg _
  norm_num at hreal
  linarith

/-! ### Specific principal unit factor -/

/-- **Specific principal Φ unit-factor data.**

The unit is tied to the actual principal Φ element `Φα`; it is not an
arbitrary unit that can be chosen independently at each denominator. -/
structure PrincipalUnitFactorData
    (α : 𝓞 K)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α) where
  /-- The unit factor relating `Φ((α))` to `α^Θ`. -/
  unit : 𝓞 K
  /-- The factor is a unit. -/
  unit_isUnit : IsUnit unit
  /-- The actual unit-factor equation. -/
  gamma_eq_unit_mul :
    Φα.gamma = unit * stickelbergerPrincipalGen (p := p) (K := K) α

namespace PrincipalUnitFactorData

/-- The unit factor has sign `±1`. This is the arithmetic content supplied by
the classical primary-unit argument. -/
def IsSign
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα) : Prop :=
  U.unit = 1 ∨ U.unit = -1

/-- **U3: existence of the principal unit factor.**

For `α ≠ 0`, the actual principal Φ element and `α^Θ` generate the same
principal ideal, hence differ by a unit. -/
theorem nonempty_of_nonzero
    {α : 𝓞 K} (hα : α ≠ 0)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α) :
    Nonempty (PrincipalUnitFactorData (p := p) (K := K) α Φα) := by
  have hA :
      Ideal.span ({α} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hα
  have h_span_phi :
      Ideal.span ({Φα.gamma} : Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K)
          (Ideal.span ({α} : Set (𝓞 K))) :=
    PhiPrimeElement.PhiIdealElement.span_gamma (p := p) (K := K) Φα hA
  have h_span :
      Ideal.span ({Φα.gamma} : Set (𝓞 K)) =
        Ideal.span
          ({stickelbergerPrincipalGen (p := p) (K := K) α} : Set (𝓞 K)) := by
    rw [h_span_phi, stickelbergerIdeal_span_singleton]
  obtain ⟨u, hu⟩ :=
    exists_unit_eq_of_span_eq
      (K := K) (γ₁ := Φα.gamma)
      (γ₂ := stickelbergerPrincipalGen (p := p) (K := K) α)
      (stickelbergerPrincipalGen_ne_zero hα) h_span
  exact ⟨{
    unit := (u : 𝓞 K)
    unit_isUnit := u.isUnit
    gamma_eq_unit_mul := hu
  }⟩

/-- A chosen principal unit factor from the same-span existence theorem. -/
noncomputable def ofNonzero
    {α : 𝓞 K} (hα : α ≠ 0)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α) :
    PrincipalUnitFactorData (p := p) (K := K) α Φα :=
  Classical.choice (nonempty_of_nonzero (p := p) (K := K) hα Φα)

/-- The concrete unit factor is semi-primary once the concrete principal Φ
element and the Stickelberger principal generator are semi-primary, with
`α^Θ` prime to `ζ - 1`.

This is the formal U4 cancellation step: it uses the actual equation
`Φ((α)) = u · α^Θ` and cancels `α^Θ` modulo `(ζ - 1)^2`; no arbitrary
unit-twisted Φ representative is being substituted. -/
theorem unit_isSemiPrimary_of_gamma_isSemiPrimary
    (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hgamma_semi : FLT37.IsSemiPrimary p (K := K) Φα.gamma)
    (h_stick_not_dvd :
      ¬ FLT37.zetaSubOne p K ∣
        stickelbergerPrincipalGen (p := p) (K := K) α) :
    FLT37.IsSemiPrimary p (K := K) U.unit := by
  have hstick_semi :
      FLT37.IsSemiPrimary p (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) :=
    isSemiPrimary_stickelbergerPrincipalGen
      (p := p) (K := K) hp_two hα_semi
  have hprod :
      FLT37.IsSemiPrimary p (K := K)
        (U.unit * stickelbergerPrincipalGen (p := p) (K := K) α) := by
    simpa [U.gamma_eq_unit_mul] using hgamma_semi
  exact isSemiPrimary_of_mul_right_of_not_zetaSubOne_dvd
    (p := p) (K := K) hp_three hprod hstick_semi h_stick_not_dvd

/-- Unit-valued version of
`PrincipalUnitFactorData.unit_isSemiPrimary_of_gamma_isSemiPrimary`. -/
theorem unitUnit_isSemiPrimary_of_gamma_isSemiPrimary
    (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hgamma_semi : FLT37.IsSemiPrimary p (K := K) Φα.gamma)
    (h_stick_not_dvd :
      ¬ FLT37.zetaSubOne p K ∣
        stickelbergerPrincipalGen (p := p) (K := K) α) :
    FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K) := by
  have h :=
    U.unit_isSemiPrimary_of_gamma_isSemiPrimary
      (p := p) (K := K) hp_two hp_three
      hα_semi hgamma_semi h_stick_not_dvd
  simpa [IsUnit.unit_spec U.unit_isUnit] using h

/-- The concrete unit factor is semi-primary when the concrete principal Φ
element is semi-primary and `α` itself is prime to `ζ - 1`. -/
theorem unitUnit_isSemiPrimary_of_gamma_isSemiPrimary_of_not_zetaSubOne_dvd
    (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hα_not_dvd : ¬ FLT37.zetaSubOne p K ∣ α)
    (hgamma_semi : FLT37.IsSemiPrimary p (K := K) Φα.gamma) :
    FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K) :=
  U.unitUnit_isSemiPrimary_of_gamma_isSemiPrimary
    (p := p) (K := K) hp_two hp_three hα_semi hgamma_semi
    (not_zetaSubOne_dvd_stickelbergerPrincipalGen
      (p := p) (K := K) hp_two hα_not_dvd)

/-- The concrete unit factor is semi-primary from prime-level semi-primarity
of the actual Φ factors.

This is the product-and-cancellation part of U4 in the form used after the
principal Φ product has been constructed from actual descended prime Φ
elements. -/
theorem unitUnit_isSemiPrimary_of_primePhiSemi_of_not_zetaSubOne_dvd
    (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hα_semi : FLT37.IsSemiPrimary p (K := K) α)
    (hα_not_dvd : ¬ FLT37.zetaSubOne p K ∣ α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma) :
    FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K) :=
  U.unitUnit_isSemiPrimary_of_gamma_isSemiPrimary_of_not_zetaSubOne_dvd
    (p := p) (K := K) hp_two hp_three hα_semi hα_not_dvd
    (phiPrincipalGamma_isSemiPrimary_of_prime_semi
      (p := p) (K := K) Φα h_prime_semi)

/-- The conjugation product formula for the concrete Φ element forces the
specific unit factor to be antisymmetric.

This is the algebraic U4 step behind the classical `conj(u) * u = 1`
claim. It does not use ideal-span data alone: it uses the actual element
equation `Φ((α)) = u · α^Θ` together with the concrete conjugation product
identity for that same Φ element. -/
theorem conj_gamma_mul_self_eq_unit_conj_mul_self_mul_conj_stick_mul_self
    [IsCMField K]
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα) :
    ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
      (((unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit : (𝓞 K)ˣ) :
          𝓞 K) *
        (ringOfIntegersComplexConj K
            (stickelbergerPrincipalGen (p := p) (K := K) α) *
          stickelbergerPrincipalGen (p := p) (K := K) α)) := by
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
  calc
    ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
        (((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) *
          ringOfIntegersComplexConj K S) * ((u : 𝓞 K) * S) := by
          rw [hconj_gamma, hgamma]
    _ =
        (((unitsComplexConj K u * u : (𝓞 K)ˣ) : 𝓞 K) *
          (ringOfIntegersComplexConj K S * S)) := by
          simp [Units.val_mul]
          ring

end PrincipalUnitFactorData
end Furtwaengler

end BernoulliRegular

end
