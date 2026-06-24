import BernoulliRegular.FLT37.Eichler.DworkCoordinate.UnscaledCoordDeg32SliceDecomposition
import BernoulliRegular.FLT37.Eichler.ArtinHasse.Deg68OnwardCorrectionDischarge

/-!
# The deg-`≠32,68` slice-vanishing: the `varpi^{32}` Dwork power-basis fold (mod `37²`)

This file builds toward `CaseIICor823Level71Deg68OtherSlicesVanish37`
(`CaseIICor823Level71Deg68OnwardDischarge.lean`): the sum of the degree-`d` slice `varpi^{32}`
coordinates over `d ∈ ((range 2664).erase 32).erase 68` vanishes mod `37²`.  It imports only; it does
**not** modify any existing file.  No `sorry`, no `axiom`.

## The two vanishing mechanisms (the `d mod 36` dichotomy)

Through the Dwork ramification fold `dworkParameter^{36} = -37·tailUnit`
(`dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`), the degree-`d` slice's `varpi^{32}` coordinate is
governed by `d mod 36`:

* **`d mod 36 ≠ 32`**: the slice's image folds onto the `varpi^{d mod 36}` Dwork basis vector, away
  from `varpi^{32}`, so the `varpi^{32}` coordinate vanishes.  The clean part of this — that the
  `varpi^{32}` coordinate of the *Dwork power* `dworkParameter^d` itself vanishes mod `37²` for
  `d mod 36 ≠ 32` — is proven here (`x_pow_coordModSq_eq_zero_of_emod_ne`).

* **`d mod 36 = 32`, `d ≥ 104`** (i.e. `d ∉ {32, 68}` in range): the **whole** degree-`d` slice
  `S_d^{(71)}` is `0` in the level-`71` precision quotient `⧸ (λ)^{72}`, because the formal degree-`d`
  Artin-Hasse log source `formalSum_d` is `≡ 0 (mod 37²)` (its `37`-adic valuation grows with `d` by
  the Artin-Hasse Frobenius structure — `v_37(formalSum_d) = (d - 32)/36 ≥ 2` for `d ≥ 104`), and the
  cross-level factorial-weighted membership forces `S_d^{(71)} ∈ (λ)^{36·v_37(d!) + 72}`, i.e.
  `S_d^{(71)} = 0`.  This is the **opposite** of the `d = 68` slice (`v_37(formalSum_68) = 1`, hence
  `S_68^{(71)} ≠ 0`, carrying the genuine second digit `c₆₈ = 4`).

## Soundness note (recorded)

A `B_d/d`-based heuristic for the `d ≥ 104` slices is **unsound**: the rational identity
`formalSum_d = B_d/d` holds only for `d ≤ p - 3 = 34` (`coeff_logOf_…_eq_bernoulli`).  For `d ≥ p`
the Artin-Hasse Frobenius correction makes `formalSum_d` strictly more `37`-divisible than `B_d/d`
(e.g. `formalSum_68 ≡ 37·21` vs `B_68/68 ≡ 37·22`), and it is precisely this extra divisibility that
forces the `d ≥ 104` slices to vanish.  The correct source is `formalSum_d`, *not* `B_d/d`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 1. The `varpi^{32}` coordinate of `dworkParameter^d` vanishes mod `37²` for `d mod 36 ≠ 32` -/

omit [NumberField.IsCMField K] in
/-- **The degree-`r` Dwork power (`r < 36`, `r ≠ 32`) is off the `varpi^{32}` basis vector** (proven):
`repr(dworkParameter^r) 32 = 0`, since `r < 36 = p - 1` so `dworkParameter^r = dworkParameterPowerBasis
r` is the basis vector of index `r ≠ 32`. -/
theorem repr_dworkParameter_pow_eq_zero_of_lt_of_ne
    (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) (r : ℕ) (hr : r < 36) (hrne : r ≠ 32) :
    (dworkParameterPowerBasis 37 K).repr (dworkParameter 37 K ^ r) k = 0 := by
  have hrlt : r < 37 - 1 := by omega
  have hbasis : dworkParameter 37 K ^ r = dworkParameterPowerBasis 37 K ⟨r, hrlt⟩ := by
    rw [dworkParameterPowerBasis_apply]
  rw [hbasis, Module.Basis.repr_self, Finsupp.single_apply]
  rw [if_neg]
  intro hcontra
  -- `⟨r, _⟩ = k` would force `r = (k : ℕ) = 32`, contradicting `r ≠ 32`.
  apply hrne
  have : r = (k : ℕ) := by rw [← hcontra]
  rw [this, hk]

omit [NumberField.IsCMField K] in
/-- **The Dwork ramification fold at degree `d = 36·q + r`** (proven): in the completed Dwork ring,
`dworkParameter^d = (-37·tailUnit)^q · dworkParameter^r`, from `dworkParameter^{36} = -37·tailUnit`
(`dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`) and `d = 36·q + r`.  The `(-37)^q` factor is the
ramification scalar; for `q ≥ 2` it is `≡ 0 (mod 37²)`. -/
theorem dworkParameter_pow_eq_fold (hp2 : 2 < 37) (q r : ℕ) :
    dworkParameter 37 K ^ (36 * q + r) =
      (-(37 : DworkCompleteIntegerRing 37 K) *
        artinHasseTailUnit (p := 37) (K := K) hp2) ^ q * dworkParameter 37 K ^ r := by
  have h36 : dworkParameter 37 K ^ 36 =
      -(37 : DworkCompleteIntegerRing 37 K) * artinHasseTailUnit (p := 37) (K := K) hp2 := by
    have := dworkParameter_pow_pred_eq_neg_p_mul_tailUnit (p := 37) (K := K) hp2
    simpa using this
  rw [pow_add, pow_mul, h36]

/-- **`(-37)^q` lies in `(rationalPadicPrimeIdeal)^2` for `q ≥ 2`** (proven): the ramification scalar
is `37²`-divisible once `q ≥ 2`, so it vanishes mod `37²`.  Used for the `d ≥ 104` (`q ≥ 2`) Dwork
powers.  `(rationalPadicPrimeIdeal)^2 = span {37²}`, and `(-37)^q = 37²·((-1)^q·37^{q-2})`. -/
theorem neg_thirtyseven_pow_mem_primeIdeal_sq (q : ℕ) (hq : 2 ≤ q) :
    (-(37 : RationalPadicIntegerRing 37)) ^ q ∈ (rationalPadicPrimeIdeal 37) ^ 2 := by
  have h37 : (37 : RationalPadicIntegerRing 37) ∈ rationalPadicPrimeIdeal 37 :=
    Ideal.mem_span_singleton_self _
  -- `37^q ∈ (ideal)^q ⊆ (ideal)^2`, then `(-37)^q = (-1)^q · 37^q` keeps membership.
  have hpowq : (37 : RationalPadicIntegerRing 37) ^ q ∈ (rationalPadicPrimeIdeal 37) ^ q :=
    Ideal.pow_mem_pow h37 q
  have hle : (37 : RationalPadicIntegerRing 37) ^ q ∈ (rationalPadicPrimeIdeal 37) ^ 2 :=
    Ideal.pow_le_pow_right hq hpowq
  have heq : (-(37 : RationalPadicIntegerRing 37)) ^ q =
      (-1 : RationalPadicIntegerRing 37) ^ q * (37 : RationalPadicIntegerRing 37) ^ q := by
    rw [← neg_one_mul, mul_pow]
  rw [heq]
  exact Ideal.mul_mem_left _ _ hle

omit [NumberField.IsCMField K] in
/-- **The `varpi^{32}` coordinate of `x^d` vanishes mod `37²` for `d < 36`, `d ≠ 32`** (proven): for
`x = dworkParameterApprox 72` and the basis index `k` with `(k : ℕ) = 32`,
`coordModSq(mk(x^d)) = 0`.  Via `mk(x^d) = evalₐ(dworkParameter^d)`, the coordinate readout
`valuedLambdaQuotientDworkCoeffModSq_evalₐ`, and `repr(dworkParameter^d) 32 = 0` (the basis index
`d < 36`, `d ≠ 32` — `repr_dworkParameter_pow_eq_zero_of_lt_of_ne`). -/
theorem x_pow_coordModSq_eq_zero_of_lt_of_ne
    (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) (d : ℕ) (hd : d < 36) (hdne : d ≠ 32) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ (2 * (37 - 1)))
          (dworkParameterApprox 37 K (2 * (37 - 1)) ^ d)) = 0 := by
  have hmk : Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ (2 * (37 - 1)))
        (dworkParameterApprox 37 K (2 * (37 - 1)) ^ d) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) (2 * (37 - 1)) (dworkParameter 37 K ^ d) := by
    rw [map_pow, map_pow, dworkParameter_evalₐ]
  rw [hmk, valuedLambdaQuotientDworkCoeffModSq_evalₐ,
    repr_dworkParameter_pow_eq_zero_of_lt_of_ne (K := K) k hk d hd hdne, map_zero]

omit [NumberField.IsCMField K] in
/-- **The formal `rIntegralRat` scalar factors out of the mod-`37²` coordinate of `x^d`** (proven,
general degree): for any `37`-integral rational `q`,
`coordModSq(quotMap(x^d)·RIntToQuot(q)) = (q.num·q.den⁻¹)·coordModSq(quotMap(x^d))`.  The general-`d`
analog of `rIntegralRat_scalar_factors_through_coordModSq_x68` (identical proof, with the exponent a
parameter): denominator clearing by the `37`-unit `q.den` and `den_mul_rIntegralRatToValuedInteger`. -/
theorem rIntegralRat_scalar_factors_through_coordModSq_xpow
    (d : ℕ) (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) (k : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
        (samePrimeQuotientMap (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (2 * (37 - 1)) ^ d) *
          samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71 q) =
      ((q : ℚ).num : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹ *
        valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
          (samePrimeQuotientMap (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (2 * (37 - 1)) ^ d)) := by
  set xp := dworkParameterApprox 37 K (2 * (37 - 1)) ^ d with hxp
  set C := valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
    (samePrimeQuotientMap (p := 37) (K := K) 71 xp) with hC
  set L := valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) k
      (samePrimeQuotientMap (p := 37) (K := K) 71 xp *
        samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71 q) with hL
  have hunit : IsUnit (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) := by
    have hcop : ((q : ℚ).den : ℕ).Coprime 37 := q.property
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_right 2)
  have hden : (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) * L = ((q : ℚ).num : ZMod (37 ^ 2)) * C := by
    rw [hL, ← valuedLambdaQuotientDworkCoeffModSq_natCast_mul]
    have hRItoQ : samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71 q =
        samePrimeQuotientMap (p := 37) (K := K) 71 (rIntegralRatToValuedInteger 37 K q) := rfl
    rw [hRItoQ, ← map_mul,
      ← map_natCast (samePrimeQuotientMap (p := 37) (K := K) 71) ((q : ℚ).den), ← map_mul]
    have hclear :
        (((q : ℚ).den : ValuedIntegerRing 37 K)) *
            (xp * rIntegralRatToValuedInteger 37 K q) =
          ((q : ℚ).num : ValuedIntegerRing 37 K) * xp := by
      calc
        (((q : ℚ).den : ValuedIntegerRing 37 K)) *
            (xp * rIntegralRatToValuedInteger 37 K q)
            = ((((q : ℚ).den : ValuedIntegerRing 37 K)) *
                rIntegralRatToValuedInteger 37 K q) * xp := by ring
        _ = ((q : ℚ).num : ValuedIntegerRing 37 K) * xp := by
            rw [den_mul_rIntegralRatToValuedInteger (p := 37) (K := K) q]
    rw [hclear, map_mul, map_intCast, valuedLambdaQuotientDworkCoeffModSq_intCast_mul, ← hC]
  apply hunit.mul_left_cancel
  rw [hden,
    show (((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) *
        (((q : ℚ).num : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹ * C) =
      ((q : ℚ).num : ZMod (37 ^ 2)) *
        ((((q : ℚ).den : ℕ) : ZMod (37 ^ 2)) * (((q : ℚ).den : ℕ) : ZMod (37 ^ 2))⁻¹) * C by
      ring]
  rw [ZMod.mul_inv_of_unit _ hunit, mul_one]

/-! ## 2. The whole-slice vanishing engine: `S_d^{(71)} = 0` from formal-source `37`-divisibility

For `d ≥ 72` (Case B and the bulk of Case A), the entire degree-`d` slice `S_d^{(71)}` vanishes in the
level-`71` precision quotient `⧸ (λ)^{72}` once the formal Artin-Hasse log source `formalSum_d` is
sufficiently `37`-divisible.  We prove this by mirroring the proven
`samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_zero_of_coeff_log_eq_zero`
(`KummerLogNormalization/Part3.lean`), replacing its `formalSum_d = 0` hypothesis with the weaker
`rIntegralRatToValuedInteger formalSum_d ∈ (λ)^{36·w}` plus the degree bound `d + 36·w ≥ 36·v + 72`
(`v = v₃₇(d!)`, `w` the formal-source `37`-valuation). -/

omit [NumberField.IsCMField K] in
/-- **The factorial-weighted numerator sum vanishes at level `M = 36v + 71` from formal `37`-divisibility**
(proven): if `rIntegralRatToValuedInteger formalSum_d ∈ (λ)^{36·w}` and `d + 36·w ≥ 36·v + 72`
(`v = v₃₇(d!) = d!.factorization 37`), then at level `M = d!.factorization 37 · 36 + 71` the
factorial-weighted numerator sum lies in `(λ)^{M+1}`.

The `M`-level identity `quotient_mk_…_factorial_weighted_sum_eq_formal` gives
`mk_{M+1}(Y_d^{(M)}) = mk_{M+1}(x^d) · RIntToQuot(formalSum_d)`; the right factors are `x^d ∈ (λ)^d`
and `rIntToVal(formalSum_d) ∈ (λ)^{36w}`, so the product is in `(λ)^{d + 36w} ⊆ (λ)^{M+1}` (the degree
bound), forcing the quotient image to `0`, i.e. membership in `(λ)^{M+1}`. -/
theorem factorial_weighted_numerator_sum_mem_highLevel_of_formalSum_mem
    (d w : ℕ) {x : ValuedIntegerRing 37 K} (hx : x ∈ lambdaIdeal 37 K)
    (hformal :
      rIntegralRatToValuedInteger 37 K
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) ∈
        (lambdaIdeal 37 K) ^ (36 * w))
    (hdeg : 36 * (Nat.factorial d).factorization 37 + 72 ≤ d + 36 * w) :
    (∑ n ∈ Finset.Icc 1 d,
      ((Nat.factorial d / n : ℕ) : ValuedIntegerRing 37 K) *
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
          (p := 37) (K := K) ((Nat.factorial d).factorization 37 * 36 + 71) n d x) ∈
      (lambdaIdeal 37 K) ^
        (((Nat.factorial d).factorization 37 * 36 + 71) + 1) := by
  classical
  set M : ℕ := (Nat.factorial d).factorization 37 * 36 + 71 with hM
  -- The `M`-level factorial-weighted formal identity.
  have hq :=
    quotient_mk_samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
      (p := 37) (K := K) M d hx
  -- `x^d · rIntToVal(formalSum_d) ∈ (λ)^{d + 36w}`.
  have hprod_mem :
      x ^ d *
          rIntegralRatToValuedInteger 37 K
            (∑ n ∈ Finset.Icc 1 d,
              rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) ∈
        (lambdaIdeal 37 K) ^ (d + 36 * w) := by
    have hxd : x ^ d ∈ (lambdaIdeal 37 K) ^ d := Ideal.pow_mem_pow hx d
    rw [pow_add]
    exact Ideal.mul_mem_mul hxd hformal
  -- hence in `(λ)^{M+1}` by the degree bound.
  have hprod_high :
      x ^ d *
          rIntegralRatToValuedInteger 37 K
            (∑ n ∈ Finset.Icc 1 d,
              rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) ∈
        (lambdaIdeal 37 K) ^ (M + 1) :=
    Ideal.pow_le_pow_right (by rw [hM]; omega) hprod_mem
  -- the quotient image of the factorial-weighted sum equals the quotient image of that product, = 0.
  have hRHS :
      samePrimeQuotientMap (p := 37) (K := K) M (x ^ d) *
          samePrimeRIntegralRatToQuotient (p := 37) (K := K) M
            (∑ n ∈ Finset.Icc 1 d,
              rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) =
        Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ (M + 1))
          (x ^ d *
            rIntegralRatToValuedInteger 37 K
              (∑ n ∈ Finset.Icc 1 d,
                rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n)) := by
    rw [map_mul]
    rfl
  have hRHS_zero :
      samePrimeQuotientMap (p := 37) (K := K) M (x ^ d) *
          samePrimeRIntegralRatToQuotient (p := 37) (K := K) M
            (∑ n ∈ Finset.Icc 1 d,
              rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) = 0 := by
    rw [hRHS, Ideal.Quotient.eq_zero_iff_mem]
    exact hprod_high
  rw [hRHS_zero] at hq
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact hq

omit [NumberField.IsCMField K] in
/-- **The level-`71` factorial-weighted numerator sum lies in `(λ)^{36v + 72}` from formal `37`-divisibility**
(proven): combining the high-level vanishing (`…_mem_highLevel_of_formalSum_mem`, at level
`M = 36v + 71`) with the proven cross-level numerator-difference bound
(`…_factorial_weighted_sub_precision_mem_lambdaIdeal_pow`, `Y_d^{(71)} - Y_d^{(M)} ∈ (λ)^{36v + 72}`),
the level-`71` sum `Y_d^{(71)} = (Y_d^{(71)} - Y_d^{(M)}) + Y_d^{(M)}` lies in `(λ)^{36v + 72}`. -/
theorem factorial_weighted_numerator_sum_mem_of_formalSum_mem
    (d w : ℕ) {x : ValuedIntegerRing 37 K} (hx : x ∈ lambdaIdeal 37 K)
    (hformal :
      rIntegralRatToValuedInteger 37 K
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) ∈
        (lambdaIdeal 37 K) ^ (36 * w))
    (hdeg : 36 * (Nat.factorial d).factorization 37 + 72 ≤ d + 36 * w) :
    (∑ n ∈ Finset.Icc 1 d,
      ((Nat.factorial d / n : ℕ) : ValuedIntegerRing 37 K) *
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
          (p := 37) (K := K) 71 n d x) ∈
      (lambdaIdeal 37 K) ^ ((Nat.factorial d).factorization 37 * (37 - 1) + (71 + 1)) := by
  classical
  set M : ℕ := (Nat.factorial d).factorization 37 * 36 + 71 with hM
  set I : Ideal (ValuedIntegerRing 37 K) :=
    (lambdaIdeal 37 K) ^ ((Nat.factorial d).factorization 37 * (37 - 1) + (71 + 1)) with hI
  have hNM : (71 : ℕ) ≤ M := by rw [hM]; omega
  -- the cross-level difference is in `I`.
  have hdiff :
      (∑ n ∈ Finset.Icc 1 d,
        ((Nat.factorial d / n : ℕ) : ValuedIntegerRing 37 K) *
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := 37) (K := K) 71 n d x -
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := 37) (K := K) M n d x)) ∈ I := by
    refine Ideal.sum_mem _ ?_
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
    simpa [I] using
      samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
        (p := 37) (K := K) 71 M n d hx hNM hn1 hnd
  -- the high-level sum is in `(λ)^{M+1} = (λ)^{36v + 72} = I`.
  have hsumM : (∑ n ∈ Finset.Icc 1 d,
        ((Nat.factorial d / n : ℕ) : ValuedIntegerRing 37 K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := 37) (K := K) M n d x) ∈ I := by
    have h := factorial_weighted_numerator_sum_mem_highLevel_of_formalSum_mem
      (K := K) d w hx hformal hdeg
    -- `M + 1 = 36v + 72`; rewrite the membership ideal exponent of `h` to the `I` exponent.
    have hexp : (((Nat.factorial d).factorization 37 * 36 + 71) + 1) =
        (Nat.factorial d).factorization 37 * (37 - 1) + (71 + 1) := by
      norm_num
    rw [hI]
    rw [show ((Nat.factorial d).factorization 37 * 36 + 71) = M from hM] at h
    rw [← hexp]
    exact h
  -- assemble: `Y^{(71)} = diff + Y^{(M)}`.
  have hsplit :
      (∑ n ∈ Finset.Icc 1 d,
        ((Nat.factorial d / n : ℕ) : ValuedIntegerRing 37 K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := 37) (K := K) 71 n d x) =
      (∑ n ∈ Finset.Icc 1 d,
        ((Nat.factorial d / n : ℕ) : ValuedIntegerRing 37 K) *
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := 37) (K := K) 71 n d x -
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := 37) (K := K) M n d x)) +
      (∑ n ∈ Finset.Icc 1 d,
        ((Nat.factorial d / n : ℕ) : ValuedIntegerRing 37 K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := 37) (K := K) M n d x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  rw [hsplit]
  exact I.add_mem hdiff hsumM

omit [NumberField.IsCMField K] in
/-- **The whole degree-`d` slice vanishes at level `71` from formal `37`-divisibility** (proven): if
`rIntegralRatToValuedInteger formalSum_d ∈ (λ)^{36·w}` and `d + 36·w ≥ 36·v + 72`, then
`S_d^{(71)} = samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum 71 d x = 0`.

Composes `factorial_weighted_numerator_sum_mem_of_formalSum_mem` (the level-`71` factorial-weighted
sum lies in `(λ)^{36v + 72}`) with the proven
`samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem`.
This is the **whole-slice** vanishing — the bulk mechanism for `d ≥ 72` (Case B and large Case A). -/
theorem slice_eq_zero_of_formalSum_mem
    (d w : ℕ) {x : ValuedIntegerRing 37 K} (hx : x ∈ lambdaIdeal 37 K)
    (hformal :
      rIntegralRatToValuedInteger 37 K
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) ∈
        (lambdaIdeal 37 K) ^ (36 * w))
    (hdeg : 36 * (Nat.factorial d).factorization 37 + 72 ≤ d + 36 * w) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
      (p := 37) (K := K) 71 d x hx = 0 :=
  samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem
    (p := 37) (K := K) 71 d hx
    (factorial_weighted_numerator_sum_mem_of_formalSum_mem (K := K) d w hx hformal hdeg)

omit [NumberField.IsCMField K] in
/-- **`unscaled32SliceCoord d = 0` from formal `37`-divisibility** (proven): the whole degree-`d` slice
vanishes (`slice_eq_zero_of_formalSum_mem`), so its `varpi^{32}` coordinate `unscaled32SliceCoord d`
vanishes.  This is the bulk reduction: every `d ≥ 72` whose formal source `formalSum_d` is `37^w`-divisible
with `d + 36w ≥ 36·v₃₇(d!) + 72` contributes `0` to the correction sum. -/
theorem unscaled32SliceCoord_eq_zero_of_formalSum_mem
    (d w : ℕ)
    (hformal :
      rIntegralRatToValuedInteger 37 K
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) ∈
        (lambdaIdeal 37 K) ^ (36 * w))
    (hdeg : 36 * (Nat.factorial d).factorization 37 + 72 ≤ d + 36 * w) :
    unscaled32SliceCoord (K := K) d = 0 := by
  rw [unscaled32SliceCoord]
  rw [slice_eq_zero_of_formalSum_mem (K := K) d w
    (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1)) hformal hdeg]
  exact valuedLambdaQuotientDworkCoeffModSq_zero (p := 37) (K := K) _

/-! ## 3. Reducing the formal-source membership to subring `37`-divisibility -/

omit [NumberField.IsCMField K] in
/-- **`37^w`-divisibility of `formalSum_d` in the integral subring gives the formal-source membership**
(proven): if `formalSum_d = 37^w · g` for some `g` in the `37`-integral rational subring, then
`rIntegralRatToValuedInteger formalSum_d = 37^w · rIntegralRatToValuedInteger g ∈ (λ)^{36·w}`, via the
ring-hom property and `(37 : ValuedInteger)^w ∈ (λ)^{w·(37-1)} = (λ)^{36·w}`
(`natCast_prime_pow_mem_lambdaIdeal_pow_mul_pred`). -/
theorem rIntegralRatToValuedInteger_formalSum_mem_of_dvd
    (d w : ℕ)
    (g : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37)
    (hg : (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) =
          (37 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) ^ w * g) :
    rIntegralRatToValuedInteger 37 K
        (∑ n ∈ Finset.Icc 1 d,
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) ∈
      (lambdaIdeal 37 K) ^ (36 * w) := by
  rw [hg, map_mul, map_pow]
  -- `rIntToVal (37 : subring) = (37 : ValuedInteger)` (natCast through the ring hom).
  have h37 : rIntegralRatToValuedInteger 37 K
      (37 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) =
      (37 : ValuedIntegerRing 37 K) := by
    rw [show (37 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) =
        ((37 : ℕ) : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) by norm_num]
    rw [map_natCast]
    norm_num
  rw [h37]
  have hpow : (37 : ValuedIntegerRing 37 K) ^ w ∈ (lambdaIdeal 37 K) ^ (36 * w) := by
    have := natCast_prime_pow_mem_lambdaIdeal_pow_mul_pred (p := 37) (K := K) w
    rwa [show w * (37 - 1) = 36 * w by ring] at this
  exact Ideal.mul_mem_right _ _ hpow

/-! ## 3b. The Case-A small-`d` coordinate vanishing (`d < 37`, `d ≠ 32`) via the factorial route -/

omit [NumberField.IsCMField K] in
/-- **The factorial-`d` second-order extraction at general degree** (proven): for `x = dworkParameterApprox
72`, `(d! : ZMod 37²)·coordModSq(deg-d slice) = coordModSq(quotMap(x^d)·formalSum_d)`.  The general-`d`
analog of `factorial37_deg68_coordModSq_extraction`: the mod-`37²` coordinate image of the all-degrees
factorial identity `natCast_factorial_mul_…_eq_formal` via `valuedLambdaQuotientDworkCoeffModSq_natCast_mul`. -/
theorem factorial_deg_coordModSq_extraction
    (i : Fin (37 - 1)) (d : ℕ) {x : ValuedIntegerRing 37 K} (hx : x ∈ lambdaIdeal 37 K) :
    ((Nat.factorial d : ℕ) : ZMod (37 ^ 2)) *
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := 37) (K := K) 71 d x hx) =
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
      (samePrimeQuotientMap (p := 37) (K := K) 71 (x ^ d) *
        samePrimeRIntegralRatToQuotient (p := 37) (K := K) 71
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n)) := by
  have hid :=
    natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal
      (p := 37) (K := K) 71 d hx
  have hcoord := congrArg (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i) hid
  rwa [valuedLambdaQuotientDworkCoeffModSq_natCast_mul] at hcoord

omit [NumberField.IsCMField K] in
/-- **`(d! : ZMod 37²)` is a unit for `d < 37`** (proven): `37 ∤ d!` since `d < 37`, so `d!` is coprime
to `37²`. -/
theorem factorial_isUnit_modSq_of_lt (d : ℕ) (hd : d < 37) :
    IsUnit ((Nat.factorial d : ℕ) : ZMod (37 ^ 2)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hp : Nat.Prime 37 := by norm_num
  have hndvd : ¬ (37 ∣ Nat.factorial d) := by
    rw [hp.dvd_factorial]; omega
  have hcop : (Nat.factorial d).Coprime 37 :=
    (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hndvd))
  exact hcop.pow_right 2

omit [NumberField.IsCMField K] in
/-- **The Case-A small-`d` coordinate vanishes** (proven): for `d < 36`, `d ≠ 32`,
`unscaled32SliceCoord d = 0`.  The factorial route: `(d!)·coordModSq(S_d) = (formalSum residue)·coordModSq(x^d)`
(`factorial_deg_coordModSq_extraction` + `rIntegralRat_scalar_factors_through_coordModSq_xpow`), with
`coordModSq(x^d) = 0` (`x_pow_coordModSq_eq_zero_of_lt_of_ne`, the basis index `d ≠ 32`), so
`(d!)·coordModSq(S_d) = 0`; dividing by the `37`-unit `d!` (`factorial_isUnit_modSq_of_lt`) gives
`coordModSq(S_d) = 0`.  This discharges the `d < 36` members of `otherSlicesCaseASet`. -/
theorem unscaled32SliceCoord_eq_zero_of_lt_of_ne
    (d : ℕ) (hd : d < 36) (hdne : d ≠ 32) :
    unscaled32SliceCoord (K := K) d = 0 := by
  set i : Fin (37 - 1) :=
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1 with hi
  have hival : (i : ℕ) = 32 := rfl
  have hx : dworkParameterApprox 37 K (71 + 1) ∈ lambdaIdeal 37 K :=
    dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1)
  -- `(d!)·coordModSq(S_d) = coordModSq(x^d·formalSum_d) = (residue)·coordModSq(x^d) = 0`.
  have hext := factorial_deg_coordModSq_extraction (K := K) i d hx
  have hscalar := rIntegralRat_scalar_factors_through_coordModSq_xpow (K := K) d
    (∑ n ∈ Finset.Icc 1 d,
      rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) i
  -- `coordModSq(x^d) = 0` (the basis index `d < 36`, `d ≠ 32`); the precisions `71+1` and `2*(37-1)`
  -- agree definitionally (`72 = 2·36`).
  have hxd0 : valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := K) i
      (samePrimeQuotientMap (p := 37) (K := K) 71
        (dworkParameterApprox 37 K (71 + 1) ^ d)) = 0 := by
    have h := x_pow_coordModSq_eq_zero_of_lt_of_ne (K := K) i hival d hd hdne
    -- `samePrimeQuotientMap 71 = mk (lambda)^{72}` and `dworkParameterApprox (71+1) =
    -- dworkParameterApprox (2*(37-1))` (both `72`).
    exact h
  -- assemble.
  have hzero : ((Nat.factorial d : ℕ) : ZMod (37 ^ 2)) *
      unscaled32SliceCoord (K := K) d = 0 := by
    rw [unscaled32SliceCoord, ← hi]
    rw [hext, hscalar, hxd0, mul_zero]
  -- divide by the unit `d!`.
  have hunit := factorial_isUnit_modSq_of_lt (d := d) (by omega)
  apply hunit.mul_left_cancel
  rw [mul_zero]
  exact hzero

omit [NumberField.IsCMField K] in
/-- **The combined whole-slice vanishing from subring `37`-divisibility** (proven): packaging
`rIntegralRatToValuedInteger_formalSum_mem_of_dvd` into
`unscaled32SliceCoord_eq_zero_of_formalSum_mem`: if `formalSum_d = 37^w · g` (subring divisibility) and
`d + 36·w ≥ 36·v₃₇(d!) + 72`, then `unscaled32SliceCoord d = 0`. -/
theorem unscaled32SliceCoord_eq_zero_of_dvd
    (d w : ℕ)
    (g : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37)
    (hg : (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) =
          (37 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) ^ w * g)
    (hdeg : 36 * (Nat.factorial d).factorization 37 + 72 ≤ d + 36 * w) :
    unscaled32SliceCoord (K := K) d = 0 :=
  unscaled32SliceCoord_eq_zero_of_formalSum_mem (K := K) d w
    (rIntegralRatToValuedInteger_formalSum_mem_of_dvd (K := K) d w g hg) hdeg

omit [NumberField.IsCMField K] in
/-- **Case B reduction: `unscaled32SliceCoord d = 0` for `d ≥ 72` from `37`-integrality of the
Artin-Hasse log coefficient** (proven): if `formalSum_d = 37^{v₃₇(d!)} · g` (i.e. the normalized
Artin-Hasse log coefficient `formalSum_d / d!` is `37`-integral) and `d ≥ 72`, then
`unscaled32SliceCoord d = 0`.

Taking `w = v₃₇(d!) = (Nat.factorial d).factorization 37` in `unscaled32SliceCoord_eq_zero_of_dvd`,
the degree bound `36·v + 72 ≤ d + 36·w = d + 36·v` reduces to `72 ≤ d`.  This is the **Case B**
mechanism: the `d ≡ 32 (mod 36)`, `d ≥ 104` slices whose formal source is `37`-integral after the
`d!`-division vanish entirely. -/
theorem unscaled32SliceCoord_eq_zero_of_formalIntegral
    (d : ℕ) (hd : 72 ≤ d)
    (g : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37)
    (hg : (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) =
          (37 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) ^
              ((Nat.factorial d).factorization 37) * g) :
    unscaled32SliceCoord (K := K) d = 0 :=
  unscaled32SliceCoord_eq_zero_of_dvd (K := K) d ((Nat.factorial d).factorization 37) g hg
    (by omega)

omit [NumberField.IsCMField K] in
/-- **The degree-`0` slice vanishes** (proven): `samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
71 0 x` is the empty sum (`Finset.Icc 1 0 = ∅`), hence `0`, so `unscaled32SliceCoord 0 = 0`. -/
theorem unscaled32SliceCoord_zero_eq_zero :
    unscaled32SliceCoord (K := K) 0 = 0 := by
  rw [unscaled32SliceCoord]
  rw [show samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
      (p := 37) (K := K) 71 0 (dworkParameterApprox 37 K (71 + 1))
        (dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) (71 + 1)) = 0 by
    rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum,
      show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl]
    rw [Finset.attach_empty, Finset.sum_empty]]
  exact valuedLambdaQuotientDworkCoeffModSq_zero (p := 37) (K := K) _

/-! ## 4. The deg-`≠32,68` slice-vanishing residuals and the assembly

The whole-slice engine (§2–§3) reduces the deg-`≠32,68` slice vanishing to two precisely-characterized
pieces, which we name as residuals (`def … : Prop`, **not** axioms):

* **`OtherSlicesCaseAVanish37`** (the finite Case-A grading): for the explicit finite set of `d ≤ 74`,
  `d ∉ {32, 68}`, `d ≢ 32 (mod 36)` whose whole slice is *not* forced to vanish, the `varpi^{32}`
  coordinate `unscaled32SliceCoord d` vanishes (the slice has no `varpi^{32}` graded component — a
  mod-`37²` Dwork-grading fact).

* **`OtherSlicesDworkDivisibility37`** (the Case-B Dwork congruence): for every `d ∈ range 2664`,
  `d ∉ {32, 68}` *outside* the finite Case-A set, the formal Artin-Hasse log source `formalSum_d` is
  `37`-divisible enough — `formalSum_d = 37^w · g` with `d + 36·w ≥ 36·v₃₇(d!) + 72` — the genuine
  Dwork/Frobenius valuation content (Washington Proposition 8.12 at general degree).  (The degrees with
  `formalSum_d = 0`, including `d = 0`, are covered trivially by `g = 0`.) -/

/-- **The finite Case-A set** `{1,2,4,…,30,34,37,38,…,70,74}` (`d ≤ 74`, `d ∉ {32, 68}`,
`d ≢ 32 (mod 36)`) whose whole slice `S_d^{(71)}` does *not* vanish (the formal source is too
`37`-singular: `d + 36·v₃₇(formalSum_d/d!) < 72`), so the deg-`≠32,68` vanishing on these `d` is the
`varpi^{32}`-coordinate vanishing, not the whole-slice vanishing.  Enumerated from the Artin-Hasse log
coefficient valuations. -/
def otherSlicesCaseASet : Finset ℕ :=
  {1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 34, 37, 38, 40, 42, 44, 46, 48, 50, 52,
    54, 56, 58, 60, 62, 64, 66, 70, 74}

/-- **The mid Case-A set** `{37, 38, 40, …, 70, 74}` — the members of `otherSlicesCaseASet` with
`37 ≤ d` (so `36 ≤ d`, beyond the factorial-unit range).  The complement (`d < 36` members) is
discharged unconditionally by the factorial route (`unscaled32SliceCoord_eq_zero_of_lt_of_ne`). -/
def otherSlicesCaseAMidSet : Finset ℕ :=
  {37, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 70, 74}

open BernoulliRegular (CPlusGenerator) in
/-- **The mid Case-A coordinate-vanishing residual** (a `def … : Prop`, **not** an axiom): for every
`d ∈ otherSlicesCaseAMidSet` (the `37 ≤ d ≤ 74`, `d ≢ 32 (mod 36)` slices) the `varpi^{32}` coordinate
`unscaled32SliceCoord d` vanishes mod `37²`.  These slices have nonzero whole slice but zero `varpi^{32}`
graded component — a finite mod-`37²` Dwork power-basis grading fact for `d ≥ 36` (where the factorial
route is unavailable since `37 ∣ d!`).  The `d < 36` Case-A members are proven unconditionally. -/
def OtherSlicesCaseAMidVanish37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ d ∈ otherSlicesCaseAMidSet, unscaled32SliceCoord (K := CyclotomicField 37 ℚ) d = 0

open BernoulliRegular (CPlusGenerator) in
/-- **The full finite Case-A coordinate vanishing, from the mid residual** (proven): every
`d ∈ otherSlicesCaseASet` has `unscaled32SliceCoord d = 0`.  The `d < 36` members
(`{1,2,4,…,30,34}`) are discharged by the factorial route `unscaled32SliceCoord_eq_zero_of_lt_of_ne`
(proven); the `37 ≤ d ≤ 74` members are exactly `otherSlicesCaseAMidSet`, supplied by the residual. -/
theorem otherSlicesCaseAVanish_of_mid
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hMid : OtherSlicesCaseAMidVanish37) :
    ∀ d ∈ otherSlicesCaseASet, unscaled32SliceCoord (K := CyclotomicField 37 ℚ) d = 0 := by
  intro d hd
  by_cases hlt : d < 36
  · -- `d < 36`, `d ≠ 32` (32 ∉ otherSlicesCaseASet): factorial route.
    have hne : d ≠ 32 := by
      rintro rfl
      simp [otherSlicesCaseASet] at hd
    exact unscaled32SliceCoord_eq_zero_of_lt_of_ne (K := CyclotomicField 37 ℚ) d hlt hne
  · -- `d ≥ 36`: `d ∈ otherSlicesCaseAMidSet`, supplied by the residual.
    apply hMid
    -- membership transfer: the `≥ 36` members of `otherSlicesCaseASet` are `otherSlicesCaseAMidSet`.
    fin_cases hd <;> first | (exfalso; omega) | (simp [otherSlicesCaseAMidSet])

open BernoulliRegular (CPlusGenerator) in
/-- **The Case-B Dwork-divisibility residual** (a `def … : Prop`, **not** an axiom): for every
`d ∈ range 2664` with `d ≥ 72`, `d ∉ {32, 68}`, and `d ∉ otherSlicesCaseASet`, the formal Artin-Hasse
log source `formalSum_d = ∑_n …FactorialWeightedLogCoeff` is `37`-divisible enough:
`formalSum_d = 37^w · g` for some `w` and `g` in the `37`-integral rational subring, with
`36·v₃₇(d!) + 72 ≤ d + 36·w`.

This is the genuine Dwork/Frobenius valuation of the normalized Artin-Hasse logarithm coefficients at
general degree (Washington Proposition 8.12) — the same deep `p`-adic-`L` content the rest of R4
reduces to, here localized to the degree-`d` slice sources.  The whole-slice engine
(`unscaled32SliceCoord_eq_zero_of_dvd`) turns it into `unscaled32SliceCoord d = 0`. -/
def OtherSlicesDworkDivisibility37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := 37) 71),
    d ≠ 32 → d ≠ 68 → d ∉ otherSlicesCaseASet →
    ∃ (w : ℕ) (g : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37),
      (∑ n ∈ Finset.Icc 1 d,
        rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 d n) =
          (37 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) ^ w * g ∧
      36 * (Nat.factorial d).factorization 37 + 72 ≤ d + 36 * w

open BernoulliRegular (CPlusGenerator) in
/-- **Every deg-`≠32,68` slice coordinate vanishes, from the two residuals** (proven): for every
`d ∈ ((range 2664).erase 32).erase 68`, `unscaled32SliceCoord d = 0`.  Cases on `d ∈ otherSlicesCaseASet`
(use `OtherSlicesCaseAVanish37`, the finite Case-A grading) versus `d ∉ otherSlicesCaseASet` (use
`OtherSlicesDworkDivisibility37` + the whole-slice engine `unscaled32SliceCoord_eq_zero_of_dvd`). -/
theorem unscaled32SliceCoord_eq_zero_of_mem_erase
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCaseA : OtherSlicesCaseAMidVanish37)
    (hDwork : OtherSlicesDworkDivisibility37)
    (d : ℕ)
    (hd : d ∈ ((Finset.range (samePrimeFiniteLogCutoff (p := 37) 71)).erase 32).erase 68) :
    unscaled32SliceCoord (K := CyclotomicField 37 ℚ) d = 0 := by
  rw [Finset.mem_erase, Finset.mem_erase] at hd
  obtain ⟨hd68, hd32, hdrange⟩ := hd
  by_cases hS : d ∈ otherSlicesCaseASet
  · exact otherSlicesCaseAVanish_of_mid hCaseA d hS
  · obtain ⟨w, g, hg, hbound⟩ := hDwork d hdrange hd32 hd68 hS
    exact unscaled32SliceCoord_eq_zero_of_dvd (K := CyclotomicField 37 ℚ) d w g hg hbound

open BernoulliRegular (CPlusGenerator) in
/-- **The deg-`≠32,68` slice-vanishing residual, from the two pieces** (proven, axiom-clean given the
residuals): `OtherSlicesCaseAVanish37 → OtherSlicesDworkDivisibility37 →
CaseIICor823Level71Deg68OtherSlicesVanish37`.

`Finset.sum_eq_zero` over `((range 2664).erase 32).erase 68`, each term `unscaled32SliceCoord d = 0` by
`unscaled32SliceCoord_eq_zero_of_mem_erase`.  This discharges the deg-`≠32,68` half of
`CaseIICor823Level71Deg68OnwardCorrection37` to the two named residuals: the finite Case-A coordinate
grading and the Case-B Dwork-divisibility (Washington Prop 8.12). -/
theorem caseIICor823Level71Deg68OtherSlicesVanish37_of_residuals
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCaseA : OtherSlicesCaseAMidVanish37)
    (hDwork : OtherSlicesDworkDivisibility37) :
    CaseIICor823Level71Deg68OtherSlicesVanish37 := by
  rw [CaseIICor823Level71Deg68OtherSlicesVanish37]
  refine Finset.sum_eq_zero ?_
  intro d hd
  exact unscaled32SliceCoord_eq_zero_of_mem_erase hCaseA hDwork d hd

/-! ## 5. The FLT37 endpoint, with the deg-`≠32,68` slice vanishing reduced to the two residuals -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with the deg-`≠32,68` slice vanishing reduced to the Case-A
coordinate grading + the Case-B Dwork divisibility** (proven, axiom-clean given the residuals + the
Kellner Prop).

`CaseIICor823Level71Deg68OtherSlicesVanish37` of
`fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridgeAndFiniteLog` is replaced by its two genuine
pieces via `caseIICor823Level71Deg68OtherSlicesVanish37_of_residuals`:

* `OtherSlicesCaseAMidVanish37` — the finite (18-element) Case-A coordinate grading for `37 ≤ d ≤ 74`,
  `d ≢ 32 (mod 36)` (the `d < 36` Case-A members are proven unconditionally);
* `OtherSlicesDworkDivisibility37` — the Case-B Artin-Hasse log valuation (Washington Prop 8.12) for
  `d ≥ 36`, `d ≡ 32 (mod 36)` `∉ {32, 68}`.

The whole-slice vanishing engine (`slice_eq_zero_of_formalSum_mem`) and the deg-`≠32,68` sum assembly
are **proven in full**; the deg-`≠32,68` slice vanishing rests only on the two residuals. -/
theorem fermatLastTheoremFor_thirtyseven_of_otherSlicesResiduals
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_precisionBridge : CaseIICor823Level71Deg68ModCubePrecisionBridge37)
    (caseII_otherSlicesCaseA : OtherSlicesCaseAMidVanish37)
    (caseII_otherSlicesDwork : OtherSlicesDworkDivisibility37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridgeAndFiniteLog
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    caseII_finiteLogIdentity
    caseII_precisionBridge
    (caseIICor823Level71Deg68OtherSlicesVanish37_of_residuals
      caseII_otherSlicesCaseA caseII_otherSlicesDwork)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
