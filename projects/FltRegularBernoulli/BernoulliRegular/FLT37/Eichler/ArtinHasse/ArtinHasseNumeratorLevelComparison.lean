import BernoulliRegular.FLT37.Eichler.ArtinHasse.ArtinHasseCoordPolyHomogeneity

/-!
# The level-`107` ↔ level-`71` deg-`68` Artin-Hasse numerator difference lies in `(λ)^{108}`

For each `a ∈ [1, 68]`, the degree-`68` Artin-Hasse log numerator at level `107` (Dwork-parameter
approximant `x₁₀₇ = dworkParameterApprox 108`) and at level `71` (approximant `x₇₁ =
dworkParameterApprox 72`) differ by an element of `(λ)^{108}`:

  `coeff_{68} ((Poly 107 x₁₀₇)^a) − coeff_{68} ((Poly 71 x₇₁)^a) ∈ (λ)^{108}`.

The difference splits into a **truncation** part (level `107` vs `71`, same `x₁₀₇`) lying in `(λ)^{140}`
(`…_pow_coeff_sub_coeff_mem_lambdaIdeal_pow` at `N=71, M=107, d=68`), and an **`x`-difference** part
(same truncation `71`, `x₁₀₇` vs `x₇₁`) which by the homogeneity
`…_pow_coeff_eq_mul_pow` (`coeff_{68}((Poly 71 x)^a) = C₇₁·x^{68}`, `C₇₁` `x`-independent) equals
`C₇₁·(x₁₀₇^{68} − x₇₁^{68})`, lying in `(λ)^{139}` since `x₁₀₇ − x₇₁ ∈ (λ)^{72}`
(`dworkParameterApprox_sub_mem_lambdaIdeal_pow`) and each `x ∈ (λ)^{1}`.  Both parts lie in `(λ)^{108}`.

This is the key membership making the level-`107` deg-`68` slice, folded to precision `72`, **equal**
to the level-`71` deg-`68` slice (the `a = 37` Frobenius division by `37` keeps the `(λ)^{108}`
agreement at `(λ)^{72} = ` the precision, killing the difference).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField
open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

private instance instFact37Deg68NLD : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **`dworkParameterApprox 108 ^ 68 − dworkParameterApprox 72 ^ 68 ∈ (λ)^{139}`** (proven): the
power difference `x₁₀₇^{68} − x₇₁^{68} = (x₁₀₇ − x₇₁)·∑ᵢ x₁₀₇^i x₇₁^{67−i}` has the factor
`x₁₀₇ − x₇₁ ∈ (λ)^{72}` (`dworkParameterApprox_sub_mem_lambdaIdeal_pow`) and the cofactor
`∑ᵢ x₁₀₇^i x₇₁^{67−i} ∈ (λ)^{67}` (each summand a product of `67` factors each in `λ`), so the
difference lies in `(λ)^{72+67} = (λ)^{139}`. -/
theorem dworkParameterApprox_pow_sixtyeight_sub_mem :
    dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68 -
        dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68 ∈
      (lambdaIdeal 37 K) ^ 139 := by
  have hamem : dworkParameterApprox 37 K (3 * (37 - 1)) ∈ lambdaIdeal 37 K :=
    dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) _
  have hbmem : dworkParameterApprox 37 K (2 * (37 - 1)) ∈ lambdaIdeal 37 K :=
    dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) _
  have hsub : dworkParameterApprox 37 K (3 * (37 - 1)) -
      dworkParameterApprox 37 K (2 * (37 - 1)) ∈ (lambdaIdeal 37 K) ^ 72 := by
    have h := dworkParameterApprox_sub_mem_lambdaIdeal_pow (p := 37) (K := K)
      (show 2 * (37 - 1) ≤ 3 * (37 - 1) by norm_num)
    convert h using 2
  -- geometric-sum factorization `a^68 - b^68 = (∑ a^i b^{67-i})·(a - b)`
  rw [(geom_sum₂_mul (dworkParameterApprox 37 K (3 * (37 - 1)))
    (dworkParameterApprox 37 K (2 * (37 - 1))) 68).symm]
  -- cofactor `∑ a^i b^{67-i} ∈ (λ)^{67}`
  have hcofactor : (∑ i ∈ Finset.range 68,
      dworkParameterApprox 37 K (3 * (37 - 1)) ^ i *
        dworkParameterApprox 37 K (2 * (37 - 1)) ^ (68 - 1 - i)) ∈
      (lambdaIdeal 37 K) ^ 67 := by
    refine Ideal.sum_mem _ ?_
    intro i hi
    have hilt : i < 68 := Finset.mem_range.mp hi
    have hai : dworkParameterApprox 37 K (3 * (37 - 1)) ^ i ∈ (lambdaIdeal 37 K) ^ i :=
      Ideal.pow_mem_pow hamem i
    have hbi : dworkParameterApprox 37 K (2 * (37 - 1)) ^ (68 - 1 - i) ∈
        (lambdaIdeal 37 K) ^ (68 - 1 - i) := Ideal.pow_mem_pow hbmem _
    have hmul : dworkParameterApprox 37 K (3 * (37 - 1)) ^ i *
        dworkParameterApprox 37 K (2 * (37 - 1)) ^ (68 - 1 - i) ∈
        (lambdaIdeal 37 K) ^ (i + (68 - 1 - i)) := by
      rw [pow_add]; exact Ideal.mul_mem_mul hai hbi
    exact Ideal.pow_le_pow_right (by omega) hmul
  -- product `(λ)^{67}·(λ)^{72} = (λ)^{139}`
  have hprod := Ideal.mul_mem_mul hcofactor hsub
  rw [← pow_add] at hprod
  exact hprod

-- The ideal-power membership transports over the heavy `adicCompletionIntegers` ring; the
-- `generalize` steps dodge the `Ideal.pow` `whnf` wall but the assembly is above the default budget.
set_option maxHeartbeats 2000000 in
omit [NumberField.IsCMField K] in
/-- **The level-`107` ↔ level-`71` deg-`68` poly-power coefficient difference lies in `(λ)^{108}`**
(proven, axiom-clean): for every `a`,

  `coeff_{68} ((Poly 107 x₁₀₇)^a) − coeff_{68} ((Poly 71 x₇₁)^a) ∈ (λ)^{108}`,

with `x₁₀₇ = dworkParameterApprox 108`, `x₇₁ = dworkParameterApprox 72`.  The difference splits as

  `[coeff_{68}((Poly 107 x₁₀₇)^a) − coeff_{68}((Poly 71 x₁₀₇)^a)]   (truncation, same x₁₀₇)`
  `+ [coeff_{68}((Poly 71 x₁₀₇)^a) − coeff_{68}((Poly 71 x₇₁)^a)]    (x-difference, same level 71)`.

The truncation part lies in `(λ)^{140}` (`…_pow_coeff_sub_coeff_mem_lambdaIdeal_pow` at `N=71, M=107,
d=68`, with `68 < 71 + a`); the `x`-difference part is `C₇₁·(x₁₀₇^{68} − x₇₁^{68})` by homogeneity
(`…_pow_coeff_eq_mul_pow`), and `x₁₀₇^{68} − x₇₁^{68} ∈ (λ)^{139}`
(`dworkParameterApprox_pow_sixtyeight_sub_mem`).  Both lie in `(λ)^{108}`. -/
theorem deg68_coordPoly_pow_coeff_level_diff_mem (a : ℕ) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
        (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
        (dworkParameterApprox 37 K (2 * (37 - 1)))) ^ a).coeff 68 ∈
      (lambdaIdeal 37 K) ^ 108 := by
  have hx107mem : dworkParameterApprox 37 K (3 * (37 - 1)) ∈ lambdaIdeal 37 K :=
    dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) _
  -- split through the level-71 / x₁₀₇ coefficient.
  have hsplit :
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
          (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
          (dworkParameterApprox 37 K (2 * (37 - 1)))) ^ a).coeff 68 =
      (((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
          (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
          (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68) +
      (((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
          (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
          (dworkParameterApprox 37 K (2 * (37 - 1)))) ^ a).coeff 68) := by ring
  have hle140 : (lambdaIdeal 37 K) ^ (71 + 1 + 68) ≤ (lambdaIdeal 37 K) ^ 108 :=
    Ideal.pow_le_pow_right (by omega)
  have hle139 : (lambdaIdeal 37 K) ^ 139 ≤ (lambdaIdeal 37 K) ^ 108 :=
    Ideal.pow_le_pow_right (by omega)
  rw [hsplit]
  refine Ideal.add_mem _ ?_ ?_
  · -- truncation part: in `(λ)^{140} ⊆ (λ)^{108}`, with `N = 71 ≤ M = 107`, `d = 68 < 71 + a`.
    -- The lemma gives `coeff(Poly 71) - coeff(Poly 107)`; the goal is its negation.
    have htrunc := samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_sub_coeff_mem_lambdaIdeal_pow
      (p := 37) (K := K) 71 107 a 68 hx107mem (by norm_num)
    rw [if_pos (by omega : 68 < 71 + a)] at htrunc
    have hgoal :
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
            (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 =
        -(((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
            (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68) := by ring
    rw [hgoal]
    -- generalize the heavy coefficient element to dodge the `adicCompletionIntegers` whnf wall.
    generalize ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
        (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
        (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 = w at htrunc ⊢
    exact neg_mem (hle140 htrunc)
  · -- x-difference part: by homogeneity `= C₇₁·(x₁₀₇^{68} - x₇₁^{68}) ∈ (λ)^{139} ⊆ (λ)^{108}`.
    rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow
        (p := 37) (K := K) 71 a 68 (dworkParameterApprox 37 K (3 * (37 - 1))),
      samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow
        (p := 37) (K := K) 71 a 68 (dworkParameterApprox 37 K (2 * (37 - 1)))]
    rw [← mul_sub]
    have hpow := dworkParameterApprox_pow_sixtyeight_sub_mem (K := K)
    have hmem : ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71 1) ^ a).coeff 68 *
        (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68 -
          dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68) ∈ (lambdaIdeal 37 K) ^ 139 :=
      (Ideal.mul_mem_left _ _ hpow)
    -- generalize to dodge the whnf wall on the heavy product element.
    generalize ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71 1) ^ a).coeff 68 *
        (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68 -
          dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68) = w at hmem ⊢
    exact hle139 hmem

-- The numerator `def`-unfold introduces `(-1)^{a+1}·coeff` over the heavy `adicCompletionIntegers`
-- ring; the membership is above the default budget (the coeff difference lemma is the heavy input).
set_option maxHeartbeats 2000000 in
omit [NumberField.IsCMField K] in
/-- **The level-`107` ↔ level-`71` deg-`68` Artin-Hasse numerator difference lies in `(λ)^{108}`**
(proven, axiom-clean): for every `a`,

  `numerator 107 a 68 x₁₀₇ − numerator 71 a 68 x₇₁ ∈ (λ)^{108}`.

The numerator is `(−1)^{a+1}·coeff_{68}((Poly N x)^a)`, so the difference is `(−1)^{a+1}·(coeff₁₀₇ −
coeff₇₁)` and `coeff₁₀₇ − coeff₇₁ ∈ (λ)^{108}` (`deg68_coordPoly_pow_coeff_level_diff_mem`). -/
theorem deg68_numerator_level_diff_mem (a : ℕ) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator (p := 37) (K := K) 107 a 68
        (dworkParameterApprox 37 K (3 * (37 - 1))) -
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator (p := 37) (K := K) 71 a 68
        (dworkParameterApprox 37 K (2 * (37 - 1))) ∈ (lambdaIdeal 37 K) ^ 108 := by
  have hcoeff := deg68_coordPoly_pow_coeff_level_diff_mem (K := K) a
  have heq : samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator (p := 37) (K := K) 107
        a 68 (dworkParameterApprox 37 K (3 * (37 - 1))) -
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator (p := 37) (K := K) 71 a 68
        (dworkParameterApprox 37 K (2 * (37 - 1))) =
      ((-1 : ValuedIntegerRing 37 K) ^ (a + 1)) *
        (((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
            (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
            (dworkParameterApprox 37 K (2 * (37 - 1)))) ^ a).coeff 68) := by
    rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator, mul_sub]
  rw [heq]
  exact Ideal.mul_mem_left _ _ hcoeff

end CyclotomicUnits
end BernoulliRegular

end
