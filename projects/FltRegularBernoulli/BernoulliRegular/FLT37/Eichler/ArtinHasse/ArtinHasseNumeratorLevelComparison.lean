import BernoulliRegular.FLT37.Eichler.ArtinHasse.ArtinHasseCoordPolyHomogeneity

/-!
# Level comparison for the degree-`68` Artin-Hasse numerator

This file proves that the degree-`68` Artin-Hasse numerator slice computed at level
`107` agrees with the corresponding level-`71` slice modulo `(λ)^{108}`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

private instance instFact37Deg68NLD : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

set_option maxRecDepth 4000 in
omit [NumberField.IsCMField K] in
/-- The degree-`68` powers of the level-`108` and level-`72` Dwork-parameter
approximants differ by an element of `(λ)^{139}`. -/
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
  rw [(geom_sum₂_mul (dworkParameterApprox 37 K (3 * (37 - 1)))
    (dworkParameterApprox 37 K (2 * (37 - 1))) 68).symm]
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
  have hprod := Ideal.mul_mem_mul hcofactor hsub
  rw [← pow_add] at hprod
  exact hprod

set_option maxRecDepth 4000 in
omit [NumberField.IsCMField K] in
/-- The level-`107` and level-`71` degree-`68` coordinate-polynomial coefficients
differ by an element of `(λ)^{108}`. -/
theorem deg68_coordPoly_pow_coeff_level_diff_mem (a : ℕ) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
        (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
        (dworkParameterApprox 37 K (2 * (37 - 1)))) ^ a).coeff 68 ∈
      (lambdaIdeal 37 K) ^ 108 := by
  have hx107mem : dworkParameterApprox 37 K (3 * (37 - 1)) ∈ lambdaIdeal 37 K :=
    dworkParameterApprox_mem_lambdaIdeal (p := 37) (K := K) _
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
    Ideal.pow_le_pow_right (by lia)
  have hle139 : (lambdaIdeal 37 K) ^ 139 ≤ (lambdaIdeal 37 K) ^ 108 :=
    Ideal.pow_le_pow_right (by lia)
  rw [hsplit]
  refine Ideal.add_mem _ ?_ ?_
  · have htrunc :=
      samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_sub_coeff_mem_lambdaIdeal_pow
      (p := 37) (K := K) 71 107 a 68 hx107mem (by norm_num)
    rw [if_pos (by lia : 68 < 71 + a)] at htrunc
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
    generalize ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71
        (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 -
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 107
        (dworkParameterApprox 37 K (3 * (37 - 1)))) ^ a).coeff 68 = w at htrunc ⊢
    exact neg_mem (hle140 htrunc)
  · rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow
        (p := 37) (K := K) 71 a 68 (dworkParameterApprox 37 K (3 * (37 - 1))),
      samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow
        (p := 37) (K := K) 71 a 68 (dworkParameterApprox 37 K (2 * (37 - 1)))]
    rw [← mul_sub]
    have hpow := dworkParameterApprox_pow_sixtyeight_sub_mem (K := K)
    have hmem :
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71 1) ^ a).coeff 68 *
        (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68 -
          dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68) ∈ (lambdaIdeal 37 K) ^ 139 :=
      (Ideal.mul_mem_left _ _ hpow)
    generalize
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := 37) (K := K) 71 1) ^ a).coeff 68 *
        (dworkParameterApprox 37 K (3 * (37 - 1)) ^ 68 -
          dworkParameterApprox 37 K (2 * (37 - 1)) ^ 68) = w at hmem ⊢
    exact hle139 hmem

omit [NumberField.IsCMField K] in
/-- The level-`107` and level-`71` degree-`68` Artin-Hasse numerator terms
differ by an element of `(λ)^{108}`. -/
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
