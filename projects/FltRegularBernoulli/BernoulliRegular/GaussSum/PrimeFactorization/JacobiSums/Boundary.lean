module

public import BernoulliRegular.GaussSum.PrimeFactorization.JacobiSums.Additive

/-!
# Normalized boundary valuation for inverse-generator Gauss sums
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped Pointwise

namespace BernoulliRegular

section Assembly

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

local notation "𝔭" => (Ideal.span ({(p : ℤ)} : Set ℤ))
local instance : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩

lemma gaussSumIntegers_eq_rootSum
    (χ : DirichletCharacter ℂ p) :
    gaussSumIntegers p L χ =
      ∑ m : Fin (p - 1),
        gaussSumLiftCharacterValue (p := p) (L := L) χ
            (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)) *
          gaussSumLiftAdditiveRoot (p := p) L ^
            ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val) := by
  apply Subtype.ext
  change gaussSumLift p L χ =
      algebraMap (𝓞 L) L
        (∑ m : Fin (p - 1),
          gaussSumLiftCharacterValue (p := p) (L := L) χ
              (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)) *
            gaussSumLiftAdditiveRoot (p := p) L ^
              ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val))
  rw [gaussSumLift_eq_gaussSumLiftRootSum (p := p) (L := L)]
  unfold gaussSumLiftRootSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hlog :
      characterUnitGeneratorExponent (p := p)
          (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)) = m :=
    (characterUnitGeneratorPowEquiv (p := p)).symm_apply_apply m
  simp [gaussSumLiftCharacterValue, hlog, map_mul, map_pow]

lemma normalizedCharacterPrime_quotient_mk_natCast (n : ℕ) :
    characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
        (Pchar := normalizedCharacterPrime (p := p) (L := L))
        (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L))
          (n : 𝓞 (characterSubfield (L := L) (p := p)))) =
      (n : ZMod p) :=
  map_natCast (characterSubfieldPrimeQuotientEquivZMod
      (p := p) (L := L)
      (Pchar := normalizedCharacterPrime (p := p) (L := L))) n

lemma inverseGeneratorCoefficient_mul_val_sub_one_mem_normalizedBoundaryPrime
    (a : (ZMod p)ˣ) :
    gaussSumLiftCharacterValue (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) a *
        (a : ZMod p).val - 1 ∈
      normalizedBoundaryPrime (p := p) (L := L) := by
  let xchar : 𝓞 (characterSubfield (L := L) (p := p)) :=
    gaussSumLiftCharacterValueCharacterSubfieldInteger
        (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) a *
      (a : ZMod p).val - 1
  have hinv :=
    normalizedCharacterPrime_quotient_mk_inverseGeneratorCharacterValueCharacterSubfieldInteger
      (p := p) (L := L) a
  have hquot :
      characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
          (Pchar := normalizedCharacterPrime (p := p) (L := L))
          (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L)) xchar) = 0 := by
    calc
      characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
          (Pchar := normalizedCharacterPrime (p := p) (L := L))
          (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L)) xchar) =
        characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
            (Pchar := normalizedCharacterPrime (p := p) (L := L))
            (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L))
              (gaussSumLiftCharacterValueCharacterSubfieldInteger
                (p := p) (L := L)
                (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) a)) *
          characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
            (Pchar := normalizedCharacterPrime (p := p) (L := L))
            (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L))
              ((a : ZMod p).val : 𝓞 (characterSubfield (L := L) (p := p)))) -
          1 := by
        simp [xchar]
      _ = (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (a : ZMod p) - 1) := by
        rw [hinv,
          normalizedCharacterPrime_quotient_mk_natCast (p := p) (L := L)
            ((a : ZMod p).val),
          ZMod.natCast_zmod_val]
      _ = 0 := by
            calc
              (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (a : ZMod p) - 1) =
                  (1 : ZMod p) - 1 := by
                    congr 1
                    exact congrArg (fun u : (ZMod p)ˣ => ((u : ZMod p))) (inv_mul_cancel a)
              _ = 0 := by simp
  have hxchar_mem :
      xchar ∈ normalizedCharacterPrime (p := p) (L := L) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hquot' :
        characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
            (Pchar := normalizedCharacterPrime (p := p) (L := L))
            (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L)) xchar) =
          characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
            (Pchar := normalizedCharacterPrime (p := p) (L := L)) 0 := by
      simpa using hquot
    exact (characterSubfieldPrimeQuotientEquivZMod
      (p := p) (L := L)
      (Pchar := normalizedCharacterPrime (p := p) (L := L))).injective hquot'
  have hxchar_mem' :
      xchar ∈ (normalizedBoundaryPrime (p := p) (L := L)).under
        (𝓞 (characterSubfield (L := L) (p := p))) := by
    simpa [normalizedBoundaryPrime_under_characterSubfield (p := p) (L := L)] using hxchar_mem
  rw [Ideal.mem_comap] at hxchar_mem'
  change
    gaussSumLiftCharacterValue (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) a *
        ((a : ZMod p).val : 𝓞 L) - 1 ∈
      normalizedBoundaryPrime (p := p) (L := L) at hxchar_mem'
  simpa [ZMod.natCast_val] using hxchar_mem'

lemma inverseGeneratorCoefficientSum_eq_zero (hp_odd : p ≠ 2) :
    ∑ m : Fin (p - 1),
      gaussSumLiftCharacterValue (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2))
        (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)) = 0 := by
  let χ : DirichletCharacter ℂ p :=
    stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)
  have hp2 : 2 ≤ p := hp.out.two_le
  let j : Fin (p - 1) := ⟨p - 2, by omega⟩
  have hj : j ≠ 0 := by
    intro hj0
    have hval : p - 2 = 0 := by
      simpa [j] using congrArg Fin.val hj0
    omega
  have hχ : χ ≠ 1 := by
    simpa [χ, j] using
      stickelbergerComplexCharacterGenerator_pow_ne_one_of_ne_zero
        (p := p) (j := j) hj
  apply Subtype.ext
  have hsumC :
      ∑ m : Fin (p - 1),
        stickelbergerEmbedding p L
          (((gaussSumLiftCharacterValue (p := p) (L := L) χ
              (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)) : 𝓞 L) : L)) = 0 := by
    have hF0 : χ (0 : ZMod p) = 0 :=
      MulChar.map_nonunit _ (by simp)
    calc
      ∑ m : Fin (p - 1),
          stickelbergerEmbedding p L
            (((gaussSumLiftCharacterValue (p := p) (L := L) χ
                (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)) : 𝓞 L) : L)) =
        ∑ m : Fin (p - 1),
          χ ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p)) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [stickelbergerEmbedding_gaussSumLiftCharacterValue]
      _ = ∑ a : ZMod p, χ a := by
            symm
            exact sum_zmod_eq_sum_characterUnitGeneratorPowers (p := p) (F := fun a => χ a) hF0
      _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  have hsumL :
      (((∑ m : Fin (p - 1),
          gaussSumLiftCharacterValue (p := p) (L := L)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2))
            (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ))) : 𝓞 L) : L) = 0 := by
    apply (stickelbergerEmbedding p L).injective
    simpa [map_sum] using hsumC
  have hsumL' :
      (((∑ m : Fin (p - 1),
          gaussSumLiftCharacterValue (p := p) (L := L)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2))
            (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ))) : 𝓞 L) : L) =
        ((0 : 𝓞 L) : L) := by
    simpa using hsumL
  exact hsumL'

lemma inverseGeneratorRootSum_term_sub_coeff_sub_uniformizer_mem_normalizedBoundaryPrime_sq
    (m : Fin (p - 1)) :
    let a : ℕ :=
      ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val)
    let c : 𝓞 L :=
      gaussSumLiftCharacterValue (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2))
        (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ))
    c * gaussSumLiftAdditiveRoot (p := p) L ^ a - c -
        (gaussSumLiftAdditiveRoot (p := p) L - 1) ∈
      normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
  let a : ℕ :=
    ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val)
  let u : (ZMod p)ˣ := ((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)
  let c : 𝓞 L :=
    gaussSumLiftCharacterValue (p := p) (L := L)
      (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) u
  change
    c * gaussSumLiftAdditiveRoot (p := p) L ^ a - c -
        (gaussSumLiftAdditiveRoot (p := p) L - 1) ∈
      normalizedBoundaryPrime (p := p) (L := L) ^ 2
  have hadd :
      c * (gaussSumLiftAdditiveRoot (p := p) L ^ a - 1 -
            (a : 𝓞 L) * (gaussSumLiftAdditiveRoot (p := p) L - 1)) ∈
        normalizedBoundaryPrime (p := p) (L := L) ^ 2 :=
    Ideal.mul_mem_left _ _ <|
      gaussSumLiftAdditiveRoot_pow_sub_one_sub_mul_mem_normalizedBoundaryPrime_sq
        (p := p) (L := L) a
  have hcoeff :
      (c * a - 1) * (gaussSumLiftAdditiveRoot (p := p) L - 1) ∈
        normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
    have hcoeff' :
        (c * ((u : ZMod p).val : 𝓞 L) - 1) *
            (gaussSumLiftAdditiveRoot (p := p) L - 1) ∈
          normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
      simpa [c, pow_two] using Ideal.mul_mem_mul
        (inverseGeneratorCoefficient_mul_val_sub_one_mem_normalizedBoundaryPrime
          (p := p) (L := L) u)
        (gaussSumLiftAdditiveRoot_sub_one_mem_normalizedBoundaryPrime (p := p) (L := L))
    simpa [a, u] using hcoeff'
  have hrewrite :
      c * gaussSumLiftAdditiveRoot (p := p) L ^ a - c -
          (gaussSumLiftAdditiveRoot (p := p) L - 1) =
        c * (gaussSumLiftAdditiveRoot (p := p) L ^ a - 1 -
              (a : 𝓞 L) * (gaussSumLiftAdditiveRoot (p := p) L - 1)) +
          (c * a - 1) * (gaussSumLiftAdditiveRoot (p := p) L - 1) := by
    dsimp [a, c]
    ring_nf
  rw [hrewrite]
  exact Ideal.add_mem _ hadd hcoeff

lemma gaussSumIntegers_inverseGenerator_add_sub_one_mem_normalizedBoundaryPrime_sq
    (hp_odd : p ≠ 2) :
    gaussSumIntegers p L
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) +
        (gaussSumLiftAdditiveRoot (p := p) L - 1) ∈
      normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
  let χ : DirichletCharacter ℂ p :=
    stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)
  let ζ : 𝓞 L := gaussSumLiftAdditiveRoot (p := p) L
  have hsum_mem :
      (∑ m : Fin (p - 1),
          let a : ℕ :=
            ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val)
          let c : 𝓞 L :=
            gaussSumLiftCharacterValue (p := p) (L := L) χ
              (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ))
          c * ζ ^ a - c - (ζ - 1)) ∈
        normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
    refine Ideal.sum_mem _ ?_
    intro m hm
    simpa [χ, ζ] using
      inverseGeneratorRootSum_term_sub_coeff_sub_uniformizer_mem_normalizedBoundaryPrime_sq
        (p := p) (L := L) m
  have hcoeffsum :
      ∑ m : Fin (p - 1),
        gaussSumLiftCharacterValue (p := p) (L := L) χ
          (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ)) = 0 :=
    inverseGeneratorCoefficientSum_eq_zero (p := p) (L := L) hp_odd
  have hrewrite :
      (∑ m : Fin (p - 1),
          let a : ℕ :=
            ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val)
          let c : 𝓞 L :=
            gaussSumLiftCharacterValue (p := p) (L := L) χ
              (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ))
          c * ζ ^ a - c - (ζ - 1)) =
        gaussSumIntegers p L χ - ((p - 1 : ℕ) : 𝓞 L) * (ζ - 1) := by
    rw [gaussSumIntegers_eq_rootSum (p := p) (L := L) χ,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcoeffsum,
      Finset.sum_const]
    simp [ζ, nsmul_eq_mul]
  have hbase :
      gaussSumIntegers p L χ - ((p - 1 : ℕ) : 𝓞 L) * (ζ - 1) ∈
        normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
    rw [← hrewrite]
    exact hsum_mem
  have hnorm : normalizedBoundaryPrime (p := p) (L := L) ∈ primesAboveP p L := by
    rw [← characterSidePrimeOrbit_eq_primesAboveP (p := p) (L := L)]
    exact normalizedBoundaryPrime_mem_characterSidePrimeOrbit (p := p) (L := L)
  have hp_mem :
      (p : 𝓞 L) ∈ normalizedBoundaryPrime (p := p) (L := L) := by
    have hP_over :
        normalizedBoundaryPrime (p := p) (L := L) ∈ Ideal.primesOver 𝔭 (𝓞 L) :=
      (mem_primesAboveP_iff (p := p) (L := L)).1 hnorm
    have hunder :
        𝔭 = (normalizedBoundaryPrime (p := p) (L := L)).under ℤ :=
      (Ideal.liesOver_iff _ _).mp hP_over.2
    have hp_mem_under :
        (p : ℤ) ∈ (normalizedBoundaryPrime (p := p) (L := L)).under ℤ := by
      rw [← hunder]
      exact Ideal.subset_span (by simp : (p : ℤ) ∈ ({(p : ℤ)} : Set ℤ))
    rw [Ideal.mem_comap] at hp_mem_under
    simpa using hp_mem_under
  have hpζ_mem :
      (p : 𝓞 L) * (ζ - 1) ∈ normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hp_mem
      (gaussSumLiftAdditiveRoot_sub_one_mem_normalizedBoundaryPrime (p := p) (L := L))
  have hp_cast : ((p - 1 : ℕ) : 𝓞 L) + 1 = (p : 𝓞 L) := by
    exact_mod_cast Nat.sub_add_cancel hp.out.one_le
  have hrewrite' :
      gaussSumIntegers p L χ + (ζ - 1) =
        (gaussSumIntegers p L χ - ((p - 1 : ℕ) : 𝓞 L) * (ζ - 1)) +
          (p : 𝓞 L) * (ζ - 1) := by
    calc
      gaussSumIntegers p L χ + (ζ - 1) =
          (gaussSumIntegers p L χ - ((p - 1 : ℕ) : 𝓞 L) * (ζ - 1)) +
            ((((p - 1 : ℕ) : 𝓞 L) + 1) * (ζ - 1)) := by ring
      _ = (gaussSumIntegers p L χ - ((p - 1 : ℕ) : 𝓞 L) * (ζ - 1)) +
            (p : 𝓞 L) * (ζ - 1) := by rw [hp_cast]
  rw [hrewrite']
  exact Ideal.add_mem _ hbase hpζ_mem

lemma gaussSumIntegers_inverseGenerator_mem_normalizedBoundaryPrime
    (hp_odd : p ≠ 2) :
    gaussSumIntegers p L
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) ∈
      normalizedBoundaryPrime (p := p) (L := L) := by
  let χ : DirichletCharacter ℂ p :=
    stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)
  let ζ : 𝓞 L := gaussSumLiftAdditiveRoot (p := p) L
  have hcong_sq :
      gaussSumIntegers p L χ + (ζ - 1) ∈
        normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
    simpa [χ, ζ] using
      gaussSumIntegers_inverseGenerator_add_sub_one_mem_normalizedBoundaryPrime_sq
        (p := p) (L := L) hp_odd
  have hsq_le :
      normalizedBoundaryPrime (p := p) (L := L) ^ 2 ≤
        normalizedBoundaryPrime (p := p) (L := L) := by
    rw [pow_two]
    exact Ideal.mul_le_left
  have hcong :
      gaussSumIntegers p L χ + (ζ - 1) ∈
        normalizedBoundaryPrime (p := p) (L := L) :=
    hsq_le hcong_sq
  have hζ :
      ζ - 1 ∈ normalizedBoundaryPrime (p := p) (L := L) := by
    simpa [ζ] using
      gaussSumLiftAdditiveRoot_sub_one_mem_normalizedBoundaryPrime (p := p) (L := L)
  have hrewrite :
      gaussSumIntegers p L χ =
        (gaussSumIntegers p L χ + (ζ - 1)) - (ζ - 1) := by
    ring
  rw [hrewrite]
  exact Ideal.sub_mem _ hcong hζ

lemma gaussSumIntegers_inverseGenerator_not_mem_normalizedBoundaryPrime_sq
    (hp_odd : p ≠ 2) :
    gaussSumIntegers p L
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) ∉
      normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
  intro hτ
  let χ : DirichletCharacter ℂ p :=
    stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)
  let ζ : 𝓞 L := gaussSumLiftAdditiveRoot (p := p) L
  have hcong :
      gaussSumIntegers p L χ + (ζ - 1) ∈
        normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
    simpa [χ, ζ] using
      gaussSumIntegers_inverseGenerator_add_sub_one_mem_normalizedBoundaryPrime_sq
        (p := p) (L := L) hp_odd
  have hζ_sq :
      ζ - 1 ∈ normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
    have hrewrite :
        ζ - 1 = (gaussSumIntegers p L χ + (ζ - 1)) - gaussSumIntegers p L χ := by
      ring
    rw [hrewrite]
    exact Ideal.sub_mem _ hcong (by simpa [χ] using hτ)
  exact gaussSumLiftAdditiveRoot_sub_one_not_mem_normalizedBoundaryPrime_sq
    (p := p) (L := L) (by simpa [ζ] using hζ_sq)

lemma primeAbovePExponent_normalizedBoundaryPrime_inverseGenerator_eq_one
    (hp_odd : p ≠ 2) :
    primeAbovePExponent (p := p) (L := L)
        (normalizedBoundaryPrime (p := p) (L := L))
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) = 1 := by
  unfold primeAbovePExponent gaussSumIdeal
  apply Ideal.count_normalizedFactors_eq
  · rw [pow_one, Ideal.span_singleton_le_iff_mem]
    exact gaussSumIntegers_inverseGenerator_mem_normalizedBoundaryPrime
      (p := p) (L := L) hp_odd
  · intro hle
    exact gaussSumIntegers_inverseGenerator_not_mem_normalizedBoundaryPrime_sq
      (p := p) (L := L) hp_odd
      ((Ideal.span_singleton_le_iff_mem
        (I := normalizedBoundaryPrime (p := p) (L := L) ^ 2)).mp (by simpa using hle))

lemma stickelbergerComplexCharacterGenerator_pow_pred_ne_one (hp_odd : p ≠ 2) :
    stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2) ≠ 1 := by
  have hp_two : 2 ≤ p := hp.out.two_le
  let j : Fin (p - 1) := ⟨p - 2, by omega⟩
  have hj : j ≠ 0 := by
    intro hj0
    have hval : p - 2 = 0 := by
      simpa [j] using congrArg Fin.val hj0
    omega
  simpa [j] using
    stickelbergerComplexCharacterGenerator_pow_ne_one_of_ne_zero
      (p := p) (j := j) hj

lemma distinguishedPrimeExponent_inverseGenerator_normalizedTransport_eq_one
    (hp_odd : p ≠ 2) :
    distinguishedPrimeExponent (p := p) (L := L)
        ((stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) ^
          (((normalizedCharacterPrimeIndex (p := p) (L := L))⁻¹ :
              (ZMod (p - 1))ˣ) : ZMod (p - 1)).val) = 1 := by
  let χ : DirichletCharacter ℂ p :=
    stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)
  let b : (ZMod (p - 1))ˣ := normalizedCharacterPrimeIndex (p := p) (L := L)
  have hχ : χ ≠ 1 := by
    simpa [χ] using
      stickelbergerComplexCharacterGenerator_pow_pred_ne_one (p := p) hp_odd
  have hψ : χ ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val) ≠ 1 :=
    pow_characterSideUnit_ne_one (p := p) hχ b⁻¹
  have hpow :
      (χ ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val)) ^
          ((b : ZMod (p - 1)).val) = χ := by
    simpa using
      pow_characterSideUnit_val_pow_inv_eq_self (p := p) (b := b⁻¹) χ
  have htransport :=
    sigmaOfCharacterUnitPrimeExponent_eq_distinguishedPrimeExponent
      (p := p) (L := L) b
      (χ := χ ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val)) hψ
  have htransport' :
      primeAbovePExponent (p := p) (L := L)
          (normalizedBoundaryPrime (p := p) (L := L)) χ =
        distinguishedPrimeExponent (p := p) (L := L)
          (χ ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val)) := by
    simpa [χ, b, normalizedBoundaryPrime, characterSidePrimeMap, hpow] using htransport
  have hcount :
      primeAbovePExponent (p := p) (L := L)
          (normalizedBoundaryPrime (p := p) (L := L)) χ = 1 := by
    simpa [χ] using
      primeAbovePExponent_normalizedBoundaryPrime_inverseGenerator_eq_one
        (p := p) (L := L) hp_odd
  simpa [χ, b] using htransport'.symm.trans hcount

lemma characterSideExponentVector_inverseGenerator_normalizedCharacterPrimeIndex_eq_one
    (hp_odd : p ≠ 2) :
    characterSideExponentVector (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2))
        (normalizedCharacterPrimeIndex (p := p) (L := L)) = 1 := by
  simpa [characterSideExponentVector] using
    distinguishedPrimeExponent_inverseGenerator_normalizedTransport_eq_one
      (p := p) (L := L) hp_odd

lemma stickelbergerCoefficientTarget_inverseGenerator_normalizedIndex_eq_one
    (hp_odd : p ≠ 2) :
    stickelbergerGeneratorPowerCoefficientTarget (p := p) (L := L)
        ((p - 2 : ℕ) : ZMod (p - 1))
        (normalizedCharacterPrimeIndex (p := p) (L := L)) = 1 := by
  have hp1 : 1 < p - 1 := by
    have hp2 : 2 ≤ p := hp.out.two_le
    omega
  letI : Fact (1 < p - 1) := ⟨hp1⟩
  have hpred_add :
      ((p - 2 : ℕ) : ZMod (p - 1)) + 1 = 0 := by
    have hsub : p - 2 + 1 = p - 1 := by omega
    have hcast :
        ((p - 2 : ℕ) : ZMod (p - 1)) + ((1 : ℕ) : ZMod (p - 1)) = 0 := by
      rw [← Nat.cast_add, hsub]
      simp
    simpa using hcast
  have hpred :
      ((p - 2 : ℕ) : ZMod (p - 1)) = -1 :=
    eq_neg_of_add_eq_zero_left hpred_add
  have hval1 : (1 : ZMod (p - 1)).val = 1 := ZMod.val_one (p - 1)
  simp [stickelbergerGeneratorPowerCoefficientTarget,
    stickelbergerGeneratorPowerNormalizedParameter,
    stickelbergerGeneratorPowerParameter, hpred, hval1]

lemma characterSideExponentVector_inverseGenerator_normalizedIndex_eq_target
    (hp_odd : p ≠ 2) :
    characterSideExponentVector (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2))
        (normalizedCharacterPrimeIndex (p := p) (L := L)) =
      stickelbergerGeneratorPowerCoefficientTarget (p := p) (L := L)
        ((p - 2 : ℕ) : ZMod (p - 1))
        (normalizedCharacterPrimeIndex (p := p) (L := L)) := by
  rw [characterSideExponentVector_inverseGenerator_normalizedCharacterPrimeIndex_eq_one
      (p := p) (L := L) hp_odd,
    stickelbergerCoefficientTarget_inverseGenerator_normalizedIndex_eq_one
      (p := p)
      (L := L) hp_odd]

end Assembly

end BernoulliRegular
