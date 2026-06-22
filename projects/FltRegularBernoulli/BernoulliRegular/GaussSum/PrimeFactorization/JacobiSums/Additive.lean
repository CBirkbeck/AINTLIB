module

public import BernoulliRegular.GaussSum.PrimeFactorization.JacobiSums.Basic

/-!
# Additive first-order expansions for Jacobi sums
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

private lemma additiveZetaPrime_mem_primesOver :
    additiveZetaPrime (L := L) (p := p) ∈
      Ideal.primesOver 𝔭 (𝓞 (additiveSubfield (L := L) (p := p))) := by
  have hmem :
      (distinguishedPrimeAboveP p L).under
          (𝓞 (additiveSubfield (L := L) (p := p))) ∈
        Ideal.primesOver 𝔭 (𝓞 (additiveSubfield (L := L) (p := p))) := by
    let P : Ideal (𝓞 (additiveSubfield (L := L) (p := p))) :=
      (distinguishedPrimeAboveP p L).under
        (𝓞 (additiveSubfield (L := L) (p := p)))
    haveI : P.IsPrime := inferInstance
    haveI : P.LiesOver 𝔭 := by
      dsimp [P]
      infer_instance
    exact ⟨inferInstance, inferInstance⟩
  simpa [distinguishedPrimeAboveP_under_additiveSubfield_eq_additiveZetaPrime
    (p := p) (L := L)] using hmem

private lemma normalizedBoundaryPrime_mem_primesAboveP :
    normalizedBoundaryPrime (p := p) (L := L) ∈ primesAboveP p L := by
  rw [← characterSidePrimeOrbit_eq_primesAboveP (p := p) (L := L)]
  exact normalizedBoundaryPrime_mem_characterSidePrimeOrbit (p := p) (L := L)

lemma gaussSumLiftAdditiveRoot_sub_one_mem_primeAboveP
    {P : Ideal (𝓞 L)} (hP : P ∈ primesAboveP p L) :
    gaussSumLiftAdditiveRoot (p := p) L - 1 ∈ P := by
  have hP_over : P ∈ Ideal.primesOver 𝔭 (𝓞 L) :=
    (mem_primesAboveP_iff (p := p) (L := L)).1 hP
  haveI : P.IsPrime := hP_over.1
  haveI : P.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP_over
  haveI : P.LiesOver 𝔭 := hP_over.2
  have hp0 : (𝔭 : Ideal ℤ) ≠ ⊥ := by
    simp [hp.out.ne_zero]
  have hp_mem : (p : 𝓞 L) ∈ P := by
    have hunder : 𝔭 = P.under ℤ :=
      (Ideal.liesOver_iff _ _).mp (show P.LiesOver 𝔭 from inferInstance)
    have hp_mem_under : (p : ℤ) ∈ P.under ℤ := by
      rw [← hunder]
      exact Ideal.subset_span (by simp : (p : ℤ) ∈ ({(p : ℤ)} : Set ℤ))
    rw [Ideal.mem_comap] at hp_mem_under
    simpa using hp_mem_under
  have hp_nonunit : (p : 𝓞 L) ∈ nonunits (𝓞 L) := by
    rw [mem_nonunits_iff]
    intro hp_unit
    exact (show P ≠ ⊤ from (inferInstance : P.IsPrime).ne_top)
      (Ideal.eq_top_of_isUnit_mem P hp_mem hp_unit)
  letI : NeZero (Ideal.ramificationIdx 𝔭 P) :=
    ⟨Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
      (R := ℤ) (S := 𝓞 L) (p := 𝔭) P hp0⟩
  letI : Algebra (ℤ ⧸ 𝔭) (𝓞 L ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero 𝔭 P
  letI : CharP (ℤ ⧸ 𝔭) p :=
    charP_of_injective_ringHom
      (f := (Int.quotientSpanNatEquivZMod p).symm.toRingHom)
      (Int.quotientSpanNatEquivZMod p).symm.injective p
  letI : CharP (𝓞 L ⧸ P) p :=
    charP_of_injective_algebraMap' (ℤ ⧸ 𝔭) p
  let ζbar : 𝓞 L ⧸ P := Ideal.Quotient.mk P (gaussSumLiftAdditiveRoot (p := p) L)
  have hpow : ζbar ^ p = 1 := by
    simpa [ζbar] using congrArg (Ideal.Quotient.mk P)
      ((gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L)).pow_eq_one)
  have hsubpow : (ζbar - 1) ^ p = 0 := by
    calc
      (ζbar - 1) ^ p = ζbar ^ p - 1 := by
        simpa using
          (sub_pow_char_of_commute p (Commute.one_right ζbar) :
            (ζbar - 1) ^ p = ζbar ^ p - 1 ^ p)
      _ = 0 := by simp [hpow]
  have hsub : ζbar - 1 = 0 := eq_zero_of_pow_eq_zero hsubpow
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [ζbar] using hsub)

lemma gaussSumLiftAdditiveRoot_pow_sub_one_sub_mul_mem_primeAboveP_sq
    {P : Ideal (𝓞 L)} (hP : P ∈ primesAboveP p L) (n : ℕ) :
    gaussSumLiftAdditiveRoot (p := p) L ^ n - 1 -
        (n : 𝓞 L) * (gaussSumLiftAdditiveRoot (p := p) L - 1) ∈
      P ^ 2 := by
  let ζ : 𝓞 L := gaussSumLiftAdditiveRoot (p := p) L
  have hζ : ζ - 1 ∈ P :=
    gaussSumLiftAdditiveRoot_sub_one_mem_primeAboveP (p := p) (L := L) hP
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      have hsquare : (ζ - 1) ^ 2 ∈ P ^ 2 := by
        simpa [pow_two] using Ideal.mul_mem_mul hζ hζ
      have hrewrite :
          ζ ^ (n + 1) - 1 - ((n + 1 : ℕ) : 𝓞 L) * (ζ - 1) =
            ζ * (ζ ^ n - 1 - (n : 𝓞 L) * (ζ - 1)) +
              (n : 𝓞 L) * (ζ - 1) ^ 2 := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring_nf
      rw [hrewrite]
      exact Ideal.add_mem (P ^ 2)
        (Ideal.mul_mem_left _ _ ihn)
        (Ideal.mul_mem_left _ _ hsquare)

lemma gaussSumLiftAdditiveRoot_sub_one_mem_normalizedBoundaryPrime :
    gaussSumLiftAdditiveRoot (p := p) L - 1 ∈
      normalizedBoundaryPrime (p := p) (L := L) :=
  gaussSumLiftAdditiveRoot_sub_one_mem_primeAboveP (p := p) (L := L)
    (normalizedBoundaryPrime_mem_primesAboveP p L)

lemma gaussSumLiftAdditiveRoot_pow_sub_one_sub_mul_mem_normalizedBoundaryPrime_sq
    (n : ℕ) :
    gaussSumLiftAdditiveRoot (p := p) L ^ n - 1 -
        (n : 𝓞 L) * (gaussSumLiftAdditiveRoot (p := p) L - 1) ∈
      normalizedBoundaryPrime (p := p) (L := L) ^ 2 :=
  gaussSumLiftAdditiveRoot_pow_sub_one_sub_mul_mem_primeAboveP_sq
    (p := p) (L := L) (normalizedBoundaryPrime_mem_primesAboveP p L) n

/-- The additive `p`-th root, repackaged as an algebraic integer in the
additive cyclotomic subfield. -/
noncomputable def gaussSumLiftAdditiveRootAdditiveSubfieldInteger :
    𝓞 (additiveSubfield (L := L) (p := p)) :=
  ⟨⟨(((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L)),
      IntermediateField.subset_adjoin ℚ
        ({(((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L))} : Set L)
        (by simp)⟩,
    (IntermediateField.coe_isIntegral_iff).mp
      (RingOfIntegers.isIntegral_coe
        (gaussSumLiftAdditiveRoot (p := p) L))⟩

lemma algebraMap_gaussSumLiftAdditiveRootAdditiveSubfieldInteger :
    algebraMap (𝓞 (additiveSubfield (L := L) (p := p))) (𝓞 L)
        (gaussSumLiftAdditiveRootAdditiveSubfieldInteger (p := p) (L := L)) =
      gaussSumLiftAdditiveRoot (p := p) L := by
  rfl

lemma gaussSumLiftAdditiveRootAdditiveSubfieldInteger_isPrimitiveRoot :
    IsPrimitiveRoot
      (gaussSumLiftAdditiveRootAdditiveSubfieldInteger (p := p) (L := L)) p :=
  IsPrimitiveRoot.of_map_of_injective
    (f := algebraMap (𝓞 (additiveSubfield (L := L) (p := p))) (𝓞 L))
    (by
      simpa [algebraMap_gaussSumLiftAdditiveRootAdditiveSubfieldInteger
        (p := p) (L := L)] using
        gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L))
    (FaithfulSMul.algebraMap_injective
      (𝓞 (additiveSubfield (L := L) (p := p))) (𝓞 L))

lemma additiveRootAdditiveSubfieldPrime_eq_additiveZetaPrime :
    Ideal.span
        ({gaussSumLiftAdditiveRootAdditiveSubfieldInteger (p := p) (L := L) - 1} :
          Set (𝓞 (additiveSubfield (L := L) (p := p)))) =
      additiveZetaPrime (L := L) (p := p) := by
  let ζF : additiveSubfield (L := L) (p := p) :=
    ⟨(((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L)),
      IntermediateField.subset_adjoin ℚ
        ({(((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L))} : Set L)
        (by simp)⟩
  have hζF : IsPrimitiveRoot ζF p :=
    IsPrimitiveRoot.of_map_of_injective
      (f := algebraMap (additiveSubfield (L := L) (p := p)) L)
      (by
        simpa [ζF] using
          (gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L)).map_of_injective
            NumberField.RingOfIntegers.coe_injective)
      (FaithfulSMul.algebraMap_injective (additiveSubfield (L := L) (p := p)) L)
  have hto :
      hζF.toInteger =
        gaussSumLiftAdditiveRootAdditiveSubfieldInteger (p := p) (L := L) := by
    ext
    rfl
  haveI : (additiveZetaPrime (L := L) (p := p)).IsPrime :=
    (additiveZetaPrime_mem_primesOver p L).1
  haveI : (additiveZetaPrime (L := L) (p := p)).LiesOver 𝔭 :=
    (additiveZetaPrime_mem_primesOver p L).2
  have hEq :
      additiveZetaPrime (L := L) (p := p) =
        Ideal.span ({hζF.toInteger - 1} :
          Set (𝓞 (additiveSubfield (L := L) (p := p)))) := by
    simpa [additiveZetaPrime] using
      (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
        (p := p)
        (K := additiveSubfield (L := L) (p := p))
        (hζ := hζF)
        (P := additiveZetaPrime (L := L) (p := p)))
  simpa [hto] using hEq.symm

lemma map_additiveZetaPrime_eq_span_additiveRoot_sub_one :
    Ideal.map
        (algebraMap (𝓞 (additiveSubfield (L := L) (p := p))) (𝓞 L))
        (additiveZetaPrime (L := L) (p := p)) =
      Ideal.span ({gaussSumLiftAdditiveRoot (p := p) L - 1} : Set (𝓞 L)) := by
  rw [← additiveRootAdditiveSubfieldPrime_eq_additiveZetaPrime (p := p) (L := L),
    Ideal.map_span, Set.image_singleton]
  simp [algebraMap_gaussSumLiftAdditiveRootAdditiveSubfieldInteger]

lemma normalizedBoundaryPrime_under_additiveSubfield :
    (normalizedBoundaryPrime (p := p) (L := L)).under
        (𝓞 (additiveSubfield (L := L) (p := p))) =
      additiveZetaPrime (L := L) (p := p) :=
  characterSidePrimeOrbit_under_additiveSubfield_eq_additiveZetaPrime
    (p := p) (L := L)
    (normalizedBoundaryPrime_mem_characterSidePrimeOrbit (p := p) (L := L))

lemma normalizedBoundaryPrime_ramificationIdx_over_additiveSubfield :
    Ideal.ramificationIdx
        (additiveZetaPrime (L := L) (p := p))
        (normalizedBoundaryPrime (p := p) (L := L)) = 1 := by
  let Padd := additiveZetaPrime (L := L) (p := p)
  have hPadd_mem :
      Padd ∈ Ideal.primesOver 𝔭 (𝓞 (additiveSubfield (L := L) (p := p))) :=
    additiveZetaPrime_mem_primesOver p L
  haveI : Padd.IsPrime := hPadd_mem.1
  haveI : Padd.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPadd_mem
  haveI : Padd.LiesOver 𝔭 := hPadd_mem.2
  have hm : ¬ p ∣ 1 :=
    Nat.Prime.not_dvd_one hp.out
  letI : IsGalois ℚ (additiveSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ))
      (K := ℚ) (L := additiveSubfield (L := L) (p := p))
  letI : IsGaloisGroup Gal(additiveSubfield (L := L) (p := p) / ℚ)
      ℤ (𝓞 (additiveSubfield (L := L) (p := p))) := inferInstance
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois (S := ({p * (p - 1)} : Set ℕ)) (K := ℚ) (L := L)
  letI : IsGaloisGroup Gal(L / ℚ) ℤ (𝓞 L) := inferInstance
  let GBC := characterSideFixingSubgroup (p := p) L
  letI : IsGaloisGroup ↥GBC (additiveSubfield (L := L) (p := p)) L := by
    change IsGaloisGroup ((additiveSubfield (L := L) (p := p)).fixingSubgroup)
      (additiveSubfield (L := L) (p := p)) L
    exact IsGaloisGroup.intermediateField
      (G := Gal(L / ℚ)) (K := ℚ) (L := L)
      (F := additiveSubfield (L := L) (p := p))
  letI : IsGaloisGroup ↥GBC
      (𝓞 (additiveSubfield (L := L) (p := p))) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (G := ↥GBC) (A := 𝓞 (additiveSubfield (L := L) (p := p))) (B := 𝓞 L)
      (K := additiveSubfield (L := L) (p := p)) (L := L)
  have hramAdd :
      Ideal.ramificationIdxIn 𝔭 (𝓞 (additiveSubfield (L := L) (p := p))) =
        p - 1 := by
    simpa using
      (IsCyclotomicExtension.Rat.ramificationIdxIn_eq
        (n := p) (K := additiveSubfield (L := L) (p := p)) (p := p)
        (k := 0) (m := 1) (by simp) hm)
  have hm_total : ¬ p ∣ p - 1 :=
    (hp.out.coprime_iff_not_dvd).mp (prime_coprime_pred (p := p))
  have hramTotal : Ideal.ramificationIdxIn 𝔭 (𝓞 L) = p - 1 := by
    simpa using
      (IsCyclotomicExtension.Rat.ramificationIdxIn_eq
        (n := p * (p - 1)) (K := L) (p := p) (k := 0) (m := p - 1) (by simp)
        hm_total)
  have hmul :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn
      (A := ℤ)
      (B := 𝓞 (additiveSubfield (L := L) (p := p)))
      (C := 𝓞 L)
      (p := 𝔭) (P := Padd)
      (G := Gal(additiveSubfield (L := L) (p := p) / ℚ))
      (GAC := Gal(L / ℚ)) (GBC := ↥GBC)
  rw [hramAdd, hramTotal] at hmul
  have hramIn :
      Ideal.ramificationIdxIn Padd (𝓞 L) = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.out.one_lt) (by simpa using hmul)
  haveI : (normalizedBoundaryPrime (p := p) (L := L)).LiesOver Padd := by
    rw [Ideal.liesOver_iff,
      normalizedBoundaryPrime_under_additiveSubfield (p := p) (L := L)]
  have hPadd_ne : Padd ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (show Padd.IsMaximal from inferInstance)
      (NumberField.RingOfIntegers.not_isField (additiveSubfield (L := L) (p := p)))
  rw [Ideal.ramificationIdx_eq_ramificationIdx' Padd _ hPadd_ne]
  exact (Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := Padd) (P := normalizedBoundaryPrime (p := p) (L := L)) (G := ↥GBC)).symm.trans
    hramIn

lemma normalizedBoundaryPrime_count_span_additiveRoot_sub_one :
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSumLiftAdditiveRoot (p := p) L - 1} : Set (𝓞 L)))).count
      (normalizedBoundaryPrime (p := p) (L := L)) = 1 := by
  let Padd := additiveZetaPrime (L := L) (p := p)
  let P := normalizedBoundaryPrime (p := p) (L := L)
  let IL : Ideal (𝓞 L) :=
    Ideal.span ({gaussSumLiftAdditiveRoot (p := p) L - 1} : Set (𝓞 L))
  have hPadd_mem :
      Padd ∈ Ideal.primesOver 𝔭 (𝓞 (additiveSubfield (L := L) (p := p))) :=
    additiveZetaPrime_mem_primesOver p L
  haveI : Padd.IsPrime := hPadd_mem.1
  haveI : Padd.LiesOver 𝔭 := hPadd_mem.2
  haveI : Padd.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPadd_mem
  have hP_mem : P ∈ primesAboveP p L :=
    normalizedBoundaryPrime_mem_primesAboveP p L
  haveI : P.IsPrime := ((mem_primesAboveP_iff (p := p) (L := L)).1 hP_mem).1
  haveI : P.LiesOver 𝔭 := ((mem_primesAboveP_iff (p := p) (L := L)).1 hP_mem).2
  haveI : P.LiesOver Padd := by
    rw [Ideal.liesOver_iff,
      normalizedBoundaryPrime_under_additiveSubfield (p := p) (L := L)]
  have hPadd_ne : Padd ≠ ⊥ :=
    primeAboveP_ne_bot (p := p) (L := additiveSubfield (L := L) (p := p)) (P := Padd)
  have hP_ne : P ≠ ⊥ :=
    primeAboveP_ne_bot (p := p) (L := L) (P := P)
  have hPadd_irr : Irreducible Padd :=
    (Ideal.prime_of_isPrime hPadd_ne inferInstance).irreducible
  have hP_irr : Irreducible P :=
    (Ideal.prime_of_isPrime hP_ne inferInstance).irreducible
  have hroot_ne :
      gaussSumLiftAdditiveRoot (p := p) L - 1 ≠ 0 :=
    sub_ne_zero.mpr
      ((gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L)).ne_one hp.out.one_lt)
  have hIL_ne : IL ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hroot_ne
  have hmap :
      Ideal.map
          (algebraMap (𝓞 (additiveSubfield (L := L) (p := p))) (𝓞 L))
          Padd = IL := by
    simpa [Padd, IL] using
      map_additiveZetaPrime_eq_span_additiveRoot_sub_one (p := p) (L := L)
  have hemul :=
    Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
      (R := 𝓞 (additiveSubfield (L := L) (p := p))) (S := 𝓞 L)
      (v := Padd) (w := P) (I := Padd)
      hPadd_ne hPadd_irr hP_irr hP_ne
  have hPadd_count :
      (UniqueFactorizationMonoid.normalizedFactors Padd).count Padd = 1 := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hPadd_irr, normalize_eq Padd]
    simp
  rw [hmap,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hP_irr hIL_ne,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPadd_irr hPadd_ne,
    normalize_eq P,
    normalize_eq Padd,
    normalizedBoundaryPrime_ramificationIdx_over_additiveSubfield (p := p) (L := L)] at hemul
  simpa [P, Padd, IL, hPadd_count] using hemul

lemma gaussSumLiftAdditiveRoot_sub_one_not_mem_normalizedBoundaryPrime_sq :
    gaussSumLiftAdditiveRoot (p := p) L - 1 ∉
      normalizedBoundaryPrime (p := p) (L := L) ^ 2 := by
  intro hmem
  let P := normalizedBoundaryPrime (p := p) (L := L)
  let I : Ideal (𝓞 L) :=
    Ideal.span ({gaussSumLiftAdditiveRoot (p := p) L - 1} : Set (𝓞 L))
  have hI_le : I ≤ P ^ 2 := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hroot_ne :
      gaussSumLiftAdditiveRoot (p := p) L - 1 ≠ 0 :=
    sub_ne_zero.mpr
      ((gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L)).ne_one hp.out.one_lt)
  have hI_ne : I ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hroot_ne
  have hP_mem : P ∈ primesAboveP p L :=
    normalizedBoundaryPrime_mem_primesAboveP p L
  haveI : P.IsPrime := ((mem_primesAboveP_iff (p := p) (L := L)).1 hP_mem).1
  have hP_ne : P ≠ ⊥ := by
    haveI : P.LiesOver 𝔭 := ((mem_primesAboveP_iff (p := p) (L := L)).1 hP_mem).2
    exact primeAboveP_ne_bot (p := p) (L := L) (P := P)
  have hP_irr : Irreducible P :=
    (Ideal.prime_of_isPrime hP_ne inferInstance).irreducible
  have hcount_pow :
      (UniqueFactorizationMonoid.normalizedFactors (P ^ 2)).count P = 2 := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hP_irr,
      normalize_eq P]
    simp
  have hcount_le := Ideal.count_le_of_ideal_ge hI_le hI_ne P
  have hcount_I :
      (UniqueFactorizationMonoid.normalizedFactors I).count P = 1 := by
    simpa [I, P] using
      normalizedBoundaryPrime_count_span_additiveRoot_sub_one (p := p) (L := L)
  omega

end Assembly

end BernoulliRegular
