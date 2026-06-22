module

public import BernoulliRegular.GaussSum.PrimeFactorization.Assembly

/-!
# Jacobi-sum lifts and additive exponent relations

Let

`L = ℚ(ζ_{p(p-1)})`.

This file isolates the Jacobi-sum lift used in the Stickelberger prime
factorization argument and the additive relations it induces on the
distinguished-prime exponent along generator powers.
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

@[simp] lemma distinguishedPrimeExponent_one :
    distinguishedPrimeExponent (p := p) (L := L) (1 : DirichletCharacter ℂ p) = 0 := by
  unfold distinguishedPrimeExponent gaussSumIdeal
  have hτ :
      gaussSumIntegers p L (1 : DirichletCharacter ℂ p) = (-1 : 𝓞 L) := by
    apply Subtype.ext
    change gaussSumLift p L (1 : DirichletCharacter ℂ p) = (-1 : L)
    apply (stickelbergerEmbedding p L).injective
    simp [stickelbergerEmbedding_gaussSumLift, gaussSum_one_stdAddChar]
  rw [hτ]
  have htop : Ideal.span ({(-1 : 𝓞 L)} : Set (𝓞 L)) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr isUnit_one.neg
  rw [htop, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
  simp

lemma stickelbergerComplexCharacterGenerator_pow_ne_one_of_ne_zero
    {j : Fin (p - 1)} (hj : j ≠ 0) :
    stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ) ≠ 1 := by
  intro h
  have hpow :
      stickelbergerComplexCharacterRoot (p := p) ^ (j : ℕ) = 1 := by
    have hEval := congrArg
      (fun χ : DirichletCharacter ℂ p =>
        χ (((characterUnitGenerator (p := p)) : (ZMod p)ˣ) : ZMod p)) h
    simpa [MulChar.pow_apply_coe,
      stickelbergerComplexCharacterGenerator_apply_characterUnitGenerator] using hEval
  have hjpos : 0 < (j : ℕ) := Fin.pos_iff_ne_zero.mpr hj
  exact
    (stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).pow_ne_one_of_pos_of_lt
      hjpos.ne' j.is_lt hpow

/-- The integral Stickelberger-field lift of the Jacobi sum
`jacobiSum χ ψ`. -/
noncomputable def jacobiSumLift
    (χ ψ : DirichletCharacter ℂ p) : 𝓞 L :=
  ∑ x : ZMod p,
    if hx0 : x = 0 then 0 else
      if hx1 : x = 1 then 0 else
        gaussSumLiftCharacterValue (p := p) (L := L) χ (Units.mk0 x hx0) *
          gaussSumLiftCharacterValue (p := p) (L := L) ψ
            (Units.mk0 (1 - x) (by
              apply sub_ne_zero.mpr
              simpa [eq_comm] using hx1))

lemma stickelbergerEmbedding_jacobiSumLift
    (χ ψ : DirichletCharacter ℂ p) :
    stickelbergerEmbedding p L (((jacobiSumLift (p := p) (L := L) χ ψ : 𝓞 L) : L)) =
      jacobiSum χ ψ := by
  let term : ZMod p → 𝓞 L := fun x =>
    if hx0 : x = 0 then 0 else
      if hx1 : x = 1 then 0 else
        gaussSumLiftCharacterValue (p := p) (L := L) χ (Units.mk0 x hx0) *
          gaussSumLiftCharacterValue (p := p) (L := L) ψ
            (Units.mk0 (1 - x) (by
              apply sub_ne_zero.mpr
              simpa [eq_comm] using hx1))
  unfold jacobiSumLift jacobiSum
  let f : 𝓞 L →+* ℂ :=
    (stickelbergerEmbedding p L).toRingHom.comp (algebraMap (𝓞 L) L)
  change f (∑ x : ZMod p, term x) =
    ∑ x : ZMod p, χ x * ψ (1 - x)
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    simpa [term] using
      (MulChar.map_nonunit χ (show ¬ IsUnit (0 : ZMod p) by simp)).symm
  · by_cases hx1 : x = 1
    · subst hx1
      simpa [term, hx0] using
        (MulChar.map_nonunit ψ (show ¬ IsUnit (0 : ZMod p) by simp)).symm
    · simp [term, hx0, hx1, f, stickelbergerEmbedding_gaussSumLiftCharacterValue]

lemma gaussSumLiftCharacterValue_mem_characterSubfield
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    (((gaussSumLiftCharacterValue (p := p) (L := L) χ a : 𝓞 L) : L)) ∈
      characterSubfield (L := L) (p := p) := by
  have hroot :
      (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L)) ∈
        characterSubfield (L := L) (p := p) :=
    IntermediateField.subset_adjoin ℚ
      ({(((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L))} : Set L)
      (by simp)
  unfold gaussSumLiftCharacterValue
  exact pow_mem hroot
    ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
      (characterUnitGeneratorExponent (p := p) a : ℕ))

lemma jacobiSumLift_mem_characterSubfield
    (χ ψ : DirichletCharacter ℂ p) :
    (((jacobiSumLift (p := p) (L := L) χ ψ : 𝓞 L) : L)) ∈
      characterSubfield (L := L) (p := p) := by
  let term : ZMod p → L := fun x =>
    algebraMap (𝓞 L) L
      (if hx0 : x = 0 then 0 else
        if hx1 : x = 1 then 0 else
          gaussSumLiftCharacterValue (p := p) (L := L) χ (Units.mk0 x hx0) *
            gaussSumLiftCharacterValue (p := p) (L := L) ψ
              (Units.mk0 (1 - x) (by
                apply sub_ne_zero.mpr
                simpa [eq_comm] using hx1)))
  unfold jacobiSumLift
  have hsum : ∑ x : ZMod p, term x ∈
      (characterSubfield (L := L) (p := p)).toSubring :=
    sum_mem fun x hx => by
      by_cases hx0 : x = 0
      · simp [term, hx0]
      · by_cases hx1 : x = 1
        · simp [term, hx1]
        · simpa [term, hx0, hx1] using
            Subring.mul_mem
              ((characterSubfield (L := L) (p := p)).toSubring)
              (gaussSumLiftCharacterValue_mem_characterSubfield
                (p := p) (L := L) χ (Units.mk0 x hx0))
              (gaussSumLiftCharacterValue_mem_characterSubfield
                (p := p) (L := L) ψ
                (Units.mk0 (1 - x) (by
                  apply sub_ne_zero.mpr
                  simpa [eq_comm] using hx1)))
  have hsum' : (∑ x : ZMod p, term x) ∈ characterSubfield (L := L) (p := p) := hsum
  simpa [term] using hsum'

/-- The Jacobi-sum lift, repackaged as an algebraic integer in the character
subfield. -/
noncomputable def jacobiSumCharacterSubfieldInteger
    (χ ψ : DirichletCharacter ℂ p) :
    𝓞 (characterSubfield (L := L) (p := p)) :=
  ⟨⟨(((jacobiSumLift (p := p) (L := L) χ ψ : 𝓞 L) : L)),
      jacobiSumLift_mem_characterSubfield (p := p) (L := L) χ ψ⟩,
    (IntermediateField.coe_isIntegral_iff).mp
      (RingOfIntegers.isIntegral_coe
        (jacobiSumLift (p := p) (L := L) χ ψ))⟩

lemma algebraMap_jacobiSumCharacterSubfieldInteger
    (χ ψ : DirichletCharacter ℂ p) :
    algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L)
        (jacobiSumCharacterSubfieldInteger (p := p) (L := L) χ ψ) =
      jacobiSumLift (p := p) (L := L) χ ψ := by
  rfl

lemma gaussSumIntegers_mul_eq_jacobiSumLift_mul_gaussSumIntegers
    {χ ψ : DirichletCharacter ℂ p} (hχψ : χ * ψ ≠ 1) :
    gaussSumIntegers p L χ * gaussSumIntegers p L ψ =
      jacobiSumLift (p := p) (L := L) χ ψ *
        gaussSumIntegers p L (χ * ψ) := by
  apply Subtype.ext
  change gaussSumLift p L χ * gaussSumLift p L ψ =
    (((jacobiSumLift (p := p) (L := L) χ ψ : 𝓞 L) : L)) *
      gaussSumLift p L (χ * ψ)
  apply (stickelbergerEmbedding p L).injective
  rw [map_mul, map_mul]
  simpa [stickelbergerEmbedding_gaussSumLift,
    stickelbergerEmbedding_jacobiSumLift] using
    (gaussSum_mul_gaussSum_eq_jacobiSum_mul_gaussSum_stdAddChar
      (p := p) (χ := χ) (φ := ψ) hχψ)

lemma gaussSumIdeal_mul_eq_jacobiSumLift_mul_gaussSumIdeal
    {χ ψ : DirichletCharacter ℂ p} (hχψ : χ * ψ ≠ 1) :
    gaussSumIdeal (p := p) (L := L) χ *
        gaussSumIdeal (p := p) (L := L) ψ =
      Ideal.span ({jacobiSumLift (p := p) (L := L) χ ψ} : Set (𝓞 L)) *
        gaussSumIdeal (p := p) (L := L) (χ * ψ) := by
  unfold gaussSumIdeal
  rw [Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun x : 𝓞 L => Ideal.span ({x} : Set (𝓞 L)))
    (gaussSumIntegers_mul_eq_jacobiSumLift_mul_gaussSumIntegers
      (p := p) (L := L) hχψ)

lemma jacobiSumLift_ne_zero
    {χ ψ : DirichletCharacter ℂ p} (hχψ : χ * ψ ≠ 1) :
    jacobiSumLift (p := p) (L := L) χ ψ ≠ 0 := by
  intro hzero
  have hcomp :
      stickelbergerEmbedding p L
          (((jacobiSumLift (p := p) (L := L) χ ψ : 𝓞 L) : L)) = 0 := by
    simp [hzero]
  rw [stickelbergerEmbedding_jacobiSumLift] at hcomp
  exact (jacobiSum_ne_zero_stdAddChar (p := p) hχψ) hcomp

lemma distinguishedPrimeAboveP_ramificationIdx_over_characterSubfield :
    Ideal.ramificationIdx
        (distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L))
        (distinguishedPrimeAboveP p L) = p - 1 := by
  let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  haveI : Pchar.IsPrime :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).1
  haveI : Pchar.IsMaximal := Ideal.isMaximal_of_mem_primesOver
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L))
  haveI : Pchar.LiesOver 𝔭 :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).2
  have hm : ¬ p ∣ p - 1 :=
    (hp.out.coprime_iff_not_dvd).mp (prime_coprime_pred (p := p))
  letI : IsGalois ℚ (characterSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p - 1} : Set ℕ))
      (K := ℚ) (L := characterSubfield (L := L) (p := p))
  letI : IsGaloisGroup Gal(characterSubfield (L := L) (p := p) / ℚ)
      ℤ (𝓞 (characterSubfield (L := L) (p := p))) := inferInstance
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois (S := ({p * (p - 1)} : Set ℕ)) (K := ℚ) (L := L)
  letI : IsGaloisGroup Gal(L / ℚ) ℤ (𝓞 L) := inferInstance
  let GBC := characterSubfieldFixingSubgroup (p := p) L
  letI : IsGaloisGroup ↥GBC (characterSubfield (L := L) (p := p)) L := by
    change IsGaloisGroup ((characterSubfield (L := L) (p := p)).fixingSubgroup)
      (characterSubfield (L := L) (p := p)) L
    exact IsGaloisGroup.intermediateField
      (G := Gal(L / ℚ)) (K := ℚ) (L := L)
      (F := characterSubfield (L := L) (p := p))
  letI : IsGaloisGroup ↥GBC
      (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (G := ↥GBC) (A := 𝓞 (characterSubfield (L := L) (p := p))) (B := 𝓞 L)
      (K := characterSubfield (L := L) (p := p)) (L := L)
  have hramChar :
      Ideal.ramificationIdxIn 𝔭 (𝓞 (characterSubfield (L := L) (p := p))) = 1 := by
    simpa using
      (IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
        (p := p) (K := characterSubfield (L := L) (p := p)) hm)
  have hramTotal : Ideal.ramificationIdxIn 𝔭 (𝓞 L) = p - 1 := by
    simpa using
      (IsCyclotomicExtension.Rat.ramificationIdxIn_eq
        (n := p * (p - 1)) (K := L) (p := p) (k := 0) (m := p - 1) (by simp) hm)
  have hmul :
      Ideal.ramificationIdxIn Pchar (𝓞 L) = p - 1 := by
    have h := Ideal.ramificationIdxIn_mul_ramificationIdxIn
      (A := ℤ)
      (B := 𝓞 (characterSubfield (L := L) (p := p)))
      (C := 𝓞 L)
      (p := 𝔭) (P := Pchar)
      (G := Gal(characterSubfield (L := L) (p := p) / ℚ))
      (GAC := Gal(L / ℚ)) (GBC := ↥GBC)
    rwa [hramChar, one_mul, hramTotal] at h
  haveI : (distinguishedPrimeAboveP p L).LiesOver Pchar := by
    rw [Ideal.liesOver_iff]
  have hPchar_ne : Pchar ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField inferInstance
      (NumberField.RingOfIntegers.not_isField (characterSubfield (L := L) (p := p)))
  rw [Ideal.ramificationIdx_eq_ramificationIdx' Pchar _ hPchar_ne]
  exact (Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := Pchar) (P := distinguishedPrimeAboveP p L) (G := ↥GBC)).symm.trans hmul

lemma jacobiSumLift_distinguishedPrimeExponent_dvd_pred
    {χ ψ : DirichletCharacter ℂ p} (hχψ : χ * ψ ≠ 1) :
    p - 1 ∣
      (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({jacobiSumLift (p := p) (L := L) χ ψ} : Set (𝓞 L)))).count
        (distinguishedPrimeAboveP p L) := by
  let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  let xchar := jacobiSumCharacterSubfieldInteger (p := p) (L := L) χ ψ
  have hxchar_ne : xchar ≠ 0 := by
    intro hx
    apply jacobiSumLift_ne_zero (p := p) (L := L) hχψ
    have hmap := congrArg
      (algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L)) hx
    simpa [xchar, algebraMap_jacobiSumCharacterSubfieldInteger] using hmap
  have hIchar_ne :
      Ideal.span ({xchar} : Set (𝓞 (characterSubfield (L := L) (p := p)))) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hxchar_ne
  have hJ_ne :
      Ideal.span ({jacobiSumLift (p := p) (L := L) χ ψ} : Set (𝓞 L)) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr
      (jacobiSumLift_ne_zero (p := p) (L := L) hχψ)
  have hmap :
      Ideal.map
          (algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L))
          (Ideal.span ({xchar} : Set (𝓞 (characterSubfield (L := L) (p := p))))) =
        Ideal.span ({jacobiSumLift (p := p) (L := L) χ ψ} : Set (𝓞 L)) := by
    rw [Ideal.map_span, Set.image_singleton,
      algebraMap_jacobiSumCharacterSubfieldInteger]
  haveI : Pchar.IsPrime :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).1
  haveI : Pchar.LiesOver 𝔭 :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).2
  haveI : (distinguishedPrimeAboveP p L).LiesOver Pchar := by
    rw [Ideal.liesOver_iff]
  have hPchar_irr : Irreducible Pchar :=
    (Ideal.prime_of_isPrime
      (primeAboveP_ne_bot (p := p) (L := characterSubfield (L := L) (p := p)) (P := Pchar))
      inferInstance).irreducible
  have hP0_irr : Irreducible (distinguishedPrimeAboveP p L) :=
    (Ideal.prime_of_isPrime
      (primeAboveP_ne_bot (p := p) (L := L) (P := distinguishedPrimeAboveP p L))
      inferInstance).irreducible
  have hemul :=
    Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
      (R := 𝓞 (characterSubfield (L := L) (p := p))) (S := 𝓞 L)
      (v := Pchar) (w := distinguishedPrimeAboveP p L)
      (I := Ideal.span ({xchar} : Set (𝓞 (characterSubfield (L := L) (p := p)))))
      hIchar_ne hPchar_irr hP0_irr
      (primeAboveP_ne_bot (p := p) (L := L) (P := distinguishedPrimeAboveP p L))
  rw [hmap,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hP0_irr hJ_ne,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPchar_irr hIchar_ne,
    normalize_eq (distinguishedPrimeAboveP p L),
    normalize_eq Pchar,
    distinguishedPrimeAboveP_ramificationIdx_over_characterSubfield (p := p) (L := L)] at hemul
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({xchar} : Set (𝓞 (characterSubfield (L := L) (p := p)))))).count Pchar, ?_⟩
  exact_mod_cast hemul

end Assembly

end BernoulliRegular
