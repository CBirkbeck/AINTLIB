module

public import BernoulliRegular.GaussSum.PrimeFactorization.GaloisAction.Basic

/-!
# Character subfield primes in the Stickelberger field
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped Pointwise

namespace BernoulliRegular

section GaloisAction

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

local notation "𝔭" => (Ideal.span ({(p : ℤ)} : Set ℤ))
local instance : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩

/-- The `(p - 1)`-cyclotomic subfield inside the Stickelberger field. -/
noncomputable abbrev characterSubfield : IntermediateField ℚ L :=
  IntermediateField.adjoin ℚ {(((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L))}

instance characterSubfield_isCyclotomic :
    IsCyclotomicExtension {p - 1} ℚ (characterSubfield (L := L) (p := p)) := by
  let ζ : L := ((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L)
  have hζ : IsPrimitiveRoot ζ (p - 1) := by
    simpa [ζ] using
      (gaussSumLiftCharacterRoot_isPrimitiveRoot (p := p) (L := L)).map_of_injective
        NumberField.RingOfIntegers.coe_injective
  exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    (K := ℚ) (L := L) (n := p - 1) (F := characterSubfield (L := L) (p := p)) hζ).2 rfl

/-- The distinguished prime of the `(p - 1)`-cyclotomic subfield obtained by
contracting `distinguishedPrimeAboveP`. -/
noncomputable abbrev distinguishedPrimeAboveP_under_characterSubfield :
    Ideal (𝓞 (characterSubfield (L := L) (p := p))) :=
  (distinguishedPrimeAboveP p L).under (𝓞 (characterSubfield (L := L) (p := p)))

lemma distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver :
    distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L) ∈
      Ideal.primesOver 𝔭 (𝓞 (characterSubfield (L := L) (p := p))) := by
  let P : Ideal (𝓞 (characterSubfield (L := L) (p := p))) :=
    distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  haveI : P.IsPrime := inferInstance
  haveI : P.LiesOver 𝔭 := by
    dsimp [P, distinguishedPrimeAboveP_under_characterSubfield]
    infer_instance
  exact ⟨inferInstance, inferInstance⟩

/-- The lifted character root, repackaged as an algebraic integer in the
`(p - 1)`-cyclotomic character subfield. -/
noncomputable def gaussSumLiftCharacterRootCharacterSubfieldInteger :
    𝓞 (characterSubfield (L := L) (p := p)) :=
  ⟨⟨(((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L)),
      IntermediateField.subset_adjoin ℚ
        ({(((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L))} : Set L)
        (by simp)⟩,
    (IntermediateField.coe_isIntegral_iff).mp
      (RingOfIntegers.isIntegral_coe
        (gaussSumLiftCharacterRoot (p := p) L))⟩

lemma algebraMap_gaussSumLiftCharacterRootCharacterSubfieldInteger :
    algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L)
        (gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L)) =
      gaussSumLiftCharacterRoot (p := p) L := by
  rfl

lemma gaussSumLiftCharacterRootCharacterSubfieldInteger_isPrimitiveRoot :
    IsPrimitiveRoot
      (gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L))
      (p - 1) :=
  IsPrimitiveRoot.of_map_of_injective
    (f := algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L))
    (by
      simpa [algebraMap_gaussSumLiftCharacterRootCharacterSubfieldInteger
        (p := p) (L := L)] using
        gaussSumLiftCharacterRoot_isPrimitiveRoot (p := p) (L := L))
    (FaithfulSMul.algebraMap_injective
      (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L))

/-- The character-side coefficient of `gaussSumLiftRootSum`, now viewed inside
the ring of integers of the character subfield. -/
noncomputable def gaussSumLiftCharacterValueCharacterSubfieldInteger
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    𝓞 (characterSubfield (L := L) (p := p)) :=
  gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L) ^
    ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
      (characterUnitGeneratorExponent (p := p) a : ℕ))

lemma algebraMap_gaussSumLiftCharacterValueCharacterSubfieldInteger
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L)
        (gaussSumLiftCharacterValueCharacterSubfieldInteger
          (p := p) (L := L) χ a) =
      gaussSumLiftCharacterValue (p := p) (L := L) χ a := by
  simp [gaussSumLiftCharacterValueCharacterSubfieldInteger, gaussSumLiftCharacterValue,
    algebraMap_gaussSumLiftCharacterRootCharacterSubfieldInteger, map_pow]

section CharacterSubfieldPrime

variable {Pchar : Ideal (𝓞 (characterSubfield (L := L) (p := p)))}
  [Pchar.IsPrime] [Pchar.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]

lemma characterSubfieldPrime_inertiaDeg_eq_one :
    Ideal.inertiaDeg 𝔭 Pchar = 1 := by
  have hm : ¬ p ∣ p - 1 :=
    (hp.out.coprime_iff_not_dvd).mp (prime_coprime_pred (p := p))
  have hp_cast : (p : ZMod (p - 1)) = 1 := by
    have hmod : 1 ≡ p [MOD p - 1] := by
      rw [Nat.modEq_iff_dvd' hp.out.one_le]
    simpa using (ZMod.natCast_eq_natCast_iff p 1 (p - 1)).2 hmod.symm
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
    (p := p)
    (m := p - 1)
    (K := characterSubfield (L := L) (p := p))
    (P := Pchar)
    hm]
  simp [hp_cast]

lemma characterSubfieldPrime_absNorm_eq_p :
    Ideal.absNorm Pchar = p := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp.out,
    characterSubfieldPrime_inertiaDeg_eq_one (p := p) (L := L) (Pchar := Pchar),
    pow_one]

/-- Any prime of the character subfield above `(p)` has residue degree `1`. -/
lemma characterSubfieldPrime_quotient_finrank_eq_one :
    Module.finrank (ℤ ⧸ 𝔭)
      (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar) = 1 := by
  letI : (𝔭 : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  letI : Field (ℤ ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  rw [← Ideal.inertiaDeg_algebraMap (R := ℤ)
    (S := 𝓞 (characterSubfield (L := L) (p := p))) (p := 𝔭) (P := Pchar),
    characterSubfieldPrime_inertiaDeg_eq_one (p := p) (L := L) (Pchar := Pchar)]

/-- The canonical residue-field map from `ℤ/(p)` to the quotient by a
character-side prime is bijective. -/
lemma characterSubfieldPrime_quotientAlgebraMap_bijective :
    Function.Bijective
      (algebraMap (ℤ ⧸ 𝔭)
        (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar)) := by
  have hP_over : Pchar ∈ Ideal.primesOver (Ideal.span ({(p : ℤ)} : Set ℤ))
      (𝓞 (characterSubfield (L := L) (p := p))) := ⟨inferInstance, inferInstance⟩
  letI : Pchar.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP_over
  letI : Field (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar) := Ideal.Quotient.field Pchar
  letI : Fintype (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar) := Fintype.ofFinite _
  letI : (𝔭 : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  letI : Field (ℤ ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have hsurj_linear :
      Function.Surjective
        (Algebra.linearMap (ℤ ⧸ 𝔭)
          (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar)) :=
    surjective_of_nonzero_of_finrank_eq_one
      (K := ℤ ⧸ 𝔭) (A := ℤ ⧸ 𝔭) (V := ℤ ⧸ 𝔭)
      (W := 𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar)
      (characterSubfieldPrime_quotient_finrank_eq_one
        (p := p) (L := L) (Pchar := Pchar))
      (f := Algebra.linearMap (ℤ ⧸ 𝔭)
        (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar))
      (by
        intro hzero
        have hone := congrArg
          (fun f : (ℤ ⧸ 𝔭) →ₗ[ℤ ⧸ 𝔭]
              (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar) => f 1) hzero
        simp at hone)
  have hbij_linear :
      Function.Bijective
        (Algebra.linearMap (ℤ ⧸ 𝔭)
          (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar)) := by
    refine ⟨?_, hsurj_linear⟩
    intro x y hxy
    exact FaithfulSMul.algebraMap_injective
      (ℤ ⧸ 𝔭) (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar)
      (by simpa [Algebra.linearMap_apply] using hxy)
  exact bijective_algebraMap_of_linearMap
    (b := Algebra.linearMap (ℤ ⧸ 𝔭)
      (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar))
    hbij_linear

/-- The quotient by a character-side prime is canonically identified with
`ℤ/(p)` via the residue algebra map. -/
noncomputable def characterSubfieldPrimeQuotientEquivIntQuotient :
    (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar) ≃ₐ[ℤ ⧸ 𝔭] (ℤ ⧸ 𝔭) :=
  (AlgEquiv.ofBijective
      (Algebra.ofId (ℤ ⧸ 𝔭)
        (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar))
      (characterSubfieldPrime_quotientAlgebraMap_bijective
        (p := p) (L := L) (Pchar := Pchar))).symm

/-- Any prime of the character subfield above `(p)` has residue field `𝔽_p`. -/
noncomputable def characterSubfieldPrimeQuotientEquivZMod :
    (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar) ≃+* ZMod p :=
  (characterSubfieldPrimeQuotientEquivIntQuotient
    (p := p) (L := L) (Pchar := Pchar)).toRingEquiv.trans
    (Int.quotientSpanNatEquivZMod p)

lemma quotient_mk_gaussSumLiftCharacterRootCharacterSubfieldInteger_isPrimitiveRoot :
    IsPrimitiveRoot
      (Ideal.Quotient.mk Pchar
        (gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L)))
      (p - 1) := by
  have hne : Ideal.absNorm Pchar ≠ 1 := by
    rw [characterSubfieldPrime_absNorm_eq_p (p := p) (L := L) (Pchar := Pchar)]
    exact hp.out.ne_one
  have hcoprime : (Ideal.absNorm Pchar).Coprime (p - 1) := by
    rw [characterSubfieldPrime_absNorm_eq_p (p := p) (L := L) (Pchar := Pchar)]
    exact prime_coprime_pred (p := p)
  exact (gaussSumLiftCharacterRootCharacterSubfieldInteger_isPrimitiveRoot
    (p := p) (L := L)).idealQuotient_mk hne hcoprime

/-- The prime-dependent residue of the lifted character root, identified with a
primitive root in `ZMod p`. -/
noncomputable def characterSubfieldPrimeGenerator : ZMod p :=
  characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L) (Pchar := Pchar)
    (Ideal.Quotient.mk Pchar
      (gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L)))

lemma characterSubfieldPrimeGenerator_isPrimitiveRoot :
    IsPrimitiveRoot
      (characterSubfieldPrimeGenerator (p := p) (L := L) (Pchar := Pchar))
      (p - 1) := by
  unfold characterSubfieldPrimeGenerator
  exact
    (quotient_mk_gaussSumLiftCharacterRootCharacterSubfieldInteger_isPrimitiveRoot
      (p := p) (L := L) (Pchar := Pchar)).map_of_injective
        (characterSubfieldPrimeQuotientEquivZMod
          (p := p) (L := L) (Pchar := Pchar)).injective

lemma characterSubfieldPrime_quotient_gaussSumLiftCharacterValue
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L) (Pchar := Pchar)
        (Ideal.Quotient.mk Pchar
          (gaussSumLiftCharacterValueCharacterSubfieldInteger
            (p := p) (L := L) χ a)) =
      characterSubfieldPrimeGenerator (p := p) (L := L) (Pchar := Pchar) ^
        ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
          (characterUnitGeneratorExponent (p := p) a : ℕ)) := by
  simp [gaussSumLiftCharacterValueCharacterSubfieldInteger, characterSubfieldPrimeGenerator,
    map_pow]

/-- The primitive-root residue generator attached to a character-side prime,
packaged as a unit of `𝔽_pˣ`. -/
noncomputable def characterSubfieldPrimeUnitGenerator : (ZMod p)ˣ :=
  ((characterSubfieldPrimeGenerator_isPrimitiveRoot
      (p := p) (L := L) (Pchar := Pchar)).isUnit
    (Nat.sub_ne_zero_of_lt hp.out.one_lt)).unit

@[simp]
lemma coe_characterSubfieldPrimeUnitGenerator :
    ((characterSubfieldPrimeUnitGenerator
        (p := p) (L := L) (Pchar := Pchar) : (ZMod p)ˣ) : ZMod p) =
      characterSubfieldPrimeGenerator (p := p) (L := L) (Pchar := Pchar) := by
  simp [characterSubfieldPrimeUnitGenerator]

lemma characterSubfieldPrimeUnitGenerator_isPrimitiveRoot :
    IsPrimitiveRoot
      (characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Pchar))
      (p - 1) := by
  simpa [characterSubfieldPrimeUnitGenerator] using
    IsPrimitiveRoot.isUnit_unit
      (Nat.sub_ne_zero_of_lt hp.out.one_lt)
      (characterSubfieldPrimeGenerator_isPrimitiveRoot
        (p := p) (L := L) (Pchar := Pchar))

theorem orderOf_characterSubfieldPrimeUnitGenerator :
    orderOf (characterSubfieldPrimeUnitGenerator
      (p := p) (L := L) (Pchar := Pchar)) = p - 1 := by
  simpa using
    (characterSubfieldPrimeUnitGenerator_isPrimitiveRoot
      (p := p) (L := L) (Pchar := Pchar)).eq_orderOf.symm

theorem characterSubfieldPrimeUnitGenerator_zpowers (u : (ZMod p)ˣ) :
    u ∈ Subgroup.zpowers
      (characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Pchar)) := by
  obtain ⟨n, _, hn⟩ :=
    (characterSubfieldPrimeGenerator_isPrimitiveRoot
      (p := p) (L := L) (Pchar := Pchar)).eq_pow_of_pow_eq_one (by
        exact ZMod.pow_card_sub_one_eq_one (Units.ne_zero u))
  refine ⟨n, ?_⟩
  apply Units.ext
  simpa [zpow_natCast, coe_characterSubfieldPrimeUnitGenerator,
    Units.val_pow_eq_pow_val] using hn

end CharacterSubfieldPrime

section CharacterSubfieldPrimeTransport

variable {Pchar Qchar : Ideal (𝓞 (characterSubfield (L := L) (p := p)))}
  [Pchar.IsPrime] [Pchar.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
  [Qchar.IsPrime] [Qchar.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]

lemma characterSubfieldPrimeQuotientEquivIntQuotient_algEquivOfEqMap_apply
    (σ : Gal(characterSubfield (L := L) (p := p)/ℚ))
    (hQ :
      Qchar =
        Pchar.map
          (MulSemiringAction.toAlgEquiv
            ℤ (𝓞 (characterSubfield (L := L) (p := p))) σ))
    (x : 𝓞 (characterSubfield (L := L) (p := p))) :
    characterSubfieldPrimeQuotientEquivIntQuotient
        (p := p) (L := L) (Pchar := Qchar)
        (Ideal.Quotient.algEquivOfEqMap
          (A := ℤ)
          (B := 𝓞 (characterSubfield (L := L) (p := p)))
          (C := 𝓞 (characterSubfield (L := L) (p := p)))
          (p := 𝔭)
          (σ := MulSemiringAction.toAlgEquiv
            ℤ (𝓞 (characterSubfield (L := L) (p := p))) σ)
          hQ
          x) =
      characterSubfieldPrimeQuotientEquivIntQuotient
        (p := p) (L := L) (Pchar := Pchar)
        (Ideal.Quotient.mk Pchar x) := by
  have hcomp :
      (characterSubfieldPrimeQuotientEquivIntQuotient
          (p := p) (L := L) (Pchar := Qchar)).toAlgHom.comp
        (Ideal.Quotient.algEquivOfEqMap
          (A := ℤ)
          (B := 𝓞 (characterSubfield (L := L) (p := p)))
          (C := 𝓞 (characterSubfield (L := L) (p := p)))
          (p := 𝔭)
          (σ := MulSemiringAction.toAlgEquiv
            ℤ (𝓞 (characterSubfield (L := L) (p := p))) σ)
          hQ).toAlgHom =
        (characterSubfieldPrimeQuotientEquivIntQuotient
          (p := p) (L := L) (Pchar := Pchar)).toAlgHom := by
    ext y
    obtain ⟨a, rfl⟩ :=
      (characterSubfieldPrime_quotientAlgebraMap_bijective
        (p := p) (L := L) (Pchar := Pchar)).2 y
    simp [characterSubfieldPrimeQuotientEquivIntQuotient]
  simpa using congrArg
    (fun f :
      (𝓞 (characterSubfield (L := L) (p := p)) ⧸ Pchar) →ₐ[ℤ ⧸ 𝔭] (ℤ ⧸ 𝔭) =>
        f (Ideal.Quotient.mk Pchar x))
    hcomp

end CharacterSubfieldPrimeTransport

@[simp]
lemma coe_gaussSumLiftCharacterRootCharacterSubfieldInteger :
    (((gaussSumLiftCharacterRootCharacterSubfieldInteger
        (p := p) (L := L) :
          𝓞 (characterSubfield (L := L) (p := p))) :
        characterSubfield (L := L) (p := p)) : L) =
      (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L)) :=
  rfl

/-- The character-side Galois lift restricted to the character subfield. -/
noncomputable def sigmaOfCharacterUnitCharacterSubfield (b : (ZMod (p - 1))ˣ) :
    Gal(characterSubfield (L := L) (p := p) / ℚ) := by
  letI : IsGalois ℚ (characterSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p - 1} : Set ℕ))
      (K := ℚ) (L := characterSubfield (L := L) (p := p))
  exact AlgEquiv.restrictNormalHom
    (characterSubfield (L := L) (p := p))
    (sigmaOfCharacterUnit (p := p) L b)

lemma sigmaOfCharacterUnitCharacterSubfield_smul_gaussSumLiftCharacterRootCharacterSubfieldInteger
    (b : (ZMod (p - 1))ˣ) :
    sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b •
        gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L) =
      gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L) ^
        (b : ZMod (p - 1)).val := by
  letI : IsGalois ℚ (characterSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p - 1} : Set ℕ))
      (K := ℚ) (L := characterSubfield (L := L) (p := p))
  letI : Normal ℚ (characterSubfield (L := L) (p := p)) := inferInstance
  apply NumberField.RingOfIntegers.ext
  apply Subtype.ext
  let x : characterSubfield (L := L) (p := p) :=
    ((gaussSumLiftCharacterRootCharacterSubfieldInteger
      (p := p) (L := L) : 𝓞 (characterSubfield (L := L) (p := p))) :
      characterSubfield (L := L) (p := p))
  change (((sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b) • x : _ ) : L) =
    ((x ^ (b : ZMod (p - 1)).val : characterSubfield (L := L) (p := p)) : L)
  calc
    (((sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b) • x : _ ) : L)
        = (sigmaOfCharacterUnit (p := p) L b) ((x : characterSubfield (L := L) (p := p)) : L) :=
            AlgEquiv.restrictNormal_commutes
              (χ := sigmaOfCharacterUnit (p := p) L b)
              (E := characterSubfield (L := L) (p := p)) x
    _ = (((gaussSumLiftCharacterRootCharacterSubfieldInteger
          (p := p) (L := L) : 𝓞 (characterSubfield (L := L) (p := p))) :
          characterSubfield (L := L) (p := p)) : L) ^ (b : ZMod (p - 1)).val := by
          dsimp [x]
          have hbridge :
              ((sigmaOfCharacterUnit (p := p) L b •
                  gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L) =
                (sigmaOfCharacterUnit (p := p) L b)
                  ((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L) := by
            rw [show ((sigmaOfCharacterUnit (p := p) L b •
                  gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L) =
                sigmaOfCharacterUnit (p := p) L b •
                  ((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L) from rfl,
              AlgEquiv.smul_def]
          have hsmul := congrArg
            (fun y : 𝓞 L => ((y : 𝓞 L) : L))
            (sigmaOfCharacterUnit_smul_gaussSumLiftCharacterRoot (p := p) (L := L) b)
          rw [hbridge] at hsmul
          simpa [map_pow] using hsmul
    _ = ((x ^ (b : ZMod (p - 1)).val : characterSubfield (L := L) (p := p)) : L) := by
          dsimp [x]

section CharacterSubfieldPrimeCharacterAction

variable {Pchar Qchar : Ideal (𝓞 (characterSubfield (L := L) (p := p)))}
  [Pchar.IsPrime] [Pchar.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
  [Qchar.IsPrime] [Qchar.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]

lemma characterSubfieldPrimeGenerator_pow_eq_of_sigmaOfCharacterUnit_smul
    (b : (ZMod (p - 1))ˣ)
    (hQ : Qchar = sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b • Pchar) :
    characterSubfieldPrimeGenerator (p := p) (L := L) (Pchar := Qchar) ^
        (b : ZMod (p - 1)).val =
      characterSubfieldPrimeGenerator (p := p) (L := L) (Pchar := Pchar) := by
  let σ := sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b
  let x : 𝓞 (characterSubfield (L := L) (p := p)) :=
    gaussSumLiftCharacterRootCharacterSubfieldInteger (p := p) (L := L)
  have hQ' :
      Qchar =
        Pchar.map
          (MulSemiringAction.toAlgEquiv
            ℤ (𝓞 (characterSubfield (L := L) (p := p))) σ) := by
    rw [hQ, Ideal.pointwise_smul_def]
    rfl
  have hxσ : σ • x = x ^ (b : ZMod (p - 1)).val := by
    simpa [σ, x] using
      sigmaOfCharacterUnitCharacterSubfield_smul_gaussSumLiftCharacterRootCharacterSubfieldInteger
        (p := p) (L := L) b
  calc
    characterSubfieldPrimeGenerator (p := p) (L := L) (Pchar := Qchar) ^
        (b : ZMod (p - 1)).val =
      characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L) (Pchar := Qchar)
        (Ideal.Quotient.mk Qchar (x ^ (b : ZMod (p - 1)).val)) := by
          simp [characterSubfieldPrimeGenerator, x, map_pow]
    _ =
      characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L) (Pchar := Qchar)
        (Ideal.Quotient.mk Qchar (σ • x)) := by
          congr 1
          exact (congrArg (Ideal.Quotient.mk Qchar) hxσ).symm
    _ =
      characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L) (Pchar := Qchar)
        (Ideal.Quotient.algEquivOfEqMap
          (A := ℤ)
          (B := 𝓞 (characterSubfield (L := L) (p := p)))
          (C := 𝓞 (characterSubfield (L := L) (p := p)))
          (p := 𝔭)
          (σ := MulSemiringAction.toAlgEquiv
            ℤ (𝓞 (characterSubfield (L := L) (p := p))) σ)
          hQ'
          x) := by
            rw [Ideal.Quotient.algEquivOfEqMap_apply]
            rfl
    _ =
      characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L) (Pchar := Pchar)
        (Ideal.Quotient.mk Pchar x) := by
          simpa [characterSubfieldPrimeQuotientEquivZMod, σ, x] using
            characterSubfieldPrimeQuotientEquivIntQuotient_algEquivOfEqMap_apply
              (p := p) (L := L) (Pchar := Pchar) (Qchar := Qchar) σ hQ' x
    _ = characterSubfieldPrimeGenerator (p := p) (L := L) (Pchar := Pchar) := by
          simp [characterSubfieldPrimeGenerator, x]

lemma characterSubfieldPrimeUnitGenerator_pow_eq_of_sigmaOfCharacterUnit_smul
    (b : (ZMod (p - 1))ˣ)
    (hQ : Qchar = sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b • Pchar) :
    characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Qchar) ^
        (b : ZMod (p - 1)).val =
      characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Pchar) := by
  apply Units.ext
  simpa [Units.val_pow_eq_pow_val, coe_characterSubfieldPrimeUnitGenerator] using
    characterSubfieldPrimeGenerator_pow_eq_of_sigmaOfCharacterUnit_smul
      (p := p) (L := L) (Pchar := Pchar) (Qchar := Qchar) b hQ

end CharacterSubfieldPrimeCharacterAction

/-- The discrete logarithm of the distinguished contracted character-side prime
generator with respect to `characterUnitGenerator`. -/
noncomputable def distinguishedCharacterPrimeUnitExponent : Fin (p - 1) := by
  let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  haveI : Pchar.IsPrime :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).1
  haveI : Pchar.LiesOver 𝔭 :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).2
  exact characterUnitGeneratorExponent (p := p)
    (characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Pchar))

lemma characterUnitGenerator_pow_distinguishedCharacterPrimeUnitExponent :
    characterUnitGenerator (p := p) ^
        (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) =
      characterSubfieldPrimeUnitGenerator (p := p) (L := L)
        (Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)) := by
  let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  haveI : Pchar.IsPrime :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).1
  haveI : Pchar.LiesOver 𝔭 :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).2
  simpa [distinguishedCharacterPrimeUnitExponent, Pchar] using
    characterUnitGenerator_pow_characterUnitGeneratorExponent (p := p)
      (characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Pchar))

lemma distinguishedCharacterPrimeUnitExponent_coprime :
    Nat.Coprime
      (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ)
      (p - 1) := by
  have hprim :
      IsPrimitiveRoot
        (characterUnitGenerator (p := p) ^
          (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ))
        (p - 1) := by
    rw [characterUnitGenerator_pow_distinguishedCharacterPrimeUnitExponent
      (p := p) (L := L)]
    let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
    haveI : Pchar.IsPrime :=
      (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
        (p := p) (L := L)).1
    haveI : Pchar.LiesOver 𝔭 :=
      (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
        (p := p) (L := L)).2
    simpa [Pchar] using
      characterSubfieldPrimeUnitGenerator_isPrimitiveRoot
        (p := p) (L := L) (Pchar := Pchar)
  exact (characterUnitGenerator_isPrimitiveRoot (p := p)).pow_iff_coprime
    (Nat.sub_pos_of_lt hp.out.one_lt)
    (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) |>.mp hprim

/-- The character-side Galois index sending the distinguished contracted prime
to the unique one whose residue generator is `characterUnitGenerator`. -/
noncomputable def normalizedCharacterPrimeIndex : (ZMod (p - 1))ˣ :=
  ZMod.unitOfCoprime
    (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ)
    (distinguishedCharacterPrimeUnitExponent_coprime (p := p) (L := L))

/-- The normalized contracted character-side prime, characterized by having
residue generator `characterUnitGenerator`. -/
noncomputable def normalizedCharacterPrime :
    Ideal (𝓞 (characterSubfield (L := L) (p := p))) :=
  sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L)
      (normalizedCharacterPrimeIndex (p := p) (L := L)) •
    distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)

instance normalizedCharacterPrime_isPrime :
    (normalizedCharacterPrime (p := p) (L := L)).IsPrime := by
  dsimp [normalizedCharacterPrime]
  infer_instance

instance normalizedCharacterPrime_liesOver :
    (normalizedCharacterPrime (p := p) (L := L)).LiesOver 𝔭 := by
  dsimp [normalizedCharacterPrime]
  infer_instance

lemma normalizedCharacterPrimeIndex_val :
    (((normalizedCharacterPrimeIndex (p := p) (L := L) : (ZMod (p - 1))ˣ) :
        ZMod (p - 1))).val =
      (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) := by
  rw [normalizedCharacterPrimeIndex, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt]
  exact (distinguishedCharacterPrimeUnitExponent (p := p) (L := L)).is_lt

lemma characterSubfieldPrimeUnitGenerator_normalizedCharacterPrime :
    characterSubfieldPrimeUnitGenerator (p := p) (L := L)
        (Pchar := normalizedCharacterPrime (p := p) (L := L)) =
      characterUnitGenerator (p := p) := by
  let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  let Qchar := normalizedCharacterPrime (p := p) (L := L)
  haveI : Pchar.IsPrime :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).1
  haveI : Pchar.LiesOver 𝔭 :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).2
  have hpow :
      characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Qchar) ^
          (((normalizedCharacterPrimeIndex (p := p) (L := L) : (ZMod (p - 1))ˣ) :
              ZMod (p - 1))).val =
        characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Pchar) := by
    simpa [Qchar, Pchar, normalizedCharacterPrime] using
      characterSubfieldPrimeUnitGenerator_pow_eq_of_sigmaOfCharacterUnit_smul
        (p := p) (L := L) (Pchar := Pchar) (Qchar := Qchar)
        (normalizedCharacterPrimeIndex (p := p) (L := L)) rfl
  let k : ℕ :=
    characterUnitGeneratorExponent (p := p)
      (characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Qchar))
  have hEqPow :
      characterUnitGenerator (p := p) ^
          (k * (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ)) =
        characterUnitGenerator (p := p) ^
          (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) := by
    calc
      characterUnitGenerator (p := p) ^
          (k * (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ))
          =
        (characterUnitGenerator (p := p) ^ k) ^
          (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) := by
            rw [pow_mul]
      _ =
        characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Qchar) ^
          (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) := by
            simp [k, characterUnitGenerator_pow_characterUnitGeneratorExponent]
      _ =
        characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Qchar) ^
          (((normalizedCharacterPrimeIndex (p := p) (L := L) : (ZMod (p - 1))ˣ) :
              ZMod (p - 1))).val := by
            rw [normalizedCharacterPrimeIndex_val]
      _ =
        characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Pchar) := hpow
      _ =
        characterUnitGenerator (p := p) ^
          (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) := by
            rw [characterUnitGenerator_pow_distinguishedCharacterPrimeUnitExponent
              (p := p) (L := L)]
  have hmod :
      k * (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) ≡
        (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ)
          [MOD p - 1] := by
    have hmod' :
        k * (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) ≡
          (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ)
            [MOD orderOf (characterUnitGenerator (p := p))] := by
      simpa using
        (pow_eq_pow_iff_modEq (x := characterUnitGenerator (p := p))
          (n := k * (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ))
          (m := (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ))).mp hEqPow
    simpa [orderOf_characterUnitGenerator (p := p)] using hmod'
  have hkmod : k ≡ 1 [MOD p - 1] := by
    have hcoprime_gcd :
        Nat.gcd (p - 1)
          (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) = 1 := by
      simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using
        distinguishedCharacterPrimeUnitExponent_coprime (p := p) (L := L)
    have hmod' :
        k * (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ) ≡
          1 * (distinguishedCharacterPrimeUnitExponent (p := p) (L := L) : ℕ)
            [MOD p - 1] := by
      simpa [one_mul] using hmod
    exact Nat.ModEq.cancel_right_of_coprime hcoprime_gcd hmod'
  have hkpow :
      characterUnitGenerator (p := p) ^ k = characterUnitGenerator (p := p) ^ 1 := by
    apply pow_eq_pow_of_modEq hkmod
    simpa [orderOf_characterUnitGenerator (p := p)] using
      (characterUnitGenerator_isPrimitiveRoot (p := p)).pow_eq_one
  calc
    characterSubfieldPrimeUnitGenerator (p := p) (L := L) (Pchar := Qchar) =
      characterUnitGenerator (p := p) ^ k := by
        symm
        simp [k, characterUnitGenerator_pow_characterUnitGeneratorExponent]
    _ = characterUnitGenerator (p := p) ^ 1 := hkpow
    _ = characterUnitGenerator (p := p) := by simp

lemma characterSubfieldPrimeGenerator_normalizedCharacterPrime :
    characterSubfieldPrimeGenerator (p := p) (L := L)
        (Pchar := normalizedCharacterPrime (p := p) (L := L)) =
      ((characterUnitGenerator (p := p) : (ZMod p)ˣ) : ZMod p) := by
  simpa [coe_characterSubfieldPrimeUnitGenerator] using congrArg
    (fun u : (ZMod p)ˣ => ((u : ZMod p)))
    (characterSubfieldPrimeUnitGenerator_normalizedCharacterPrime (p := p) (L := L))

lemma normalizedCharacterPrime_quotient_mk_gaussSumLiftCharacterValueCharacterSubfieldInteger
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
        (Pchar := normalizedCharacterPrime (p := p) (L := L))
        (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L))
          (gaussSumLiftCharacterValueCharacterSubfieldInteger
            (p := p) (L := L) χ a)) =
      ((a ^ (stickelbergerCharacterExponent (p := p) χ : ℕ) : (ZMod p)ˣ) : ZMod p) := by
  have hpow :
      (characterSubfieldPrimeGenerator (p := p) (L := L)
          (Pchar := normalizedCharacterPrime (p := p) (L := L))) ^
          ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
            (characterUnitGeneratorExponent (p := p) a : ℕ)) =
        ((a ^ (stickelbergerCharacterExponent (p := p) χ : ℕ) : (ZMod p)ˣ) : ZMod p) := by
    rw [characterSubfieldPrimeGenerator_normalizedCharacterPrime (p := p) (L := L)]
    have hpow_units :
        characterUnitGenerator (p := p) ^
            ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
              (characterUnitGeneratorExponent (p := p) a : ℕ)) =
          a ^ (stickelbergerCharacterExponent (p := p) χ : ℕ) := by
      rw [Nat.mul_comm, pow_mul,
        characterUnitGenerator_pow_characterUnitGeneratorExponent (p := p) a]
    exact congrArg (fun u : (ZMod p)ˣ => ((u : ZMod p))) hpow_units |>.trans <|
      by simp [Units.val_pow_eq_pow_val]
  calc
    characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
        (Pchar := normalizedCharacterPrime (p := p) (L := L))
        (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L))
          (gaussSumLiftCharacterValueCharacterSubfieldInteger
            (p := p) (L := L) χ a)) =
      (characterSubfieldPrimeGenerator (p := p) (L := L)
          (Pchar := normalizedCharacterPrime (p := p) (L := L))) ^
        ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
          (characterUnitGeneratorExponent (p := p) a : ℕ)) :=
            characterSubfieldPrime_quotient_gaussSumLiftCharacterValue
                (p := p) (L := L)
                (Pchar := normalizedCharacterPrime (p := p) (L := L)) χ a
    _ = ((a ^ (stickelbergerCharacterExponent (p := p) χ : ℕ) : (ZMod p)ˣ) : ZMod p) := hpow

lemma zmodUnit_pow_pred_eq_inv (a : (ZMod p)ˣ) :
    a ^ (p - 2) = a⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  have hp2 : 2 ≤ p := hp.out.two_le
  have hs : 1 + (p - 2) = p - 1 := by
    omega
  calc
    a * a ^ (p - 2) = a ^ (1 + (p - 2)) := by
      simp [pow_add]
    _ = a ^ (p - 1) := by
      simp [hs]
    _ = 1 := ZMod.units_pow_card_sub_one_eq_one p a

lemma normalizedCharacterPrime_quotient_mk_inverseGeneratorCharacterValueCharacterSubfieldInteger
    (a : (ZMod p)ˣ) :
    characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
        (Pchar := normalizedCharacterPrime (p := p) (L := L))
        (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L))
          (gaussSumLiftCharacterValueCharacterSubfieldInteger
            (p := p) (L := L)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) a)) =
      ((a⁻¹ : (ZMod p)ˣ) : ZMod p) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  let j : Fin (p - 1) := ⟨p - 2, by omega⟩
  calc
    characterSubfieldPrimeQuotientEquivZMod (p := p) (L := L)
        (Pchar := normalizedCharacterPrime (p := p) (L := L))
        (Ideal.Quotient.mk (normalizedCharacterPrime (p := p) (L := L))
          (gaussSumLiftCharacterValueCharacterSubfieldInteger
            (p := p) (L := L)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) a)) =
      ((a ^
          (stickelbergerCharacterExponent (p := p)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) : ℕ) :
            (ZMod p)ˣ) : ZMod p) :=
          normalizedCharacterPrime_quotient_mk_gaussSumLiftCharacterValueCharacterSubfieldInteger
              (p := p) (L := L)
              (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2))
              a
    _ = ((a ^ (p - 2) : (ZMod p)ˣ) : ZMod p) := by
          rw [show (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) =
                (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) by rfl,
            stickelbergerCharacterExponent_stickelbergerComplexCharacterGenerator_pow
              (p := p) j]
    _ = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) :=
          congrArg (fun u : (ZMod p)ˣ => ((u : ZMod p)))
            (zmodUnit_pow_pred_eq_inv (p := p) a)

lemma sigmaOfCharacterUnitCharacterSubfield_smul_algebraMap
    (b : (ZMod (p - 1))ˣ)
    (x : 𝓞 (characterSubfield (L := L) (p := p))) :
    algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L)
        (sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b • x) =
      sigmaOfCharacterUnit (p := p) L b •
        algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L) x := by
  letI : IsGalois ℚ (characterSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p - 1} : Set ℕ))
      (K := ℚ) (L := characterSubfield (L := L) (p := p))
  letI : Normal ℚ (characterSubfield (L := L) (p := p)) := inferInstance
  apply NumberField.RingOfIntegers.ext
  change (((sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b) •
      ((x : 𝓞 (characterSubfield (L := L) (p := p))) :
        characterSubfield (L := L) (p := p)) : characterSubfield (L := L) (p := p)) : L) =
    (sigmaOfCharacterUnit (p := p) L b)
      (((x : 𝓞 (characterSubfield (L := L) (p := p))) :
        characterSubfield (L := L) (p := p)) : L)
  exact AlgEquiv.restrictNormal_commutes
    (χ := sigmaOfCharacterUnit (p := p) L b)
    (E := characterSubfield (L := L) (p := p))
    ((x : 𝓞 (characterSubfield (L := L) (p := p))) :
      characterSubfield (L := L) (p := p))

lemma sigmaOfCharacterUnitCharacterSubfield_inv_smul_algebraMap
    (b : (ZMod (p - 1))ˣ)
    (x : 𝓞 (characterSubfield (L := L) (p := p))) :
    algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L)
        ((sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b)⁻¹ • x) =
      (sigmaOfCharacterUnit (p := p) L b)⁻¹ •
        algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L) x := by
  letI : IsGalois ℚ (characterSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p - 1} : Set ℕ))
      (K := ℚ) (L := characterSubfield (L := L) (p := p))
  letI : Normal ℚ (characterSubfield (L := L) (p := p)) := inferInstance
  have hinv :
      ((sigmaOfCharacterUnit (p := p) L b)⁻¹).restrictNormal
          (characterSubfield (L := L) (p := p)) =
        (sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b)⁻¹ := by
    change AlgEquiv.restrictNormalHom
        (characterSubfield (L := L) (p := p))
        ((sigmaOfCharacterUnit (p := p) L b)⁻¹) =
      (AlgEquiv.restrictNormalHom
        (characterSubfield (L := L) (p := p))
        (sigmaOfCharacterUnit (p := p) L b))⁻¹
    exact (AlgEquiv.restrictNormalHom
      (characterSubfield (L := L) (p := p))).map_inv
      (sigmaOfCharacterUnit (p := p) L b)
  apply NumberField.RingOfIntegers.ext
  change ((((sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b)⁻¹) •
      ((x : 𝓞 (characterSubfield (L := L) (p := p))) :
        characterSubfield (L := L) (p := p)) :
        characterSubfield (L := L) (p := p)) : L) =
    (sigmaOfCharacterUnit (p := p) L b)⁻¹
      ((((x : 𝓞 (characterSubfield (L := L) (p := p))) :
        characterSubfield (L := L) (p := p)) : L))
  have hcomm :=
    AlgEquiv.restrictNormal_commutes
      (χ := (sigmaOfCharacterUnit (p := p) L b)⁻¹)
      (E := characterSubfield (L := L) (p := p))
      ((x : 𝓞 (characterSubfield (L := L) (p := p))) :
        characterSubfield (L := L) (p := p))
  rw [hinv] at hcomm
  simpa using hcomm

lemma sigmaOfCharacterUnit_smul_distinguishedPrimeAboveP_under_characterSubfield_eq
    (b : (ZMod (p - 1))ˣ) :
    ((sigmaOfCharacterUnit (p := p) L b) • distinguishedPrimeAboveP p L).under
        (𝓞 (characterSubfield (L := L) (p := p))) =
      sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b •
        distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L) := by
  ext x
  change x ∈ Ideal.comap
      (algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L))
      (sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L) ↔
    x ∈ sigmaOfCharacterUnitCharacterSubfield (p := p) (L := L) b •
      Ideal.comap (algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L))
        (distinguishedPrimeAboveP p L)
  rw [Ideal.mem_comap,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  simpa using (congrArg
    (fun y : 𝓞 L => y ∈ distinguishedPrimeAboveP p L)
    (sigmaOfCharacterUnitCharacterSubfield_inv_smul_algebraMap
      (p := p) (L := L) b x)).symm

/-- The subgroup of `Gal(L/ℚ)` fixing the `(p - 1)`-cyclotomic character
subfield. -/
noncomputable def characterSubfieldFixingSubgroup : Subgroup Gal(L / ℚ) :=
  (characterSubfield (L := L) (p := p)).fixingSubgroup

lemma sigmaOfUnit_mem_characterSubfieldFixingSubgroup (a : (ZMod p)ˣ) :
    sigmaOfUnit (p := p) L a ∈ characterSubfieldFixingSubgroup (p := p) L := by
  letI : IsGalois ℚ (characterSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p - 1} : Set ℕ))
      (K := ℚ) (L := characterSubfield (L := L) (p := p))
  letI : Normal ℚ (characterSubfield (L := L) (p := p)) := inferInstance
  rw [characterSubfieldFixingSubgroup, IntermediateField.mem_fixingSubgroup_iff]
  have hrestr :
      AlgEquiv.restrictNormalHom (characterSubfield (L := L) (p := p))
        (sigmaOfUnit (p := p) L a) = 1 := by
    apply (IsCyclotomicExtension.Rat.galEquivZMod (p - 1)
      (characterSubfield (L := L) (p := p))).injective
    change (IsCyclotomicExtension.Rat.galEquivZMod (p - 1)
        (characterSubfield (L := L) (p := p))
        ((sigmaOfUnit (p := p) L a).restrictNormal
          (characterSubfield (L := L) (p := p))) =
      IsCyclotomicExtension.Rat.galEquivZMod (p - 1)
        (characterSubfield (L := L) (p := p)) 1)
    rw [IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
        (n := p * (p - 1)) (K := L)
        (F := characterSubfield (L := L) (p := p))
        (h := Nat.dvd_mul_left (p - 1) p)]
    ext
    rw [ZMod.unitsMap_val]
    rw [sigmaOfUnit, stickelbergerGalEquivZMod_sigmaOfExponent]
    simpa using unitExponentOfUnit_cast_pred (p := p) a
  intro x hx
  have happly := congrArg
    (fun τ : Gal(characterSubfield (L := L) (p := p) / ℚ) => τ ⟨x, hx⟩) hrestr
  have hcomm :
      (((sigmaOfUnit (p := p) L a).restrictNormal
          (characterSubfield (L := L) (p := p)) ⟨x, hx⟩ :
            characterSubfield (L := L) (p := p)) : L) =
        (sigmaOfUnit (p := p) L a) x :=
    AlgEquiv.restrictNormal_commutes
      (χ := sigmaOfUnit (p := p) L a)
      (E := characterSubfield (L := L) (p := p)) ⟨x, hx⟩
  exact hcomm.symm.trans (congrArg Subtype.val happly)

lemma sigmaOfUnit_smul_distinguishedPrimeAboveP_under_characterSubfield_eq
    (a : (ZMod p)ˣ) :
    ((sigmaOfUnit (p := p) L a) • distinguishedPrimeAboveP p L).under
        (𝓞 (characterSubfield (L := L) (p := p))) =
      distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L) := by
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois (S := ({p * (p - 1)} : Set ℕ)) (K := ℚ) (L := L)
  letI : IsGaloisGroup Gal(L / ℚ) ℚ L := inferInstance
  let G := characterSubfieldFixingSubgroup (p := p) L
  letI : IsGaloisGroup G (characterSubfield (L := L) (p := p)) L := by
    change IsGaloisGroup ((characterSubfield (L := L) (p := p)).fixingSubgroup)
      (characterSubfield (L := L) (p := p)) L
    exact IsGaloisGroup.intermediateField
      (G := Gal(L / ℚ)) (K := ℚ) (L := L)
      (F := characterSubfield (L := L) (p := p))
  letI : MulSemiringAction G L := inferInstance
  letI : IsGaloisGroup G
      (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (G := G) (A := 𝓞 (characterSubfield (L := L) (p := p))) (B := 𝓞 L)
      (K := characterSubfield (L := L) (p := p)) (L := L)
  letI : MulSemiringAction G (𝓞 L) := inferInstance
  let σ : G := ⟨sigmaOfUnit (p := p) L a,
    sigmaOfUnit_mem_characterSubfieldFixingSubgroup (p := p) (L := L) a⟩
  ext x
  change x ∈ Ideal.comap (algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L))
      (σ • distinguishedPrimeAboveP p L) ↔
    x ∈ Ideal.comap (algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L))
      (distinguishedPrimeAboveP p L)
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have hiff :=
    Ideal.mem_pointwise_smul_iff_inv_smul_mem
      (a := σ)
      (S := distinguishedPrimeAboveP p L)
      (x := (algebraMap (𝓞 (characterSubfield (L := L) (p := p))) (𝓞 L)) x)
  rwa [smul_algebraMap] at hiff

end GaloisAction

end BernoulliRegular
