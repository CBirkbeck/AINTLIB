module

public import BernoulliRegular.GaussSum.PrimeFactorization.Assembly.Factorization

/-!
# Stickelberger group-ring targets for Gauss-sum factorisation
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

section Assembly

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

local notation "𝔭" => (Ideal.span ({(p : ℤ)} : Set ℤ))
local instance : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩

/-- Package a character-side coefficient vector as an integer group-ring element
using the same inverse-basis convention as the Stickelberger packages. -/
noncomputable def characterSideCoefficientGroupRing
    (v : (ZMod (p - 1))ˣ → ℕ) : MonoidAlgebra ℤ (ZMod (p - 1))ˣ :=
  ∑ b : (ZMod (p - 1))ˣ, MonoidAlgebra.single b⁻¹ (v b : ℤ)

/-- The coefficient at `b⁻¹` recovers the character-side exponent indexed by
`b`. -/
@[simp] lemma characterSideCoefficientGroupRing_apply_inv
    (v : (ZMod (p - 1))ˣ → ℕ) (b : (ZMod (p - 1))ˣ) :
    characterSideCoefficientGroupRing (p := p) v b⁻¹ = (v b : ℤ) := by
  rw [characterSideCoefficientGroupRing]
  calc
    (∑ c : (ZMod (p - 1))ˣ, MonoidAlgebra.single c⁻¹ (v c : ℤ)) b⁻¹ =
        ∑ c : (ZMod (p - 1))ˣ, MonoidAlgebra.single c⁻¹ (v c : ℤ) b⁻¹ :=
          (Finsupp.finsetSum_apply
            (S := (Finset.univ : Finset (ZMod (p - 1))ˣ))
            (f := fun c : (ZMod (p - 1))ˣ =>
              MonoidAlgebra.single c⁻¹ (v c : ℤ))
            (a := b⁻¹))
    _ = (v b : ℤ) := by
        rw [Fintype.sum_eq_single b]
        · simp
        · intro c hc
          simp [hc, inv_inj]

/-- Interpret a character-side exponent vector as the corresponding product of
prime powers in the Gauss-sum factorisation. -/
noncomputable def characterSideIdealFactorizationFromVector
    (v : (ZMod (p - 1))ˣ → ℕ) : Ideal (𝓞 L) :=
  ∏ b : (ZMod (p - 1))ˣ, characterSidePrimeMap (p := p) (L := L) b ^ v b

/-- Interpret an integer group-ring exponent as the same character-side product
of prime powers. Coefficients are read in the inverse-basis convention. -/
noncomputable def characterSideIdealFactorizationFromGroupRing
    (E : MonoidAlgebra ℤ (ZMod (p - 1))ˣ) : Ideal (𝓞 L) :=
  ∏ b : (ZMod (p - 1))ˣ,
    characterSidePrimeMap (p := p) (L := L) b ^ (E b⁻¹).toNat

@[simp] lemma characterSideIdealFactorizationFromGroupRing_coefficientGroupRing
    (v : (ZMod (p - 1))ˣ → ℕ) :
    characterSideIdealFactorizationFromGroupRing (p := p) (L := L)
        (characterSideCoefficientGroupRing (p := p) v) =
      characterSideIdealFactorizationFromVector (p := p) (L := L) v := by
  simp [characterSideIdealFactorizationFromGroupRing,
    characterSideIdealFactorizationFromVector]

lemma gaussSumIdeal_eq_characterSideIdealFactorizationFromVector
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSumIdeal (p := p) (L := L) χ =
      characterSideIdealFactorizationFromVector (p := p) (L := L)
        (characterSideExponentVector (p := p) (L := L) χ) := by
  simpa [characterSideIdealFactorizationFromVector] using
    gaussSumIdeal_eq_prod_characterSideExponentVector (p := p) (L := L) hχ

/-- Reduce the distinguished-prime coefficient to the chosen generator-power
presentation of the character. -/
lemma distinguishedPrimeExponent_eq_stickelbergerComplexCharacterGenerator_pow
    (χ : DirichletCharacter ℂ p) :
    distinguishedPrimeExponent (p := p) (L := L) χ =
      distinguishedPrimeExponent (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^
          (stickelbergerCharacterExponent (p := p) χ : ℕ)) := by
  rw [stickelbergerComplexCharacter_eq_pow (p := p) χ]

/-- Reduce the additive exponent vector to the chosen generator-power
presentation of the character. -/
lemma additiveExponentVector_eq_stickelbergerComplexCharacterGenerator_pow
    (χ : DirichletCharacter ℂ p) :
    additiveExponentVector (p := p) (L := L) χ =
      additiveExponentVector (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^
          (stickelbergerCharacterExponent (p := p) χ : ℕ)) := by
  rw [stickelbergerComplexCharacter_eq_pow (p := p) χ]

/-- Reduce the normalized coefficient vector to the chosen generator-power
presentation of the character. -/
lemma characterSideExponentVector_eq_stickelbergerComplexCharacterGenerator_pow
    (χ : DirichletCharacter ℂ p) :
    characterSideExponentVector (p := p) (L := L) χ =
      characterSideExponentVector (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^
          (stickelbergerCharacterExponent (p := p) χ : ℕ)) := by
  rw [stickelbergerComplexCharacter_eq_pow (p := p) χ]

/-- For generator-power characters, the normalized coefficient at `b` is the
distinguished-prime exponent of the corresponding generator power. -/
lemma characterSideExponentVector_stickelbergerComplexCharacterGenerator_pow
    (j : Fin (p - 1)) :
    characterSideExponentVector (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) =
      fun b =>
        distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^
            ((j : ℕ) * (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val))) := by
  funext b
  simp [characterSideExponentVector, ← pow_mul]

/-- On generator-power characters, the additive exponent vector is the constant
fixed-prime coefficient function. -/
lemma additiveExponentVector_stickelbergerComplexCharacterGenerator_pow
    (j : Fin (p - 1)) :
    additiveExponentVector (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) =
      fun _ =>
        distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) :=
  additiveExponentVector_eq_distinguishedPrimeExponent (p := p) (L := L)
    (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ))

/-- The closed-form parameter at the distinguished prime after translating the
arbitrary distinguished prime to the normalized character-side prime. -/
noncomputable def stickelbergerGeneratorPowerNormalizedParameter
    (j : ZMod (p - 1)) : ℕ :=
  stickelbergerGeneratorPowerParameter (p := p)
    (j * (((normalizedCharacterPrimeIndex (p := p) (L := L) :
      (ZMod (p - 1))ˣ) : ZMod (p - 1))))

/-- The classical closed-form coefficient target for the generator-power
character `stickelbergerComplexCharacterGenerator ^ j`, written in the project's
inverse-indexing convention on `(ZMod (p - 1))ˣ` and normalized so the
distinguished prime is the translate used by `normalizedBoundaryPrime`. -/
noncomputable def stickelbergerGeneratorPowerCoefficientTarget (j : ZMod (p - 1)) :
    (ZMod (p - 1))ˣ → ℕ := fun b =>
  stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
    (j * (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1))))

lemma stickelbergerGeneratorPowerCoefficientTarget_apply
    (j : ZMod (p - 1)) (b : (ZMod (p - 1))ˣ) :
    stickelbergerGeneratorPowerCoefficientTarget (p := p) (L := L) j b =
      stickelbergerGeneratorPowerParameter (p := p)
        ((j * (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)))) *
          (((normalizedCharacterPrimeIndex (p := p) (L := L) :
            (ZMod (p - 1))ˣ) : ZMod (p - 1)))) := by
  simp [stickelbergerGeneratorPowerCoefficientTarget,
    stickelbergerGeneratorPowerNormalizedParameter]

lemma stickelbergerGeneratorPowerCoefficientTarget_one (j : ZMod (p - 1)) :
    stickelbergerGeneratorPowerCoefficientTarget (p := p) (L := L) j 1 =
      stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L) j := by
  simp [stickelbergerGeneratorPowerCoefficientTarget]

/-- The exact closed-form target for the distinguished-prime exponent of the
generator-power character `stickelbergerComplexCharacterGenerator ^ j`, using
the same normalized distinguished-prime convention as the character-side
coefficient vector. -/
def distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget : Prop :=
  ∀ j : Fin (p - 1),
    distinguishedPrimeExponent (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) =
      stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
        (j : ZMod (p - 1))

lemma distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget_iff
    :
    distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget
      (p := p) (L := L) ↔
      ∀ j : Fin (p - 1),
        distinguishedPrimeExponent (p := p) (L := L)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) =
          stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
            (j : ZMod (p - 1)) :=
  Iff.rfl

/-- The exact closed-form target for the normalized coefficient vector on
generator-power characters. -/
def characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget : Prop :=
  ∀ j : Fin (p - 1),
    characterSideExponentVector (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) =
      stickelbergerGeneratorPowerCoefficientTarget (p := p) (L := L)
        (j : ZMod (p - 1))

lemma characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget_of_distinguished
    (h :
      distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget
        (p := p) (L := L)) :
    characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget
      (p := p) (L := L) := by
  intro j
  rw [characterSideExponentVector_stickelbergerComplexCharacterGenerator_pow]
  funext b
  let k : Fin (p - 1) :=
    ⟨(((j : ZMod (p - 1)) * (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)))).val),
      ZMod.val_lt _⟩
  have horder :
      orderOf (stickelbergerComplexCharacterGenerator (p := p)) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one
      (stickelbergerComplexCharacterGenerator_pow_sub_one_eq_one (p := p))
  have hpow :
      stickelbergerComplexCharacterGenerator (p := p) ^
          ((j : ℕ) * ((((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1))).val)) =
        stickelbergerComplexCharacterGenerator (p := p) ^ (k : ℕ) := by
    rw [pow_eq_pow_iff_modEq]
    apply Nat.ModEq.of_dvd horder
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
    simp [Nat.cast_mul]
  calc
    distinguishedPrimeExponent (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^
          ((j : ℕ) * ((((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1))).val)))
      =
        distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^ (k : ℕ)) := by
            rw [hpow]
    _ = stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
          (k : ZMod (p - 1)) := h k
    _ = stickelbergerGeneratorPowerCoefficientTarget
          (p := p) (L := L) (j : ZMod (p - 1)) b := by
          simp [stickelbergerGeneratorPowerCoefficientTarget,
            stickelbergerGeneratorPowerNormalizedParameter, k]

lemma distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget_of_characterSide
    (h :
      characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget
        (p := p) (L := L)) :
    distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget
      (p := p) (L := L) := by
  intro j
  by_cases hj : j = 0
  · subst hj
    simpa [characterSideExponentVector, stickelbergerGeneratorPowerCoefficientTarget,
      stickelbergerGeneratorPowerNormalizedParameter,
      stickelbergerGeneratorPowerParameter] using congrFun (h 0) (1 : (ZMod (p - 1))ˣ)
  · have hjpos : 0 < j := Fin.pos_iff_ne_zero.mpr hj
    have hp1 : 1 < p - 1 := by omega
    letI : Fact (1 < p - 1) := ⟨hp1⟩
    have hval1 : (1 : ZMod (p - 1)).val = 1 := ZMod.val_one (p - 1)
    simpa [characterSideExponentVector, stickelbergerGeneratorPowerCoefficientTarget,
      stickelbergerGeneratorPowerNormalizedParameter,
      stickelbergerGeneratorPowerParameter, hval1] using congrFun (h j) (1 : (ZMod (p - 1))ˣ)

theorem distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget_iff_characterSide
    :
    distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget
        (p := p) (L := L) ↔
      characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget
        (p := p) (L := L) :=
  ⟨characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget_of_distinguished
      (p := p) (L := L),
    distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget_of_characterSide
      (p := p) (L := L)⟩

/-- The closed-form coefficient target for an arbitrary character, expressed by
first writing it as a power of `stickelbergerComplexCharacterGenerator`. -/
noncomputable def stickelbergerCharacterCoefficientTarget
    (χ : DirichletCharacter ℂ p) : (ZMod (p - 1))ˣ → ℕ :=
  stickelbergerGeneratorPowerCoefficientTarget (p := p) (L := L)
    (stickelbergerCharacterExponent (p := p) χ : ZMod (p - 1))

/-- The group-ring exponent attached to the arbitrary-character coefficient
target, in the inverse-basis convention used downstream. -/
noncomputable def stickelbergerCharacterCoefficientGroupRingTarget
    (χ : DirichletCharacter ℂ p) : MonoidAlgebra ℤ (ZMod (p - 1))ˣ :=
  characterSideCoefficientGroupRing (p := p)
    (stickelbergerCharacterCoefficientTarget (p := p) (L := L) χ)

/-- Coefficients of the character-side group-ring target. -/
@[simp] lemma stickelbergerCharacterCoefficientGroupRingTarget_apply_inv
    (χ : DirichletCharacter ℂ p) (b : (ZMod (p - 1))ˣ) :
    stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ b⁻¹ =
      (stickelbergerCharacterCoefficientTarget (p := p) (L := L) χ b : ℤ) := by
  simp [stickelbergerCharacterCoefficientGroupRingTarget]

/-- The additive-side group-ring target for an arbitrary character after the
pointwise coefficient formula has collapsed to the distinguished-prime
exponent. -/
noncomputable def stickelbergerCharacterAdditiveGroupRingTarget
    (χ : DirichletCharacter ℂ p) : MonoidAlgebra ℤ (ZMod p)ˣ :=
  unitExponentVectorGroupRing (p := p)
    (fun _ =>
      stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
        (stickelbergerCharacterExponent (p := p) χ : ZMod (p - 1)))

/-- Coefficients of the arbitrary-character additive group-ring target. -/
@[simp] lemma stickelbergerCharacterAdditiveGroupRingTarget_apply_inv
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    stickelbergerCharacterAdditiveGroupRingTarget (p := p) (L := L) χ a⁻¹ =
      (stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
        (stickelbergerCharacterExponent (p := p) χ : ZMod (p - 1)) : ℤ) := by
  simp [stickelbergerCharacterAdditiveGroupRingTarget]

/-- The distinguished-prime closed-form target for arbitrary characters. -/
def distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget : Prop :=
  ∀ χ : DirichletCharacter ℂ p,
    distinguishedPrimeExponent (p := p) (L := L) χ =
      stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
        (stickelbergerCharacterExponent (p := p) χ : ZMod (p - 1))

/-- The character-side vector closed-form target for arbitrary characters. -/
def characterSideExponentVector_stickelbergerCharacterClosedFormTarget : Prop :=
  ∀ χ : DirichletCharacter ℂ p,
    characterSideExponentVector (p := p) (L := L) χ =
      stickelbergerCharacterCoefficientTarget (p := p) (L := L) χ

/-- The additive group-ring closed-form target for arbitrary characters. -/
def additiveExponentVectorGroupRing_stickelbergerCharacterClosedFormTarget : Prop :=
  ∀ χ : DirichletCharacter ℂ p,
    additiveExponentVectorGroupRing (p := p) (L := L) χ =
      stickelbergerCharacterAdditiveGroupRingTarget (p := p) (L := L) χ

/-- The final character-side group-ring factorisation target: the Gauss-sum
ideal is the prime-power product obtained by reading the coefficients of the
packaged Stickelberger character exponent. -/
def gaussSumIdeal_stickelbergerCharacterGroupRingFactorizationTarget : Prop :=
  ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
    gaussSumIdeal (p := p) (L := L) χ =
      characterSideIdealFactorizationFromGroupRing (p := p) (L := L)
        (stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ)

lemma distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget_of_generatorPower
    (h :
      distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget
        (p := p) (L := L)) :
    distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget
      (p := p) (L := L) := by
  intro χ
  rw [distinguishedPrimeExponent_eq_stickelbergerComplexCharacterGenerator_pow]
  exact h (stickelbergerCharacterExponent (p := p) χ)

lemma additiveExponentVectorGroupRing_stickelbergerCharacterClosedFormTarget_of_distinguished
    (h :
      distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget
        (p := p) (L := L)) :
    additiveExponentVectorGroupRing_stickelbergerCharacterClosedFormTarget
      (p := p) (L := L) := by
  intro χ
  rw [additiveExponentVectorGroupRing_eq_distinguishedPrimeExponent]
  simp [stickelbergerCharacterAdditiveGroupRingTarget, h χ]

lemma gaussSumIdeal_stickelbergerCharacterGroupRingFactorizationTarget_of_characterSide
    (h :
      characterSideExponentVector_stickelbergerCharacterClosedFormTarget
        (p := p) (L := L)) :
    gaussSumIdeal_stickelbergerCharacterGroupRingFactorizationTarget
      (p := p) (L := L) := by
  intro χ hχ
  calc
    gaussSumIdeal (p := p) (L := L) χ =
        characterSideIdealFactorizationFromVector (p := p) (L := L)
          (characterSideExponentVector (p := p) (L := L) χ) :=
            gaussSumIdeal_eq_characterSideIdealFactorizationFromVector
              (p := p) (L := L) hχ
    _ =
        characterSideIdealFactorizationFromVector (p := p) (L := L)
          (stickelbergerCharacterCoefficientTarget (p := p) (L := L) χ) := by
            rw [h χ]
    _ =
        characterSideIdealFactorizationFromGroupRing (p := p) (L := L)
          (stickelbergerCharacterCoefficientGroupRingTarget (p := p) (L := L) χ) := by
            simp [stickelbergerCharacterCoefficientGroupRingTarget]

lemma characterSideExponentVector_stickelbergerCharacterClosedFormTarget_of_generatorPower
    (h :
      characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget
        (p := p) (L := L)) :
    characterSideExponentVector_stickelbergerCharacterClosedFormTarget
      (p := p) (L := L) := by
  intro χ
  rw [characterSideExponentVector_eq_stickelbergerComplexCharacterGenerator_pow]
  simpa [stickelbergerCharacterCoefficientTarget] using
    h (stickelbergerCharacterExponent (p := p) χ)

end Assembly

end BernoulliRegular
