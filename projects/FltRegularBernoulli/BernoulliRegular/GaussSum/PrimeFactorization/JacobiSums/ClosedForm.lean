module

public import BernoulliRegular.GaussSum.PrimeFactorization.JacobiSums.Boundary

/-!
# Closed-form Stickelberger coefficients from Jacobi sums
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

private lemma distinguishedPrimeExponent_stickelbergerComplexCharacterGenerator_pow_add_eq
    (j k : Fin (p - 1)) :
    ∃ n,
      distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^
            ((j : ℕ) + (k : ℕ))) +
          (p - 1) * n =
        distinguishedPrimeExponent (p := p) (L := L)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) +
          distinguishedPrimeExponent (p := p) (L := L)
            (stickelbergerComplexCharacterGenerator (p := p) ^ (k : ℕ)) := by
  let g := stickelbergerComplexCharacterGenerator (p := p)
  by_cases hj : j = 0
  · subst hj
    refine ⟨0, ?_⟩
    simp [distinguishedPrimeExponent_one]
  · by_cases hk : k = 0
    · subst hk
      refine ⟨0, ?_⟩
      simp [distinguishedPrimeExponent_one]
    · by_cases hsum : (j : ℕ) + (k : ℕ) = p - 1
      · have hgj : g ^ (j : ℕ) ≠ 1 :=
          stickelbergerComplexCharacterGenerator_pow_ne_one_of_ne_zero (p := p) (j := j) hj
        have hmul : g ^ (k : ℕ) * g ^ (j : ℕ) = 1 := by
          have hpow : g ^ ((k : ℕ) + (j : ℕ)) = (1 : DirichletCharacter ℂ p) := by
            simpa [Nat.add_comm, hsum] using
              (stickelbergerComplexCharacterGenerator_pow_sub_one_eq_one (p := p))
          simpa [pow_add] using hpow
        have hginv : (g ^ (j : ℕ))⁻¹ = g ^ (k : ℕ) :=
          inv_eq_of_mul_eq_one_left hmul
        refine ⟨1, ?_⟩
        rw [show g ^ ((j : ℕ) + (k : ℕ)) = (1 : DirichletCharacter ℂ p) by
            simpa [g, hsum] using
              (stickelbergerComplexCharacterGenerator_pow_sub_one_eq_one (p := p)),
          distinguishedPrimeExponent_one]
        simpa [g, hginv, Nat.mul_one] using
          (distinguishedPrimeExponent_add_inv_eq_pred (p := p) (L := L)
            (χ := g ^ (j : ℕ)) hgj).symm
      · have hgj : g ^ (j : ℕ) ≠ 1 :=
          stickelbergerComplexCharacterGenerator_pow_ne_one_of_ne_zero (p := p) (j := j) hj
        have hgk : g ^ (k : ℕ) ≠ 1 :=
          stickelbergerComplexCharacterGenerator_pow_ne_one_of_ne_zero (p := p) (j := k) hk
        have hgsum : g ^ ((j : ℕ) + (k : ℕ)) ≠ 1 := by
          intro htriv
          have hroot :
              stickelbergerComplexCharacterRoot (p := p) ^ ((j : ℕ) + (k : ℕ)) = 1 := by
            have hEval := congrArg
              (fun χ : DirichletCharacter ℂ p =>
                χ (((characterUnitGenerator (p := p)) : (ZMod p)ˣ) : ZMod p)) htriv
            simpa [g, MulChar.pow_apply_coe,
              stickelbergerComplexCharacterGenerator_apply_characterUnitGenerator] using hEval
          have hdvd :
              p - 1 ∣ (j : ℕ) + (k : ℕ) :=
            (stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).dvd_of_pow_eq_one _ hroot
          have hj_pos : 0 < (j : ℕ) := Fin.pos_iff_ne_zero.mpr hj
          have hk_pos : 0 < (k : ℕ) := Fin.pos_iff_ne_zero.mpr hk
          have hsum_pos : 0 < (j : ℕ) + (k : ℕ) := by omega
          have hsum_lt : (j : ℕ) + (k : ℕ) < 2 * (p - 1) := by
            have hj_lt : (j : ℕ) < p - 1 := j.2
            have hk_lt : (k : ℕ) < p - 1 := k.2
            omega
          exact hsum (Nat.eq_of_dvd_of_lt_two_mul hsum_pos.ne' hdvd hsum_lt)
        have hprod : (g ^ (j : ℕ)) * (g ^ (k : ℕ)) ≠ 1 := by
          simpa [g, pow_add] using hgsum
        let JI : Ideal (𝓞 L) :=
          Ideal.span ({jacobiSumLift (p := p) (L := L)
            (g ^ (j : ℕ)) (g ^ (k : ℕ))} : Set (𝓞 L))
        have hJ_ne : JI ≠ ⊥ :=
          Ideal.span_singleton_eq_bot.not.mpr
            (jacobiSumLift_ne_zero (p := p) (L := L) hprod)
        have hIgj_ne :
            gaussSumIdeal (p := p) (L := L) (g ^ (j : ℕ)) ≠ ⊥ :=
          gaussSumIdeal_ne_bot (p := p) (L := L) hgj
        have hIgk_ne :
            gaussSumIdeal (p := p) (L := L) (g ^ (k : ℕ)) ≠ ⊥ :=
          gaussSumIdeal_ne_bot (p := p) (L := L) hgk
        have hIgsum_ne :
            gaussSumIdeal (p := p) (L := L) (g ^ ((j : ℕ) + (k : ℕ))) ≠ ⊥ :=
          gaussSumIdeal_ne_bot (p := p) (L := L) hgsum
        have hcount0 := congrArg
          (fun I : Ideal (𝓞 L) =>
            (UniqueFactorizationMonoid.normalizedFactors I).count
              (distinguishedPrimeAboveP p L))
          (gaussSumIdeal_mul_eq_jacobiSumLift_mul_gaussSumIdeal
            (p := p) (L := L) (χ := g ^ (j : ℕ)) (ψ := g ^ (k : ℕ)) hprod)
        rw [← pow_add] at hcount0
        have hcount :
            distinguishedPrimeExponent (p := p) (L := L) (g ^ (j : ℕ)) +
                distinguishedPrimeExponent (p := p) (L := L) (g ^ (k : ℕ)) =
              (UniqueFactorizationMonoid.normalizedFactors JI).count
                  (distinguishedPrimeAboveP p L) +
                distinguishedPrimeExponent (p := p) (L := L)
                  (g ^ ((j : ℕ) + (k : ℕ))) := by
          simpa [g, JI, distinguishedPrimeExponent, gaussSumIdeal,
            UniqueFactorizationMonoid.normalizedFactors_mul hIgj_ne hIgk_ne,
            UniqueFactorizationMonoid.normalizedFactors_mul hJ_ne hIgsum_ne,
            Multiset.count_add] using hcount0
        obtain ⟨n, hn⟩ :=
          jacobiSumLift_distinguishedPrimeExponent_dvd_pred
            (p := p) (L := L) (χ := g ^ (j : ℕ)) (ψ := g ^ (k : ℕ)) hprod
        refine ⟨n, ?_⟩
        have hJcount :
            (UniqueFactorizationMonoid.normalizedFactors JI).count
                (distinguishedPrimeAboveP p L) = (p - 1) * n := by
          simpa [JI] using hn
        simpa [hJcount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcount.symm

lemma distinguishedPrimeExponent_stickelbergerComplexCharacterGenerator_pow_add_le
    (j k : Fin (p - 1)) :
    distinguishedPrimeExponent (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^
          ((j : ℕ) + (k : ℕ))) ≤
      distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) +
        distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^ (k : ℕ)) := by
  obtain ⟨n, hn⟩ :=
    distinguishedPrimeExponent_stickelbergerComplexCharacterGenerator_pow_add_eq
      (p := p) (L := L) j k
  omega

lemma distinguishedPrimeExponent_stickelbergerComplexCharacterGenerator_pow_add_modEq
    (j k : Fin (p - 1)) :
    distinguishedPrimeExponent (p := p) (L := L)
        (stickelbergerComplexCharacterGenerator (p := p) ^
          ((j : ℕ) + (k : ℕ))) ≡
      distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) +
        distinguishedPrimeExponent (p := p) (L := L)
          (stickelbergerComplexCharacterGenerator (p := p) ^ (k : ℕ))
      [MOD p - 1] := by
  obtain ⟨n, hn⟩ :=
    distinguishedPrimeExponent_stickelbergerComplexCharacterGenerator_pow_add_eq
      (p := p) (L := L) j k
  rw [← hn]
  simp [Nat.ModEq, Nat.add_mul_mod_self_left]

/-- Distinguished-prime exponent of a generator-power character, indexed by
`ZMod (p - 1)` rather than by a chosen natural representative. -/
noncomputable def distinguishedPrimeExponentGeneratorPowerIndex
    (j : ZMod (p - 1)) : ℕ :=
  distinguishedPrimeExponent (p := p) (L := L)
    (stickelbergerComplexCharacterGenerator (p := p) ^ j.val)

lemma distinguishedPrimeExponentGeneratorPowerIndex_zero :
    distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) 0 = 0 := by
  simp [distinguishedPrimeExponentGeneratorPowerIndex, distinguishedPrimeExponent_one]

private lemma stickelbergerComplexCharacterGenerator_pow_eq_of_zmod_eq
    {a b : ℕ} (h : (a : ZMod (p - 1)) = (b : ZMod (p - 1))) :
    stickelbergerComplexCharacterGenerator (p := p) ^ a =
      stickelbergerComplexCharacterGenerator (p := p) ^ b := by
  have horder :
      orderOf (stickelbergerComplexCharacterGenerator (p := p)) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one
      (stickelbergerComplexCharacterGenerator_pow_sub_one_eq_one (p := p))
  rw [pow_eq_pow_iff_modEq]
  apply Nat.ModEq.of_dvd horder
  rwa [← ZMod.natCast_eq_natCast_iff]

lemma distinguishedPrimeExponentGeneratorPowerIndex_add_le
    (j k : ZMod (p - 1)) :
    distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) (j + k) ≤
      distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) j +
        distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) k := by
  let jf : Fin (p - 1) := ⟨j.val, ZMod.val_lt j⟩
  let kf : Fin (p - 1) := ⟨k.val, ZMod.val_lt k⟩
  have hpow :
      stickelbergerComplexCharacterGenerator (p := p) ^ (j + k).val =
        stickelbergerComplexCharacterGenerator (p := p) ^ ((jf : ℕ) + (kf : ℕ)) := by
    apply stickelbergerComplexCharacterGenerator_pow_eq_of_zmod_eq (p := p)
    simp [jf, kf, Nat.cast_add]
  rw [distinguishedPrimeExponentGeneratorPowerIndex, hpow]
  simpa [distinguishedPrimeExponentGeneratorPowerIndex, jf, kf] using
    distinguishedPrimeExponent_stickelbergerComplexCharacterGenerator_pow_add_le
      (p := p) (L := L) jf kf

lemma distinguishedPrimeExponentGeneratorPowerIndex_add_modEq
    (j k : ZMod (p - 1)) :
    distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) (j + k) ≡
      distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) j +
        distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) k
      [MOD p - 1] := by
  let jf : Fin (p - 1) := ⟨j.val, ZMod.val_lt j⟩
  let kf : Fin (p - 1) := ⟨k.val, ZMod.val_lt k⟩
  have hpow :
      stickelbergerComplexCharacterGenerator (p := p) ^ (j + k).val =
        stickelbergerComplexCharacterGenerator (p := p) ^ ((jf : ℕ) + (kf : ℕ)) := by
    apply stickelbergerComplexCharacterGenerator_pow_eq_of_zmod_eq (p := p)
    simp [jf, kf, Nat.cast_add]
  rw [distinguishedPrimeExponentGeneratorPowerIndex, hpow]
  simpa [distinguishedPrimeExponentGeneratorPowerIndex, jf, kf] using
    distinguishedPrimeExponent_stickelbergerComplexCharacterGenerator_pow_add_modEq
      (p := p) (L := L) jf kf

/-- The additive `ZMod (p - 1)` index corresponding to the normalized
transport of the inverse-generator boundary character. -/
noncomputable def normalizedInverseGeneratorIndex : (ZMod (p - 1))ˣ :=
  (-1 : (ZMod (p - 1))ˣ) *
    (normalizedCharacterPrimeIndex (p := p) (L := L))⁻¹

lemma distinguishedPrimeExponentGeneratorPowerIndex_normalizedInverseGeneratorIndex_eq_one
    (hp_odd : p ≠ 2) :
    distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L)
        (((normalizedInverseGeneratorIndex (p := p) (L := L) :
          (ZMod (p - 1))ˣ) : ZMod (p - 1))) = 1 := by
  let u : (ZMod (p - 1))ˣ := normalizedCharacterPrimeIndex (p := p) (L := L)
  have hp1 : 1 < p - 1 := by have := hp.out.two_le; omega
  letI : Fact (1 < p - 1) := ⟨hp1⟩
  have hpred_add :
      ((p - 2 : ℕ) : ZMod (p - 1)) + 1 = 0 := by
    have hsub : p - 2 + 1 = p - 1 := by omega
    rw [← Nat.cast_one (R := ZMod (p - 1)), ← Nat.cast_add, hsub]
    simp
  have hpred :
      ((p - 2 : ℕ) : ZMod (p - 1)) = -1 :=
    eq_neg_of_add_eq_zero_left hpred_add
  have hpow :
      stickelbergerComplexCharacterGenerator (p := p) ^
          (((normalizedInverseGeneratorIndex (p := p) (L := L) :
            (ZMod (p - 1))ˣ) : ZMod (p - 1))).val =
        (stickelbergerComplexCharacterGenerator (p := p) ^ (p - 2)) ^
          ((u⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val := by
    rw [← pow_mul]
    apply stickelbergerComplexCharacterGenerator_pow_eq_of_zmod_eq (p := p)
    simp [normalizedInverseGeneratorIndex, u, hpred, Nat.cast_mul]
  rw [distinguishedPrimeExponentGeneratorPowerIndex, hpow]
  simpa [u] using
    distinguishedPrimeExponent_inverseGenerator_normalizedTransport_eq_one
      (p := p) (L := L) hp_odd

lemma distinguishedPrimeExponentGeneratorPowerIndex_nsmul_normalizedInverseGeneratorIndex
    (hp_odd : p ≠ 2) :
    ∀ n : ℕ, n < p - 1 →
      distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L)
          (((n : ZMod (p - 1)) *
            ((normalizedInverseGeneratorIndex (p := p) (L := L) :
              (ZMod (p - 1))ˣ) : ZMod (p - 1)))) = n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [distinguishedPrimeExponentGeneratorPowerIndex_zero]
  | succ n ih =>
      intro hsucc_lt
      have hn_lt : n < p - 1 := by omega
      let a : ZMod (p - 1) :=
        ((normalizedInverseGeneratorIndex (p := p) (L := L) :
          (ZMod (p - 1))ˣ) : ZMod (p - 1))
      have ha :
          distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L) a = 1 :=
        distinguishedPrimeExponentGeneratorPowerIndex_normalizedInverseGeneratorIndex_eq_one
          (p := p) (L := L) hp_odd
      have ih' :
          distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L)
              ((n : ZMod (p - 1)) * a) = n := by
        simpa [a] using ih hn_lt
      have hsucc_index :
          ((Nat.succ n : ZMod (p - 1)) * a) =
            (n : ZMod (p - 1)) * a + a := by
        rw [Nat.cast_succ]
        ring
      have hle :=
        distinguishedPrimeExponentGeneratorPowerIndex_add_le
          (p := p) (L := L) ((n : ZMod (p - 1)) * a) a
      have hupper :
          distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L)
              ((Nat.succ n : ZMod (p - 1)) * a) ≤ Nat.succ n := by
        rw [hsucc_index]
        simpa [ih', ha, Nat.succ_eq_add_one] using hle
      have hmod :=
        distinguishedPrimeExponentGeneratorPowerIndex_add_modEq
          (p := p) (L := L) ((n : ZMod (p - 1)) * a) a
      have hmod_succ :
          distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L)
              ((Nat.succ n : ZMod (p - 1)) * a) ≡ Nat.succ n [MOD p - 1] := by
        rw [hsucc_index]
        simpa [ih', ha, Nat.succ_eq_add_one] using hmod
      have hleft_lt :
          distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L)
              ((Nat.succ n : ZMod (p - 1)) * a) < p - 1 :=
        lt_of_le_of_lt hupper hsucc_lt
      rw [Nat.ModEq] at hmod_succ
      rwa [Nat.mod_eq_of_lt hleft_lt, Nat.mod_eq_of_lt hsucc_lt] at hmod_succ

lemma distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget_of_normalizedBoundary
    (hp_odd : p ≠ 2) :
    distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget
      (p := p) (L := L) := by
  intro j
  let u : (ZMod (p - 1))ˣ := normalizedCharacterPrimeIndex (p := p) (L := L)
  let a : ZMod (p - 1) :=
    ((normalizedInverseGeneratorIndex (p := p) (L := L) :
      (ZMod (p - 1))ˣ) : ZMod (p - 1))
  let n : ℕ :=
    stickelbergerGeneratorPowerNormalizedParameter (p := p) (L := L)
      (j : ZMod (p - 1))
  have hn_lt : n < p - 1 := by
    simpa [n, stickelbergerGeneratorPowerNormalizedParameter] using
      stickelbergerGeneratorPowerParameter_lt (p := p)
        ((j : ZMod (p - 1)) * (u : ZMod (p - 1)))
  have hcycle :
      distinguishedPrimeExponentGeneratorPowerIndex (p := p) (L := L)
          ((n : ZMod (p - 1)) * a) = n := by
    simpa [a] using
      distinguishedPrimeExponentGeneratorPowerIndex_nsmul_normalizedInverseGeneratorIndex
        (p := p) (L := L) hp_odd n hn_lt
  have hn_zmod :
      ((n : ℕ) : ZMod (p - 1)) =
        -((j : ZMod (p - 1)) * (u : ZMod (p - 1))) := by
    simp [n, u, stickelbergerGeneratorPowerNormalizedParameter,
      stickelbergerGeneratorPowerParameter]
  have hindex :
      ((n : ZMod (p - 1)) * a) = (j : ZMod (p - 1)) := by
    rw [hn_zmod]
    simp [a, u, normalizedInverseGeneratorIndex, mul_assoc]
  have hpow :
      stickelbergerComplexCharacterGenerator (p := p) ^ j.val =
        stickelbergerComplexCharacterGenerator (p := p) ^
          (((n : ZMod (p - 1)) * a).val) := by
    apply stickelbergerComplexCharacterGenerator_pow_eq_of_zmod_eq (p := p)
    simp [hindex]
  rw [hpow]
  simpa [distinguishedPrimeExponentGeneratorPowerIndex] using hcycle

lemma characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget_of_normalizedBoundary
    (hp_odd : p ≠ 2) :
    characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget
      (p := p) (L := L) :=
  characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget_of_distinguished
    (p := p) (L := L)
    (distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget_of_normalizedBoundary
      (p := p) (L := L) hp_odd)

lemma distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget_of_normalizedBoundary
    (hp_odd : p ≠ 2) :
    distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget
      (p := p) (L := L) :=
  distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget_of_generatorPower
    (p := p) (L := L)
    (distinguishedPrimeExponent_stickelbergerGeneratorPowerClosedFormTarget_of_normalizedBoundary
      (p := p) (L := L) hp_odd)

lemma additiveExponentVectorGroupRing_stickelbergerCharacterClosedFormTarget_of_normalizedBoundary
    (hp_odd : p ≠ 2) :
    additiveExponentVectorGroupRing_stickelbergerCharacterClosedFormTarget
      (p := p) (L := L) :=
  additiveExponentVectorGroupRing_stickelbergerCharacterClosedFormTarget_of_distinguished
    (p := p) (L := L)
    (distinguishedPrimeExponent_stickelbergerCharacterClosedFormTarget_of_normalizedBoundary
      (p := p) (L := L) hp_odd)

lemma characterSideExponentVector_stickelbergerCharacterClosedFormTarget_of_normalizedBoundary
    (hp_odd : p ≠ 2) :
    characterSideExponentVector_stickelbergerCharacterClosedFormTarget
      (p := p) (L := L) :=
  characterSideExponentVector_stickelbergerCharacterClosedFormTarget_of_generatorPower
    (p := p) (L := L)
    (characterSideExponentVector_stickelbergerGeneratorPowerClosedFormTarget_of_normalizedBoundary
      (p := p) (L := L) hp_odd)

lemma gaussSumIdeal_stickelbergerCharacterGroupRingFactorizationTarget_of_normalizedBoundary
    (hp_odd : p ≠ 2) :
    gaussSumIdeal_stickelbergerCharacterGroupRingFactorizationTarget
      (p := p) (L := L) :=
  gaussSumIdeal_stickelbergerCharacterGroupRingFactorizationTarget_of_characterSide
    (p := p) (L := L)
    (characterSideExponentVector_stickelbergerCharacterClosedFormTarget_of_normalizedBoundary
      (p := p) (L := L) hp_odd)

end Assembly

end BernoulliRegular
