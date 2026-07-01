module

public import BernoulliRegular.GaussSum.PrimeFactorization.Assembly.Orbits

/-!
# Gauss-sum ideal factorisation over character-side orbits
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

/-- Package an exponent vector indexed by `(ZMod p)ˣ` as an integer group-ring
element, using the Stickelberger convention that the coefficient attached to
`a` sits on the basis element `single a⁻¹ 1`. -/
noncomputable def unitExponentVectorGroupRing (v : (ZMod p)ˣ → ℕ) :
    MonoidAlgebra ℤ (ZMod p)ˣ :=
  stickelbergerCoefficientPackage (p := p) (fun a ↦ (v a : ℤ))

/-- The coefficient at `a⁻¹` recovers the exponent indexed by `a`. -/
@[simp] lemma unitExponentVectorGroupRing_apply_inv
    (v : (ZMod p)ˣ → ℕ) (a : (ZMod p)ˣ) :
    unitExponentVectorGroupRing (p := p) v a⁻¹ = (v a : ℤ) := by
  simp [unitExponentVectorGroupRing]

/-- The additive-side exponent vector packaged in the downstream group-ring
coefficient convention. -/
noncomputable def additiveExponentVectorGroupRing (χ : DirichletCharacter ℂ p) :
    MonoidAlgebra ℤ (ZMod p)ˣ :=
  unitExponentVectorGroupRing (p := p)
    (additiveExponentVector (p := p) (L := L) χ)

/-- Packaging the additive-side exponent vector is the same as packaging the
constant vector with value `distinguishedPrimeExponent χ`. -/
lemma additiveExponentVectorGroupRing_eq_distinguishedPrimeExponent
    (χ : DirichletCharacter ℂ p) :
    additiveExponentVectorGroupRing (p := p) (L := L) χ =
      unitExponentVectorGroupRing (p := p)
        (fun _ ↦ distinguishedPrimeExponent (p := p) (L := L) χ) := by
  simp [additiveExponentVectorGroupRing,
    additiveExponentVector_eq_distinguishedPrimeExponent]

/-- The orbit map, viewed as a map onto the subtype cut out by the orbit finset. -/
noncomputable def characterSidePrimeMapToOrbit :
    (ZMod (p - 1))ˣ → {P // P ∈ characterSidePrimeOrbit p L} := fun b ↦
  ⟨characterSidePrimeMap (p := p) (L := L) b,
    characterSidePrimeMap_mem_characterSidePrimeOrbit (p := p) (L := L) b⟩

lemma characterSidePrimeMapToOrbit_surjective :
    Function.Surjective (characterSidePrimeMapToOrbit (p := p) (L := L)) := by
  intro P
  rcases (mem_characterSidePrimeOrbit_iff (p := p) (L := L)).1 P.2 with ⟨b, hb⟩
  exact ⟨b, Subtype.ext hb⟩

/-- The character-side orbit map is bijective onto the orbit subtype. -/
theorem characterSidePrimeMapToOrbit_bijective :
    Function.Bijective (characterSidePrimeMapToOrbit (p := p) (L := L)) := by
  refine (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨characterSidePrimeMapToOrbit_surjective (p := p) (L := L), ?_⟩
  rw [Fintype.card_of_subtype (characterSidePrimeOrbit p L) (by simp),
    card_characterSidePrimeOrbit (p := p) (L := L),
    ZMod.card_units_eq_totient]

/-- The orbit map on ideals is injective, so the orbit product can be reindexed
without duplicate factors. -/
theorem characterSidePrimeMap_injective :
    Function.Injective (characterSidePrimeMap (p := p) (L := L)) := by
  intro b₁ b₂ h
  exact (characterSidePrimeMapToOrbit_bijective (p := p) (L := L)).1 (Subtype.ext h)

/-- The character-side lifts parameterize the orbit finset of the distinguished
prime above `(p)`. -/
noncomputable def characterSidePrimeEquivOrbit :
    (ZMod (p - 1))ˣ ≃ {P // P ∈ characterSidePrimeOrbit p L} :=
  Equiv.ofBijective
    (characterSidePrimeMapToOrbit (p := p) (L := L))
    (characterSidePrimeMapToOrbit_bijective (p := p) (L := L))

/-- Every prime factor of the lifted Gauss-sum ideal lies above `(p)`. -/
lemma normalizedFactors_gaussSumIdeal_subset_primesAboveP
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    (UniqueFactorizationMonoid.normalizedFactors
        (gaussSumIdeal (p := p) (L := L) χ)).toFinset ⊆ primesAboveP p L := by
  classical
  intro P hP
  let Iχ : Ideal (𝓞 L) := gaussSumIdeal (p := p) (L := L) χ
  let Iχinv : Ideal (𝓞 L) := gaussSumIdeal (p := p) (L := L) χ⁻¹
  have hP_mem :
      P ∈ UniqueFactorizationMonoid.normalizedFactors Iχ :=
    Multiset.mem_toFinset.1 hP
  have hP_fac := (Ideal.mem_normalizedFactors_iff
    (gaussSumIdeal_ne_bot (p := p) (L := L) hχ)).1 hP_mem
  have hP_prime : P.IsPrime := hP_fac.1
  have hIχ_le_P : Iχ ≤ P := hP_fac.2
  letI : P.IsPrime := hP_prime
  have hspan_p_le_P : Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L)) ≤ P := by
    calc
      Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L)) = Iχ * Iχinv := by
        symm
        simpa [Iχ, Iχinv, gaussSumIdeal] using
          (gaussSum_ideal_mul_inv_eq_span_p (p := p) (L := L) hχ)
      _ ≤ Iχ := Ideal.mul_le_right
      _ ≤ P := hIχ_le_P
  have hp_mem_P : (p : 𝓞 L) ∈ P :=
    hspan_p_le_P (Ideal.subset_span (by simp))
  have hp_mem_under : (p : ℤ) ∈ P.under ℤ := by
    simpa [Ideal.under] using hp_mem_P
  have hspan_p_under_le : 𝔭 ≤ P.under ℤ := by
    simpa using ((Ideal.span_singleton_le_iff_mem (I := P.under ℤ)).mpr hp_mem_under :
      Ideal.span ({(p : ℤ)} : Set ℤ) ≤ P.under ℤ)
  have hunder_eq : P.under ℤ = 𝔭 := by
    symm
    apply Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p)
    · exact Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ P)
    · exact hspan_p_under_le
  have hP_lies : P.LiesOver 𝔭 := by
    rw [Ideal.liesOver_iff, hunder_eq]
  exact (mem_primesAboveP_iff (p := p) (L := L)).2 ⟨hP_prime, hP_lies⟩

/-- The principal ideal generated by the lifted Gauss sum factors as the product
of its prime-above-`p` contributions. -/
lemma gaussSumIdeal_eq_prod_primesAboveP
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSumIdeal (p := p) (L := L) χ =
      ∏ P ∈ primesAboveP p L, P ^ primeAbovePExponent (p := p) (L := L) P χ := by
  classical
  let m := UniqueFactorizationMonoid.normalizedFactors (gaussSumIdeal (p := p) (L := L) χ)
  have hI_ne : gaussSumIdeal (p := p) (L := L) χ ≠ ⊥ :=
    gaussSumIdeal_ne_bot (p := p) (L := L) hχ
  have hsubset : m.toFinset ⊆ primesAboveP p L := by
    simpa [m] using
      (normalizedFactors_gaussSumIdeal_subset_primesAboveP (p := p) (L := L) hχ)
  calc
    gaussSumIdeal (p := p) (L := L) χ = m.prod := by
      symm
      simpa [m] using (UniqueFactorizationMonoid.prod_normalizedFactors_eq hI_ne)
    _ = ∏ P ∈ primesAboveP p L, P ^ m.count P := by
      simpa using Finset.prod_multiset_count_of_subset m (primesAboveP p L) hsubset
    _ = ∏ P ∈ primesAboveP p L, P ^ primeAbovePExponent (p := p) (L := L) P χ := by
      apply Finset.prod_congr rfl
      intro P hP
      simp [m, primeAbovePExponent]

/-- Reindex the Gauss-sum ideal factorisation by the character-side orbit of
the distinguished prime above `(p)`. -/
lemma gaussSumIdeal_eq_prod_characterSidePrimeOrbit
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSumIdeal (p := p) (L := L) χ =
      ∏ P ∈ characterSidePrimeOrbit p L,
        P ^ primeAbovePExponent (p := p) (L := L) P χ := by
  rw [characterSidePrimeOrbit_eq_primesAboveP (p := p) (L := L)]
  exact gaussSumIdeal_eq_prod_primesAboveP (p := p) (L := L) hχ

/-- Raising a character by a unit exponent and then by the inverse unit exponent
recovers the original character. -/
lemma pow_characterSideUnit_val_pow_inv_eq_self
    (b : (ZMod (p - 1))ˣ) (χ : DirichletCharacter ℂ p) :
    (χ ^ (b : ZMod (p - 1)).val) ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val) = χ := by
  rw [← pow_mul]
  conv_rhs => rw [← pow_one χ]
  rw [pow_eq_pow_iff_modEq]
  have hpow : χ ^ (p - 1) = 1 := by
    have h := MulChar.pow_card_eq_one χ (M := ZMod p)
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h
  have horder : orderOf χ ∣ p - 1 := orderOf_dvd_of_pow_eq_one hpow
  apply Nat.ModEq.of_dvd horder
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val]
  convert congrArg
    (fun u : (ZMod (p - 1))ˣ ↦ ((u : ZMod (p - 1))))
    (mul_inv_cancel b) using 1 <;> simp

/-- A nontrivial character stays nontrivial after raising it to a unit exponent. -/
lemma pow_characterSideUnit_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (b : (ZMod (p - 1))ˣ) :
    χ ^ (b : ZMod (p - 1)).val ≠ 1 := by
  intro hpow
  have hpow' := congrArg
    (fun ψ : DirichletCharacter ℂ p ↦
      ψ ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val)) hpow
  exact hχ (by
    simpa [pow_characterSideUnit_val_pow_inv_eq_self (p := p) (b := b) χ] using hpow')

/-- Rewrite the character-side orbit factorization as an explicit product over
`(ZMod (p - 1))ˣ`, with the exponents transported to the distinguished-prime
convention. -/
lemma gaussSumIdeal_eq_prod_characterSideUnits
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSumIdeal (p := p) (L := L) χ =
      ∏ b : (ZMod (p - 1))ˣ,
        characterSidePrimeMap (p := p) (L := L) b⁻¹ ^
          distinguishedPrimeExponent (p := p) (L := L)
            (χ ^ (b : ZMod (p - 1)).val) := by
  calc
    gaussSumIdeal (p := p) (L := L) χ
        =
        ∏ P ∈ characterSidePrimeOrbit p L,
          P ^ primeAbovePExponent (p := p) (L := L) P χ :=
            gaussSumIdeal_eq_prod_characterSidePrimeOrbit (p := p) (L := L) hχ
    _ = ∏ P : {P // P ∈ characterSidePrimeOrbit p L},
          P.1 ^ primeAbovePExponent (p := p) (L := L) P.1 χ := by
            simpa using
              (Finset.prod_coe_sort
                (s := characterSidePrimeOrbit p L)
                (f := fun P : Ideal (𝓞 L) ↦
                  P ^ primeAbovePExponent (p := p) (L := L) P χ)).symm
    _ = ∏ b : (ZMod (p - 1))ˣ,
          (characterSidePrimeEquivOrbit (p := p) (L := L) b).1 ^
            primeAbovePExponent (p := p) (L := L)
              (characterSidePrimeEquivOrbit (p := p) (L := L) b).1 χ :=
            (Fintype.prod_equiv
              (characterSidePrimeEquivOrbit (p := p) (L := L)) _ _ fun _ ↦ rfl).symm
    _ = ∏ b : (ZMod (p - 1))ˣ,
          characterSidePrimeMap (p := p) (L := L) b ^
            primeAbovePExponent (p := p) (L := L)
              (characterSidePrimeMap (p := p) (L := L) b) χ := rfl
    _ = ∏ b : (ZMod (p - 1))ˣ,
          characterSidePrimeMap (p := p) (L := L) b⁻¹ ^
            primeAbovePExponent (p := p) (L := L)
              (characterSidePrimeMap (p := p) (L := L) b⁻¹) χ :=
            (Fintype.prod_equiv (Equiv.inv ((ZMod (p - 1))ˣ)) _ _ fun _ ↦ rfl).symm
    _ = ∏ b : (ZMod (p - 1))ˣ,
          characterSidePrimeMap (p := p) (L := L) b⁻¹ ^
            distinguishedPrimeExponent (p := p) (L := L)
              (χ ^ (b : ZMod (p - 1)).val) := by
            refine Fintype.prod_congr _ _ ?_
            intro b
            congr 1
            have hχb :
                χ ^ (b : ZMod (p - 1)).val ≠ 1 :=
              pow_characterSideUnit_ne_one (p := p) hχ b
            have htransport :=
              sigmaOfCharacterUnitPrimeExponent_eq_distinguishedPrimeExponent
                (p := p) (L := L) b⁻¹ (χ := χ ^ (b : ZMod (p - 1)).val) hχb
            have hpow :
                (χ ^ (b : ZMod (p - 1)).val) ^
                    (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val) = χ :=
              pow_characterSideUnit_val_pow_inv_eq_self (p := p) (b := b) χ
            simpa [characterSidePrimeMap, hpow] using htransport

/-- The normalized exponent vector on `(ZMod (p - 1))ˣ` attached to the
Gauss-sum ideal factorization of `χ`. The coefficient at `b` is the
distinguished-prime exponent of the inverse-transformed character. -/
noncomputable def characterSideExponentVector (χ : DirichletCharacter ℂ p) :
    (ZMod (p - 1))ˣ → ℕ := fun b ↦
  distinguishedPrimeExponent (p := p) (L := L)
    (χ ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val))

/-- The character-side orbit factorization in the final exponent-vector
convention used by the subsequent Stickelberger group-ring repackaging. -/
lemma gaussSumIdeal_eq_prod_characterSideExponentVector
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSumIdeal (p := p) (L := L) χ =
      ∏ b : (ZMod (p - 1))ˣ,
        characterSidePrimeMap (p := p) (L := L) b ^
          characterSideExponentVector (p := p) (L := L) χ b := by
  calc
    gaussSumIdeal (p := p) (L := L) χ
        =
        ∏ b : (ZMod (p - 1))ˣ,
          characterSidePrimeMap (p := p) (L := L) b⁻¹ ^
            distinguishedPrimeExponent (p := p) (L := L)
              (χ ^ (b : ZMod (p - 1)).val) :=
            gaussSumIdeal_eq_prod_characterSideUnits (p := p) (L := L) hχ
    _ = ∏ b : (ZMod (p - 1))ˣ,
          characterSidePrimeMap (p := p) (L := L) b ^
            distinguishedPrimeExponent (p := p) (L := L)
              (χ ^ (((b⁻¹ : (ZMod (p - 1))ˣ) : ZMod (p - 1)).val)) :=
            (Fintype.prod_equiv (Equiv.inv ((ZMod (p - 1))ˣ)) _ _ fun _ ↦ rfl).symm
    _ = ∏ b : (ZMod (p - 1))ˣ,
          characterSidePrimeMap (p := p) (L := L) b ^
            characterSideExponentVector (p := p) (L := L) χ b := rfl

end Assembly

end BernoulliRegular
