module

public import BernoulliRegular.GaussSum.PrimeFactorization.Assembly.Transport

/-!
# Prime-above-p orbits for Gauss-sum factorisation
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

/-- Every prime above `(p)` in the Stickelberger field contracts to the
canonical `1 - ζ_p` prime in the additive cyclotomic subfield. -/
lemma primeAboveP_under_additiveSubfield_eq_additiveZetaPrime
    {P : Ideal (𝓞 L)} (hP : P ∈ primesAboveP p L) :
    P.under (𝓞 (additiveSubfield (L := L) (p := p))) =
      additiveZetaPrime (L := L) (p := p) := by
  have hP_over : P ∈ Ideal.primesOver 𝔭 (𝓞 L) :=
    (mem_primesAboveP_iff (p := p) (L := L)).1 hP
  let P' : Ideal (𝓞 (additiveSubfield (L := L) (p := p))) :=
    P.under (𝓞 (additiveSubfield (L := L) (p := p)))
  haveI : P.IsPrime := hP_over.1
  haveI : P.LiesOver 𝔭 := hP_over.2
  haveI : P'.IsPrime := inferInstance
  haveI : P'.LiesOver 𝔭 := by
    dsimp [P']
    infer_instance
  simpa [P', additiveZetaPrime] using
    (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
      (p := p)
      (K := additiveSubfield (L := L) (p := p))
      (hζ := IsCyclotomicExtension.zeta_spec p ℚ (additiveSubfield (L := L) (p := p)))
      (P := P'))

/-- The orbit map from `(ZMod p)ˣ` to the primes above `(p)`, obtained by
acting on the distinguished prime with the additive-side lifts. -/
noncomputable def additivePrimeMap (a : (ZMod p)ˣ) : Ideal (𝓞 L) :=
  sigmaOfUnit (p := p) L a • distinguishedPrimeAboveP p L

/-- The finite orbit of the distinguished prime under the additive-side Galois
lifts indexed by `(ZMod p)ˣ`. -/
noncomputable def additivePrimeOrbit : Finset (Ideal (𝓞 L)) :=
  Finset.univ.image (additivePrimeMap (p := p) (L := L))

lemma additivePrimeMap_mem_additivePrimeOrbit (a : (ZMod p)ˣ) :
    additivePrimeMap (p := p) (L := L) a ∈ additivePrimeOrbit p L := by
  classical
  simp [additivePrimeOrbit, additivePrimeMap]

lemma mem_additivePrimeOrbit_iff {P : Ideal (𝓞 L)} :
    P ∈ additivePrimeOrbit p L ↔
      ∃ a : (ZMod p)ˣ,
        sigmaOfUnit (p := p) L a • distinguishedPrimeAboveP p L = P := by
  classical
  simp [additivePrimeOrbit, additivePrimeMap]

/-- Every prime in the additive-side orbit of the distinguished prime still
lies above `(p)`. -/
lemma additivePrimeOrbit_subset_primesAboveP :
    additivePrimeOrbit p L ⊆ primesAboveP p L := by
  classical
  intro P hP
  rcases (mem_additivePrimeOrbit_iff (p := p) (L := L)).1 hP with ⟨a, rfl⟩
  exact (mem_primesAboveP_iff (p := p) (L := L)).2 ⟨inferInstance, inferInstance⟩

/-- Every prime in the additive-side orbit contracts to the canonical additive
cyclotomic prime. -/
lemma additivePrimeOrbit_under_additiveSubfield_eq_additiveZetaPrime
    {P : Ideal (𝓞 L)} (hP : P ∈ additivePrimeOrbit p L) :
    P.under (𝓞 (additiveSubfield (L := L) (p := p))) =
      additiveZetaPrime (L := L) (p := p) := by
  rcases (mem_additivePrimeOrbit_iff (p := p) (L := L)).1 hP with ⟨a, rfl⟩
  exact sigmaOfUnit_smul_distinguishedPrimeAboveP_under_eq_additiveZetaPrime
    (p := p) (L := L) a

/-- Every prime in the additive-side orbit contracts to the same distinguished
prime of the `(p - 1)`-cyclotomic character subfield. -/
lemma additivePrimeOrbit_under_characterSubfield_eq_distinguishedPrimeAboveP_under
    {P : Ideal (𝓞 L)} (hP : P ∈ additivePrimeOrbit p L) :
    P.under (𝓞 (characterSubfield (L := L) (p := p))) =
      distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L) := by
  rcases (mem_additivePrimeOrbit_iff (p := p) (L := L)).1 hP with ⟨a, rfl⟩
  exact sigmaOfUnit_smul_distinguishedPrimeAboveP_under_characterSubfield_eq
    (p := p) (L := L) a

/-- The additive-side exponent vector on `(ZMod p)ˣ` attached to the
Gauss-sum ideal factorization of `χ`. The coefficient at `a` is the exponent
of the prime `σ_a(P₀)`. -/
noncomputable def additiveExponentVector (χ : DirichletCharacter ℂ p) :
    (ZMod p)ˣ → ℕ := fun a ↦
  sigmaOfUnitPrimeExponent (p := p) (L := L) a χ

/-- The orbit map from `(ZMod (p - 1))ˣ` to the primes above `(p)`, obtained by
acting on the distinguished prime with the character-side lifts. -/
noncomputable def characterSidePrimeMap (b : (ZMod (p - 1))ˣ) : Ideal (𝓞 L) :=
  sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L

/-- The finite orbit of the distinguished prime under the character-side
Galois lifts indexed by `(ZMod (p - 1))ˣ`. -/
noncomputable def characterSidePrimeOrbit : Finset (Ideal (𝓞 L)) :=
  Finset.univ.image (characterSidePrimeMap (p := p) (L := L))

lemma characterSidePrimeMap_mem_characterSidePrimeOrbit (b : (ZMod (p - 1))ˣ) :
    characterSidePrimeMap (p := p) (L := L) b ∈ characterSidePrimeOrbit p L := by
  classical
  simp [characterSidePrimeOrbit, characterSidePrimeMap]

lemma mem_characterSidePrimeOrbit_iff {P : Ideal (𝓞 L)} :
    P ∈ characterSidePrimeOrbit p L ↔
      ∃ b : (ZMod (p - 1))ˣ,
        sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L = P := by
  classical
  simp [characterSidePrimeOrbit, characterSidePrimeMap]

/-- Every prime in the character-side orbit of the distinguished prime still
lies above `(p)`. -/
lemma characterSidePrimeOrbit_subset_primesAboveP :
    characterSidePrimeOrbit p L ⊆ primesAboveP p L := by
  classical
  intro P hP
  rcases (mem_characterSidePrimeOrbit_iff (p := p) (L := L)).1 hP with ⟨b, rfl⟩
  exact (mem_primesAboveP_iff (p := p) (L := L)).2 ⟨inferInstance, inferInstance⟩

/-- Every prime in the character-side orbit contracts to the canonical additive
cyclotomic prime. -/
lemma characterSidePrimeOrbit_under_additiveSubfield_eq_additiveZetaPrime
    {P : Ideal (𝓞 L)} (hP : P ∈ characterSidePrimeOrbit p L) :
    P.under (𝓞 (additiveSubfield (L := L) (p := p))) =
      additiveZetaPrime (L := L) (p := p) :=
  primeAboveP_under_additiveSubfield_eq_additiveZetaPrime
    (p := p) (L := L) ((characterSidePrimeOrbit_subset_primesAboveP (p := p) (L := L)) hP)

/-- The subgroup of `Gal(L/ℚ)` fixing the additive `p`-cyclotomic subfield. -/
noncomputable def characterSideFixingSubgroup : Subgroup Gal(L / ℚ) :=
  (additiveSubfield (L := L) (p := p)).fixingSubgroup

lemma finrank_rat_additiveSubfield :
    Module.finrank ℚ (additiveSubfield (L := L) (p := p)) = p - 1 := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  simpa [Nat.totient_prime hp.out] using
    (IsCyclotomicExtension.Rat.finrank (k := p)
      (K := additiveSubfield (L := L) (p := p)))

lemma finrank_additiveSubfield :
    Module.finrank (additiveSubfield (L := L) (p := p)) L = Nat.totient (p - 1) := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  letI : NeZero (p * (p - 1)) :=
    ⟨Nat.mul_ne_zero hp.out.ne_zero (Nat.sub_ne_zero_of_lt hp.out.one_lt)⟩
  have hmul := Module.finrank_mul_finrank ℚ (additiveSubfield (L := L) (p := p)) L
  rw [finrank_rat_additiveSubfield (p := p) (L := L),
    IsCyclotomicExtension.Rat.finrank (k := p * (p - 1)) (K := L),
    Nat.totient_mul (prime_coprime_pred (p := p)), Nat.totient_prime hp.out] at hmul
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.out.one_lt) hmul

lemma characterExponentOfUnit_injective :
    Function.Injective (characterExponentOfUnit (p := p)) := by
  intro b₁ b₂ h
  have h'' := congrArg (stickelbergerUnitsEquivProd (p := p)) h
  rw [stickelbergerUnitsEquivProd_characterExponentOfUnit,
    stickelbergerUnitsEquivProd_characterExponentOfUnit] at h''
  exact congrArg Prod.snd h''

lemma sigmaOfCharacterUnit_injective :
    Function.Injective (sigmaOfCharacterUnit (p := p) L) := by
  intro b₁ b₂ h
  have h' := congrArg (stickelbergerGalEquivZMod (p := p) L) h
  rw [sigmaOfCharacterUnit, stickelbergerGalEquivZMod_sigmaOfExponent,
    sigmaOfCharacterUnit, stickelbergerGalEquivZMod_sigmaOfExponent] at h'
  exact characterExponentOfUnit_injective (p := p) h'

lemma sigmaOfCharacterUnit_mem_characterSideFixingSubgroup (b : (ZMod (p - 1))ˣ) :
    sigmaOfCharacterUnit (p := p) L b ∈ characterSideFixingSubgroup (p := p) L := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  letI : IsGalois ℚ (additiveSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ))
      (K := ℚ) (L := additiveSubfield (L := L) (p := p))
  letI : Normal ℚ (additiveSubfield (L := L) (p := p)) := inferInstance
  rw [characterSideFixingSubgroup, IntermediateField.mem_fixingSubgroup_iff]
  have hrestr :
      AlgEquiv.restrictNormalHom (additiveSubfield (L := L) (p := p))
        (sigmaOfCharacterUnit (p := p) L b) = 1 := by
    apply (IsCyclotomicExtension.Rat.galEquivZMod p
      (additiveSubfield (L := L) (p := p))).injective
    change (IsCyclotomicExtension.Rat.galEquivZMod p (additiveSubfield (L := L) (p := p))
        ((sigmaOfCharacterUnit (p := p) L b).restrictNormal
          (additiveSubfield (L := L) (p := p))) =
      IsCyclotomicExtension.Rat.galEquivZMod p (additiveSubfield (L := L) (p := p)) 1)
    rw [IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
        (n := p * (p - 1)) (K := L)
        (F := additiveSubfield (L := L) (p := p))
        (h := Nat.dvd_mul_right p (p - 1))]
    ext
    rw [ZMod.unitsMap_val]
    rw [sigmaOfCharacterUnit, stickelbergerGalEquivZMod_sigmaOfExponent]
    simpa using characterExponentOfUnit_cast_p (p := p) b
  intro x hx
  have happly := congrArg
    (fun τ : Gal(additiveSubfield (L := L) (p := p) / ℚ) => τ ⟨x, hx⟩) hrestr
  have hcomm :
      (((sigmaOfCharacterUnit (p := p) L b).restrictNormal
          (additiveSubfield (L := L) (p := p)) ⟨x, hx⟩ :
            additiveSubfield (L := L) (p := p)) : L) =
        (sigmaOfCharacterUnit (p := p) L b) x :=
    AlgEquiv.restrictNormal_commutes
      (χ := sigmaOfCharacterUnit (p := p) L b)
      (E := additiveSubfield (L := L) (p := p)) ⟨x, hx⟩
  exact hcomm.symm.trans (congrArg Subtype.val happly)

/-- The map from `(ZMod (p - 1))ˣ` to the subgroup fixing the additive
subfield, given by the character-side cyclotomic lifts. -/
noncomputable def sigmaOfCharacterUnitToFixingSubgroup :
    (ZMod (p - 1))ˣ → characterSideFixingSubgroup (p := p) L := fun b ↦
    ⟨sigmaOfCharacterUnit (p := p) L b,
      sigmaOfCharacterUnit_mem_characterSideFixingSubgroup (p := p) (L := L) b⟩

theorem sigmaOfCharacterUnitToFixingSubgroup_bijective :
    Function.Bijective (sigmaOfCharacterUnitToFixingSubgroup (p := p) (L := L)) := by
  let f : (ZMod (p - 1))ˣ → characterSideFixingSubgroup (p := p) L :=
    sigmaOfCharacterUnitToFixingSubgroup (p := p) (L := L)
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois (S := ({p * (p - 1)} : Set ℕ)) (K := ℚ) (L := L)
  letI : Fintype (characterSideFixingSubgroup (p := p) L) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_, ?_⟩
  · intro b₁ b₂ h
    exact sigmaOfCharacterUnit_injective (p := p) (L := L) (congrArg Subtype.val h)
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      show Nat.card (characterSideFixingSubgroup (p := p) L) =
        Module.finrank (additiveSubfield (L := L) (p := p)) L by
          simpa [characterSideFixingSubgroup] using
            (IsGalois.card_fixingSubgroup_eq_finrank
              (F := ℚ) (E := L) (K := additiveSubfield (L := L) (p := p))),
      finrank_additiveSubfield (p := p) (L := L)]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- The character-side lifts parameterize exactly the subgroup fixing the
additive cyclotomic subfield. -/
noncomputable def sigmaOfCharacterUnitEquivFixingSubgroup :
    (ZMod (p - 1))ˣ ≃ characterSideFixingSubgroup (p := p) L :=
  Equiv.ofBijective
    (sigmaOfCharacterUnitToFixingSubgroup (p := p) (L := L))
    (sigmaOfCharacterUnitToFixingSubgroup_bijective (p := p) (L := L))

lemma exists_sigmaOfCharacterUnit_eq_of_mem_characterSideFixingSubgroup
    {σ : Gal(L/ℚ)} (hσ : σ ∈ characterSideFixingSubgroup (p := p) L) :
    ∃ b : (ZMod (p - 1))ˣ, sigmaOfCharacterUnit (p := p) L b = σ := by
  obtain ⟨b, hb⟩ :=
    (sigmaOfCharacterUnitEquivFixingSubgroup (p := p) (L := L)).surjective ⟨σ, hσ⟩
  exact ⟨b, congrArg Subtype.val hb⟩

/-- Every prime above `(p)` is in the character-side orbit of the distinguished
prime, because the character-side lifts exhaust the subgroup fixing the
additive cyclotomic subfield. -/
lemma exists_sigmaOfCharacterUnit_smul_distinguishedPrimeAboveP_eq
    {P : Ideal (𝓞 L)} (hP : P ∈ primesAboveP p L) :
    ∃ b : (ZMod (p - 1))ˣ,
      sigmaOfCharacterUnit (p := p) L b • distinguishedPrimeAboveP p L = P := by
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois (S := ({p * (p - 1)} : Set ℕ)) (K := ℚ) (L := L)
  letI : IsGaloisGroup Gal(L / ℚ) ℚ L := inferInstance
  letI : IsGaloisGroup (characterSideFixingSubgroup (p := p) L)
      (additiveSubfield (L := L) (p := p)) L := by
    change IsGaloisGroup ((additiveSubfield (L := L) (p := p)).fixingSubgroup)
      (additiveSubfield (L := L) (p := p)) L
    exact IsGaloisGroup.intermediateField
      (G := Gal(L / ℚ)) (K := ℚ) (L := L)
      (F := additiveSubfield (L := L) (p := p))
  letI : MulSemiringAction (characterSideFixingSubgroup (p := p) L) L := inferInstance
  letI : IsGaloisGroup (characterSideFixingSubgroup (p := p) L)
      (𝓞 (additiveSubfield (L := L) (p := p))) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (G := characterSideFixingSubgroup (p := p) L)
      (A := 𝓞 (additiveSubfield (L := L) (p := p))) (B := 𝓞 L)
      (K := additiveSubfield (L := L) (p := p)) (L := L)
  letI : MulSemiringAction (characterSideFixingSubgroup (p := p) L) (𝓞 L) := inferInstance
  have hP0_under :
      (distinguishedPrimeAboveP p L).under
          (𝓞 (additiveSubfield (L := L) (p := p))) =
        additiveZetaPrime (L := L) (p := p) :=
    primeAboveP_under_additiveSubfield_eq_additiveZetaPrime
      (p := p) (L := L) (distinguishedPrimeAboveP_mem (p := p) (L := L))
  have hP_under :
      P.under (𝓞 (additiveSubfield (L := L) (p := p))) =
        additiveZetaPrime (L := L) (p := p) :=
    primeAboveP_under_additiveSubfield_eq_additiveZetaPrime (p := p) (L := L) hP
  letI : (distinguishedPrimeAboveP p L).LiesOver
      (additiveZetaPrime (L := L) (p := p)) := by
    simp [Ideal.liesOver_iff, hP0_under]
  have hP_over : P ∈ Ideal.primesOver 𝔭 (𝓞 L) :=
    (mem_primesAboveP_iff (p := p) (L := L)).1 hP
  letI : P.IsPrime := hP_over.1
  letI : P.LiesOver (additiveZetaPrime (L := L) (p := p)) := by
    simp [Ideal.liesOver_iff, hP_under]
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (A := 𝓞 (additiveSubfield (L := L) (p := p))) (B := 𝓞 L)
    (p := additiveZetaPrime (L := L) (p := p))
    (P := distinguishedPrimeAboveP p L) (Q := P)
    (G := characterSideFixingSubgroup (p := p) L)
  rcases exists_sigmaOfCharacterUnit_eq_of_mem_characterSideFixingSubgroup
    (p := p) (L := L) (σ := σ.1) σ.2 with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rw [hb]; exact hσ

/-- The character-side orbit of the distinguished prime is exactly the full
finset of primes above `(p)`. -/
lemma characterSidePrimeOrbit_eq_primesAboveP :
    characterSidePrimeOrbit p L = primesAboveP p L := by
  classical
  apply Finset.Subset.antisymm
  · exact characterSidePrimeOrbit_subset_primesAboveP (p := p) (L := L)
  · intro P hP
    rcases exists_sigmaOfCharacterUnit_smul_distinguishedPrimeAboveP_eq
      (p := p) (L := L) hP with ⟨b, hb⟩
    exact (mem_characterSidePrimeOrbit_iff (p := p) (L := L)).2 ⟨b, hb⟩

/-- The number of primes of the Stickelberger field above `(p)` is `φ(p - 1)`. -/
lemma card_primesAboveP :
    Finset.card (primesAboveP p L) = Nat.totient (p - 1) := by
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois (S := ({p * (p - 1)} : Set ℕ)) (K := ℚ) (L := L)
  letI : IsGaloisGroup Gal(L / ℚ) ℤ (𝓞 L) := inferInstance
  have hp0 : (𝔭 : Ideal ℤ) ≠ ⊥ := by
    simp [hp.out.ne_zero]
  have hm : ¬ p ∣ p - 1 :=
    (hp.out.coprime_iff_not_dvd).mp (prime_coprime_pred (p := p))
  have hp_cast : (p : ZMod (p - 1)) = 1 := by
    have hmod : 1 ≡ p [MOD p - 1] := by
      rw [Nat.modEq_iff_dvd' hp.out.one_le]
    simpa using (ZMod.natCast_eq_natCast_iff p 1 (p - 1)).2 hmod.symm
  have hinertia : Ideal.inertiaDegIn 𝔭 (𝓞 L) = 1 := by
    rw [IsCyclotomicExtension.Rat.inertiaDegIn_eq
      (n := p * (p - 1)) (K := L) (p := p) (k := 0) (m := p - 1) (by simp) hm]
    simp [hp_cast]
  have hram : Ideal.ramificationIdxIn 𝔭 (𝓞 L) = p - 1 := by
    simpa using
      (IsCyclotomicExtension.Rat.ramificationIdxIn_eq
        (n := p * (p - 1)) (K := L) (p := p) (k := 0) (m := p - 1) (by simp) hm)
  have hmain :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (A := ℤ) (B := 𝓞 L) (G := Gal(L / ℚ)) (p := 𝔭)
  rw [← coe_primesAboveP (p := p) (L := L), Set.ncard_coe_finset, hram, hinertia, mul_one,
    show Nat.card Gal(L / ℚ) = Module.finrank ℚ L by
      simpa using (IsGalois.card_aut_eq_finrank (F := ℚ) (E := L)),
    IsCyclotomicExtension.Rat.finrank (k := p * (p - 1)) (K := L),
    Nat.totient_mul (prime_coprime_pred (p := p)), Nat.totient_prime hp.out] at hmain
  have hmain' :
      (p - 1) * Finset.card (primesAboveP p L) = (p - 1) * Nat.totient (p - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.out.one_lt) hmain'

/-- The character-side orbit has the expected cardinality `φ(p - 1)`. -/
lemma card_characterSidePrimeOrbit :
    Finset.card (characterSidePrimeOrbit p L) = Nat.totient (p - 1) := by
  rw [characterSidePrimeOrbit_eq_primesAboveP (p := p) (L := L)]
  exact card_primesAboveP (p := p) (L := L)

/-- The number of primes of the character subfield above `(p)` is `φ(p - 1)`. -/
lemma ncard_primesOver_characterSubfield_eq_totient_pred :
    (Ideal.primesOver 𝔭 (𝓞 (characterSubfield (L := L) (p := p)))).ncard =
      Nat.totient (p - 1) := by
  letI : IsGalois ℚ (characterSubfield (L := L) (p := p)) :=
    IsCyclotomicExtension.isGalois (S := ({p - 1} : Set ℕ))
      (K := ℚ) (L := characterSubfield (L := L) (p := p))
  letI : IsGaloisGroup Gal(characterSubfield (L := L) (p := p) / ℚ)
      ℤ (𝓞 (characterSubfield (L := L) (p := p))) := inferInstance
  have hp0 : (𝔭 : Ideal ℤ) ≠ ⊥ := by
    simp [hp.out.ne_zero]
  have hm : ¬ p ∣ p - 1 :=
    (hp.out.coprime_iff_not_dvd).mp (prime_coprime_pred (p := p))
  have hp_cast : (p : ZMod (p - 1)) = 1 := by
    have hmod : 1 ≡ p [MOD p - 1] := by
      rw [Nat.modEq_iff_dvd' hp.out.one_le]
    simpa using (ZMod.natCast_eq_natCast_iff p 1 (p - 1)).2 hmod.symm
  have hinertia :
      Ideal.inertiaDegIn 𝔭 (𝓞 (characterSubfield (L := L) (p := p))) = 1 := by
    rw [IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
      (p := p) (K := characterSubfield (L := L) (p := p)) hm]
    simp [hp_cast]
  have hram :
      Ideal.ramificationIdxIn 𝔭 (𝓞 (characterSubfield (L := L) (p := p))) = 1 := by
    simpa using
      (IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
        (p := p) (K := characterSubfield (L := L) (p := p)) hm)
  have hmain :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (A := ℤ) (B := 𝓞 (characterSubfield (L := L) (p := p)))
      (G := Gal(characterSubfield (L := L) (p := p) / ℚ))
      (p := 𝔭)
  rw [hram, hinertia, one_mul, mul_one,
    show Nat.card Gal(characterSubfield (L := L) (p := p) / ℚ) =
        Module.finrank ℚ (characterSubfield (L := L) (p := p)) by
          simpa using
            (IsGalois.card_aut_eq_finrank
              (F := ℚ) (E := characterSubfield (L := L) (p := p))),
    IsCyclotomicExtension.Rat.finrank
      (k := p - 1) (K := characterSubfield (L := L) (p := p))] at hmain
  simpa using hmain

/-- There is a unique prime of `𝓞_L` above the contracted character-side prime
of `distinguishedPrimeAboveP`. -/
lemma ncard_primesOver_characterSubfieldPrime_eq_one
    (Pchar : Ideal (𝓞 (characterSubfield (L := L) (p := p))))
    [Pchar.IsPrime] [Pchar.LiesOver 𝔭] :
    (Ideal.primesOver Pchar (𝓞 L)).ncard = 1 := by
  have hPchar : Pchar ∈ Ideal.primesOver 𝔭 (𝓞 (characterSubfield (L := L) (p := p))) :=
    ⟨inferInstance, inferInstance⟩
  haveI : Pchar.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPchar
  have hp0 : (𝔭 : Ideal ℤ) ≠ ⊥ := by
    simp [hp.out.ne_zero]
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
  have hmain :=
    Ideal.ncard_primesOver_mul_ncard_primesOver
      (A := ℤ)
      (B := 𝓞 (characterSubfield (L := L) (p := p)))
      (C := 𝓞 L)
      (p := 𝔭)
      (P := Pchar)
      (G := Gal(characterSubfield (L := L) (p := p) / ℚ))
      (GAC := Gal(L / ℚ))
      (GBC := ↥GBC)
  have hL :
      (Ideal.primesOver 𝔭 (𝓞 L)).ncard = Nat.totient (p - 1) := by
    rw [← coe_primesAboveP (p := p) (L := L), Set.ncard_coe_finset]
    exact card_primesAboveP (p := p) (L := L)
  rw [ncard_primesOver_characterSubfield_eq_totient_pred (p := p) (L := L), hL] at hmain
  exact Nat.eq_of_mul_eq_mul_left
    ((Nat.totient_pos).2 (Nat.sub_pos_of_lt hp.out.one_lt))
    (by simpa [one_mul] using hmain)

/-- There is a unique prime of `𝓞_L` above the contracted character-side prime
of `distinguishedPrimeAboveP`. -/
lemma ncard_primesOver_distinguishedPrimeAboveP_under_characterSubfield_eq_one :
    (Ideal.primesOver (distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L))
      (𝓞 L)).ncard = 1 := by
  let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  haveI : Pchar.IsPrime :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).1
  haveI : Pchar.LiesOver 𝔭 :=
    (distinguishedPrimeAboveP_under_characterSubfield_mem_primesOver
      (p := p) (L := L)).2
  simpa [Pchar] using
    ncard_primesOver_characterSubfieldPrime_eq_one (p := p) (L := L) Pchar

/-- The normalized boundary prime in `𝓞_L`, obtained by transporting the
distinguished prime by the character-side index that normalizes the contracted
character-side residue generator. -/
noncomputable def normalizedBoundaryPrime : Ideal (𝓞 L) :=
  characterSidePrimeMap (p := p) (L := L)
    (normalizedCharacterPrimeIndex (p := p) (L := L))

lemma normalizedBoundaryPrime_mem_characterSidePrimeOrbit :
    normalizedBoundaryPrime (p := p) (L := L) ∈ characterSidePrimeOrbit p L := by
  simpa [normalizedBoundaryPrime] using
    characterSidePrimeMap_mem_characterSidePrimeOrbit (p := p) (L := L)
      (normalizedCharacterPrimeIndex (p := p) (L := L))

lemma normalizedBoundaryPrime_under_characterSubfield :
    (normalizedBoundaryPrime (p := p) (L := L)).under
        (𝓞 (characterSubfield (L := L) (p := p))) =
      normalizedCharacterPrime (p := p) (L := L) := by
  simpa [normalizedBoundaryPrime, characterSidePrimeMap, normalizedCharacterPrime] using
    sigmaOfCharacterUnit_smul_distinguishedPrimeAboveP_under_characterSubfield_eq
      (p := p) (L := L) (normalizedCharacterPrimeIndex (p := p) (L := L))

lemma ncard_primesOver_normalizedCharacterPrime_eq_one :
    (Ideal.primesOver (normalizedCharacterPrime (p := p) (L := L))
      (𝓞 L)).ncard = 1 :=
  ncard_primesOver_characterSubfieldPrime_eq_one (p := p) (L := L)
    (normalizedCharacterPrime (p := p) (L := L))

instance normalizedBoundaryPrime_isPrime :
    (normalizedBoundaryPrime (p := p) (L := L)).IsPrime := by
  dsimp [normalizedBoundaryPrime, characterSidePrimeMap]
  infer_instance

lemma normalizedBoundaryPrime_mem_primesOver_normalizedCharacterPrime :
    normalizedBoundaryPrime (p := p) (L := L) ∈
      Ideal.primesOver (normalizedCharacterPrime (p := p) (L := L)) (𝓞 L) := by
  refine ⟨inferInstance, ?_⟩
  rw [Ideal.liesOver_iff, normalizedBoundaryPrime_under_characterSubfield (p := p) (L := L)]

lemma eq_normalizedBoundaryPrime_of_mem_primesOver_normalizedCharacterPrime
    {P : Ideal (𝓞 L)}
    (hP : P ∈ Ideal.primesOver (normalizedCharacterPrime (p := p) (L := L)) (𝓞 L)) :
    P = normalizedBoundaryPrime (p := p) (L := L) := by
  obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp
    (ncard_primesOver_normalizedCharacterPrime_eq_one (p := p) (L := L))
  have hPQ : P = Q := by
    simpa [hQ] using hP
  have hnormQ : normalizedBoundaryPrime (p := p) (L := L) = Q := by
    simpa [hQ] using
      normalizedBoundaryPrime_mem_primesOver_normalizedCharacterPrime (p := p) (L := L)
  exact hPQ.trans hnormQ.symm

/-- The additive-side lifts actually fix the distinguished prime above `(p)`. -/
lemma sigmaOfUnit_smul_distinguishedPrimeAboveP_eq (a : (ZMod p)ˣ) :
    sigmaOfUnit (p := p) L a • distinguishedPrimeAboveP p L =
      distinguishedPrimeAboveP p L := by
  let Pchar := distinguishedPrimeAboveP_under_characterSubfield (p := p) (L := L)
  have hcard :
      (Ideal.primesOver Pchar (𝓞 L)).ncard = 1 :=
    ncard_primesOver_distinguishedPrimeAboveP_under_characterSubfield_eq_one
      (p := p) (L := L)
  have hP0 :
      distinguishedPrimeAboveP p L ∈ Ideal.primesOver Pchar (𝓞 L) := by
    refine ⟨inferInstance, ?_⟩
    rw [Ideal.liesOver_iff]
  have ha :
      sigmaOfUnit (p := p) L a • distinguishedPrimeAboveP p L ∈
        Ideal.primesOver Pchar (𝓞 L) := by
    refine ⟨inferInstance, ?_⟩
    rw [Ideal.liesOver_iff,
      sigmaOfUnit_smul_distinguishedPrimeAboveP_under_characterSubfield_eq
        (p := p) (L := L) a]
  obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp hcard
  have hP0Q : distinguishedPrimeAboveP p L = Q := by
    simpa [hQ] using hP0
  have haQ : sigmaOfUnit (p := p) L a • distinguishedPrimeAboveP p L = Q := by
    simpa [hQ] using ha
  exact haQ.trans hP0Q.symm

/-- The additive orbit map is constant: every `sigmaOfUnit`-translate of
`distinguishedPrimeAboveP` is the distinguished prime itself. -/
lemma additivePrimeMap_eq_distinguishedPrimeAboveP (a : (ZMod p)ˣ) :
    additivePrimeMap (p := p) (L := L) a = distinguishedPrimeAboveP p L := by
  simpa [additivePrimeMap] using
    sigmaOfUnit_smul_distinguishedPrimeAboveP_eq (p := p) (L := L) a

/-- The exponent of `sigma_a(P₀)` coincides with the distinguished-prime
exponent, because `sigma_a(P₀) = P₀`. -/
lemma sigmaOfUnitPrimeExponent_eq_distinguishedPrimeExponent
    (a : (ZMod p)ˣ) (χ : DirichletCharacter ℂ p) :
    sigmaOfUnitPrimeExponent (p := p) (L := L) a χ =
      distinguishedPrimeExponent (p := p) (L := L) χ := by
  unfold sigmaOfUnitPrimeExponent distinguishedPrimeExponent primeAbovePExponent
  rw [sigmaOfUnit_smul_distinguishedPrimeAboveP_eq (p := p) (L := L) a]

/-- The additive prime orbit is the singleton `{P₀}`. -/
lemma additivePrimeOrbit_eq_singleton :
    additivePrimeOrbit p L = {distinguishedPrimeAboveP p L} := by
  classical
  ext P
  constructor
  · intro hP
    rcases (mem_additivePrimeOrbit_iff (p := p) (L := L)).1 hP with ⟨a, rfl⟩
    simp [sigmaOfUnit_smul_distinguishedPrimeAboveP_eq (p := p) (L := L) a]
  · intro hP
    rcases Finset.mem_singleton.mp hP with rfl
    simpa [additivePrimeMap_eq_distinguishedPrimeAboveP (p := p) (L := L) 1] using
      additivePrimeMap_mem_additivePrimeOrbit (p := p) (L := L) (1 : (ZMod p)ˣ)

/-- The additive exponent vector is constant with value
`distinguishedPrimeExponent χ`. -/
lemma additiveExponentVector_eq_distinguishedPrimeExponent
    (χ : DirichletCharacter ℂ p) :
    additiveExponentVector (p := p) (L := L) χ =
      fun _ ↦ distinguishedPrimeExponent (p := p) (L := L) χ := by
  funext a
  exact sigmaOfUnitPrimeExponent_eq_distinguishedPrimeExponent
    (p := p) (L := L) a χ

end Assembly

end BernoulliRegular
