module

public import BernoulliRegular.GaussSum.QuadraticEndpoint
public import BernoulliRegular.HMinus.LValueReduction.GaussGoal

/-!
# Pairing odd characters in the raw Gauss product

This file handles the inversion-pair partition arguments for the raw odd
Gauss-product, separately in the `p ≡ 1 [ZMOD 4]` and `p ≡ 3 [ZMOD 4]`
branches.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BernoulliRegular

section PairingDefs

variable (p : ℕ)

/-- Pair odd characters modulo inversion when `p ≡ 1 [ZMOD 4]`. -/
def oddCharacterInvSetoid : Setoid (DirichletCharacter ℂ p) where
  r χ ψ := χ = ψ ∨ χ = ψ⁻¹
  iseqv := by
    constructor
    · intro χ
      exact Or.inl rfl
    · intro χ ψ h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        simp [h]
    · intro χ ψ ϕ hχψ hψϕ
      rcases hχψ with hχψ | hχψ <;> rcases hψϕ with hψϕ | hψϕ
      · exact Or.inl (hχψ.trans hψϕ)
      · exact Or.inr (hχψ.trans hψϕ)
      · exact Or.inr <| by simpa [hψϕ] using hχψ
      · left
        simpa [hψϕ] using hχψ

noncomputable def oddCharacterInvClass (χ : DirichletCharacter ℂ p) :
    Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.filter (fun ψ ↦
    Quotient.mk (oddCharacterInvSetoid (p := p)) ψ =
      Quotient.mk (oddCharacterInvSetoid (p := p)) χ) (oddCharacters (p := p))

noncomputable def oddCharacterInvPair (χ : DirichletCharacter ℂ p) :
    Finset (DirichletCharacter ℂ p) := by
  classical
  exact {χ, χ⁻¹}

theorem odd_inv_odd {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) : (χ⁻¹).Odd := by
  rw [DirichletCharacter.Odd] at hχ_odd ⊢
  rw [MulChar.inv_apply_eq_inv', hχ_odd]
  norm_num

theorem oddCharacterInvClass_eq_pair
    {χ : DirichletCharacter ℂ p} (hχ : χ ∈ oddCharacters (p := p)) :
    oddCharacterInvClass (p := p) χ = oddCharacterInvPair (p := p) χ := by
  classical
  apply Finset.ext
  intro ψ
  constructor
  · intro hψ
    have hψ' :
        ψ ∈ Finset.filter (fun ψ ↦
          Quotient.mk (oddCharacterInvSetoid (p := p)) ψ =
            Quotient.mk (oddCharacterInvSetoid (p := p)) χ) (oddCharacters (p := p)) := by
      simpa [oddCharacterInvClass] using hψ
    have hrel : ψ = χ ∨ ψ = χ⁻¹ := by
      exact Quotient.exact (Finset.mem_filter.mp hψ').2
    simpa [oddCharacterInvPair, Finset.mem_insert, Finset.mem_singleton] using hrel
  · intro hψ
    have hψ' :
        ψ ∈ ({χ, χ⁻¹} : Finset (DirichletCharacter ℂ p)) := by
      simpa [oddCharacterInvPair] using hψ
    rcases Finset.mem_insert.mp hψ' with rfl | hψ
    · simpa [oddCharacterInvClass] using Finset.mem_filter.mpr ⟨hχ, rfl⟩
    · have hψeq : ψ = χ⁻¹ := by
        simpa [Finset.mem_singleton] using hψ
      subst ψ
      have hχinv : χ⁻¹ ∈ oddCharacters (p := p) := inv_mem_oddCharacters (p := p) hχ
      have :
          χ⁻¹ ∈ Finset.filter (fun ψ ↦
            Quotient.mk (oddCharacterInvSetoid (p := p)) ψ =
              Quotient.mk (oddCharacterInvSetoid (p := p)) χ) (oddCharacters (p := p)) := by
        refine Finset.mem_filter.mpr ⟨hχinv, ?_⟩
        exact Quotient.sound (show (oddCharacterInvSetoid (p := p)).r χ⁻¹ χ by
          right
          rfl)
      simpa [oddCharacterInvClass] using this

end PairingDefs

section GaussPairing

variable (p : ℕ) [hp : Fact p.Prime]

theorem oddCharacterInvClass_card
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 1) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ oddCharacters (p := p)) :
    (oddCharacterInvClass (p := p) χ).card = 2 := by
  classical
  have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ).2
  have hχ_ne : χ ≠ χ⁻¹ :=
    odd_character_ne_inv_of_mod_four_eq_one (p := p) hp_odd' hp₄ hχ_odd
  rw [oddCharacterInvClass_eq_pair (p := p) hχ]
  simp [oddCharacterInvPair, hχ_ne]

/-- **T023d4**: In the `p ≡ 1 [ZMOD 4]` case, the odd Gauss product is the
pair product `(-(p : ℂ))` repeated once for each inversion class. -/
theorem rawGaussProduct_of_mod_four_eq_one
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 1) :
    Finset.prod (oddCharacters (p := p))
        (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) =
      (-(p : ℂ)) ^ ((p - 1) / 4) := by
  classical
  let R := oddCharacterInvSetoid (p := p)
  let q : Finset (Quotient R) := (oddCharacters (p := p)).image (Quotient.mk R)
  have hpartition :
      Finset.prod (oddCharacters (p := p)) (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) =
        ∏ xbar ∈ q, ∏ ψ ∈ oddCharacters (p := p) with Quotient.mk R ψ = xbar,
          gaussSum ψ (ZMod.stdAddChar (N := p)) := by
    simpa [q, R] using
      (Finset.prod_partition (s := oddCharacters (p := p)) (R := R)
        (f := fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))))
  have hqcard :
      q.card = (p - 1) / 4 := by
    have hcard :
        (oddCharacters (p := p)).card =
          ∑ xbar ∈ q, (Finset.filter (fun ψ ↦ Quotient.mk R ψ = xbar)
            (oddCharacters (p := p))).card := by
      simpa [q, R] using
        (Finset.card_eq_sum_card_image (f := Quotient.mk R) (s := oddCharacters (p := p)))
    have hcard' :
        (oddCharacters (p := p)).card = q.card * 2 := by
      calc
        (oddCharacters (p := p)).card =
            ∑ xbar ∈ q, (Finset.filter (fun ψ ↦ Quotient.mk R ψ = xbar)
              (oddCharacters (p := p))).card := hcard
        _ = ∑ xbar ∈ q, (2 : ℕ) := by
              refine Finset.sum_congr rfl ?_
              intro xbar hxbar
              rcases Finset.mem_image.mp hxbar with ⟨χ, hχ, rfl⟩
              simpa [R, oddCharacterInvClass] using
                (oddCharacterInvClass_card (p := p) hp_odd' hp₄ hχ)
        _ = q.card * 2 :=
              Finset.sum_const_nat (s := q) (m := 2) (f := fun _ ↦ 2)
                (by intro _ _; rfl)
    rw [card_oddCharacters (p := p) hp_odd'] at hcard'
    omega
  rw [hpartition]
  calc
    ∏ xbar ∈ q, ∏ ψ ∈ oddCharacters (p := p) with Quotient.mk R ψ = xbar,
        gaussSum ψ (ZMod.stdAddChar (N := p)) =
      ∏ xbar ∈ q, (-(p : ℂ)) := by
        refine Finset.prod_congr rfl ?_
        intro xbar hxbar
        rcases Finset.mem_image.mp hxbar with ⟨χ, hχ, rfl⟩
        have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ).2
        have hχ_ne : χ ≠ χ⁻¹ :=
          odd_character_ne_inv_of_mod_four_eq_one (p := p) hp_odd' hp₄ hχ_odd
        rw [show Finset.filter (fun ψ ↦ Quotient.mk R ψ = Quotient.mk R χ)
            (oddCharacters (p := p)) = oddCharacterInvClass (p := p) χ by
              rfl]
        rw [oddCharacterInvClass_eq_pair (p := p) hχ]
        change ∏ ψ ∈ ({χ, χ⁻¹} : Finset (DirichletCharacter ℂ p)),
            gaussSum ψ (ZMod.stdAddChar (N := p)) = -(p : ℂ)
        rw [Finset.prod_insert]
        · simp [odd_gaussSum_mul_gaussSum_inv_stdAddChar (p := p) hχ_odd]
        · simpa [oddCharacterInvPair, Finset.mem_singleton] using hχ_ne
    _ = (-(p : ℂ)) ^ q.card := by
          rw [Finset.prod_const]
    _ = (-(p : ℂ)) ^ ((p - 1) / 4) := by
          rw [hqcard]

noncomputable def oddCharactersWithoutQuadratic :
    Finset (DirichletCharacter ℂ p) := by
  classical
  exact (oddCharacters (p := p)).erase (quadraticCharComplex p)

theorem quadraticCharComplex_mem_oddCharacters_of_mod_four_eq_three
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 3) :
    quadraticCharComplex p ∈ oddCharacters (p := p) := by
  classical
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, quadraticCharComplex_odd_of_mod_four_eq_three_lvalue (p := p) hp_odd' hp₄⟩

theorem card_oddCharactersWithoutQuadratic_of_mod_four_eq_three
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 3) :
    (oddCharactersWithoutQuadratic (p := p)).card = (p - 3) / 2 := by
  classical
  rw [oddCharactersWithoutQuadratic]
  rw [Finset.card_erase_of_mem
    (quadraticCharComplex_mem_oddCharacters_of_mod_four_eq_three (p := p) hp_odd' hp₄)]
  rw [card_oddCharacters (p := p) hp_odd']
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨k, hk⟩
  omega

theorem inv_mem_oddCharactersWithoutQuadratic {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ oddCharactersWithoutQuadratic (p := p)) :
    χ⁻¹ ∈ oddCharactersWithoutQuadratic (p := p) := by
  classical
  rcases Finset.mem_erase.mp hχ with ⟨hχ_ne_quad, hχ_mem⟩
  refine Finset.mem_erase.mpr ⟨?_, inv_mem_oddCharacters (p := p) hχ_mem⟩
  intro hχinv_quad
  apply hχ_ne_quad
  calc
    χ = (χ⁻¹)⁻¹ := by simp
    _ = (quadraticCharComplex p)⁻¹ := by simp [hχinv_quad]
    _ = quadraticCharComplex p := by simp [quadraticCharComplex_inv (p := p)]

noncomputable def oddCharacterInvClassWithoutQuadratic
    (χ : DirichletCharacter ℂ p) : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.filter (fun ψ ↦
    Quotient.mk (oddCharacterInvSetoid (p := p)) ψ =
      Quotient.mk (oddCharacterInvSetoid (p := p)) χ) (oddCharactersWithoutQuadratic (p := p))

theorem oddCharacterInvClassWithoutQuadratic_eq_pair
    {χ : DirichletCharacter ℂ p} (hχ : χ ∈ oddCharactersWithoutQuadratic (p := p)) :
    oddCharacterInvClassWithoutQuadratic (p := p) χ = oddCharacterInvPair (p := p) χ := by
  classical
  apply Finset.ext
  intro ψ
  constructor
  · intro hψ
    have hψ' :
        ψ ∈ Finset.filter (fun ψ ↦
          Quotient.mk (oddCharacterInvSetoid (p := p)) ψ =
            Quotient.mk (oddCharacterInvSetoid (p := p)) χ)
          (oddCharactersWithoutQuadratic (p := p)) := by
      simpa [oddCharacterInvClassWithoutQuadratic] using hψ
    have hrel : ψ = χ ∨ ψ = χ⁻¹ := by
      exact Quotient.exact (Finset.mem_filter.mp hψ').2
    simpa [oddCharacterInvPair, Finset.mem_insert, Finset.mem_singleton] using hrel
  · intro hψ
    have hψ' :
        ψ ∈ ({χ, χ⁻¹} : Finset (DirichletCharacter ℂ p)) := by
      simpa [oddCharacterInvPair] using hψ
    rcases Finset.mem_insert.mp hψ' with rfl | hψ
    · simpa [oddCharacterInvClassWithoutQuadratic] using Finset.mem_filter.mpr ⟨hχ, rfl⟩
    · have hψeq : ψ = χ⁻¹ := by
        simpa [Finset.mem_singleton] using hψ
      subst ψ
      have hχinv : χ⁻¹ ∈ oddCharactersWithoutQuadratic (p := p) :=
        inv_mem_oddCharactersWithoutQuadratic (p := p) hχ
      have :
          χ⁻¹ ∈ Finset.filter (fun ψ ↦
            Quotient.mk (oddCharacterInvSetoid (p := p)) ψ =
              Quotient.mk (oddCharacterInvSetoid (p := p)) χ)
            (oddCharactersWithoutQuadratic (p := p)) := by
        refine Finset.mem_filter.mpr ⟨hχinv, ?_⟩
        exact Quotient.sound (show (oddCharacterInvSetoid (p := p)).r χ⁻¹ χ by
          right
          rfl)
      simpa [oddCharacterInvClassWithoutQuadratic] using this

theorem oddCharacterInvClassWithoutQuadratic_card
    (hp_odd' : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ oddCharactersWithoutQuadratic (p := p)) :
    (oddCharacterInvClassWithoutQuadratic (p := p) χ).card = 2 := by
  classical
  rcases Finset.mem_erase.mp hχ with ⟨hχ_ne_quad, hχ_mem⟩
  have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ_mem).2
  have hχ_ne : χ ≠ χ⁻¹ := by
    intro hχself
    have hquad :
        χ = quadraticCharComplex p :=
      odd_selfInverse_character_eq_quadratic (p := p) hp_odd' hχ_odd hχself
    exact hχ_ne_quad hquad
  rw [oddCharacterInvClassWithoutQuadratic_eq_pair (p := p) hχ]
  simp [oddCharacterInvPair, hχ_ne]

theorem rawGaussProduct_withoutQuadratic_of_mod_four_eq_three
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 3) :
    Finset.prod (oddCharactersWithoutQuadratic (p := p))
        (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) =
      (-(p : ℂ)) ^ ((p - 3) / 4) := by
  classical
  let R := oddCharacterInvSetoid (p := p)
  let q : Finset (Quotient R) :=
    (oddCharactersWithoutQuadratic (p := p)).image (Quotient.mk R)
  have hpartition :
      Finset.prod (oddCharactersWithoutQuadratic (p := p))
          (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) =
        ∏ xbar ∈ q,
          ∏ ψ ∈ oddCharactersWithoutQuadratic (p := p) with Quotient.mk R ψ = xbar,
            gaussSum ψ (ZMod.stdAddChar (N := p)) := by
    simpa [q, R] using
      (Finset.prod_partition (s := oddCharactersWithoutQuadratic (p := p)) (R := R)
        (f := fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))))
  have hqcard :
      q.card = (p - 3) / 4 := by
    have hcard :
        (oddCharactersWithoutQuadratic (p := p)).card =
          ∑ xbar ∈ q, (Finset.filter (fun ψ ↦ Quotient.mk R ψ = xbar)
            (oddCharactersWithoutQuadratic (p := p))).card := by
      simpa [q, R] using
        (Finset.card_eq_sum_card_image
          (f := Quotient.mk R) (s := oddCharactersWithoutQuadratic (p := p)))
    have hcard' :
        (oddCharactersWithoutQuadratic (p := p)).card = q.card * 2 := by
      calc
        (oddCharactersWithoutQuadratic (p := p)).card =
            ∑ xbar ∈ q, (Finset.filter (fun ψ ↦ Quotient.mk R ψ = xbar)
              (oddCharactersWithoutQuadratic (p := p))).card := hcard
        _ = ∑ xbar ∈ q, (2 : ℕ) := by
              refine Finset.sum_congr rfl ?_
              intro xbar hxbar
              rcases Finset.mem_image.mp hxbar with ⟨χ, hχ, rfl⟩
              simpa [R, oddCharacterInvClassWithoutQuadratic] using
                (oddCharacterInvClassWithoutQuadratic_card (p := p) hp_odd' hχ)
        _ = q.card * 2 :=
              Finset.sum_const_nat (s := q) (m := 2) (f := fun _ ↦ 2)
                (by intro _ _; rfl)
    rw [card_oddCharactersWithoutQuadratic_of_mod_four_eq_three (p := p) hp_odd' hp₄] at hcard'
    omega
  rw [hpartition]
  calc
    ∏ xbar ∈ q,
        ∏ ψ ∈ oddCharactersWithoutQuadratic (p := p) with Quotient.mk R ψ = xbar,
          gaussSum ψ (ZMod.stdAddChar (N := p)) =
      ∏ xbar ∈ q, (-(p : ℂ)) := by
        refine Finset.prod_congr rfl ?_
        intro xbar hxbar
        rcases Finset.mem_image.mp hxbar with ⟨χ, hχ, rfl⟩
        have hχ_odd : χ.Odd := (Finset.mem_filter.mp (Finset.mem_erase.mp hχ).2).2
        have hχ_ne : χ ≠ χ⁻¹ := by
          intro hχself
          rcases Finset.mem_erase.mp hχ with ⟨hχ_ne_quad, hχ_mem⟩
          have hquad :
              χ = quadraticCharComplex p :=
            odd_selfInverse_character_eq_quadratic (p := p) hp_odd'
              (Finset.mem_filter.mp hχ_mem).2 hχself
          exact hχ_ne_quad hquad
        rw [show Finset.filter (fun ψ ↦ Quotient.mk R ψ = Quotient.mk R χ)
            (oddCharactersWithoutQuadratic (p := p)) =
              oddCharacterInvClassWithoutQuadratic (p := p) χ by rfl]
        rw [oddCharacterInvClassWithoutQuadratic_eq_pair (p := p) hχ]
        change ∏ ψ ∈ ({χ, χ⁻¹} : Finset (DirichletCharacter ℂ p)),
            gaussSum ψ (ZMod.stdAddChar (N := p)) = -(p : ℂ)
        rw [Finset.prod_insert]
        · simp [odd_gaussSum_mul_gaussSum_inv_stdAddChar (p := p) hχ_odd]
        · simpa [oddCharacterInvPair, Finset.mem_singleton] using hχ_ne
    _ = (-(p : ℂ)) ^ q.card := by
          rw [Finset.prod_const]
    _ = (-(p : ℂ)) ^ ((p - 3) / 4) := by
          rw [hqcard]

/-- **T023d5**: In the `p ≡ 3 [ZMOD 4]` case, isolate the quadratic character
and pair the remaining odd characters by inversion. -/
theorem rawGaussProduct_of_mod_four_eq_three
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 3) :
    Finset.prod (oddCharacters (p := p))
        (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) =
      (Complex.I * (Real.sqrt p : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) := by
  classical
  have hquad_mem :
      quadraticCharComplex p ∈ oddCharacters (p := p) :=
    quadraticCharComplex_mem_oddCharacters_of_mod_four_eq_three (p := p) hp_odd' hp₄
  calc
    Finset.prod (oddCharacters (p := p))
        (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) =
      gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) *
        Finset.prod (oddCharactersWithoutQuadratic (p := p))
          (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) := by
            symm
            simpa [oddCharactersWithoutQuadratic] using
              (Finset.mul_prod_erase (s := oddCharacters (p := p))
                (f := fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) hquad_mem)
    _ =
      gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) *
        (-(p : ℂ)) ^ ((p - 3) / 4) := by
          rw [rawGaussProduct_withoutQuadratic_of_mod_four_eq_three (p := p) hp_odd' hp₄]
    _ = (Complex.I * (Real.sqrt p : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) := by
          rw [show gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
            Complex.I * (Real.sqrt p : ℂ) by
              simpa [quadraticCharComplex] using
                gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_three (p := p) hp_odd' hp₄]

end GaussPairing

end BernoulliRegular
