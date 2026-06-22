module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import BernoulliRegular.GaussSum.SignInvariant.Operator

/-!
# Determinant-ready block decomposition scaffolding for quadratic Gauss sums

This file packages the ambient `δ₀ +` character basis used to reorganize the
normalized finite Fourier transform into the trivial block, non-self-dual
character-pair blocks, and the surviving quadratic line.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

/-- The delta function supported at `0`. -/
def deltaZeroFunction : ZMod p → ℂ :=
  Pi.basisFun ℂ (ZMod p) (0 : ZMod p)

/-- Restrict a function on `ZMod p` to the unit group. -/
def restrictUnitsLinear : (ZMod p → ℂ) →ₗ[ℂ] ((ZMod p)ˣ → ℂ) where
  toFun Φ u := Φ u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- View a Dirichlet character as a monoid homomorphism on the unit group with
values in `ℂ`. -/
def dirichletCharacterUnitMonoidHom (χ : DirichletCharacter ℂ p) : (ZMod p)ˣ →* ℂ :=
  (Units.coeHom ℂ).comp χ.toUnitHom

@[simp] theorem dirichletCharacterUnitMonoidHom_apply
    (χ : DirichletCharacter ℂ p) (u : (ZMod p)ˣ) :
    dirichletCharacterUnitMonoidHom (p := p) χ u = χ u := by
  simp [dirichletCharacterUnitMonoidHom]

theorem dirichletCharacterUnitMonoidHom_injective :
    Function.Injective (dirichletCharacterUnitMonoidHom (p := p)) := by
  intro χ ψ hχψ
  apply (DirichletCharacter.toUnitHom_inj (χ := χ) (ψ := ψ)).mp
  ext u
  have hcoe : ((χ.toUnitHom u : ℂˣ) : ℂ) = ((ψ.toUnitHom u : ℂˣ) : ℂ) :=
    DFunLike.congr_fun hχψ u
  exact hcoe

/-- Dirichlet characters are linearly independent on the unit group. -/
theorem linearIndependent_dirichletCharactersOnUnits :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ p =>
      (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ)) :=
  (linearIndependent_monoidHom ((ZMod p)ˣ) ℂ).comp
      (dirichletCharacterUnitMonoidHom (p := p))
      (dirichletCharacterUnitMonoidHom_injective (p := p))

/-- Dirichlet characters are linearly independent as functions on `ZMod p`. -/
theorem linearIndependent_dirichletCharacters :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ p => (χ : ZMod p → ℂ)) := by
  apply LinearIndependent.of_comp (restrictUnitsLinear (p := p))
  have h := linearIndependent_dirichletCharactersOnUnits (p := p)
  convert h using 1
  funext χ u
  simp [restrictUnitsLinear, dirichletCharacterUnitMonoidHom_apply]

/-- Evaluation at `0`. -/
def evalAtZeroLinear : (ZMod p → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ := Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dirichletCharacter_apply_zero (χ : DirichletCharacter ℂ p) :
    χ (0 : ZMod p) = 0 := by
  simpa using MulChar.map_nonunit χ (a := (0 : ZMod p)) (by simp)

theorem span_dirichletCharacters_le_ker_evalAtZero :
    Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ p => (χ : ZMod p → ℂ)) ≤
      LinearMap.ker (evalAtZeroLinear (p := p)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨χ, rfl⟩
  change evalAtZeroLinear (p := p) ((χ : DirichletCharacter ℂ p) : ZMod p → ℂ) = 0
  simp [evalAtZeroLinear, dirichletCharacter_apply_zero]

theorem deltaZero_not_mem_span_dirichletCharacters :
    deltaZeroFunction (p := p) ∉
      Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ p => (χ : ZMod p → ℂ)) := by
  intro hdelta
  have hker : deltaZeroFunction (p := p) ∈ LinearMap.ker (evalAtZeroLinear (p := p)) :=
    span_dirichletCharacters_le_ker_evalAtZero (p := p) hdelta
  rw [LinearMap.mem_ker] at hker
  simp [evalAtZeroLinear, deltaZeroFunction] at hker

/-- The ambient family consisting of `δ₀` together with all Dirichlet
characters. -/
def deltaZeroDirichletCharacterFamily : Option (DirichletCharacter ℂ p) → (ZMod p → ℂ) :=
  fun o => Option.casesOn' o (deltaZeroFunction (p := p)) fun χ => (χ : ZMod p → ℂ)

theorem linearIndependent_deltaZeroDirichletCharacterFamily :
    LinearIndependent ℂ (deltaZeroDirichletCharacterFamily (p := p)) :=
  (linearIndependent_dirichletCharacters (p := p)).option
      (x := deltaZeroFunction (p := p))
      (deltaZero_not_mem_span_dirichletCharacters (p := p))

/-- A basis of the ambient function space given by `δ₀` together with all
Dirichlet characters. -/
def deltaZeroDirichletCharacterBasis :
    Module.Basis (Option (DirichletCharacter ℂ p)) ℂ (ZMod p → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_deltaZeroDirichletCharacterFamily (p := p)) <| by
      rw [Fintype.card_option, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
        Nat.totient_prime hp.out]
      rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
      exact Nat.sub_add_cancel hp.out.one_le

@[simp] theorem deltaZeroDirichletCharacterBasis_apply_none :
    deltaZeroDirichletCharacterBasis (p := p) none = deltaZeroFunction (p := p) := by
  rw [deltaZeroDirichletCharacterBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

@[simp] theorem deltaZeroDirichletCharacterBasis_apply_some
    (χ : DirichletCharacter ℂ p) :
    deltaZeroDirichletCharacterBasis (p := p) (some χ) = (χ : ZMod p → ℂ) := by
  rw [deltaZeroDirichletCharacterBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- The `δ₀/1` block singled out by the raw DFT formulas. -/
def trivialBlock : Submodule ℂ (ZMod p → ℂ) :=
  Submodule.span ℂ (Set.range ![deltaZeroFunction (p := p), (fun _ : ZMod p => (1 : ℂ))])

/-- The same trivial block, but generated by `δ₀` and the trivial Dirichlet
character. This generating set aligns with `deltaZeroDirichletCharacterBasis`. -/
def trivialCharacterBlock : Submodule ℂ (ZMod p → ℂ) :=
  Submodule.span ℂ
    (Set.range ![deltaZeroFunction (p := p), ((1 : DirichletCharacter ℂ p) : ZMod p → ℂ)])

theorem deltaZero_mem_trivialBlock :
    deltaZeroFunction (p := p) ∈ trivialBlock (p := p) :=
  Submodule.subset_span ⟨0, by simp⟩

theorem constOne_mem_trivialBlock :
    (fun _ : ZMod p => (1 : ℂ)) ∈ trivialBlock (p := p) :=
  Submodule.subset_span ⟨1, by simp⟩

theorem constOne_eq_deltaZero_add_trivialCharacter :
    (fun _ : ZMod p => (1 : ℂ)) =
      deltaZeroFunction (p := p) + ((1 : DirichletCharacter ℂ p) : ZMod p → ℂ) := by
  ext x
  by_cases hx : x = 0
  · subst hx
    simp [deltaZeroFunction]
  · have htriv : (1 : DirichletCharacter ℂ p) x = 1 :=
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    simp [deltaZeroFunction, hx, htriv]

theorem trivialCharacter_eq_constOne_sub_deltaZero :
    (((1 : DirichletCharacter ℂ p) : ZMod p → ℂ)) =
      (fun _ : ZMod p => (1 : ℂ)) - deltaZeroFunction (p := p) :=
  eq_sub_of_add_eq' (constOne_eq_deltaZero_add_trivialCharacter (p := p)).symm

theorem trivialBlock_eq_trivialCharacterBlock :
    trivialBlock (p := p) = trivialCharacterBlock (p := p) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨0, by simp⟩
    · rw [constOne_eq_deltaZero_add_trivialCharacter (p := p)]
      exact (trivialCharacterBlock (p := p)).add_mem
        (Submodule.subset_span ⟨0, by simp⟩) (Submodule.subset_span ⟨1, by simp⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact deltaZero_mem_trivialBlock (p := p)
    · rw [trivialCharacter_eq_constOne_sub_deltaZero (p := p)]
      exact (trivialBlock (p := p)).sub_mem
        (constOne_mem_trivialBlock (p := p))
        (deltaZero_mem_trivialBlock (p := p))

theorem trivialCharacter_mem_trivialBlock :
    (((1 : DirichletCharacter ℂ p) : ZMod p → ℂ)) ∈ trivialBlock (p := p) := by
  rw [trivialBlock_eq_trivialCharacterBlock (p := p)]
  exact Submodule.subset_span ⟨1, by simp⟩

theorem normalizedDft_deltaZero :
    normalizedDft p (deltaZeroFunction (p := p)) =
      (Real.sqrt p : ℂ)⁻¹ • (fun _ : ZMod p => (1 : ℂ)) := by
  ext x
  rw [normalizedDft_apply, deltaZeroFunction, dft_deltaZero_eq_constOne]
  simp [smul_eq_mul]

theorem normalizedDft_constOne :
    normalizedDft p (fun _ : ZMod p => (1 : ℂ)) =
      (((Real.sqrt p : ℂ)⁻¹) * p) • deltaZeroFunction (p := p) := by
  ext x
  rw [normalizedDft_apply, congrFun (dft_constOne_eq_prime_smul_deltaZero (p := p)) x]
  simp [deltaZeroFunction, smul_eq_mul, mul_assoc]

theorem normalizedDft_maps_trivialBlock {f : ZMod p → ℂ}
    (hf : f ∈ trivialBlock (p := p)) :
    normalizedDft p f ∈ trivialBlock (p := p) := by
  refine Submodule.span_induction
    (p := fun g _ => normalizedDft p g ∈ trivialBlock (p := p)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · change normalizedDft p (deltaZeroFunction (p := p)) ∈ trivialBlock (p := p)
      rw [normalizedDft_deltaZero (p := p)]
      exact Submodule.smul_mem (trivialBlock (p := p)) _ (constOne_mem_trivialBlock (p := p))
    · change normalizedDft p (fun _ : ZMod p => (1 : ℂ)) ∈ trivialBlock (p := p)
      rw [normalizedDft_constOne (p := p)]
      exact Submodule.smul_mem (trivialBlock (p := p)) _ (deltaZero_mem_trivialBlock (p := p))
  · simp
  · intro g h hg hh hgm hhm
    simpa using (trivialBlock (p := p)).add_mem hgm hhm
  · intro a g hg hgm
    simpa using (trivialBlock (p := p)).smul_mem a hgm

theorem normalizedDft_maps_characterPairSubmodule {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) {f : ZMod p → ℂ} (hf : f ∈ characterPairSubmodule (p := p) χ) :
    normalizedDft p f ∈ characterPairSubmodule (p := p) χ := by
  have hdft : ZMod.dft f ∈ characterPairSubmodule (p := p) χ :=
    dft_maps_characterPairSubmodule (p := p) (χ := χ) hχ hf
  rw [show normalizedDft p f = ((Real.sqrt p : ℂ)⁻¹) • ZMod.dft f by
    ext x
    simp [normalizedDft_apply, smul_eq_mul]]
  exact Submodule.smul_mem (characterPairSubmodule (p := p) χ) _ hdft

/-- The surviving `1 × 1` block. -/
def quadraticCharacterLine : Submodule ℂ (ZMod p → ℂ) :=
  Submodule.span ℂ {((quadraticCharComplex p : DirichletCharacter ℂ p) : ZMod p → ℂ)}

theorem quadraticCharComplex_mem_quadraticCharacterLine :
    ((quadraticCharComplex p : DirichletCharacter ℂ p) : ZMod p → ℂ) ∈
      quadraticCharacterLine (p := p) :=
  Submodule.mem_span_singleton_self _

theorem normalizedDft_quadraticCharComplex_eq_scalar_smul (hp₂ : p ≠ 2) :
    normalizedDft p (quadraticCharComplex p) =
      (((Real.sqrt p : ℂ)⁻¹) *
        (quadraticCharComplex p (-1) *
          gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)))) •
        ((quadraticCharComplex p : DirichletCharacter ℂ p) : ZMod p → ℂ) := by
  ext x
  rw [normalizedDft_apply,
    congrFun
      (dft_eq_scalar_smul_inv_character (p := p) (χ := quadraticCharComplex p)
        (quadraticCharComplex_ne_one (p := p) hp₂)) x]
  simp [quadraticCharComplex_inv (p := p), smul_eq_mul, mul_left_comm, mul_comm]

theorem normalizedDft_maps_quadraticCharacterLine (hp₂ : p ≠ 2) {f : ZMod p → ℂ}
    (hf : f ∈ quadraticCharacterLine (p := p)) :
    normalizedDft p f ∈ quadraticCharacterLine (p := p) := by
  refine Submodule.span_induction
    (p := fun g _ => normalizedDft p g ∈ quadraticCharacterLine (p := p)) ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with rfl
    rw [normalizedDft_quadraticCharComplex_eq_scalar_smul (p := p) hp₂]
    exact Submodule.smul_mem (quadraticCharacterLine (p := p)) _
      (quadraticCharComplex_mem_quadraticCharacterLine (p := p))
  · simp
  · intro g h hg hh hgm hhm
    simpa using (quadraticCharacterLine (p := p)).add_mem hgm hhm
  · intro a g hg hgm
    simpa using (quadraticCharacterLine (p := p)).smul_mem a hgm

/-- Each basis vector belongs to exactly the block type expected for later
determinant bookkeeping: the trivial block, a non-self-dual character pair, or
the quadratic line. -/
theorem deltaZeroDirichletCharacterBasis_mem_trivial_or_pair_or_quadratic
    (hp₂ : p ≠ 2) (i : Option (DirichletCharacter ℂ p)) :
    deltaZeroDirichletCharacterBasis (p := p) i ∈ trivialBlock (p := p) ∨
      (∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧ χ ≠ χ⁻¹ ∧
        deltaZeroDirichletCharacterBasis (p := p) i ∈ characterPairSubmodule (p := p) χ) ∨
      deltaZeroDirichletCharacterBasis (p := p) i ∈ quadraticCharacterLine (p := p) := by
  cases i with
  | none =>
      left
      simpa using deltaZero_mem_trivialBlock (p := p)
  | some χ =>
      by_cases hχ : χ = 1
      · left
        subst hχ
        simpa using trivialCharacter_mem_trivialBlock (p := p)
      · by_cases hχself : χ = χ⁻¹
        · right
          right
          have hquad : χ = quadraticCharComplex p :=
            nontrivial_selfInverse_character_eq_quadratic (p := p) hp₂ hχ hχself
          subst hquad
          simpa using quadraticCharComplex_mem_quadraticCharacterLine (p := p)
        · right
          left
          refine ⟨χ, hχ, hχself, ?_⟩
          simpa using character_mem_characterPairSubmodule (p := p) χ

end SignInvariant

end BernoulliRegular
