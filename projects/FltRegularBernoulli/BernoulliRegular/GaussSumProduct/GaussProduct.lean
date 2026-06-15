module

public import BernoulliRegular.GaussSum
public import BernoulliRegular.GaussSumSign
public import BernoulliRegular.LFunctionPositive
public import BernoulliRegular.LValueAtOne
public import BernoulliRegular.ZetaFactorisation
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Product of Gauss sums over odd Dirichlet characters

For `p` a prime, we compute the square of the product of Gauss sums over
the set of odd Dirichlet characters modulo `p`:

`(∏_{χ∈X⁻} τ(χ))² = (-p)^n`

where `n = (p-1)/2 = |X⁻|`. This avoids the classical Gauss sum sign
theorem — we only use T026 (`τ(χ)·τ(χ⁻¹) = χ(-1)·p`) and the fact that
conjugation `χ ↦ χ⁻¹` is an involution preserving oddness.

## Main results

* `BernoulliRegular.gaussSum_oddCharacters_prod_sq`: the squared product
  identity. This is the Gauss-sign-free half of section9_detailed Prop 5.3.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Complex

section GaussProduct

variable (p : ℕ) [hp : Fact p.Prime]

/-- Conjugation `χ ↦ χ⁻¹` preserves oddness of Dirichlet characters. -/
lemma odd_inv_mem_oddCharacters {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ oddCharacters p) : χ⁻¹ ∈ oddCharacters p := by
  classical
  rw [oddCharacters, Finset.mem_filter] at hχ ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  -- `χ⁻¹(-1) = (χ(-1))⁻¹ = (-1)⁻¹ = -1`.
  change χ⁻¹ (-1) = -1
  have h_neg_unit : IsUnit ((-1 : ZMod p)) := IsUnit.neg isUnit_one
  have hχ_neg_one : χ (-1) = -1 := hχ.2
  rw [MulChar.inv_apply_eq_inv, hχ_neg_one]
  simp

/-- **G7 (squared form)**: `(∏_{χ odd} τ(χ))² = (-p)^|X⁻|`.

The squared version of section9_detailed Prop 5.3. Avoids the Gauss sum
sign theorem; uses only T026 and the involution `χ ↦ χ⁻¹` on the odd
characters. -/
theorem gaussSum_oddCharacters_prod_sq :
    (∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) ^ 2 =
      (-(p : ℂ)) ^ (oddCharacters p).card := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- Step 1: reindex ∏ τ(χ⁻¹) = ∏ τ(χ) via the involution.
  have h_bij : ∏ χ ∈ oddCharacters p,
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
    refine Finset.prod_bij (fun χ _ => χ⁻¹)
      (fun χ hχ => odd_inv_mem_oddCharacters p hχ) ?_ ?_ ?_
    · intro χ₁ _ χ₂ _ hχ
      rw [show χ₁ = (χ₁⁻¹)⁻¹ from (inv_inv _).symm, hχ, inv_inv]
    · intro χ hχ
      refine ⟨χ⁻¹, odd_inv_mem_oddCharacters p hχ, ?_⟩
      exact inv_inv _
    · intro χ _
      rfl
  -- Step 2: `(∏ τ(χ))² = ∏ τ(χ) · ∏ τ(χ⁻¹) = ∏ (τ(χ)·τ(χ⁻¹))`.
  rw [sq]
  nth_rw 2 [← h_bij]
  rw [← Finset.prod_mul_distrib]
  -- Step 3: each factor `τ(χ)·τ(χ⁻¹) = χ(-1)·p = -p` for odd `χ`.
  have h_term : ∀ χ ∈ oddCharacters p,
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) = -(p : ℂ) := by
    intro χ hχ
    classical
    rw [oddCharacters, Finset.mem_filter] at hχ
    have hχ_neg_one : χ (-1) = -1 := hχ.2
    have hχ_ne_one : χ ≠ 1 := by
      intro h
      rw [h] at hχ_neg_one
      have : (1 : DirichletCharacter ℂ p) (-1) = 1 :=
        MulChar.one_apply (IsUnit.neg isUnit_one)
      rw [this] at hχ_neg_one
      norm_num at hχ_neg_one
    rw [gaussSum_mul_gaussSum_inv_stdAddChar p hχ_ne_one, hχ_neg_one]
    ring
  rw [Finset.prod_congr rfl h_term, Finset.prod_const]

end GaussProduct

end BernoulliRegular
