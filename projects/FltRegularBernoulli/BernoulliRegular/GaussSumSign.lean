module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import BernoulliRegular.GaussSum

/-!
# Sign of the quadratic Gauss sum

For an odd prime `p`, the Legendre-symbol Dirichlet character `η : DirichletCharacter ℂ p`
is the unique order-2 character. When `p ≡ 3 (mod 4)`, it is odd, and the classical
Gauss sum sign theorem (Gauss 1805) states

`τ(η) = gaussSum η ZMod.stdAddChar = i · √p`.

This file builds the infrastructure:

* `BernoulliRegular.legendreDirichlet p` — the Legendre-symbol Dirichlet character
  `η : DirichletCharacter ℂ p`, obtained by composing `quadraticChar (ZMod p)`
  with `Int.castRingHom ℂ`.
* `BernoulliRegular.legendreDirichlet_isQuadratic`, `legendreDirichlet_ne_one`,
  `legendreDirichlet_isPrimitive`, `legendreDirichlet_odd` — basic properties.
* `BernoulliRegular.rootNumber_legendreDirichlet_sq` — the squared root-number
  identity `(rootNumber η)² = 1` (Phase 3), obtained directly from
  `gaussSum_sq` and the explicit formula for `rootNumber`.

The full sign determination (that `rootNumber η = +1`, equivalently `τ(η) = i√p`)
is the classical Gauss theorem and is not yet formalised here; it is the
remaining step needed to close the two `hMinus_formula` sorries in
`BernoulliRegular/HMinus/LValueReduction.lean`.

## References

* Diekmann 2023, §9 detailed note, Lemma 5.2.
* Washington, *Introduction to Cyclotomic Fields*, Chapter 6.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Complex

section Legendre

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Legendre-symbol Dirichlet character mod `p`, valued in `ℂ`. Obtained
from mathlib's `quadraticChar (ZMod p) : MulChar (ZMod p) ℤ` by composing with
the canonical `ℤ →+* ℂ`. -/
noncomputable def legendreDirichlet : DirichletCharacter ℂ p := by
  classical
  exact (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- `legendreDirichlet p` is quadratic: `η² = 1`. -/
theorem legendreDirichlet_isQuadratic : (legendreDirichlet p).IsQuadratic := by
  classical
  exact (quadraticChar_isQuadratic (ZMod p)).comp _

/-- Evaluation of `legendreDirichlet p` at `a` equals the complex cast of
`quadraticChar (ZMod p) a`. -/
theorem legendreDirichlet_apply (a : ZMod p) :
    legendreDirichlet p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := by
  classical
  rfl

/-- `Int.castRingHom ℂ` is injective. -/
private lemma intCastRingHom_injective_C : Function.Injective (Int.castRingHom ℂ) :=
  Int.cast_injective

/-- For `p` an odd prime, `legendreDirichlet p` is non-trivial. -/
theorem legendreDirichlet_ne_one (hp_odd : p ≠ 2) :
    legendreDirichlet p ≠ 1 := by
  classical
  have h_ring_char : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp_odd
  have h_base : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one h_ring_char
  exact (MulChar.ringHomComp_ne_one_iff intCastRingHom_injective_C).mpr h_base

/-- For `p` an odd prime, `legendreDirichlet p` is primitive. -/
theorem legendreDirichlet_isPrimitive (hp_odd : p ≠ 2) :
    (legendreDirichlet p).IsPrimitive :=
  DirichletCharacter.isPrimitive_of_ne_one p (legendreDirichlet_ne_one p hp_odd)

/-- For `p ≡ 3 (mod 4)`, `legendreDirichlet p` is odd: `η(-1) = -1`. -/
theorem legendreDirichlet_odd (hp_three_mod_four : p % 4 = 3) :
    (legendreDirichlet p).Odd := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  have h_ring_char : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp_odd
  change legendreDirichlet p (-1) = -1
  rw [legendreDirichlet_apply, quadraticChar_neg_one h_ring_char, ZMod.card p,
    ZMod.χ₄_nat_three_mod_four hp_three_mod_four]
  push_cast
  ring

/-- **Phase 3 (squared root number identity)**: for the Legendre-symbol Dirichlet
character `η` modulo `p ≡ 3 (mod 4)`, the root number satisfies `(rootNumber η)² = 1`.

This follows directly from the explicit formula `rootNumber χ = gaussSum χ stdAddChar / I / √p`
combined with `gaussSum_sq : (gaussSum χ stdAddChar)² = χ(-1) · Fintype.card (ZMod p) = -p`
for odd primitive quadratic `χ`. -/
theorem rootNumber_legendreDirichlet_sq (hp_three_mod_four : p % 4 = 3) :
    (DirichletCharacter.rootNumber (legendreDirichlet p)) ^ 2 = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  have h_odd : (legendreDirichlet p).Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_not_even : ¬ (legendreDirichlet p).Even := h_odd.not_even
  have h_prim : (legendreDirichlet p).IsPrimitive := legendreDirichlet_isPrimitive p hp_odd
  have h_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
  have h_quad : (legendreDirichlet p).IsQuadratic := legendreDirichlet_isQuadratic p
  have h_psi_prim : (ZMod.stdAddChar : AddChar (ZMod p) ℂ).IsPrimitive :=
    ZMod.isPrimitive_stdAddChar p
  -- `gaussSum_sq` gives `(gaussSum η stdAddChar)^2 = η(-1) · p = -p`.
  have h_gs_sq : (gaussSum (legendreDirichlet p)
      (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) ^ 2 =
        (legendreDirichlet p) (-1) * (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_sq h_ne_one h_quad h_psi_prim
  have h_card : (Fintype.card (ZMod p) : ℂ) = (p : ℂ) := by
    exact_mod_cast ZMod.card p
  have h_chi_neg_one : (legendreDirichlet p) (-1) = (-1 : ℂ) := h_odd
  rw [h_chi_neg_one, h_card] at h_gs_sq
  -- Expand `rootNumber`: for odd `η`, `rootNumber η = gaussSum η stdAddChar / I / √p`.
  unfold DirichletCharacter.rootNumber
  rw [if_neg h_not_even, pow_one]
  -- Simplify `rootNumber η = gaussSum η stdAddChar / I / p^(1/2)`; square it.
  have hp_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [div_pow, div_pow, h_gs_sq]
  rw [Complex.I_sq]
  -- Goal: -1 * ↑p / -1 / (↑p ^ (1/2))^2 = 1
  have h_half_sq : ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.cpow_mul_nat]
    norm_num
  rw [h_half_sq]
  field_simp

/-- **Disjunction form of Phase 3**: the root number of the odd Legendre-symbol
Dirichlet character is `+1` or `-1`. -/
theorem rootNumber_legendreDirichlet_eq_one_or_neg_one (hp_three_mod_four : p % 4 = 3) :
    DirichletCharacter.rootNumber (legendreDirichlet p) = 1 ∨
      DirichletCharacter.rootNumber (legendreDirichlet p) = -1 := by
  have h_sq : (DirichletCharacter.rootNumber (legendreDirichlet p)) ^ 2 = 1 :=
    rootNumber_legendreDirichlet_sq p hp_three_mod_four
  exact sq_eq_one_iff.mp h_sq

/-- **Corollary of Phase 3**: for the odd Legendre-symbol Dirichlet character
`η` mod `p ≡ 3 (mod 4)`, the Gauss sum is `τ(η) = ± i·√p`. -/
theorem gaussSum_legendreDirichlet_eq (hp_three_mod_four : p % 4 = 3) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
        Complex.I * (p : ℂ) ^ (1 / 2 : ℂ) ∨
      gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
        -(Complex.I * (p : ℂ) ^ (1 / 2 : ℂ)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  have h_odd : (legendreDirichlet p).Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_not_even : ¬ (legendreDirichlet p).Even := h_odd.not_even
  -- `rootNumber η = gaussSum / I / √p`, and `rootNumber η ∈ {±1}`.
  -- So `gaussSum = rootNumber · I · √p = ±I·√p`.
  have h_rn : DirichletCharacter.rootNumber (legendreDirichlet p) = 1 ∨
      DirichletCharacter.rootNumber (legendreDirichlet p) = -1 :=
    rootNumber_legendreDirichlet_eq_one_or_neg_one p hp_three_mod_four
  have h_def : DirichletCharacter.rootNumber (legendreDirichlet p) =
      gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) /
        Complex.I / ((p : ℂ) ^ (1 / 2 : ℂ)) := by
    unfold DirichletCharacter.rootNumber
    rw [if_neg h_not_even, pow_one]
  have hp_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp_cpow_ne_zero : (p : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp_ne_zero)
  have h_I_ne_zero : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_I_ne_zero : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  rcases h_rn with h1 | h1
  · left
    have heq := h_def
    rw [h1] at heq
    have heq' : Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) =
        gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
      field_simp at heq
      linear_combination heq
    exact heq'.symm
  · right
    have heq := h_def
    rw [h1] at heq
    have heq' : -(Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) =
        gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
      field_simp at heq
      linear_combination heq
    exact heq'.symm

end Legendre

end BernoulliRegular
