module

public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Gauss sums for Dirichlet characters modulo a prime

Thin wrapper around mathlib's `gaussSum` specialised to Dirichlet characters
modulo a prime `p`, using the standard additive character
`ZMod.stdAddChar`.

## Main results

* `BernoulliRegular.gaussSum_one_stdAddChar`: the Gauss sum of the trivial
  Dirichlet character modulo a prime `p` with the standard additive character
  equals `-1`.
* `BernoulliRegular.gaussSum_mul_gaussSum_inv_stdAddChar`: for a non-trivial
  Dirichlet character `χ` modulo a prime `p`,
  `τ(χ) · τ(χ̄) = χ(-1) · p`.
* `BernoulliRegular.DirichletCharacter.isPrimitive_of_prime_of_ne_one`: for
  `p` prime, every non-trivial Dirichlet character mod `p` is primitive.
* `BernoulliRegular.gaussSum_stdAddChar_mulShift`: the key Galois-equivariance
  identity for the Gauss sum: for nontrivial `χ` mod prime `p` and `a : ZMod p`,
  `gaussSum χ (stdAddChar.mulShift a) = χ⁻¹ a · gaussSum χ stdAddChar`.
* `BernoulliRegular.isIntegral_gaussSum_stdAddChar`: the Gauss sum
  `τ(χ) = gaussSum χ ZMod.stdAddChar` is an algebraic integer — integral over `ℤ`
  as an element of `ℂ`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- **T025**: The Gauss sum of the trivial Dirichlet character modulo a
prime `p`, paired with the standard additive character
`ZMod.stdAddChar : AddChar (ZMod p) ℂ`, evaluates to `-1`. -/
theorem gaussSum_one_stdAddChar :
    gaussSum (1 : DirichletCharacter ℂ p) (ZMod.stdAddChar (N := p)) = -1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  haveI : Nontrivial (ZMod p) := ZMod.nontrivial p
  -- `stdAddChar` is not the trivial additive character, so its values sum to `0`.
  have h_ne : (ZMod.stdAddChar (N := p)) ≠ 1 := by
    intro h
    have h01 : (ZMod.stdAddChar (N := p)) (1 : ZMod p) =
        (ZMod.stdAddChar (N := p)) (0 : ZMod p) := by
      have hrhs : (ZMod.stdAddChar (N := p)) (0 : ZMod p) = 1 :=
        AddChar.map_zero_eq_one _
      have hlhs : (ZMod.stdAddChar (N := p)) (1 : ZMod p) = 1 := by
        rw [h]; rfl
      rw [hlhs, hrhs]
    exact one_ne_zero (ZMod.injective_stdAddChar h01)
  have h_sum_std : ∑ a : ZMod p, (ZMod.stdAddChar (N := p)) a = 0 :=
    AddChar.sum_eq_zero_of_ne_one h_ne
  have h_zero_std : (ZMod.stdAddChar (N := p)) (0 : ZMod p) = 1 :=
    AddChar.map_zero_eq_one _
  -- The key identity: rewriting each term so the a = 0 contribution becomes explicit.
  have h_term : ∀ a : ZMod p,
      (1 : DirichletCharacter ℂ p) a * (ZMod.stdAddChar (N := p)) a =
        (ZMod.stdAddChar (N := p)) a -
          (if a = 0 then (ZMod.stdAddChar (N := p)) a else 0) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · have h0 : (1 : DirichletCharacter ℂ p) (0 : ZMod p) = 0 :=
        MulChar.map_nonunit _ (by simp)
      simp [h0]
    · have hu : IsUnit a := ha.isUnit
      simp [MulChar.one_apply hu, if_neg ha]
  classical
  calc gaussSum (1 : DirichletCharacter ℂ p) (ZMod.stdAddChar (N := p))
      = ∑ a : ZMod p, (1 : DirichletCharacter ℂ p) a * (ZMod.stdAddChar (N := p)) a := rfl
    _ = ∑ a : ZMod p, ((ZMod.stdAddChar (N := p)) a -
          (if a = 0 then (ZMod.stdAddChar (N := p)) a else 0)) := by
          refine Finset.sum_congr rfl fun a _ => h_term a
    _ = (∑ a : ZMod p, (ZMod.stdAddChar (N := p)) a) -
          ∑ a : ZMod p, (if a = 0 then (ZMod.stdAddChar (N := p)) a else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 - (ZMod.stdAddChar (N := p)) (0 : ZMod p) := by
          rw [h_sum_std, Finset.sum_ite_eq' Finset.univ
            (0 : ZMod p) (fun a => (ZMod.stdAddChar (N := p)) a)]
          simp
    _ = -1 := by rw [h_zero_std]; ring

/-- **T026**: For a non-trivial Dirichlet character `χ` modulo a prime `p`,
`τ(χ) · τ(χ̄) = χ(-1) · p`, where `τ(χ) = gaussSum χ ZMod.stdAddChar` is
the classical Gauss sum. -/
theorem gaussSum_mul_gaussSum_inv_stdAddChar
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
      χ (-1) * p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_prim : (ZMod.stdAddChar : AddChar (ZMod p) ℂ).IsPrimitive :=
    ZMod.isPrimitive_stdAddChar p
  have h_card : (Fintype.card (ZMod p) : ℂ) = p := by
    rw [ZMod.card]
  -- Mathlib's Gauss sum identity: τ(χ) · τ(χ⁻¹)|_{ψ⁻¹} = card.
  have h1 : gaussSum χ (ZMod.stdAddChar (N := p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹ = (p : ℂ) := by
    rw [← h_card]; exact gaussSum_mul_gaussSum_eq_card hχ h_prim
  -- Bridge between `ψ` and `ψ⁻¹` via `χ⁻¹(-1) · τ(χ⁻¹)|_{ψ⁻¹} = τ(χ⁻¹)|_ψ`.
  have h2 := mul_gaussSum_inv_eq_gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))
  -- Simplify `χ⁻¹(-1) = χ(-1)` via `χ(-1)² = 1`.
  have h_neg_unit : IsUnit (-1 : ZMod p) := isUnit_one.neg
  have h_sq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, show (-1 : ZMod p) * -1 = 1 from by ring, MulChar.map_one]
  have h_ne : χ (-1) ≠ 0 := fun h => by
    rw [h, mul_zero] at h_sq; exact zero_ne_one h_sq
  have h_inv_neg_one : χ⁻¹ (-1) = χ (-1) := by
    have h_inv_mul : χ⁻¹ (-1) * χ (-1) = 1 := by
      rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply h_neg_unit]
    exact mul_right_cancel₀ h_ne (h_inv_mul.trans h_sq.symm)
  rw [h_inv_neg_one] at h2
  -- Multiply `h1` by `χ(-1)` and use `h2` to replace `ψ⁻¹` by `ψ` on the right.
  have h3 : χ (-1) * (gaussSum χ (ZMod.stdAddChar (N := p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹) = χ (-1) * p := by rw [h1]
  rw [show χ (-1) * (gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹) =
      gaussSum χ (ZMod.stdAddChar (N := p)) *
        (χ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))⁻¹) from by ring, h2] at h3
  exact h3

/-- The standard Jacobi-sum factorization specialized to Dirichlet characters
modulo the prime `p` and the additive character `ZMod.stdAddChar`. -/
theorem gaussSum_mul_gaussSum_eq_jacobiSum_mul_gaussSum_stdAddChar
    {χ φ : DirichletCharacter ℂ p} (hχφ : χ * φ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum φ (ZMod.stdAddChar (N := p)) =
      jacobiSum χ φ * gaussSum (χ * φ) (ZMod.stdAddChar (N := p)) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (jacobiSum_mul_nontrivial hχφ (ZMod.stdAddChar (N := p))).symm

/-- The Jacobi sum attached to two Dirichlet characters modulo the prime `p`
does not vanish as soon as their product is nontrivial. -/
theorem jacobiSum_ne_zero_stdAddChar
    {χ φ : DirichletCharacter ℂ p} (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ ≠ 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  by_cases hχ : χ = 1
  · subst hχ
    have hφ : φ ≠ 1 := by simpa using hχφ
    rw [jacobiSum_one_nontrivial hφ]
    exact neg_ne_zero.mpr one_ne_zero
  · by_cases hφ : φ = 1
    · subst hφ
      rw [jacobiSum_comm, jacobiSum_one_nontrivial hχ]
      exact neg_ne_zero.mpr one_ne_zero
    · have hcard : (Fintype.card (ZMod p) : ℂ) ≠ 0 := by
        rw [ZMod.card]
        exact_mod_cast hp.out.ne_zero
      have hprim : (ZMod.stdAddChar : AddChar (ZMod p) ℂ).IsPrimitive :=
        ZMod.isPrimitive_stdAddChar p
      have hτχ :
          gaussSum χ (ZMod.stdAddChar (N := p)) ≠ 0 :=
        gaussSum_ne_zero_of_nontrivial hcard hχ hprim
      have hτφ :
          gaussSum φ (ZMod.stdAddChar (N := p)) ≠ 0 :=
        gaussSum_ne_zero_of_nontrivial hcard hφ hprim
      intro hJ
      have hmul :=
        gaussSum_mul_gaussSum_eq_jacobiSum_mul_gaussSum_stdAddChar
          (p := p) (χ := χ) (φ := φ) hχφ
      rw [hJ, zero_mul] at hmul
      exact (mul_ne_zero hτχ hτφ) hmul

/-- **T027a**: For a prime modulus `p`, any non-trivial Dirichlet character
is primitive. Follows from `χ.conductor ∣ p` and the fact that the only
character factoring through `1` is the trivial character. -/
theorem DirichletCharacter.isPrimitive_of_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    χ.IsPrimitive := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.factorsThrough_one_iff χ).mp
      (h ▸ χ.factorsThrough_conductor)) hχ
  · exact h

/-- **T023d1a**: The quadratic Dirichlet character modulo `p`, viewed as
`ℂ`-valued so it can be paired with `ZMod.stdAddChar` in Gauss sums. -/
noncomputable def quadraticCharComplex : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- **T023d1a**: The quadratic character modulo `p`, after base change to
`ℂ`, is still quadratic. -/
theorem quadraticCharComplex_isQuadratic :
    (quadraticCharComplex p).IsQuadratic := by
  simpa [quadraticCharComplex] using
    (quadraticChar_isQuadratic (F := ZMod p)).comp (Int.castRingHom ℂ)

/-- **T023d1a**: For odd prime `p`, the quadratic character modulo `p` is
nontrivial after base change to `ℂ`. -/
theorem quadraticCharComplex_ne_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p ≠ 1 := by
  simpa [quadraticCharComplex] using
    (MulChar.ringHomComp_ne_one_iff
      (f := Int.castRingHom ℂ) (hf := Int.cast_injective)).2
      (quadraticChar_ne_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂))

/-- **T023d1a**: The quadratic character modulo `p` is self-inverse after
base change to `ℂ`. -/
theorem quadraticCharComplex_inv :
    (quadraticCharComplex p)⁻¹ = quadraticCharComplex p := by
  simpa using
    (quadraticCharComplex_isQuadratic (p := p)).inv

/-- **T023d1a**: Equivalently, the square of the quadratic character modulo
`p` is the trivial character after base change to `ℂ`. -/
theorem quadraticCharComplex_sq_eq_one :
    quadraticCharComplex p ^ 2 = 1 := by
  simpa using
    (quadraticCharComplex_isQuadratic (p := p)).sq_eq_one

/-- **T023d1a**: The quadratic character at `-1` is given by `χ₄(p)`. -/
theorem quadraticCharComplex_eval_neg_one_eq_chi4 (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = ZMod.χ₄ p := by
  rw [quadraticCharComplex, MulChar.ringHomComp_apply,
    quadraticChar_neg_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂), ZMod.card]
  rfl

/-- **T023d1a**: The value of the quadratic character at `-1` is determined
by `p % 4`. -/
theorem quadraticCharComplex_eval_neg_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = if p % 4 = 1 then 1 else -1 := by
  have hp_odd : p % 2 = 1 := by
    rcases hp.out.odd_of_ne_two hp₂ with ⟨k, hk⟩
    omega
  rw [quadraticCharComplex_eval_neg_one_eq_chi4 (p := p) hp₂, ZMod.χ₄_nat_eq_if_mod_four]
  simp [hp_odd]

/-- **T023d1a**: If `p ≡ 1 (mod 4)`, the quadratic character takes the value
`1` at `-1`. -/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 1) :
    quadraticCharComplex p (-1) = 1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

/-- **T023d1a**: If `p ≡ 3 (mod 4)`, the quadratic character takes the value
`-1` at `-1`. -/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 3) :
    quadraticCharComplex p (-1) = -1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

/-- **T023d1b**: The number of square roots of `a : ZMod p` is
`1 + quadraticChar (ZMod p) a`, in the integer-valued normalization used by
mathlib's quadratic-character API. -/
theorem quadraticChar_card_sqrts_zmod (hp₂ : p ≠ 2) (a : ZMod p) :
    (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℤ)) =
      quadraticChar (ZMod p) a + 1 := by
  simpa using
    (quadraticChar_card_sqrts (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂) a)

/-- **T023d1b**: The same square-root counting identity, rewritten using the
`ℂ`-valued quadratic character packaged for the quadratic Gauss-sum argument. -/
theorem quadraticCharComplex_card_sqrts (hp₂ : p ≠ 2) (a : ZMod p) :
    (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℂ)) =
      quadraticCharComplex p a + 1 := by
  calc
    (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℂ))
        = ((({x : ZMod p | x ^ 2 = a}.toFinset.card : ℤ)) : ℂ) := by norm_num
    _ = (((quadraticChar (ZMod p) a + 1 : ℤ)) : ℂ) := by
      exact_mod_cast quadraticChar_card_sqrts_zmod (p := p) hp₂ a
    _ = quadraticCharComplex p a + 1 := by
      simp [quadraticCharComplex]

/-- **T023d1c**: The discrete Fourier transform of the square-root counting
function is the quadratic exponential sum obtained by counting fibers of the
map `x ↦ x^2`. -/
theorem dft_squareRootCount (k : ZMod p) :
    ZMod.dft (fun a : ZMod p => (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℂ))) k =
      ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-(k * x ^ 2)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    ∑ a : ZMod p,
        ZMod.stdAddChar (N := p) (-(a * k)) *
          (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℂ))
      = ∑ a : ZMod p, ∑ x : {x : ZMod p // x ^ 2 = a},
          ZMod.stdAddChar (N := p) (-(a * k)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [show (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℂ)) =
              ∑ _ : {x : ZMod p // x ^ 2 = a}, (1 : ℂ) by
                calc
                  (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℂ))
                      = (Fintype.card {x : ZMod p // x ^ 2 = a} : ℂ) := by
                          norm_num [Fintype.card_subtype]
                  _ = ∑ _ : {x : ZMod p // x ^ 2 = a}, (1 : ℂ) := by
                        exact_mod_cast
                          (Fintype.card_eq_sum_ones (α := {x : ZMod p // x ^ 2 = a})),
            Finset.mul_sum]
          simp
    _ = ∑ y : Σ a : ZMod p, {x : ZMod p // x ^ 2 = a},
          ZMod.stdAddChar (N := p) (-(y.1 * k)) := by
          rw [Fintype.sum_sigma]
    _ = ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-(x ^ 2 * k)) := by
          refine Fintype.sum_equiv (Equiv.sigmaFiberEquiv (fun x : ZMod p => x ^ 2)) _ _ ?_
          intro y
          rcases y with ⟨a, x⟩
          simp [Equiv.sigmaFiberEquiv, x.2]
    _ = ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-(k * x ^ 2)) := by
          simp_rw [mul_comm]

/-- **T023d1c**: Rewriting the direct-counting Fourier transform identity in
terms of `quadraticCharComplex p a + 1`, using the square-counting package
from `T023d1b`. -/
theorem dft_quadraticCharComplex_add_one (hp₂ : p ≠ 2) (k : ZMod p) :
    ZMod.dft (fun a : ZMod p => quadraticCharComplex p a + 1) k =
      ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-(k * x ^ 2)) := by
  have hfun :
      (fun a : ZMod p => quadraticCharComplex p a + 1) =
        (fun a : ZMod p => (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℂ))) := by
    funext a
    exact (quadraticCharComplex_card_sqrts (p := p) hp₂ a).symm
  rw [hfun]
  exact dft_squareRootCount (p := p) k

/-- **T023d1d**: The discrete Fourier transform of the complex-valued
quadratic character is the inverse character times its Gauss sum. -/
theorem dft_quadraticCharComplex_eq_gaussSum (hp₂ : p ≠ 2) (k : ZMod p) :
    ZMod.dft (quadraticCharComplex p) k =
      quadraticCharComplex p (-k) *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hprim : (quadraticCharComplex p).IsPrimitive :=
    DirichletCharacter.isPrimitive_of_ne_one (p := p)
      (quadraticCharComplex_ne_one (p := p) hp₂)
  simpa [quadraticCharComplex_inv (p := p)] using
    (DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
      (χ := quadraticCharComplex p) hprim k)

/-- The discrete Fourier transform of the constant-one function on `ZMod p` is
`p` at `0` and `0` away from `0`. -/
theorem dft_const_one (k : ZMod p) :
    ZMod.dft (fun _ : ZMod p => (1 : ℂ)) k = if k = 0 then p else 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  by_cases hk : k = 0
  · subst hk
    rw [ZMod.dft_apply_zero]
    simp
  · rw [ZMod.dft_apply, if_neg hk]
    have hne : ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) ≠ 1 := by
      intro hshift
      have heval : (ZMod.stdAddChar (N := p)) (-k) = 1 := by
        simpa [AddChar.mulShift_apply] using
          congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ 1) hshift
      have hzero : (ZMod.stdAddChar (N := p)) (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _
      have hkzero : (-k : ZMod p) = 0 := ZMod.injective_stdAddChar (heval.trans hzero.symm)
      exact hk (by simpa using hkzero)
    have hsum : ∑ j : ZMod p, ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) j = 0 :=
      AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- **T023d1d**: The Fourier transform of the square-counting normalization
`quadraticCharComplex p + 1` is the sum of the quadratic-character Gauss-sum
term and the transform of the constant function. -/
theorem dft_quadraticCharComplex_add_one_eq_gaussSum (hp₂ : p ≠ 2) (k : ZMod p) :
    ZMod.dft (fun a : ZMod p => quadraticCharComplex p a + 1) k =
      quadraticCharComplex p (-k) *
          gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) +
        if k = 0 then p else 0 := by
  change (ZMod.dft ((quadraticCharComplex p : ZMod p → ℂ) + fun _ : ZMod p => (1 : ℂ))) k = _
  rw [map_add]
  simp [dft_quadraticCharComplex_eq_gaussSum (p := p) hp₂, dft_const_one (p := p) k]

/-- **T023d1d**: Away from `0`, the constant term vanishes, so the Fourier
transform of `quadraticCharComplex p + 1` is exactly the quadratic Gauss-sum
term. -/
theorem dft_quadraticCharComplex_add_one_of_ne_zero (hp₂ : p ≠ 2)
    {k : ZMod p} (hk : k ≠ 0) :
    ZMod.dft (fun a : ZMod p => quadraticCharComplex p a + 1) k =
      quadraticCharComplex p (-k) *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  simpa [hk] using dft_quadraticCharComplex_add_one_eq_gaussSum (p := p) hp₂ k

/-- Conjugating the standard additive character negates its input. -/
theorem conj_stdAddChar (a : ZMod p) :
  conj (ZMod.stdAddChar (N := p) a) = ZMod.stdAddChar (N := p) (-a) := by
  rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv,
    ← ZMod.stdAddChar_apply]

/-- **T023d1e**: Specializing the two Fourier-transform computations at
`k = -1` identifies the quadratic Gauss sum with the quadratic exponential sum
`∑ x, stdAddChar (x^2)`. -/
theorem gaussSum_quadraticCharComplex_eq_squareExponentialSum (hp₂ : p ≠ 2) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
      ∑ x : ZMod p, ZMod.stdAddChar (N := p) (x ^ 2) := by
  have hneg1 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  calc
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        quadraticCharComplex p (-(-1 : ZMod p)) *
          gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
            simp
    _ = ZMod.dft (fun a : ZMod p => quadraticCharComplex p a + 1) (-1) := by
          symm
          exact dft_quadraticCharComplex_add_one_of_ne_zero (p := p) hp₂ (k := (-1 : ZMod p)) hneg1
    _ = ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-((-1 : ZMod p) * x ^ 2)) :=
          dft_quadraticCharComplex_add_one (p := p) hp₂ (-1)
    _ = ∑ x : ZMod p, ZMod.stdAddChar (N := p) (x ^ 2) := by
          simp

/-- **T023d1e**: Conjugating the quadratic Gauss sum multiplies it by the
quadratic character evaluated at `-1`. Equivalently,
`conj τ = quadraticCharComplex p (-1) * τ`. -/
theorem conj_gaussSum_quadraticCharComplex_eq_eval_neg_one_mul (hp₂ : p ≠ 2) :
    conj (gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) =
      quadraticCharComplex p (-1) *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  calc
    conj (gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) =
    conj (∑ x : ZMod p, ZMod.stdAddChar (N := p) (x ^ 2)) := by
          rw [gaussSum_quadraticCharComplex_eq_squareExponentialSum (p := p) hp₂]
    _ = ∑ x : ZMod p, conj (ZMod.stdAddChar (N := p) (x ^ 2)) :=
          map_sum conj (fun x : ZMod p => ZMod.stdAddChar (N := p) (x ^ 2)) Finset.univ
    _ = ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-(x ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          simpa using conj_stdAddChar (p := p) (x ^ 2)
    _ = ZMod.dft (fun a : ZMod p => quadraticCharComplex p a + 1) (1 : ZMod p) := by
          symm
          simpa using dft_quadraticCharComplex_add_one (p := p) hp₂ (1 : ZMod p)
    _ = quadraticCharComplex p (-1) *
          gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) :=
          dft_quadraticCharComplex_add_one_of_ne_zero (p := p) hp₂
            (k := (1 : ZMod p)) one_ne_zero

/-- **T023d1e**: If `p ≡ 1 (mod 4)`, the quadratic Gauss sum is fixed by
complex conjugation, hence is real. -/
theorem conj_gaussSum_quadraticCharComplex_eq_self_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
  conj (gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) =
      gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  rw [conj_gaussSum_quadraticCharComplex_eq_eval_neg_one_mul (p := p) hp₂,
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (p := p) hp₂ hp₄, one_mul]

/-- **T023d1e**: If `p ≡ 3 (mod 4)`, the quadratic Gauss sum changes sign
under complex conjugation, hence is purely imaginary. -/
theorem conj_gaussSum_quadraticCharComplex_eq_neg_self_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
  conj (gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) =
      -gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  rw [conj_gaussSum_quadraticCharComplex_eq_eval_neg_one_mul (p := p) hp₂,
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄, neg_one_mul]

/-- **T023d1f**: The square of the quadratic Gauss sum is
`quadraticCharComplex p (-1) * p`. -/
theorem gaussSum_quadraticCharComplex_sq (hp₂ : p ≠ 2) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) ^ 2 =
      quadraticCharComplex p (-1) * p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  simpa [ZMod.card] using
    gaussSum_sq (χ := quadraticCharComplex p)
      (quadraticCharComplex_ne_one (p := p) hp₂)
      (quadraticCharComplex_isQuadratic (p := p))
      (ZMod.isPrimitive_stdAddChar p)

/-- **T023d1f**: If `p ≡ 1 (mod 4)`, then the quadratic Gauss sum is one of
`±√p`. -/
theorem gaussSum_quadraticCharComplex_eq_or_neg_eq_sqrt_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        (Real.sqrt p : ℂ) ∨
      gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        (-(Real.sqrt p : ℂ)) := by
  let τ : ℂ := gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))
  have hconj : conj τ = τ := by
    simpa [τ] using
      conj_gaussSum_quadraticCharComplex_eq_self_of_mod_four_eq_one (p := p) hp₂ hp₄
  rcases (Complex.conj_eq_iff_real).1 hconj with ⟨r, hr⟩
  have hτsq : τ ^ 2 = (p : ℂ) := by
    simpa [τ,
      quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (p := p) hp₂ hp₄] using
      gaussSum_quadraticCharComplex_sq (p := p) hp₂
  have hsq : ((r : ℂ)) ^ 2 = (p : ℂ) := by
    simpa [hr] using hτsq
  have hsq_real : r ^ 2 = (p : ℝ) := by
    have hsq_re := congrArg Complex.re hsq
    simpa [pow_two] using hsq_re
  have hp_nonneg : (0 : ℝ) ≤ p := by exact_mod_cast Nat.zero_le p
  have hsqrt : r = Real.sqrt p ∨ r = -Real.sqrt p := by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [hsq_real, Real.sq_sqrt hp_nonneg]
  rcases hsqrt with hrsqrt | hrneg
  · left
    simp [τ, hr, hrsqrt]
  · right
    simp [τ, hr, hrneg]

/-- **T023d1f**: If `p ≡ 3 (mod 4)`, then the quadratic Gauss sum is one of
`± I * √p`. -/
theorem gaussSum_quadraticCharComplex_eq_or_neg_eq_I_mul_sqrt_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        Complex.I * (Real.sqrt p : ℂ) ∨
      gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        -(Complex.I * (Real.sqrt p : ℂ)) := by
  let τ : ℂ := gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))
  let z : ℂ := -Complex.I * τ
  have hτconj : conj τ = -τ := by
    simpa [τ] using
      conj_gaussSum_quadraticCharComplex_eq_neg_self_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hzconj : conj z = z := by
    calc
      conj z = conj (-Complex.I * τ) := by rfl
      _ = conj (-Complex.I) * conj τ := by simp
      _ = Complex.I * (-τ) := by rw [hτconj]; simp
      _ = z := by simp [z]
  rcases (Complex.conj_eq_iff_real).1 hzconj with ⟨r, hr⟩
  have hτsq : τ ^ 2 = (-(p : ℂ)) := by
    simpa [τ,
      quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄] using
      gaussSum_quadraticCharComplex_sq (p := p) hp₂
  have hzsq : z ^ 2 = (p : ℂ) := by
    calc
      z ^ 2 = (-Complex.I * τ) ^ 2 := by rfl
      _ = (-Complex.I) ^ 2 * τ ^ 2 := by ring
      _ = (-(1 : ℂ)) * τ ^ 2 := by simp [pow_two]
      _ = (p : ℂ) := by rw [hτsq]; ring
  have hsq : ((r : ℂ)) ^ 2 = (p : ℂ) := by
    simpa [hr] using hzsq
  have hsq_real : r ^ 2 = (p : ℝ) := by
    have hsq_re := congrArg Complex.re hsq
    simpa [pow_two] using hsq_re
  have hp_nonneg : (0 : ℝ) ≤ p := by exact_mod_cast Nat.zero_le p
  have hsqrt : r = Real.sqrt p ∨ r = -Real.sqrt p := by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [hsq_real, Real.sq_sqrt hp_nonneg]
  have hτ : τ = Complex.I * r := by
    have hmul := congrArg (fun w : ℂ => Complex.I * w) hr
    have hIz : Complex.I * z = τ := by
      calc
        Complex.I * z = -(Complex.I * (Complex.I * τ)) := by simp [z]
        _ = -((Complex.I * Complex.I) * τ) := by rw [← mul_assoc]
        _ = τ := by simp
    calc
      τ = Complex.I * z := hIz.symm
      _ = Complex.I * r := by simpa using hmul
  rcases hsqrt with hrsqrt | hrneg
  · left
    simp [τ, hτ, hrsqrt]
  · right
    simp [τ, hτ, hrneg]

/-- **T027b**: The Galois-equivariance identity for the Gauss sum with the
standard additive character: shifting `ZMod.stdAddChar` by `a ∈ ZMod p`
multiplies the Gauss sum by `χ⁻¹ a`. This encodes the action of the Galois
automorphism `σ_a` on `τ(χ)`.

In classical notation: `σ_a(τ(χ)) = χ⁻¹(a) · τ(χ)`, since applying `σ_a`
to `ζ_p^b = stdAddChar b` gives `ζ_p^(ab) = (stdAddChar.mulShift a) b`. -/
theorem gaussSum_stdAddChar_mulShift {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1)
    (a : ZMod p) :
    gaussSum χ ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift a) =
      χ⁻¹ a * gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  gaussSum_mulShift_of_isPrimitive _ (DirichletCharacter.isPrimitive_of_ne_one p hχ) a

/-- **T027c (character-side)**: `χ a` is integral over `ℤ` for any Dirichlet
character `χ : DirichletCharacter ℂ p`. Uses `χ^(p-1) = 1` + membership in
`Algebra.adjoin ℤ {μ_{p-1}}`, which is contained in the integral closure. -/
theorem DirichletCharacter.isIntegral_apply (χ : DirichletCharacter ℂ p) (a : ZMod p) :
    IsIntegral ℤ (χ a) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_sub : 0 < p - 1 := by have := hp.out.one_lt; omega
  set μ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p - 1 : ℕ))
  have hμ : IsPrimitiveRoot μ (p - 1) :=
    Complex.isPrimitiveRoot_exp _ hp_sub.ne'
  have h_pow : χ ^ (p - 1) = 1 := by
    have h := MulChar.pow_card_eq_one χ (M := ZMod p)
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h
  have h_mem : χ a ∈ Algebra.adjoin ℤ {μ} :=
    haveI : NeZero (p - 1) := ⟨hp_sub.ne'⟩
    MulChar.apply_mem_algebraAdjoin_of_pow_eq_one h_pow hμ a
  exact (mem_integralClosure_iff ℤ ℂ).mp
    (adjoin_le_integralClosure (hμ.isIntegral hp_sub) h_mem)

/-- **T027c (additive-side)**: the standard additive character values are
integral over `ℤ` (each is a `p`-th root of unity). -/
theorem ZMod.isIntegral_stdAddChar (a : ZMod p) :
    IsIntegral ℤ ((ZMod.stdAddChar : AddChar (ZMod p) ℂ) a) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hx_pow : ((ZMod.stdAddChar : AddChar (ZMod p) ℂ) a) ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, show ((p : ℕ) • a : ZMod p) = 0 from by
        rw [show ((p : ℕ) • a : ZMod p) = (p : ZMod p) * a from by ring,
          ZMod.natCast_self, zero_mul], AddChar.map_zero_eq_one]
  refine ⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero, ?_⟩
  simp [hx_pow]

/-- **T027c**: the Gauss sum `τ(χ) = gaussSum χ ZMod.stdAddChar` for a
Dirichlet character `χ` modulo a prime `p` is an algebraic integer. -/
theorem isIntegral_gaussSum_stdAddChar (χ : DirichletCharacter ℂ p) :
    IsIntegral ℤ (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) := by
  unfold gaussSum
  refine IsIntegral.sum _ fun a _ => IsIntegral.mul ?_ ?_
  · exact DirichletCharacter.isIntegral_apply p χ a
  · exact ZMod.isIntegral_stdAddChar p a

/-- The canonical complex primitive `p(p-1)`-th root of unity used in the
Stickelberger infrastructure: `ζ_{p(p-1)} := exp(2πi/(p(p-1))) ∈ ℂ`. -/
noncomputable def stickelbergerComplexRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (p * (p - 1) : ℕ))

/-- `stickelbergerComplexRoot p` is a primitive `p(p-1)`-th root of unity. -/
theorem stickelbergerComplexRoot_isPrimitiveRoot :
    IsPrimitiveRoot (stickelbergerComplexRoot p) (p * (p - 1)) := by
  have hp_pos : 0 < p := hp.out.pos
  have hp_sub : 0 < p - 1 := by have := hp.out.one_lt; omega
  have hN_pos : 0 < p * (p - 1) := Nat.mul_pos hp_pos hp_sub
  exact Complex.isPrimitiveRoot_exp _ hN_pos.ne'

/-- **T027d1** (refinement of T027c): the Gauss sum `τ(χ)` for a Dirichlet
character `χ` modulo a prime `p` lies in `Algebra.adjoin ℤ {ζ}` where
`ζ = stickelbergerComplexRoot p` is the canonical primitive `p(p-1)`-th
root of unity `exp(2πi/(p(p-1)))`. This pins the integrality of `τ(χ)`
to a concrete subring of `ℂ`, one step toward Stickelberger's theorem. -/
theorem gaussSum_mem_algebraAdjoin_stickelbergerComplexRoot
    (χ : DirichletCharacter ℂ p) :
    gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ∈
      Algebra.adjoin ℤ ({stickelbergerComplexRoot p} : Set ℂ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_one_lt : 1 < p := hp.out.one_lt
  have hp_sub : 0 < p - 1 := by omega
  have hp_pos : 0 < p := hp.out.pos
  have hN_pos : 0 < p * (p - 1) := Nat.mul_pos hp_pos hp_sub
  set ζ : ℂ := stickelbergerComplexRoot p with hζ_def
  have hζ : IsPrimitiveRoot ζ (p * (p - 1)) :=
    stickelbergerComplexRoot_isPrimitiveRoot p
  have hζ_p : IsPrimitiveRoot (ζ ^ (p - 1)) p :=
    hζ.pow hN_pos (by ring)
  have hζ_pm1 : IsPrimitiveRoot (ζ ^ p) (p - 1) :=
    hζ.pow hN_pos rfl
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
  have hpm1_nat_ne : (p - 1 : ℕ) ≠ 0 := hp_sub.ne'
  have hpm1_cplx_ne : ((p - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpm1_nat_ne
  -- Key fact: `stdAddChar 1 = ζ ^ (p-1)`.
  have h_stdAddChar_one : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 = ζ ^ (p - 1) := by
    have h1 : ((1 : ZMod p)) = ((1 : ℤ) : ZMod p) := by norm_cast
    rw [h1, ZMod.stdAddChar_coe, hζ_def, stickelbergerComplexRoot,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  unfold gaussSum
  refine Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ ?_ ?_
  · -- `χ a ∈ Algebra.adjoin ℤ {ζ}` via `adjoin ℤ {ζ^p} ⊆ adjoin ℤ {ζ}`.
    have h_pow : χ ^ (p - 1) = 1 := by
      have h := MulChar.pow_card_eq_one χ (M := ZMod p)
      rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h
    haveI : NeZero (p - 1) := ⟨hp_sub.ne'⟩
    have h_mem : χ a ∈ Algebra.adjoin ℤ ({ζ ^ p} : Set ℂ) :=
      MulChar.apply_mem_algebraAdjoin_of_pow_eq_one h_pow hζ_pm1 a
    have h_sub : Algebra.adjoin ℤ ({ζ ^ p} : Set ℂ) ≤ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
      apply Algebra.adjoin_le
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton _ _) _
    exact h_sub h_mem
  · -- `stdAddChar a = (ζ^(p-1))^(a.val) ∈ adjoin ℤ {ζ}`.
    have h_val : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a =
        (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 ^ a.val := by
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [h_val, h_stdAddChar_one]
    exact Subalgebra.pow_mem _ (Subalgebra.pow_mem _
      (Algebra.self_mem_adjoin_singleton _ _) _) _

/-- **T027d1** (existential form): the Gauss sum `τ(χ)` lies in
`Algebra.adjoin ℤ {ζ}` for some primitive `p(p-1)`-th root of unity `ζ`. -/
theorem gaussSum_mem_algebraAdjoin_primitiveRoot_p_mul_pm1
    (χ : DirichletCharacter ℂ p) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ (p * (p - 1)) ∧
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ∈
        Algebra.adjoin ℤ ({ζ} : Set ℂ) :=
  ⟨stickelbergerComplexRoot p, stickelbergerComplexRoot_isPrimitiveRoot p,
    gaussSum_mem_algebraAdjoin_stickelbergerComplexRoot p χ⟩

end GaussSum

end BernoulliRegular
