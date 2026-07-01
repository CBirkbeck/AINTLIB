module

public import BernoulliRegular.GaussSumProduct

/-!
# Completed Dedekind zeta for the cyclotomic field `ℚ(ζ_p)`

This module sets up the completed Dedekind zeta function for the cyclotomic field
`ℚ(ζ_p)` (for `p` prime) via the L-function factorization
`ζ_K(s) = ζ(s) · ∏_{χ ≠ 1 mod p} L(χ, s)`.

## Main definitions

* `completedDedekindZetaCyclotomic p s`: the completed Dedekind zeta of `ℚ(ζ_p)`,
  defined as `completedRiemannZeta s · ∏_{χ ∈ nontrivialCharacters p} completedLFunction χ s`.

## Main results

* `completedDedekindZetaCyclotomic_one_sub_mul_prod_rootNumber`: the "half" FE
  derivable from the individual FEs plus `completedRiemannZeta_one_sub`. It expresses
  `Λ_K(1-s)` as `p^{(p-2)(s-1/2)} · (∏ W_χ) · Λ_K(s)`.

The missing piece for unconditional closure is the ABSTRACT Dedekind FE:
`Λ_K(1-s) = p^{(p-2)(s-1/2)} · Λ_K(s)` (with no ∏ W_χ factor). This is the
classical Hecke functional equation for cyclotomic Dedekind zeta, provable via
theta functions and Poisson summation for the ring of integers of `ℚ(ζ_p)`.
Equivalently, it follows from the classical statement that the Artin root number
of the regular representation of `Gal(ℚ(ζ_p)/ℚ)` equals `1`. Neither is
currently in mathlib.

Given the abstract Dedekind FE (matching our "half" FE), we conclude `∏ W_χ = 1`
unconditionally (see `prod_rootNumber_eq_one_of_dedekindFE` in `GaussSumProduct`).

## References

* Washington, *Introduction to Cyclotomic Fields*, Corollary 4.6.
* Lang, *Algebraic Number Theory*, Chapter XIII (Hecke's theorem).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

section CompletedDedekindZeta

variable (p : ℕ) [hp : Fact p.Prime]

/-- The completed Dedekind zeta function of the cyclotomic field `ℚ(ζ_p)`,
defined as `completedRiemannZeta s · ∏_{χ ∈ nontrivialCharacters p} completedLFunction χ s`.

This is the product form given by the Dedekind factorization
`ζ_K = ζ · ∏_{χ ≠ 1 mod p} L(χ)` composed with the completion. -/
noncomputable def completedDedekindZetaCyclotomic (s : ℂ) : ℂ :=
  completedRiemannZeta s *
    ∏ χ ∈ nontrivialCharacters p, DirichletCharacter.completedLFunction χ s

/-- The "half" functional equation for the cyclotomic completed Dedekind zeta,
derived from the individual L-function FEs:
`Λ_K(1-s) = p^{(p-2)(s-1/2)} · (∏_{χ ≠ 1} W_χ) · Λ_K(s)`.

The missing input to conclude `Λ_K(1-s) = p^{(p-2)(s-1/2)} · Λ_K(s)` (the CLEAN
Dedekind FE) is the fact that `∏ W_χ = 1`, which comes from the classical Hecke
FE of `ζ_{ℚ(ζ_p)}`. See the module docstring. -/
theorem completedDedekindZetaCyclotomic_one_sub (s : ℂ) :
    completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ) *
        completedDedekindZetaCyclotomic p s := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold completedDedekindZetaCyclotomic
  rw [completedRiemannZeta_one_sub,
    prod_completedLFunction_nontrivial_one_sub p s,
    card_nontrivialCharacters p]
  ring

/-- **Reformulation of WP-E as a Dedekind FE hypothesis**: given the CLEAN Dedekind
FE for `Λ_K`, we deduce `∏ W_χ = 1`. -/
theorem prod_rootNumber_eq_one_of_cleanFE
    (s : ℂ) (hs : 1 < s.re)
    (h_FE : completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s) :
    ∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_half := completedDedekindZetaCyclotomic_one_sub p s
  rw [h_FE] at h_half
  -- h_half: p^{...} · Λ_K(s) = p^{...} · (∏ W_χ) · Λ_K(s)
  have hp_cpow_ne : ((p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ))) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.out.ne_zero))
  have h_Λ_ne : completedDedekindZetaCyclotomic p s ≠ 0 := by
    unfold completedDedekindZetaCyclotomic
    exact mul_ne_zero (completedRiemannZeta_ne_zero_of_one_lt_re hs)
      (Finset.prod_ne_zero_iff.mpr fun χ _ ↦ completedLFunction_ne_zero_of_one_lt_re χ hs)
  -- From h_half: p^{...} · Λ_K(s) = p^{...} · (∏ W_χ) · Λ_K(s).
  -- Cancel p^{...} and Λ_K(s).
  have h_eq : (1 : ℂ) *
      ((p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s) =
    (∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ) *
      ((p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s) := by
    rw [one_mul]
    linear_combination h_half
  have h_prod_ne : (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
      completedDedekindZetaCyclotomic p s ≠ 0 := mul_ne_zero hp_cpow_ne h_Λ_ne
  exact (mul_right_cancel₀ h_prod_ne h_eq).symm

/-- **Converse direction**: if `∏ W_χ = 1`, then the clean Dedekind FE holds.

Together with `prod_rootNumber_eq_one_of_cleanFE` (modulo nonvanishing at a
specific `s`), this shows that proving the clean Dedekind FE is EQUIVALENT to
proving `∏ W_χ = 1`. -/
theorem completedDedekindZetaCyclotomic_one_sub_of_prod_rootNumber_eq_one
    (h_prod : ∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ = 1) (s : ℂ) :
    completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s := by
  rw [completedDedekindZetaCyclotomic_one_sub p s, h_prod, mul_one]

/-- **Capstone using `completedDedekindZetaCyclotomic`**: for `p ≡ 3 mod 4`
prime, given the clean Dedekind FE for `Λ_K` (the object we've defined), the
Gauss sum of the Legendre character equals `I · √p`. -/
theorem gaussSum_legendreDirichlet_eq_I_mul_sqrt_of_cleanFE
    (hp_three_mod_four : p % 4 = 3) (s : ℂ) (hs : 1 < s.re)
    (h_FE : completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) :=
  gaussSum_legendreDirichlet_eq_I_mul_sqrt p hp_three_mod_four
    (prod_rootNumber_eq_one_of_cleanFE p s hs h_FE)

/-- **Explicit capstone using `completedDedekindZetaCyclotomic`**: for
`p ≡ 3 mod 4` prime, given the clean Dedekind FE for `Λ_K`,
`∏_{χ odd} gaussSum χ = I · √p · (-p)^{(p-3)/4}`. -/
theorem gaussSum_oddCharacters_prod_signed_explicit_of_cleanFE
    (hp_three_mod_four : p % 4 = 3) (s : ℂ) (hs : 1 < s.re)
    (h_FE : completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s) :
    ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) :=
  gaussSum_oddCharacters_prod_signed_explicit p hp_three_mod_four
    (gaussSum_legendreDirichlet_eq_I_mul_sqrt_of_cleanFE p hp_three_mod_four s hs h_FE)

end CompletedDedekindZeta

end BernoulliRegular
