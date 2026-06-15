module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Rational-prime local Euler factor for a general number field

For an arbitrary number field `L` and a rational prime `q`, the local Euler
factor of the Dedekind zeta function `ζ_L(s)` at `q`, written as a finite
product over the primes of `𝓞 L` lying above `q`:
$$
\mathrm{localFactor}_L(q, s) :=
  \prod_{Q \mid q}\bigl(1 - N(Q)^{-s}\bigr).
$$

This file provides the definition and basic API (continuity in `s`,
non-vanishing in `Re(s) > 0` for `q.Prime`). The Euler-product identity
relating this finite product to the rational-prime local factor of `ζ_L(s)`
(i.e., `∑' k, idealNormMultiplicity L (q^k) · (q^k)^(-s)`) is proved
separately in REF-21c2a2.

This file generalises the project's `BernoulliRegular.dedekindLocalFactor`
(which is restricted to cyclotomic `K`) to arbitrary number fields. The
naming is in a separate namespace `BernoulliRegular.WeakSplitting` to avoid
clash with the cyclotomic-specific version.

## Main definitions

* `BernoulliRegular.WeakSplitting.dedekindLocalFactorRat`: the local
  Euler factor at a rational prime, as a finite product over the primes of
  `𝓞 L` lying above the rational prime `q`.

## Main results

* `BernoulliRegular.WeakSplitting.absNorm_ne_zero_of_mem_primesOverFinset_rat`:
  if `q.Prime` and `Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 L)`,
  then `Ideal.absNorm Q ≠ 0`.
* `BernoulliRegular.WeakSplitting.dedekindLocalFactorRat_continuous`:
  continuity in `s`.
* `BernoulliRegular.WeakSplitting.dedekindLocalFactorRat_ne_zero`:
  the local factor is nonzero in the half-plane `Re(s) > 0`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField Ideal

/--
The local Euler factor of the Dedekind zeta function of the number field
`L` at the rational prime `q`, written as a finite product over the prime
ideals of `𝓞 L` lying above `q`.
-/
def dedekindLocalFactorRat (L : Type*) [Field L] [NumberField L] (q : ℕ) (s : ℂ) : ℂ :=
  ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L),
    (1 - (Ideal.absNorm Q : ℂ) ^ (-s))

variable (L : Type*) [Field L] [NumberField L]

/--
For a rational prime `q`, every prime `Q ∈ IsDedekindDomain.primesOverFinset (q) (𝓞 L)` is
nonzero, hence has nonzero absolute norm and is `1 < Ideal.absNorm Q`.
-/
theorem one_lt_absNorm_of_mem_primesOverFinset_rat
    {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 L)}
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) :
    1 < Ideal.absNorm Q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  have hQ_mem : Q ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp hQ
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    ⟨Q, hQ_mem.1, Ideal.ne_bot_of_mem_primesOver hq_ne hQ_mem⟩
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

/--
For a rational prime `q`, every prime `Q ∈ IsDedekindDomain.primesOverFinset (q) (𝓞 L)` has
nonzero absolute norm.
-/
theorem absNorm_ne_zero_of_mem_primesOverFinset_rat
    {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 L)}
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) :
    Ideal.absNorm Q ≠ 0 := by
  have := one_lt_absNorm_of_mem_primesOverFinset_rat L hq hQ
  omega

/--
The local Euler factor `dedekindLocalFactorRat L q` is continuous in `s`
when `q` is a rational prime.
-/
theorem dedekindLocalFactorRat_continuous {q : ℕ} (hq : q.Prime) :
    Continuous (fun s : ℂ => dedekindLocalFactorRat L q s) := by
  unfold dedekindLocalFactorRat
  refine continuous_finsetProd _ fun Q hQ => ?_
  refine continuous_const.sub <| continuous_neg.const_cpow (.inl ?_)
  exact_mod_cast absNorm_ne_zero_of_mem_primesOverFinset_rat L hq hQ

/--
For a positive rational prime `q ≥ 2`, the local Euler factor
`dedekindLocalFactorRat L q s` is nonzero in the half-plane `Re(s) > 0`,
since each factor `(1 - N(Q)^{-s})` is nonzero (`N(Q) ≥ 2` and
`‖N(Q)^{-s}‖ < 1` when `Re(s) > 0`).
-/
theorem dedekindLocalFactorRat_ne_zero {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 0 < s.re) :
    dedekindLocalFactorRat L q s ≠ 0 := by
  unfold dedekindLocalFactorRat
  refine Finset.prod_ne_zero_iff.mpr fun Q hQ => ?_
  have hQ_one_lt_real : (1 : ℝ) < (Ideal.absNorm Q : ℝ) := by
    exact_mod_cast one_lt_absNorm_of_mem_primesOverFinset_rat L hq hQ
  have hcast : ((Ideal.absNorm Q : ℝ) : ℂ) = (Ideal.absNorm Q : ℂ) := by push_cast; rfl
  have h_norm_lt : ‖(Ideal.absNorm Q : ℂ) ^ (-s)‖ < 1 := by
    rw [← hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    refine Real.rpow_lt_one_of_one_lt_of_neg hQ_one_lt_real ?_
    simp only [Complex.neg_re]; linarith
  intro h_eq
  rw [(sub_eq_zero.mp h_eq).symm] at h_norm_lt
  exact absurd h_norm_lt (by norm_num)

end WeakSplitting

end BernoulliRegular
