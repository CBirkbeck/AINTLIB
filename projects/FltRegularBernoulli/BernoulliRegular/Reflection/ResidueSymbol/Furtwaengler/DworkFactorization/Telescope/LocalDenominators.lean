module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Telescope.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Local denominator estimates for the finite Dwork telescope

This file connects the exact `Q`-adic order of powers of the rational
residue characteristic with the quotient-local fraction evaluator from
`ConcreteSetup`.  The denominator `ℓ^m` is not invertible at `Q`, so the API
uses an actual local representation `ℓ^m * y = d * x` with
`d ∉ Q`; then `y / d` is the `Q`-local value of `x / ℓ^m`.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open WithZero Multiplicative IsDedekindDomain

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

/-- A fraction with numerator already divisible by its away-from-`Q`
denominator evaluates to the expected quotient class. -/
theorem quotientFractionEvalPrimeCompl_den_mul_eq_mk
    (N : ℕ) (x : 𝓞 R') (d : F.Q.primeCompl) :
    F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N
        ((d : 𝓞 R') * x) d =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  rw [show
      F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N
          ((d : 𝓞 R') * x) d =
        F.toConcreteStickelbergerSetup.quotientFractionEval N
          ((d : 𝓞 R') * x) (d : 𝓞 R') d.property from rfl]
  rw [F.toConcreteStickelbergerSetup.quotientFractionEval_eq_mk_mul_inv]
  rw [map_mul, mul_assoc,
    mul_comm (Ideal.Quotient.mk (F.Q ^ (N + 1)) x),
    ← mul_assoc,
    F.toConcreteStickelbergerSetup.quotient_mk_mul_quotientInvOfNotMemQ,
    one_mul]

/-- Multiplying the evaluated local fraction `y / d` by `ℓ^m` gives the
evaluation of `(ℓ^m * y) / d`. -/
theorem quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl
    (N m : ℕ) (y : 𝓞 R') (d : F.Q.primeCompl) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
        F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N y d =
      F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N
        (((ℓ : 𝓞 R') ^ m) * y) d := by
  simpa [one_mul] using
    (F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl_mul
      N ((ℓ : 𝓞 R') ^ m) y 1 d).symm

/-- If `ℓ^m * y = d * x` with `d ∉ Q`, then `y / d` is the quotient-level
local value of `x / ℓ^m`. -/
theorem quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl_eq_mk_of_eq
    (N m : ℕ) {x y : 𝓞 R'} {d : F.Q.primeCompl}
    (hxy : ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * x) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
        F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N y d =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  rw [F.quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl N m y d, hxy]
  exact F.quotientFractionEvalPrimeCompl_den_mul_eq_mk N x d

/-- Local existence of the quotient by `ℓ^m`: if `x` has at least
`m * (ℓ - 1)` extra `Q`-adic order, then `x / ℓ^m` is represented in the
localization at `Q` by a fraction `y / d` with `d ∉ Q`. -/
theorem exists_primeCompl_natCast_ell_pow_denom_of_mem_Q_pow
    (m s : ℕ) {x : 𝓞 R'}
    (hx : x ∈ F.Q ^ (m * (ℓ - 1) + s)) :
    ∃ y : 𝓞 R', ∃ d : F.Q.primeCompl,
      ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * x ∧ y ∈ F.Q ^ s := by
  classical
  by_cases hx0 : x = 0
  · subst x
    refine ⟨0, 1, ?_, by simp⟩
    simp
  let v : HeightOneSpectrum (𝓞 R') :=
    { asIdeal := F.Q
      isPrime := F.toTraceFormStickelbergerSetup.Q_isPrime
      ne_bot := F.toTraceFormStickelbergerSetup.Q_ne_bot }
  let r : ℕ := m * (ℓ - 1)
  let e : 𝓞 R' := (ℓ : 𝓞 R') ^ m
  have he_ne : e ≠ 0 :=
    pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero)
  have hval_x :
      v.intValuation x ≤ exp (-(r : ℤ)) := by
    have hx' : x ∈ v.asIdeal ^ (r + s) := by
      simpa [v, r, Nat.add_comm] using hx
    have hmain := (v.intValuation_le_pow_iff_mem x (r + s)).2 hx'
    refine hmain.trans ?_
    rw [exp_le_exp]
    omega
  have he_mem : e ∈ F.Q ^ r := by
    simpa [e, r] using
      F.toTraceFormStickelbergerSetup.natCast_ell_pow_mem_Q_pow_mul_pred m
  have he_not_mem : e ∉ F.Q ^ (r + 1) := by
    simpa [e, r, Nat.add_comm] using
      F.natCast_ell_pow_not_mem_Q_pow_mul_pred_succ m
  let Ie : Ideal (𝓞 R') := Ideal.span ({e} : Set (𝓞 R'))
  have hIe_le : Ie ≤ F.Q ^ r := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact he_mem
  have hIe_not_le : ¬ Ie ≤ F.Q ^ (r + 1) := fun hle =>
    he_not_mem (hle (Ideal.mem_span_singleton_self e))
  have hIe_count :
      Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors Ie) = r :=
    Ideal.count_normalizedFactors_eq hIe_le hIe_not_le
  have hIe_ne : Ie ≠ ⊥ := by
    change Ideal.span ({e} : Set (𝓞 R')) ≠ ⊥
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hval_e :
      v.intValuation e = exp (-(r : ℤ)) := by
    rw [v.intValuation_if_neg he_ne]
    have hcount_assoc :
        (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span ({e} : Set (𝓞 R')) : Ideal (𝓞 R'))).factors = r := by
      rw [Ideal.count_associates_factors_eq]
      · simpa [v, Ie] using hIe_count
      · simpa [Ie] using hIe_ne
      · exact F.toTraceFormStickelbergerSetup.Q_isPrime
      · exact F.toTraceFormStickelbergerSetup.Q_ne_bot
    rw [hcount_assoc]
  have hquot_val :
      v.valuation R' (algebraMap (𝓞 R') R' x / algebraMap (𝓞 R') R' e) ≤ 1 := by
    simpa [div_eq_mul_inv, v.valuation_of_algebraMap (K := R'), hval_e] using
      div_le_one_of_le₀ hval_x zero_le'
  obtain ⟨y, d, hfrac⟩ :=
    v.exists_primeCompl_mul_eq_of_integer (K := R')
      (algebraMap (𝓞 R') R' x / algebraMap (𝓞 R') R' e) hquot_val
  have hfield :
      algebraMap (𝓞 R') R' (e * y) =
        algebraMap (𝓞 R') R' ((d : 𝓞 R') * x) := by
    have he_field_ne : algebraMap (𝓞 R') R' e ≠ 0 :=
      NumberField.RingOfIntegers.coe_ne_zero_iff.mpr he_ne
    calc
      algebraMap (𝓞 R') R' (e * y)
          = algebraMap (𝓞 R') R' y * algebraMap (𝓞 R') R' e := by
            rw [map_mul]
            ring
      _ = ((algebraMap (𝓞 R') R' x / algebraMap (𝓞 R') R' e) *
              algebraMap (𝓞 R') R' (d : 𝓞 R')) *
            algebraMap (𝓞 R') R' e := by
            rw [hfrac]
      _ = algebraMap (𝓞 R') R' ((d : 𝓞 R') * x) := by
            rw [map_mul]
            field_simp [he_field_ne]
  have hxy : e * y = (d : 𝓞 R') * x :=
    NumberField.RingOfIntegers.coe_injective hfield
  refine ⟨y, d, hxy, ?_⟩
  refine F.mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
    (m := m) (n := s) ?_
  rw [show ((ℓ : 𝓞 R') ^ m) = e from rfl, hxy]
  exact Ideal.mul_mem_left (F.Q ^ (m * (ℓ - 1) + s)) (d : 𝓞 R') hx

/-- Exact `Q`-adic order of `(ℓ)^m`: after cancelling the local denominator
`ℓ^m`, a represented local fraction has the predicted `Q`-adic order in the
finite quotient. -/
theorem quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_natCast_ell_pow_mul_mem
    (N m s : ℕ) {y : 𝓞 R'} (d : F.Q.primeCompl)
    (hy : ((ℓ : 𝓞 R') ^ m) * y ∈ F.Q ^ (m * (ℓ - 1) + s)) :
    F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N y d ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s) := by
  have hy_mem :
      y ∈ F.Q ^ s :=
    F.mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
      (m := m) (n := s) hy
  rw [show
      F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N y d =
        F.toConcreteStickelbergerSetup.quotientFractionEval N y (d : 𝓞 R') d.property
      from rfl]
  rw [F.toConcreteStickelbergerSetup.quotientFractionEval_eq_mk_mul_inv]
  exact
    (Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s)).mul_mem_right
      (F.toConcreteStickelbergerSetup.quotientInvOfNotMemQ N (d : 𝓞 R') d.property)
      (Ideal.mem_map_of_mem (Ideal.Quotient.mk (F.Q ^ (N + 1))) hy_mem)

/-- Usable local-denominator form: if a high-order numerator `x` is represented
locally as `ℓ^m * y = d * x` with `d ∉ Q`, then the quotient image of
`y / d = x / ℓ^m` lies in `Q^s / Q^(N+1)`. -/
theorem quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_natCast_ell_pow_eq
    (N m s : ℕ) {x y : 𝓞 R'} {d : F.Q.primeCompl}
    (hxy : ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * x)
    (hx : x ∈ F.Q ^ (m * (ℓ - 1) + s)) :
    F.toConcreteStickelbergerSetup.quotientFractionEvalPrimeCompl N y d ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s) := by
  refine F.quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_natCast_ell_pow_mul_mem
    N m s d ?_
  rw [hxy]
  exact Ideal.mul_mem_left (F.Q ^ (m * (ℓ - 1) + s)) (d : 𝓞 R') hx

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular
