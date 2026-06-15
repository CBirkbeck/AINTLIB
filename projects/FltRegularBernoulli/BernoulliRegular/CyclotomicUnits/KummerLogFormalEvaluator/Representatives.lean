import BernoulliRegular.CyclotomicUnits.KummerLogCoefficient

/-!
# Formal-to-finite evaluator bridge for Kummer logarithm coefficients

This file is the home for the remaining CU-11f2b work: turning the formal
normalized Artin-Hasse logarithm into the finite same-prime Dwork quotient
coefficient.  The coefficient-extraction API already lives in
`KummerLogCoefficient`; this file keeps the evaluator proof separated so that
the coefficient file stays focused and below the route line limit.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]
omit [NumberField.IsCMField K] in
/-- Formal coefficient shape for the normalized Kummer Artin-Hasse logarithm:
the `T^d` coefficient is the one-variable normalized coefficient multiplied
by `1 - X^d`.

This is still a formal power-series identity over `Polynomial ℚ`; no
finite quotient or analytic logarithm is involved. -/
theorem coeff_formalKummerLogSeries_eq_one_sub_pow_mul_coeff_normalized
    (d : ℕ) :
    (PowerSeries.coeff (R := KummerLogCoeffRing) d) (formalKummerLogSeries p) =
      (1 - kummerLogScalarX ^ d) *
        (PowerSeries.coeff (R := KummerLogCoeffRing) d)
          (PowerSeries.logOf (formalArtinHasseNormalizedExpMinusOne p)) := by
  simp [formalKummerLogSeries,
    coeff_logOf_formalArtinHasseScaledNormalizedExpMinusOne_eq_pow_mul]
  ring

omit [NumberField.IsCMField K] in
/-- The degree-one formal coefficient of the normalized Kummer logarithm. -/
theorem coeff_formalKummerLogSeries_one (hp_three : 3 ≤ p) :
    (PowerSeries.coeff (R := KummerLogCoeffRing) 1)
        (formalKummerLogSeries p) =
      (1 - kummerLogScalarX) * Polynomial.C (1 / 2 : ℚ) := by
  rw [coeff_formalKummerLogSeries_eq_one_sub_pow_mul_coeff_normalized,
    coeff_logOf_formalArtinHasseNormalizedExpMinusOne_one hp_three]
  ring

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The chosen rational-padic lift of the formal Kummer coefficient in a
matrix row after specializing the scalar at the column residue.

This is a Teichmüller lift of the already proved mod-`p` formal coefficient.
It is deliberately an integral lift, not a fake map `ℚ → ZMod p`. -/
noncomputable def kummerLogFormalEvenRowCoeffLift
    (hp_three : 3 ≤ p) (a j : Fin (kummerLogRank p)) :
    RationalPadicIntegerRing p :=
  rationalPadicTeichmuller p
    (Polynomial.eval
      (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
      (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)))

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- A low-degree polynomial whose even row coefficients lift the formal
Kummer logarithm coefficients after specializing the scalar at the selected
column residue. -/
noncomputable def kummerLogFormalEvenRowRepresentative
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    Polynomial (RationalPadicIntegerRing p) :=
  ∑ j : Fin (kummerLogRank p),
    Polynomial.monomial (2 * kummerLogRowIndex (p := p) j)
      (kummerLogFormalEvenRowCoeffLift (p := p) hp_three a j)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The formal even-row representative has degree `< p - 1`, so it can be
evaluated in the Dwork quotient modulo `varpi^(p - 1)`. -/
theorem kummerLogFormalEvenRowRepresentative_natDegree_lt
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogFormalEvenRowRepresentative (p := p) hp_three a).natDegree <
      p - 1 := by
  classical
  have hlt : p - 3 < p - 1 := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp_three
    simp
  refine lt_of_le_of_lt ?_ hlt
  dsimp [kummerLogFormalEvenRowRepresentative]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.univ) (n := p - 3)
    (f := fun j : Fin (kummerLogRank p) =>
      Polynomial.monomial (2 * kummerLogRowIndex (p := p) j)
        (kummerLogFormalEvenRowCoeffLift (p := p) hp_three a j)) ?_
  intro j _hj
  exact (Polynomial.natDegree_monomial_le
    (kummerLogFormalEvenRowCoeffLift (p := p) hp_three a j)).trans
      (two_mul_kummerLogRowIndex_le_sub_three (p := p) j)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The coefficient of the representative in the selected even row is the
chosen rational-padic lift of the formal coefficient. -/
theorem kummerLogFormalEvenRowRepresentative_coeff_even
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    (kummerLogFormalEvenRowRepresentative (p := p) hp_three a).coeff
        ((kummerLogEvenPowerIndex (p := p) hp_five j).1 : ℕ) =
      kummerLogFormalEvenRowCoeffLift (p := p) hp_three a j := by
  classical
  rw [kummerLogEvenPowerIndex_val]
  dsimp [kummerLogFormalEvenRowRepresentative]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _hb hbj
    rw [if_neg]
    intro h
    apply hbj
    apply Fin.ext
    omega
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- Reducing the selected even-row coefficient of the representative modulo
`p` recovers the formal `ZMod p` Kummer coefficient. -/
theorem kummerLogFormalEvenRowRepresentative_coeff_even_modP
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    rationalPadicIntegerToZMod p
        ((kummerLogFormalEvenRowRepresentative (p := p) hp_three a).coeff
          ((kummerLogEvenPowerIndex (p := p) hp_five j).1 : ℕ)) =
      Polynomial.eval
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) := by
  rw [kummerLogFormalEvenRowRepresentative_coeff_even,
    kummerLogFormalEvenRowCoeffLift,
    rationalPadicIntegerToZMod_teichmuller]

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The selected Kummer column index is a nonzero residue modulo `p`. -/
theorem kummerLogColumnIndex_zmod_ne_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ≠ 0 := by
  intro hzero
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have hk_pos : 0 < k := by
    have hk_two := kummerLogColumnIndex_two_le (p := p) hp_three a
    omega
  have hk_lt : k < p := kummerLogColumnIndex_lt_p (p := p) hp_three a
  have hp_dvd : p ∣ k := by
    simpa [k] using (ZMod.natCast_eq_zero_iff k p).mp hzero
  have hp_le : p ≤ k := Nat.le_of_dvd hk_pos hp_dvd
  omega

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The Kummer column residue as a cyclotomic Galois-group element. -/
noncomputable def kummerLogColumnDelta
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    CyclotomicUnitDelta p :=
  Units.mk0
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
    (kummerLogColumnIndex_zmod_ne_zero (p := p) hp_three a)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
@[simp]
theorem kummerLogColumnDelta_val
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ((kummerLogColumnDelta (p := p) hp_three a : CyclotomicUnitDelta p) :
        ZMod p) =
      (kummerLogColumnIndex (p := p) hp_three a : ZMod p) :=
  rfl
end CyclotomicUnits
end BernoulliRegular

end
