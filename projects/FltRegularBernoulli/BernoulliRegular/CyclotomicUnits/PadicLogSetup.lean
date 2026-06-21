module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseGlobalDecomposition
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseValuationTrace
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse
public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Local `p`-adic setup for the cyclotomic-unit route

This file exposes the completed local cyclotomic model already available in
the Furtwängler development under route-level names for the cyclotomic-unit
reflection proof.

The local model here uses the proved uniformizer `lambda = zeta_p - 1`.  The
formal Artin-Hasse inverse package below records the corrected Dwork
normalization: the inverse of `E_p(T) - 1` has integral coefficients, starts
with `T`, and satisfies the formal sign identity behind `c(varpi) = -varpi`.

The originally advertised stronger Artin-Hasse/Dwork parameter package,

```text
varpi^(p - 1) = -p,     E_p(varpi) = zeta_p,     c(varpi) = -varpi,
```

is false for the standard Artin-Hasse normalization.  The analytic step that
is still missing is the construction of the completed local element
`varpi = (E_p(T)-1)^{-1}(zeta_p - 1)` together with the real fixed-basis
theorem.  This file deliberately does not replace that missing construction
by a bundled hypothesis.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup

namespace FormalDwork

variable (p : ℕ) [Fact p.Prime]

/-- The Artin-Hasse logarithm series `L_p(T) = sum T^(p^n)/p^n`. -/
abbrev logSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseLogSeries p

/-- The Artin-Hasse exponential series `E_p(T) = exp(L_p(T))`. -/
abbrev expSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseExpSeries p

/-- The series `E_p(T) - 1`, whose inverse is the corrected Dwork parameter
series. -/
abbrev expMinusOneSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseExpMinusOneSeries p

/-- The formal inverse of `E_p(T) - 1`.  Evaluated at `zeta_p - 1` in a
complete local ring, this is the corrected Dwork parameter from CU-09. -/
abbrev inverseSeries : PowerSeries ℚ :=
  Furtwaengler.artinHasseExpInverseSeries p

/-- The Artin-Hasse logarithm series has zero constant term. -/
@[simp]
theorem logSeries_constantCoeff :
    PowerSeries.constantCoeff (logSeries p) = 0 :=
  Furtwaengler.artinHasseLogSeries_constantCoeff p

/-- The Artin-Hasse logarithm series is substitutable. -/
theorem logSeries_hasSubst :
    PowerSeries.HasSubst (logSeries p) :=
  Furtwaengler.artinHasseLogSeries_hasSubst p

/-- The Artin-Hasse exponential series has constant term `1`. -/
@[simp]
theorem expSeries_constantCoeff :
    PowerSeries.constantCoeff (expSeries p) = 1 :=
  Furtwaengler.artinHasseExpSeries_constantCoeff p

/-- The series `E_p(T) - 1` has zero constant term. -/
@[simp]
theorem expMinusOneSeries_constantCoeff :
    PowerSeries.constantCoeff (expMinusOneSeries p) = 0 :=
  Furtwaengler.artinHasseExpMinusOneSeries_constantCoeff p

/-- The series `E_p(T) - 1` has linear coefficient `1`. -/
@[simp]
theorem expMinusOneSeries_coeff_one :
    (PowerSeries.coeff (R := ℚ) 1) (expMinusOneSeries p) = 1 :=
  Furtwaengler.artinHasseExpMinusOneSeries_coeff_one p

/-- The formal inverse of `E_p(T) - 1` has zero constant term. -/
@[simp]
theorem inverseSeries_constantCoeff :
    PowerSeries.constantCoeff (inverseSeries p) = 0 :=
  Furtwaengler.artinHasseExpInverseSeries_constantCoeff p

/-- The formal inverse of `E_p(T) - 1` has linear coefficient `1`. -/
@[simp]
theorem inverseSeries_coeff_one :
    (PowerSeries.coeff (R := ℚ) 1) (inverseSeries p) = 1 :=
  Furtwaengler.artinHasseExpInverseSeries_coeff_one p

/-- For odd `p`, the formal inverse of `E_p(T) - 1` has quadratic coefficient `-1/2`. -/
theorem inverseSeries_coeff_two_of_two_lt (hp_two : 2 < p) :
    (PowerSeries.coeff (R := ℚ) 2) (inverseSeries p) = -(1 / 2 : ℚ) :=
  Furtwaengler.artinHasseExpInverseSeries_coeff_two_of_two_lt p hp_two

/-- The formal inverse of `E_p(T) - 1` is substitutable. -/
theorem inverseSeries_hasSubst :
    PowerSeries.HasSubst (inverseSeries p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (inverseSeries_constantCoeff p)

/-- The series `E_p(T) - 1` has `p`-integral coefficients. -/
theorem expMinusOneSeries_isPIntegral :
    Furtwaengler.DieudonneDwork.IsRIntegralPS p (expMinusOneSeries p) :=
  Furtwaengler.artinHasseExpMinusOneSeries_isRIntegral p

/-- The formal inverse of `E_p(T) - 1` has `p`-integral coefficients. -/
theorem inverseSeries_isPIntegral :
    Furtwaengler.DieudonneDwork.IsRIntegralPS p (inverseSeries p) :=
  Furtwaengler.artinHasseExpInverseSeries_isRIntegral p

/-- Formal right-inverse identity: `(E_p(T)-1)(G_p(T)) = T`. -/
theorem expMinusOneSeries_subst_inverse :
    (expMinusOneSeries p).subst (inverseSeries p) =
      (PowerSeries.X : PowerSeries ℚ) :=
  Furtwaengler.artinHasseExpMinusOneSeries_subst_inverse p

/-- Equivalent formal identity: `E_p(G_p(T)) = 1 + T`. -/
theorem expSeries_subst_inverse :
    (expSeries p).subst (inverseSeries p) =
      1 + (PowerSeries.X : PowerSeries ℚ) :=
  Furtwaengler.artinHasseExpSeries_subst_inverse p

/-- The other formal inverse identity: `G_p(E_p(T)-1) = T`. -/
theorem inverseSeries_subst_expMinusOneSeries :
    (inverseSeries p).subst (expMinusOneSeries p) =
      (PowerSeries.X : PowerSeries ℚ) := by
  let P : PowerSeries ℚ := expMinusOneSeries p
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P, expMinusOneSeries]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  simpa [P, inverseSeries, expMinusOneSeries,
    Furtwaengler.artinHasseExpInverseSeries] using
    PowerSeries.subst_substInv_left P (by simp [P, expMinusOneSeries])

/-- Formal identity `log(E_p(T)) = L_p(T)`.

This is the power-series identity that should be evaluated at the completed
Dwork parameter before applying the ordinary `p`-adic logarithm. -/
theorem logOf_expSeries_eq_logSeries :
    PowerSeries.logOf (expSeries p) = logSeries p := by
  let L : PowerSeries ℚ := logSeries p
  let E : PowerSeries ℚ := expSeries p
  have hE_const : PowerSeries.constantCoeff E = 1 := by
    simp [E, expSeries]
  have hE_sub_const : PowerSeries.constantCoeff (E - 1) = 0 := by
    simp [hE_const]
  have hE_subst : PowerSeries.HasSubst (E - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hE_sub_const
  have hE_deriv :
      (PowerSeries.derivative ℚ) E =
        E * (PowerSeries.derivative ℚ) L := by
    simp only [E, L, expSeries]
    unfold Furtwaengler.artinHasseExpSeries
    rw [PowerSeries.derivative_subst ℚ (logSeries_hasSubst p), PowerSeries.derivative_exp]
  have hgeom :
      PowerSeries.subst (E - 1) ((PowerSeries.derivative ℚ) (PowerSeries.log ℚ)) *
          E = 1 := by
    have hbase :
        (PowerSeries.derivative ℚ) (PowerSeries.log ℚ) *
            (1 + (PowerSeries.X : PowerSeries ℚ)) = 1 := by
      rw [PowerSeries.deriv_log]
      let G : PowerSeries ℚ := PowerSeries.mk fun n ↦ ((-1 : ℚ) ^ n)
      change G * (1 + PowerSeries.X) = 1
      rw [mul_add, mul_one]
      ext n
      cases n with
      | zero =>
          simp [G]
      | succ n =>
          rw [map_add, PowerSeries.coeff_succ_mul_X]
          simp [G, pow_succ]
    have hsubst :
        PowerSeries.subst (E - 1)
            ((PowerSeries.derivative ℚ) (PowerSeries.log ℚ) *
              (1 + (PowerSeries.X : PowerSeries ℚ))) =
          PowerSeries.subst (E - 1) (1 : PowerSeries ℚ) := by
      rw [hbase]
    rw [PowerSeries.subst_mul hE_subst, PowerSeries.subst_add hE_subst,
      PowerSeries.subst_X hE_subst] at hsubst
    have hsubst_one :
        PowerSeries.subst (E - 1) (1 : PowerSeries ℚ) = 1 := by
      simpa using
        (PowerSeries.subst_C (a := (E - 1 : PowerSeries ℚ)) (r := (1 : ℚ)))
    rw [hsubst_one] at hsubst
    simpa [hE_sub_const, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsubst
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ℚ hE_subst, map_sub,
      Derivation.map_one_eq_zero, sub_zero, hE_deriv]
    calc
      PowerSeries.subst (E - 1) ((PowerSeries.derivative ℚ) (PowerSeries.log ℚ)) *
          (E * (PowerSeries.derivative ℚ) L)
          =
        (PowerSeries.subst (E - 1) ((PowerSeries.derivative ℚ) (PowerSeries.log ℚ)) *
            E) * (PowerSeries.derivative ℚ) L := by ring
      _ = (PowerSeries.derivative ℚ) L := by rw [hgeom, one_mul]
  · rw [PowerSeries.constantCoeff_logOf hE_const]
    simp

/-- Formal identity after substituting the corrected inverse:
`L_p(G_p(T)) = log(1 + T)`.

This isolates the purely formal part of the intended CU-09c logarithm proof.
The remaining analytic step is evaluating the right hand side at
`T = zeta_p - 1` in the completed local field and proving that this ordinary
`p`-adic logarithm vanishes on the `p`-torsion root of unity. -/
theorem logSeries_subst_inverse_eq_log :
    PowerSeries.subst (inverseSeries p) (logSeries p) = PowerSeries.log ℚ := by
  let H : PowerSeries ℚ := expMinusOneSeries p
  let G : PowerSeries ℚ := inverseSeries p
  have hH0 : PowerSeries.constantCoeff H = 0 := by
    simp [H]
  have hG0 : PowerSeries.constantCoeff G = 0 := by
    simp [G]
  have hH : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH0
  have hG : PowerSeries.HasSubst G :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hG0
  calc
    PowerSeries.subst (inverseSeries p) (logSeries p)
        =
      PowerSeries.subst G (PowerSeries.logOf (expSeries p)) := by
        simp [G, logOf_expSeries_eq_logSeries]
    _ =
      PowerSeries.subst G (PowerSeries.subst H (PowerSeries.log ℚ)) := by
        simp [H, expSeries, Furtwaengler.artinHasseExpMinusOneSeries,
          PowerSeries.logOf_eq]
    _ =
      PowerSeries.subst (PowerSeries.subst G H) (PowerSeries.log ℚ) := by
        rw [PowerSeries.subst_comp_subst_apply hH hG]
    _ =
      PowerSeries.log ℚ := by
        rw [show PowerSeries.subst G H = (PowerSeries.X : PowerSeries ℚ) by
          simpa [G, H] using expMinusOneSeries_subst_inverse (p := p)]
        exact PowerSeries.X_subst (PowerSeries.log ℚ)

/-- Integral-coefficient form of `E_p(G_p(T)) = 1 + T`, transported to any
coefficient ring receiving the `p`-integral rational coefficients. -/
theorem expSeries_mapTo_subst_inverse
    {A : Type*} [CommRing A]
    (φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A) :
    PowerSeries.subst
        ((inverseSeries_isPIntegral p).mapTo φ)
        ((show Furtwaengler.DieudonneDwork.IsRIntegralPS p
            (Furtwaengler.artinHasseExpSeries p) from
          Furtwaengler.artinHasseExpSeries_coeff_isRIntegral p).mapTo φ) =
      1 + (PowerSeries.X : PowerSeries A) :=
  Furtwaengler.artinHasseExpSeries_mapTo_subst_inverse p φ

/-- The inverse series starts with `T`.  This is the formal source of the
eventual congruence `varpi == zeta_p - 1 mod (zeta_p - 1)^2`. -/
theorem inverseSeries_trunc_two :
    PowerSeries.trunc 2 (inverseSeries p) =
      PowerSeries.trunc 2 (PowerSeries.X : PowerSeries ℚ) := by
  ext n
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hn : n < 2
  · interval_cases n <;> simp [inverseSeries]
  · simp [hn]

/-- The series `E_p(T)-1` also starts with `T`. -/
theorem expMinusOneSeries_trunc_two :
    PowerSeries.trunc 2 (expMinusOneSeries p) =
      PowerSeries.trunc 2 (PowerSeries.X : PowerSeries ℚ) := by
  ext n
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hn : n < 2
  · interval_cases n <;> simp [expMinusOneSeries]
  · simp [hn]

/-- For odd `p`, the Artin-Hasse logarithm is an odd formal series. -/
theorem logSeries_rescale_neg (hp_two : 2 < p) :
    PowerSeries.rescale (-1 : ℚ) (logSeries p) = -logSeries p := by
  have hp_odd : Odd p := by
    rcases (Fact.out : Nat.Prime p).eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  ext n
  rw [PowerSeries.coeff_rescale, map_neg, Furtwaengler.artinHasseLogSeries_coeff]
  by_cases hpow : p ^ Nat.log p n = n ∧ n ≠ 0
  · rw [if_pos hpow]
    have hn_odd : Odd n := by
      rw [← hpow.1]
      exact hp_odd.pow
    rw [Odd.neg_one_pow (α := ℚ) hn_odd]
    ring
  · rw [if_neg hpow]
    ring

/-- Substituting `L_p(T)` into `exp(-T)` agrees with substituting `-L_p(T)` into `exp`. -/
theorem subst_logSeries_evalNeg_exp :
    PowerSeries.subst (logSeries p) (PowerSeries.evalNegHom (PowerSeries.exp ℚ)) =
      PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ) := by
  rw [PowerSeries.evalNegHom, PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply]
  · have hLX :
        PowerSeries.subst (logSeries p) ((-1 : ℚ) • (PowerSeries.X : PowerSeries ℚ)) =
          -logSeries p := by
      rw [PowerSeries.subst_smul (logSeries_hasSubst p), PowerSeries.subst_X (logSeries_hasSubst p)]
      simp
    rw [hLX]
  · exact PowerSeries.HasSubst.smul_X (-1 : ℚ) ()
  · exact logSeries_hasSubst p

/-- The series `exp(-L_p(T))` is a right inverse of `E_p(T)`. -/
theorem subst_neg_log_exp_mul_expSeries :
    PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ) * expSeries p = 1 := by
  have h0 := congrArg
    (fun F : PowerSeries ℚ ↦ PowerSeries.subst (logSeries p) F)
    (PowerSeries.exp_mul_exp_neg_eq_one (A := ℚ))
  have h :
      PowerSeries.subst (logSeries p)
          (PowerSeries.exp ℚ * PowerSeries.evalNegHom (PowerSeries.exp ℚ)) =
        PowerSeries.subst (logSeries p) (1 : PowerSeries ℚ) := h0
  rw [PowerSeries.subst_mul (logSeries_hasSubst p), subst_logSeries_evalNeg_exp] at h
  have h1 : PowerSeries.subst (logSeries p) (1 : PowerSeries ℚ) = 1 := by
    simpa using
      (PowerSeries.subst_C (a := logSeries p) (r := (1 : ℚ)))
  rw [h1] at h
  rw [mul_comm]
  exact h

/-- Formal identity `E_p(-T) = E_p(T)^{-1}`, stated without choosing the
inverse: the product is `1`. -/
theorem expSeries_rescale_neg_mul_self (hp_two : 2 < p) :
    PowerSeries.rescale (-1 : ℚ) (expSeries p) * expSeries p = 1 := by
  have hneg :
      PowerSeries.rescale (-1 : ℚ) (expSeries p) =
        PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ) := by
    change PowerSeries.rescale (-1 : ℚ) (Furtwaengler.artinHasseExpSeries p) =
      PowerSeries.subst (-(logSeries p)) (PowerSeries.exp ℚ)
    unfold Furtwaengler.artinHasseExpSeries
    rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply]
    · have h := logSeries_rescale_neg p hp_two
      rw [PowerSeries.rescale_eq_subst] at h
      simpa using
        congrArg (fun L ↦ PowerSeries.subst L (PowerSeries.exp ℚ)) h
    · exact logSeries_hasSubst p
    · exact PowerSeries.HasSubst.smul_X (-1 : ℚ) ()
  rw [hneg]
  exact subst_neg_log_exp_mul_expSeries p

/-- The same sign identity in terms of `H_p(T) = E_p(T)-1`.  This is the
formal source of the conjugation relation for the corrected local parameter. -/
theorem one_add_rescale_neg_expMinusOneSeries_mul_self (hp_two : 2 < p) :
    (1 + PowerSeries.rescale (-1 : ℚ) (expMinusOneSeries p)) *
        (1 + expMinusOneSeries p) = 1 := by
  simpa [expMinusOneSeries, expSeries, Furtwaengler.artinHasseExpMinusOneSeries,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    expSeries_rescale_neg_mul_self p hp_two

/-- Substituting the inverse parameter into the Artin--Hasse sign identity gives
the formal fractional-linear conjugation formula in denominator-cleared form:
`H_p(-G_p(S)) * (1 + S) = -S`, where `H_p(T) = E_p(T)-1`. -/
theorem expMinusOneSeries_subst_neg_inverse_mul_one_add_X_eq_neg_X
    (hp_two : 2 < p) :
    (PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p)) *
        (1 + (PowerSeries.X : PowerSeries ℚ)) =
      -(PowerSeries.X : PowerSeries ℚ) := by
  let H : PowerSeries ℚ := expMinusOneSeries p
  let G : PowerSeries ℚ := inverseSeries p
  have hG : PowerSeries.HasSubst G := by
    simpa [G] using inverseSeries_hasSubst p
  have hnegG : PowerSeries.HasSubst (-G) := by
    simpa using hG.smul' (-1 : ℚ)
  have hsubst := congrArg
    (fun F : PowerSeries ℚ ↦ PowerSeries.subst G F)
    (one_add_rescale_neg_expMinusOneSeries_mul_self p hp_two)
  change PowerSeries.subst G
      ((1 + PowerSeries.rescale (-1 : ℚ) (expMinusOneSeries p)) *
        (1 + expMinusOneSeries p)) =
    PowerSeries.subst G (1 : PowerSeries ℚ) at hsubst
  rw [PowerSeries.subst_mul hG] at hsubst
  have hsubst_one :
      PowerSeries.subst G (1 : PowerSeries ℚ) = 1 := by
    simpa using PowerSeries.subst_C (a := G) (r := (1 : ℚ))
  have hleft :
      PowerSeries.subst G (1 + PowerSeries.rescale (-1 : ℚ) H) =
        1 + PowerSeries.subst (-G) H := by
    rw [PowerSeries.subst_add hG, hsubst_one]
    congr 1
    rw [PowerSeries.rescale_eq_subst]
    calc
      PowerSeries.subst G
          (PowerSeries.subst ((-1 : ℚ) • (PowerSeries.X : PowerSeries ℚ)) H) =
          PowerSeries.subst
            (PowerSeries.subst G ((-1 : ℚ) • (PowerSeries.X : PowerSeries ℚ))) H :=
            PowerSeries.subst_comp_subst_apply
              (PowerSeries.HasSubst.smul_X' (-1 : ℚ)) hG H
      _ = PowerSeries.subst (-G) H := by
            rw [PowerSeries.subst_smul hG, PowerSeries.subst_X hG]
            simp [G]
  have hright :
      PowerSeries.subst G (1 + H) =
        1 + (PowerSeries.X : PowerSeries ℚ) := by
    rw [PowerSeries.subst_add hG, hsubst_one]
    rw [show PowerSeries.subst G H = (PowerSeries.X : PowerSeries ℚ) by
      simpa [H, G] using expMinusOneSeries_subst_inverse (p := p)]
  have hmul :
      (1 + PowerSeries.subst (-G) H) *
          (1 + (PowerSeries.X : PowerSeries ℚ)) = 1 := by
    simpa [H, hleft, hright, hsubst_one] using hsubst
  simpa [H, G] using
    (calc
      PowerSeries.subst (-G) H * (1 + (PowerSeries.X : PowerSeries ℚ)) =
          (1 + PowerSeries.subst (-G) H) *
              (1 + (PowerSeries.X : PowerSeries ℚ)) -
            (1 + (PowerSeries.X : PowerSeries ℚ)) := by
            ring
      _ = 1 - (1 + (PowerSeries.X : PowerSeries ℚ)) := by
            rw [hmul]
      _ = -(PowerSeries.X : PowerSeries ℚ) := by
            ring)

/-- The inverse series carries the formal conjugate parameter
`H_p(-G_p(S))` to `-G_p(S)`. -/
theorem inverseSeries_subst_expMinusOneSeries_subst_neg_inverse :
    PowerSeries.subst
        (PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p))
        (inverseSeries p) =
      -(inverseSeries p) := by
  let H : PowerSeries ℚ := expMinusOneSeries p
  let G : PowerSeries ℚ := inverseSeries p
  have hH : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (expMinusOneSeries_constantCoeff p)
  have hnegG : PowerSeries.HasSubst (-G) := by
    have hG : PowerSeries.HasSubst G := by
      simpa [G] using inverseSeries_hasSubst p
    simpa using hG.smul' (-1 : ℚ)
  calc
    PowerSeries.subst (PowerSeries.subst (-G) H) G =
        PowerSeries.subst (-G) (PowerSeries.subst H G) :=
          (PowerSeries.subst_comp_subst_apply hH hnegG G).symm
    _ = PowerSeries.subst (-G) (PowerSeries.X : PowerSeries ℚ) := by
          rw [show PowerSeries.subst H G = (PowerSeries.X : PowerSeries ℚ) by
            simpa [H, G] using inverseSeries_subst_expMinusOneSeries (p := p)]
    _ = -G := by
          rw [PowerSeries.subst_X hnegG]
    _ = -(inverseSeries p) := by
          rfl

/-- Integral-coefficient form of the denominator-cleared sign identity,
transported to any coefficient ring receiving the `p`-integral rational
coefficients. -/
theorem expMinusOneSeries_mapTo_subst_neg_inverse_mul_one_add_X_eq_neg_X
    {A : Type*} [CommRing A]
    (φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A)
    (hp_two : 2 < p) :
    PowerSeries.subst
        (-((inverseSeries_isPIntegral p).mapTo φ))
        ((expMinusOneSeries_isPIntegral p).mapTo φ) *
        (1 + (PowerSeries.X : PowerSeries A)) =
      -(PowerSeries.X : PowerSeries A) := by
  let hInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (inverseSeries p) :=
    inverseSeries_isPIntegral p
  let hH : Furtwaengler.DieudonneDwork.IsRIntegralPS p (expMinusOneSeries p) :=
    expMinusOneSeries_isPIntegral p
  let hNegInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (-(inverseSeries p)) :=
    hInv.neg
  have hNegInv0 : PowerSeries.constantCoeff (-(inverseSeries p)) = 0 := by
    simp
  let inner : PowerSeries ℚ :=
    PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p)
  let hInner : Furtwaengler.DieudonneDwork.IsRIntegralPS p inner :=
    hH.subst hNegInv hNegInv0
  have hInnerMap :
      hInner.mapTo φ =
        PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
    calc
      hInner.mapTo φ =
          PowerSeries.subst (hNegInv.mapTo φ) (hH.mapTo φ) :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
              φ hH hNegInv hNegInv0
      _ = PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
            rw [show hNegInv.mapTo φ = -(hInv.mapTo φ) by
              simpa [hNegInv, hInv] using
                Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv]
  let hOneAddX : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (1 + (PowerSeries.X : PowerSeries ℚ)) :=
    (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p).add
      (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p)
  have hOneAddXMap :
      hOneAddX.mapTo φ = 1 + (PowerSeries.X : PowerSeries A) := by
    calc
      hOneAddX.mapTo φ =
          (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p).mapTo φ +
            (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p).mapTo φ :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_add
              φ (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p)
                (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p)
      _ = 1 + (PowerSeries.X : PowerSeries A) := by
            simp
  calc
    PowerSeries.subst
        (-((inverseSeries_isPIntegral p).mapTo φ))
        ((expMinusOneSeries_isPIntegral p).mapTo φ) *
        (1 + (PowerSeries.X : PowerSeries A)) =
        hInner.mapTo φ * hOneAddX.mapTo φ := by
          rw [hInnerMap, hOneAddXMap]
    _ = (hInner.mul hOneAddX).mapTo φ :=
          (Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_mul
            φ hInner hOneAddX).symm
    _ = ((Furtwaengler.DieudonneDwork.IsRIntegralPS.X p).neg).mapTo φ :=
          Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
            φ (hInner.mul hOneAddX)
            ((Furtwaengler.DieudonneDwork.IsRIntegralPS.X p).neg)
            (by
              simpa [inner] using
                expMinusOneSeries_subst_neg_inverse_mul_one_add_X_eq_neg_X
                  (p := p) hp_two)
    _ = -(PowerSeries.X : PowerSeries A) := by
          simpa using Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg
            φ (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p)

/-- Integral-coefficient form of `G_p(H_p(-G_p(T))) = -G_p(T)`,
transported to any coefficient ring receiving the `p`-integral rational
coefficients. -/
theorem inverseSeries_mapTo_subst_expMinusOneSeries_subst_neg_inverse
    {A : Type*} [CommRing A]
    (φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A) :
    PowerSeries.subst
        (PowerSeries.subst
          (-((inverseSeries_isPIntegral p).mapTo φ))
          ((expMinusOneSeries_isPIntegral p).mapTo φ))
        ((inverseSeries_isPIntegral p).mapTo φ) =
      -((inverseSeries_isPIntegral p).mapTo φ) := by
  let hInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (inverseSeries p) :=
    inverseSeries_isPIntegral p
  let hH : Furtwaengler.DieudonneDwork.IsRIntegralPS p (expMinusOneSeries p) :=
    expMinusOneSeries_isPIntegral p
  let hNegInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p (-(inverseSeries p)) :=
    hInv.neg
  have hNegInv0 : PowerSeries.constantCoeff (-(inverseSeries p)) = 0 := by
    simp
  let inner : PowerSeries ℚ :=
    PowerSeries.subst (-(inverseSeries p)) (expMinusOneSeries p)
  let hInner : Furtwaengler.DieudonneDwork.IsRIntegralPS p inner :=
    hH.subst hNegInv hNegInv0
  have hInner0 : PowerSeries.constantCoeff inner = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero
      (by simp : PowerSeries.constantCoeff (-(inverseSeries p)) = 0)
      (expMinusOneSeries p) (expMinusOneSeries_constantCoeff p)
  have hInnerMap :
      hInner.mapTo φ =
        PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
    calc
      hInner.mapTo φ =
          PowerSeries.subst (hNegInv.mapTo φ) (hH.mapTo φ) :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
              φ hH hNegInv hNegInv0
      _ = PowerSeries.subst (-(hInv.mapTo φ)) (hH.mapTo φ) := by
            rw [show hNegInv.mapTo φ = -(hInv.mapTo φ) by
              simpa [hNegInv, hInv] using
                Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv]
  calc
    PowerSeries.subst
        (PowerSeries.subst
          (-((inverseSeries_isPIntegral p).mapTo φ))
          ((expMinusOneSeries_isPIntegral p).mapTo φ))
        ((inverseSeries_isPIntegral p).mapTo φ) =
        PowerSeries.subst (hInner.mapTo φ) (hInv.mapTo φ) := by
          rw [hInnerMap]
    _ = (hInv.subst hInner hInner0).mapTo φ :=
          (Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
            φ hInv hInner hInner0).symm
    _ = hInv.neg.mapTo φ :=
          Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
            φ (hInv.subst hInner hInner0) hInv.neg
            (by
              simpa [inner] using
                inverseSeries_subst_expMinusOneSeries_subst_neg_inverse
                  (p := p))
    _ = -(hInv.mapTo φ) :=
          Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv

/-- Algebraic form of the corrected Eisenstein equation.  Once a completed
local element `varpi` is known to satisfy
`varpi + varpi^p / p + varpi * tail = 0`, this lemma rewrites it as
`varpi^(p-1) = -p * (1 + tail)`. -/
theorem correctedPowEquation_of_logTail_eq_zero
    {A : Type*} [Field A] {varpi tail : A}
    (hpA : (p : A) ≠ 0) (hvarpi : varpi ≠ 0)
    (hlog : varpi + varpi ^ p / (p : A) + varpi * tail = 0) :
    varpi ^ (p - 1) = -(p : A) * (1 + tail) := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hmul : varpi ^ p = -(p : A) * (varpi * (1 + tail)) := by
    have h1 : varpi ^ p / (p : A) = -(varpi * (1 + tail)) := by
      linear_combination hlog
    calc
      varpi ^ p = (p : A) * (varpi ^ p / (p : A)) := by
        field_simp [hpA]
      _ = (p : A) * (-(varpi * (1 + tail))) := by
        rw [h1]
      _ = -(p : A) * (varpi * (1 + tail)) := by
        ring
  have hpow : varpi ^ p = varpi ^ (p - 1) * varpi := by
    rw [← pow_succ, Nat.sub_one_add_one (Nat.ne_of_gt hp_pos)]
  rw [hpow] at hmul
  refine mul_right_cancel₀ hvarpi ?_
  rw [hmul]
  ring

/-- Guard lemma for the false exact normalization: under the same logarithmic
equation, `varpi^(p-1) = -p` can hold only if the higher Artin-Hasse tail is
zero. -/
theorem tail_eq_zero_of_logTail_eq_zero_of_pow_eq_neg
    {A : Type*} [Field A] {varpi tail : A}
    (hpA : (p : A) ≠ 0) (hvarpi : varpi ≠ 0)
    (hlog : varpi + varpi ^ p / (p : A) + varpi * tail = 0)
    (hpow : varpi ^ (p - 1) = -(p : A)) :
    tail = 0 := by
  have hcorr :=
    correctedPowEquation_of_logTail_eq_zero (p := p) hpA hvarpi hlog
  have hmul : (p : A) * tail = 0 := by
    linear_combination hcorr - hpow
  exact (mul_eq_zero.mp hmul).resolve_left hpA

omit [Fact p.Prime] in
/-- The finite Artin-Hasse tail
`sum_{2 <= n <= N} varpi^(p^n - 1) / p^n`.  The eventual CU-09c tail is the
adic limit of these finite tails. -/
def artinHasseTailFinite
    {A : Type*} [Field A] (N : ℕ) (varpi : A) : A :=
  ∑ n ∈ Finset.Icc 2 N, varpi ^ (p ^ n - 1) / (p : A) ^ n

omit [Fact p.Prime] in
/-- The finite corrected Eisenstein unit factor `1 + tail_N`. -/
def artinHasseTailUnitFinite
    {A : Type*} [Field A] (N : ℕ) (varpi : A) : A :=
  1 + artinHasseTailFinite p N varpi

/-- Finite-tail form of the corrected Eisenstein equation.  This is the exact
algebraic step used after a completed logarithm evaluation has identified the
limit of the finite tails. -/
theorem correctedPowEquation_of_logTailFinite_eq_zero
    {A : Type*} [Field A] {N : ℕ} {varpi : A}
    (hpA : (p : A) ≠ 0) (hvarpi : varpi ≠ 0)
    (hlog :
      varpi + varpi ^ p / (p : A) +
          varpi * artinHasseTailFinite p N varpi = 0) :
    varpi ^ (p - 1) = -(p : A) * artinHasseTailUnitFinite p N varpi :=
  correctedPowEquation_of_logTail_eq_zero (p := p) hpA hvarpi hlog

/-- Finite-tail guard for the false exact normalization.  Under the same
logarithmic equation, `varpi^(p-1) = -p` forces the finite tail to vanish. -/
theorem artinHasseTailFinite_eq_zero_of_logTailFinite_eq_zero_of_pow_eq_neg
    {A : Type*} [Field A] {N : ℕ} {varpi : A}
    (hpA : (p : A) ≠ 0) (hvarpi : varpi ≠ 0)
    (hlog :
      varpi + varpi ^ p / (p : A) +
          varpi * artinHasseTailFinite p N varpi = 0)
    (hpow : varpi ^ (p - 1) = -(p : A)) :
    artinHasseTailFinite p N varpi = 0 :=
  tail_eq_zero_of_logTail_eq_zero_of_pow_eq_neg
    (p := p) hpA hvarpi hlog hpow

omit [Fact p.Prime] in
/-- The precision-two finite Artin-Hasse tail has a single term. -/
@[simp]
theorem artinHasseTailFinite_two
    {A : Type*} [Field A] (varpi : A) :
    artinHasseTailFinite p 2 varpi =
      varpi ^ (p ^ 2 - 1) / (p : A) ^ 2 := by
  simp [artinHasseTailFinite]

/-- If the false exact normalization `varpi^(p-1) = -p` holds in
characteristic not dividing `p`, then the finite Artin-Hasse tail already has
a nonzero `n = 2` term. -/
theorem artinHasseTailFinite_two_ne_zero_of_pow_eq_neg
    {A : Type*} [Field A] {varpi : A}
    (hpA : (p : A) ≠ 0) (hpow : varpi ^ (p - 1) = -(p : A)) :
    artinHasseTailFinite p 2 varpi ≠ 0 := by
  have hp_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hp_pred_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp_one
  have hvarpi : varpi ≠ 0 := by
    intro hzero
    have hneg : -(p : A) = 0 := by
      simpa [hzero, Nat.ne_of_gt hp_pred_pos] using hpow
    exact hpA (neg_eq_zero.mp hneg)
  rw [artinHasseTailFinite_two]
  exact div_ne_zero (pow_ne_zero _ hvarpi) (pow_ne_zero _ hpA)

/-- Finite-precision obstruction to the false exact normalization.  At
precision two, the logarithmic equation plus `varpi^(p-1) = -p` would force the
finite Artin-Hasse tail to vanish, but its only term is nonzero. -/
theorem not_logTailFinite_two_eq_zero_of_pow_eq_neg
    {A : Type*} [Field A] {varpi : A}
    (hpA : (p : A) ≠ 0) (hvarpi : varpi ≠ 0)
    (hlog :
      varpi + varpi ^ p / (p : A) +
          varpi * artinHasseTailFinite p 2 varpi = 0)
    (hpow : varpi ^ (p - 1) = -(p : A)) :
    False := by
  have htail_zero :=
    artinHasseTailFinite_eq_zero_of_logTailFinite_eq_zero_of_pow_eq_neg
      (p := p) hpA hvarpi hlog hpow
  exact (artinHasseTailFinite_two_ne_zero_of_pow_eq_neg
    (p := p) hpA hpow) htail_zero

omit [Fact p.Prime] in
/-- The lambda-valuation exponent predicted for the `n`th tail summand,
assuming `v(varpi)=1` and `v(p)=p-1`. -/
def artinHasseTailValuationIndex (n : ℕ) : ℤ :=
  (p : ℤ) ^ n - 1 - (n : ℤ) * ((p : ℤ) - 1)

omit [Fact p.Prime] in
/-- The predicted valuation of the second tail term is `(p - 1)^2`. -/
theorem artinHasseTailValuationIndex_two :
    artinHasseTailValuationIndex p 2 = ((p : ℤ) - 1) ^ 2 := by
  unfold artinHasseTailValuationIndex
  ring

omit [Fact p.Prime] in
/-- Successive predicted tail valuations differ by `(p - 1)(p^n - 1)`. -/
theorem artinHasseTailValuationIndex_succ_sub (n : ℕ) :
    artinHasseTailValuationIndex p (n + 1) -
        artinHasseTailValuationIndex p n =
      ((p : ℤ) - 1) * ((p : ℤ) ^ n - 1) := by
  unfold artinHasseTailValuationIndex
  push_cast
  ring

/-- The predicted tail valuations strictly increase after the first term. -/
theorem artinHasseTailValuationIndex_lt_succ {n : ℕ} (hn : 1 ≤ n) :
    artinHasseTailValuationIndex p n <
      artinHasseTailValuationIndex p (n + 1) := by
  have hdiff := artinHasseTailValuationIndex_succ_sub (p := p) n
  have hp_one : 1 < (p : ℤ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_sub_pos : 0 < (p : ℤ) - 1 := by omega
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hpow_gt : 1 < (p : ℤ) ^ n := one_lt_pow₀ hp_one hn_ne
  have hprod_pos : 0 < ((p : ℤ) - 1) * ((p : ℤ) ^ n - 1) := by
    nlinarith
  nlinarith

/-- From the second term on, the predicted tail valuations are at least the second one. -/
theorem artinHasseTailValuationIndex_ge_two {n : ℕ} (hn : 2 ≤ n) :
    artinHasseTailValuationIndex p 2 ≤
      artinHasseTailValuationIndex p n := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
      exact ih.trans
        (le_of_lt (artinHasseTailValuationIndex_lt_succ (p := p) (by omega)))

/-- Every predicted tail valuation is at least the `n = 2` valuation
`(p - 1)^2`. -/
theorem artinHasseTailValuationIndex_ge_sq {n : ℕ} (hn : 2 ≤ n) :
    ((p : ℤ) - 1) ^ 2 ≤ artinHasseTailValuationIndex p n := by
  rw [← artinHasseTailValuationIndex_two (p := p)]
  exact artinHasseTailValuationIndex_ge_two (p := p) hn

end FormalDwork

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The completed local integer ring at `lambda = zeta_p - 1`. -/
abbrev LocalIntegerRing : Type _ :=
  Furtwaengler.KummerArtinHasse.LambdaLocalIntegerRing p K

/-- The corresponding completed local field model. -/
abbrev LocalField : Type _ :=
  Furtwaengler.KummerArtinHasse.LambdaLocalField p K

/-- The completed maximal ideal at `lambda`. -/
abbrev LocalMaximalIdeal : Ideal (LocalIntegerRing p K) :=
  Furtwaengler.KummerArtinHasse.LambdaMaximalIdeal p K

/-- The completed local unit group. -/
abbrev LocalUnitGroup : Type _ :=
  Furtwaengler.KummerArtinHasse.LambdaUnitGroup p K

/-- The completed principal-unit filtration `1 + lambda^n O_F`. -/
abbrev PrincipalUnitSubgroup (n : ℕ) : Subgroup (LocalUnitGroup p K) :=
  Furtwaengler.KummerArtinHasse.LambdaPrincipalUnitSubgroup p K n

/-- The proved cyclotomic local uniformizer `lambda = zeta_p - 1`. -/
def cyclotomicLambda : LocalIntegerRing p K :=
  Furtwaengler.KummerArtinHasse.lambdaPi p K

/-- The distinguished local `p`-th root of unity. -/
def cyclotomicZetaUnit : LocalUnitGroup p K :=
  Furtwaengler.KummerArtinHasse.lambdaZetaUnit p K

/-- The local uniformizer `lambda = zeta_p - 1` is nonzero. -/
@[simp]
theorem cyclotomicLambda_ne_zero :
    cyclotomicLambda p K ≠ 0 :=
  Furtwaengler.KummerArtinHasse.lambdaPi_ne_zero (p := p) (K := K)

/-- The completed maximal ideal is generated by `lambda = zeta_p - 1`. -/
theorem localMaximalIdeal_eq_span_lambda :
    LocalMaximalIdeal p K =
      Ideal.span ({cyclotomicLambda p K} : Set (LocalIntegerRing p K)) :=
  Furtwaengler.KummerArtinHasse.lambdaMaximalIdeal_eq_span_pi (p := p) (K := K)

/-- The completed maximal ideal at `lambda` is principal. -/
theorem localMaximalIdeal_isPrincipal :
    Submodule.IsPrincipal (LocalMaximalIdeal p K) :=
  Furtwaengler.KummerArtinHasse.lambdaMaximalIdeal_isPrincipal (p := p) (K := K)

/-- The distinguished local root of unity is a `p`-th root of unity. -/
theorem cyclotomicZetaUnit_pow_eq_one :
    cyclotomicZetaUnit p K ^ p = 1 :=
  Furtwaengler.KummerArtinHasse.lambdaZetaUnit_pow_eq_one p K

/-- The distinguished local root of unity lies in the first principal-unit subgroup. -/
theorem cyclotomicZetaUnit_mem_principalUnits_one :
    cyclotomicZetaUnit p K ∈ PrincipalUnitSubgroup p K 1 :=
  Furtwaengler.KummerArtinHasse.lambdaZetaUnit_mem_principalUnits_one
    (p := p) (K := K)

/-- The distinguished local root of unity does not lie in the second principal-unit
subgroup. -/
theorem cyclotomicZetaUnit_not_mem_principalUnits_two :
    cyclotomicZetaUnit p K ∉ PrincipalUnitSubgroup p K 2 :=
  Furtwaengler.KummerArtinHasse.lambdaZetaUnit_not_mem_principalUnits_two
    (p := p) (K := K)

/-- The valuation-completion integer ring used for finite trace formulas. -/
abbrev ValuedIntegerRing : Type _ :=
  Furtwaengler.KummerArtinHasse.LambdaValuedIntegerRing p K

/-- The valuation-completion field used for finite trace formulas. -/
abbrev ValuedCompletion : Type _ :=
  Furtwaengler.KummerArtinHasse.LambdaValuedCompletion p K

/-- `lambda = zeta_p - 1` in the valuation-completion integer ring. -/
def valuedCyclotomicLambdaInteger : ValuedIntegerRing p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedPiInteger p K

/-- `lambda = zeta_p - 1` in the valuation-completion field. -/
def valuedCyclotomicLambda : ValuedCompletion p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedPi p K

/-- `zeta_p` in the valuation-completion integer ring. -/
def valuedCyclotomicZetaInteger : ValuedIntegerRing p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedZetaInteger p K

/-- `zeta_p` in the valuation-completion field. -/
def valuedCyclotomicZeta : ValuedCompletion p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedZeta p K

/-- In the valuation completion, `zeta_p = 1 + lambda`. -/
@[simp]
theorem valuedCyclotomicZeta_eq_one_add_lambda :
    valuedCyclotomicZeta p K = 1 + valuedCyclotomicLambda p K := by
  simp [valuedCyclotomicZeta, valuedCyclotomicLambda,
    Furtwaengler.KummerArtinHasse.lambdaValuedZeta,
    Furtwaengler.KummerArtinHasse.lambdaValuedPi,
    Furtwaengler.KummerArtinHasse.lambdaValuedZetaInteger,
    Furtwaengler.KummerArtinHasse.lambdaValuedPiInteger, map_sub]

/-- In the valuation completion, `zeta_p` is a `p`-th root of unity. -/
@[simp]
theorem valuedCyclotomicZeta_pow_eq_one :
    valuedCyclotomicZeta p K ^ p = 1 := by
  change (algebraMap K (ValuedCompletion p K)
      (IsCyclotomicExtension.zeta p ℚ K)) ^ p = 1
  rw [← map_pow, (IsCyclotomicExtension.zeta_spec p ℚ K).pow_eq_one, map_one]

/-- The corrected finite logarithm `log_<=p` used by the existing
Kummer--Artin--Hasse trace API. -/
def valuedLogLeP
    (u : Furtwaengler.KummerArtinHasse.LambdaValuedPrincipalUnitSubgroup p K 1) :
    ValuedCompletion p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedLogLeP p K u

/-- The corrected trace argument `zeta_p * lambda^{-1} log_<=p(u)`. -/
def valuedCorrectedTraceArgument
    (u : Furtwaengler.KummerArtinHasse.LambdaValuedPrincipalUnitSubgroup p K 1) :
    ValuedCompletion p K :=
  Furtwaengler.KummerArtinHasse.lambdaValuedCorrectedATraceArgument p K u

/-- The global integral element `zeta_p - 1`. -/
def globalCyclotomicLambdaInteger : 𝓞 K :=
  Furtwaengler.KummerArtinHasse.lambdaPiIntegral p K

/-- The global integral element `zeta_p - 1` is nonzero. -/
@[simp]
theorem globalCyclotomicLambdaInteger_ne_zero :
    globalCyclotomicLambdaInteger p K ≠ 0 :=
  Furtwaengler.KummerArtinHasse.lambdaPiIntegral_ne_zero (p := p) (K := K)

/-- The global field unit attached to `zeta_p - 1`. -/
def globalCyclotomicLambdaFieldUnit : Kˣ :=
  Furtwaengler.KummerArtinHasse.lambdaPiFieldUnit p K

/-- The global field unit `zeta_p - 1` coerces to its integral representative in `K`. -/
@[simp]
theorem globalCyclotomicLambdaFieldUnit_val :
    (globalCyclotomicLambdaFieldUnit p K : K) =
      algebraMap (𝓞 K) K (globalCyclotomicLambdaInteger p K) :=
  Furtwaengler.KummerArtinHasse.lambdaPiFieldUnit_val (p := p) (K := K)

/-- The global field unit `zeta_p - 1` has `lambda`-valuation `exp (-1)`. -/
theorem globalCyclotomicLambdaFieldUnit_valuation :
    (Furtwaengler.KummerArtinHasse.lambdaHeightOne p K).valuation K
        (globalCyclotomicLambdaFieldUnit p K : K) =
      WithZero.exp (-1 : ℤ) :=
  Furtwaengler.KummerArtinHasse.lambdaPiFieldUnit_valuation (p := p) (K := K)

/-- The lambda valuation of `zeta_p - 1` in the valuation completion. -/
theorem valuedCyclotomicLambda_valuation :
    Valued.v (valuedCyclotomicLambda p K) = WithZero.exp (-1 : ℤ) := by
  change Valued.v
      (algebraMap K (ValuedCompletion p K)
        (globalCyclotomicLambdaFieldUnit p K : K)) =
    WithZero.exp (-1 : ℤ)
  rw [show algebraMap K (ValuedCompletion p K)
      (globalCyclotomicLambdaFieldUnit p K : K) =
        ((globalCyclotomicLambdaFieldUnit p K : K) : ValuedCompletion p K) from rfl]
  rw [Valued.valuedCompletion_apply]
  exact globalCyclotomicLambdaFieldUnit_valuation (p := p) (K := K)

/-- The element `zeta_p - 1` is topologically nilpotent in the valuation
completion. -/
theorem valuedCyclotomicLambda_isTopologicallyNilpotent :
    IsTopologicallyNilpotent (valuedCyclotomicLambda p K) := by
  have hlt : Valued.v (valuedCyclotomicLambda p K) < 1 := by
    rw [valuedCyclotomicLambda_valuation]
    simpa using
      (WithZero.exp_lt_exp (a := (-1 : ℤ)) (b := 0)).mpr (by norm_num)
  exact Valued.tendsto_zero_pow_of_v_lt_one hlt

/-- Power-series convergence predicate for evaluating at `zeta_p - 1` in the
valuation completion. -/
theorem valuedCyclotomicLambda_hasEval :
    PowerSeries.HasEval (valuedCyclotomicLambda p K) :=
  valuedCyclotomicLambda_isTopologicallyNilpotent (p := p) (K := K)

end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
