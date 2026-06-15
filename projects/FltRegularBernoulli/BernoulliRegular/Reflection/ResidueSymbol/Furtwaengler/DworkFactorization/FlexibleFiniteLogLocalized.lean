module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLogBridge

/-!
# Localized finite-log polynomial evaluator

This file packages the local-denominator evaluator used for homogeneous
pieces of the finite logarithm.  The denominator is a natural number `n`; its
`ell`-power part is cancelled by the forced `Q`-adic order of the numerator,
and its prime-to-`Q` part is inverted in the quotient.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- The image of a natural coefficient has at least the `Q`-adic order forced
by its `ell`-adic factorization. -/
theorem natCast_mem_Q_pow_factorization_mul_pred (c : ℕ) :
    (c : 𝓞 R') ∈ F.Q ^ (c.factorization ℓ * (ℓ - 1)) := by
  by_cases hc : c = 0
  · subst c
    simp
  · have hp : Nat.Prime ℓ := Fact.out
    have hdvd : ℓ ^ c.factorization ℓ ∣ c :=
      (hp.pow_dvd_iff_le_factorization hc).2 le_rfl
    let T := F.toConductorFlexibleTraceFormStickelbergerSetup
    exact T.natCast_mem_Q_pow_mul_pred_of_ell_pow_dvd hdvd

theorem natCast_mul_mem_Q_pow_factorization_mul_pred_add {c e : ℕ} {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ e) :
    (c : 𝓞 R') * z ∈ F.Q ^ (c.factorization ℓ * (ℓ - 1) + e) := by
  have hc := F.natCast_mem_Q_pow_factorization_mul_pred c
  simpa [pow_add] using Ideal.mul_mem_mul hc hz

theorem quotientFractionEvalPrimeCompl_self (N : ℕ) (s : F.Q.primeCompl) :
    F.quotientFractionEvalPrimeCompl N (s : 𝓞 R') s =
      1 := by
  apply
    (F.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [mul_comm (F.quotientFractionEvalPrimeCompl N
      (s : 𝓞 R') s),
    F.quotientFractionEvalPrimeCompl_den_mul]
  simp

theorem quotientFractionEvalPrimeCompl_mul_den_cancel (N : ℕ) (x : 𝓞 R')
    (s t : F.Q.primeCompl) :
    F.quotientFractionEvalPrimeCompl N (x * (t : 𝓞 R'))
        (s * t) =
      F.quotientFractionEvalPrimeCompl N x s := by
  calc
    F.quotientFractionEvalPrimeCompl N (x * (t : 𝓞 R'))
        (s * t)
        = F.quotientFractionEvalPrimeCompl N x s *
            F.quotientFractionEvalPrimeCompl N
              (t : 𝓞 R') t :=
          F.quotientFractionEvalPrimeCompl_mul
            N x (t : 𝓞 R') s t
    _ = F.quotientFractionEvalPrimeCompl N x s := by
          simp [quotientFractionEvalPrimeCompl_self]

/-- Chosen numerator representing `z / ell^v_ell(n)` locally at `Q`, when `z`
has the order needed to cancel that `ell`-power denominator. -/
noncomputable def finiteLogNatDivNumerator (n s : ℕ) (z : 𝓞 R')
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) : 𝓞 R' :=
  Classical.choose
    (F.exists_primeCompl_natCast_ell_pow_denom_of_mem_Q_pow
      (m := n.factorization ℓ) (s := s) (x := z) hz)

/-- Chosen denominator away from `Q` representing `z / ell^v_ell(n)`. -/
noncomputable def finiteLogNatDivDenom (n s : ℕ) (z : 𝓞 R')
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) : F.Q.primeCompl :=
  Classical.choose
    (Classical.choose_spec
      (F.exists_primeCompl_natCast_ell_pow_denom_of_mem_Q_pow
        (m := n.factorization ℓ) (s := s) (x := z) hz))

theorem finiteLogNatDivNumerator_spec {n s : ℕ} {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    ((ℓ : 𝓞 R') ^ n.factorization ℓ) *
        F.finiteLogNatDivNumerator n s z hz =
      (F.finiteLogNatDivDenom n s z hz : 𝓞 R') * z ∧
    F.finiteLogNatDivNumerator n s z hz ∈ F.Q ^ s := by
  unfold finiteLogNatDivNumerator finiteLogNatDivDenom
  exact Classical.choose_spec
    (Classical.choose_spec
      (F.exists_primeCompl_natCast_ell_pow_denom_of_mem_Q_pow
        (m := n.factorization ℓ) (s := s) (x := z) hz))

theorem finiteLogNatDivNumerator_mul_spec {n s : ℕ} {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    ((ℓ : 𝓞 R') ^ n.factorization ℓ) *
        F.finiteLogNatDivNumerator n s z hz =
      (F.finiteLogNatDivDenom n s z hz : 𝓞 R') * z :=
  (F.finiteLogNatDivNumerator_spec hz).1

theorem finiteLogNatDivNumerator_mem_Q_pow {n s : ℕ} {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivNumerator n s z hz ∈ F.Q ^ s :=
  (F.finiteLogNatDivNumerator_spec hz).2

/-- Local quotient value of `z / n`, where the `ell`-part of `n` is cancelled
by the supplied order hypothesis on `z`. -/
noncomputable def finiteLogNatDivEval (N n s : ℕ) (hn : n ≠ 0) (z : 𝓞 R')
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  F.quotientFractionEvalPrimeCompl N
    (F.finiteLogNatDivNumerator n s z hz)
    (F.finiteLogNatDivDenom n s z hz * F.ordComplPrimeCompl hn)

theorem finiteLogNatDivEval_mem_map_Q_pow {N n s : ℕ} (hn : n ≠ 0) {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn z hz ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s) := by
  rw [finiteLogNatDivEval]
  exact F.quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_mem N s
    (F.finiteLogNatDivDenom n s z hz * F.ordComplPrimeCompl hn)
    (F.finiteLogNatDivNumerator_mem_Q_pow hz)

theorem finiteLogNatDivEval_eq_zero_of_succ_le {N n s : ℕ} (hn : n ≠ 0)
    {z : 𝓞 R'} (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hs : N + 1 ≤ s) :
    F.finiteLogNatDivEval N n s hn z hz = 0 :=
  F.eq_zero_of_mem_map_Q_pow_of_succ_le
    (F.finiteLogNatDivEval_mem_map_Q_pow hn hz) hs

/-- Denominator bridge for the localized evaluator: multiplying the quotient
value of `z / n` by `n` recovers `z`. -/
theorem finiteLogNatDivEval_natCast_mul_eq_mk {N n s : ℕ} (hn : n ≠ 0)
    {z : 𝓞 R'} (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((n : ℕ) : 𝓞 R') *
        F.finiteLogNatDivEval N n s hn z hz =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) z := by
  classical
  let m : ℕ := n.factorization ℓ
  let d : F.Q.primeCompl := F.finiteLogNatDivDenom n s z hz
  let c : F.Q.primeCompl := F.ordComplPrimeCompl hn
  let y : 𝓞 R' := F.finiteLogNatDivNumerator n s z hz
  let dc : F.Q.primeCompl := d * c
  have hspec : ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * z := by
    simpa [m, d, y] using F.finiteLogNatDivNumerator_mul_spec hz
  have hn_decomp_nat : ℓ ^ m * ordCompl[ℓ] n = n := by
    simpa [m] using Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hn_cast :
      ((n : ℕ) : 𝓞 R') = ((ℓ : 𝓞 R') ^ m) * (c : 𝓞 R') := by
    rw [← hn_decomp_nat]
    simp [m, c, ordComplPrimeCompl, Nat.cast_mul, Nat.cast_pow]
  rw [finiteLogNatDivEval]
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((n : ℕ) : 𝓞 R') *
        F.quotientFractionEvalPrimeCompl N
          (F.finiteLogNatDivNumerator n s z hz)
          (F.finiteLogNatDivDenom n s z hz * F.ordComplPrimeCompl hn)
        =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
          (Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
            F.quotientFractionEvalPrimeCompl N y dc) := by
        simp [hn_cast, y, dc, d, c, mul_comm, mul_left_comm]
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
          F.quotientFractionEvalPrimeCompl N y dc) := by
        ring
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
        F.quotientFractionEvalPrimeCompl N
          (((ℓ : 𝓞 R') ^ m) * y) dc := by
        rw [F.quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl]
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (c : 𝓞 R') *
        F.quotientFractionEvalPrimeCompl N
          ((d : 𝓞 R') * z) dc := by
        rw [hspec]
    _ =
      F.quotientFractionEvalPrimeCompl N
        ((c : 𝓞 R') * ((d : 𝓞 R') * z)) dc := by
        rw [← F.quotientFractionEvalPrimeCompl_one
          N (c : 𝓞 R')]
        rw [← F.quotientFractionEvalPrimeCompl_mul]
        simp [dc]
    _ =
      F.quotientFractionEvalPrimeCompl N
        ((dc : 𝓞 R') * z) dc := by
        congr 1
        simp [dc, d, c, mul_assoc, mul_comm]
    _ = Ideal.Quotient.mk (F.Q ^ (N + 1)) z :=
        F.quotientFractionEvalPrimeCompl_den_mul_eq_mk N z dc

/-- The localized evaluator is independent of the particular local
representation of the `ell`-power denominator. -/
theorem finiteLogNatDivEval_eq_of_spec {N n s : ℕ} (hn : n ≠ 0)
    {z y : 𝓞 R'} {d : F.Q.primeCompl}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hy : ((ℓ : 𝓞 R') ^ n.factorization ℓ) * y = (d : 𝓞 R') * z) :
    F.finiteLogNatDivEval N n s hn z hz =
      F.quotientFractionEvalPrimeCompl N y
        (d * F.ordComplPrimeCompl hn) := by
  rw [← sub_eq_zero]
  let m : ℕ := n.factorization ℓ
  let c : F.Q.primeCompl := F.ordComplPrimeCompl hn
  let y₀ : 𝓞 R' := F.finiteLogNatDivNumerator n s z hz
  let d₀ : F.Q.primeCompl := F.finiteLogNatDivDenom n s z hz
  let s₀ : F.Q.primeCompl := d₀ * c
  let s₁ : F.Q.primeCompl := d * c
  let num : 𝓞 R' := y₀ * (s₁ : 𝓞 R') - y * (s₀ : 𝓞 R')
  have hspec₀ : ((ℓ : 𝓞 R') ^ m) * y₀ = (d₀ : 𝓞 R') * z := by
    simpa [m, y₀, d₀] using F.finiteLogNatDivNumerator_mul_spec hz
  have hnum_mul : ((ℓ : 𝓞 R') ^ m) * num = 0 := by
    calc
      ((ℓ : 𝓞 R') ^ m) * num
          = (((ℓ : 𝓞 R') ^ m) * y₀) * (s₁ : 𝓞 R') -
              (((ℓ : 𝓞 R') ^ m) * y) * (s₀ : 𝓞 R') := by
                simp [num]
                ring
      _ = ((d₀ : 𝓞 R') * z) * (s₁ : 𝓞 R') -
              ((d : 𝓞 R') * z) * (s₀ : 𝓞 R') := by
                rw [hspec₀, hy]
      _ = 0 := by
                simp [s₀, s₁, c]
                ring
  have hnum : num ∈ F.Q ^ (N + 1) := by
    refine F.mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
      (m := m) (n := N + 1) ?_
    rw [hnum_mul]
    simp
  rw [finiteLogNatDivEval]
  change
    F.quotientFractionEvalPrimeCompl N y₀ s₀ -
        F.quotientFractionEvalPrimeCompl N y s₁ = 0
  have hsub :=
    F.quotientFractionEvalPrimeCompl_sub N y₀ y s₀ s₁
  rw [← hsub]
  exact
    F.quotientFractionEvalPrimeCompl_eq_zero_of_mem
      N (s₀ * s₁) hnum

/-- The localized value of `z / n` is independent of the particular
`Q`-adic order proof used to cancel the `ell`-power denominator. -/
theorem finiteLogNatDivEval_eq_of_mem {N n s t : ℕ} (hn : n ≠ 0)
    {z : 𝓞 R'}
    (hzs : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hzt : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + t)) :
    F.finiteLogNatDivEval N n s hn z hzs =
      F.finiteLogNatDivEval N n t hn z hzt := by
  calc
    F.finiteLogNatDivEval N n s hn z hzs
        =
      F.quotientFractionEvalPrimeCompl N
        (F.finiteLogNatDivNumerator n s z hzs)
        (F.finiteLogNatDivDenom n s z hzs * F.ordComplPrimeCompl hn) := by
        rfl
    _ =
      F.finiteLogNatDivEval N n t hn z hzt :=
        (F.finiteLogNatDivEval_eq_of_spec hn hzt
          (F.finiteLogNatDivNumerator_mul_spec hzs)).symm

theorem finiteLogNatDivEval_eq_of_eq {N n s : ℕ} (hn : n ≠ 0)
    {z w : 𝓞 R'} (hzw : z = w)
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hw : w ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn z hz =
      F.finiteLogNatDivEval N n s hn w hw := by
  subst w
  exact F.finiteLogNatDivEval_eq_of_mem hn hz hw

theorem finiteLogNatDivEval_zero {N n s : ℕ} (hn : n ≠ 0)
    (hzero : (0 : 𝓞 R') ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn 0 hzero = 0 := by
  calc
    F.finiteLogNatDivEval N n s hn 0 hzero
        =
      F.quotientFractionEvalPrimeCompl N 0
        (1 * F.ordComplPrimeCompl hn) :=
        F.finiteLogNatDivEval_eq_of_spec hn hzero (by simp)
    _ = 0 :=
        F.quotientFractionEvalPrimeCompl_eq_zero_of_mem
          N (1 * F.ordComplPrimeCompl hn) (zero_mem _)

/-- The localized evaluator is additive in the numerator, for a fixed natural
denominator and target order. -/
theorem finiteLogNatDivEval_add {N n s : ℕ} (hn : n ≠ 0)
    {z₁ z₂ : 𝓞 R'}
    (hz₁ : z₁ ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hz₂ : z₂ ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hz₁₂ : z₁ + z₂ ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn (z₁ + z₂) hz₁₂ =
      F.finiteLogNatDivEval N n s hn z₁ hz₁ +
        F.finiteLogNatDivEval N n s hn z₂ hz₂ := by
  classical
  let m : ℕ := n.factorization ℓ
  let c : F.Q.primeCompl := F.ordComplPrimeCompl hn
  let y₁ : 𝓞 R' := F.finiteLogNatDivNumerator n s z₁ hz₁
  let y₂ : 𝓞 R' := F.finiteLogNatDivNumerator n s z₂ hz₂
  let d₁ : F.Q.primeCompl := F.finiteLogNatDivDenom n s z₁ hz₁
  let d₂ : F.Q.primeCompl := F.finiteLogNatDivDenom n s z₂ hz₂
  let d₁c : F.Q.primeCompl := d₁ * c
  let d₂c : F.Q.primeCompl := d₂ * c
  let d₁d₂c : F.Q.primeCompl := d₁ * d₂ * c
  let y₁₂ : 𝓞 R' := y₁ * (d₂c : 𝓞 R') + y₂ * (d₁c : 𝓞 R')
  have hspec₁ : ((ℓ : 𝓞 R') ^ m) * y₁ = (d₁ : 𝓞 R') * z₁ := by
    simpa [m, y₁, d₁] using F.finiteLogNatDivNumerator_mul_spec hz₁
  have hspec₂ : ((ℓ : 𝓞 R') ^ m) * y₂ = (d₂ : 𝓞 R') * z₂ := by
    simpa [m, y₂, d₂] using F.finiteLogNatDivNumerator_mul_spec hz₂
  have hrepr :
      ((ℓ : 𝓞 R') ^ n.factorization ℓ) * y₁₂ =
        (d₁d₂c : 𝓞 R') * (z₁ + z₂) := by
    change ((ℓ : 𝓞 R') ^ m) * y₁₂ =
      (d₁d₂c : 𝓞 R') * (z₁ + z₂)
    calc
      ((ℓ : 𝓞 R') ^ m) * y₁₂
          = (((ℓ : 𝓞 R') ^ m) * y₁) * (d₂c : 𝓞 R') +
              (((ℓ : 𝓞 R') ^ m) * y₂) * (d₁c : 𝓞 R') := by
                simp [y₁₂]
                ring
      _ = ((d₁ : 𝓞 R') * z₁) * (d₂c : 𝓞 R') +
              ((d₂ : 𝓞 R') * z₂) * (d₁c : 𝓞 R') := by
                rw [hspec₁, hspec₂]
      _ = (d₁d₂c : 𝓞 R') * (z₁ + z₂) := by
                simp [d₁c, d₂c, d₁d₂c, c]
                ring
  calc
    F.finiteLogNatDivEval N n s hn (z₁ + z₂) hz₁₂
        =
      F.quotientFractionEvalPrimeCompl N y₁₂
        (d₁d₂c * F.ordComplPrimeCompl hn) :=
        F.finiteLogNatDivEval_eq_of_spec hn hz₁₂ hrepr
    _ =
      F.quotientFractionEvalPrimeCompl N y₁₂
        (d₁c * d₂c) :=
        congrArg
          (fun den : F.Q.primeCompl =>
            F.quotientFractionEvalPrimeCompl N y₁₂ den)
          (Subtype.ext (by
            simp [d₁c, d₂c, d₁d₂c, c, mul_assoc, mul_left_comm, mul_comm]))
    _ =
      F.quotientFractionEvalPrimeCompl N y₁ d₁c +
        F.quotientFractionEvalPrimeCompl N y₂ d₂c := by
        rw [← F.quotientFractionEvalPrimeCompl_add]
    _ =
      F.finiteLogNatDivEval N n s hn z₁ hz₁ +
        F.finiteLogNatDivEval N n s hn z₂ hz₂ := by
        simp [finiteLogNatDivEval, y₁, y₂, d₁c, d₂c, d₁, d₂, c]

theorem finiteLogNatDivEval_sum {ι : Type*} {N n s : ℕ}
    (hn : n ≠ 0) (t : Finset ι) (z : ι → 𝓞 R')
    (hz : ∀ i, z i ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hsum : (∑ i ∈ t, z i) ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn (∑ i ∈ t, z i) hsum =
      ∑ i ∈ t, F.finiteLogNatDivEval N n s hn (z i) (hz i) := by
  classical
  revert hsum
  refine Finset.induction_on t ?empty ?insert
  · intro hsum
    simp [F.finiteLogNatDivEval_zero hn]
  · intro a t hat ih hsum
    have htail : (∑ i ∈ t, z i) ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
      refine Ideal.sum_mem _ ?_
      intro i hi
      exact hz i
    have hadd : z a + ∑ i ∈ t, z i ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
      simpa [Finset.sum_insert, hat] using hsum
    calc
      F.finiteLogNatDivEval N n s hn (∑ i ∈ insert a t, z i) hsum
          =
        F.finiteLogNatDivEval N n s hn (z a + ∑ i ∈ t, z i) hadd := by
          congr 1
          simp [Finset.sum_insert, hat]
      _ =
        F.finiteLogNatDivEval N n s hn (z a) (hz a) +
          F.finiteLogNatDivEval N n s hn (∑ i ∈ t, z i) htail := by
          rw [F.finiteLogNatDivEval_add hn (hz a) htail hadd]
      _ =
        F.finiteLogNatDivEval N n s hn (z a) (hz a) +
          ∑ i ∈ t, F.finiteLogNatDivEval N n s hn (z i) (hz i) := by
          rw [ih htail]
      _ =
        ∑ i ∈ insert a t, F.finiteLogNatDivEval N n s hn (z i) (hz i) := by
          simp [Finset.sum_insert, hat]

/-- Moving `z / n` to the common denominator `n*m` does not change its
localized quotient value. -/
theorem finiteLogNatDivEval_mul_denominator_right {N n m s : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hmz : (m : 𝓞 R') * z ∈ F.Q ^ ((n * m).factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N (n * m) s (Nat.mul_ne_zero hn hm) ((m : 𝓞 R') * z) hmz =
      F.finiteLogNatDivEval N n s hn z hz := by
  classical
  let hnm : n * m ≠ 0 := Nat.mul_ne_zero hn hm
  let vn : ℕ := n.factorization ℓ
  let vm : ℕ := m.factorization ℓ
  let y : 𝓞 R' := F.finiteLogNatDivNumerator n s z hz
  let d : F.Q.primeCompl := F.finiteLogNatDivDenom n s z hz
  let cn : F.Q.primeCompl := F.ordComplPrimeCompl hn
  let cm : F.Q.primeCompl := F.ordComplPrimeCompl hm
  let cnm : F.Q.primeCompl := F.ordComplPrimeCompl hnm
  have hfac : (n * m).factorization ℓ = vn + vm := by
    simpa [vn, vm] using
      congrArg (fun f : ℕ →₀ ℕ => f ℓ) (Nat.factorization_mul hn hm)
  have hspec : ((ℓ : 𝓞 R') ^ vn) * y = (d : 𝓞 R') * z := by
    simpa [vn, y, d] using F.finiteLogNatDivNumerator_mul_spec hz
  have hm_decomp_nat : ℓ ^ vm * ordCompl[ℓ] m = m := by
    simpa [vm] using Nat.ordProj_mul_ordCompl_eq_self m ℓ
  have hm_cast : (m : 𝓞 R') = ((ℓ : 𝓞 R') ^ vm) * (cm : 𝓞 R') := by
    rw [← hm_decomp_nat]
    simp [vm, cm, ordComplPrimeCompl, Nat.cast_mul, Nat.cast_pow]
  have hrepr :
      ((ℓ : 𝓞 R') ^ (n * m).factorization ℓ) * (y * (cm : 𝓞 R')) =
        (d : 𝓞 R') * ((m : 𝓞 R') * z) := by
    calc
      ((ℓ : 𝓞 R') ^ (n * m).factorization ℓ) * (y * (cm : 𝓞 R'))
          = (((ℓ : 𝓞 R') ^ vn) * y) *
              (((ℓ : 𝓞 R') ^ vm) * (cm : 𝓞 R')) := by
                rw [hfac, pow_add]
                ring
      _ = ((d : 𝓞 R') * z) * (m : 𝓞 R') := by
                rw [hspec, ← hm_cast]
      _ = (d : 𝓞 R') * ((m : 𝓞 R') * z) := by
                ring
  have hord : cnm = cn * cm := by
    apply Subtype.ext
    simp [cnm, cn, cm, ordComplPrimeCompl, Nat.cast_mul, Nat.ordCompl_mul]
  calc
    F.finiteLogNatDivEval N (n * m) s hnm ((m : 𝓞 R') * z) hmz
        =
      F.quotientFractionEvalPrimeCompl N (y * (cm : 𝓞 R'))
        (d * cnm) :=
        F.finiteLogNatDivEval_eq_of_spec hnm hmz hrepr
    _ =
      F.quotientFractionEvalPrimeCompl N (y * (cm : 𝓞 R'))
        ((d * cn) * cm) :=
        congrArg
          (fun den : F.Q.primeCompl =>
            F.quotientFractionEvalPrimeCompl N
              (y * (cm : 𝓞 R')) den)
          (Subtype.ext (by simp [hord, mul_assoc]))
    _ =
      F.quotientFractionEvalPrimeCompl N y (d * cn) :=
        F.quotientFractionEvalPrimeCompl_mul_den_cancel N y (d * cn) cm
    _ =
      F.finiteLogNatDivEval N n s hn z hz := by
        simp [finiteLogNatDivEval, y, d, cn]

/-- Combine two localized natural-denominator values over the common
denominator `n*m`. -/
theorem finiteLogNatDivEval_add_common_denominator {N n m s : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) {z w : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hw : w ∈ F.Q ^ (m.factorization ℓ * (ℓ - 1) + s))
    (hzw : (m : 𝓞 R') * z + (n : 𝓞 R') * w ∈
      F.Q ^ ((n * m).factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn z hz + F.finiteLogNatDivEval N m s hm w hw =
      F.finiteLogNatDivEval N (n * m) s (Nat.mul_ne_zero hn hm)
        ((m : 𝓞 R') * z + (n : 𝓞 R') * w) hzw := by
  let hnm : n * m ≠ 0 := Nat.mul_ne_zero hn hm
  have hfac : (n * m).factorization ℓ = n.factorization ℓ + m.factorization ℓ := by
    simpa using
      congrArg (fun f : ℕ →₀ ℕ => f ℓ) (Nat.factorization_mul hn hm)
  have hmz : (m : 𝓞 R') * z ∈ F.Q ^ ((n * m).factorization ℓ * (ℓ - 1) + s) := by
    have h := F.natCast_mul_mem_Q_pow_factorization_mul_pred_add (c := m) hz
    simpa [hfac, Nat.add_mul, add_assoc, add_comm, add_left_comm] using h
  have hnw : (n : 𝓞 R') * w ∈ F.Q ^ ((n * m).factorization ℓ * (ℓ - 1) + s) := by
    have h := F.natCast_mul_mem_Q_pow_factorization_mul_pred_add (c := n) hw
    simpa [hfac, Nat.add_mul, add_assoc, add_comm, add_left_comm] using h
  have hchange_z :
      F.finiteLogNatDivEval N (n * m) s hnm ((m : 𝓞 R') * z) hmz =
        F.finiteLogNatDivEval N n s hn z hz :=
    F.finiteLogNatDivEval_mul_denominator_right (N := N) hn hm hz hmz
  have hchange_w :
      F.finiteLogNatDivEval N (n * m) s hnm ((n : 𝓞 R') * w) hnw =
        F.finiteLogNatDivEval N m s hm w hw := by
    have hnw_mn :
        (n : 𝓞 R') * w ∈ F.Q ^ ((m * n).factorization ℓ * (ℓ - 1) + s) := by
      simpa [Nat.mul_comm] using hnw
    have h := F.finiteLogNatDivEval_mul_denominator_right (N := N) hm hn hw hnw_mn
    simpa [Nat.mul_comm] using h
  calc
    F.finiteLogNatDivEval N n s hn z hz + F.finiteLogNatDivEval N m s hm w hw
        =
      F.finiteLogNatDivEval N (n * m) s hnm ((m : 𝓞 R') * z) hmz +
        F.finiteLogNatDivEval N (n * m) s hnm ((n : 𝓞 R') * w) hnw := by
        rw [← hchange_z, ← hchange_w]
    _ =
      F.finiteLogNatDivEval N (n * m) s hnm
        ((m : 𝓞 R') * z + (n : 𝓞 R') * w) hzw := by
        rw [← F.finiteLogNatDivEval_add hnm hmz hnw hzw]

theorem finiteLogNatDivEval_factorial_weighted_mem {d n s : ℕ} (hn : n ≠ 0)
    (hnd : n ≤ d) {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    (((d.factorial / n : ℕ) : 𝓞 R') * z) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + s) := by
  have hdiv : n ∣ d.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hn) hnd
  have hmul_div : d.factorial / n * n = d.factorial := Nat.div_mul_cancel hdiv
  have hm : d.factorial / n ≠ 0 := by
    intro hm0
    have hfac0 : d.factorial = 0 := by
      simpa [hm0] using hmul_div.symm
    exact Nat.factorial_ne_zero d hfac0
  have hfac :
      d.factorial.factorization ℓ =
        (d.factorial / n).factorization ℓ + n.factorization ℓ := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f ℓ) (Nat.factorization_mul hm hn)
    simpa [hmul_div] using h
  have h := F.natCast_mul_mem_Q_pow_factorization_mul_pred_add
    (c := d.factorial / n) hz
  simpa [hfac, Nat.add_mul, add_assoc, add_comm, add_left_comm] using h

theorem finiteLogNatDivEval_eq_factorial_denominator {N d n s : ℕ} (hn : n ≠ 0)
    (hnd : n ≤ d) {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hDz : (((d.factorial / n : ℕ) : 𝓞 R') * z) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn z hz =
      F.finiteLogNatDivEval N d.factorial s (Nat.factorial_ne_zero d)
        (((d.factorial / n : ℕ) : 𝓞 R') * z) hDz := by
  have hdiv : n ∣ d.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hn) hnd
  have hmul_div : d.factorial / n * n = d.factorial := Nat.div_mul_cancel hdiv
  have hm : d.factorial / n ≠ 0 := by
    intro hm0
    have hfac0 : d.factorial = 0 := by
      simpa [hm0] using hmul_div.symm
    exact Nat.factorial_ne_zero d hfac0
  have hmul : n * (d.factorial / n) = d.factorial := by
    simpa [Nat.mul_comm] using hmul_div
  have hmz_nm :
      (((d.factorial / n : ℕ) : 𝓞 R') * z) ∈
        F.Q ^ ((n * (d.factorial / n)).factorization ℓ * (ℓ - 1) + s) := by
    simpa [hmul] using hDz
  have h := F.finiteLogNatDivEval_mul_denominator_right (N := N) hn hm hz hmz_nm
  simpa [hmul] using h.symm

/-- Fixed-degree transport for a denominator-cleared rational coefficient
identity.  If the factorial-cleared numerator of `∑ z_n / n` vanishes for
`1 ≤ n ≤ d`, then the corresponding localized quotient sum is zero. -/
theorem finiteLogNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_eq_zero
    {N d s : ℕ} (z : ℕ → 𝓞 R')
    (hz : ∀ n ∈ Finset.Icc 1 d, z n ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hclear : (∑ n ∈ Finset.Icc 1 d, ((d.factorial / n : ℕ) : 𝓞 R') * z n) = 0) :
    (∑ a ∈ (Finset.Icc 1 d).attach,
      F.finiteLogNatDivEval N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2)) = 0 := by
  classical
  let t : Finset {n // n ∈ Finset.Icc 1 d} := (Finset.Icc 1 d).attach
  let w : {n // n ∈ Finset.Icc 1 d} → 𝓞 R' :=
    fun a => ((d.factorial / a.1 : ℕ) : 𝓞 R') * z a.1
  have hw : ∀ a, w a ∈ F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + s) := by
    intro a
    have ha := Finset.mem_Icc.mp a.2
    exact F.finiteLogNatDivEval_factorial_weighted_mem
      (Nat.ne_zero_of_lt ha.1) ha.2 (hz a.1 a.2)
  have hsum_zero : (∑ a ∈ t, w a) = 0 := by
    rw [show (∑ a ∈ t, w a) =
        ∑ n ∈ Finset.Icc 1 d, ((d.factorial / n : ℕ) : 𝓞 R') * z n by
      simpa [t, w] using
        (Finset.sum_attach (Finset.Icc 1 d)
          (fun n => ((d.factorial / n : ℕ) : 𝓞 R') * z n))]
    exact hclear
  have hsum_mem : (∑ a ∈ t, w a) ∈ F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + s) := by
    rw [hsum_zero]
    exact zero_mem _
  calc
    (∑ a ∈ (Finset.Icc 1 d).attach,
      F.finiteLogNatDivEval N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2))
        =
      ∑ a ∈ t, F.finiteLogNatDivEval N d.factorial s (Nat.factorial_ne_zero d)
        (w a) (hw a) := by
        refine Finset.sum_congr ?_ ?_
        · simp [t]
        · intro a ha
          dsimp [w]
          have haI : a.1 ∈ Finset.Icc 1 d := a.2
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp haI).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp haI).2
          exact F.finiteLogNatDivEval_eq_factorial_denominator (N := N)
            (Nat.ne_zero_of_lt ha1) had (hz a.1 a.2) (hw a)
    _ =
      F.finiteLogNatDivEval N d.factorial s (Nat.factorial_ne_zero d)
        (∑ a ∈ t, w a) hsum_mem := by
        rw [← F.finiteLogNatDivEval_sum (N := N) (n := d.factorial) (s := s)
          (Nat.factorial_ne_zero d) t w hw hsum_mem]
    _ =
      F.finiteLogNatDivEval N d.factorial s (Nat.factorial_ne_zero d) 0
        (zero_mem _) := by
        congr 1
    _ = 0 :=
        F.finiteLogNatDivEval_zero (N := N) (n := d.factorial) (s := s)
          (Nat.factorial_ne_zero d) (zero_mem _)

/-- Fixed-degree transport for a denominator-cleared coefficient error.
If the factorial-cleared numerator of `∑ z_n / n` has sufficiently high
`Q`-adic order, then the corresponding localized quotient sum is zero. -/
theorem finiteLogNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_Q_pow
    {N d s t : ℕ} (z : ℕ → 𝓞 R')
    (hz : ∀ n ∈ Finset.Icc 1 d, z n ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hclear : (∑ n ∈ Finset.Icc 1 d, ((d.factorial / n : ℕ) : 𝓞 R') * z n) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + t))
    (ht : N + 1 ≤ t) :
    (∑ a ∈ (Finset.Icc 1 d).attach,
      F.finiteLogNatDivEval N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2)) = 0 := by
  classical
  let T : Finset {n // n ∈ Finset.Icc 1 d} := (Finset.Icc 1 d).attach
  let w : {n // n ∈ Finset.Icc 1 d} → 𝓞 R' :=
    fun a => ((d.factorial / a.1 : ℕ) : 𝓞 R') * z a.1
  have hw : ∀ a, w a ∈ F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + s) := by
    intro a
    have ha := Finset.mem_Icc.mp a.2
    exact F.finiteLogNatDivEval_factorial_weighted_mem
      (Nat.ne_zero_of_lt ha.1) ha.2 (hz a.1 a.2)
  have hsum_s : (∑ a ∈ T, w a) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + s) :=
    Ideal.sum_mem _ fun a _ha => hw a
  have hsum_t : (∑ a ∈ T, w a) ∈
      F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + t) := by
    rw [show (∑ a ∈ T, w a) =
        ∑ n ∈ Finset.Icc 1 d, ((d.factorial / n : ℕ) : 𝓞 R') * z n by
      simpa [T, w] using
        (Finset.sum_attach (Finset.Icc 1 d)
          (fun n => ((d.factorial / n : ℕ) : 𝓞 R') * z n))]
    exact hclear
  calc
    (∑ a ∈ (Finset.Icc 1 d).attach,
      F.finiteLogNatDivEval N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2))
        =
      ∑ a ∈ T, F.finiteLogNatDivEval N d.factorial s (Nat.factorial_ne_zero d)
        (w a) (hw a) := by
        refine Finset.sum_congr ?_ ?_
        · simp [T]
        · intro a ha
          dsimp [w]
          have haI : a.1 ∈ Finset.Icc 1 d := a.2
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp haI).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp haI).2
          exact F.finiteLogNatDivEval_eq_factorial_denominator (N := N)
            (Nat.ne_zero_of_lt ha1) had (hz a.1 a.2) (hw a)
    _ =
      F.finiteLogNatDivEval N d.factorial s (Nat.factorial_ne_zero d)
        (∑ a ∈ T, w a) hsum_s := by
        rw [← F.finiteLogNatDivEval_sum (N := N) (n := d.factorial) (s := s)
          (Nat.factorial_ne_zero d) T w hw hsum_s]
    _ =
      F.finiteLogNatDivEval N d.factorial t (Nat.factorial_ne_zero d)
        (∑ a ∈ T, w a) hsum_t :=
        F.finiteLogNatDivEval_eq_of_mem (N := N) (n := d.factorial)
          (s := s) (t := t) (Nat.factorial_ne_zero d) hsum_s hsum_t
    _ = 0 :=
        F.finiteLogNatDivEval_eq_zero_of_succ_le
          (N := N) (n := d.factorial) (s := t)
          (Nat.factorial_ne_zero d) hsum_t ht

/-- The localized evaluator commutes with negating the numerator. -/
theorem finiteLogNatDivEval_neg {N n s : ℕ} (hn : n ≠ 0) {z : 𝓞 R'}
    (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hneg : -z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn (-z) hneg =
      -F.finiteLogNatDivEval N n s hn z hz := by
  let y : 𝓞 R' := F.finiteLogNatDivNumerator n s z hz
  let d : F.Q.primeCompl := F.finiteLogNatDivDenom n s z hz
  have hspec : ((ℓ : 𝓞 R') ^ n.factorization ℓ) * (-y) = (d : 𝓞 R') * (-z) := by
    have h := F.finiteLogNatDivNumerator_mul_spec hz
    rw [mul_neg, mul_neg, h]
  calc
    F.finiteLogNatDivEval N n s hn (-z) hneg
        =
      F.quotientFractionEvalPrimeCompl N (-y)
        (d * F.ordComplPrimeCompl hn) :=
        F.finiteLogNatDivEval_eq_of_spec hn hneg hspec
    _ = -F.quotientFractionEvalPrimeCompl N y
        (d * F.ordComplPrimeCompl hn) := by
        rw [F.quotientFractionEvalPrimeCompl_neg]
    _ = -F.finiteLogNatDivEval N n s hn z hz := by
        simp [finiteLogNatDivEval, y, d]

/-- Multiplying the numerator by an integral scalar multiplies the localized
value by the scalar's quotient class. -/
theorem finiteLogNatDivEval_mul_left {N n s : ℕ} (hn : n ≠ 0) (r : 𝓞 R')
    {z : 𝓞 R'} (hz : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s))
    (hrz : r * z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEval N n s hn (r * z) hrz =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) r *
        F.finiteLogNatDivEval N n s hn z hz := by
  let y : 𝓞 R' := F.finiteLogNatDivNumerator n s z hz
  let d : F.Q.primeCompl := F.finiteLogNatDivDenom n s z hz
  have hspec :
      ((ℓ : 𝓞 R') ^ n.factorization ℓ) * (r * y) = (d : 𝓞 R') * (r * z) := by
    have h : ((ℓ : 𝓞 R') ^ n.factorization ℓ) * y = (d : 𝓞 R') * z := by
      simpa [y, d] using F.finiteLogNatDivNumerator_mul_spec hz
    calc
      ((ℓ : 𝓞 R') ^ n.factorization ℓ) * (r * y)
          = r * (((ℓ : 𝓞 R') ^ n.factorization ℓ) * y) := by ring
      _ = r * ((d : 𝓞 R') * z) := by rw [h]
      _ = (d : 𝓞 R') * (r * z) := by ring
  calc
    F.finiteLogNatDivEval N n s hn (r * z) hrz
        =
      F.quotientFractionEvalPrimeCompl N (r * y)
        (d * F.ordComplPrimeCompl hn) :=
        F.finiteLogNatDivEval_eq_of_spec hn hrz hspec
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) r *
        F.quotientFractionEvalPrimeCompl N y
          (d * F.ordComplPrimeCompl hn) := by
        simpa using
          (F.quotientFractionEvalPrimeCompl_mul
            N r y 1 (d * F.ordComplPrimeCompl hn))
    _ =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) r *
        F.finiteLogNatDivEval N n s hn z hz := by
        simp [finiteLogNatDivEval, y, d]

/-- Degree-indexed localized evaluator for a homogeneous numerator of total
degree `d`. -/
noncomputable def finiteLogNatDivEvalAtDegree (N n d : ℕ) (hn : n ≠ 0)
    (z : 𝓞 R') (hz : z ∈ F.Q ^ d)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ d) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  F.finiteLogNatDivEval N n (d - n.factorization ℓ * (ℓ - 1)) hn z (by
    simpa [Nat.add_sub_of_le hden] using hz)

theorem finiteLogNatDivEvalAtDegree_eq_zero_of_cutoff_le {N n d : ℕ}
    (hn : n ≠ 0) (hnd : n ≤ d) (hcut : finiteLogCutoff (ℓ := ℓ) N ≤ d)
    {z : 𝓞 R'} (hz : z ∈ F.Q ^ d)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ d) :
    F.finiteLogNatDivEvalAtDegree N n d hn z hz hden = 0 := by
  rw [finiteLogNatDivEvalAtDegree]
  exact F.finiteLogNatDivEval_eq_zero_of_succ_le hn _
      (Nat.succ_le_sub_factorization_mul_pred_of_mul_succ_le_of_le
        (ell := ℓ) (N := N) (n := n) (d := d)
        (Fact.out : Nat.Prime ℓ) hcut hnd)

/-- Viewing a homogeneous numerator at degree `d` gives the same quotient
value as any other valid order proof for the same local fraction `z / n`. -/
theorem finiteLogNatDivEvalAtDegree_eq_finiteLogNatDivEval {N n d s : ℕ}
    (hn : n ≠ 0) {z : 𝓞 R'} (hz : z ∈ F.Q ^ d)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ d)
    (hzs : z ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s)) :
    F.finiteLogNatDivEvalAtDegree N n d hn z hz hden =
      F.finiteLogNatDivEval N n s hn z hzs := by
  rw [finiteLogNatDivEvalAtDegree]
  exact F.finiteLogNatDivEval_eq_of_mem hn _ hzs

theorem finiteLogNatDivEvalAtDegree_zero {N n d : ℕ} (hn : n ≠ 0)
    (hzero : (0 : 𝓞 R') ∈ F.Q ^ d)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ d) :
    F.finiteLogNatDivEvalAtDegree N n d hn 0 hzero hden = 0 := by
  rw [finiteLogNatDivEvalAtDegree]
  exact F.finiteLogNatDivEval_zero hn _

theorem finiteLogNatDivEvalAtDegree_add {N n d : ℕ} (hn : n ≠ 0)
    {z w : 𝓞 R'} (hz : z ∈ F.Q ^ d) (hw : w ∈ F.Q ^ d)
    (hzw : z + w ∈ F.Q ^ d)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ d) :
    F.finiteLogNatDivEvalAtDegree N n d hn (z + w) hzw hden =
      F.finiteLogNatDivEvalAtDegree N n d hn z hz hden +
        F.finiteLogNatDivEvalAtDegree N n d hn w hw hden := by
  rw [finiteLogNatDivEvalAtDegree, finiteLogNatDivEvalAtDegree,
    finiteLogNatDivEvalAtDegree]
  exact F.finiteLogNatDivEval_add hn _ _ _

theorem finiteLogNatDivEvalAtDegree_neg {N n d : ℕ} (hn : n ≠ 0)
    {z : 𝓞 R'} (hz : z ∈ F.Q ^ d) (hneg : -z ∈ F.Q ^ d)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ d) :
    F.finiteLogNatDivEvalAtDegree N n d hn (-z) hneg hden =
      -F.finiteLogNatDivEvalAtDegree N n d hn z hz hden := by
  rw [finiteLogNatDivEvalAtDegree, finiteLogNatDivEvalAtDegree]
  exact F.finiteLogNatDivEval_neg hn _ _

theorem finiteLogNatDivEvalAtDegree_mul_left {N n d : ℕ} (hn : n ≠ 0)
    (r : 𝓞 R') {z : 𝓞 R'} (hz : z ∈ F.Q ^ d)
    (hrz : r * z ∈ F.Q ^ d)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ d) :
    F.finiteLogNatDivEvalAtDegree N n d hn (r * z) hrz hden =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) r *
        F.finiteLogNatDivEvalAtDegree N n d hn z hz hden := by
  rw [finiteLogNatDivEvalAtDegree, finiteLogNatDivEvalAtDegree]
  exact F.finiteLogNatDivEval_mul_left hn r _ _

theorem finiteLogTermCore_eq_finiteLogNatDivEvalAtDegree {N n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLogTermCore N n x hx =
      F.finiteLogNatDivEvalAtDegree N n n hn (x ^ n) (Ideal.pow_mem_pow hx n)
        (by
          have h := Nat.factorization_mul_pred_le_pred
            (ell := ℓ) (n := n) (Fact.out : Nat.Prime ℓ) hn
          omega) := by
  rw [finiteLogNatDivEvalAtDegree]
  rw [finiteLogTermCore, dif_neg hn]
  symm
  exact F.finiteLogNatDivEval_eq_of_spec hn _
    (F.finiteLogTermNumerator_mul_spec hn hx)

/-- The existing finite-log sum is the localized polynomial evaluator obtained
by applying `finiteLogNatDivEvalAtDegree` to the homogeneous term `x^n`. -/
noncomputable def finiteLogLocalizedPolynomial (N : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
    if hn : n = 0 then 0 else
      ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
        F.finiteLogNatDivEvalAtDegree N n n hn (x ^ n) (Ideal.pow_mem_pow hx n)
          (by
            have h := Nat.factorization_mul_pred_le_pred
              (ell := ℓ) (n := n) (Fact.out : Nat.Prime ℓ) hn
            omega)

theorem finiteLog_eq_finiteLogLocalizedPolynomial (N : ℕ)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLog N x hx = F.finiteLogLocalizedPolynomial N x hx := by
  classical
  unfold finiteLog finiteLogLocalizedPolynomial
  refine Finset.sum_congr rfl ?_
  intro n _hn
  by_cases hn0 : n = 0
  · subst n
    simp
  simp [hn0, finiteLogTerm, F.finiteLogTermCore_eq_finiteLogNatDivEvalAtDegree hn0 hx]

/-- A mixed monomial in two principal-unit coordinates has at least its total
degree of `Q`-adic order. -/
theorem mixedMonomial_mem_Q_pow_totalDegree {x y : 𝓞 R'} (hx : x ∈ F.Q)
    (hy : y ∈ F.Q) (a b c : ℕ) :
    x ^ a * y ^ b * (x * y) ^ c ∈ F.Q ^ (a + b + 2 * c) := by
  have hxpow : x ^ a ∈ F.Q ^ a := Ideal.pow_mem_pow hx a
  have hypow : y ^ b ∈ F.Q ^ b := Ideal.pow_mem_pow hy b
  have hxypow : (x * y) ^ c ∈ F.Q ^ (2 * c) := by
    have hxy : x * y ∈ F.Q ^ 2 := by
      have hmul : x * y ∈ F.Q * F.Q := Ideal.mul_mem_mul hx hy
      simpa [pow_two] using hmul
    simpa [pow_mul] using Ideal.pow_mem_pow hxy c
  have hxyab : x ^ a * y ^ b ∈ F.Q ^ (a + b) := by
    have hmul : x ^ a * y ^ b ∈ F.Q ^ a * F.Q ^ b :=
      Ideal.mul_mem_mul hxpow hypow
    simpa [← pow_add] using hmul
  have hall : (x ^ a * y ^ b) * (x * y) ^ c ∈
      F.Q ^ (a + b) * F.Q ^ (2 * c) :=
    Ideal.mul_mem_mul hxyab hxypow
  simpa [← pow_add, add_assoc] using hall

theorem smul_mixedMonomial_mem_Q_pow_totalDegree {x y : 𝓞 R'} (hx : x ∈ F.Q)
    (hy : y ∈ F.Q) (r : 𝓞 R') (a b c : ℕ) :
    r * (x ^ a * y ^ b * (x * y) ^ c) ∈ F.Q ^ (a + b + 2 * c) :=
  Ideal.mul_mem_left _ r (F.mixedMonomial_mem_Q_pow_totalDegree hx hy a b c)

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
