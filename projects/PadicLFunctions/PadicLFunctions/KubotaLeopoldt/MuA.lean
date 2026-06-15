import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.KubotaLeopoldt.ZetaValues
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The measures `μ_a` (RJW §4.1–§4.2)

For `a` coprime to `p`, the power series
`F_a(T) = 1/T − a/((1+T)^a − 1) ∈ ℤ_p⟦T⟧` (RJW Prop. 4.4, `PropFaT`) is realised here
through its characterising identity `((1+T)^a − 1)·F_a = (Σ_{i<a}(1+T)^i) − a`: the
factor `(1+T)^a − 1 = T·geomSum` with `geomSum = Σ_{i<a}(1+T)^i` a unit (constant
coefficient `a`), so `F_a := ((geomSum − a)/T)·geomSum⁻¹`.

`μ_a` is the measure with Mahler transform `F_a` (RJW Def. 4.5). Its moments are
`∫ x^k dμ_a = (−1)^k (1−a^{k+1}) ζ(−k)` (RJW Prop. 4.6), proved via the substitution
`T = e^t − 1` and the Bernoulli generating function (RJW Lem. 4.2/4.3, realised
algebraically over `ℚ_p⟦t⟧` — see `X_mul_subst_exp_Fa`).

`ψ(μ_a) = μ_a` (RJW Lem. 4.7, `LemmaPsiInvariant`): the source argues through the
roots-of-unity formula for `φ∘ψ`; here we use the equivalent ξ-free route via the
projection formula `ψ(φν·μ) = ν·ψμ` and the finite Dirac-sum identity
`([a]−[0])·μ_a = Σ_{i<a}[i] − a·[0]` (replan recorded in the §4 ticket board).

Restricting to `ℤ_p^×` then removes the Euler factor:
`∫_{ℤ_p^×} x^k dμ_a = (−1)^k (1−p^k)(1−a^{k+1}) ζ(−k)` (RJW Prop. 4.8).
-/

noncomputable section

open PowerSeries

namespace PadicInt

/-- A natural number not divisible by `p` is a unit of `ℤ_p`. -/
lemma isUnit_natCast_of_not_dvd {p : ℕ} [hp : Fact p.Prime] {a : ℕ} (hpa : ¬ p ∣ a) :
    IsUnit (a : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hpa ?_)
  exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (a : ℤ)).1 (by simpa using h)

end PadicInt

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The power series `F_a` and the measure `μ_a` (RJW §4.1) -/

/-- The geometric sum `Σ_{i<a} (1+T)^i ∈ ℤ_p⟦T⟧`, the cofactor in
`(1+T)^a − 1 = T · geomSum a`. Source: RJW Prop. 4.4 (TeX lines 1488–1494). -/
def geomSum (a : ℕ) : PowerSeries ℤ_[p] :=
  ∑ i ∈ Finset.range a, (1 + X) ^ i

@[simp]
lemma constantCoeff_geomSum (a : ℕ) : constantCoeff (geomSum p a) = (a : ℤ_[p]) := by
  simp [geomSum]

lemma geomSum_mul_X (a : ℕ) : geomSum p a * X = (1 + X) ^ a - 1 := by
  have h := geom_sum_mul (1 + X : PowerSeries ℤ_[p]) a
  rw [add_sub_cancel_left] at h
  exact h

lemma isUnit_geomSum {a : ℕ} (hpa : ¬ p ∣ a) : IsUnit (geomSum p a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_geomSum]
  exact PadicInt.isUnit_natCast_of_not_dvd hpa

/-- The numerator `(geomSum a − a)/T` of `F_a`. -/
def FaNum (a : ℕ) : PowerSeries ℤ_[p] :=
  PowerSeries.mk fun n => coeff (n + 1) (geomSum p a)

lemma X_mul_FaNum (a : ℕ) :
    X * FaNum p a = geomSum p a - (a : PowerSeries ℤ_[p]) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, map_sub, ← map_natCast (PowerSeries.C (R := ℤ_[p])) a,
      PowerSeries.coeff_C]
    simp [FaNum]

/-- **RJW Prop. 4.4 (`PropFaT`)**: the power series
`F_a = 1/T − a/((1+T)^a−1) ∈ ℤ_p⟦T⟧`, realised as
`((geomSum a − a)/T)·geomSum a⁻¹`.
Junk value (`0` denominator-inverse) when `p ∣ a`. -/
def Fa (a : ℕ) : PowerSeries ℤ_[p] :=
  FaNum p a * Ring.inverse (geomSum p a)

lemma geomSum_mul_Fa {a : ℕ} (hpa : ¬ p ∣ a) :
    geomSum p a * Fa p a = FaNum p a := by
  rw [Fa, ← mul_assoc, mul_comm (geomSum p a) (FaNum p a), mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_geomSum p hpa), mul_one]

/-- The characterising identity `((1+T)^a − 1)·F_a = geomSum a − a`, the formal
content of `F_a = 1/T − a/((1+T)^a−1)`. Source: RJW Lem. 4.3 (TeX line 1475). -/
lemma one_add_X_pow_sub_one_mul_Fa {a : ℕ} (hpa : ¬ p ∣ a) :
    ((1 + X) ^ a - 1) * Fa p a = geomSum p a - (a : PowerSeries ℤ_[p]) := by
  rw [← geomSum_mul_X, mul_comm (geomSum p a) X, mul_assoc, geomSum_mul_Fa p hpa,
    X_mul_FaNum]

/-- **RJW Def. 4.5 (`DefinitionMeasuremua`)**: the measure `μ_a` on `ℤ_p` whose Mahler
transform is `F_a`. -/
def muA (a : ℕ) : PadicMeasure p ℤ_[p] :=
  (mahlerLinearEquiv p).symm (Fa p a)

@[simp]
lemma mahlerTransform_muA (a : ℕ) : mahlerTransform p (muA p a) = Fa p a :=
  (mahlerLinearEquiv p).apply_symm_apply (Fa p a)

@[simp]
lemma mahlerTransform_sub (μ ν : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (μ - ν) = mahlerTransform p μ - mahlerTransform p ν :=
  map_sub (mahlerTransformₗ p) μ ν

@[simp]
lemma mahlerTransform_smul (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (c • μ) = c • mahlerTransform p μ :=
  map_smul (mahlerTransformₗ p) c μ

/-- The convolution form of the characterising identity:
`([a] − [0])·μ_a = Σ_{i<a} [i] − a·[0]` in `Λ(ℤ_p)`. (mathlib's `binomialSeries_nat`
identifies `𝓐(δ_a) = (1+T)^a`.) -/
lemma dirac_natCast_sub_one_mul_muA {a : ℕ} (hpa : ¬ p ∣ a) :
    (dirac p ((a : ℕ) : ℤ_[p]) - 1) * muA p a
      = (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p])) - (a : ℤ_[p]) • 1 := by
  have hsum : mahlerTransform p (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p]))
      = geomSum p a := by
    rw [show mahlerTransform p (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p]))
        = mahlerTransformₗ p (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p])) from rfl,
      map_sum, geomSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show mahlerTransformₗ p (dirac p ((i : ℕ) : ℤ_[p]))
        = mahlerTransform p (dirac p ((i : ℕ) : ℤ_[p])) from rfl,
      mahlerTransform_dirac, binomialSeries_nat]
  apply mahlerTransform_injective p
  rw [mahlerTransform_mul, mahlerTransform_sub, mahlerTransform_one, mahlerTransform_dirac,
    binomialSeries_nat, mahlerTransform_muA, one_add_X_pow_sub_one_mul_Fa p hpa,
    mahlerTransform_sub, mahlerTransform_smul, mahlerTransform_one, hsum,
    PowerSeries.smul_eq_C_mul, mul_one, ← map_natCast (PowerSeries.C (R := ℤ_[p])) a]

/-- `Λ(ℤ_p)` is a domain (transport along `mahlerRingEquiv` from `ℤ_p⟦T⟧`). -/
instance instIsDomain : IsDomain (PadicMeasure p ℤ_[p]) :=
  MulEquiv.isDomain (PowerSeries ℤ_[p]) (mahlerRingEquiv p).toMulEquiv

instance : SMulCommClass ℤ_[p] (PadicMeasure p ℤ_[p]) (PadicMeasure p ℤ_[p]) where
  smul_comm c μ ν := by
    change c • (μ * ν) = μ * (c • ν)
    apply mahlerTransform_injective p
    rw [mahlerTransform_smul, mahlerTransform_mul, mahlerTransform_mul,
      mahlerTransform_smul]
    exact (mul_smul_comm c _ _).symm

lemma dirac_natCast_sub_one_ne_zero {a : ℕ} (ha : a ≠ 0) :
    (dirac p ((a : ℕ) : ℤ_[p]) - 1 : PadicMeasure p ℤ_[p]) ≠ 0 := by
  intro h
  have h2 := congrArg (mahlerTransform p) h
  rw [mahlerTransform_sub, mahlerTransform_one, mahlerTransform_dirac, mahlerTransform_zero,
    binomialSeries_nat, sub_eq_zero] at h2
  have h3 := congrArg (PowerSeries.coeff 1) h2
  rw [show ((1 : PowerSeries ℤ_[p]) + X) ^ a = ((1 + Polynomial.X : Polynomial ℤ_[p]) ^ a :
      Polynomial ℤ_[p]).toPowerSeries by push_cast [Polynomial.coe_one, Polynomial.coe_X]; ring]
    at h3
  rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow] at h3
  simp at h3
  omega

/-! ## Moments of `μ_a`: the Bernoulli computation (RJW Lem. 4.2/4.3, Prop. 4.6)

The substitution `e^t = T+1` turning `∂ = (1+T)d/dT` into `d/dt` (RJW Lem. 4.3) is
realised by `PowerSeries.subst (exp ℚ_p − 1)`; the value `f_a^{(k)}(0)` is then read
off from the Bernoulli generating function `B(t)·(e^t−1) = t` via
`t·f_a(t) = B(t) − B(at)`. -/

/-- `∂ = (1+T) d/dT` over `ℚ_p`. (To be merged with `PadicMeasure.del` when the
latter is generalised to arbitrary commutative rings — cleanup note in tickets.) -/
def delQ (G : PowerSeries ℚ_[p]) : PowerSeries ℚ_[p] :=
  (1 + X) * PowerSeries.derivativeFun G

lemma map_derivativeFun (F : PowerSeries ℤ_[p]) :
    PowerSeries.map PadicInt.Coe.ringHom (PowerSeries.derivativeFun F)
      = PowerSeries.derivativeFun (PowerSeries.map PadicInt.Coe.ringHom F) := by
  ext n
  simp [coeff_derivativeFun]

lemma map_del (F : PowerSeries ℤ_[p]) :
    PowerSeries.map PadicInt.Coe.ringHom (del p F)
      = delQ p (PowerSeries.map PadicInt.Coe.ringHom F) := by
  rw [del, delQ, map_mul, map_add, map_one, PowerSeries.map_X, map_derivativeFun]

lemma hasSubst_exp_sub_one : HasSubst (exp ℚ_[p] - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- Chain rule for the substitution `T = e^t − 1`: `d/dt (F(e^t−1)) = (∂F)(e^t−1)`.
Source: RJW Lem. 4.3 ("the derivative `d/dt` becomes the operator `∂`"). -/
lemma derivativeFun_subst_exp (F : PowerSeries ℚ_[p]) :
    PowerSeries.derivativeFun (F.subst (exp ℚ_[p] - 1))
      = (delQ p F).subst (exp ℚ_[p] - 1) := by
  have hg := hasSubst_exp_sub_one p
  have hone : (1 : PowerSeries ℚ_[p]).subst (exp ℚ_[p] - 1) = 1 := by
    rw [← coe_substAlgHom hg, map_one]
  have hder : d⁄dX ℚ_[p] (exp ℚ_[p] - 1) = exp ℚ_[p] := by
    rw [map_sub, derivative_exp, Derivation.map_one_eq_zero, sub_zero]
  calc PowerSeries.derivativeFun (F.subst (exp ℚ_[p] - 1))
      = d⁄dX ℚ_[p] (F.subst (exp ℚ_[p] - 1)) := rfl
    _ = (d⁄dX ℚ_[p] F).subst (exp ℚ_[p] - 1) * d⁄dX ℚ_[p] (exp ℚ_[p] - 1) :=
        derivative_subst ℚ_[p] hg
    _ = (delQ p F).subst (exp ℚ_[p] - 1) := by
        rw [hder, delQ, subst_mul hg, subst_add hg, subst_X hg, hone]
        ring_nf
        rfl

lemma constantCoeff_subst_exp (F : PowerSeries ℚ_[p]) :
    constantCoeff (F.subst (exp ℚ_[p] - 1)) = constantCoeff F := by
  rw [show (constantCoeff (F.subst (exp ℚ_[p] - 1)) : ℚ_[p])
      = MvPowerSeries.constantCoeff (F.subst (exp ℚ_[p] - 1)) from rfl,
    constantCoeff_subst (hasSubst_exp_sub_one p),
    finsum_eq_single _ 0 fun d hd => by
      have h0 : MvPowerSeries.constantCoeff (exp ℚ_[p] - 1) = (0 : ℚ_[p]) := by
        have h1 : PowerSeries.constantCoeff (exp ℚ_[p] - 1) = (0 : ℚ_[p]) := by simp
        exact h1
      rw [map_pow, h0, zero_pow hd, smul_zero]]
  simp

lemma constantCoeff_iterate_derivativeFun (k : ℕ) (G : PowerSeries ℚ_[p]) :
    constantCoeff (PowerSeries.derivativeFun^[k] G)
      = (k.factorial : ℚ_[p]) * coeff k G := by
  induction k generalizing G with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, coeff_derivativeFun, Nat.factorial_succ]
    push_cast
    ring

/-- `(∂^k F)(0) = k! · [t^k](F(e^t−1))`: evaluating iterated `∂` at `0` extracts
Taylor coefficients after the exponential substitution (RJW eq. between Lem. 4.3
and Prop. 4.6). -/
lemma constantCoeff_iterate_delQ (k : ℕ) (F : PowerSeries ℚ_[p]) :
    constantCoeff ((delQ p)^[k] F)
      = (k.factorial : ℚ_[p]) * coeff k (F.subst (exp ℚ_[p] - 1)) := by
  induction k generalizing F with
  | zero => simp [constantCoeff_subst_exp, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (delQ p F), ← derivativeFun_subst_exp,
      coeff_derivativeFun, Nat.factorial_succ]
    push_cast
    ring

/-- The Bernoulli evaluation `t·f_a(t) = B(t) − B(at)` where `B` is the Bernoulli
generating function and `f_a = F_a(e^t−1)`: the algebraic content of RJW Lem. 4.2
(`f_a^{(k)}(0) = (−1)^k(1−a^{k+1})ζ(−k)`). -/
lemma X_mul_subst_exp_Fa {a : ℕ} (hpa : ¬ p ∣ a) :
    X * (PowerSeries.map PadicInt.Coe.ringHom (Fa p a)).subst (exp ℚ_[p] - 1)
      = bernoulliPowerSeries ℚ_[p] - rescale (a : ℚ_[p]) (bernoulliPowerSeries ℚ_[p]) := by
  have hg := hasSubst_exp_sub_one p
  have haN : a ≠ 0 := fun h => hpa (h ▸ dvd_zero p)
  have ha0 : ((a : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 haN
  -- the cancellation factor e^{at} − 1 ≠ 0
  have hreg : rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1 ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    rw [map_sub, coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one] at h1
    have h2 : ((a : ℕ) : ℚ_[p]) = 0 := by simpa [Nat.factorial] using h1
    exact haN (Nat.cast_eq_zero.mp h2)
  have hX : (substAlgHom hg) (X : PowerSeries ℚ_[p]) = exp ℚ_[p] - 1 := by
    rw [show ⇑(substAlgHom hg) = PowerSeries.subst (exp ℚ_[p] - 1) from coe_substAlgHom hg]
    exact subst_X hg
  -- ℚ_p-side characterising identity (T031 mapped along ℤ_p → ℚ_p)
  have hQ : ((1 + X) ^ a - 1) * PowerSeries.map PadicInt.Coe.ringHom (Fa p a)
      = (∑ i ∈ Finset.range a, (1 + X) ^ i) - (a : PowerSeries ℚ_[p]) := by
    have h0 := congrArg (PowerSeries.map PadicInt.Coe.ringHom)
      (one_add_X_pow_sub_one_mul_Fa p hpa)
    rw [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X, map_sub,
      map_natCast] at h0
    rw [h0]
    congr 1
    simp only [geomSum, map_sum, map_pow, map_add, map_one, PowerSeries.map_X]
  -- substitute T = e^t − 1: (e^{at} − 1) · f̂_a = Σ_{i<a} e^{it} − a
  have hsub := congrArg (substAlgHom hg) hQ
  simp only [map_mul, map_sub, map_pow, map_add, map_one, map_sum, map_natCast, hX,
    show (1 : PowerSeries ℚ_[p]) + (exp ℚ_[p] - 1) = exp ℚ_[p] by ring,
    exp_pow_eq_rescale_exp, coe_substAlgHom hg] at hsub
  -- Bernoulli side: (B − rescale_a B)·(e^{at} − 1) = X·(Σ_{i<a} e^{it} − a)
  have hb1 : bernoulliPowerSeries ℚ_[p] * (exp ℚ_[p] - 1) = X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ_[p]
  have hfac : rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1
      = (exp ℚ_[p] - 1)
        * ∑ i ∈ Finset.range a, rescale ((i : ℕ) : ℚ_[p]) (exp ℚ_[p]) := by
    have h2 := geom_sum_mul (exp ℚ_[p]) a
    simp only [exp_pow_eq_rescale_exp] at h2
    rw [← h2]
    ring
  have hresc : rescale ((a : ℕ) : ℚ_[p]) (bernoulliPowerSeries ℚ_[p])
      * (rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1) = (a : PowerSeries ℚ_[p]) * X := by
    rw [show rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1
        = rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p] - 1) by rw [map_sub, map_one],
      ← map_mul, hb1, rescale_X, map_natCast]
  have hB : (bernoulliPowerSeries ℚ_[p]
        - rescale ((a : ℕ) : ℚ_[p]) (bernoulliPowerSeries ℚ_[p]))
      * (rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1)
      = X * ((∑ i ∈ Finset.range a, rescale ((i : ℕ) : ℚ_[p]) (exp ℚ_[p]))
        - (a : PowerSeries ℚ_[p])) := by
    rw [sub_mul, hresc]
    nth_rewrite 1 [hfac]
    rw [← mul_assoc, hb1]
    ring
  refine mul_right_cancel₀ hreg ?_
  calc X * (PowerSeries.map PadicInt.Coe.ringHom (Fa p a)).subst (exp ℚ_[p] - 1)
      * (rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1)
      = X * ((rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1)
        * (PowerSeries.map PadicInt.Coe.ringHom (Fa p a)).subst (exp ℚ_[p] - 1)) := by
        ring
    _ = X * ((∑ i ∈ Finset.range a, rescale ((i : ℕ) : ℚ_[p]) (exp ℚ_[p]))
        - (a : PowerSeries ℚ_[p])) := by rw [hsub]
    _ = (bernoulliPowerSeries ℚ_[p]
          - rescale ((a : ℕ) : ℚ_[p]) (bernoulliPowerSeries ℚ_[p]))
        * (rescale ((a : ℕ) : ℚ_[p]) (exp ℚ_[p]) - 1) := hB.symm

/-- **RJW Prop. 4.6**: `∫_{ℤ_p} x^k dμ_a = (−1)^k (1 − a^{k+1}) ζ(−k)` in `ℚ_p`. -/
theorem muA_apply_powCM {a : ℕ} (hpa : ¬ p ∣ a) (k : ℕ) :
    ((muA p a (powCM p k) : ℤ_[p]) : ℚ_[p])
      = (-1) ^ k * (1 - (a : ℚ_[p]) ^ (k + 1)) * ((zetaNeg k : ℚ) : ℚ_[p]) := by
  rw [apply_powCM, mahlerTransform_muA,
    show ((PowerSeries.constantCoeff ((del p)^[k] (Fa p a)) : ℤ_[p]) : ℚ_[p])
      = PowerSeries.constantCoeff
        (PowerSeries.map PadicInt.Coe.ringHom ((del p)^[k] (Fa p a))) from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rfl]
  have hiter : PowerSeries.map PadicInt.Coe.ringHom ((del p)^[k] (Fa p a))
      = (delQ p)^[k] (PowerSeries.map PadicInt.Coe.ringHom (Fa p a)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_del, ih]
  rw [hiter, constantCoeff_iterate_delQ]
  -- coefficient extraction from the Bernoulli identity
  have hcoeff : coeff k ((PowerSeries.map PadicInt.Coe.ringHom (Fa p a)).subst (exp ℚ_[p] - 1))
      = (1 - (a : ℚ_[p]) ^ (k + 1))
        * algebraMap ℚ ℚ_[p] (bernoulli (k + 1) / (k + 1).factorial) := by
    have h := congrArg (PowerSeries.coeff (k + 1)) (X_mul_subst_exp_Fa p hpa)
    rw [coeff_succ_X_mul, map_sub, coeff_rescale,
      show coeff (k + 1) (bernoulliPowerSeries ℚ_[p])
        = algebraMap ℚ ℚ_[p] (bernoulli (k + 1) / (k + 1).factorial) from coeff_mk _ _] at h
    rw [h]
    ring
  rw [hcoeff,
    show ((zetaNeg k : ℚ) : ℚ_[p]) = algebraMap ℚ ℚ_[p] (zetaNeg k) from
      (eq_ratCast _ _).symm,
    zetaNeg]
  simp only [map_div₀, map_mul, map_pow, map_neg, map_add, map_one, map_natCast]
  have hfact : (((k + 1).factorial : ℕ) : ℚ_[p])
      = ((k + 1 : ℕ) : ℚ_[p]) * (k.factorial : ℚ_[p]) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hk1 : (((k + 1 : ℕ)) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
  have hkf : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [hfact]
  rcases Nat.even_or_odd k with hk | hk <;> rw [hk.neg_one_pow] <;> field_simp <;>
    push_cast <;> ring

/-! ## `ψ`-invariance of `μ_a` (RJW Lem. 4.7) -/

/-- Projection formula: `ψ(φ(ν)·μ) = ν·ψ(μ)` in `Λ(ℤ_p)`. The ξ-free engine for
RJW Lem. 4.7 (replan note: replaces the source's roots-of-unity partial-fraction
computation, TeX lines 1517–1524). -/
theorem psi_phi_mul (ν μ : PadicMeasure p ℤ_[p]) :
    psi p (phi p ν * μ) = ν * psi p μ := by
  refine LinearMap.ext fun f => ?_
  change (phi p ν * μ) ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
      f.comp (shiftDiv p)) = (ν * psi p μ) f
  rw [mul_apply, mul_apply]
  change ν ((convInner p μ
      ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
      f.comp (shiftDiv p))).comp (mulCM p (p : ℤ_[p]))) = ν (convInner p (psi p μ) f)
  congr 1
  ext x
  change μ (((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
        f.comp (shiftDiv p)).comp ⟨fun y => (p : ℤ_[p]) * x + y, by fun_prop⟩)
      = μ ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
        (f.comp ⟨fun y => x + y, by fun_prop⟩).comp (shiftDiv p))
  congr 1
  ext y
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
    LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
  by_cases hy : ‖y‖ < 1
  · have hmem : (p : ℤ_[p]) * x + y ∈ {z : ℤ_[p] | ‖z‖ < 1} :=
      lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt (mem_pZp_of_mul p) hy)
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (by exact hy)]
    simp only [Pi.one_apply, one_mul]
    rw [show (p : ℤ_[p]) * x + y = (p : ℤ_[p]) * (x + shiftDiv p y) by
        rw [mul_add, mul_shiftDiv_of_mem p hy],
      shiftDiv_mul]
  · have hnmem : (p : ℤ_[p]) * x + y ∉ {z : ℤ_[p] | ‖z‖ < 1} := by
      intro hmem
      apply hy
      calc ‖y‖ = ‖((p : ℤ_[p]) * x + y) + -((p : ℤ_[p]) * x)‖ := by ring_nf
        _ ≤ max ‖(p : ℤ_[p]) * x + y‖ ‖-((p : ℤ_[p]) * x)‖ :=
            PadicInt.nonarchimedean _ _
        _ < 1 := max_lt hmem (by rw [norm_neg]; exact mem_pZp_of_mul p)
    rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem (by exact hy), zero_mul,
      zero_mul]

@[simp]
lemma phi_dirac (x : ℤ_[p]) : phi p (dirac p x) = dirac p ((p : ℤ_[p]) * x) :=
  LinearMap.ext fun _ => rfl

@[simp]
lemma psi_dirac_mul (x : ℤ_[p]) : psi p (dirac p ((p : ℤ_[p]) * x)) = dirac p x := by
  rw [← phi_dirac, psi_phi]

lemma psi_dirac_of_isUnit {x : ℤ_[p]} (hx : IsUnit x) : psi p (dirac p x) = 0 := by
  refine LinearMap.ext fun f => ?_
  change (LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) x
      * (f.comp (shiftDiv p)) x = 0
  have hnmem : x ∉ {z : ℤ_[p] | ‖z‖ < 1} := by
    simp [PadicInt.isUnit_iff.1 hx]
  rw [show ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) x : ℤ_[p])
      = Set.indicator {z : ℤ_[p] | ‖z‖ < 1} 1 x from rfl,
    Set.indicator_of_notMem hnmem, zero_mul]

lemma psi_zero : psi p (0 : PadicMeasure p ℤ_[p]) = 0 :=
  LinearMap.ext fun _ => rfl

lemma psi_add (μ ν : PadicMeasure p ℤ_[p]) : psi p (μ + ν) = psi p μ + psi p ν :=
  LinearMap.ext fun _ => rfl

lemma psi_smul (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) : psi p (c • μ) = c • psi p μ :=
  LinearMap.ext fun _ => rfl

lemma psi_sum {ι : Type*} (s : Finset ι) (f : ι → PadicMeasure p ℤ_[p]) :
    psi p (∑ i ∈ s, f i) = ∑ i ∈ s, psi p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using psi_zero p
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, psi_add, ih]

/-- `δ_0 = 1` in `Λ(ℤ_p)`. -/
lemma dirac_zero_eq_one : dirac p (0 : ℤ_[p]) = 1 := by
  apply mahlerTransform_injective p
  rw [mahlerTransform_dirac, mahlerTransform_one, binomialSeries_zero]

/-- `ψ(δ_n) = δ_{n/p}` if `p ∣ n`, and `0` otherwise (`n : ℕ`). -/
lemma psi_dirac_natCast (n : ℕ) :
    psi p (dirac p ((n : ℕ) : ℤ_[p]))
      = if p ∣ n then dirac p ((n / p : ℕ) : ℤ_[p]) else 0 := by
  by_cases hn : p ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [if_pos ⟨m, rfl⟩,
      show (((p * m : ℕ)) : ℤ_[p]) = (p : ℤ_[p]) * (m : ℤ_[p]) by push_cast; ring,
      psi_dirac_mul, Nat.mul_div_cancel_left m hp.out.pos]
  · rw [if_neg hn]
    exact psi_dirac_of_isUnit p (PadicInt.isUnit_natCast_of_not_dvd hn)

/-- **RJW Lem. 4.7 (`LemmaPsiInvariant`)**: `ψ(μ_a) = μ_a`.

The source's proof runs through the roots-of-unity formula for `φ∘ψ` (TeX
1517–1524); here the same content is the elementary computation
`([a]−1)·ψμ_a = ψ(([ap]−1)·μ_a) = ψ((Σ_{j<p}[aj])·([a]−1)·μ_a) = ([a]−1)·μ_a`,
using the projection formula and the finite Dirac identities. -/
theorem psi_muA {a : ℕ} (hpa : ¬ p ∣ a) : psi p (muA p a) = muA p a := by
  classical
  have haN : a ≠ 0 := fun h => hpa (h ▸ dvd_zero p)
  -- φ([a] − 1) = [ap] − 1
  have hphi_va : phi p (dirac p ((a : ℕ) : ℤ_[p]) - 1)
      = dirac p ((a * p : ℕ) : ℤ_[p]) - 1 := by
    rw [map_sub, phi_dirac, ← dirac_zero_eq_one, phi_dirac, mul_zero]
    congr 2
    push_cast
    ring
  -- telescope: (Σ_{j<p} [aj])·([a] − 1) = [ap] − 1
  have htel : (∑ j ∈ Finset.range p, dirac p ((a * j : ℕ) : ℤ_[p]))
      * (dirac p ((a : ℕ) : ℤ_[p]) - 1)
      = dirac p ((a * p : ℕ) : ℤ_[p]) - 1 := by
    rw [mul_sub, mul_one, Finset.sum_mul,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range p) =>
        show dirac p ((a * j : ℕ) : ℤ_[p]) * dirac p ((a : ℕ) : ℤ_[p])
            = dirac p ((a * (j + 1) : ℕ) : ℤ_[p]) by
          rw [dirac_mul_dirac]; congr 1; push_cast; ring),
      ← Finset.sum_sub_distrib, Finset.sum_range_sub
        (fun j => dirac p ((a * j : ℕ) : ℤ_[p]))]
    simp [dirac_zero_eq_one]
  -- (Σ_{j<p}[aj])·(Σ_{i<a}[i]) = Σ_{n<ap}[n]
  have htr : ∀ b : ℕ,
      mahlerTransform p (∑ i ∈ Finset.range b, dirac p ((i : ℕ) : ℤ_[p]))
      = geomSum p b := fun b => by
    rw [show mahlerTransform p (∑ i ∈ Finset.range b, dirac p ((i : ℕ) : ℤ_[p]))
        = mahlerTransformₗ p (∑ i ∈ Finset.range b, dirac p ((i : ℕ) : ℤ_[p])) from rfl,
      map_sum, geomSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show mahlerTransformₗ p (dirac p ((i : ℕ) : ℤ_[p]))
        = mahlerTransform p (dirac p ((i : ℕ) : ℤ_[p])) from rfl,
      mahlerTransform_dirac, binomialSeries_nat]
  have hgeom : (∑ j ∈ Finset.range p, dirac p ((a * j : ℕ) : ℤ_[p]))
      * (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p]))
      = ∑ n ∈ Finset.range (a * p), dirac p ((n : ℕ) : ℤ_[p]) := by
    have htrj : mahlerTransform p (∑ j ∈ Finset.range p, dirac p ((a * j : ℕ) : ℤ_[p]))
        = ∑ j ∈ Finset.range p, ((1 + X : PowerSeries ℤ_[p]) ^ a) ^ j := by
      rw [show mahlerTransform p (∑ j ∈ Finset.range p, dirac p ((a * j : ℕ) : ℤ_[p]))
          = mahlerTransformₗ p (∑ j ∈ Finset.range p, dirac p ((a * j : ℕ) : ℤ_[p]))
          from rfl, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show mahlerTransformₗ p (dirac p ((a * j : ℕ) : ℤ_[p]))
          = mahlerTransform p (dirac p ((a * j : ℕ) : ℤ_[p])) from rfl,
        mahlerTransform_dirac, binomialSeries_nat, ← pow_mul]
    apply mahlerTransform_injective p
    rw [mahlerTransform_mul, htr, htr, htrj]
    refine mul_right_cancel₀ (X_ne_zero (R := ℤ_[p])) ?_
    rw [mul_assoc, geomSum_mul_X, geom_sum_mul, geomSum_mul_X, ← pow_mul]
  -- ψ(Σ_{n<ap}[n]) = Σ_{m<a}[m]
  have hpsi1 : psi p (∑ n ∈ Finset.range (a * p), dirac p ((n : ℕ) : ℤ_[p]))
      = ∑ m ∈ Finset.range a, dirac p ((m : ℕ) : ℤ_[p]) := by
    rw [psi_sum, Finset.sum_congr rfl fun n _ => psi_dirac_natCast p n,
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
    refine Finset.sum_nbij' (fun n => n / p) (fun m => p * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      exact Finset.mem_range.2 (Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hn.1))
    · intro m hm
      simp only [Finset.mem_range] at hm
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ⟨m, rfl⟩⟩
      rw [mul_comm a p]
      exact mul_lt_mul_of_pos_left hm hp.out.pos
    · intro n hn
      exact Nat.mul_div_cancel' (Finset.mem_filter.1 hn).2
    · intro m _
      exact Nat.mul_div_cancel_left m hp.out.pos
    · intro n _
      rfl
  -- ψ(Σ_{j<p}[aj]) = 1
  have hpsi2 : psi p (∑ j ∈ Finset.range p, dirac p ((a * j : ℕ) : ℤ_[p])) = 1 := by
    rw [psi_sum, Finset.sum_congr rfl fun j _ => psi_dirac_natCast p (a * j),
      Finset.sum_eq_single 0]
    · simp [dirac_zero_eq_one]
    · intro j hj hj0
      rw [if_neg]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp.out).1 hdvd with h | h
      · exact hpa h
      · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) h)
          (not_le.2 (Finset.mem_range.1 hj))
    · intro h
      exact absurd (Finset.mem_range.2 hp.out.pos) h
  -- assemble and cancel [a] − 1
  have key : (dirac p ((a : ℕ) : ℤ_[p]) - 1) * psi p (muA p a)
      = (dirac p ((a : ℕ) : ℤ_[p]) - 1) * muA p a := by
    have h1 : (dirac p ((a : ℕ) : ℤ_[p]) - 1) * psi p (muA p a)
        = psi p ((dirac p ((a * p : ℕ) : ℤ_[p]) - 1) * muA p a) := by
      rw [← hphi_va, psi_phi_mul]
    rw [h1, ← htel, mul_assoc, dirac_natCast_sub_one_mul_muA p hpa, mul_sub,
      hgeom, mul_smul_comm, mul_one, psi_sub, hpsi1, psi_smul, hpsi2]
  exact mul_left_cancel₀ (dirac_natCast_sub_one_ne_zero p haN) key

/-! ## Restriction to `ℤ_p^×` (RJW §4.2) -/

lemma phi_apply_powCM (μ : PadicMeasure p ℤ_[p]) (k : ℕ) :
    phi p μ (powCM p k) = (p : ℤ_[p]) ^ k * μ (powCM p k) := by
  change μ ((powCM p k).comp (mulCM p (p : ℤ_[p]))) = (p : ℤ_[p]) ^ k * μ (powCM p k)
  have hfun : (powCM p k).comp (mulCM p (p : ℤ_[p])) = (p : ℤ_[p]) ^ k • powCM p k := by
    ext x
    simp [powCM, mulCM, mul_pow]
  rw [hfun, map_smul, smul_eq_mul]

/-- **RJW Prop. 4.8 (`PropInterpolation1`)**: restricting to `ℤ_p^×` removes the
Euler factor at `p`:
`∫_{ℤ_p^×} x^k dμ_a = (−1)^k (1−p^k)(1−a^{k+1}) ζ(−k)`. -/
theorem res_units_muA_apply_powCM {a : ℕ} (hpa : ¬ p ∣ a) (k : ℕ) :
    ((res p (isClopen_units p) (muA p a) (powCM p k) : ℤ_[p]) : ℚ_[p])
      = (-1) ^ k * (1 - (p : ℚ_[p]) ^ k) * (1 - (a : ℚ_[p]) ^ (k + 1))
          * ((zetaNeg k : ℚ) : ℚ_[p]) := by
  rw [res_units_eq, psi_muA p hpa, LinearMap.sub_apply, phi_apply_powCM]
  push_cast
  rw [muA_apply_powCM p hpa k]
  ring

end PadicMeasure
