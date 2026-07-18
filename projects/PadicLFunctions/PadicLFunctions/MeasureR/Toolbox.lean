/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Measure.Toolbox
import PadicLFunctions.MeasureR.Convolution

/-!
# The measure-theoretic toolbox over the integer ring of a field

RJW §3.5 over `R := integerRing K`: multiplication by a continuous function
and by `x` (`∂ = (1+T)d/dT`), evaluation at `x^k`, restriction to clopens,
the `ℤ_p^×`-action `σ_a`, and the operators `φ`, `ψ` with their identities
`ψ∘φ = id`, `φ∘ψ = Res_{pℤ_p}`, `Res_{ℤ_p^×} = 1 − φψ` and Cor 3.32. The
space-side gadgets (`digit`, `shiftDiv`, the clopen sets) are coefficient-free
and reused from the `ℤ_p`-layer `PadicLFunctions/Measure/Toolbox.lean`.
-/

open scoped fwdDiff
open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

section cmul

/-- Multiplication of a measure by a continuous function: `(g·μ)(f) = μ(gf)`
(RJW §3.5.2, TeX 1086–1089). -/
def cmul (g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p] :=
  μ.comp (LinearMap.mulLeft (integerRing K) g)

variable {p K}

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
@[simp]
lemma cmul_apply (g f : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) :
    cmul p K g μ f = μ (g * f) := rfl

variable (p K)

/-- The operator `∂ = (1+T)d/dT` on `R⟦T⟧` (RJW Lem 3.24), over `integerRing K`.
This is the `integerRing K`-specialisation of the generic `PadicLFunctions.del`. -/
def del (F : PowerSeries (integerRing K)) : PowerSeries (integerRing K) :=
  PadicLFunctions.del F

variable {p K}

omit [CompleteSpace K] in
/-- The coefficients of `∂F`: `(∂F)_n = (n+1)F_{n+1} + n·F_n`. -/
private lemma coeff_del (F : PowerSeries (integerRing K)) (n : ℕ) :
    PowerSeries.coeff n (del K F)
      = (n + 1 : integerRing K) * PowerSeries.coeff (n + 1) F
        + (n : integerRing K) * PowerSeries.coeff n F :=
  PadicLFunctions.coeff_del F n

omit [CompleteSpace K] in
/-- Multiplication by `x` corresponds to `∂` on Mahler transforms
(RJW Lem 3.24, TeX 1066–1075): `𝓐_{xμ} = ∂𝓐_μ`, where "multiplication by `x`"
multiplies by the `R`-valued inclusion of the identity. -/
theorem mahlerTransform_cmul_X (μ : MeasureR K ℤ_[p]) :
    mahlerTransform p K (cmul p K (mahlerCM p K 1) μ)
      = del K (mahlerTransform p K μ) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_mahlerTransform]
  have hpt : (mahlerCM p K 1 * mahlerCM p K n : C(ℤ_[p], integerRing K))
      = (n + 1 : integerRing K) • mahlerCM p K (n + 1)
        + (n : integerRing K) • mahlerCM p K n := by
    ext x
    simp only [ContinuousMap.mul_apply, mahlerCM_apply, mahler_apply,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    refine congrArg Subtype.val ?_
    rw [Ring.choose_one_right, ← map_mul, PadicMeasure.mul_choose_eq p x n, map_add,
      map_mul, map_mul]
    push_cast
    ring
  rw [cmul_apply, hpt, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, coeff_del,
    coeff_mahlerTransform, coeff_mahlerTransform]

variable (p K)

/-- The monomial `x ↦ x^k`, valued in `R`. -/
def powCM (k : ℕ) : C(ℤ_[p], integerRing K) :=
  ⟨fun x => algebraMap ℤ_[p] (integerRing K) (x ^ k),
    ((integerRing.isometry_algebraMap p K).continuous).comp (by fun_prop)⟩

variable {p K}

omit [CompleteSpace K] in
@[simp]
lemma powCM_apply (k : ℕ) (x : ℤ_[p]) :
    powCM p K k x = algebraMap ℤ_[p] (integerRing K) (x ^ k) := rfl

omit [CompleteSpace K] in
/-- `∫ x^k dμ = (∂^k 𝓐_μ)(0)` (RJW Cor 3.25, TeX 1079–1082). -/
theorem apply_powCM (μ : MeasureR K ℤ_[p]) (k : ℕ) :
    μ (powCM p K k)
      = PowerSeries.constantCoeff ((del K)^[k] (mahlerTransform p K μ)) := by
  induction k generalizing μ with
  | zero =>
    have h1 : powCM p K 0 = mahlerCM p K 0 := by
      ext x
      simp [mahler_apply]
    rw [Function.iterate_zero_apply, h1, ← coeff_mahlerTransform,
      PowerSeries.coeff_zero_eq_constantCoeff]
  | succ m ih =>
    have h1 : powCM p K (m + 1) = mahlerCM p K 1 * powCM p K m := by
      ext x
      simp only [powCM_apply, ContinuousMap.mul_apply, mahlerCM_apply, mahler_apply]
      refine congrArg Subtype.val ?_
      rw [Ring.choose_one_right, ← map_mul, pow_succ, mul_comm]
    rw [h1, ← cmul_apply, ih (cmul p K (mahlerCM p K 1) μ), mahlerTransform_cmul_X,
      Function.iterate_succ_apply]

end cmul

section res

/-- Restriction of a measure to a clopen subset (RJW §3.5.3, TeX 1100–1103). -/
def res {U : Set ℤ_[p]} (hU : IsClopen U) (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p] :=
  cmul p K (charFnCM K ℤ_[p] hU) μ

/-- A measure is supported on a clopen `U` if `Res_U μ = μ` (TeX 1108). -/
def IsSupportedOn {U : Set ℤ_[p]} (hU : IsClopen U) (μ : MeasureR K ℤ_[p]) : Prop :=
  res p K hU μ = μ

end res

section phipsi

/-- The `ℤ_p^×`-action `σ_a` (RJW §3.5.5, TeX 1135–1136). -/
def sigma (a : ℤ_[p]ˣ) : MeasureR K ℤ_[p] →ₗ[integerRing K] MeasureR K ℤ_[p] :=
  pushforward K ℤ_[p] ℤ_[p] (PadicMeasure.mulCM p (a : ℤ_[p]))

/-- The operator `φ` (RJW §3.5.5, TeX 1141–1142). -/
def phi : MeasureR K ℤ_[p] →ₗ[integerRing K] MeasureR K ℤ_[p] :=
  pushforward K ℤ_[p] ℤ_[p] (PadicMeasure.mulCM p (p : ℤ_[p]))

/-- The operator `ψ` (RJW §3.5.5, TeX 1147–1148), via the coefficient-free
digit shift of the `ℤ_p`-layer. -/
def psi (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p] where
  toFun f :=
    μ (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p) * f.comp (PadicMeasure.shiftDiv p))
  map_add' f g := by
    rw [ContinuousMap.add_comp, mul_add, map_add]
  map_smul' c f := by
    rw [ContinuousMap.smul_comp, mul_smul_comm, map_smul, RingHom.id_apply]

variable {p K}

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- `ψ ∘ φ = id` (RJW TeX 1149–1150). -/
@[simp]
theorem psi_phi (μ : MeasureR K ℤ_[p]) : psi p K (phi p K μ) = μ := by
  refine LinearMap.ext fun f => ?_
  change μ ((_ * f.comp (PadicMeasure.shiftDiv p)).comp
    (PadicMeasure.mulCM p (p : ℤ_[p]))) = μ f
  congr 1
  ext x
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply, PadicMeasure.mulCM,
    ContinuousMap.coe_mk, charFnCM_apply, 
    PadicMeasure.shiftDiv_mul]
  have hmem : ((p : ℤ_[p]) * x) ∈ {y : ℤ_[p] | ‖y‖ < 1} := PadicMeasure.mem_pZp_of_mul p
  rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- `φ ∘ ψ = Res_{pℤ_p}` (RJW TeX 1149–1151). -/
theorem phi_psi (μ : MeasureR K ℤ_[p]) :
    phi p K (psi p K μ) = res p K (PadicMeasure.isClopen_pZp p) μ := by
  refine LinearMap.ext fun f => ?_
  change μ (_ * (f.comp (PadicMeasure.mulCM p (p : ℤ_[p]))).comp (PadicMeasure.shiftDiv p))
    = μ (_ * f)
  congr 1
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, charFnCM_apply,
    PadicMeasure.mulCM,
    ContinuousMap.coe_mk]
  by_cases hx : ‖x‖ < 1
  · rw [PadicMeasure.mul_shiftDiv_of_mem p hx]
  · rw [Set.indicator_of_notMem (by simpa using hx) 1, zero_mul, zero_mul]

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- `Res_{ℤ_p^×} = 1 − φ∘ψ` (RJW Eq 3.10, TeX 1152–1154). -/
theorem res_units_eq (μ : MeasureR K ℤ_[p]) :
    res p K (PadicMeasure.isClopen_units p) μ = μ - phi p K (psi p K μ) := by
  rw [phi_psi]
  refine LinearMap.ext fun f => ?_
  change μ (_ * f) = μ f - μ (_ * f)
  rw [eq_sub_iff_add_eq, ← map_add]
  congr 1
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, 
    charFnCM_apply]
  rw [← add_mul]
  by_cases hx : ‖x‖ < 1
  · have hnu : x ∉ {y : ℤ_[p] | IsUnit y} := fun hu =>
      absurd (PadicInt.isUnit_iff.1 hu) hx.ne
    have hmem : x ∈ {y : ℤ_[p] | ‖y‖ < 1} := hx
    rw [Set.indicator_of_notMem hnu, Set.indicator_of_mem hmem, Pi.one_apply, zero_add,
      one_mul]
  · have hu : x ∈ {y : ℤ_[p] | IsUnit y} :=
      PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one x) (not_lt.1 hx))
    have hnm : x ∉ {y : ℤ_[p] | ‖y‖ < 1} := hx
    rw [Set.indicator_of_mem hu, Set.indicator_of_notMem hnm, Pi.one_apply, add_zero,
      one_mul]

omit [CompleteSpace K] in
/-- The `φ`-scaling of moments: `∫x^k d(φμ) = p^k·∫x^k dμ` (the `R`-widening
of the §4 `phi_apply_powCM`). -/
lemma phi_apply_powCM (μ : MeasureR K ℤ_[p]) (k : ℕ) :
    phi p K μ (powCM p K k)
      = algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ k)
          * μ (powCM p K k) := by
  change μ ((powCM p K k).comp (PadicMeasure.mulCM p (p : ℤ_[p]))) = _
  have hfun : (powCM p K k).comp (PadicMeasure.mulCM p (p : ℤ_[p]))
      = algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ k) • powCM p K k := by
    ext x
    simp [PadicMeasure.mulCM, mul_pow]
  rw [hfun, map_smul, smul_eq_mul]

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
lemma psi_sub (μ ν : MeasureR K ℤ_[p]) :
    psi p K (μ - ν) = psi p K μ - psi p K ν :=
  LinearMap.ext fun _f => LinearMap.sub_apply μ ν _

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
lemma psi_add (μ ν : MeasureR K ℤ_[p]) :
    psi p K (μ + ν) = psi p K μ + psi p K ν :=
  LinearMap.ext fun _f => LinearMap.add_apply μ ν _

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
lemma psi_smul (r : integerRing K) (μ : MeasureR K ℤ_[p]) :
    psi p K (r • μ) = r • psi p K μ :=
  LinearMap.ext fun _f => LinearMap.smul_apply r μ _

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
lemma psi_zero : psi p K (0 : MeasureR K ℤ_[p]) = 0 :=
  LinearMap.ext fun _f => rfl

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
lemma psi_sum {ι : Type*} (s : Finset ι) (μ : ι → MeasureR K ℤ_[p]) :
    psi p K (∑ i ∈ s, μ i) = ∑ i ∈ s, psi p K (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [psi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, psi_add, ih, Finset.sum_insert ha]

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- `ψ(δ_0) = δ_0`. -/
lemma psi_dirac_zero : psi p K (dirac K ℤ_[p] 0) = dirac K ℤ_[p] 0 := by
  refine LinearMap.ext fun f => ?_
  change dirac K ℤ_[p] 0 (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
    * f.comp (PadicMeasure.shiftDiv p)) = dirac K ℤ_[p] 0 f
  rw [dirac_apply, dirac_apply, ContinuousMap.mul_apply, charFnCM_apply,
    ContinuousMap.comp_apply,
    Set.indicator_of_mem (show (0 : ℤ_[p]) ∈ {y : ℤ_[p] | ‖y‖ < 1} from by simp),
    Pi.one_apply, one_mul,
    show PadicMeasure.shiftDiv p (0 : ℤ_[p]) = 0 from by
      simpa using PadicMeasure.shiftDiv_mul p (0 : ℤ_[p])]

/-- **RJW Cor 3.32** over `R`: supported on `ℤ_p^×` iff `ψμ = 0`
(TeX 1161–1167). -/
theorem isSupportedOn_units_iff_psi_eq_zero (μ : MeasureR K ℤ_[p]) :
    IsSupportedOn p K (PadicMeasure.isClopen_units p) μ ↔ psi p K μ = 0 := by
  rw [IsSupportedOn]
  constructor
  · intro h
    have hres := congrArg (psi p K) h
    rw [res_units_eq, psi_sub, psi_phi, sub_self] at hres
    exact hres.symm
  · intro h
    rw [res_units_eq, h, map_zero, sub_zero]

/-- `ψ(δ_u) = 0` for a unit `u`: the Dirac measure at a unit is supported on
`ℤ_p^×` (RJW Cor 3.32 instance). -/
lemma psi_dirac_of_isUnit {u : ℤ_[p]} (hu : IsUnit u) :
    psi p K (dirac K ℤ_[p] u) = 0 := by
  rw [← isSupportedOn_units_iff_psi_eq_zero, IsSupportedOn]
  refine LinearMap.ext fun f => ?_
  change dirac K ℤ_[p] u (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f)
    = dirac K ℤ_[p] u f
  rw [dirac_apply, dirac_apply, ContinuousMap.mul_apply, charFnCM_apply,
    Set.indicator_of_mem (show u ∈ {y : ℤ_[p] | IsUnit y} from hu), Pi.one_apply,
    one_mul]

/-- **The projection formula** `ψ(φ(ν)·μ) = ν·ψ(μ)` (the cleared form of
RJW's trace identity Eq. (3.12); used by §5.2's ξ-free route for
`ψ(μ_η) = η(p)μ_η`, decomposition L5.2.4). Proof on test functions through
the convolution formula: both sides integrate
`y ↦ 1_{pℤ_p}(y)·f(x + y/p)` against `μ` in the inner variable. -/
theorem psi_phi_mul (ν μ : MeasureR K ℤ_[p]) :
    psi p K (phi p K ν * μ) = ν * psi p K μ := by
  refine LinearMap.ext fun f => ?_
  rw [show (psi p K (phi p K ν * μ)) f
      = (phi p K ν * μ) (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
          * f.comp (PadicMeasure.shiftDiv p)) from rfl,
    mul_apply, mul_apply]
  change ν ((convInner p K μ (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
      * f.comp (PadicMeasure.shiftDiv p))).comp (PadicMeasure.mulCM p (p : ℤ_[p])))
    = ν (convInner p K (psi p K μ) f)
  congr 1
  ext x
  rw [ContinuousMap.comp_apply, convInner_apply, convInner_apply]
  rw [show (psi p K μ) (f.comp (⟨fun y => x + y, by fun_prop⟩ : C(ℤ_[p], ℤ_[p])))
      = μ (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
          * (f.comp (⟨fun y => x + y, by fun_prop⟩ : C(ℤ_[p], ℤ_[p]))).comp
              (PadicMeasure.shiftDiv p)) from rfl]
  refine congrArg Subtype.val (congrArg μ (ContinuousMap.ext fun y => ?_))
  simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, charFnCM_apply,
    PadicMeasure.mulCM, ContinuousMap.coe_mk]
  by_cases hy : ‖y‖ < 1
  · have hpx : ((p : ℤ_[p]) * x) ∈ {z : ℤ_[p] | ‖z‖ < 1} :=
      PadicMeasure.mem_pZp_of_mul p
    have hsum : ((p : ℤ_[p]) * x + y) ∈ {z : ℤ_[p] | ‖z‖ < 1} :=
      lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hpx hy)
    rw [Set.indicator_of_mem hsum, Set.indicator_of_mem
        (show y ∈ {z : ℤ_[p] | ‖z‖ < 1} from hy),
      Pi.one_apply, Pi.one_apply, one_mul, one_mul]
    congr 1
    rw [show (p : ℤ_[p]) * x + y = (p : ℤ_[p]) * (x + PadicMeasure.shiftDiv p y)
        from by rw [mul_add, PadicMeasure.mul_shiftDiv_of_mem p hy],
      PadicMeasure.shiftDiv_mul]
  · have hpx : ‖(p : ℤ_[p]) * x‖ < 1 := PadicMeasure.mem_pZp_of_mul p
    have hsum : ((p : ℤ_[p]) * x + y) ∉ {z : ℤ_[p] | ‖z‖ < 1} := by
      rw [Set.mem_setOf_eq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (hpx.trans_le (not_lt.1 hy)).ne, max_lt_iff, not_and]
      exact fun _ => hy
    rw [Set.indicator_of_notMem hsum, Set.indicator_of_notMem
      (show y ∉ {z : ℤ_[p] | ‖z‖ < 1} from hy), zero_mul, zero_mul]

end phipsi

end MeasureR

end

end PadicLFunctions
