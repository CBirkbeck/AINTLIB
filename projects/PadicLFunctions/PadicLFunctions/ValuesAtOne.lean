/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.ExtLog
import PadicLFunctions.Interpolation.LpFunction
import PadicLFunctions.MeasureR.FormalPsi
import PadicLFunctions.ValuesAtOneComplex

/-!
# The p-adic value L_p(θ,1) (RJW §6.2, Thm 6.1(ii), decomposition P6)

**RJW Theorem 6.1(ii)** (Leopoldt; `s=1 theorem`(ii), TeX 1992–1995):
`L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)`,
for `θ = χη` non-trivial, `η` primitive of tame conductor `D > 1` prime to
`p`, `χ` of conductor `p^n` (the §5.2 standing hypotheses; the pure
`p`-power case `D = 1` is deferred — decomposition R6, replan 4).

Route (distribution-free; recorded replans R6 1–3): the antiderivative
`F̃_θ` is an EXPLICIT power series over `K` (TeX 2076–2080 expansion, with
`extLog`-constant terms); `∂F̃_θ = F_θ` is a formal identity; the Mahler
transform of the genuine measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` equals
`F̃_θ − φψF̃_θ` by matching `∂` and pinning the constant in `ker ψ`; and the
value `(ψF̃_θ)(0)` is computed by the evaluated `Eqphipsi`
(`psiSeries_eval_zero`) with the `μ_p`-collapse
`Σ_ξ log_p(ξw−1) = log_p(w^p−1)` and the `c ↦ pc` bookkeeping
(automorphism for `n = 0`; primitive-character fiber sums for `n ≥ 1`).

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster P6.
-/

open PowerSeries

namespace PadicLFunctions

namespace MeasureR

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- P6-p1: the per-root logarithmic series
`log((1+T)u − 1) = extLog(u−1) + Σ_{n≥1} ((−1)^{n−1}/n)(u/(u−1))ⁿ Tⁿ`
(TeX 2076–2080), as an explicit `K`-coefficient power series. -/
noncomputable def logSeriesAt (u : K) : PowerSeries K :=
  PowerSeries.mk fun n =>
    if n = 0 then extLog p (u - 1)
    else (-1 : K) ^ (n - 1) * ((n : K))⁻¹ * (u / (u - 1)) ^ n

/-- P6-p1 (continued): the explicit antiderivative `F̃_θ` of RJW TeX ~2070
(stated G-cleared, per the §5 clearing conventions — replan R6.5). -/
noncomputable def Ftilde {N : ℕ} [NeZero N] (θ : DirichletCharacter K N)
    {ε : K} (_hε : IsPrimitiveRoot ε N) : PowerSeries K :=
  -∑ c ∈ Finset.range N,
    PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)

variable {p K}

omit [CompleteSpace K] [CharZero K] in
/-- P6-p9: the theorem's arguments are norm-one units: `‖1 − ε_N^c‖ = 1`
for `c ∈ (ℤ/N)ˣ` when the tame part `D > 1` (cyclotomic-product argument
`Π_c (1−ε_D^c) = Φ_D(1)` of norm one; each factor `≤ 1` forces each `= 1`).
Stated for the tame root itself; the mixed-root variants are derived in the
assembly. -/
theorem norm_one_sub_pow_eq_one {D : ℕ} [NeZero D] (_hD1 : 1 < D)
    (hD : ¬ (p : ℕ) ∣ D) {ε : K} (hε : IsPrimitiveRoot ε D) {c : ℕ}
    (hc : ¬ D ∣ c) : ‖1 - ε ^ c‖ = 1 := by
  rw [← norm_neg, neg_sub]
  exact hε.norm_pow_sub_one_eq_one (norm_natCast_eq_one_of_not_dvd hD) hc

omit [CompleteSpace K] [CharZero K] in
/-- P6-p9 helper: from `‖x^m − 1‖ = 1` and `‖x‖ ≤ 1` conclude `‖x − 1‖ = 1`.
The divisibility `x^m − 1 = (∑_{i<m} x^i)·(x − 1)` gives
`‖x^m − 1‖ ≤ ‖x − 1‖` (the geometric factor has norm `≤ 1`), so `‖x − 1‖ ≥ 1`;
the ultrametric bound `‖x − 1‖ ≤ max ‖x‖ 1 = 1` closes it. Used to lift the
tame norm-one fact to the mixed root `ε^c` (`N = D·p^n`). -/
theorem norm_sub_one_eq_one_of_pow {x : K} {m : ℕ} (hpow : ‖x ^ m - 1‖ = 1)
    (hx : ‖x‖ ≤ 1) : ‖x - 1‖ = 1 := by
  -- `‖x − 1‖ ≤ 1`
  have hle : ‖x - 1‖ ≤ 1 := by
    calc ‖x - 1‖ = ‖x + (-1)‖ := by rw [sub_eq_add_neg]
      _ ≤ max ‖x‖ ‖(-1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [norm_neg, norm_one]; exact max_le hx le_rfl
  -- `‖x − 1‖ ≥ ‖x^m − 1‖ = 1` via `x^m − 1 = (∑_{i<m} x^i)·(x − 1)`
  have hge : (1 : ℝ) ≤ ‖x - 1‖ := by
    have hgeom : ‖∑ i ∈ Finset.range m, x ^ i‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hsplit : ‖x ^ m - 1‖ ≤ ‖x - 1‖ := by
      rw [← geom_sum_mul x m, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hgeom
    rwa [hpow] at hsplit
  exact le_antisymm hle hge

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- P6-p9 (the discharge for `LpFunction_one`): for `N = D·p^n` with `D > 1`
prime to `p`, `ε` a primitive `N`-th root and `c` coprime to `N`,
`‖ε^c − 1‖ = 1`. The `p^n`-power `ε^{p^n}` is a primitive `D`-th root, `D ∤ c`
(coprimality), so `‖(ε^c)^{p^n} − 1‖ = ‖(ε^{p^n})^c − 1‖ = 1`
(`norm_one_sub_pow_eq_one`); lifting along `norm_sub_one_eq_one_of_pow` gives
`‖ε^c − 1‖ = 1`. -/
theorem norm_pow_sub_one_eq_one_of_unit {D : ℕ} [NeZero D] (hD1 : 1 < D)
    (hD : ¬ (p : ℕ) ∣ D) {n : ℕ} {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n))
    {c : ℕ} (hcu : IsUnit ((c : ZMod (D * p ^ n)))) : ‖ε ^ c - 1‖ = 1 := by
  haveI : NeZero (D * p ^ n) := ⟨Nat.mul_ne_zero (NeZero.ne D) (pow_ne_zero _ hp.out.ne_zero)⟩
  -- `c` is coprime to `N = D·p^n`, hence coprime to `D`, hence `¬D∣c`
  have hcop : Nat.Coprime c (D * p ^ n) := (ZMod.isUnit_iff_coprime c (D * p ^ n)).1 hcu
  have hcopD : Nat.Coprime c D := hcop.coprime_dvd_right (Dvd.intro _ rfl)
  have hDc : ¬ D ∣ c := fun h => absurd (Nat.eq_one_of_dvd_coprimes hcopD h dvd_rfl) (by omega)
  -- `ε^{p^n}` is a primitive `D`-th root: `(D·p^n)/p^n = D`
  have hεD : IsPrimitiveRoot (ε ^ p ^ n) D := by
    have h := hε.pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) (Dvd.intro_left D rfl)
    rwa [Nat.mul_div_cancel _ (pow_pos hp.out.pos n)] at h
  -- `‖ε^c‖ = 1` and `‖(ε^c)^{p^n} − 1‖ = 1`
  have hεc : ‖ε ^ c‖ = 1 :=
    norm_eq_one_of_pow_eq_one (L := K) (m := D * p ^ n)
      (by rw [← pow_mul, mul_comm, pow_mul, hε.pow_eq_one, one_pow]) (NeZero.ne _)
  have hpow1 : ‖(ε ^ c) ^ p ^ n - 1‖ = 1 := by
    rw [← pow_mul, mul_comm c (p ^ n), pow_mul]
    exact hεD.norm_pow_sub_one_eq_one (norm_natCast_eq_one_of_not_dvd hD) hDc
  exact norm_sub_one_eq_one_of_pow hpow1 hεc.le

/-- A unit's `Ring.inverse` is the unique right inverse. -/
private theorem ring_inverse_eq_of_mul_eq_one {M₀ : Type*} [MonoidWithZero M₀]
    {a b : M₀} (ha : IsUnit a) (h : a * b = 1) : Ring.inverse a = b := by
  calc Ring.inverse a = Ring.inverse a * (a * b) := by rw [h, mul_one]
    _ = Ring.inverse a * a * b := by rw [mul_assoc]
    _ = b := by rw [Ring.inverse_mul_cancel a ha, one_mul]

/-- The geometric-series inverse `(1 + C b·T)⁻¹ = Σ_n (−b)ⁿ Tⁿ` over any
commutative ring (telescoping coefficient identity, decomposition R6 P6-p2). -/
private theorem one_add_C_mul_X_mul_geom {R : Type*} [CommRing R] (b : R) :
    (1 + PowerSeries.C b * PowerSeries.X) * (PowerSeries.mk fun n => (-b) ^ n) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero =>
    rw [PowerSeries.coeff_mk, pow_zero, mul_comm (PowerSeries.C b) PowerSeries.X, mul_assoc,
      PowerSeries.coeff_zero_X_mul, add_zero, PowerSeries.coeff_one, if_pos rfl]
  | succ m =>
    rw [PowerSeries.coeff_mk, mul_comm (PowerSeries.C b) PowerSeries.X, mul_assoc,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m)]
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- P6-p2: the formal logarithmic derivative
`∂(logSeriesAt u) = 1 + ((1+T)·u − 1)⁻¹` for `u − 1` a unit
(TeX 2102–2105). Route (decomposition R6 P6-p2): factor
`(1+T)·u − 1 = C(u−1)·(1 + C(u/(u−1))·T)`, invert the geometric factor, then
match coefficients (`derivativeFun` raises the index and the `(1+T)`-multiply
splits adjacent coefficients). -/
theorem one_add_mul_derivative_logSeriesAt {u : K} (hu : IsUnit (u - 1)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (logSeriesAt p K u)
      = 1 + Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C u - 1) := by
  have hune : (u - 1) ≠ 0 := hu.ne_zero
  set a : K := u / (u - 1) with ha
  have hCmul : PowerSeries.C (u - 1) * PowerSeries.C a = PowerSeries.C u := by
    rw [← map_mul]; congr 1; rw [ha]; field_simp
  have hfactor : (1 + PowerSeries.X) * PowerSeries.C u - 1
      = PowerSeries.C (u - 1) * (1 + PowerSeries.C a * PowerSeries.X) := by
    have hexp : PowerSeries.C (u - 1) * (1 + PowerSeries.C a * PowerSeries.X)
        = PowerSeries.C (u - 1)
          + (PowerSeries.C (u - 1) * PowerSeries.C a) * PowerSeries.X := by ring
    rw [hexp, hCmul, map_sub, map_one]; ring
  have hCunit : IsUnit (PowerSeries.C (u - 1) : PowerSeries K) := by
    simpa [PowerSeries.isUnit_iff_constantCoeff] using hu
  have hgeomunit : IsUnit (1 + PowerSeries.C a * PowerSeries.X : PowerSeries K) := by
    simp [PowerSeries.isUnit_iff_constantCoeff]
  have hinv : Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C u - 1)
      = PowerSeries.C (u - 1)⁻¹ * (PowerSeries.mk fun n => (-a) ^ n) := by
    refine ring_inverse_eq_of_mul_eq_one (hfactor ▸ hCunit.mul hgeomunit) ?_
    rw [hfactor]
    calc PowerSeries.C (u - 1) * (1 + PowerSeries.C a * PowerSeries.X)
          * (PowerSeries.C (u - 1)⁻¹ * (PowerSeries.mk fun n => (-a) ^ n))
        = (PowerSeries.C (u - 1) * PowerSeries.C (u - 1)⁻¹)
          * ((1 + PowerSeries.C a * PowerSeries.X)
            * (PowerSeries.mk fun n => (-a) ^ n)) := by ring
      _ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hune, map_one, one_add_C_mul_X_mul_geom, mul_one]
  rw [hinv]
  ext n
  rw [map_add, PowerSeries.coeff_one]
  have hsplit : ((1 : PowerSeries K) + PowerSeries.X)
        * PowerSeries.derivativeFun (logSeriesAt p K u)
      = PowerSeries.derivativeFun (logSeriesAt p K u)
        + PowerSeries.X * PowerSeries.derivativeFun (logSeriesAt p K u) := by ring
  have h1a : (1 : K) - a = -(u - 1)⁻¹ := by
    rw [ha, eq_neg_iff_add_eq_zero]; field_simp; ring
  cases n with
  | zero =>
    rw [if_pos rfl, hsplit, map_add, PowerSeries.coeff_zero_X_mul, add_zero,
      PowerSeries.coeff_derivativeFun, logSeriesAt, PowerSeries.coeff_mk,
      if_neg (Nat.succ_ne_zero 0), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ha]
    simp only [pow_zero, pow_one, mul_one, Nat.cast_zero, zero_add, Nat.cast_one]
    field_simp
    ring
  | succ m =>
    rw [if_neg (Nat.succ_ne_zero m), zero_add, hsplit, map_add,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun,
      PowerSeries.coeff_derivativeFun, logSeriesAt, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero (m + 1)), if_neg (Nat.succ_ne_zero m),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    simp only [Nat.add_sub_cancel]
    have hm1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hm2 : ((m : K) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
    push_cast
    rw [mul_assoc _ (((m : K) + 1 + 1)⁻¹) (a ^ (m + 1 + 1)),
      mul_comm (((m : K) + 1 + 1)⁻¹) (a ^ (m + 1 + 1)), ← mul_assoc,
      mul_assoc _ (((m : K) + 1 + 1)⁻¹), inv_mul_cancel₀ hm2, mul_one,
      mul_assoc _ (((m : K) + 1)⁻¹) (a ^ (m + 1)),
      mul_comm (((m : K) + 1)⁻¹) (a ^ (m + 1)), ← mul_assoc,
      mul_assoc _ (((m : K) + 1)⁻¹), inv_mul_cancel₀ hm1, mul_one,
      show (-a) ^ (m + 1) = (-1) ^ (m + 1) * a ^ (m + 1) by rw [← neg_one_mul, mul_pow]]
    linear_combination ((-1 : K) ^ m * a ^ (m + 1)) * h1a

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- P6-p3: `∂F̃_θ = F_θ` — the constant terms cancel by
`Σ_c θ⁻¹(c) = 0` for `θ ≠ 1` (TeX 2100–2110, Lem 6.3 first half in the
formal route). -/
theorem one_add_mul_derivative_Ftilde {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} (hθ1 : θ ≠ 1) {ε : K}
    (hε : IsPrimitiveRoot ε N)
    (hunit : ∀ c ∈ Finset.range N, ¬ N ∣ c → IsUnit (ε ^ c - 1)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (Ftilde p K θ hε)
      = -∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C (ε ^ c) - 1) := by
  haveI : Fact (1 < N) := ⟨hN⟩
  -- push `∂` through the negated sum (the `C`-coefficients pull out by linearity)
  have hder : PowerSeries.derivativeFun (Ftilde p K θ hε)
      = -∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          * PowerSeries.derivativeFun (logSeriesAt p K (ε ^ c)) := by
    rw [Ftilde, show PowerSeries.derivativeFun (-∑ c ∈ Finset.range N,
          PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))
        = d⁄dX K (-∑ c ∈ Finset.range N,
          PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)) from rfl,
      map_neg, map_sum, neg_inj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show (d⁄dX K) (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))
        = PowerSeries.derivativeFun (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * logSeriesAt p K (ε ^ c)) from rfl,
      show PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)
        = (θ⁻¹ ((c : ZMod N))) • logSeriesAt p K (ε ^ c) from
      (PowerSeries.smul_eq_C_mul _ _).symm,
      PowerSeries.derivativeFun_smul, PowerSeries.smul_eq_C_mul]
  rw [hder, mul_neg, Finset.mul_sum]
  -- per term: `c = 0` is killed by `θ⁻¹ 0 = 0`; for `c ≠ 0`, apply P6-p2
  rw [show (∑ c ∈ Finset.range N, (1 + PowerSeries.X)
        * (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          * PowerSeries.derivativeFun (logSeriesAt p K (ε ^ c))))
      = ∑ c ∈ Finset.range N, (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
          + PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C (ε ^ c) - 1)) from by
    refine Finset.sum_congr rfl fun c hc => ?_
    by_cases hdvd : N ∣ c
    · have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (Finset.mem_range.mp hc)
      have hθ0 : θ⁻¹ ((c : ZMod N)) = 0 := by
        rw [hc0, Nat.cast_zero]; exact MulChar.map_nonunit _ not_isUnit_zero
      rw [hθ0, map_zero, zero_mul, mul_zero, zero_add, zero_mul]
    · have hu := hunit c hc hdvd
      rw [show (1 + PowerSeries.X) * (PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * PowerSeries.derivativeFun (logSeriesAt p K (ε ^ c)))
          = PowerSeries.C (θ⁻¹ ((c : ZMod N)))
            * ((1 + PowerSeries.X) * PowerSeries.derivativeFun
              (logSeriesAt p K (ε ^ c))) from by ring,
        one_add_mul_derivative_logSeriesAt hu, mul_add, mul_one]]
  -- the constant `1`-terms sum to `C(Σ_c θ⁻¹(c)) = C 0 = 0` (nontrivial character)
  rw [Finset.sum_add_distrib]
  have hsum0 : (∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ ((c : ZMod N))))
      = (0 : PowerSeries K) := by
    rw [← map_sum]
    have hreindex : ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
        = ∑ x : ZMod N, θ⁻¹ x := by
      refine Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod N)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
      · intro c _; exact Finset.mem_univ _
      · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
      · intro c hc; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hc)
      · intro x _; exact ZMod.natCast_zmod_val x
      · intro c _; rfl
    rw [hreindex, MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hθ1), map_zero]
  rw [hsum0, zero_add]

variable (p K)

/-- P6-p4: the genuine measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` on `ℤ_p`
(the §5 `zetaEtaCleared` pattern applied to the `χ`-twisted `μ̃_η`,
pushed forward along the unit inclusion). -/
noncomputable def rhoTheta {D : ℕ} [NeZero D]
    (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    MeasureR K ℤ_[p] :=
  iota p K
    ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)).comp
      ((extendByZero p K).comp
        (LinearMap.mulLeft (integerRing K) (invUnitsCM p K))))

variable {p K}

omit [CharZero K] in
/-- P6-p5: `ρ_θ` is supported on the units, so `ψ(ρ_θ) = 0`. -/
theorem psi_rhoTheta {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0 :=
  -- `ρ_θ` is in the image of `ι`, whose range is `ker ψ` (RJW Rem 3.33)
  (mem_range_iota_iff (rhoTheta p K η hζ hD χ)).mp ⟨_, rfl⟩

/-- `PowerSeries.map` commutes with `derivativeFun` (coefficient-wise: both
raise the index and scale by `n+1`, which the ring hom preserves). -/
private theorem map_derivativeFun {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f (PowerSeries.derivativeFun F)
      = PowerSeries.derivativeFun (PowerSeries.map f F) :=
  PadicLFunctions.map_derivativeFun f F

/-- `PowerSeries.map` commutes with the operator `∂ = (1+T)d/dT`. -/
private theorem map_one_add_mul_derivativeFun {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f ((1 + PowerSeries.X) * PowerSeries.derivativeFun F)
      = (1 + PowerSeries.X) * PowerSeries.derivativeFun (PowerSeries.map f F) :=
  PadicLFunctions.map_del f F

omit [CharZero K] in
/-- P6-p5 (continued): `∂𝓐(ρ_θ) = (1−φψ)F_θ` over `K` — multiplication by
`x` recovers `Res_{ℤ_p^×}(μ_θ)` and `Res = 1 − φ∘ψ`
(Lem 6.3's second half in the formal route; the right-hand side is `p3`'s
explicit series). -/
theorem one_add_mul_derivative_mahlerK_rhoTheta {D : ℕ} [NeZero D]
    (_hD1 : 1 < D) {η : DirichletCharacter (integerRing K) D}
    (_hη : η.IsPrimitive) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hD : ¬ (p : ℕ) ∣ D) {n : ℕ}
    (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = mahlerK p K (res p K (PadicMeasure.isClopen_units p)
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))) := by
  -- the measure-level multiplication-by-`x` identity: `x·ρ_θ = Res_{ℤ_p^×}(μ_θ)`
  -- (the `x⁻¹` in `ρ_θ` cancels against the `x`-monomial on the units)
  have hmeas : cmul p K (mahlerCM p K 1) (rhoTheta p K η hζ hD χ)
      = res p K (PadicMeasure.isClopen_units p)
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)) := by
    refine LinearMap.ext fun f => ?_
    rw [cmul_apply, rhoTheta, iota, pushforward_apply]
    change (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
        (extendByZero p K (invUnitsCM p K
          * ((mahlerCM p K 1 * f).comp (PadicMeasure.unitsValCM p)))) = _
    rw [show invUnitsCM p K * ((mahlerCM p K 1 * f).comp (PadicMeasure.unitsValCM p))
        = f.comp (PadicMeasure.unitsValCM p) from ?_, extendByZero_comp_unitsVal]
    · rfl
    · refine ContinuousMap.ext fun u => ?_
      simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, invUnitsCM_apply,
        mahlerCM_apply, PadicMeasure.unitsValCM, ContinuousMap.coe_mk]
      rw [mahler_apply, Ring.choose_one_right, ← mul_assoc, ← map_mul]
      rw [show PadicMeasure.invCM p u * (u : ℤ_[p]) = 1 from ?_, map_one, one_mul]
      change ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- transport through `mahlerK` via `𝓐_{xμ} = ∂𝓐_μ` and `map`-commutation with `∂`
  rw [← hmeas]
  simp only [mahlerK]
  rw [mahlerTransform_cmul_X,
    show del K (mahlerTransform p K (rhoTheta p K η hζ hD χ))
      = (1 + PowerSeries.X)
        * PowerSeries.derivativeFun (mahlerTransform p K (rhoTheta p K η hζ hD χ)) from rfl,
    map_one_add_mul_derivativeFun]

omit [CompleteSpace K] [CharZero K] in
/-- `anglePowCM p K 0 = 1` (the `0`-th power is the constant `1`): `onePAdicPow
y hy 0 = y^0 = 1`. The `s = 1` specialisation `⟨x⟩^{1−1}` of the `L_p` integrand. -/
private theorem anglePowCM_zero : anglePowCM p K 0 = 1 := by
  ext u
  rw [anglePowCM_apply, ← Nat.cast_zero (R := ℤ_[p]),
    PadicInt.onePAdicPow_natCast, pow_zero, map_one]
  rfl

omit [CharZero K] in
/-- P6-p8 step 1 (the mass identity): the `L_p`-integrand of `ζ_η` at `s = 1`
(where `⟨x⟩^{1−1} = 1`) pairs to the constant coefficient of `𝓐_{ρ_θ}`.
Concretely `(ζ_η-cleared)(χ̃·1) = ρ_θ(x^0) = constantCoeff 𝓐_{ρ_θ}` in
`integerRing K`: unfolding `ρ_θ = ι(twist χ̃ μ̃_η ∘ extendByZero ∘ ·invU)` and
`apply_powCM` at `0`, both reduce to `μ̃_η(χ̃·extendByZero(invU))` (the integrand
identity `extendByZero(invU·(χ̃∘val)) = χ̃·extendByZero(invU)`: at units both are
`χ̃(u)·invU(u)`, at non-units both `0`). -/
private theorem zetaEtaCleared_one_eq_rhoTheta_mass {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {n : ℕ}
    {χ : DirichletCharacter (integerRing K) (p ^ n)} :
    zetaEtaCleared p K η hζ hD
        (χ.toContinuousMapZp.comp (PadicMeasure.unitsValCM p) * anglePowCM p K (1 - 1))
      = PowerSeries.constantCoeff (mahlerTransform p K (rhoTheta p K η hζ hD χ)) := by
  -- the constant coefficient is the mass `ρ_θ(x^0)`
  rw [show PowerSeries.constantCoeff (mahlerTransform p K (rhoTheta p K η hζ hD χ))
        = rhoTheta p K η hζ hD χ (powCM p K 0) from by
      rw [apply_powCM, Function.iterate_zero_apply]]
  -- unfold `ρ_θ(x^0)` through `ι`, the twist composition, and `x^0 = 1`
  rw [rhoTheta, iota, pushforward_apply]
  change zetaEtaCleared p K η hζ hD _
    = twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)
        (extendByZero p K (invUnitsCM p K * ((powCM p K 0).comp (PadicMeasure.unitsValCM p))))
  rw [twist_apply, zetaEtaCleared_apply]
  -- both sides are `μ̃_η` of the same function; reduce to the integrand identity
  congr 1
  ext x
  refine congrArg Subtype.val ?_
  -- `(1 − 1 : ℤ_p) = 0`, so the angle factor is `1`
  rw [show (1 : ℤ_[p]) - 1 = 0 from sub_self 1, anglePowCM_zero]
  by_cases hx : IsUnit x
  · -- at a unit: LHS `extendByZero(invU·(χ̃∘val·1))`, RHS `χ̃·extendByZero(invU·(x^0∘val))`
    rw [ContinuousMap.mul_apply, ← hx.unit_spec, extendByZero_coe_unit, extendByZero_coe_unit]
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply,
      powCM_apply, pow_zero, map_one, mul_one]
    rw [show (PadicMeasure.unitsValCM p) hx.unit = ((hx.unit : ℤ_[p])) from rfl, mul_comm]
  · -- at a non-unit: LHS `0`, RHS `χ̃(x)·0 = 0`
    rw [ContinuousMap.mul_apply,
      show (extendByZero p K (invUnitsCM p K
          * (χ.toContinuousMapZp.comp (PadicMeasure.unitsValCM p) * 1))) x = 0 from dif_neg hx,
      show (extendByZero p K (invUnitsCM p K
          * ((powCM p K 0).comp (PadicMeasure.unitsValCM p)))) x = 0 from dif_neg hx, mul_zero]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- `‖(n : K)⁻¹‖ ≤ n` for `n ≥ 1`: the norm of `(n : K)` is `p^{−v_p(n)}`, whose
inverse is `p^{v_p(n)} = ordProj[p] n ≤ n`. The polynomial-growth bound for the
`1/n`-coefficients of `logSeriesAt` / `F̃`. -/
private theorem norm_natCast_inv_le {n : ℕ} (hn : 1 ≤ n) : ‖((n : K))⁻¹‖ ≤ (n : ℝ) := by
  have hn0 : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnK : ((n : K)) = algebraMap ℚ_[p] K (n : ℚ_[p]) := (map_natCast _ n).symm
  have hnorm : ‖((n : K))⁻¹‖ = ((p ^ padicValNat p n : ℕ) : ℝ) := by
    rw [norm_inv, hnK, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation hn0,
      Padic.valuation_natCast, ← zpow_neg, neg_neg, zpow_natCast]
    push_cast; ring
  rw [hnorm, ← Nat.factorization_def n hp.out]
  exact_mod_cast Nat.ordProj_le p (by omega)

/-! #### The boundary `p`-adic logarithm (T618 / Washington §5.1)

`padicLog`'s `p`-power law `padicLog (z^p) = p·padicLog z` and multiplicativity are
proven in `PadicExp` only INSIDE the exponential ball `‖z−1‖^{p−1} < p⁻¹`. The
arguments `1 − ε_N^c`, `ξ^i − 1` of RJW Thm 6.1(ii) sit on the boundary
`‖·‖^{p−1} = p⁻¹` of that ball. This block extends those facts to the WHOLE open unit
ball `‖z−1‖ < 1` by aligning the convergent `padicLog` series with the formal
`formalLog` and pushing `phiSeries_formalLog : φ formalLog = p·formalLog` through the
`seriesEval` bridge. Decomposition R6.6, ticket T618. -/

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [CharZero K] in
/-- The open unit ball `‖x − 1‖ < 1` is closed under powers, in any ultrametric normed field
(no `p`-adic algebra structure needed). -/
theorem boundary_norm_pow_sub_one_lt_one {x : K} (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ < 1 := by
  induction n with
  | zero => rw [pow_zero, sub_self, norm_zero]; exact one_pos
  | succ k ih =>
    have hbd : ‖x ^ (k + 1) - 1‖ ≤ max ‖x ^ k - 1‖ ‖x - 1‖ := by
      rw [show x ^ (k + 1) - 1 = (x ^ k - 1) * x + (x - 1) from by rw [pow_succ]; ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
      have hx1 : ‖x‖ ≤ 1 := by
        calc ‖x‖ = ‖(x - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ max ‖x - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ 1 := by rw [norm_one]; exact max_le hx.le le_rfl
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hx1
    exact lt_of_le_of_lt hbd (max_lt ih hx)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- T618: the coefficients of `formalLog` are linearly bounded `‖coeff n‖ ≤ n + 1`
(the `1/n`-factor has norm `≤ n`). Drives summability of `seriesEval (formalLog K) z`
for `‖z‖ < 1`. -/
private theorem norm_coeff_formalLog_le (n : ℕ) :
    ‖PowerSeries.coeff n (formalLog K)‖ ≤ (n : ℝ) + 1 := by
  cases n with
  | zero => rw [coeff_zero_formalLog, norm_zero]; positivity
  | succ m =>
    rw [coeff_succ_formalLog, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖((m : K) + 1)⁻¹‖ = ‖(((m + 1 : ℕ) : K))⁻¹‖ := by rw [Nat.cast_succ]
      _ ≤ ((m + 1 : ℕ) : ℝ) := norm_natCast_inv_le (p := p) (K := K) (by omega)
      _ ≤ (↑(m + 1) : ℝ) + 1 := by push_cast; linarith

omit [CharZero K] in
include hp in
/-- T618: `seriesEval (formalLog K) z` converges for `‖z‖ < 1` (linear-growth
coefficients). -/
private theorem summable_seriesEval_formalLog {z : K} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n (formalLog K) * z ^ n :=
  summable_seriesEval_of_norm_coeff_le_linear (C := 1)
    (fun n => by simpa using norm_coeff_formalLog_le (p := p) n) hz

omit [CharZero K] in
include hp in
/-- T618 (the eval-alignment): for `‖z − 1‖ < 1`, `seriesEval (formalLog K) (z − 1) =
padicLog p z`. Reindex by one (`coeff 0 = 0`) and match the scalar `((n:ℚ_[p])+1)⁻¹`
against `((n:K)+1)⁻¹` through `algebraMap`. -/
theorem seriesEval_formalLog {z : K} (hz : ‖z - 1‖ < 1) :
    seriesEval (formalLog K) (z - 1) = padicLog p z := by
  have hsum := summable_seriesEval_formalLog (p := p) hz
  rw [seriesEval, hsum.tsum_eq_zero_add, coeff_zero_formalLog, zero_mul, zero_add, padicLog]
  refine tsum_congr fun n => ?_
  rw [coeff_succ_formalLog, Algebra.smul_def,
    show algebraMap ℚ_[p] K ((n : ℚ_[p]) + 1)⁻¹ = ((n : K) + 1)⁻¹ from by
      rw [map_inv₀, map_add, map_natCast, map_one]]
  ring

omit [CharZero K] in
include hp in
/-- T618: `padicLog p (z^p) = (p : K) • padicLog p z` for `‖z − 1‖ < 1` — the
boundary `p`-power law. Evaluate `phiSeries_formalLog` at `z − 1` through the
`seriesEval` bridge: `padicLog (z^p) = seriesEval formalLog (z^p − 1) =
seriesEval (φ formalLog) (z − 1) = seriesEval (p·formalLog) (z − 1) =
p·padicLog z`. -/
theorem padicLog_pow_p_of_norm_lt_one {z : K} (hz : ‖z - 1‖ < 1) :
    padicLog p (z ^ p) = (p : K) • padicLog p z := by
  have hzp1 : ‖z ^ p - 1‖ < 1 := boundary_norm_pow_sub_one_lt_one hz p
  have h1z : (1 : K) + (z - 1) = z := by ring
  have hzp1' : ‖(1 + (z - 1)) ^ p - 1‖ < 1 := by rwa [h1z]
  have hprodsum := summable_prod_of_norm_coeff_le_linear (p := p) (G := formalLog K) (C := 1)
    (fun n => by simpa using norm_coeff_formalLog_le (p := p) n) hz
  -- evaluate `φ formalLog` at `z − 1`, two ways
  have hbridge : seriesEval (phiSeries p (formalLog K)) (z - 1) = padicLog p (z ^ p) := by
    rw [seriesEval_phi_of_summable_prod p (formalLog K) (z - 1) hprodsum,
      ← seriesEval, seriesEval_formalLog (p := p) hzp1', h1z]
  rw [← hbridge, phiSeries_formalLog, PowerSeries.smul_eq_C_mul, seriesEval_C_mul,
    seriesEval_formalLog (p := p) hz, smul_eq_mul]

omit [CharZero K] in
include hp in
/-- T618: `padicLog p (z ^ (p ^ N)) = (p ^ N : K) • padicLog p z` for `‖z − 1‖ < 1`
(iterate the `p`-power law; each intermediate `z ^ (p ^ i)` stays in the unit ball). -/
theorem padicLog_pow_pPow_of_norm_lt_one {z : K} (hz : ‖z - 1‖ < 1) (N : ℕ) :
    padicLog p (z ^ (p ^ N)) = ((p : K) ^ N) • padicLog p z := by
  induction N with
  | zero => rw [pow_zero, pow_one, pow_zero, one_smul]
  | succ M ih =>
    rw [pow_succ, pow_mul, padicLog_pow_p_of_norm_lt_one (p := p)
        (boundary_norm_pow_sub_one_lt_one hz (p ^ M)), ih, smul_smul, pow_succ, mul_comm]

omit [CharZero K] in
include hp in
/-- T618: multiplicativity of `padicLog` on the whole open unit ball:
`padicLog p (x * y) = padicLog p x + padicLog p y` when `‖x − 1‖ < 1` and `‖y − 1‖ < 1`. -/
theorem padicLog_mul_of_norm_lt_one {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    padicLog p (x * y) = padicLog p x + padicLog p y := by
  have hxy : ‖x * y - 1‖ < 1 := by
    rw [show x * y - 1 = (x - 1) * y + (y - 1) by ring]
    have hy1 : ‖y‖ ≤ 1 := by
      rw [show y = (y - 1) + 1 by ring]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp [hy.le])
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hy)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hy1).trans_lt hx
  obtain ⟨jx, hjx⟩ := exists_pPow_pow_inExpBall (p := p) hx
  obtain ⟨jy, hjy⟩ := exists_pPow_pow_inExpBall (p := p) hy
  have hpow_ball : ∀ {w : K} {j : ℕ} (d : ℕ), InExpBall p (w ^ p ^ j - 1) →
      InExpBall p (w ^ p ^ (j + d) - 1) := fun d hwj => by
    rw [pow_add, pow_mul]
    exact pow_mem_expBall (p := p) hwj (p ^ d)
  set N : ℕ := max jx jy with hN
  have hbx : InExpBall p (x ^ p ^ N - 1) := by
    rw [hN, show max jx jy = jx + (max jx jy - jx) by omega]
    exact hpow_ball _ hjx
  have hby : InExpBall p (y ^ p ^ N - 1) := by
    rw [hN, show max jx jy = jy + (max jx jy - jy) by omega]
    exact hpow_ball _ hjy
  have hkey : padicLog p ((x * y) ^ p ^ N) = padicLog p (x ^ p ^ N) + padicLog p (y ^ p ^ N) := by
    rw [mul_pow, padicLog_mul (p := p) hbx hby]
  rw [padicLog_pow_pPow_of_norm_lt_one (p := p) hxy,
    padicLog_pow_pPow_of_norm_lt_one (p := p) hx,
    padicLog_pow_pPow_of_norm_lt_one (p := p) hy, ← smul_add] at hkey
  exact smul_right_injective K (pow_ne_zero _ (natCast_p_ne_zero (L := K) p)) hkey

omit [CharZero K] in
include hp in
/-- T618: `padicLog p (x ^ n) = n • padicLog p x` on the whole open unit ball
(induction via `padicLog_mul_of_norm_lt_one`). -/
theorem padicLog_pow_of_norm_lt_one {x : K} (hx : ‖x - 1‖ < 1) (n : ℕ) :
    padicLog p (x ^ n) = n • padicLog p x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicLog_mul_of_norm_lt_one (p := p)
        (boundary_norm_pow_sub_one_lt_one hx k) hx, ih, succ_nsmul]

omit [CharZero K] in
include hp in
/-- T618: `extLog p x = padicLog p x` on the whole open unit ball `‖x − 1‖ < 1`. The
witness `(p^j, 0, x^{p^j})` (with `x^{p^j}` in the exp ball, `exists_pPow_pow_inExpBall`)
computes `extLog`, and the `p^j`-power law cancels the `(p^j)⁻¹`-scalar. -/
theorem extLog_eq_padicLog_of_norm_lt_one {x : K} (hx : ‖x - 1‖ < 1) :
    extLog p x = padicLog p x := by
  obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall (p := p) hx
  have hpne : ((p ^ j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (pow_pos hp.out.pos j).ne'
  rw [extLog_eq_of_witness (p := p) (m := p ^ j) (k := 0) (y := x ^ p ^ j)
      (pow_pos hp.out.pos j) (by rw [zpow_zero, one_mul]) hj,
    padicLog_pow_pPow_of_norm_lt_one (p := p) hx,
    -- rewrite the `K`-scalar `(p:K)^j` as the `ℚ_[p]`-scalar `((p^j:ℕ):ℚ_[p])`
    show ((p : K) ^ j) • padicLog p x = ((p ^ j : ℕ) : ℚ_[p]) • padicLog p x from by
      rw [smul_eq_mul, Algebra.smul_def, map_natCast]; push_cast; ring,
    smul_smul, inv_mul_cancel₀ hpne, one_smul]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Character values into `K` have norm `≤ 1` (units map to roots of unity of
norm one, non-units to `0`). -/
private theorem norm_dirichletChar_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter K N)
    (c : ZMod N) : ‖ψ c‖ ≤ 1 := by
  rcases eq_or_ne (ψ c) 0 with h0 | h0
  · rw [h0, norm_zero]; exact zero_le_one
  · have hu : IsUnit c := by by_contra hu; exact h0 (ψ.map_nonunit hu)
    obtain ⟨u, rfl⟩ := hu
    have hpow : ψ (u : ZMod N) ^ Nat.totient N = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
    exact le_of_eq (PadicLFunctions.norm_eq_one_of_pow_eq_one (L := K) hpow
      (Nat.totient_pos.2 (NeZero.pos N)).ne')

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `Ring.inverse (1 + X) = ∑ (−1)ⁿ Xⁿ`, hence has integral coefficients. -/
private theorem norm_coeff_inverse_one_add_X_le_one (n : ℕ) :
    ‖PowerSeries.coeff n (Ring.inverse (1 + PowerSeries.X : PowerSeries K))‖ ≤ 1 := by
  have hunit : IsUnit (1 + PowerSeries.X : PowerSeries K) := by
    simp [PowerSeries.isUnit_iff_constantCoeff]
  have hgeom : (1 + PowerSeries.X : PowerSeries K)
      * (PowerSeries.mk fun n => (-1) ^ n) = 1 := by
    have := one_add_C_mul_X_mul_geom (R := K) 1
    rwa [map_one, one_mul] at this
  rw [ring_inverse_eq_of_mul_eq_one hunit hgeom, PowerSeries.coeff_mk, norm_pow, norm_neg,
    norm_one, one_pow]

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- Bounded antiderivative (c₀-design): when `B` has integral coefficients, the
antiderivative `C` (from the coefficient-wise division) has linearly-bounded
coefficients `‖coeff m C‖ ≤ p·(m+1)` — the `(p(m+1))⁻¹`-factor has polynomial
norm. Feeds the convergence of `seriesEval (φ C₁)` in the constant pin. -/
theorem exists_antideriv_bounded (B : PowerSeries K)
    (hB : ∀ n, ‖PowerSeries.coeff n B‖ ≤ 1) :
    ∃ C : PowerSeries K, PowerSeries.constantCoeff C = 0
      ∧ (p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C) = B
      ∧ ∀ m, ‖PowerSeries.coeff m C‖ ≤ (p : ℝ) * ((m : ℝ) + 1) := by
  haveI := charZero_of_qpAlgebra (M := K) p
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hunit : IsUnit (1 + PowerSeries.X : PowerSeries K) := by
    simp [PowerSeries.isUnit_iff_constantCoeff]
  set E : PowerSeries K := (p : K)⁻¹ • (B * Ring.inverse (1 + PowerSeries.X)) with hE
  have hpinv : ‖((p : K))⁻¹‖ ≤ (p : ℝ) := norm_natCast_inv_le (p := p) (K := K) hp.out.one_le
  -- `‖coeff k E‖ ≤ p`  (integral product scaled by `(p:K)⁻¹` of norm `p`)
  have hEbd : ∀ k, ‖PowerSeries.coeff k E‖ ≤ (p : ℝ) := by
    intro k
    rw [hE, map_smul, smul_eq_mul, norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (by rw [mul_one]; exact hpinv)
    rw [PowerSeries.coeff_mul]
    rcases (Finset.antidiagonal k).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact zero_le_one
    obtain ⟨ab, -, hab⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun ab => PowerSeries.coeff ab.1 B
        * PowerSeries.coeff ab.2 (Ring.inverse (1 + PowerSeries.X)))
    refine hab.trans ?_
    rw [norm_mul]
    exact mul_le_one₀ (hB ab.1) (norm_nonneg _) (norm_coeff_inverse_one_add_X_le_one ab.2)
  refine ⟨PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) E / n, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]
  · have hDC : PowerSeries.derivativeFun
        (PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) E / n) = E := by
      refine PowerSeries.ext fun n => ?_
      rw [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n),
        Nat.add_sub_cancel]
      have hne : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [Nat.cast_succ, div_mul_cancel₀ _ hne]
    rw [hDC, hE, mul_smul_comm, smul_smul, mul_inv_cancel₀ hp0, one_smul,
      mul_comm (1 + PowerSeries.X), mul_assoc, Ring.inverse_mul_cancel _ hunit, mul_one]
  · intro m
    rw [PowerSeries.coeff_mk]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [if_pos rfl, norm_zero]; positivity
    · rw [if_neg (by omega : m ≠ 0), div_eq_mul_inv, norm_mul]
      calc ‖PowerSeries.coeff (m - 1) E‖ * ‖((m : K))⁻¹‖
          ≤ (p : ℝ) * (m : ℝ) :=
            mul_le_mul (hEbd _) (norm_natCast_inv_le (p := p) (K := K) hm) (norm_nonneg _)
              (by positivity)
        _ ≤ (p : ℝ) * ((m : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- For a norm-one argument `‖u − 1‖ = 1` (so `‖u‖ = 1`), the positive-degree
coefficients of `logSeriesAt u` are bounded linearly: `‖coeff n (logSeriesAt u)‖ ≤ n`
for `n ≥ 1` (the `1/n`-factor has norm `≤ n` and `‖u/(u−1)‖ = 1`). -/
private theorem norm_coeff_logSeriesAt_le_of_norm_one {u : K} (hu1 : ‖u - 1‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) : ‖PowerSeries.coeff n (logSeriesAt p K u)‖ ≤ (n : ℝ) := by
  -- `‖u‖ ≤ 1`: `u = (u−1) + 1`, both summands of norm `≤ 1`
  have hunorm : ‖u‖ ≤ 1 := by
    calc ‖u‖ = ‖(u - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖u - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [hu1, norm_one, max_self]
  rw [logSeriesAt, PowerSeries.coeff_mk, if_neg (by omega : n ≠ 0)]
  have hratio : ‖u / (u - 1)‖ ≤ 1 := by rwa [norm_div, hu1, div_one]
  calc ‖(-1 : K) ^ (n - 1) * ((n : K))⁻¹ * (u / (u - 1)) ^ n‖
      = ‖((n : K))⁻¹‖ * ‖u / (u - 1)‖ ^ n := by
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    _ ≤ ‖((n : K))⁻¹‖ * 1 := by
        refine mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hratio) (norm_nonneg _)
    _ = ‖((n : K))⁻¹‖ := mul_one _
    _ ≤ (n : ℝ) := norm_natCast_inv_le (p := p) (K := K) hn

omit [CharZero K] in
include hp in
/-- Lem 6.2 as a coefficient bound: with the contributing roots of norm one,
`‖coeff n F̃‖ ≤ C·(n+1)` for a uniform `C` (the positive-degree coefficients are
linearly bounded; the constant term is absorbed). Hence `seriesEval F̃ z` converges
for `‖z‖ < 1`. -/
private theorem summable_seriesEval_Ftilde {N : ℕ} [NeZero N] (_hN : 1 < N)
    {θ : DirichletCharacter K N} {ε : K} (hε : IsPrimitiveRoot ε N)
    (hnorm : ∀ c ∈ Finset.range N, IsUnit ((c : ZMod N)) → ‖ε ^ c - 1‖ = 1)
    {z : K} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n (Ftilde p K θ hε) * z ^ n := by
  -- linear bound `‖coeff n F̃‖ ≤ C·(n+1)` with `C := max ‖coeff 0 F̃‖ 1`
  set C : ℝ := max ‖PowerSeries.constantCoeff (Ftilde p K θ hε)‖ 1
  refine summable_seriesEval_of_norm_coeff_le_linear (C := C) (fun n => ?_) hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- constant term: `‖coeff 0 F̃‖ ≤ C ≤ C·1`
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero]
    calc ‖PowerSeries.constantCoeff (Ftilde p K θ hε)‖ ≤ C := le_max_left _ _
      _ = C * ((0 : ℝ) + 1) := by ring
  · -- positive degree: ultrametric `‖Σ_c term_c‖ ≤ max_c ‖term_c‖ ≤ n ≤ C·(n+1)`
    rw [Ftilde, map_neg, norm_neg, map_sum]
    have hbd : ‖∑ c ∈ Finset.range N, PowerSeries.coeff n
          (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))‖ ≤ (n : ℝ) := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun c hc => ?_
      rw [PowerSeries.coeff_C_mul, norm_mul]
      by_cases hcu : IsUnit ((c : ZMod N))
      · calc ‖θ⁻¹ ((c : ZMod N))‖ * ‖PowerSeries.coeff n (logSeriesAt p K (ε ^ c))‖
            ≤ 1 * (n : ℝ) :=
              mul_le_mul (norm_dirichletChar_le_one _ _)
                (norm_coeff_logSeriesAt_le_of_norm_one (u := ε ^ c) (hnorm c hc hcu) hn)
                (norm_nonneg _) zero_le_one
          _ = (n : ℝ) := one_mul _
      · -- `θ⁻¹(c) = 0` (non-unit `c`); whole term vanishes
        rw [show (θ⁻¹) ((c : ZMod N)) = 0 from MulChar.map_nonunit _ hcu, norm_zero, zero_mul]
        positivity
    refine le_trans hbd (le_trans ?_ (le_mul_of_one_le_left (by positivity) (le_max_right _ _)))
    linarith

set_option maxHeartbeats 800000 in
-- The c₀-design proof chains many `rw`s over `PowerSeries.coeff`/`derivativeFun`
-- through the heavy `rhoTheta`/`twist` measure terms; the elaboration is heartbeat-heavy.
/-- P6-p6' (the constant pin, c₀-design — replan R6.6; Lem 6.3 made
distribution-free WITHOUT field-level `ψ`): the cleared mass identity
`p·𝓐_ρ(0)·G = p·F̃(0) − Σ_{i<p} F̃(ξ^i−1)`. Internally: `W := C G⁻¹·F̃ −
𝓐_ρ` has `∂W = φ(B)` for the bounded `B = G⁻¹-cleared 𝓐(ψ-part)`, so
`W = φC + c₀` (antiderivative + ker ∂); evaluating at `0` and at the
`ξ^i − 1` (where `φ`-images collapse and `Σ 𝓐_ρ(ξ^i−1) = p·𝓐_{ψρ}(0) = 0`
by `sum_seriesEval_mahlerK` + `psi_rhoTheta`) pins `c₀`.

**Statement-fix (replan R6.6, recorded 2026-06-11; coprime-guard refinement
2026-06-12 in `b2_log.jsonl`):** the original frozen skeleton omitted the norm
hypothesis `hnorm`, needed to bound `‖coeff n F̃‖` linearly so the evaluations
`seriesEval F̃ (ξ^i − 1)` converge (Lem 6.2's `ℛ⁺`-membership, as a coefficient
bound). `hnorm` is guarded by `IsUnit (c : ZMod N)` (equivalently `c` coprime to
`N`): only the unit-`c` terms contribute (`θ⁻¹(c) = 0` otherwise), and for those
the tame part `D > 1` forces `‖ε^c − 1‖ = 1` (RJW's cyclotomic-product fact, T612
`norm_one_sub_pow_eq_one`). The original `¬N∣c`-guard is FALSE for `c = D·j`
(`ε^{Dj}` a nontrivial `p`-power root, norm `< 1`), hence undischargeable in
`LpFunction_one`; the coprime-guarded form IS discharged there. The
`IsUnit (ε^c − 1)` side-condition of `one_add_mul_derivative_Ftilde` is now proved
directly (`ε^c ≠ 1` for `¬N∣c` since `ε` is primitive, and a field nonzero is a
unit). -/
theorem p_mul_constantCoeff_mahlerK_rhoTheta {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (_hχ : χ.IsPrimitive)
    {θK : DirichletCharacter K (D * p ^ n)} (hN : 1 < D * p ^ n)
    (hθ1 : θK ≠ 1)
    (_hθK : θK = toFieldChar (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n)) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p)
    (hnorm : ∀ c ∈ Finset.range (D * p ^ n), IsUnit ((c : ZMod (D * p ^ n))) →
      ‖ε ^ c - 1‖ = 1)
    {G : K} (_hG : IsUnit G)
    (hGtwist : mahlerK p K (twist p K χ.toContinuousMapZp
        (muEtaCleared p K η hζ hD))
      = PowerSeries.C G⁻¹ * (-∑ c ∈ Finset.range (D * p ^ n),
          PowerSeries.C (θK⁻¹ ((c : ZMod (D * p ^ n))))
            * Ring.inverse ((1 + PowerSeries.X)
              * PowerSeries.C (ε ^ c) - 1))) :
    (p : K) * PowerSeries.constantCoeff
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = G⁻¹ * ((p : K) * PowerSeries.constantCoeff (Ftilde p K θK hε)
        - ∑ i : Fin p, seriesEval (Ftilde p K θK hε) (ξ ^ (i : ℕ) - 1)) := by
  haveI : Fact (1 < D * p ^ n) := ⟨hN⟩
  -- abbreviations for the power-series objects (NOT the heavy measure terms, which
  -- `set` would expensively abstract through `rhoTheta`/`twist`/`muEtaCleared`)
  -- the unit hypothesis for `one_add_mul_derivative_Ftilde`: `ε^c − 1 ≠ 0` for `¬N∣c`
  -- (a field nonzero is a unit); `ε^c = 1 ⟺ N∣c` since `ε` is a primitive `N`-th root
  have hunit : ∀ c ∈ Finset.range (D * p ^ n), ¬ (D * p ^ n) ∣ c → IsUnit (ε ^ c - 1) :=
    fun c _ hcd => isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h =>
      hcd ((hε.pow_eq_one_iff_dvd c).1 h))
  -- the `ψ`-part `K`-series `B` (integral coefficients) and the antiderivative `C₁`
  obtain ⟨C₁, hC₁0, hC₁, hC₁bd⟩ := exists_antideriv_bounded (p := p)
    (mahlerK p K (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))))
    (norm_coeff_mahlerK_le_one _ _)
  -- `(1+X)·∂(C G⁻¹·F̃) = mahlerK tw`  (proven `∂F̃` + `hGtwist`, with `C`-scalar pulled out)
  have hCFder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (PowerSeries.C G⁻¹ * Ftilde p K θK hε)
      = mahlerK p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)) := by
    rw [show PowerSeries.derivativeFun (PowerSeries.C G⁻¹ * Ftilde p K θK hε)
          = PowerSeries.C G⁻¹ * PowerSeries.derivativeFun (Ftilde p K θK hε) from by
        rw [show PowerSeries.C G⁻¹ * Ftilde p K θK hε = G⁻¹ • Ftilde p K θK hε from
          (PowerSeries.smul_eq_C_mul _ _).symm, PowerSeries.derivativeFun_smul,
          PowerSeries.smul_eq_C_mul],
      show (1 + PowerSeries.X) * (PowerSeries.C G⁻¹ * PowerSeries.derivativeFun (Ftilde p K θK hε))
          = PowerSeries.C G⁻¹
            * ((1 + PowerSeries.X) * PowerSeries.derivativeFun (Ftilde p K θK hε)) from by ring,
      one_add_mul_derivative_Ftilde hN hθ1 hε hunit, hGtwist]
  -- `(1+X)·∂(𝓐_ρ) = mahlerK tw − φ B`  (Res = 1 − φψ, transported)
  have hAder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = mahlerK p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
        - phiSeries p (mahlerK p K
          (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))) := by
    rw [one_add_mul_derivative_mahlerK_rhoTheta hD1 hη hζ hD χ, res_units_eq, mahlerK_sub,
      mahlerK_phi]
  -- the W-equation: `(1+X)·∂W = φ B` where `W := C G⁻¹·F̃ − 𝓐_ρ`
  have hWder : (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
      = phiSeries p (mahlerK p K
          (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))) := by
    rw [show PowerSeries.derivativeFun
          (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
        = PowerSeries.derivativeFun (PowerSeries.C G⁻¹ * Ftilde p K θK hε)
          - PowerSeries.derivativeFun (mahlerK p K (rhoTheta p K η hζ hD χ)) from
        map_sub (PowerSeries.derivative K) _ _,
      mul_sub, hCFder, hAder]
    ring
  -- `(1+X)·∂(φ C₁) = φ B`  (∂φ = p·φ∂ + scalar pull-through)
  have hphiC₁der : (1 + PowerSeries.X) * PowerSeries.derivativeFun (phiSeries p C₁)
      = phiSeries p (mahlerK p K
          (MeasureR.psi p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))) := by
    rw [one_add_mul_derivative_phiSeries,
      show (p : K) • phiSeries p ((1 + PowerSeries.X) * PowerSeries.derivativeFun C₁)
        = phiSeries p ((p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C₁)) from by
        rw [PowerSeries.smul_eq_C_mul, ← phiSeries_C_mul, ← PowerSeries.smul_eq_C_mul], hC₁]
  -- `W − φ C₁` is `∂`-killed, hence the constant `C c₀`; set `c₀ := constantCoeff(W − φC₁)`
  have hker : (1 + PowerSeries.X) * PowerSeries.derivativeFun
      ((PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
        - phiSeries p C₁) = 0 := by
    rw [show PowerSeries.derivativeFun
          ((PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
            - phiSeries p C₁)
        = PowerSeries.derivativeFun
            (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
          - PowerSeries.derivativeFun (phiSeries p C₁) from
        map_sub (PowerSeries.derivative K) _ _,
      mul_sub, hWder, hphiC₁der, sub_self]
  have hWeq := eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero (p := p) hker
  set c₀ := PowerSeries.constantCoeff
    ((PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ))
      - phiSeries p C₁)
  -- so `W = φ C₁ + C c₀`
  have hWval : PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ)
      = phiSeries p C₁ + PowerSeries.C c₀ := by rw [← hWeq]; ring
  -- `‖z_j‖ < 1` and `(1 + z_j)^p = 1` for `z_j = ξ^j − 1`
  have hzlt : ∀ j : Fin p, ‖ξ ^ (j : ℕ) - 1‖ < 1 := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
    · rw [hj0, pow_zero, sub_self, norm_zero]; exact one_pos
    · have hcop : (j : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hjpos hdvd) (by omega : ¬ p ≤ (j : ℕ)))
      exact (by rw [pow_one] at *; exact hξ.pow_of_coprime (j : ℕ) hcop :
        IsPrimitiveRoot (ξ ^ (j : ℕ)) (p ^ 1)).norm_sub_one_lt (p := p)
  have hzp : ∀ j : Fin p, (1 + (ξ ^ (j : ℕ) - 1)) ^ p = 1 := fun j => by
    rw [show (1 : K) + (ξ ^ (j : ℕ) - 1) = ξ ^ (j : ℕ) by ring, ← pow_mul, mul_comm, pow_mul,
      hξ.pow_eq_one, one_pow]
  -- summability facts at `z_j = ξ^j − 1`
  have hsumF : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (Ftilde p K θK hε) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_seriesEval_Ftilde (θ := θK) hN hε hnorm (hzlt j)
  have hsumA : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (mahlerK p K (rhoTheta p K η hζ hD χ)) * (ξ ^ (j : ℕ) - 1) ^ m :=
    fun j => summable_seriesEval_of_norm_coeff_le_one (norm_coeff_mahlerK_le_one _ _) (hzlt j)
  have hsumCF : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.C G⁻¹ * Ftilde p K θK hε) * (ξ ^ (j : ℕ) - 1) ^ m :=
    fun j => ((hsumF j).mul_left G⁻¹).congr fun m => by rw [PowerSeries.coeff_C_mul, mul_assoc]
  -- the constant series `C c₀` evaluates summably (finite support)
  have hsumCc₀ : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.C c₀) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_of_ne_finset_zero (s := {0}) fun m hm => by
      rw [PowerSeries.coeff_C, if_neg (by simpa using hm), zero_mul]
  have hsumphiC₁ : ∀ j : Fin p, Summable fun m : ℕ =>
      PowerSeries.coeff m (phiSeries p C₁) * (ξ ^ (j : ℕ) - 1) ^ m := fun j =>
    summable_seriesEval_of_norm_coeff_le_linear (C := (p : ℝ))
      (norm_coeff_phiSeries_le_linear p (C := (p : ℝ)) (by positivity) hC₁bd) (hzlt j)
  -- evaluating `W = φ C₁ + C c₀` at each `z_j` gives `c₀`; on the other side
  -- `seriesEval W z_j = G⁻¹·F̃(z_j) − 𝓐_ρ(z_j)`. Sum over `j`.
  have hsumW : ∑ j : Fin p, (G⁻¹ * seriesEval (Ftilde p K θK hε) (ξ ^ (j : ℕ) - 1)
        - seriesEval (mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1))
      = (p : K) * c₀ := by
    rw [show (∑ j : Fin p, (G⁻¹ * seriesEval (Ftilde p K θK hε) (ξ ^ (j : ℕ) - 1)
          - seriesEval (mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1)))
        = ∑ j : Fin p, seriesEval
            (PowerSeries.C G⁻¹ * Ftilde p K θK hε
              - mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1) from
      Finset.sum_congr rfl fun j _ => by
        rw [seriesEval_sub (hsumCF j) (hsumA j), seriesEval_C_mul]]
    rw [show (∑ j : Fin p, seriesEval
            (PowerSeries.C G⁻¹ * Ftilde p K θK hε
              - mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1))
        = ∑ _j : Fin p, c₀ from Finset.sum_congr rfl fun j _ => by
      rw [hWval, seriesEval_add (hsumphiC₁ j) (hsumCc₀ j),
        seriesEval_phi_at_root_of_summable p
          (summable_prod_of_norm_coeff_le_linear p (C := (p : ℝ)) hC₁bd (hzlt j)) (hzp j),
        hC₁0, seriesEval_C, zero_add]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the `𝓐_ρ`-sum vanishes: `Σ_j 𝓐_ρ(z_j) = p·constantCoeff (mahlerK (ψρ)) = 0`
  have hAsum : ∑ j : Fin p, seriesEval (mahlerK p K (rhoTheta p K η hζ hD χ)) (ξ ^ (j : ℕ) - 1)
      = 0 := by
    rw [sum_seriesEval_mahlerK (p := p) hξ (rhoTheta p K η hζ hD χ), psi_rhoTheta hζ hD χ]
    simp [mahlerK]
  -- `p·c₀ = G⁻¹·Σ_j F̃(z_j)`
  have hexpand : (p : K) * c₀ = G⁻¹ * ∑ j : Fin p, seriesEval (Ftilde p K θK hε) (ξ ^ (j : ℕ) - 1)
      := by rw [← hsumW, Finset.sum_sub_distrib, ← Finset.mul_sum, hAsum, sub_zero]
  -- `c₀ = G⁻¹·constantCoeff F̃ − constantCoeff 𝓐_ρ` (evaluate `W = φC₁ + C c₀` at `0`)
  have hcWexp : c₀ = G⁻¹ * PowerSeries.constantCoeff (Ftilde p K θK hε)
      - PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ)) := by
    have : c₀ = PowerSeries.constantCoeff
        (PowerSeries.C G⁻¹ * Ftilde p K θK hε - mahlerK p K (rhoTheta p K η hζ hD χ)) := by
      rw [hWval, map_add, constantCoeff_phiSeries, hC₁0, zero_add, PowerSeries.constantCoeff_C]
    rw [this, map_sub, map_mul, PowerSeries.constantCoeff_C]
  -- assemble the displayed identity
  have h1 : (p : K) * c₀ = (p : K) * (G⁻¹ * PowerSeries.constantCoeff (Ftilde p K θK hε))
      - (p : K) * PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ)) := by
    rw [hcWexp]; ring
  rw [hexpand] at h1
  linear_combination h1

/-! #### Helpers for the evaluated trace `sum_seriesEval_Ftilde` (T616, RJW TeX 2113–2155)

The route (decomposition R6 P6-p7 + replans R6.3/R6.6): a per-term resummation
`seriesEval (logSeriesAt (ε^c)) (ξ^i − 1) = extLog(ξ^i·ε^c − 1)` (split constant +
tail, the tail being `padicLog` of `1 + ε^c(ξ^i−1)/(ε^c−1)` via the T618 layer), the
`μ_p`-collapse `Σ_{i<p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)`
(`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` + `extLog_prod`), and the `c ↦ pc`
bookkeeping (automorphism for `¬p∣N`; primitive-character fiber sums for `p∣N`). -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A root of unity is integral over `ℤ` (it satisfies the monic `Xⁿ − C 1`). -/
private theorem isIntegral_of_pow_eq_one {x : K} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) :
    IsIntegral ℤ x :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hx]⟩

omit [CompleteSpace K] [CharZero K] in
/-- The shifted root `ξ^i·ε^c − 1` has norm one (`‖ε^c − 1‖ = 1` and the isoceles
`‖ξ^i ε^c − ε^c‖ = ‖ξ^i − 1‖ < 1 = ‖ε^c − 1‖`). -/
private theorem norm_pow_mul_pow_sub_one_eq_one {ε ξ : K} {N : ℕ} (hN0 : 0 < N)
    (hε : IsPrimitiveRoot ε N) {c i : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ‖ξ ^ i - 1‖ < 1) :
    ‖ξ ^ i * ε ^ c - 1‖ = 1 := by
  have hεc1 : ‖ε ^ c‖ = 1 :=
    norm_eq_one_of_pow_eq_one (L := K) (m := N)
      (by rw [← pow_mul, mul_comm, pow_mul, hε.pow_eq_one, one_pow]) hN0.ne'
  have hlt : ‖ξ ^ i * ε ^ c - ε ^ c‖ < ‖ε ^ c - 1‖ := by
    rw [show ξ ^ i * ε ^ c - ε ^ c = (ξ ^ i - 1) * ε ^ c from by ring, norm_mul, hεc1,
      mul_one, hc1]; exact hil
  have hkey := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hlt)
  rw [show (ξ ^ i * ε ^ c - ε ^ c) + (ε ^ c - 1) = ξ ^ i * ε ^ c - 1 from by ring,
    max_eq_right hlt.le, hc1] at hkey
  exact hkey

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- T616 step 3 (domain engine): the shifted root `ξ^i·ε^c − 1` lies in the extended-log
domain — it is integral (a root of unity minus `1`) and has norm one. -/
private theorem extLogDomain_pow_mul_pow_sub_one {ε ξ : K} {N : ℕ} (hN0 : 0 < N)
    (hε : IsPrimitiveRoot ε N) (hξ : IsPrimitiveRoot ξ p) {c i : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ‖ξ ^ i - 1‖ < 1) :
    ExtLogDomain p (ξ ^ i * ε ^ c - 1) :=
  extLogDomain_of_integral_norm_one p
    ((((isIntegral_of_pow_eq_one (n := p) hp.out.pos hξ.pow_eq_one).pow i).mul
      ((isIntegral_of_pow_eq_one (n := N) hN0 hε.pow_eq_one).pow c)).sub isIntegral_one)
    (norm_pow_mul_pow_sub_one_eq_one hN0 hε hc1 hil)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The positive-degree coefficients of `logSeriesAt u` factor through `formalLog`:
`coeff (n+1) (logSeriesAt u) = coeff (n+1) (formalLog) · (u/(u−1))^{n+1}`. -/
private theorem coeff_succ_logSeriesAt (u : K) (n : ℕ) :
    PowerSeries.coeff (n + 1) (logSeriesAt p K u)
      = PowerSeries.coeff (n + 1) (formalLog K) * (u / (u - 1)) ^ (n + 1) := by
  rw [logSeriesAt, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), coeff_succ_formalLog,
    Nat.add_sub_cancel, Nat.cast_succ]

omit [CharZero K] in
include hp in
/-- Summability of `seriesEval (logSeriesAt u) z` for `‖u − 1‖ = 1`, `‖z‖ < 1` (the
positive coefficients are `≤ n`; the constant `extLog(u−1)` is absorbed into `C`). -/
private theorem summable_seriesEval_logSeriesAt {u z : K} (hu1 : ‖u - 1‖ = 1) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n (logSeriesAt p K u) * z ^ n := by
  set C : ℝ := max ‖extLog p (u - 1)‖ 1
  refine summable_seriesEval_of_norm_coeff_le_linear (C := C) (fun n => ?_) hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [logSeriesAt, PowerSeries.coeff_mk, if_pos rfl, Nat.cast_zero]
    calc ‖extLog p (u - 1)‖ ≤ C := le_max_left _ _
      _ = C * ((0 : ℝ) + 1) := by ring
  · refine le_trans (norm_coeff_logSeriesAt_le_of_norm_one (p := p) hu1 hn) ?_
    calc (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      _ ≤ C * ((n : ℝ) + 1) := le_mul_of_one_le_left (by positivity) (le_max_right _ _)

omit [CharZero K] in
include hp in
/-- T616 step 1 (the per-term resummation, half a): for `‖u − 1‖ = 1` and `‖z‖ < 1`,
`seriesEval (logSeriesAt u) z = extLog(u − 1) + padicLog (1 + u·z/(u−1))`. Split the
constant coefficient `extLog(u−1)` off and identify the tail with `seriesEval (formalLog)
(u·z/(u−1)) = padicLog (1 + u·z/(u−1))` (T618 eval-alignment). -/
private theorem seriesEval_logSeriesAt_of_norm {u z : K} (hu1 : ‖u - 1‖ = 1) (hz : ‖z‖ < 1) :
    seriesEval (logSeriesAt p K u) z
      = extLog p (u - 1) + padicLog p (1 + u * z / (u - 1)) := by
  -- `‖u‖ = 1`, so `‖w‖ = ‖u·z/(u−1)‖ = ‖z‖ < 1`
  have hunorm : ‖u‖ ≤ 1 := by
    calc ‖u‖ = ‖(u - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖u - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [hu1, norm_one, max_self]
  have hwnorm : ‖u * z / (u - 1)‖ < 1 := by
    rw [norm_div, hu1, div_one, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hunorm) hz
  have hsum := summable_seriesEval_logSeriesAt (p := p) hu1 hz
  have hcoeff0 : PowerSeries.coeff 0 (logSeriesAt p K u) = extLog p (u - 1) := by
    rw [logSeriesAt, PowerSeries.coeff_mk, if_pos rfl]
  -- the `padicLog`/`formalLog` tail at `w := u·z/(u−1)`
  have htail : padicLog p (1 + u * z / (u - 1))
      = seriesEval (formalLog K) (u * z / (u - 1)) := by
    rw [← seriesEval_formalLog (p := p)
      (show ‖(1 + u * z / (u - 1)) - 1‖ < 1 from by rwa [add_sub_cancel_left]),
      add_sub_cancel_left]
  rw [seriesEval, hsum.tsum_eq_zero_add, hcoeff0, pow_zero, mul_one, htail, seriesEval,
    (summable_seriesEval_formalLog (p := p) hwnorm).tsum_eq_zero_add, coeff_zero_formalLog,
    zero_mul, zero_add]
  refine congrArg _ (tsum_congr fun n => ?_)
  rw [coeff_succ_logSeriesAt, coeff_succ_formalLog,
    show u * z / (u - 1) = (u / (u - 1)) * z from by ring, mul_pow]
  ring

omit [CompleteSpace K] [CharZero K] in
include hp in
/-- T616: any element of the open unit ball `‖x − 1‖ < 1` lies in the extended-log
domain (a `p`-power iterate lands in the exp ball; `exists_pPow_pow_inExpBall`). -/
private theorem extLogDomain_of_norm_sub_one_lt_one {x : K} (hx : ‖x - 1‖ < 1) :
    ExtLogDomain p x := by
  obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall (p := p) hx
  exact ⟨p ^ j, 0, x ^ p ^ j, pow_pos hp.out.pos j, by rw [zpow_zero, one_mul], hj⟩

omit [CharZero K] in
include hp in
/-- T616 step 1 (the per-term identity): for `‖ε^c − 1‖ = 1` and `‖ξ^i − 1‖ < 1`
(with `ε` integral over `ℤ`), `seriesEval (logSeriesAt (ε^c)) (ξ^i − 1) =
extLog(ξ^i·ε^c − 1)`. Combine the resummation (`seriesEval_logSeriesAt_of_norm`) with
the factorisation `ξ^i·ε^c − 1 = (ε^c − 1)·(1 + ε^c(ξ^i−1)/(ε^c−1))` and
`extLog_mul`/`extLog_eq_padicLog`. -/
private theorem seriesEval_logSeriesAt_eq_extLog {ε ξ : K} (hεint : IsIntegral ℤ ε) {c i : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ‖ξ ^ i - 1‖ < 1) :
    seriesEval (logSeriesAt p K (ε ^ c)) (ξ ^ i - 1) = extLog p (ξ ^ i * ε ^ c - 1) := by
  set u : K := ε ^ c with hu
  set z : K := ξ ^ i - 1 with hz
  have hune : (u - 1) ≠ 0 := by rw [← norm_pos_iff, hu, hc1]; exact one_pos
  -- `‖u‖ = 1`, `‖w‖ = ‖u z/(u−1)‖ = ‖z‖ < 1`
  have hunorm : ‖u‖ ≤ 1 := by
    calc ‖u‖ = ‖(u - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖u - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by rw [hu, hc1, norm_one, max_self]
  have hwnorm : ‖u * z / (u - 1)‖ < 1 := by
    rw [norm_div, hu, hc1, div_one, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hunorm) hil
  have hwsub : ‖(1 + u * z / (u - 1)) - 1‖ < 1 := by rwa [add_sub_cancel_left]
  -- the factorisation `ξ^i ε^c − 1 = (u − 1)·(1 + u z/(u−1))`
  have hfac : ξ ^ i * ε ^ c - 1 = (u - 1) * (1 + u * z / (u - 1)) := by
    rw [← hu, show ξ ^ i = z + 1 from by rw [hz]; ring]
    field_simp
    ring
  rw [seriesEval_logSeriesAt_of_norm (p := p) hc1 hil, hfac,
    extLog_mul p (extLogDomain_of_integral_norm_one p
      ((hεint.pow c).sub isIntegral_one) (by rw [← hu]; exact hc1))
      (extLogDomain_of_norm_sub_one_lt_one (p := p) hwsub),
    extLog_eq_padicLog_of_norm_lt_one (p := p) hwsub]

omit [CharZero K] in
include hp in
/-- A `±1` sign is invisible to `extLog`: `extLog((−1)^m · x) = extLog x`
(induction via `extLog_neg`). -/
private theorem extLog_neg_one_pow_mul {x : K} (hx : ExtLogDomain p x) (m : ℕ) :
    extLog p ((-1 : K) ^ m * x) = extLog p x := by
  induction m with
  | zero => rw [pow_zero, one_mul]
  | succ k ih =>
    have hdom : ExtLogDomain p ((-1 : K) ^ k * x) :=
      ExtLogDomain.mul p
        (extLogDomain_of_integral_norm_one p ((IsIntegral.neg isIntegral_one).pow k)
          (by rw [norm_pow, norm_neg, norm_one, one_pow])) hx
    rw [pow_succ, show (-1 : K) ^ k * (-1) * x = -((-1) ^ k * x) from by ring,
      extLog_neg p hdom, ih]

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- Reindex a `Fin p`-sum over the powers of a primitive `p`-th root as a sum over
`nthRootsFinset p 1` (`i ↦ ξ^i` is a bijection). -/
private theorem sum_fin_pow_eq_sum_nthRootsFinset {ξ : K} (hξ : IsPrimitiveRoot ξ p)
    (f : K → K) :
    ∑ i : Fin p, f (ξ ^ (i : ℕ)) = ∑ ζ ∈ Polynomial.nthRootsFinset p (1 : K), f ζ := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.sum_nbij (fun i => ξ ^ (i : ℕ))
    (fun i _ => (Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mpr (by
      rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]))
    (fun a _ b _ hab => Fin.ext (hξ.pow_inj a.2 b.2 hab)) (fun ζ hζ => ?_) (fun i _ => rfl)
  -- surjectivity: every `ζ ∈ nthRootsFinset p 1` is `ξ^i` for some `i < p`
  obtain ⟨i, hik, rfl⟩ := hξ.eq_pow_of_pow_eq_one
    ((Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mp hζ)
  exact ⟨⟨i, hik⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩

omit [CharZero K] in
include hp in
/-- T616 step 3 (the `μ_p`-collapse): for a primitive `p`-th root `ξ`, an `‖·‖ = 1`
unit `ε^c` (`ε` integral over `ℤ`) with `‖ξ^i − 1‖ < 1`,
`Σ_{i<p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)`. Uses the product identity
`∏_{i<p}(ξ^i·Y − 1) = (−1)^{p+1}·(Y^p − 1)`
(`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`), `extLog_prod`, and the sign-stripping
`extLog_neg_one_pow_mul`. -/
private theorem sum_extLog_pow_mul_collapse {ε ξ : K} {N : ℕ} (hN0 : 0 < N)
    (hε : IsPrimitiveRoot ε N) (hεint : IsIntegral ℤ ε) (hξ : IsPrimitiveRoot ξ p) {c : ℕ}
    (hc1 : ‖ε ^ c - 1‖ = 1) (hil : ∀ i : Fin p, ‖ξ ^ (i : ℕ) - 1‖ < 1) :
    ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) = extLog p (ε ^ (p * c) - 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- each factor `ξ^i ε^c − 1` is in the extended-log domain
  have hdomζ : ∀ ζ ∈ Polynomial.nthRootsFinset p (1 : K),
      ExtLogDomain p (ζ * ε ^ c - 1) := by
    intro ζ hζmem
    obtain ⟨i, hik, rfl⟩ := hξ.eq_pow_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mp hζmem)
    exact extLogDomain_pow_mul_pow_sub_one hN0 hε hξ hc1 (hil ⟨i, hik⟩)
  -- the `μ_p` product identity: `∏_ζ (ζ·ε^c − 1) = (−1)^p·(1 − ε^{pc})`
  have hprodId : ∏ ζ ∈ Polynomial.nthRootsFinset p (1 : K), (ζ * ε ^ c - 1)
      = (-1 : K) ^ p * (1 - (ε ^ c) ^ p) := by
    rw [show (1 : K) - (ε ^ c) ^ p = (1 : K) ^ p - (ε ^ c) ^ p from by rw [one_pow],
      hξ.pow_sub_pow_eq_prod_sub_mul (x := 1) (y := ε ^ c) hp.out.pos,
      show (-1 : K) ^ p = ∏ _ζ ∈ Polynomial.nthRootsFinset p (1 : K), (-1 : K) from by
        rw [Finset.prod_const, hξ.card_nthRootsFinset],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ζ _ => by ring
  -- `‖ε^{pc} − 1‖ = ‖(ε^c)^p − 1‖ = 1` (product of the norm-one factors `ξ^i ε^c − 1`)
  have hnorm_pc : ‖(ε ^ c) ^ p - 1‖ = 1 := by
    have hnormprod : ‖∏ ζ ∈ Polynomial.nthRootsFinset p (1 : K), (ζ * ε ^ c - 1)‖ = 1 := by
      rw [norm_prod, Finset.prod_eq_one fun ζ hζmem => ?_]
      obtain ⟨i, hik, rfl⟩ := hξ.eq_pow_of_pow_eq_one
        ((Polynomial.mem_nthRootsFinset hp.out.pos (1 : K)).mp hζmem)
      exact norm_pow_mul_pow_sub_one_eq_one hN0 hε hc1 (hil ⟨i, hik⟩)
    rw [hprodId, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      show (1 : K) - (ε ^ c) ^ p = -((ε ^ c) ^ p - 1) from by ring, norm_neg] at hnormprod
    exact hnormprod
  rw [sum_fin_pow_eq_sum_nthRootsFinset hξ (fun ζ => extLog p (ζ * ε ^ c - 1)),
    ← extLog_prod p _ _ hdomζ, hprodId,
    show (-1 : K) ^ p * (1 - (ε ^ c) ^ p) = (-1 : K) ^ (p + 1) * ((ε ^ c) ^ p - 1) from by
      rw [pow_succ]; ring,
    extLog_neg_one_pow_mul (extLogDomain_of_integral_norm_one p
      (((hεint.pow c).pow p).sub isIntegral_one) hnorm_pc),
    ← pow_mul, mul_comm c p]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- T616 step 4 (the `p∣N` primitive-character fiber sum, replan R6.3): for a primitive
`ψ : DirichletCharacter K N` and `M ∣ N` with `ψ` NOT factoring through `M`, the sum of
`ψ` over any residue fibre `{c : ZMod N | c ≡ r mod M}` vanishes. Proof: pick a unit
`v ≡ 1 mod M` with `ψ v ≠ 1` (failure of factoring), and note `c ↦ v·c` permutes the
fibre (it fixes residues mod M), so `S = ψ(v)·S`, forcing `S = 0`. -/
private theorem sum_dirichlet_fiber_eq_zero {N M : ℕ} [NeZero N] (hMN : M ∣ N)
    {ψ : DirichletCharacter K N} (hψ : ¬ ψ.FactorsThrough M) (r : ZMod M) :
    ∑ c ∈ Finset.univ.filter (fun c : ZMod N => ZMod.castHom hMN (ZMod M) c = r), ψ c = 0 := by
  classical
  -- a unit `v ≡ 1 mod M` (i.e. in `ker (unitsMap hMN)`) with `ψ v ≠ 1`
  obtain ⟨v, hvker, hvψ⟩ : ∃ v : (ZMod N)ˣ, ZMod.unitsMap hMN v = 1 ∧ ψ.toUnitHom v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hψ ((DirichletCharacter.factorsThrough_iff_ker_unitsMap hMN).mpr fun v hv => by
      rw [MonoidHom.mem_ker]; exact hcon v (by rwa [MonoidHom.mem_ker] at hv))
  -- `castHom hMN (v : ZMod N) = 1`
  have hvcast : ZMod.castHom hMN (ZMod M) (v : ZMod N) = 1 := by
    have := congrArg (Units.val) hvker
    rwa [ZMod.unitsMap_val, Units.val_one] at this
  -- `ψ (v : ZMod N) ≠ 1`
  have hvψ' : ψ ((v : ZMod N)) ≠ 1 := by
    rw [← MulChar.coe_toUnitHom ψ v, Ne, Units.val_eq_one]; exact hvψ
  -- `castHom hMN (v⁻¹ : ZMod N) = 1` too
  have hvcastinv : ZMod.castHom hMN (ZMod M) ((v⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    have hinv : ZMod.unitsMap hMN v⁻¹ = 1 := by rw [map_inv, hvker, inv_one]
    have := congrArg Units.val hinv
    rwa [ZMod.unitsMap_val, Units.val_one] at this
  set S := ∑ c ∈ Finset.univ.filter (fun c : ZMod N => ZMod.castHom hMN (ZMod M) c = r), ψ c with hS
  -- `c ↦ v·c` permutes the fibre, twisting the sum by `ψ v`
  have hperm : S = ψ ((v : ZMod N)) * S := by
    rw [hS, Finset.mul_sum]
    refine (Finset.sum_nbij' (fun c => (v : ZMod N) * c) (fun c => (v⁻¹ : (ZMod N)ˣ) * c)
      ?_ ?_ ?_ ?_ ?_).symm
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rwa [map_mul, hvcast, one_mul]
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rwa [map_mul, hvcastinv, one_mul]
    · intro c _; rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · intro c _; rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · intro c _; rw [map_mul]
  -- `(1 − ψ v)·S = 0` with `ψ v ≠ 1`
  have : (1 - ψ ((v : ZMod N))) * S = 0 := by rw [sub_mul, one_mul, ← hperm]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hvψ'
  · exact h

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
include hp in
/-- T616 step 4 (the `c ↦ pc` bookkeeping, both cases — replans R6.3): for primitive
`θ` of level `N > 1` and a primitive `N`-th root `ε`,
`Σ_{c<N} θ⁻¹(c)·extLog(ε^{pc} − 1) = θ(p)·Σ_{c<N} θ⁻¹(c)·extLog(ε^c − 1)`. The function
`extLog(ε^a − 1)` is `ε`-cyclic so reindexes over `ZMod N`; for `¬p∣N` the unit `p`
substitutes (`c ↦ pc`, `θ⁻¹(p⁻¹) = θ(p)`); for `p∣N` both sides vanish — `θ(p) = 0`
and the `LHS` groups along the `p`-to-`1` map into fibres killed by
`sum_dirichlet_fiber_eq_zero` (primitivity of `θ⁻¹`). -/
private theorem sum_theta_inv_mul_extLog_pc {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} (hprim : θ.IsPrimitive) {ε : K} (hε : IsPrimitiveRoot ε N) :
    ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ (p * c) - 1)
      = θ ((p : ZMod N)) * ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ c - 1) := by
  classical
  haveI : Fact (1 < N) := ⟨hN⟩
  -- `g a := extLog(ε^{a.val} − 1)` on `ZMod N`; `ε` is cyclic so `ε^k = ε^{(k:ZMod N).val}`
  set g : ZMod N → K := fun a => extLog p (ε ^ a.val - 1) with hgdef
  have hcyc : ∀ k : ℕ, ε ^ k = ε ^ ((k : ZMod N)).val := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k N, pow_add, pow_mul, hε.pow_eq_one, one_pow, one_mul]
    rw [ZMod.val_natCast]
  -- reindex both `range N` sums over `ZMod N`, identifying `extLog(ε^c − 1) = g c`
  have hreindex : ∀ f : ZMod N → K, ∑ c ∈ Finset.range N, f ((c : ZMod N))
      = ∑ a : ZMod N, f a := fun f =>
    Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod N)) (fun a => a.val)
      (fun c _ => Finset.mem_univ _) (fun a _ => Finset.mem_range.mpr (ZMod.val_lt a))
      (fun c hc => ZMod.val_natCast_of_lt (Finset.mem_range.mp hc))
      (fun a _ => ZMod.natCast_zmod_val a) (fun c _ => rfl)
  have hLHS : ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ (p * c) - 1)
      = ∑ a : ZMod N, θ⁻¹ a * g (((p : ℕ) : ZMod N) * a) := by
    rw [← hreindex (fun a => θ⁻¹ a * g (((p : ℕ) : ZMod N) * a))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hgdef]
    simp only
    rw [show ((p : ℕ) : ZMod N) * ((c : ℕ) : ZMod N) = ((p * c : ℕ) : ZMod N) from by
      push_cast; ring]
    rw [← hcyc (p * c)]
  have hRHS : ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ c - 1)
      = ∑ a : ZMod N, θ⁻¹ a * g a := by
    rw [← hreindex (fun a => θ⁻¹ a * g a)]
    exact Finset.sum_congr rfl fun c _ => by rw [hgdef]; simp only; rw [← hcyc c]
  rw [hLHS, hRHS]
  by_cases hpN : (p : ℕ) ∣ N
  · -- `p ∣ N`: both sides vanish
    have hpnu : ¬ IsUnit ((p : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp.out]; exact fun h => h hpN
    rw [θ.map_nonunit hpnu, zero_mul]
    -- group the `a`-sum along the `p`-to-`1` map `a ↦ p·a` (fibres mod `N/p`)
    obtain ⟨M, rfl⟩ := hpN
    have hM0 : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · rw [h, mul_zero] at hN; omega
      · exact h
    haveI : NeZero M := ⟨hM0.ne'⟩
    have hMdvd : M ∣ p * M := dvd_mul_left M p
    -- `θ⁻¹` does not factor through `M = N/p < N` (else conductor ≤ M < N)
    have hnotft : ¬ (θ⁻¹).FactorsThrough M := by
      intro hft
      have hcond : (θ⁻¹).conductor ≤ M :=
        Nat.sInf_le ⟨hft.dvd, hft.χ₀, hft.eq_changeLevel⟩
      rw [DirichletCharacter.conductor_inv, hprim] at hcond
      have hMlt : M < p * M := by nlinarith [hp.out.one_lt, hM0]
      omega
    -- `p·a` depends only on `a mod M` (the `p`-multiple kills the `M`-difference)
    have hpconst : ∀ a : ZMod (p * M), ((p : ℕ) : ZMod (p * M)) * a
        = ((p : ℕ) : ZMod (p * M)) * ((ZMod.castHom hMdvd (ZMod M) a).val : ZMod (p * M)) := by
      intro a
      rw [show ((p : ℕ) : ZMod (p * M)) * a = ((p * a.val : ℕ) : ZMod (p * M)) from by
          rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id],
        show ((p : ℕ) : ZMod (p * M)) * ((ZMod.castHom hMdvd (ZMod M) a).val : ZMod (p * M))
          = ((p * (ZMod.castHom hMdvd (ZMod M) a).val : ℕ) : ZMod (p * M)) from by
          rw [Nat.cast_mul],
        ZMod.natCast_eq_natCast_iff]
      -- `p·a.val ≡ p·(cast_M a).val [MOD p·M]` since `a.val ≡ (cast_M a).val [MOD M]`
      have hmod : a.val ≡ (ZMod.castHom hMdvd (ZMod M) a).val [MOD M] := by
        have hval : (ZMod.castHom hMdvd (ZMod M) a).val = a.val % M := by
          rw [ZMod.castHom_apply, ← ZMod.natCast_val a, ZMod.val_natCast]
        rw [hval]; exact (Nat.mod_modEq a.val M).symm
      exact hmod.mul_left' p
    -- `g (p·a)` is constant on each fibre `{a : cast_M a = r}`; sum over fibres of `θ⁻¹`
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun a : ZMod (p * M) => ZMod.castHom hMdvd (ZMod M) a)
      (fun a _ => Finset.mem_univ _)]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [show (∑ a ∈ Finset.univ.filter (fun a => ZMod.castHom hMdvd (ZMod M) a = r),
          θ⁻¹ a * g (((p : ℕ) : ZMod (p * M)) * a))
        = (∑ a ∈ Finset.univ.filter (fun a => ZMod.castHom hMdvd (ZMod M) a = r), θ⁻¹ a)
          * g (((p : ℕ) : ZMod (p * M)) * ((r.val : ZMod (p * M)))) from ?_,
      sum_dirichlet_fiber_eq_zero hMdvd hnotft r, zero_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [hpconst a, ha]
  · -- `¬p∣N`: `p` is a unit; substitute `a ↦ p·a`
    obtain ⟨u, hpu⟩ : IsUnit ((p : ℕ) : ZMod N) :=
      (ZMod.isUnit_iff_coprime p N).mpr ((hp.out.coprime_iff_not_dvd).mpr hpN)
    have hθθinv : θ ((p : ℕ) : ZMod N) * θ⁻¹ ((p : ℕ) : ZMod N) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel θ, MulChar.one_apply (hpu ▸ u.isUnit)]
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun a => ((p : ℕ) : ZMod N) * a)
      (fun a => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * a) (fun a _ => Finset.mem_univ _)
      (fun a _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a _; rw [← hpu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · intro a _; rw [← hpu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · intro a _
      -- `f a = θ⁻¹(a)·g(p·a)` equals `g'(p·a) = θ(p)·(θ⁻¹(p·a)·g(p·a))`
      rw [map_mul, ← mul_assoc, ← mul_assoc, hθθinv, one_mul]

omit [CharZero K] in
/-- P6-p7' (the evaluated trace, ψ-free form — replan R6.6):
`Σ_{i<p} F̃(ξ^i−1) = θ(p)·F̃(0)` — for `n = 0` by the `c ↦ pc` automorphism
and the `μ_p`-collapse `Σ_ξ extLog(ξw−1) = extLog(w^p−1)`; for `n ≥ 1`
both sides vanish (`θ(p) = 0`; primitive-character fiber sums —
replan R6.3).

**Statement-fix (replan R6.6, recorded 2026-06-11; coprime-guard refinement
2026-06-12 in `b2_log.jsonl`):** the frozen `hdom : ∀ c, ¬N∣c → ExtLogDomain
(ε^c − 1)` is too weak — the per-term identity needs the SHIFTED arguments
`ξ^i·ε^c − 1` to lie in the extended-log domain, which does not follow from
`hdom` in the ramified case (`ε^c` reducing to `1`). It is replaced by the
norm-one hypothesis `hnorm`, guarded by `IsUnit (c : ZMod N)` (equivalently `c`
coprime to `N`): the non-unit-`c` terms vanish (`θ⁻¹(c) = 0`), and for the
unit `c` every shifted domain follows (`‖ξ^i ε^c − 1‖ = 1` by ultrametric
isoceles + roots-of-unity integrality, then `extLogDomain_of_integral_norm_one`).
The earlier `¬N∣c`-guard is FALSE for `c = D·j` (`ε^{Dj}` a nontrivial `p`-power
root, norm `< 1`), so undischargeable in `LpFunction_one`; the coprime-guarded
form IS discharged there (T612 `norm_one_sub_pow_eq_one` after stripping the
`p`-part), preserving provability.

The analytic prerequisite (boundary `p`-adic-log multiplicativity
`extLog (1 + w) = padicLog (1 + w)` for `‖w‖ < 1`, since the arguments `ξ^i − 1`,
`i ≠ 0`, sit on the exp-ball boundary `‖·‖^{p−1} = p⁻¹`) is supplied by the T618
layer (`extLog_eq_padicLog_of_norm_lt_one` / `padicLog_pow_p_of_norm_lt_one`,
above). The proof assembles: the per-term identity
`seriesEval (logSeriesAt (ε^c)) (ξ^i − 1) = extLog(ξ^i·ε^c − 1)`
(`seriesEval_logSeriesAt_eq_extLog`); the `μ_p`-collapse
`Σ_{i<p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)` (`sum_extLog_pow_mul_collapse`);
and the `c ↦ pc` bookkeeping `Σ_c θ⁻¹(c)·extLog(ε^{pc} − 1) = θ(p)·Σ_c θ⁻¹(c)·
extLog(ε^c − 1)` (`sum_theta_inv_mul_extLog_pc`: automorphism for `¬p∣N`,
primitive-character fiber sums for `p∣N`). -/
theorem sum_seriesEval_Ftilde {N : ℕ} [NeZero N] (hN : 1 < N)
    {θ : DirichletCharacter K N} (hprim : θ.IsPrimitive) (_hθ1 : θ ≠ 1)
    {ε : K} (hε : IsPrimitiveRoot ε N) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p)
    (hnorm : ∀ c ∈ Finset.range N, IsUnit ((c : ZMod N)) → ‖ε ^ c - 1‖ = 1) :
    ∑ i : Fin p, seriesEval (Ftilde p K θ hε) (ξ ^ (i : ℕ) - 1)
      = θ ((p : ZMod N)) * PowerSeries.constantCoeff (Ftilde p K θ hε) := by
  haveI : Fact (1 < N) := ⟨hN⟩
  have hεint : IsIntegral ℤ ε := isIntegral_of_pow_eq_one (NeZero.pos N) hε.pow_eq_one
  -- `θ⁻¹ c = 0` for non-unit `c` (the only contributing terms are the coprime ones)
  have hθ0 : ∀ c ∈ Finset.range N, ¬ IsUnit ((c : ZMod N)) → θ⁻¹ ((c : ZMod N)) = 0 :=
    fun c _ hcu => MulChar.map_nonunit _ hcu
  -- `‖ξ^i − 1‖ < 1` for every `i : Fin p`
  have hzlt : ∀ i : Fin p, ‖ξ ^ (i : ℕ) - 1‖ < 1 := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · rw [hi0, pow_zero, sub_self, norm_zero]; exact one_pos
    · have hcop : (i : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hipos hdvd) (by omega : ¬ p ≤ (i : ℕ)))
      exact (by rw [pow_one] at *; exact hξ.pow_of_coprime (i : ℕ) hcop :
        IsPrimitiveRoot (ξ ^ (i : ℕ)) (p ^ 1)).norm_sub_one_lt (p := p)
  -- Step A: `seriesEval F̃ (ξ^i − 1) = −Σ_c θ⁻¹(c)·extLog(ξ^i·ε^c − 1)`
  have hstepA : ∀ i : Fin p, seriesEval (Ftilde p K θ hε) (ξ ^ (i : ℕ) - 1)
      = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by
    intro i
    rw [Ftilde, seriesEval_neg]
    refine congrArg Neg.neg ?_
    -- expand `seriesEval (Σ_c C(θ⁻¹c)·logSeriesAt) (ξ^i−1) = Σ_c θ⁻¹(c)·seriesEval(logSeriesAt)`
    rw [seriesEval,
      show (∑' n : ℕ, PowerSeries.coeff n (∑ c ∈ Finset.range N,
            PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)) * (ξ ^ (i : ℕ) - 1) ^ n)
        = ∑' n : ℕ, ∑ c ∈ Finset.range N, PowerSeries.coeff n
            (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)) * (ξ ^ (i : ℕ) - 1) ^ n
        from tsum_congr fun n => by rw [map_sum, Finset.sum_mul]]
    rw [Summable.tsum_finsetSum fun c hc => ?_]
    · refine Finset.sum_congr rfl fun c hc => ?_
      by_cases hcu : IsUnit ((c : ZMod N))
      · rw [show (∑' n : ℕ, PowerSeries.coeff n
              (PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c))
                * (ξ ^ (i : ℕ) - 1) ^ n)
            = θ⁻¹ ((c : ZMod N)) * seriesEval (logSeriesAt p K (ε ^ c)) (ξ ^ (i : ℕ) - 1) from by
          rw [seriesEval, ← (summable_seriesEval_logSeriesAt (p := p) (hnorm c hc hcu)
            (hzlt i)).tsum_mul_left]
          exact tsum_congr fun n => by rw [PowerSeries.coeff_C_mul, mul_assoc],
          seriesEval_logSeriesAt_eq_extLog (p := p) hεint (hnorm c hc hcu) (hzlt i)]
      · rw [hθ0 c hc hcu]
        simp only [zero_mul, map_zero, tsum_zero]
    · -- summability of each `c`-term at `ξ^i − 1`
      by_cases hcu : IsUnit ((c : ZMod N))
      · exact ((summable_seriesEval_logSeriesAt (p := p) (hnorm c hc hcu)
          (hzlt i)).mul_left (θ⁻¹ ((c : ZMod N)))).congr fun n => by
            rw [PowerSeries.coeff_C_mul, mul_assoc]
      · refine (summable_of_ne_finset_zero (s := ∅) fun n _ => ?_)
        rw [PowerSeries.coeff_C_mul, hθ0 c hc hcu, zero_mul, zero_mul]
  -- Step B: sum Step A over `i`, swap, apply the `μ_p`-collapse per `c`
  rw [Finset.sum_congr rfl fun i _ => hstepA i]
  -- `Σ_i (−Σ_c ...) = −Σ_c (Σ_i ...)`  then the `μ_p`-collapse on the inner `i`-sum
  rw [show (∑ i : Fin p, -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
            * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1))
        = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
            * ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) from by
      calc (∑ i : Fin p, -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
              * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1))
          = -∑ i : Fin p, ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
              * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by rw [← Finset.sum_neg_distrib]
        _ = -∑ c ∈ Finset.range N, ∑ i : Fin p, θ⁻¹ ((c : ZMod N))
              * extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by rw [Finset.sum_comm]
        _ = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
              * ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1) := by
            refine congrArg Neg.neg (Finset.sum_congr rfl fun c _ => ?_)
            rw [Finset.mul_sum]]
  -- collapse `Σ_i extLog(ξ^i ε^c − 1) = extLog(ε^{pc} − 1)` per contributing `c`
  rw [show (∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N))
            * ∑ i : Fin p, extLog p (ξ ^ (i : ℕ) * ε ^ c - 1))
        = ∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ (p * c) - 1) from
    Finset.sum_congr rfl fun c hc => by
      by_cases hcu : IsUnit ((c : ZMod N))
      · rw [sum_extLog_pow_mul_collapse (p := p) (NeZero.pos N) hε hεint hξ
          (hnorm c hc hcu) hzlt]
      · rw [hθ0 c hc hcu, zero_mul, zero_mul]]
  -- the `c ↦ pc` bookkeeping + the constant-coefficient identity
  rw [sum_theta_inv_mul_extLog_pc (p := p) hN hprim hε,
    show PowerSeries.constantCoeff (Ftilde p K θ hε)
        = -∑ c ∈ Finset.range N, θ⁻¹ ((c : ZMod N)) * extLog p (ε ^ c - 1) from ?_]
  · ring
  · -- `constantCoeff F̃ = −Σ_c θ⁻¹(c)·extLog(ε^c − 1)` (coeff 0 of `logSeriesAt = extLog(ε^c−1)`)
    rw [Ftilde, map_neg, map_sum, neg_inj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, PowerSeries.constantCoeff_C, logSeriesAt,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]

/-! #### The G-cleared `hGtwist` closed form (the T617 step-3 key)

`mahlerK (twist χ̃ μ̃_η) = C(G(χ⁻¹)⁻¹)·(−Σ_{c<N} θ⁻¹(c)·((1+X)C(ε^c) − 1)⁻¹)`,
the explicit Mahler transform of the twisted cleared measure in the form
`one_add_mul_derivative_Ftilde` consumes. Built by smearing the χ-twist into
`ε_{p^n}^b`-lines (`mahler_twist_formula` + `mahlerTransform_charTwist_muEtaCleared`),
mapping to `K`, and CRT-collapsing the `(b,c)` double sum to a single `range N`
sum at the split root `ε = ζ·ε_{p^n}` (decomposition R6 P6-p8 step 3). -/

omit [CompleteSpace K] [CharZero K] in
/-- `toFieldChar` commutes with `changeLevel` (both are `MulChar`-constructions
agreeing on units via `changeLevel_eq_cast_of_dvd`). -/
private theorem toFieldChar_changeLevel {D N : ℕ} [NeZero N] (h : D ∣ N)
    (η : DirichletCharacter (integerRing K) D) :
    toFieldChar (DirichletCharacter.changeLevel h η)
      = DirichletCharacter.changeLevel h (toFieldChar η) := by
  ext u
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd _ h u]
  change ((DirichletCharacter.changeLevel h η ((u : ZMod N)) : integerRing K) : K) = _
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd η h u]
  rfl

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The CRT collapse (decomposition R6 P6-p8 step 3c): the `η⊗χ` double sum over
`range p^n × range D` of `θ⁻¹`-weighted inverse-denominators at the product roots
`ζ^c·ε_{p^n}^b` reindexes — along `ZMod (D·p^n) ≃ ZMod D × ZMod (p^n)`
(`ZMod.chineseRemainder`) — to the single `range N`-sum at the glued root
`ε = ζ·ε_{p^n}`. The character factorises (`θ⁻¹ = changeLevel η⁻¹·changeLevel χ⁻¹`,
both `MulChar.map_nonunit`-killed off the unit CRT dichotomy) and the root
period-splits (`ζ` is `D`-periodic, `ε_{p^n}` is `p^n`-periodic). -/
private theorem crt_collapse {D : ℕ} [NeZero D] {n : ℕ} (hco : Nat.Coprime D (p ^ n))
    {ηK : DirichletCharacter K D} {χK : DirichletCharacter K (p ^ n)}
    {θK : DirichletCharacter K (D * p ^ n)}
    (hθ : θK = DirichletCharacter.changeLevel (Dvd.intro _ rfl) ηK
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χK)
    {ζK εpK : K} (hζK : IsPrimitiveRoot ζK D) (hεpK : IsPrimitiveRoot εpK (p ^ n)) :
    (∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
        PowerSeries.C (χK⁻¹ ((b : ℕ) : ZMod (p ^ n)) * ηK⁻¹ ((c : ℕ) : ZMod D))
          * Ring.inverse (PowerSeries.C (ζK ^ c * εpK ^ b) * (1 + PowerSeries.X) - 1))
      = ∑ j ∈ Finset.range (D * p ^ n),
          PowerSeries.C (θK⁻¹ ((j : ℕ) : ZMod (D * p ^ n)))
            * Ring.inverse (PowerSeries.C ((ζK * εpK) ^ j) * (1 + PowerSeries.X) - 1) := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (D * p ^ n) := ⟨Nat.mul_ne_zero (NeZero.ne D) (pow_ne_zero _ hp.out.ne_zero)⟩
  set e := ZMod.chineseRemainder hco
  set F : ZMod (p ^ n) → ZMod D → PowerSeries K := fun bb cc =>
    PowerSeries.C (χK⁻¹ bb * ηK⁻¹ cc)
      * Ring.inverse (PowerSeries.C (ζK ^ cc.val * εpK ^ bb.val) * (1 + PowerSeries.X) - 1)
    with hF
  have hreindex : ∀ {M : ℕ} [NeZero M] (f : ZMod M → PowerSeries K),
      ∑ c ∈ Finset.range M, f ((c : ℕ) : ZMod M) = ∑ a : ZMod M, f a := fun {M} _ f =>
    Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod M)) (fun a => a.val)
      (fun _ _ => Finset.mem_univ _) (fun a _ => Finset.mem_range.mpr (ZMod.val_lt a))
      (fun c hc => ZMod.val_natCast_of_lt (Finset.mem_range.mp hc))
      (fun a _ => ZMod.natCast_zmod_val a) (fun _ _ => rfl)
  have hcycD : ∀ c : ℕ, ζK ^ c = ζK ^ (((c : ℕ) : ZMod D)).val := fun c => by
    conv_lhs => rw [← Nat.div_add_mod c D, pow_add, pow_mul, hζK.pow_eq_one, one_pow, one_mul]
    rw [ZMod.val_natCast]
  have hcycP : ∀ b : ℕ, εpK ^ b = εpK ^ (((b : ℕ) : ZMod (p ^ n))).val := fun b => by
    conv_lhs => rw [← Nat.div_add_mod b (p ^ n), pow_add, pow_mul, hεpK.pow_eq_one, one_pow,
      one_mul]
    rw [ZMod.val_natCast]
  have hNpow : (ζK * εpK) ^ (D * p ^ n) = 1 := by
    rw [mul_pow, pow_mul, hζK.pow_eq_one, one_pow, one_mul, mul_comm D (p ^ n), pow_mul,
      hεpK.pow_eq_one, one_pow]
  have hcycN : ∀ j : ℕ, (ζK * εpK) ^ j = (ζK * εpK) ^ (((j : ℕ) : ZMod (D * p ^ n))).val :=
    fun j => by
      conv_lhs => rw [← Nat.div_add_mod j (D * p ^ n), pow_add, pow_mul, hNpow, one_pow, one_mul]
      rw [ZMod.val_natCast]
  have hLHS : (∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
        PowerSeries.C (χK⁻¹ ((b : ℕ) : ZMod (p ^ n)) * ηK⁻¹ ((c : ℕ) : ZMod D))
          * Ring.inverse (PowerSeries.C (ζK ^ c * εpK ^ b) * (1 + PowerSeries.X) - 1))
      = ∑ bb : ZMod (p ^ n), ∑ cc : ZMod D, F bb cc := by
    rw [← hreindex (fun bb => ∑ cc : ZMod D, F bb cc)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hreindex (fun cc => F ((b : ℕ) : ZMod (p ^ n)) cc)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hF]; simp only
    rw [← hcycD c, ← hcycP b]
  have hpera : ∀ a : ZMod (D * p ^ n),
      PowerSeries.C (θK⁻¹ a)
          * Ring.inverse (PowerSeries.C ((ζK * εpK) ^ a.val) * (1 + PowerSeries.X) - 1)
        = F (ZMod.cast a : ZMod (p ^ n)) (ZMod.cast a : ZMod D) := by
    intro a
    have hfst : (e a).1 = (ZMod.cast a : ZMod D) := Prod.fst_zmod_cast a
    have hsnd : (e a).2 = (ZMod.cast a : ZMod (p ^ n)) := Prod.snd_zmod_cast a
    have hvalD : (ZMod.cast a : ZMod D).val = a.val % D := by
      rw [ZMod.cast_eq_val, ZMod.val_natCast]
    have hvalP : (ZMod.cast a : ZMod (p ^ n)).val = a.val % (p ^ n) := by
      rw [ZMod.cast_eq_val, ZMod.val_natCast]
    have hcD : ζK ^ a.val = ζK ^ (a.val % D) := by
      conv_lhs => rw [← Nat.div_add_mod a.val D, pow_add, pow_mul, hζK.pow_eq_one, one_pow, one_mul]
    have hcP : εpK ^ a.val = εpK ^ (a.val % (p ^ n)) := by
      conv_lhs => rw [← Nat.div_add_mod a.val (p ^ n), pow_add, pow_mul, hεpK.pow_eq_one, one_pow,
        one_mul]
    have hθinv : θK⁻¹ a = χK⁻¹ (ZMod.cast a : ZMod (p ^ n)) * ηK⁻¹ (ZMod.cast a : ZMod D) := by
      have h1 : θK⁻¹ = DirichletCharacter.changeLevel (Dvd.intro _ rfl) ηK⁻¹
          * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χK⁻¹ := by
        rw [hθ, mul_inv]; congr 1 <;> exact (map_inv _ _).symm
      rw [h1, MulChar.mul_apply, mul_comm]
      by_cases ha : IsUnit a
      · obtain ⟨u, rfl⟩ := ha
        rw [DirichletCharacter.changeLevel_eq_cast_of_dvd,
          DirichletCharacter.changeLevel_eq_cast_of_dvd]
      · rw [(DirichletCharacter.changeLevel (Dvd.intro _ rfl) ηK⁻¹).map_nonunit ha,
          (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χK⁻¹).map_nonunit ha, zero_mul]
        have hunit : ¬ (IsUnit (ZMod.cast a : ZMod D) ∧ IsUnit (ZMod.cast a : ZMod (p ^ n))) := by
          rw [← hfst, ← hsnd, ← Prod.isUnit_iff, MulEquiv.isUnit_map (f := e) (x := a)]
          exact ha
        rw [not_and_or] at hunit
        rcases hunit with h | h
        · rw [ηK⁻¹.map_nonunit h, mul_zero]
        · rw [χK⁻¹.map_nonunit h, zero_mul]
    rw [hF]; simp only
    rw [hθinv, mul_pow, hcD, hcP, hvalD, hvalP]
  have hRHS : (∑ j ∈ Finset.range (D * p ^ n),
          PowerSeries.C (θK⁻¹ ((j : ℕ) : ZMod (D * p ^ n)))
            * Ring.inverse (PowerSeries.C ((ζK * εpK) ^ j) * (1 + PowerSeries.X) - 1))
      = ∑ a : ZMod (D * p ^ n), PowerSeries.C (θK⁻¹ a)
          * Ring.inverse (PowerSeries.C ((ζK * εpK) ^ a.val) * (1 + PowerSeries.X) - 1) := by
    rw [← hreindex (fun a => PowerSeries.C (θK⁻¹ a)
        * Ring.inverse (PowerSeries.C ((ζK * εpK) ^ a.val) * (1 + PowerSeries.X) - 1))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcycN j]
  rw [hLHS, hRHS, Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hpera a,
    show (∑ a : ZMod (D * p ^ n), F (ZMod.cast a : ZMod (p ^ n)) (ZMod.cast a : ZMod D))
          = ∑ a : ZMod (D * p ^ n),
              (fun pr : ZMod D × ZMod (p ^ n) => F pr.2 pr.1) (e.toEquiv a) from
        Finset.sum_congr rfl fun a _ => by
          change F (ZMod.cast a : ZMod (p ^ n)) (ZMod.cast a : ZMod D) = F (e a).2 (e a).1
          congr 1
          · exact (Prod.snd_zmod_cast a).symm
          · exact (Prod.fst_zmod_cast a).symm,
    Equiv.sum_comp e.toEquiv (fun pr : ZMod D × ZMod (p ^ n) => F pr.2 pr.1),
    ← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]

/-- **RJW Theorem 6.1(ii)** (Leopoldt; `s=1 theorem`(ii), TeX 1992–1995):
"We have `L_p(θ,1) = −(1 − θ(p)p⁻¹)·G(θ⁻¹)⁻¹·
Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)`." Stated for tame conductor `D > 1`
(replan R6.4; the §5.2 standing hypotheses), with `log_p` the extended
logarithm `extLog` and the Gauss factor through the §5 clearing plus the
coprime factorisation (C6-c4).

**Statement-fix (replan R6 step 3a, recorded 2026-06-12 in `b2_log.jsonl`):**
the §6 root `ε` is tied to the §5 split data via `{εp} (hεp) (hsplit : ε = ζ·εp)`
(RJW's `ε_N` is any primitive `N`-th root; the split form `ζ·ε_{p^n}` realises it
through the tame/wild factors). This is what enables the CRT Gauss-product split
`G(θ⁻¹) = G(η⁻¹)·G(χ⁻¹)` (`gaussSum_mul_coprime`) and the `hGtwist` closed form. -/
theorem LpFunction_one {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (hχ : χ.IsPrimitive)
    {θK : DirichletCharacter K (D * p ^ n)} (hθ1 : θK ≠ 1)
    (hθK : θK = toFieldChar (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    (hprim : θK.IsPrimitive)
    {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n))
    {εp : integerRing K} (hεp : IsPrimitiveRoot εp (p ^ n))
    (hsplit : ε = ((ζ : K)) * ((εp : K))) {ξ : K}
    (hξ : IsPrimitiveRoot ξ p) :
    LpFunction p K η hζ hD χ 1
      = -(1 - θK ((p : ZMod (D * p ^ n))) * (p : K)⁻¹)
          * (gaussSum θK⁻¹ (AddChar.zmodChar (D * p ^ n) hε.pow_eq_one))⁻¹
        * ∑ c ∈ Finset.range (D * p ^ n),
            θK⁻¹ ((c : ZMod (D * p ^ n))) * extLog p (1 - ε ^ c) := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (D * p ^ n) := ⟨Nat.mul_ne_zero (NeZero.ne D) (pow_ne_zero _ hp.out.ne_zero)⟩
  have hN : 1 < D * p ^ n := lt_of_lt_of_le hD1 (Nat.le_mul_of_pos_right D (pow_pos hp.out.pos n))
  haveI : Fact (1 < D) := ⟨hD1⟩
  -- coprimality and the K-side roots/characters
  have hco : Nat.Coprime D (p ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((hp.out.coprime_iff_not_dvd).mpr hD))
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  have hεpK : IsPrimitiveRoot ((εp : K)) (p ^ n) :=
    hεp.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  -- `θK = changeLevel(η_K)·changeLevel(χ_K)` (the K-side product factorisation)
  have hθKfac : θK = DirichletCharacter.changeLevel (Dvd.intro _ rfl) (toFieldChar η)
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) (toFieldChar χ) := by
    rw [hθK, show toFieldChar (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
          * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)
        = toFieldChar (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
          * toFieldChar (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ) from by
        ext x; simp [toFieldChar, MulChar.ringHomComp],
      toFieldChar_changeLevel, toFieldChar_changeLevel]
  -- the level-`p^n` Gauss unit `G_χ` (over `integerRing K`), and its `K`-coercion `GχK`
  set GχR : integerRing K := gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hεp.pow_eq_one) with hGχR
  set GχK : K := ((GχR : integerRing K) : K) with hGχK
  have hGχKne : GχK ≠ 0 := by
    rw [hGχK, hGχR, coe_gaussSum_zmodChar χ hεp hεpK]
    exact gaussSum_inv_ne_zero
      ((DirichletCharacter.isPrimitive_ringHomComp_iff χ fun _ _ h => Subtype.ext h).mpr hχ) hεpK
  -- the level-`D` Gauss unit `G_η` (over `integerRing K`), and `GηK`
  set GηK : K := ((gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one) : integerRing K) : K) with hGηK
  have hGηKne : GηK ≠ 0 := by
    rw [hGηK]
    have hu := gaussSum_isUnit_of_coprime hη hζ hD
    exact fun h => hu.ne_zero (Subtype.coe_injective (by simpa using h))
  -- STEP 3a: the integerRing-level closed form of the `G(χ⁻¹)`-smeared twist
  have hcrt : GχR • mahlerTransform p K
        (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
      = -∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
          PowerSeries.C (χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) * η⁻¹ ((c : ℕ) : ZMod D))
            * Ring.inverse (PowerSeries.C (ζ ^ c * εp ^ b) * (1 + PowerSeries.X) - 1) := by
    have h508 := mahler_twist_formula hχ hεp (muEtaCleared p K η hζ hD)
    have hsmul := congrArg (mahlerTransformₗ p K) h508
    rw [map_smul] at hsmul
    rw [show (mahlerTransformₗ p K) (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
        = mahlerTransform p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)) from rfl]
      at hsmul
    rw [hsmul, map_sum,
      show (∑ b ∈ Finset.range (p ^ n), (mahlerTransformₗ p K) (χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) •
            twist p K (charCM (εp ^ b - 1) (tendsto_pow_pow_sub_one hεp b))
              (muEtaCleared p K η hζ hD)))
          = ∑ b ∈ Finset.range (p ^ n), χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) •
              mahlerTransform p K (twist p K (charCM (εp ^ b - 1) (tendsto_pow_pow_sub_one hεp b))
                (muEtaCleared p K η hζ hD)) from
        Finset.sum_congr rfl fun b _ => by rw [map_smul]; rfl,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mahlerTransform_charTwist_muEtaCleared η hζ hD hεp b, smul_neg, Finset.smul_sum]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun c _ => ?_)
    rw [PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  -- STEP 3b: map to `K` and CRT-collapse to the single `range N` sum at `ε = ζ·εp`
  have hGtwistK : PowerSeries.C GχK
        * mahlerK p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
      = -∑ c ∈ Finset.range (D * p ^ n),
          PowerSeries.C (θK⁻¹ ((c : ZMod (D * p ^ n))))
            * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C (ε ^ c) - 1) := by
    have hmap := congrArg (PowerSeries.map (integerRing K).subtype) hcrt
    rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, Subring.coe_subtype,
      show PowerSeries.map (integerRing K).subtype
          (mahlerTransform p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))
        = mahlerK p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)) from rfl,
      map_neg, map_sum] at hmap
    rw [hGχK, hGχR, hmap]
    rw [show (-∑ b ∈ Finset.range (p ^ n),
            PowerSeries.map (integerRing K).subtype (∑ c ∈ Finset.range D,
              PowerSeries.C (χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) * η⁻¹ ((c : ℕ) : ZMod D))
                * Ring.inverse (PowerSeries.C (ζ ^ c * εp ^ b) * (1 + PowerSeries.X) - 1)))
          = -∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
              PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
                  * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
                * Ring.inverse (PowerSeries.C ((ζ : K) ^ c * (εp : K) ^ b)
                    * (1 + PowerSeries.X) - 1) from by
        refine congrArg Neg.neg (Finset.sum_congr rfl fun b _ => ?_)
        rw [map_sum]
        refine Finset.sum_congr rfl fun c hcr => ?_
        by_cases hc0 : c = 0
        · subst hc0
          rw [map_mul, PowerSeries.map_C, Subring.coe_subtype,
            show ((χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) * η⁻¹ ((0 : ℕ) : ZMod D) : integerRing K) : K) = 0
              from by
                rw [show ((0 : ℕ) : ZMod D) = 0 from Nat.cast_zero, η⁻¹.map_nonunit not_isUnit_zero,
                  mul_zero]; rfl,
            show (toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
                * (toFieldChar η)⁻¹ ((0 : ℕ) : ZMod D) = 0 from by
              rw [show ((0 : ℕ) : ZMod D) = 0 from Nat.cast_zero,
                (toFieldChar η)⁻¹.map_nonunit not_isUnit_zero, mul_zero]]
          simp only [map_zero, zero_mul]
        · have hcd : ¬ D ∣ c := fun h => hc0 (Nat.eq_zero_of_dvd_of_lt h (Finset.mem_range.mp hcr))
          have hwlt : ‖((εp ^ b : integerRing K) : K) - 1‖ < 1 := by
            simpa using norm_pow_sub_one_lt_one hεp b
          rw [map_mul, PowerSeries.map_C, Subring.coe_subtype,
            map_ring_inverse_of_isUnit _ (isUnit_root_mul_pow_one_add_X_sub_one hζ hD hcd hwlt),
            show ((χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) * η⁻¹ ((c : ℕ) : ZMod D) : integerRing K) : K)
                = (toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
                  * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D) from by
              push_cast
              rw [show (toFieldChar χ)⁻¹ = toFieldChar χ⁻¹ from MulChar.ringHomComp_inv χ _,
                show (toFieldChar η)⁻¹ = toFieldChar η⁻¹ from MulChar.ringHomComp_inv η _]
              rfl]
          congr 2
          simp only [map_sub, map_mul, map_add, map_one, PowerSeries.map_X, PowerSeries.map_C,
            Subring.coe_subtype, SubmonoidClass.coe_pow]]
    rw [crt_collapse hco hθKfac hζK hεpK]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun c _ => ?_)
    rw [hsplit, mul_comm (1 + PowerSeries.X) (PowerSeries.C (((ζ : K) * (εp : K)) ^ c))]
  -- STEP 3c: divide out `C GχK` to obtain the `hGtwist` shape (T615's hypothesis)
  have hGtwist : mahlerK p K (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
      = PowerSeries.C GχK⁻¹ * (-∑ c ∈ Finset.range (D * p ^ n),
          PowerSeries.C (θK⁻¹ ((c : ZMod (D * p ^ n))))
            * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C (ε ^ c) - 1)) := by
    rw [← hGtwistK, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hGχKne, map_one, one_mul]
  -- the norm-one discharge (the coprime-guarded `hnorm`) for T615 and T616
  have hnorm : ∀ c ∈ Finset.range (D * p ^ n), IsUnit ((c : ZMod (D * p ^ n))) →
      ‖ε ^ c - 1‖ = 1 := fun c _ hcu => norm_pow_sub_one_eq_one_of_unit hD1 hD hε hcu
  -- STEP 1: the cleared mass `(p)·𝓐_ρ(0)·G_χ = (p)·F̃(0) − Σ_i F̃(ξ^i−1)`  (T615)
  have hT615 := p_mul_constantCoeff_mahlerK_rhoTheta hD1 hη hζ hD hχ hN hθ1 hθK hε hξ
    hnorm hGχKne.isUnit hGtwist
  -- STEP 2: the evaluated trace `Σ_i F̃(ξ^i−1) = θK(p)·F̃(0)`  (T616)
  have hT616 := sum_seriesEval_Ftilde hN hprim hθ1 hε hξ hnorm
  -- the constant coefficient of `F̃` (sign-flipped to RJW's `1 − ε^c`)
  have hF0 : PowerSeries.constantCoeff (Ftilde p K θK hε)
      = -∑ c ∈ Finset.range (D * p ^ n),
          θK⁻¹ ((c : ZMod (D * p ^ n))) * extLog p (1 - ε ^ c) := by
    rw [Ftilde, map_neg, map_sum, neg_inj]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [map_mul, PowerSeries.constantCoeff_C, logSeriesAt,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]
    by_cases hcu : IsUnit ((c : ZMod (D * p ^ n)))
    · -- contributing term: `extLog(ε^c − 1) = extLog(1 − ε^c)` (a sign, `extLog_neg`)
      have hc1 : ‖ε ^ c - 1‖ = 1 := hnorm c hc hcu
      have hdom : ExtLogDomain p (ε ^ c - 1) :=
        extLogDomain_of_integral_norm_one p
          ((isIntegral_of_pow_eq_one (NeZero.pos (D * p ^ n)) hε.pow_eq_one).pow c |>.sub
            isIntegral_one) hc1
      rw [show (1 : K) - ε ^ c = -(ε ^ c - 1) from by ring, extLog_neg p hdom]
    · rw [θK⁻¹.map_nonunit hcu, zero_mul, zero_mul]
  -- STEP 1 (the mass identity): `L_p(θ,1) = G_η⁻¹·𝓐_ρ(0)`
  have hmass : LpFunction p K η hζ hD χ 1 = GηK⁻¹
      * PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ)) := by
    rw [show LpFunction p K η hζ hD χ 1
          = ((gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one) : integerRing K) : K)⁻¹
            * ((zetaEtaCleared p K η hζ hD
                (χ.toContinuousMapZp.comp (PadicMeasure.unitsValCM p) * anglePowCM p K (1 - 1))
                  : integerRing K) : K) from rfl,
      zetaEtaCleared_one_eq_rhoTheta_mass hζ hD,
      show ((PowerSeries.constantCoeff (mahlerTransform p K (rhoTheta p K η hζ hD χ))
          : integerRing K) : K)
        = PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ)) from by
        rw [mahlerK, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
        rfl, ← hGηK]
  -- the headline Gauss sum factors at the split root: `G = G_η·G_χ`
  have hGprod : gaussSum θK⁻¹ (AddChar.zmodChar (D * p ^ n) hε.pow_eq_one) = GηK * GχK := by
    rw [hGηK, hGχK, hGχR]
    have hgsplit : gaussSum θK⁻¹ (AddChar.zmodChar (D * p ^ n) hε.pow_eq_one)
        = gaussSum θK⁻¹ (AddChar.zmodChar (D * p ^ n)
            (show ((ζ : K) * (εp : K)) ^ (D * p ^ n) = 1 from by
              rw [mul_pow, pow_mul, hζK.pow_eq_one, one_pow, one_mul,
                mul_comm D (p ^ n), pow_mul, hεpK.pow_eq_one, one_pow])) := by
      subst hsplit; rfl
    have hθinvfac : θK⁻¹ = DirichletCharacter.changeLevel (Dvd.intro _ rfl) (toFieldChar η)⁻¹
        * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) (toFieldChar χ)⁻¹ := by
      rw [hθKfac, mul_inv]; congr 1 <;> exact (map_inv _ _).symm
    rw [hgsplit, coe_gaussSum_zmodChar η hζ hζK, coe_gaussSum_zmodChar χ hεp hεpK]
    exact ValuesAtOneComplex.gaussSum_mul_coprime hco (toFieldChar η)⁻¹ (toFieldChar χ)⁻¹
      hθinvfac hζK.pow_eq_one hεpK.pow_eq_one
  -- STEP 4 (final algebra): combine T615 + T616, divide by `p`, flip signs, factor `G`
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [hT616] at hT615
  -- `𝓐_ρ(0) = G_χ⁻¹·(1 − θK(p)·p⁻¹)·F̃(0)`
  have hAρ : PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ))
      = GχK⁻¹ * (1 - θK ((p : ZMod (D * p ^ n))) * (p : K)⁻¹)
        * PowerSeries.constantCoeff (Ftilde p K θK hε) := by
    have hGχ0 : GχK ≠ 0 := hGχKne
    field_simp at hT615 ⊢
    linear_combination hT615
  rw [hmass, hAρ, hF0, hGprod]
  field_simp

end MeasureR

end PadicLFunctions
