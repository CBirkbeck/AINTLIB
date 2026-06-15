/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.PowerSeries.Evaluation
import PadicLFunctions.MeasureR.BaseChange
import PadicLFunctions.Interpolation.Characters

/-!
# Twisting measures by Dirichlet characters (RJW §5.1)

The twist `μ_χ` of a measure by a Dirichlet character of `p`-power conductor
(RJW eq:twist by chi, TeX 1637–1640), the twist by a continuous additive
character (the `z`-twist of §3.5, TeX 1084–1090), and the cleared forms of
the restriction formula (`EqRestrictionFormula`, TeX 1126–1131) and of the
Mahler transform of the twist (RJW Lem 5.4, TeX 1675–1678). Denominators are
cleared per the recorded replan note R5-CLEAR (`.mathlib-quality/
decomposition.md` §5).
-/

open scoped fwdDiff
open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

/-- L5.1.2: the twist of a measure by a continuous `R`-valued function
(specialised to characters): `(twist g μ)(f) = μ(g·f)` — RJW eq:twist by chi
(TeX 1637–1640) reads `∫ f dμ_χ = ∫ χ f dμ`. -/
def twist (g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p] :=
  cmul p K g μ

variable {p K}

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
@[simp]
lemma twist_apply (g f : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) :
    twist p K g μ f = μ (g * f) := rfl

omit [CompleteSpace K] in
/-- Twisted moments: `∫ x^k d(twist g μ) = ∫ g(x)·x^k dμ`. -/
lemma twist_powCM (g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) (k : ℕ) :
    twist p K g μ (powCM p K k) = μ (g * powCM p K k) := rfl

/-- A continuous additive character of `ℤ_p`, as a continuous map (mathlib's
`addChar_of_value_at_one` with its continuity lemma). -/
def charCM (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) : C(ℤ_[p], integerRing K) :=
  ⟨⇑(PadicInt.addChar_of_value_at_one r hr),
    PadicInt.continuous_addChar_of_value_at_one hr⟩

/-- The character `κ_r` takes the value `(1+r)^k` at natural numbers. -/
@[simp]
lemma charCM_natCast (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) (k : ℕ) :
    charCM r hr ((k : ℕ) : ℤ_[p]) = (1 + r) ^ k := by
  change PadicInt.addChar_of_value_at_one r hr ((k : ℕ) : ℤ_[p]) = _
  rw [show ((k : ℤ_[p])) = k • (1 : ℤ_[p]) from (nsmul_one k).symm,
    AddChar.map_nsmul_eq_pow, PadicInt.addChar_of_value_at_one_def]

variable (p K)

/-- The fibres of reduction mod `p^n` are clopen. -/
lemma isClopen_toZModPow_fiber (n : ℕ) (b : ZMod (p ^ n)) :
    IsClopen {x : ℤ_[p] | PadicInt.toZModPow n x = b} :=
  PadicMeasure.isClopen_toZModPow_fiber p n b

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- L5.1.3 (integral form, at the use site of Thm 5.1): for `n ≥ 1`, a
`χ`-twisted integral over `ℤ_p` equals the integral over `ℤ_p^×` — i.e.
restriction to the units does not change the twist (RJW TeX 1641: "as `χ` is
supported on `ℤ_p^×`, the twisted measure `μ_χ` is automatically supported on
`ℤ_p^×` as well"; TeX 1752–1753). -/
theorem twist_res_units {n : ℕ} (hn : 1 ≤ n) (χ : DirichletCharacter (integerRing K) (p ^ n))
    (μ : MeasureR K ℤ_[p]) :
    res p K (PadicMeasure.isClopen_units p) (twist p K χ.toContinuousMapZp μ)
      = twist p K χ.toContinuousMapZp μ := by
  refine LinearMap.ext fun f => ?_
  change μ (χ.toContinuousMapZp * (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f))
      = μ (χ.toContinuousMapZp * f)
  congr 1
  ext x
  refine congrArg Subtype.val ?_
  simp only [ContinuousMap.mul_apply, charFnCM_apply]
  by_cases hx : IsUnit x
  · rw [Set.indicator_of_mem (show x ∈ {x : ℤ_[p] | IsUnit x} from hx), Pi.one_apply, one_mul]
  · rw [DirichletCharacter.toContinuousMapZp_eq_zero χ hn hx, zero_mul, zero_mul]

variable {p K}

/-- L5.1.6: the `z`-twist transform formula, coefficientwise form (recorded
fallback of the decomposition's eval₂ form — both routes recorded at L5.1.6
attack [3]): the Mahler coefficients of the twist of `μ` by the character
`κ_r = (1+r)^x` (mathlib `PadicInt.addChar_of_value_at_one`) are
`∑_{m} binom(n+m choose stuff)`-convolutions; equivalently, for every `n`,
`𝓐(κ_r·μ)_n = ∑' m, (coeff of the expansion) — here stated in the form the
§5.1 proofs consume: the twisted transform evaluated through `(1+T)(1+r)−1`.

Source (TeX 1084–1090): "the measure `z^x μ` has Mahler transform
`𝓐_μ((1+T)z − 1)`". -/
theorem mahlerTransform_charTwist (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) (μ : MeasureR K ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (mahlerTransform p K (twist p K (charCM r hr) μ))
      = ∑' m, PowerSeries.coeff n
            (((1 + PowerSeries.X) * (PowerSeries.C (1 + r)) - 1) ^ m)
          * μ (mahlerCM p K m) := by
  rw [coeff_mahlerTransform, twist_apply, apply_eq_tsum]
  refine tsum_congr fun m => ?_
  congr 1
  -- both sides are the finite sum `∑_{i ≤ m} (−1)^{m−i}·C(m,i)·(1+r)^i·C(i,n)`
  rw [fwdDiff_iter_eq_sum_shift]
  have hA : (((1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1 :
        PowerSeries (integerRing K))) ^ m
      = ∑ i ∈ Finset.range (m + 1),
          ((-1 : integerRing K) ^ (m - i) * (m.choose i) * (1 + r) ^ i) •
            (1 + PowerSeries.X) ^ i := by
    rw [sub_eq_add_neg, Commute.add_pow (Commute.all _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.smul_eq_C_mul, mul_pow, ← map_pow]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [hA, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbin : PowerSeries.coeff n
      ((1 + PowerSeries.X : PowerSeries (integerRing K)) ^ i)
      = (i.choose n : integerRing K) := by
    have hcast : (((1 + Polynomial.X) ^ i : Polynomial (integerRing K)) :
          PowerSeries (integerRing K))
        = (1 + PowerSeries.X : PowerSeries (integerRing K)) ^ i := by
      rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
    rw [← hcast, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  rw [PowerSeries.coeff_smul, smul_eq_mul, hbin, ContinuousMap.mul_apply, zero_add,
    nsmul_one, charCM_natCast, mahlerCM_apply, mahler_natCast_eq, map_natCast,
    zsmul_eq_mul]
  push_cast
  ring

omit [CompleteSpace K] in
/-- Any power of a primitive `p^n`-th root of unity satisfies `‖ζ^c − 1‖ < 1`
(W2, extended from primitive roots to all of `μ_{p^∞}`). -/
lemma norm_pow_sub_one_lt_one {ζ : integerRing K} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (c : ℕ) : ‖ζ ^ c - 1‖ < 1 := by
  by_cases hc1 : ζ ^ c = 1
  · simp [hc1]
  · have horder : orderOf (ζ ^ c) ∣ p ^ n :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hp.out).mp horder
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hc1
      · exact h
    have hprim : IsPrimitiveRoot ((ζ ^ c : integerRing K) : K) (p ^ j) := by
      have h0 : IsPrimitiveRoot (ζ ^ c) (orderOf (ζ ^ c)) := IsPrimitiveRoot.orderOf _
      rw [hj] at h0
      exact h0.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
    exact hprim.norm_sub_one_lt hj1

omit [CompleteSpace K] in
/-- `ζ^c − 1` is topologically nilpotent for `ζ ∈ μ_{p^n}`. -/
lemma tendsto_pow_pow_sub_one {ζ : integerRing K} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (c : ℕ) :
    Filter.Tendsto ((ζ ^ c - 1) ^ ·) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_pow_sub_one_lt_one hζ c)

/-- L5.1.7 (`EqRestrictionFormula`, cleared per R5-CLEAR): for a primitive
`p^n`-th root of unity `ζ` and `b : ZMod (p^n)`,
`p^n · Res_{b+p^nℤ_p}(μ) = ∑_{c} ζ^{-bc} · (κ_{ζ^c−1}-twist of μ)` as
measures (`ζ^{-bc}` realised with the positive exponent `c·(p^n − b.val)`).

Source (verbatim, TeX 1126–1131): the display `EqRestrictionFormula`,
multiplied through by `p^n`. -/
theorem res_class_eq_sum_twists {n : ℕ} (_hn : 1 ≤ n) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (b : ZMod (p ^ n)) (μ : MeasureR K ℤ_[p]) :
    ((p : ℕ) ^ n : integerRing K) •
        res p K (isClopen_toZModPow_fiber p n b) μ
      = ∑ c ∈ Finset.range (p ^ n),
          ζ ^ (c * (p ^ n - (b.val % p ^ n))) •
            twist p K (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)) μ := by
  have hbval : b.val % p ^ n = b.val := Nat.mod_eq_of_lt (ZMod.val_lt b)
  -- the pointwise orthogonality relation, as an identity of continuous maps
  have hpoint : (((p : ℕ) ^ n : integerRing K)) •
        charFnCM K ℤ_[p] (isClopen_toZModPow_fiber p n b)
      = ∑ c ∈ Finset.range (p ^ n),
          ζ ^ (c * (p ^ n - b.val % p ^ n)) •
            charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c) := by
    refine ContinuousMap.coe_injective
      (Continuous.ext_on (PadicInt.denseRange_natCast (p := p))
        (map_continuous _) (map_continuous _) ?_)
    rintro _ ⟨m, rfl⟩
    simp only [ContinuousMap.coe_smul, ContinuousMap.coe_sum, Pi.smul_apply,
      Finset.sum_apply, charFnCM_apply, charCM_natCast, smul_eq_mul]
    -- each summand is `(ζ^{s+m})^c` with `s := p^n − b.val`
    have hterm : ∀ c, ζ ^ (c * (p ^ n - b.val % p ^ n)) * (1 + (ζ ^ c - 1)) ^ m
        = (ζ ^ ((p ^ n - b.val % p ^ n) + m)) ^ c := by
      intro c
      rw [show (1 + (ζ ^ c - 1) : integerRing K) = ζ ^ c by ring, ← pow_mul,
        ← pow_add, ← mul_add, mul_comm c _, pow_mul]
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    -- `ζ^{s+m} = 1` iff `m` lies in the residue class `b`
    have hω : ζ ^ ((p ^ n - b.val % p ^ n) + m) = 1
        ↔ PadicInt.toZModPow n ((m : ℕ) : ℤ_[p]) = b := by
      rw [hζ.pow_eq_one_iff_dvd, map_natCast, hbval,
        ← ZMod.natCast_eq_zero_iff _ (p ^ n)]
      push_cast [Nat.cast_sub (ZMod.val_lt b).le]
      rw [← Nat.cast_pow, ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val b,
        neg_add_eq_zero, eq_comm]
    by_cases hmem : PadicInt.toZModPow n ((m : ℕ) : ℤ_[p]) = b
    · rw [Set.indicator_of_mem (show _ ∈ {x : ℤ_[p]
          | PadicInt.toZModPow n x = b} from hmem), Pi.one_apply, mul_one]
      rw [Finset.sum_congr rfl fun c _ => by rw [hω.mpr hmem, one_pow],
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      ring
    · rw [Set.indicator_of_notMem (show _ ∉ {x : ℤ_[p]
          | PadicInt.toZModPow n x = b} from hmem), mul_zero]
      have hωne : ζ ^ ((p ^ n - b.val % p ^ n) + m) ≠ 1 := fun h => hmem (hω.mp h)
      have hgeom := geom_sum_mul (ζ ^ ((p ^ n - b.val % p ^ n) + m)) (p ^ n)
      rw [← pow_mul, mul_comm _ (p ^ n), pow_mul, hζ.pow_eq_one, one_pow, sub_self]
        at hgeom
      exact ((mul_eq_zero.mp hgeom).resolve_right
        (sub_ne_zero.mpr hωne)).symm
  -- integrate the pointwise identity
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  change ((p : ℕ) ^ n : integerRing K) •
      μ (charFnCM K ℤ_[p] (isClopen_toZModPow_fiber p n b) * f) = _
  rw [← map_smul, ← smul_mul_assoc, hpoint, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [smul_mul_assoc, map_smul, LinearMap.smul_apply, twist_apply]

/-- L5.1.8 (RJW Lem 5.4, cleared — statement form pinned by the planning
trace at decomposition L5.1.8 attack [2]): for `χ` primitive mod `p^n`
(`n ≥ 1`) and `ζ` a primitive `p^n`-th root of unity,
`G(χ⁻¹) · 𝓐(μ_χ) = ∑_{c units} χ⁻¹(c) · 𝓐(κ_{ζ^c−1}·μ)`.

Source (verbatim, TeX 1675–1678): "The Mahler transform of `μ_χ` is
`𝓐_{μ_χ}(T) = (1/G(χ⁻¹)) ∑_c χ(c)⁻¹ 𝓐_μ((1+T)ε^c − 1)`" — multiplied
through by the Gauss sum. -/
theorem mahler_twist_formula {n : ℕ}
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n)) (μ : MeasureR K ℤ_[p]) :
    gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) (hζ.pow_eq_one)) •
        twist p K χ.toContinuousMapZp μ
      = ∑ c ∈ Finset.range (p ^ n),
          χ⁻¹ (c : ZMod (p ^ n)) •
            twist p K (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)) μ := by
  have hχinv : χ⁻¹.IsPrimitive := (DirichletCharacter.conductor_inv χ).trans hχ
  -- pointwise Gauss–Fourier expansion: `G(χ⁻¹)·χ̃ = ∑_c χ⁻¹(c)·κ_{ζ^c−1}`
  have hpoint : gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) (hζ.pow_eq_one)) •
        χ.toContinuousMapZp
      = ∑ c ∈ Finset.range (p ^ n),
          χ⁻¹ (c : ZMod (p ^ n)) •
            charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c) := by
    refine ContinuousMap.coe_injective
      (Continuous.ext_on (PadicInt.denseRange_natCast (p := p))
        (map_continuous _) (map_continuous _) ?_)
    rintro _ ⟨m, rfl⟩
    simp only [ContinuousMap.coe_smul, ContinuousMap.coe_sum, Pi.smul_apply,
      Finset.sum_apply, charCM_natCast, smul_eq_mul]
    -- the right side is the Gauss sum of `χ⁻¹` against `e.mulShift m`
    have hterm : ∀ c : ℕ, χ⁻¹ ((c : ℕ) : ZMod (p ^ n)) * (1 + (ζ ^ c - 1)) ^ m
        = χ⁻¹ ((c : ℕ) : ZMod (p ^ n))
            * AddChar.zmodChar (p ^ n) (hζ.pow_eq_one) (((m * c : ℕ) : ZMod (p ^ n))) := by
      intro c
      rw [show (1 + (ζ ^ c - 1) : integerRing K) = ζ ^ c by ring, ← pow_mul,
        AddChar.zmodChar_apply' (hζ.pow_eq_one), mul_comm c m]
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    have hsum : ∑ c ∈ Finset.range (p ^ n),
        χ⁻¹ ((c : ℕ) : ZMod (p ^ n))
          * AddChar.zmodChar (p ^ n) (hζ.pow_eq_one) (((m * c : ℕ) : ZMod (p ^ n)))
        = gaussSum χ⁻¹
            ((AddChar.zmodChar (p ^ n) (hζ.pow_eq_one)).mulShift
              ((m : ℕ) : ZMod (p ^ n))) := by
      rw [gaussSum]
      refine Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod (p ^ n))) (fun a => a.val)
        ?_ ?_ ?_ ?_ ?_
      · intro c _
        exact Finset.mem_univ _
      · intro a _
        exact Finset.mem_range.mpr (ZMod.val_lt a)
      · intro c hc
        exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hc)
      · intro a _
        exact ZMod.natCast_zmod_val a
      · intro c _
        rw [AddChar.mulShift_apply, ← Nat.cast_mul]
    rw [hsum, gaussSum_mulShift_of_isPrimitive _ hχinv, inv_inv,
      DirichletCharacter.toContinuousMapZp_apply, map_natCast]
    ring
  -- integrate the pointwise identity
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  change gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) (hζ.pow_eq_one)) •
      μ (χ.toContinuousMapZp * f) = _
  rw [← map_smul, ← smul_mul_assoc, hpoint, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [smul_mul_assoc, map_smul, LinearMap.smul_apply, twist_apply]

section substAffine

open scoped PowerSeries.WithPiTopology

instance : IsLinearTopology (integerRing K)ᵐᵒᵖ (integerRing K) :=
  (IsCentralScalar.isLinearTopology_iff _).mpr inferInstance

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- The affine substitution point `(1+X)(1+r) − 1 = C r + C(1+r)·X` is
topologically nilpotent in the product topology when `r` is. -/
lemma hasEval_affine (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) :
    PowerSeries.HasEval
      ((1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1 :
        PowerSeries (integerRing K)) := by
  have h1 : ((1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1 :
        PowerSeries (integerRing K))
      = PowerSeries.C r + PowerSeries.C (1 + r) * PowerSeries.X := by
    rw [show (PowerSeries.C (1 + r) : PowerSeries (integerRing K))
        = 1 + PowerSeries.C r by rw [map_add, map_one]]
    ring
  rw [h1]
  exact (PowerSeries.HasEval.map PowerSeries.WithPiTopology.continuous_C hr).add
    ((PowerSeries.HasEval.X).mul_left _)

/-- L5.1.6 (eval₂ form): the substitution `F(T) ↦ F((1+T)(1+r) − 1)` as a ring
homomorphism — mathlib's topological `PowerSeries.eval₂Hom` at the
topologically nilpotent affine point. -/
noncomputable def substAffine (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) :
    PowerSeries (integerRing K) →+* PowerSeries (integerRing K) :=
  PowerSeries.eval₂Hom PowerSeries.WithPiTopology.continuous_C
    (hasEval_affine r hr)

@[simp]
lemma substAffine_X (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) :
    substAffine r hr PowerSeries.X
      = (1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1 := by
  rw [show substAffine r hr PowerSeries.X
      = PowerSeries.eval₂ PowerSeries.C
          ((1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1) PowerSeries.X from
    congrFun (PowerSeries.coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C
      (hasEval_affine r hr)) PowerSeries.X]
  exact PowerSeries.eval₂_X _ _

@[simp]
lemma substAffine_C (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) (b : integerRing K) :
    substAffine r hr (PowerSeries.C b) = PowerSeries.C b := by
  rw [show substAffine r hr (PowerSeries.C b)
      = PowerSeries.eval₂ PowerSeries.C
          ((1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1) (PowerSeries.C b) from
    congrFun (PowerSeries.coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C
      (hasEval_affine r hr)) (PowerSeries.C b)]
  exact PowerSeries.eval₂_C _ _ _

/-- `substAffine r` sends `1 + X` to `C(1+r)·(1+X)`. -/
lemma substAffine_one_add_X (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) :
    substAffine r hr (1 + PowerSeries.X)
      = PowerSeries.C (1 + r) * (1 + PowerSeries.X) := by
  rw [map_add, map_one, substAffine_X]
  ring

/-- The coefficients of the affine substitution are the L5.1.6 tsums. -/
lemma coeff_substAffine (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0))
    (F : PowerSeries (integerRing K)) (n : ℕ) :
    PowerSeries.coeff n (substAffine r hr F)
      = ∑' m, PowerSeries.coeff n
            (((1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1) ^ m)
          * PowerSeries.coeff m F := by
  have h := PowerSeries.hasSum_eval₂ PowerSeries.WithPiTopology.continuous_C
    (hasEval_affine r hr) F
  have h2 := h.map (PowerSeries.coeff (R := integerRing K) n).toAddMonoidHom
    (PowerSeries.WithPiTopology.continuous_coeff (R := integerRing K) n)
  simp only [LinearMap.toAddMonoidHom_coe, Function.comp_def] at h2
  have h3 : substAffine r hr F
      = PowerSeries.eval₂ PowerSeries.C
          ((1 + PowerSeries.X) * PowerSeries.C (1 + r) - 1) F :=
    congrFun (PowerSeries.coe_eval₂Hom PowerSeries.WithPiTopology.continuous_C
      (hasEval_affine r hr)) F
  rw [h3, ← h2.tsum_eq]
  exact tsum_congr fun m => by
    rw [PowerSeries.coeff_C_mul]
    ring

/-- L5.1.6 in the source's own form (TeX 1084–1090: "the measure `z^x μ` has
Mahler transform `𝓐_μ((1+T)z − 1)`"): the eval₂-upgrade of
`mahlerTransform_charTwist`. -/
theorem mahlerTransform_charTwist_eq_substAffine (r : integerRing K)
    (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) (μ : MeasureR K ℤ_[p]) :
    mahlerTransform p K (twist p K (charCM r hr) μ)
      = substAffine r hr (mahlerTransform p K μ) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_substAffine, mahlerTransform_charTwist]
  exact tsum_congr fun m => by rw [coeff_mahlerTransform]

end substAffine

end MeasureR

end

end PadicLFunctions
