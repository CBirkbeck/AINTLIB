/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Interpolation.NonTame

/-!
# The p-adic L-function of a Dirichlet character (RJW §5.3, TeX 1929–1957)

For `θ = χη` a Dirichlet character with `η` of conductor `D` prime to `p` and
`χ` of conductor `p^n` (`n ≥ 0`), RJW Def 5.18 sets
`L_p(θ,s) := ∫_{ℤ_p^×} χ(x)⟨x⟩^{1−s}·ζ_η` for `s ∈ ℤ_p`, where
`ζ_η = x⁻¹·Res_{ℤ_p^×}(μ_η)` is a genuine measure on `ℤ_p^×`
(`zetaEtaCleared`, through the cleared `μ̃_η = −G(η⁻¹)F_η`; `LpFunction`
divides the Gauss unit back out). **RJW Theorem 5.19**
(`TheoremLeopoldtAnalyticTwist`, TeX 1943–1946):
`L_p(θ,1−k) = (1 − θω^{−k}(p)p^{k−1})·L(θω^{−k},1−k)` for all `k ≥ 1`
(`Lp_interpolation`), proved by the `eq:alternative` route (TeX 1948–1956):
the character algebra `χω^{−1}(x)⟨x⟩^{k−1} = χω^{−k}(x)x^{k−1}` reduces the
claim to the twisted moments of `ζ_η` (`zetaEta_twisted_moments`) at the
primitive core of `χω^{−k}`.
-/

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

noncomputable section

namespace MeasureR

/-- The Teichmüller character `ω`, valued in `integerRing K` (the coefficient
upgrade of `PadicInt.teichmullerChar` along the structure map). -/
def teichmullerCharR : DirichletCharacter (integerRing K) p :=
  (PadicInt.teichmullerChar p).ringHomComp (algebraMap ℤ_[p] (integerRing K))

/-- `x ↦ x⁻¹` on `ℤ_p^×`, valued in `integerRing K`. -/
def invUnitsCM : C(ℤ_[p]ˣ, integerRing K) :=
  ⟨fun u => algebraMap ℤ_[p] (integerRing K) (PadicMeasure.invCM p u),
    (integerRing.isometry_algebraMap p K).continuous.comp
      (map_continuous (PadicMeasure.invCM p))⟩

/-- `x ↦ ⟨x⟩^s` on `ℤ_p^×` for fixed `s ∈ ℤ_p`, valued in `integerRing K`
(T519's base-continuity through the isometric structure map). -/
def anglePowCM (s : ℤ_[p]) : C(ℤ_[p]ˣ, integerRing K) :=
  ⟨fun u => algebraMap ℤ_[p] (integerRing K)
      (PadicInt.onePAdicPow p (PadicInt.angleUnit p u : ℤ_[p])
        (PadicInt.angleUnit_sub_one_mem p u) s),
    (integerRing.isometry_algebraMap p K).continuous.comp
      (continuous_onePAdicPow_angleUnit p s)⟩

/-- RJW's `ζ_η := x⁻¹·Res_{ℤ_p^×}(μ_η)` (TeX 1866–1868) as a genuine measure
on `ℤ_p^×`, in the cleared normalisation `G(η⁻¹)·ζ_η`: pairing `g` against it
integrates `x⁻¹·g`, extended by zero, against `μ̃_η` (the restriction to the
units is implicit in the extension by zero). -/
def zetaEtaCleared {D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) :
    MeasureR K ℤ_[p]ˣ :=
  (muEtaCleared p K η hζ hD).comp
    ((extendByZero p K).comp (LinearMap.mulLeft (integerRing K) (invUnitsCM p K)))

/-- RJW Def 5.18 (TeX 1929–1932): the `p`-adic L-function
`L_p(θ,s) = ∫_{ℤ_p^×} χ(x)⟨x⟩^{1−s}·ζ_η` of `θ = χη`, as a `K`-value (the
Gauss-sum clearing of `μ̃_η` is divided back out; `χ` enters through its
locally constant extension to `ℤ_p`, restricted to the units). -/
def LpFunction {D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) (s : ℤ_[p]) : K :=
  (((gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one) : integerRing K) : K))⁻¹
    * ((zetaEtaCleared p K η hζ hD
        (χ.toContinuousMapZp.comp (PadicMeasure.unitsValCM p)
          * anglePowCM p K (1 - s)) : integerRing K) : K)

/-- The `p`-part of `θω^{−k}`: the character `χ·ω^{−k}` at level
`p^{max n 1}` (the join of the levels of `χ` and `ω`). -/
def twistedPChar {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n))
    (k : ℕ) : DirichletCharacter (integerRing K) (p ^ max n 1) :=
  DirichletCharacter.changeLevel (pow_dvd_pow p (le_max_left n 1)) χ
    * (DirichletCharacter.changeLevel
        (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp (le_max_right n 1)))
        (teichmullerCharR p K))⁻¹ ^ k

variable {p K}

omit [CompleteSpace K] [CharZero K] in
@[simp]
lemma invUnitsCM_apply (u : ℤ_[p]ˣ) :
    invUnitsCM p K u
      = algebraMap ℤ_[p] (integerRing K) (PadicMeasure.invCM p u) :=
  rfl

omit [CompleteSpace K] [CharZero K] in
@[simp]
lemma anglePowCM_apply (s : ℤ_[p]) (u : ℤ_[p]ˣ) :
    anglePowCM p K s u
      = algebraMap ℤ_[p] (integerRing K)
          (PadicInt.onePAdicPow p (PadicInt.angleUnit p u : ℤ_[p])
            (PadicInt.angleUnit_sub_one_mem p u) s) :=
  rfl

omit [CharZero K] in
@[simp]
lemma zetaEtaCleared_apply {D : ℕ} [NeZero D]
    (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    (g : C(ℤ_[p]ˣ, integerRing K)) :
    zetaEtaCleared p K η hζ hD g
      = muEtaCleared p K η hζ hD (extendByZero p K (invUnitsCM p K * g)) :=
  rfl

/-- Every Dirichlet character of `p`-power level factors through a primitive
character at a `p`-power sub-level (the T516 conductor argument, packaged for
instantiating `Lp_interpolation`). -/
lemma exists_primitive_pPow_factorisation {R : Type*} [CommMonoidWithZero R]
    {M : ℕ} (ψ : DirichletCharacter R (p ^ M)) :
    ∃ (m : ℕ) (hm : m ≤ M) (ψ₀ : DirichletCharacter R (p ^ m)),
      ψ₀.IsPrimitive
        ∧ ψ = DirichletCharacter.changeLevel (pow_dvd_pow p hm) ψ₀ := by
  obtain ⟨m, hmle, hcond⟩ : ∃ m, m ≤ M ∧ ψ.conductor = p ^ m := by
    obtain ⟨m, _, hm2⟩ := (Nat.dvd_prime_pow hp.out).mp ψ.conductor_dvd_level
    exact ⟨m, (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp
      (hm2 ▸ ψ.conductor_dvd_level), hm2⟩
  have hft : DirichletCharacter.FactorsThrough ψ (p ^ m) := by
    rw [← hcond]
    exact ψ.factorsThrough_conductor
  obtain ⟨hdvd, ψ₀, hψeq⟩ := hft
  refine ⟨m, hmle, ψ₀, ?_, hψeq⟩
  refine le_antisymm
    (Nat.le_of_dvd (pow_pos hp.out.pos m) ψ₀.conductor_dvd_level) ?_
  have hmem : ψ₀.conductor ∈ DirichletCharacter.conductorSet ψ :=
    ⟨dvd_trans ψ₀.conductor_dvd_level hdvd, ψ₀.primitiveCharacter, by
      rw [hψeq, DirichletCharacter.changeLevel_trans
        ψ₀.primitiveCharacter ψ₀.conductor_dvd_level hdvd,
        DirichletCharacter.changeLevel_primitiveCharacter]⟩
  calc p ^ m = ψ.conductor := hcond.symm
    _ ≤ ψ₀.conductor := Nat.sInf_le hmem

/-- **RJW Theorem 5.19** (`TheoremLeopoldtAnalyticTwist`, TeX 1943–1946):
"For all `k ≥ 1`, we have
`L_p(θ,1−k) = (1 − θω^{−k}(p)p^{k−1})L(θω^{−k},1−k)`." Here `χ'` is the
primitive core of the `p`-part `χ·ω^{−k}` of `θω^{−k}` (a factorisation
supplied by `exists_primitive_pPow_factorisation`), and `θ' = η·χ'` realises
`θω^{−k}` at its conductor, so `L(θω^{−k},1−k)` is
`LvalNeg (toFieldChar θ') (k−1)` exactly as in `zetaEta_twisted_moments`. -/
theorem Lp_interpolation {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (_hχ : χ.IsPrimitive)
    {ε : integerRing K} (hε : IsPrimitiveRoot ε (p ^ max n 1))
    {k : ℕ} (hk : 0 < k) {m : ℕ} (hmle : m ≤ max n 1)
    {χ' : DirichletCharacter (integerRing K) (p ^ m)} (hχ'prim : χ'.IsPrimitive)
    (hχ' : twistedPChar p K χ k
      = DirichletCharacter.changeLevel (pow_dvd_pow p hmle) χ')
    {θ' : DirichletCharacter (integerRing K) (D * p ^ m)}
    (hθ' : θ' = DirichletCharacter.changeLevel (Dvd.intro _ rfl) η
      * DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ') :
    LpFunction p K η hζ hD χ ((1 : ℤ_[p]) - ((k : ℕ) : ℤ_[p]))
      = (1 - (θ' ((p : ℕ) : ZMod (D * p ^ m)) : K) * (p : K) ^ (k - 1))
        * LvalNeg (toFieldChar θ') (k - 1) := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- the primitive `p^m`-th root from the ambient `p^{max n 1}`-th root
  have hε' : IsPrimitiveRoot (ε ^ p ^ (max n 1 - m)) (p ^ m) := by
    have h := hε.pow_of_dvd (pow_ne_zero _ hp.out.ne_zero)
      (pow_dvd_pow p (Nat.sub_le (max n 1) m))
    rwa [Nat.pow_div (Nat.sub_le (max n 1) m) hp.out.pos,
      Nat.sub_sub_self hmle] at h
  -- the twisted moments of `ζ_η` at the primitive core
  have hmom := zetaEta_twisted_moments hD1 hη hζ hD hχ'prim hε' hθ'
    (Nat.succ_pos k')
  simp only [Nat.succ_sub_one] at hmom ⊢
  -- the character-level key: `χ = χ'·ω^{k'+1}` at level `p^{max n 1}`
  have hkey : DirichletCharacter.changeLevel (pow_dvd_pow p (le_max_left n 1)) χ
      = DirichletCharacter.changeLevel (pow_dvd_pow p hmle) χ'
        * (DirichletCharacter.changeLevel
            (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp (le_max_right n 1)))
            (teichmullerCharR p K)) ^ (k' + 1) := by
    rw [← hχ', twistedPChar, mul_assoc, ← mul_pow, inv_mul_cancel, one_pow,
      mul_one]
  -- pointwise integrand identity on the units
  have hpt : ∀ u : ℤ_[p]ˣ,
      invUnitsCM p K u * (χ.toContinuousMapZp ((u : ℤ_[p]))
          * anglePowCM p K (((k' + 1 : ℕ) : ℤ_[p])) u)
        = χ'.toContinuousMapZp ((u : ℤ_[p])) * powCM p K k' ((u : ℤ_[p])) := by
    intro u
    have hu : IsUnit (PadicInt.toZModPow (max n 1) ((u : ℤ_[p]))) :=
      u.isUnit.map _
    -- character part: `χ(x) = χ'(x)·ω(x)^{k'+1}` at the unit `u`
    have hchar := congrArg (fun ψ : DirichletCharacter (integerRing K)
        (p ^ max n 1) => ψ (PadicInt.toZModPow (max n 1) ((u : ℤ_[p])))) hkey
    simp only [MulChar.coeToFun_mul, Pi.mul_apply] at hchar
    rw [show (DirichletCharacter.changeLevel (pow_dvd_pow p (le_max_left n 1)) χ)
          (PadicInt.toZModPow (max n 1) ((u : ℤ_[p])))
        = χ.toContinuousMapZp ((u : ℤ_[p])) from
        DirichletCharacter.toContinuousMapZp_changeLevel (le_max_left n 1)
          (pow_dvd_pow p (le_max_left n 1)) χ u.isUnit,
      show (DirichletCharacter.changeLevel (pow_dvd_pow p hmle) χ')
          (PadicInt.toZModPow (max n 1) ((u : ℤ_[p])))
        = χ'.toContinuousMapZp ((u : ℤ_[p])) from
        DirichletCharacter.toContinuousMapZp_changeLevel hmle
          (pow_dvd_pow p hmle) χ' u.isUnit,
      ← hu.unit_spec, MulChar.pow_apply_coe,
      DirichletCharacter.changeLevel_eq_cast_of_dvd (teichmullerCharR p K)
        _ hu.unit, hu.unit_spec] at hchar
    rw [show ZMod.cast (PadicInt.toZModPow (max n 1) ((u : ℤ_[p])))
        = PadicInt.toZMod ((u : ℤ_[p])) from by
        rw [← ZMod.castHom_apply (h := dvd_pow_self p
            (Nat.one_le_iff_ne_zero.mp (le_max_right n 1))),
          PadicInt.castHom_toZModPow_eq_toZMod p
            (Nat.one_le_iff_ne_zero.mp (le_max_right n 1))]] at hchar
    rw [show teichmullerCharR p K (PadicInt.toZMod ((u : ℤ_[p])))
        = algebraMap ℤ_[p] (integerRing K)
            (PadicInt.teichmullerFun p ((u : ℤ_[p]))) from by
        rw [teichmullerCharR, MulChar.ringHomComp_apply,
          PadicInt.teichmullerChar_toZMod]] at hchar
    -- `ℤ_p`-level collapse: `x⁻¹·ω(x)^{k'+1}·⟨x⟩^{k'+1} = x^{k'}`
    have hZp : PadicMeasure.invCM p u
          * ((PadicInt.teichmullerFun p ((u : ℤ_[p]))) ^ (k' + 1)
            * ((PadicInt.angleUnit p u : ℤ_[p])) ^ (k' + 1))
        = ((u : ℤ_[p])) ^ k' := by
      have hunits : (u⁻¹ : ℤ_[p]ˣ)
            * (PadicInt.teichmuller p u * PadicInt.angleUnit p u) ^ (k' + 1)
          = u ^ k' := by
        rw [PadicInt.teichmuller_mul_angleUnit, pow_succ, mul_comm (u⁻¹),
          mul_assoc, mul_inv_cancel, mul_one]
      have hval := congrArg Units.val hunits
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, mul_pow,
        Units.val_pow_eq_pow_val] at hval
      exact hval
    -- assemble over the structure map
    rw [show anglePowCM p K (((k' + 1 : ℕ) : ℤ_[p])) u
        = algebraMap ℤ_[p] (integerRing K)
            (((PadicInt.angleUnit p u : ℤ_[p])) ^ (k' + 1)) from by
        rw [anglePowCM_apply, PadicInt.onePAdicPow_natCast],
      hchar, invUnitsCM_apply, powCM_apply,
      ← hZp, map_mul, map_mul, map_pow, map_pow]
    ring
  -- the integrand identity, extended by zero
  have hfun : extendByZero p K
        (invUnitsCM p K * (χ.toContinuousMapZp.comp (PadicMeasure.unitsValCM p)
          * anglePowCM p K (((k' + 1 : ℕ) : ℤ_[p]))))
      = charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p)
        * (χ'.toContinuousMapZp * powCM p K k') := by
    ext x
    by_cases hx : IsUnit x
    · rw [← hx.unit_spec, extendByZero_coe_unit]
      simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply]
      rw [show (PadicMeasure.unitsValCM p) hx.unit = ((hx.unit : ℤ_[p]))
          from rfl,
        charFnCM_apply, Set.indicator_of_mem
          (show ((hx.unit : ℤ_[p])) ∈ {y : ℤ_[p] | IsUnit y}
            from hx.unit.isUnit), Pi.one_apply, one_mul]
      exact congrArg Subtype.val (hpt hx.unit)
    · rw [show (extendByZero p K
          (invUnitsCM p K * (χ.toContinuousMapZp.comp
            (PadicMeasure.unitsValCM p)
            * anglePowCM p K (((k' + 1 : ℕ) : ℤ_[p]))))) x = 0
          from dif_neg hx,
        ContinuousMap.mul_apply, charFnCM_apply,
        Set.indicator_of_notMem (by simpa using hx), zero_mul]
  -- the Gauss unit is invertible in `K`
  have hG : (((gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one)
      : integerRing K) : K)) ≠ 0 := by
    have hu := gaussSum_isUnit_of_coprime hη hζ hD
    have h0 : gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one)
        ≠ (0 : integerRing K) := hu.ne_zero
    exact fun h => h0 (Subtype.coe_injective (by simpa using h))
  -- conclude
  rw [LpFunction, show (1 : ℤ_[p]) - ((1 : ℤ_[p]) - (((k' + 1 : ℕ) : ℤ_[p])))
      = (((k' + 1 : ℕ) : ℤ_[p])) from by ring,
    zetaEtaCleared_apply, hfun,
    show muEtaCleared p K η hζ hD
        (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p)
          * (χ'.toContinuousMapZp * powCM p K k'))
      = twist p K χ'.toContinuousMapZp
          (res p K (PadicMeasure.isClopen_units p) (muEtaCleared p K η hζ hD))
          (powCM p K k') from rfl,
    hmom, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hG, one_mul]

end MeasureR

end

end PadicLFunctions
