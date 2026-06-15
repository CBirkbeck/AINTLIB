/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.Toolbox

/-!
# The formal ψ-operator on power series (RJW §6, decomposition W6b)

The trace operator `ψ` exists in the project at the measure level
(`PadicLFunctions.MeasureR.psi`, the coefficient-free digit shift). This
file builds its FORMAL power-series avatar: every `F ∈ R⟦T⟧` decomposes
uniquely into `p` digits `F = Σ_{i<p} (1+T)^i · φ(F_i)` along
`φG := G((1+T)^p − 1)`, and `ψF := F₀`. The deferred `Eqphipsi` formula
(`(φ∘ψ)F = p⁻¹ Σ_{ξ∈μ_p} F((1+T)ξ−1)`, plan.md "Deferred") is realised in
the only form that is meaningful for unbounded series — as the CONVERGENT
EVALUATION identity at `T = 0` (`psiSeries_eval_zero`): the substitution
`T ↦ (1+T)ξ − 1` has non-nilpotent constant term for `ξ ≠ 1`, so the
formal-series form is ill-posed (recorded replan, decomposition R6).

Decomposition: `.mathlib-quality/decomposition.md` R6, cluster W6b.
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section digits

variable {R : Type*} [CommRing R]

/-- The formal Frobenius-substitution `φ : F(T) ↦ F((1+T)^p − 1)` (the
series-side of the measure operator `phi`). -/
noncomputable def phiSeries (F : PowerSeries R) : PowerSeries R :=
  F.subst ((1 + PowerSeries.X) ^ p - 1)

omit [hp : Fact p.Prime] in
/-- The substitution series `(1+T)^p − 1` always has constant coefficient `0`,
so `φ = subst` is well-defined over any `CommRing`. -/
lemma hasSubst_one_add_X_pow_sub_one :
    PowerSeries.HasSubst ((1 + PowerSeries.X) ^ p - 1 : PowerSeries R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

omit [hp : Fact p.Prime] in
@[simp]
lemma phiSeries_zero : phiSeries p (0 : PowerSeries R) = 0 := by
  rw [phiSeries, ← PowerSeries.coe_substAlgHom (hasSubst_one_add_X_pow_sub_one p), map_zero]

omit [hp : Fact p.Prime] in
/-- `φ` preserves constant coefficients (the substituend has constant term `0`). -/
@[simp]
lemma constantCoeff_phiSeries (G : PowerSeries R) :
    PowerSeries.constantCoeff (phiSeries p G) = PowerSeries.constantCoeff G := by
  have hvanish : ∀ n : ℕ, 0 < n →
      PowerSeries.coeff 0 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries R) ^ n) = 0 :=
    fun n hn => PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp)) n) 0 hn
  rw [phiSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p),
    finsum_eq_single _ 0 fun n hn => by
      rw [hvanish n (Nat.pos_of_ne_zero hn), smul_zero], pow_zero,
    PowerSeries.coeff_zero_one, smul_eq_mul, mul_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

omit [hp : Fact p.Prime] in
/-- `φ(C a · G) = C a · φ(G)` (substitution is a ring hom fixing constants). -/
lemma phiSeries_C_mul (a : R) (G : PowerSeries R) :
    phiSeries p (PowerSeries.C a * G) = PowerSeries.C a * phiSeries p G := by
  rw [phiSeries, phiSeries, PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p),
    show ((PowerSeries.C a).subst ((1 + PowerSeries.X) ^ p - 1) : PowerSeries R)
      = PowerSeries.C a from PowerSeries.subst_C a]

/-- The digit-decomposition predicate: `G` is a family of `p` digits for `F`
along `φ`, i.e. `F = Σ_{i<p} (1+T)^i·φ(G_i)`. -/
def IsDigitDecomp (F : PowerSeries R) (G : Fin p → PowerSeries R) : Prop :=
  F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (G i)

/-- W6b-b2: the formal trace operator `ψ` — the `0`-th digit of the
(unique, over an integral base such as `integerRing K`) digit decomposition.

**Replan R6 W6b-b1' (statement defect, recorded 2026-06-11, `.mathlib-quality/
b2_log.jsonl`):** the digit decomposition `F = Σ_{i<p} (1+T)^i·φ(G_i)` is the
`p`-adically-*integral* structure. Over a `CommRing` in which `p` is invertible
it is FALSE: `(1+T)^p − 1` then has unit linear coefficient, so `φ` is a
substitution by an order-`1` series with unit leading term, hence bijective
(`PowerSeries.substInvOfIsUnit`), and the digits are wildly non-unique
(counterexample `R = ℚ`, `p = 2`: `T` has an `S`-expansion). The
existence-uniqueness theorem `existsUnique_digits` is therefore proved over
`integerRing K` (where `S ≡ T^p mod p` is distinguished); see the bridge
section. Here `psiSeries` is junk-totalised over a general `CommRing R` (`0`
when no unique decomposition exists) so the `K`-coefficient users
(`ValuesAtOne.lean`) keep type-checking. -/
noncomputable def psiSeries (F : PowerSeries R) : PowerSeries R :=
  open Classical in
  if h : ∃! G : Fin p → PowerSeries R, IsDigitDecomp p F G then h.exists.choose 0
  else 0

/-- Whenever `F` has a unique digit decomposition, `psiSeries` is its `0`-th
digit (general `CommRing` version; the `∃!` hypothesis selects the integral
locus). -/
theorem psiSeries_eq_of_unique {F : PowerSeries R} {G : Fin p → PowerSeries R}
    (hex : ∃! G : Fin p → PowerSeries R, IsDigitDecomp p F G)
    (hG : IsDigitDecomp p F G) :
    psiSeries p F = G 0 := by
  rw [psiSeries, dif_pos hex, hex.unique hex.exists.choose_spec hG]

omit [hp : Fact p.Prime] in
/-- `map f` commutes with `φ` (substitution into `(1+T)^p − 1`, which is fixed
by `map f`). -/
lemma map_phiSeries {S : Type*} [CommRing S] (f : R →+* S) (G : PowerSeries R) :
    PowerSeries.map f (phiSeries p G) = phiSeries p (PowerSeries.map f G) := by
  have hmap : PowerSeries.map f ((1 + PowerSeries.X) ^ p - 1 : PowerSeries R)
      = (1 + PowerSeries.X) ^ p - 1 := by
    simp [map_sub, map_pow, map_add]
  have hcoeffB : ∀ (m d : ℕ),
      PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries S) ^ d)
        = f (PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries R) ^ d)) :=
    fun m d => by rw [← hmap, ← map_pow, PowerSeries.coeff_map]
  have hvanishR : ∀ (m d : ℕ), m < d →
      PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries R) ^ d) = 0 :=
    fun m d hmd => PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp)) d) m hmd
  have hvanishS : ∀ (m d : ℕ), m < d →
      PowerSeries.coeff m (((1 + PowerSeries.X) ^ p - 1 : PowerSeries S) ^ d) = 0 :=
    fun m d hmd => PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp)) d) m hmd
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, phiSeries, phiSeries,
    PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p),
    PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p),
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [hvanishR _ _ (by omega), smul_zero])),
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [hvanishS _ _ (by omega), smul_zero])),
    map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [PowerSeries.coeff_map, hcoeffB, smul_eq_mul, smul_eq_mul, map_mul]

omit [hp : Fact p.Prime] in
/-- `map f` sends a digit decomposition of `F` to one of `map f F`. -/
lemma isDigitDecomp_map {S : Type*} [CommRing S] (f : R →+* S)
    {F : PowerSeries R} {G : Fin p → PowerSeries R} (hG : IsDigitDecomp p F G) :
    IsDigitDecomp p (PowerSeries.map f F) (fun i => PowerSeries.map f (G i)) := by
  rw [IsDigitDecomp, hG, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_add, map_one, PowerSeries.map_X, map_phiSeries]

/-- W6b-b3' (realigned, replan R6.6): the `∂φ = p·φ∂` commutation for
`∂ = (1+T)d/dT` — the only derivative fact the c₀-design needs (the
field-level `ψ∂`-form is meaningless since `psiSeries` is junk over
fields). -/
theorem one_add_mul_derivative_phiSeries (F : PowerSeries R) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (phiSeries p F)
      = (p : R) • phiSeries p
          ((1 + PowerSeries.X) * PowerSeries.derivativeFun F) := by
  have hS := hasSubst_one_add_X_pow_sub_one (R := R) p
  set S : PowerSeries R := (1 + PowerSeries.X) ^ p - 1 with hSdef
  -- derivative of the substitution series `S = (1+X)^p − 1`
  have hone_sub : (1 : PowerSeries R).subst S = 1 := by
    rw [← PowerSeries.coe_substAlgHom hS, map_one]
  have hderS : d⁄dX R S = (p : R) • (1 + PowerSeries.X) ^ (p - 1) := by
    rw [hSdef, map_sub, Derivation.map_one_eq_zero, sub_zero, Derivation.leibniz_pow,
      map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add, smul_eq_mul,
      mul_one, ← Nat.cast_smul_eq_nsmul R]
  -- `1 + S = (1+X)^p`
  have hSplus : 1 + S = (1 + PowerSeries.X) ^ p := by rw [hSdef]; ring
  -- `(1+X)·(1+X)^{p−1} = (1+X)^p`
  have hpow : (1 + PowerSeries.X : PowerSeries R) * (1 + PowerSeries.X) ^ (p - 1)
      = (1 + PowerSeries.X) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  -- chain rule on `phiSeries p F = F.subst S`
  rw [phiSeries, phiSeries, show PowerSeries.derivativeFun (F.subst S) = d⁄dX R (F.subst S)
      from rfl, PowerSeries.derivative_subst R hS, hderS,
    show PowerSeries.derivativeFun F = d⁄dX R F from rfl,
    PowerSeries.subst_mul hS, PowerSeries.subst_add hS, PowerSeries.subst_X hS, hone_sub,
    hSplus, mul_smul_comm, mul_smul_comm]
  refine congrArg _ ?_
  rw [← mul_assoc, mul_comm (1 + PowerSeries.X) ((d⁄dX R F).subst S), mul_assoc, hpow,
    mul_comm]

end digits

section integral

/-!
### The digit decomposition over `integerRing K` (W6b-b1, integral form)

**Replan R6 W6b-b1'** (recorded `.mathlib-quality/b2_log.jsonl`, 2026-06-11):
the digit decomposition is the `p`-adically-integral statement (false over a
ring where `p` is invertible — see `psiSeries`). It is proved here over
`R := integerRing K` by transporting the measure-level `p`-residue
decomposition through the ring isomorphism `mahlerRingEquiv` (RJW Thm 3.20):
`(1+T)^i ↔ δ_i`, `φ ↔ MeasureR.phi`, so
`F = Σ_{i<p} (1+T)^i·φ(G_i)  ↔  μ = Σ_{i<p} δ_i * MeasureR.phi(ν_i)`, and the
latter is the residue-class digit decomposition built from `MeasureR.phi_psi`
(`φψ = Res_{pℤ_p}`) and the partition `ℤ_p = ⊔_{i<p} (i + pℤ_p)`.
-/

variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

open MeasureR

/-- `δ_a * μ` is the translate `y ↦ μ(f(a + ·))` (convolution by a Dirac is a
pushforward along addition). -/
lemma dirac_mul_eq_pushforward (a : ℤ_[p]) (μ : MeasureR K ℤ_[p]) :
    dirac K ℤ_[p] a * μ
      = pushforward K ℤ_[p] ℤ_[p] ⟨fun y => a + y, by fun_prop⟩ μ := by
  refine LinearMap.ext fun f => ?_
  rw [mul_apply, dirac_apply, convInner_apply, pushforward_apply]

omit [CompleteSpace K] in
/-- The series-side of `MeasureR.phi`: `𝓐_{φμ} = phiSeries 𝓐_μ` (R-level
Eq. (3.9), the `integerRing K` analogue of `mahlerTransform_phi`). -/
theorem mahlerTransform_phi (μ : MeasureR K ℤ_[p]) :
    mahlerTransform p K (MeasureR.phi p K μ)
      = phiSeries p (mahlerTransform p K μ) := by
  let B : PowerSeries (integerRing K) := (1 + PowerSeries.X) ^ p - 1
  let BZ : PowerSeries ℤ_[p] := (1 + PowerSeries.X) ^ p - 1
  have hconst : PowerSeries.constantCoeff B = 0 := by simp [B]
  have hsub : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  have hvanish : ∀ {m d : ℕ}, m < d → PowerSeries.coeff m (BZ ^ d) = 0 := fun {m d} hmd =>
    PowerSeries.X_pow_dvd_iff.1
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp [BZ])) d) m hmd
  -- `B` is the `algebraMap`-image of `BZ`
  have hBmap : B = PowerSeries.map (algebraMap ℤ_[p] (integerRing K)) BZ := by
    change (1 + PowerSeries.X) ^ p - 1
      = PowerSeries.map (algebraMap ℤ_[p] (integerRing K)) ((1 + PowerSeries.X) ^ p - 1)
    simp [map_sub, map_pow, map_add]
  have hcoeffB : ∀ (m d : ℕ), PowerSeries.coeff m (B ^ d)
      = algebraMap ℤ_[p] (integerRing K) (PowerSeries.coeff m (BZ ^ d)) := fun m d => by
    rw [hBmap, ← map_pow, PowerSeries.coeff_map]
  refine PowerSeries.ext fun n => ?_
  rw [phiSeries, PowerSeries.coeff_subst' hsub,
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [hcoeffB, hvanish (by omega), map_zero, smul_zero]))]
  -- the `ℤ_p`-level Chu–Vandermonde for `mahler n (p * k)`
  have key : ∀ k : ℕ, mahler n ((p : ℤ_[p]) * (k : ℤ_[p]))
      = ∑ d ∈ Finset.range (n + 1),
          PowerSeries.coeff n (BZ ^ d) * ((k.choose d : ℕ) : ℤ_[p]) := by
    intro k
    have lhs_eq : mahler n ((p : ℤ_[p]) * (k : ℤ_[p]))
        = PowerSeries.coeff n ((BZ + 1) ^ k) := by
      have hpk : ((p : ℤ_[p]) * (k : ℤ_[p])) = ((p * k : ℕ) : ℤ_[p]) := by push_cast; ring
      have hb1 : (BZ + 1 : PowerSeries ℤ_[p]) = (1 + PowerSeries.X) ^ p := by
        change ((1 + PowerSeries.X) ^ p - 1) + 1 = (1 + PowerSeries.X) ^ p
        rw [sub_add_cancel]
      rw [hpk, mahler_natCast_eq, hb1, ← pow_mul, ← binomialSeries_nat (R := ℤ_[p]),
        binomialSeries_coeff, Ring.choose_natCast, smul_eq_mul, mul_one]
    have expand : PowerSeries.coeff n ((BZ + 1) ^ k)
        = ∑ d ∈ Finset.range (k + 1),
            PowerSeries.coeff n (BZ ^ d) * ((k.choose d : ℕ) : ℤ_[p]) := by
      rw [add_pow, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [one_pow, mul_one, ← map_natCast (PowerSeries.C (R := ℤ_[p])) (k.choose d),
        PowerSeries.coeff_mul_C]
    rw [lhs_eq, expand]
    rcases le_total k n with hkn | hnk
    · refine Finset.sum_subset (by intro d hd; simp only [Finset.mem_range] at *; omega)
        (fun d hd hnd => ?_)
      simp only [Finset.mem_range, not_lt] at hnd
      simp only [Finset.mem_range] at hd
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    · refine (Finset.sum_subset (by intro d hd; simp only [Finset.mem_range] at *; omega)
        (fun d hd hnd => ?_)).symm
      simp only [Finset.mem_range, not_lt] at hnd
      rw [hvanish (by omega), zero_mul]
  -- transport the function identity through the algebra map
  have hfun : (mahlerCM p K n).comp (PadicMeasure.mulCM p (p : ℤ_[p]))
      = ∑ d ∈ Finset.range (n + 1),
          (PowerSeries.coeff n (B ^ d)) • (mahlerCM p K d) := by
    apply ContinuousMap.coe_injective
    refine PadicInt.denseRange_natCast.equalizer (map_continuous _) (map_continuous _)
      (funext fun k => ?_)
    change algebraMap ℤ_[p] (integerRing K) (mahler n ((p : ℤ_[p]) * (k : ℤ_[p]))) = _
    rw [key k, map_sum, Function.comp_apply, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ContinuousMap.coe_smul, Pi.smul_apply, mahlerCM_apply, mahler_natCast_eq,
      smul_eq_mul, hcoeffB, map_mul, map_natCast]
  rw [coeff_mahlerTransform]
  change μ ((mahlerCM p K n).comp (PadicMeasure.mulCM p (p : ℤ_[p]))) = _
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, smul_eq_mul, coeff_mahlerTransform, smul_eq_mul, mul_comm]

omit [CompleteSpace K] in
/-- `𝓐_{δ_i} = (1+T)^i`. -/
lemma mahlerTransform_dirac_natCast (i : ℕ) :
    mahlerTransform p K (dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]))
      = (1 + PowerSeries.X) ^ i := by
  rw [mahlerTransform_dirac, binomialSeries_nat, map_pow, map_add, map_one,
    PowerSeries.map_X]

/-- A translate of a `φ`-image by a unit is supported off `pℤ_p`, hence killed
by `ψ`: `ψ(δ_a * φν) = 0` when `‖a‖ = 1`. -/
lemma psi_dirac_mul_phi_eq_zero {a : ℤ_[p]} (ha : ‖a‖ = 1) (ν : MeasureR K ℤ_[p]) :
    MeasureR.psi p K (dirac K ℤ_[p] a * MeasureR.phi p K ν) = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [show MeasureR.psi p K (dirac K ℤ_[p] a * MeasureR.phi p K ν) f
      = (dirac K ℤ_[p] a * MeasureR.phi p K ν)
          (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
            * f.comp (PadicMeasure.shiftDiv p)) from rfl,
    mul_apply, dirac_apply, convInner_apply]
  rw [LinearMap.zero_apply, MeasureR.phi, pushforward_apply]
  rw [show ((charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
        * f.comp (PadicMeasure.shiftDiv p)).comp
          ⟨fun y => a + y, by fun_prop⟩).comp (PadicMeasure.mulCM p (p : ℤ_[p]))
      = (0 : C(ℤ_[p], integerRing K)) from ?_, map_zero]
  refine ContinuousMap.ext fun z => ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply, charFnCM_apply,
    PadicMeasure.mulCM, ContinuousMap.coe_mk, ContinuousMap.coe_zero, Pi.zero_apply]
  have hnotmem : (a + (p : ℤ_[p]) * z) ∉ {y : ℤ_[p] | ‖y‖ < 1} := by
    simp only [Set.mem_setOf_eq, not_lt]
    have hpz : ‖(p : ℤ_[p]) * z‖ < 1 := PadicMeasure.mem_pZp_of_mul p
    by_contra hlt
    push Not at hlt
    have hane : ‖a‖ ≤ max ‖a + (p : ℤ_[p]) * z‖ ‖(p : ℤ_[p]) * z‖ := by
      calc ‖a‖ = ‖(a + (p : ℤ_[p]) * z) + -((p : ℤ_[p]) * z)‖ := by
            rw [add_neg_cancel_right]
        _ ≤ max ‖a + (p : ℤ_[p]) * z‖ ‖-((p : ℤ_[p]) * z)‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖a + (p : ℤ_[p]) * z‖ ‖(p : ℤ_[p]) * z‖ := by rw [norm_neg]
    rw [ha] at hane
    exact absurd (hane.trans_lt (max_lt hlt hpz)) (lt_irrefl _)
  rw [Set.indicator_of_notMem hnotmem, zero_mul]

/-- The unit-translate norm fact for digits: `‖(i:ℤ_[p]) − (j:ℤ_[p])‖ = 1` for
distinct `i, j < p`. -/
lemma norm_natCast_sub_natCast_eq_one {i j : ℕ} (hi : i < p) (hj : j < p)
    (hij : i ≠ j) : ‖((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p])‖ = 1 := by
  have hkey : ∀ m : ℕ, 0 < m → m < p → ‖((m : ℕ) : ℤ_[p])‖ = 1 :=
      fun m hm0 hmp => by
    rw [PadicInt.norm_natCast_eq_one_iff, hp.out.coprime_iff_not_dvd]
    exact fun hdvd => absurd (Nat.le_of_dvd hm0 hdvd) (by omega)
  rcases le_total j i with hle | hle
  · have hsub : ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) = ((i - j : ℕ) : ℤ_[p]) := by
      rw [Nat.cast_sub hle]
    rw [hsub]
    exact hkey (i - j) (by omega) (by omega)
  · have hsub : ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) = -(((j - i : ℕ) : ℤ_[p])) := by
      rw [Nat.cast_sub hle]; ring
    rw [hsub, norm_neg]
    exact hkey (j - i) (by omega) (by omega)

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- The residue partition `ℤ_p = ⊔_{i<p} (i + pℤ_p)`, coefficient form: for each
`y`, exactly one digit `i < p` lies in the same residue, so the indicator sum is
`1`. -/
lemma sum_charFn_pZp_sub_natCast (y : ℤ_[p]) :
    ∑ i : Fin p, (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
        (y - ((i : ℕ) : ℤ_[p]))) = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- the unique digit in `Fin p`
  set c : Fin p := ⟨(PadicInt.toZModPow 1 y).val,
    by simpa [pow_one] using ZMod.val_lt (PadicInt.toZModPow 1 y)⟩ with hc
  -- the membership criterion `y - i ∈ pℤ_p` holds exactly for `i = c`
  have hcrit : ∀ i : Fin p,
      (y - ((i : ℕ) : ℤ_[p])) ∈ {z : ℤ_[p] | ‖z‖ < 1} ↔ i = c := by
    intro i
    have hdvd_ker : (p : ℤ_[p]) ∣ (y - ((i : ℕ) : ℤ_[p]))
        ↔ PadicInt.toZModPow 1 (y - ((i : ℕ) : ℤ_[p])) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton]
    rw [Set.mem_setOf_eq, PadicInt.norm_lt_one_iff_dvd, hdvd_ker,
      map_sub, sub_eq_zero, map_natCast]
    have hival : ((i : ℕ) : ZMod (p ^ 1)).val = (i : ℕ) :=
      ZMod.val_natCast_of_lt (by rw [pow_one]; exact i.2)
    constructor
    · intro h
      refine Fin.ext ?_
      rw [hc, ← hival, ← h]
    · intro h
      have hi : (i : ℕ) = (PadicInt.toZModPow 1 y).val := by rw [h, hc]
      rw [hi, ZMod.natCast_val, ZMod.cast_id]
  have hiff : ∀ i : Fin p,
      (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p) (y - ((i : ℕ) : ℤ_[p])))
        = if i = c then (1 : integerRing K) else 0 := by
    intro i
    rw [charFnCM_apply]
    by_cases hmem : (y - ((i : ℕ) : ℤ_[p])) ∈ {z : ℤ_[p] | ‖z‖ < 1}
    · rw [Set.indicator_of_mem hmem, Pi.one_apply, if_pos ((hcrit i).1 hmem)]
    · rw [Set.indicator_of_notMem hmem, if_neg (fun h => hmem ((hcrit i).2 h))]
  simp_rw [hiff]
  rw [Finset.sum_ite_eq' Finset.univ c (fun _ => (1 : integerRing K))]
  simp

/-- Digit extraction: `ψ(δ_{-j} * Σ_i δ_i φ(ν_i)) = ν_j` (the `i = j` term gives
`ψφ = id`; the others are unit-translates killed by `ψ`). -/
lemma psi_dirac_neg_mul_sum (ν : Fin p → MeasureR K ℤ_[p]) (j : Fin p) :
    MeasureR.psi p K (dirac K ℤ_[p] (-((j : ℕ) : ℤ_[p]))
        * ∑ i : Fin p, dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (ν i))
      = ν j := by
  rw [Finset.mul_sum, MeasureR.psi_sum]
  rw [Finset.sum_eq_single j]
  · rw [← mul_assoc, dirac_mul_dirac, neg_add_cancel, ← MeasureR.one_def, one_mul,
      MeasureR.psi_phi]
  · intro i _ hij
    rw [← mul_assoc, dirac_mul_dirac]
    refine psi_dirac_mul_phi_eq_zero p K ?_ (ν i)
    rw [show -((j : ℕ) : ℤ_[p]) + ((i : ℕ) : ℤ_[p])
        = ((i : ℕ) : ℤ_[p]) - ((j : ℕ) : ℤ_[p]) by ring]
    exact norm_natCast_sub_natCast_eq_one p i.2 j.2 (fun h => hij (Fin.ext h))
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The measure-level `p`-residue digit decomposition: every measure is
uniquely `Σ_{i<p} δ_i * φ(ν_i)`. -/
theorem existsUnique_measure_digits (μ : MeasureR K ℤ_[p]) :
    ∃! ν : Fin p → MeasureR K ℤ_[p],
      μ = ∑ i : Fin p,
        dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (ν i) := by
  refine ⟨fun j => MeasureR.psi p K (dirac K ℤ_[p] (-((j : ℕ) : ℤ_[p])) * μ), ?_, ?_⟩
  · -- existence
    refine LinearMap.ext fun f => ?_
    -- the digit-`i` reconstruction function `y ↦ 1_{pℤ_p}(y - i)·f(y)`
    set hfun : Fin p → C(ℤ_[p], integerRing K) := fun i =>
      (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)).comp
          ⟨fun y => y - ((i : ℕ) : ℤ_[p]), by fun_prop⟩ * f with hhfun
    -- each term `(δ_i * φ(ψ(δ_{-i}μ))) f = μ(hfun i)` via `φψ = Res_{pℤ_p}`
    have hterm : ∀ i : Fin p,
        (dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (MeasureR.psi p K
            (dirac K ℤ_[p] (-((i : ℕ) : ℤ_[p])) * μ))) f
          = μ (hfun i) := by
      intro i
      rw [MeasureR.phi_psi, dirac_mul_eq_pushforward, pushforward_apply,
        MeasureR.res, cmul_apply, dirac_mul_eq_pushforward, pushforward_apply]
      refine congrArg μ (ContinuousMap.ext fun y => ?_)
      simp only [hhfun, ContinuousMap.mul_apply, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, charFnCM_apply]
      rw [show -((i : ℕ) : ℤ_[p]) + y = y - ((i : ℕ) : ℤ_[p]) by ring,
        show ((i : ℕ) : ℤ_[p]) + (y - ((i : ℕ) : ℤ_[p])) = y by ring]
    rw [LinearMap.coe_sum, Finset.sum_apply]
    simp_rw [hterm]
    rw [← map_sum]
    refine congrArg μ (ContinuousMap.ext fun y => ?_)
    rw [ContinuousMap.coe_sum, Finset.sum_apply]
    simp only [hhfun, ContinuousMap.mul_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    rw [← Finset.sum_mul,
      show ∑ i : Fin p, (charFnCM K ℤ_[p] (PadicMeasure.isClopen_pZp p)
          (y - ((i : ℕ) : ℤ_[p]))) = 1 from sum_charFn_pZp_sub_natCast p K y, one_mul]
  · -- uniqueness
    intro ν hν
    funext j
    rw [hν]
    exact (psi_dirac_neg_mul_sum p K ν j).symm

omit [CompleteSpace K] in
/-- `𝓐` is additive over finite sums (the linear-map form, repackaged). -/
private lemma mahlerTransform_sum {ι : Type*} (s : Finset ι)
    (m : ι → MeasureR K ℤ_[p]) :
    mahlerTransform p K (∑ i ∈ s, m i) = ∑ i ∈ s, mahlerTransform p K (m i) :=
  map_sum (mahlerTransformₗ p K) m s

/-- The Mahler transform intertwines the measure-level and series-level digit
decompositions: `𝓐_{Σ δ_i φ(ν_i)} = Σ (1+T)^i · phiSeries(𝓐_{ν_i})`. -/
lemma mahlerTransform_sum_dirac_mul_phi (ν : Fin p → MeasureR K ℤ_[p]) :
    mahlerTransform p K (∑ i : Fin p,
        dirac K ℤ_[p] ((i : ℕ) : ℤ_[p]) * MeasureR.phi p K (ν i))
      = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
          * phiSeries p (mahlerTransform p K (ν i)) := by
  rw [mahlerTransform_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mahlerTransform_mul, mahlerTransform_dirac_natCast, mahlerTransform_phi]

/-- W6b-b1 (integral form): the digit decomposition over `integerRing K`. The
frozen general-`CommRing` statement is false (replan R6 W6b-b1'); this is the
`p`-adically-integral theorem feeding `psiSeries`. -/
theorem existsUnique_digits (F : PowerSeries (integerRing K)) :
    ∃! G : Fin p → PowerSeries (integerRing K), IsDigitDecomp p F G := by
  obtain ⟨ν, hν, hνuniq⟩ := existsUnique_measure_digits p K (ofPowerSeries p K F)
  refine ⟨fun i => mahlerTransform p K (ν i), ?_, ?_⟩
  · -- the transported family is a digit decomposition of `F`
    change F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
        * phiSeries p (mahlerTransform p K (ν i))
    rw [← mahlerTransform_sum_dirac_mul_phi, ← hν, mahlerTransform_ofPowerSeries]
  · -- uniqueness, pulled back to the measure level
    intro G hG
    have hmeas : ofPowerSeries p K F
        = ∑ i : Fin p, dirac K ℤ_[p] ((i : ℕ) : ℤ_[p])
            * MeasureR.phi p K (ofPowerSeries p K (G i)) := by
      apply mahlerTransform_injective
      rw [mahlerTransform_ofPowerSeries, mahlerTransform_sum_dirac_mul_phi]
      simp_rw [mahlerTransform_ofPowerSeries]
      exact hG
    have hνeq := hνuniq (fun i => ofPowerSeries p K (G i)) hmeas
    funext i
    rw [show G i = mahlerTransform p K (ofPowerSeries p K (G i)) from
      (mahlerTransform_ofPowerSeries (G i)).symm, ← congrFun hνeq i]

/-- Over `integerRing K`, `psiSeries` is the `0`-th digit of *any* digit
decomposition (they all agree by `existsUnique_digits`). -/
theorem psiSeries_eq_of_isDigitDecomp {F : PowerSeries (integerRing K)}
    {G : Fin p → PowerSeries (integerRing K)} (hG : IsDigitDecomp p F G) :
    psiSeries p F = G 0 :=
  psiSeries_eq_of_unique p (existsUnique_digits p K F) hG

/-- The canonical digit family of `phiSeries p G`: `(G, 0, …, 0)`. -/
theorem psiSeries_phi (G : PowerSeries (integerRing K)) :
    psiSeries p (phiSeries p G) = G := by
  refine psiSeries_eq_of_isDigitDecomp p K
    (G := fun i => if i = 0 then G else 0) ?_
  change phiSeries p G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (if i = 0 then G else 0)
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp
  · intro i _ hi0
    rw [if_neg hi0, phiSeries_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin p)) h

omit [hp : Fact p.Prime] [CompleteSpace K] in
/-- `φ(C a) = C a`. -/
lemma phiSeries_C (a : integerRing K) :
    phiSeries p (PowerSeries.C a) = PowerSeries.C a := by
  rw [phiSeries]; exact PowerSeries.subst_C a

@[simp]
theorem psiSeries_C (a : integerRing K) :
    psiSeries p (PowerSeries.C a) = PowerSeries.C a := by
  conv_lhs => rw [← phiSeries_C p K a]
  rw [psiSeries_phi]

theorem psiSeries_add (F G : PowerSeries (integerRing K)) :
    psiSeries p (F + G) = psiSeries p F + psiSeries p G := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits p K F
  obtain ⟨GG, hGG, -⟩ := existsUnique_digits p K G
  rw [psiSeries_eq_of_isDigitDecomp p K hGF, psiSeries_eq_of_isDigitDecomp p K hGG]
  refine psiSeries_eq_of_isDigitDecomp p K (G := fun i => GF i + GG i) ?_
  change F + G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (GF i + GG i)
  rw [hGF, hGG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries, phiSeries,
    PowerSeries.subst_add (hasSubst_one_add_X_pow_sub_one p), mul_add]

theorem psiSeries_C_mul (a : integerRing K) (F : PowerSeries (integerRing K)) :
    psiSeries p (PowerSeries.C a * F)
      = PowerSeries.C a * psiSeries p F := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits p K F
  rw [psiSeries_eq_of_isDigitDecomp p K hGF]
  refine psiSeries_eq_of_isDigitDecomp p K (G := fun i => PowerSeries.C a * GF i) ?_
  change PowerSeries.C a * F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (PowerSeries.C a * GF i)
  rw [hGF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries,
    PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p),
    show ((PowerSeries.C a).subst ((1 + PowerSeries.X) ^ p - 1)
        : PowerSeries (integerRing K)) = PowerSeries.C a from PowerSeries.subst_C a]
  ring

/-- W6b-b8: `ψ` commutes with coefficient maps (out of `integerRing K`), on
the locus where the image again has a unique digit decomposition (always the
case when `S` is itself such an integral coefficient ring; the hypothesis
makes the statement sound over the junk-totalised `psiSeries` — replan R6
W6b-b1'). -/
theorem psiSeries_map {S : Type*} [CommRing S] (f : integerRing K →+* S)
    (F : PowerSeries (integerRing K))
    (hS : ∃! G : Fin p → PowerSeries S, IsDigitDecomp p (PowerSeries.map f F) G) :
    psiSeries p (PowerSeries.map f F)
      = PowerSeries.map f (psiSeries p F) := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits p K F
  rw [psiSeries_eq_of_isDigitDecomp p K hGF,
    psiSeries_eq_of_unique p hS (isDigitDecomp_map p f hGF)]

end integral

section bridge

variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

/-- W6b-b4: the formal `ψ` is the series-side of the measure-level `ψ`
through the Mahler transform. -/
theorem mahlerTransform_psi (μ : MeasureR K ℤ_[p]) :
    MeasureR.mahlerTransform p K (MeasureR.psi p K μ)
      = psiSeries p (MeasureR.mahlerTransform p K μ) := by
  -- the measure-level digit family `ν j = ψ(δ_{-j}·μ)` from the residue decomposition
  obtain ⟨ν, hν, -⟩ := existsUnique_measure_digits p K μ
  -- the `0`-th digit is `ψ μ` (the `δ_0`-translate is trivial): use uniqueness against the
  -- explicit witness `j ↦ ψ(δ_{-j}·μ)`
  have hν0 : ν 0 = MeasureR.psi p K μ := by
    have := psi_dirac_neg_mul_sum p K ν 0
    rw [← hν, show (-(((0 : Fin p) : ℕ) : ℤ_[p])) = 0 by simp, ← MeasureR.one_def,
      one_mul] at this
    exact this.symm
  -- transport: `𝓐_μ = Σ_i (1+T)^i·φ(𝓐_{ν i})`, so `(𝓐_{ν i})` is its digit decomposition
  have hdig : IsDigitDecomp p (MeasureR.mahlerTransform p K μ)
      (fun i => MeasureR.mahlerTransform p K (ν i)) := by
    rw [IsDigitDecomp]
    conv_lhs => rw [hν]
    exact mahlerTransform_sum_dirac_mul_phi p K ν
  rw [psiSeries_eq_of_isDigitDecomp p K hdig, hν0]

variable {K}

/-- W6b-b5: junk-total evaluation of a `K`-coefficient power series
(meaningful when the terms are summable). -/
noncomputable def seriesEval (F : PowerSeries K) (z : K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n F * z ^ n

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem seriesEval_zero_arg (F : PowerSeries K) :
    seriesEval F (0 : K) = PowerSeries.constantCoeff F := by
  rw [seriesEval, tsum_eq_single 0 fun n hn => by rw [zero_pow hn, mul_zero], pow_zero,
    mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply]

omit [NormedAlgebra ℚ_[p] K] in
omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `seriesEval` is additive on series whose evaluations converge. -/
theorem seriesEval_add {F H : PowerSeries K} {z : K}
    (hF : Summable fun n : ℕ => PowerSeries.coeff n F * z ^ n)
    (hH : Summable fun n : ℕ => PowerSeries.coeff n H * z ^ n) :
    seriesEval (F + H) z = seriesEval F z + seriesEval H z := by
  rw [seriesEval, seriesEval, seriesEval, ← hF.tsum_add hH]
  exact tsum_congr fun n => by rw [map_add, add_mul]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `seriesEval` negates. -/
theorem seriesEval_neg (F : PowerSeries K) (z : K) :
    seriesEval (-F) z = -seriesEval F z := by
  rw [seriesEval, seriesEval, ← tsum_neg]
  exact tsum_congr fun n => by rw [map_neg, neg_mul]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `seriesEval` subtracts on series whose evaluations converge. -/
theorem seriesEval_sub {F H : PowerSeries K} {z : K}
    (hF : Summable fun n : ℕ => PowerSeries.coeff n F * z ^ n)
    (hH : Summable fun n : ℕ => PowerSeries.coeff n H * z ^ n) :
    seriesEval (F - H) z = seriesEval F z - seriesEval H z := by
  rw [sub_eq_add_neg, seriesEval_add hF (hH.neg.congr fun n => by rw [map_neg, neg_mul]),
    seriesEval_neg, sub_eq_add_neg]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `seriesEval` of a constant series is that constant. -/
@[simp]
theorem seriesEval_C (a : K) (z : K) : seriesEval (PowerSeries.C a) z = a := by
  rw [seriesEval, tsum_eq_single 0 fun n hn => by
    rw [PowerSeries.coeff_C, if_neg hn, zero_mul], PowerSeries.coeff_zero_C, pow_zero, mul_one]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `seriesEval (C a · F) z = a · seriesEval F z`. -/
theorem seriesEval_C_mul (a : K) (F : PowerSeries K) (z : K) :
    seriesEval (PowerSeries.C a * F) z = a * seriesEval F z := by
  rw [seriesEval, seriesEval, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [PowerSeries.coeff_C_mul, mul_assoc]

/-- An ultrametric normed field is a nonarchimedean ring (the ring upgrade of
`IsUltrametricDist.nonarchimedeanAddGroup`). -/
instance : NonarchimedeanRing K where
  toIsTopologicalRing := inferInstance
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `(1+X)^p − 1` powers vanish below degree `n`: `coeff k (S^n) = 0` for `k < n`
(constant coefficient `0`, so `X^n ∣ S^n`). -/
theorem coeff_substSeries_pow_eq_zero {k n : ℕ} (hkn : k < n) :
    PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) = 0 :=
  PowerSeries.X_pow_dvd_iff.1
    (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp)) n) k hkn

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- The inner finite evaluation `∑' coeff(Sⁿ)·zᵏ = ((1+z)^p − 1)ⁿ`: since `Sⁿ` is a
polynomial, the sum is its evaluation at `z`. -/
theorem tsum_coeff_substSeries_pow (z : K) (n : ℕ) :
    (∑' k : ℕ, PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) * z ^ k)
      = ((1 + z) ^ p - 1) ^ n := by
  -- `S = (1+X)^p − 1` as a polynomial; `Sⁿ` has degree `≤ p·n`
  set Sp : Polynomial K := (1 + Polynomial.X) ^ p - 1 with hSp
  have hSpc : ((Sp ^ n : Polynomial K) : PowerSeries K)
      = ((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n := by
    rw [Polynomial.coe_pow, hSp, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add,
      Polynomial.coe_one, Polynomial.coe_X]
  have hdegSp : Sp.natDegree ≤ p := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp only [Polynomial.natDegree_one, max_le_iff, zero_le, and_true]
    refine Polynomial.natDegree_pow_le.trans (mul_le_of_le_one_right (by positivity) ?_)
    refine (Polynomial.natDegree_add_le 1 Polynomial.X).trans ?_
    simp [Polynomial.natDegree_X]
  have hdeg : (Sp ^ n).natDegree < p * n + 1 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans ?_) (lt_add_one _)
    rw [mul_comm p n]
    exact Nat.mul_le_mul_left n hdegSp
  have hcoeffeq : ∀ k, PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n)
      = (Sp ^ n).coeff k := fun k => by rw [← hSpc, Polynomial.coeff_coe]
  rw [tsum_eq_sum (s := Finset.range (p * n + 1)) fun k hk => by
    rw [hcoeffeq, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le hdeg (by simp only [Finset.mem_range, not_lt] at hk; omega)), zero_mul]]
  simp_rw [hcoeffeq]
  rw [← Polynomial.eval_eq_sum_range' hdeg, Polynomial.eval_pow, hSp, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `(1+X)^p − 1` powers vanish above degree `p·n`: `coeff k (Sⁿ) = 0` for `p·n < k`. -/
theorem coeff_substSeries_pow_eq_zero_ge {k n : ℕ} (hkn : p * n < k) :
    PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) = 0 := by
  set Sp : Polynomial K := (1 + Polynomial.X) ^ p - 1 with hSp
  have hSpc : ((Sp ^ n : Polynomial K) : PowerSeries K)
      = ((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n := by
    rw [Polynomial.coe_pow, hSp, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add,
      Polynomial.coe_one, Polynomial.coe_X]
  have hdegSp : Sp.natDegree ≤ p := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp only [Polynomial.natDegree_one, max_le_iff, zero_le, and_true]
    refine Polynomial.natDegree_pow_le.trans (mul_le_of_le_one_right (by positivity) ?_)
    refine (Polynomial.natDegree_add_le 1 Polynomial.X).trans ?_
    simp [Polynomial.natDegree_X]
  have hdeg : (Sp ^ n).natDegree < k := by
    refine lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans ?_) hkn
    rw [mul_comm p n]
    exact Nat.mul_le_mul_left n hdegSp
  rw [← hSpc, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `k ↦ coeff k (Sⁿ)·zᵏ` has finite support (`Sⁿ` is a polynomial), hence is summable. -/
theorem summable_coeff_substSeries_pow (z : K) (n : ℕ) :
    Summable fun k : ℕ =>
      PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) * z ^ k := by
  refine summable_of_ne_finset_zero (s := Finset.range (p * n + 1)) fun k hk => ?_
  rw [coeff_substSeries_pow_eq_zero_ge p (by simp only [Finset.mem_range, not_lt] at hk; omega),
    zero_mul]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- The K-native evaluation bridge for `φ`: under summability of the total
`ℕ × ℕ` product family, the evaluation of `phiSeries p G` at `z` is the
evaluation of `G` at `(1+z)^p − 1`. -/
theorem seriesEval_phi_of_summable_prod (G : PowerSeries K) (z : K)
    (hprod : Summable fun nk : ℕ × ℕ =>
      PowerSeries.coeff nk.1 G
        * PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)
        * z ^ nk.2) :
    seriesEval (phiSeries p G) z
      = ∑' n : ℕ, PowerSeries.coeff n G * ((1 + z) ^ p - 1) ^ n := by
  have hS := hasSubst_one_add_X_pow_sub_one (R := K) p
  -- the total family `T n k = coeff n G · coeff k (Sⁿ) · zᵏ`
  let T : ℕ → ℕ → K := fun n k =>
    PowerSeries.coeff n G
      * PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) * z ^ k
  have hprod' : Summable (Function.uncurry T) := hprod
  -- the LHS coefficientwise: `coeff k (G.subst S) · zᵏ = ∑' n, T n k`
  have hLHScoeff : ∀ k : ℕ,
      PowerSeries.coeff k (phiSeries p G) * z ^ k = ∑' n : ℕ, T n k := by
    intro k
    rw [phiSeries, PowerSeries.coeff_subst' hS,
      finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (k + 1)) (by
        intro n hn
        simp only [Function.mem_support] at hn
        by_contra hmem
        simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
        exact hn (by rw [coeff_substSeries_pow_eq_zero p (by omega), smul_zero]))]
    rw [Finset.sum_mul, tsum_eq_sum (s := Finset.range (k + 1)) fun n hn => by
      change PowerSeries.coeff n G * _ * z ^ k = 0
      rw [coeff_substSeries_pow_eq_zero p
        (show k < n by simp only [Finset.mem_range, not_lt] at hn; omega), mul_zero, zero_mul]]
    refine Finset.sum_congr rfl fun n _ => ?_
    change PowerSeries.coeff n G • _ * z ^ k = _
    rw [smul_eq_mul]
  -- assemble: `seriesEval (φ G) z = ∑'_k ∑'_n T n k = ∑'_n ∑'_k T n k`
  rw [seriesEval]
  simp_rw [hLHScoeff]
  rw [Summable.tsum_comm hprod']
  refine tsum_congr fun n => ?_
  -- the inner sum: `∑'_k T n k = coeff n G · ((1+z)^p − 1)ⁿ`
  change (∑' k : ℕ, PowerSeries.coeff n G
      * PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) * z ^ k) = _
  rw [show (fun k : ℕ => PowerSeries.coeff n G
        * PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) * z ^ k)
      = fun k : ℕ => PowerSeries.coeff n G
        * (PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n) * z ^ k) from by
    funext k; ring, (summable_coeff_substSeries_pow p z n).tsum_mul_left,
    tsum_coeff_substSeries_pow]

variable (K) in
/-- The `K`-mapped Mahler transform (the NonTame `map subtype` idiom; home
moved here from ValuesAtOne at the R6.6 realignment). -/
noncomputable def mahlerK (μ : MeasureR K ℤ_[p]) : PowerSeries K :=
  PowerSeries.map (integerRing K).subtype (MeasureR.mahlerTransform p K μ)

omit [CompleteSpace K] in
/-- `mahlerK` is additive on differences. -/
theorem mahlerK_sub (μ ν : MeasureR K ℤ_[p]) :
    mahlerK p K (μ - ν) = mahlerK p K μ - mahlerK p K ν := by
  rw [mahlerK, mahlerK, mahlerK, MeasureR.mahlerTransform_sub, map_sub]

omit [CompleteSpace K] in
/-- The `K`-level `φ`-transport: `𝓐_{φμ}^K = phiSeries 𝓐_μ^K` (map the
integral `mahlerTransform_phi` through the `subtype` coefficient map). -/
theorem mahlerK_phi (μ : MeasureR K ℤ_[p]) :
    mahlerK p K (MeasureR.phi p K μ) = phiSeries p (mahlerK p K μ) := by
  rw [mahlerK, mahlerTransform_phi, map_phiSeries, mahlerK]

omit [CompleteSpace K] in
/-- The `K`-mapped Mahler coefficients are integral: `‖coeff n (mahlerK μ)‖ ≤ 1`. -/
theorem norm_coeff_mahlerK_le_one (μ : MeasureR K ℤ_[p]) (n : ℕ) :
    ‖PowerSeries.coeff n (mahlerK p K μ)‖ ≤ 1 := by
  rw [mahlerK, PowerSeries.coeff_map]
  exact (PowerSeries.coeff n (MeasureR.mahlerTransform p K μ)).2

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- The coefficients of `(1+X)^p − 1` powers are integral: `‖coeff k (Sⁿ)‖ ≤ 1` (they are
`ℤ`-combinations of binomial coefficients, of norm `≤ 1` in the ultrametric field). -/
theorem norm_coeff_substSeries_pow_le_one (k n : ℕ) :
    ‖PowerSeries.coeff k (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n)‖ ≤ 1 := by
  have hmap : ((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ n
      = PowerSeries.map (Int.castRingHom K)
        (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ) ^ n) := by
    simp only [map_pow, map_sub, map_add, map_one, PowerSeries.map_X]
  rw [hmap, PowerSeries.coeff_map, Int.coe_castRingHom]
  exact IsUltrametricDist.norm_intCast_le_one _ _

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- `n ↦ (n + 1)·rⁿ → 0` for `0 ≤ r < 1` (linear-times-geometric decay). -/
private theorem tendsto_natCast_succ_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h2 : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  simpa only [add_mul, one_mul, add_zero] using h1.add h2

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- For an `‖·‖ ≤ 1`-coefficient series `G` and `‖z‖ < 1`, the total `ℕ × ℕ` family of
`φ`-evaluation terms is summable (uniform geometric `‖T n k‖ ≤ ‖z‖ᵏ`, support `n ≤ k`). -/
theorem summable_prod_of_norm_coeff_le_one {G : PowerSeries K} {z : K}
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ 1) (hz : ‖z‖ < 1) :
    Summable fun nk : ℕ × ℕ =>
      PowerSeries.coeff nk.1 G
        * PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)
        * z ^ nk.2 := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  rw [Filter.eventually_cofinite]
  -- the bound `‖T n k‖ ≤ ‖z‖ᵏ`, with support in `n ≤ k`
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz).eventually_lt_const
    hε).exists_forall_of_atTop
  refine Set.Finite.subset (Set.Finite.prod (Set.finite_Iio (N + 1)) (Set.finite_Iio (N + 1)))
    fun nk hnk => ?_
  simp only [Set.mem_setOf_eq, not_lt] at hnk
  have hbd : ‖PowerSeries.coeff nk.1 G
      * PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)
      * z ^ nk.2‖ ≤ ‖z‖ ^ nk.2 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖PowerSeries.coeff nk.1 G‖
          * ‖PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)‖
          * ‖z‖ ^ nk.2
        ≤ 1 * 1 * ‖z‖ ^ nk.2 :=
          mul_le_mul (mul_le_mul (hG nk.1) (norm_coeff_substSeries_pow_le_one p nk.2 nk.1)
            (norm_nonneg _) zero_le_one) le_rfl (by positivity) (by positivity)
      _ = ‖z‖ ^ nk.2 := by ring
  have hk : nk.2 < N + 1 := by
    by_contra hge
    rw [not_lt] at hge
    exact absurd (lt_of_le_of_lt (le_trans hnk hbd) (hN nk.2 (by omega))) (lt_irrefl ε)
  have hn : nk.1 < N + 1 := by
    by_contra hge
    rw [not_lt] at hge
    have hz0 : ‖PowerSeries.coeff nk.1 G
        * PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)
        * z ^ nk.2‖ = 0 := by
      rw [norm_mul, norm_mul,
        coeff_substSeries_pow_eq_zero p (show nk.2 < nk.1 by omega), norm_zero, mul_zero,
        zero_mul]
    rw [hz0] at hnk
    exact absurd (lt_of_lt_of_le hε hnk) (lt_irrefl _)
  exact Set.mem_prod.2 ⟨hn, hk⟩

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- Linear-growth variant of `summable_prod_of_norm_coeff_le_one`: for `‖coeff n G‖ ≤
C·(n+1)` and `‖z‖ < 1`, the `φ`-evaluation product family is summable (`‖T n k‖ ≤
C·(k+1)·‖z‖ᵏ` on the support `n ≤ k`). Feeds `seriesEval_phi_at_root_of_summable` for the
antiderivative series `C₁`. -/
theorem summable_prod_of_norm_coeff_le_linear {G : PowerSeries K} {C : ℝ}
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ C * ((n : ℝ) + 1)) {z : K} (hz : ‖z‖ < 1) :
    Summable fun nk : ℕ × ℕ =>
      PowerSeries.coeff nk.1 G
        * PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)
        * z ^ nk.2 := by
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hG 0)
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have htend : Filter.Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * ‖z‖ ^ n)) Filter.atTop (nhds 0) :=
    by simpa using (tendsto_natCast_succ_mul_pow (norm_nonneg z) hz).const_mul C
  obtain ⟨N, hN⟩ := (htend.eventually_lt_const hε).exists_forall_of_atTop
  refine Set.Finite.subset (Set.Finite.prod (Set.finite_Iio (N + 1)) (Set.finite_Iio (N + 1)))
    fun nk hnk => ?_
  simp only [Set.mem_setOf_eq, not_lt] at hnk
  -- on the support `n ≤ k`, `‖T n k‖ ≤ C·(k+1)·‖z‖ᵏ`
  by_cases hnk1 : nk.2 < nk.1
  · -- off-support term vanishes; `ε ≤ 0`, contradiction
    exfalso
    rw [norm_mul, norm_mul, coeff_substSeries_pow_eq_zero p hnk1, norm_zero, mul_zero,
      zero_mul] at hnk
    exact absurd (lt_of_lt_of_le hε hnk) (lt_irrefl _)
  rw [not_lt] at hnk1
  have hbd : ‖PowerSeries.coeff nk.1 G
      * PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)
      * z ^ nk.2‖ ≤ C * (((nk.2 : ℝ) + 1) * ‖z‖ ^ nk.2) := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖PowerSeries.coeff nk.1 G‖
          * ‖PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)‖
          * ‖z‖ ^ nk.2
        ≤ (C * ((nk.1 : ℝ) + 1)) * 1 * ‖z‖ ^ nk.2 :=
          mul_le_mul (mul_le_mul (hG nk.1) (norm_coeff_substSeries_pow_le_one p nk.2 nk.1)
            (norm_nonneg _) (by positivity)) le_rfl (by positivity) (by positivity)
      _ = C * (((nk.1 : ℝ) + 1) * ‖z‖ ^ nk.2) := by ring
      _ ≤ C * (((nk.2 : ℝ) + 1) * ‖z‖ ^ nk.2) := by
          refine mul_le_mul_of_nonneg_left ?_ hCnn
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hnk1 1)
            (by positivity)
  have hk : nk.2 < N + 1 := by
    by_contra hge
    rw [not_lt] at hge
    exact absurd (lt_of_le_of_lt (le_trans hnk hbd) (hN nk.2 (by omega))) (lt_irrefl ε)
  have hn : nk.1 < N + 1 := lt_of_le_of_lt hnk1 hk
  exact Set.mem_prod.2 ⟨hn, hk⟩

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- φ-collapse at a primitive `p`-th root: for `‖·‖ ≤ 1`-coefficient `G` and
`(1+z)^p = 1`, `(φG)(z) = constantCoeff G` (the substitution vanishes). -/
theorem seriesEval_phi_at_root {G : PowerSeries K} (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ 1)
    {z : K} (hz : ‖z‖ < 1) (hzp : (1 + z) ^ p = 1) :
    seriesEval (phiSeries p G) z = PowerSeries.constantCoeff G := by
  rw [seriesEval_phi_of_summable_prod p G z (summable_prod_of_norm_coeff_le_one p hG hz)]
  rw [tsum_eq_single 0 fun n hn => by
    rw [show (1 + z) ^ p - 1 = 0 by rw [hzp, sub_self], zero_pow hn, mul_zero]]
  rw [show (1 + z) ^ p - 1 = 0 by rw [hzp, sub_self], pow_zero, mul_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] in
/-- φ-collapse at a primitive `p`-th root, summability form: for `(1+z)^p = 1`
and the `φ`-product family summable, `(φG)(z) = constantCoeff G`. This is the
unbounded-coefficient variant of `seriesEval_phi_at_root` needed for the
antiderivative series of the `c₀`-design (whose coefficients are only of
polynomial growth, not `‖·‖ ≤ 1`). -/
theorem seriesEval_phi_at_root_of_summable {G : PowerSeries K} {z : K}
    (hprod : Summable fun nk : ℕ × ℕ =>
      PowerSeries.coeff nk.1 G
        * PowerSeries.coeff nk.2 (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ nk.1)
        * z ^ nk.2)
    (hzp : (1 + z) ^ p = 1) :
    seriesEval (phiSeries p G) z = PowerSeries.constantCoeff G := by
  rw [seriesEval_phi_of_summable_prod p G z hprod,
    tsum_eq_single 0 fun n hn => by
      rw [show (1 + z) ^ p - 1 = 0 by rw [hzp, sub_self], zero_pow hn, mul_zero],
    show (1 + z) ^ p - 1 = 0 by rw [hzp, sub_self], pow_zero, mul_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

set_option maxHeartbeats 1000000 in
-- The nested `tsum`/Cauchy-product rewrites over `PowerSeries.coeff` are heartbeat-heavy.
omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- `seriesEval` is multiplicative on factors whose evaluations converge (nonarchimedean
Cauchy product): `(F·H)(z) = F(z)·H(z)`. -/
theorem seriesEval_mul {F H : PowerSeries K} {z : K}
    (hF : Summable fun n : ℕ => PowerSeries.coeff n F * z ^ n)
    (hH : Summable fun n : ℕ => PowerSeries.coeff n H * z ^ n) :
    seriesEval (F * H) z = seriesEval F z * seriesEval H z := by
  have hfg : Summable fun ab : ℕ × ℕ =>
      (PowerSeries.coeff ab.1 F * z ^ ab.1) * (PowerSeries.coeff ab.2 H * z ^ ab.2) :=
    hF.mul_of_nonarchimedean hH
  rw [seriesEval, seriesEval, seriesEval, hF.tsum_mul_tsum_eq_tsum_sum_antidiagonal hH hfg]
  refine tsum_congr fun j => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ab hab => ?_
  have hj : ab.1 + ab.2 = j := Finset.mem_antidiagonal.mp hab
  rw [show z ^ j = z ^ ab.1 * z ^ ab.2 from by rw [← pow_add, hj]]
  ring

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
/-- A polynomial-coefficient series `(1+X)^i` evaluates to `(1+z)^i` (finite support). -/
theorem seriesEval_one_add_X_pow (z : K) (i : ℕ) :
    seriesEval ((1 + PowerSeries.X) ^ i) z = (1 + z) ^ i := by
  have hXeq : (1 + PowerSeries.X : PowerSeries K)
      = ((1 + Polynomial.X : Polynomial K) : PowerSeries K) := by
    rw [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  have hdeg : ((1 + Polynomial.X : Polynomial K) ^ i).natDegree < i + 1 := by
    refine lt_of_le_of_lt Polynomial.natDegree_pow_le ?_
    have : (1 + Polynomial.X : Polynomial K).natDegree ≤ 1 :=
      (Polynomial.natDegree_add_le 1 Polynomial.X).trans (by simp [Polynomial.natDegree_X])
    nlinarith [this, Nat.zero_le i]
  rw [seriesEval, hXeq, ← Polynomial.coe_pow,
    tsum_eq_sum (s := Finset.range (i + 1)) fun k hk => by
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le hdeg (by simp only [Finset.mem_range, not_lt] at hk; omega)), zero_mul]]
  simp_rw [Polynomial.coeff_coe]
  rw [← Polynomial.eval_eq_sum_range' hdeg, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X]

omit [NormedAlgebra ℚ_[p] K] in
/-- A series with `‖·‖ ≤ 1` coefficients evaluated at `‖z‖ < 1` is summable (the terms have
norm `≤ ‖z‖ⁿ → 0`). -/
theorem summable_seriesEval_of_norm_coeff_le_one {F : PowerSeries K}
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ ≤ 1) {z : K} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n F * z ^ n := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz).eventually_lt_const
    hε).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio (N + 1)) fun n hn => ?_
  simp only [Set.mem_setOf_eq, not_lt] at hn
  simp only [Set.mem_Iio]
  by_contra hge
  rw [not_lt] at hge
  have hlt : ‖PowerSeries.coeff n F * z ^ n‖ < ε := by
    rw [norm_mul, norm_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) (hF n)) (hN n (by omega))
  exact absurd hn (not_le.2 hlt)

omit [NormedAlgebra ℚ_[p] K] in
/-- Linear-growth summability: if `‖coeff n F‖ ≤ C·(n+1)` and `‖z‖ < 1`, the evaluation
family is summable. The antiderivative series of the `c₀`-design and `F̃` itself have
this shape (coefficients carry an `n⁻¹` or `(p(n+1))⁻¹` factor of polynomial norm). -/
theorem summable_seriesEval_of_norm_coeff_le_linear {F : PowerSeries K} {C : ℝ}
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ ≤ C * ((n : ℝ) + 1)) {z : K} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => PowerSeries.coeff n F * z ^ n := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  rw [Filter.eventually_cofinite]
  -- `‖coeff n F · zⁿ‖ ≤ C·(n+1)·‖z‖ⁿ → 0`, so only finitely many terms exceed `ε`
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hF 0)
  have htend : Filter.Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * ‖z‖ ^ n)) Filter.atTop (nhds 0) :=
    by simpa using (tendsto_natCast_succ_mul_pow (norm_nonneg z) hz).const_mul C
  obtain ⟨N, hN⟩ := (htend.eventually_lt_const hε).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio (N + 1)) fun n hn => ?_
  simp only [Set.mem_setOf_eq, not_lt] at hn
  simp only [Set.mem_Iio]
  by_contra hge
  rw [not_lt] at hge
  have hlt : ‖PowerSeries.coeff n F * z ^ n‖ < ε := by
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff n F‖ * ‖z‖ ^ n
        ≤ (C * ((n : ℝ) + 1)) * ‖z‖ ^ n :=
          mul_le_mul_of_nonneg_right (hF n) (by positivity)
      _ = C * (((n : ℝ) + 1) * ‖z‖ ^ n) := by ring
      _ < ε := hN n (by omega)
  exact absurd hn (not_le.2 hlt)

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- `φ` preserves integral coefficients: `‖coeff n (φ G)‖ ≤ 1` when `‖coeff · G‖ ≤ 1`
(a `ℤ`-combination of `G`'s integral coefficients). -/
theorem norm_coeff_phiSeries_le_one {G : PowerSeries K} (hG : ∀ n, ‖PowerSeries.coeff n G‖ ≤ 1)
    (n : ℕ) : ‖PowerSeries.coeff n (phiSeries p G)‖ ≤ 1 := by
  rw [phiSeries, PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p),
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [coeff_substSeries_pow_eq_zero p (by omega), smul_zero]))]
  obtain ⟨d, -, hd⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    (fun d => PowerSeries.coeff d G •
      PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ d))
  refine hd.trans ?_
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hG d) (norm_nonneg _) (norm_coeff_substSeries_pow_le_one p n d)

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- `φ` preserves linear coefficient bounds: `‖coeff n (φ G)‖ ≤ C·(n+1)` when
`‖coeff m G‖ ≤ C·(m+1)` (the substituent powers are integral and the support is
`m ≤ n`, so the bound `C·(m+1) ≤ C·(n+1)` propagates through the ultrametric max). -/
theorem norm_coeff_phiSeries_le_linear {G : PowerSeries K} {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ m, ‖PowerSeries.coeff m G‖ ≤ C * ((m : ℝ) + 1)) (n : ℕ) :
    ‖PowerSeries.coeff n (phiSeries p G)‖ ≤ C * ((n : ℝ) + 1) := by
  rw [phiSeries, PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p),
    finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hmem
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hmem
      exact hd (by rw [coeff_substSeries_pow_eq_zero p (by omega), smul_zero]))]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d hd => ?_
  rw [smul_eq_mul, norm_mul]
  rcases Nat.lt_or_ge n d with hnd | hdn
  · rw [coeff_substSeries_pow_eq_zero p hnd, norm_zero, mul_zero]; positivity
  · calc ‖PowerSeries.coeff d G‖
          * ‖PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries K) ^ d)‖
        ≤ (C * ((d : ℝ) + 1)) * 1 :=
          mul_le_mul (hG d) (norm_coeff_substSeries_pow_le_one p n d) (norm_nonneg _)
            (by positivity)
      _ ≤ C * ((n : ℝ) + 1) := by
          rw [mul_one]
          have hdn : (d : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
          exact mul_le_mul_of_nonneg_left (by linarith) hC

omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- Multiplying by the integral polynomial `(1+X)^i` preserves integral coefficients. -/
theorem norm_coeff_one_add_X_pow_mul_le_one {H : PowerSeries K}
    (hH : ∀ n, ‖PowerSeries.coeff n H‖ ≤ 1) (i n : ℕ) :
    ‖PowerSeries.coeff n ((1 + PowerSeries.X) ^ i * H)‖ ≤ 1 := by
  rw [PowerSeries.coeff_mul]
  rcases (Finset.antidiagonal n).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, norm_zero]; exact zero_le_one
  obtain ⟨ab, -, hab⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
    (fun ab => PowerSeries.coeff ab.1 ((1 + PowerSeries.X) ^ i) * PowerSeries.coeff ab.2 H)
  refine hab.trans ?_
  rw [norm_mul]
  refine mul_le_one₀ ?_ (norm_nonneg _) (hH ab.2)
  -- `coeff a ((1+X)^i) = C(i,a)` is integral
  have hXeq : (1 + PowerSeries.X : PowerSeries K)
      = ((1 + Polynomial.X : Polynomial K) : PowerSeries K) := by
    rw [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [hXeq, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  exact IsUltrametricDist.norm_natCast_le_one _ _

/-- W6b-b6' (the realised `Eqphipsi`, evaluation form at `T = 0`, stated at
the INTEGRAL level where the digit decomposition is honest — replan R6.6):
with `ξ` a primitive `p`-th root of unity,
`Σ_{i<p} 𝓐_μ(ξ^i − 1) = p·𝓐_{ψμ}(0)` (evaluate the measure-level digit
decomposition at `ξ^i − 1`, where `(1+(ξ^i−1))^p − 1 = 0` collapses the
`φ`-layer; then `Σ_i ξ^{ij} = p·[j ≡ 0]` orthogonality; summability is
automatic from the bounded integral coefficients and `‖ξ^i − 1‖ < 1`). -/
theorem sum_seriesEval_mahlerK {ξ : K} (hξ : IsPrimitiveRoot ξ p)
    (μ : MeasureR K ℤ_[p]) :
    ∑ i : Fin p, seriesEval (mahlerK p K μ) (ξ ^ (i : ℕ) - 1)
      = (p : K) * PowerSeries.constantCoeff
          (mahlerK p K (MeasureR.psi p K μ)) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  -- measure-level digits `ν i = ψ(δ_{-i}·μ)` with `ν 0 = ψ μ`
  obtain ⟨ν, hν, -⟩ := existsUnique_measure_digits p K μ
  have hν0 : ν 0 = MeasureR.psi p K μ := by
    have := psi_dirac_neg_mul_sum p K ν 0
    rw [← hν, show (-(((0 : Fin p) : ℕ) : ℤ_[p])) = 0 by simp, ← MeasureR.one_def, one_mul] at this
    exact this.symm
  -- the `K`-coefficient digit decomposition of `mahlerK μ`
  set c : Fin p → K := fun i => PowerSeries.constantCoeff (mahlerK p K (ν i)) with hcdef
  have hbound : ∀ (i : Fin p) (n : ℕ), ‖PowerSeries.coeff n (mahlerK p K (ν i))‖ ≤ 1 := by
    intro i n
    rw [mahlerK, PowerSeries.coeff_map]
    exact (PowerSeries.coeff n (MeasureR.mahlerTransform p K (ν i))).2
  have hzlt : ∀ j : Fin p, ‖ξ ^ (j : ℕ) - 1‖ < 1 := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
    · rw [hj0, pow_zero, sub_self, norm_zero]; exact one_pos
    · -- `ξ^j` is itself a primitive `p`-th root (`j` coprime to `p`), so `‖ξ^j − 1‖ < 1`
      have hcop : (j : ℕ).Coprime p :=
        (Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          absurd (Nat.le_of_dvd hjpos hdvd) (by omega : ¬ p ≤ (j : ℕ))))
      have hprim : IsPrimitiveRoot (ξ ^ (j : ℕ)) (p ^ 1) := by
        rw [pow_one]; exact hξ.pow_of_coprime (j : ℕ) hcop
      exact hprim.norm_sub_one_lt (p := p) le_rfl
  have hdig : mahlerK p K μ
      = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (mahlerK p K (ν i)) := by
    simp only [mahlerK]
    conv_lhs => rw [hν]
    rw [mahlerTransform_sum_dirac_mul_phi, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_add, map_one, PowerSeries.map_X, map_phiSeries]
  -- per-`j` evaluation: the `φ`-layer collapses at `ξ^j − 1` and `(1+(ξ^j−1))^i = ξ^{ij}`
  have heval : ∀ j : Fin p, seriesEval (mahlerK p K μ) (ξ ^ (j : ℕ) - 1)
      = ∑ i : Fin p, ξ ^ ((j : ℕ) * (i : ℕ)) * c i := by
    intro j
    rw [hdig, seriesEval]
    -- `coeff` of the finite sum, then split the `tsum` over the finite index `Fin p`
    have hsummand : ∀ i : Fin p, Summable fun n : ℕ =>
        PowerSeries.coeff n ((1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (mahlerK p K (ν i)))
          * (ξ ^ (j : ℕ) - 1) ^ n :=
      fun i => summable_seriesEval_of_norm_coeff_le_one
        (norm_coeff_one_add_X_pow_mul_le_one (norm_coeff_phiSeries_le_one p (hbound i)) i)
        (hzlt j)
    rw [show (∑' n : ℕ, PowerSeries.coeff n
          (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (mahlerK p K (ν i)))
          * (ξ ^ (j : ℕ) - 1) ^ n)
        = ∑' n : ℕ, ∑ i : Fin p, PowerSeries.coeff n
          ((1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (mahlerK p K (ν i)))
          * (ξ ^ (j : ℕ) - 1) ^ n from by
      refine tsum_congr fun n => ?_
      rw [map_sum, Finset.sum_mul]]
    rw [Summable.tsum_finsetSum fun i _ => hsummand i]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- `coeff n ((1+X)^i)` is integral, so its evaluation is summable
    have hpolybd : ∀ n,
        ‖PowerSeries.coeff n ((1 + PowerSeries.X : PowerSeries K) ^ (i : ℕ))‖ ≤ 1 := by
      intro n
      have hXeq : (1 + PowerSeries.X : PowerSeries K)
          = ((1 + Polynomial.X : Polynomial K) : PowerSeries K) := by
        rw [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
      rw [hXeq, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
      exact IsUltrametricDist.norm_natCast_le_one _ _
    -- `seriesEval ((1+X)^i · φ G) (ξ^j−1) = (ξ^j)^i · constantCoeff G`
    rw [← seriesEval, seriesEval_mul
      (summable_seriesEval_of_norm_coeff_le_one hpolybd (hzlt j))
      (summable_seriesEval_of_norm_coeff_le_one (norm_coeff_phiSeries_le_one p (hbound i))
        (hzlt j)),
      seriesEval_one_add_X_pow,
      seriesEval_phi_at_root p (hbound i) (hzlt j) (by
        rw [show (1 : K) + (ξ ^ (j : ℕ) - 1) = ξ ^ (j : ℕ) by ring, ← pow_mul, mul_comm,
          pow_mul, hξ.pow_eq_one, one_pow]),
      show (1 : K) + (ξ ^ (j : ℕ) - 1) = ξ ^ (j : ℕ) by ring, ← pow_mul, hcdef]
  -- sum over `j` and apply `μ_p`-orthogonality `Σ_j (ξ^i)^j = p·[i = 0]`
  simp_rw [heval]
  rw [Finset.sum_comm]
  rw [show (∑ i : Fin p, ∑ j : Fin p, ξ ^ ((j : ℕ) * (i : ℕ)) * c i)
      = ∑ i : Fin p, (∑ j : Fin p, ξ ^ ((j : ℕ) * (i : ℕ))) * c i from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]]
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp_rw [Fin.val_zero, Nat.mul_zero, pow_zero]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    simp only [hcdef, hν0]
  · intro i _ hi0
    -- for `i ≠ 0`, `Σ_j (ξ^i)^j = 0` by primitive-root orthogonality
    have horth : (∑ j : Fin p, ξ ^ ((j : ℕ) * (i : ℕ))) = 0 := by
      rw [show (∑ j : Fin p, ξ ^ ((j : ℕ) * (i : ℕ)))
          = ∑ j ∈ Finset.range p, (ξ ^ (i : ℕ)) ^ j from by
        rw [Finset.sum_range fun j => (ξ ^ (i : ℕ)) ^ j]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← pow_mul, mul_comm]]
      have hcop : (i : ℕ).Coprime p :=
        Nat.coprime_comm.mp (hp.out.coprime_iff_not_dvd.mpr fun hdvd =>
          hi0 (Fin.ext (Nat.eq_zero_of_dvd_of_lt hdvd i.2)))
      exact (hξ.pow_of_coprime (i : ℕ) hcop).geom_sum_eq_zero hp.out.one_lt
    rw [horth, zero_mul]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin p)) h

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The formal antiderivative over `K` (char 0): every series is
`p·∂C` for a `C` vanishing at `0` (coefficient-wise division; replan
R6.6 — the c₀-design's existence half). -/
theorem exists_antideriv (B : PowerSeries K) :
    ∃ C : PowerSeries K, PowerSeries.constantCoeff C = 0
      ∧ (p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C)
        = B := by
  haveI := charZero_of_qpAlgebra (M := K) p
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  -- `1 + X` is a unit, with `(1+X)·(1+X)⁻¹ʳ = 1`
  have hunit : IsUnit (1 + PowerSeries.X : PowerSeries K) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, PowerSeries.constantCoeff_one,
      PowerSeries.constantCoeff_X, add_zero]
    exact isUnit_one
  set E : PowerSeries K := (p : K)⁻¹ • (B * Ring.inverse (1 + PowerSeries.X)) with hE
  -- the formal antiderivative: divide the `n`-th coefficient of `E` by `n+1`
  refine ⟨PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) E / n, ?_, ?_⟩
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

omit [IsUltrametricDist K] [CompleteSpace K] in
include hp in
/-- W6b-b7: the kernel of `∂ = (1+T)d/dT` is the constants
(char-zero coefficients). -/
theorem eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero
    {F : PowerSeries K}
    (h : (1 + PowerSeries.X) * PowerSeries.derivativeFun F = 0) :
    F = PowerSeries.C (PowerSeries.constantCoeff F) := by
  haveI := charZero_of_qpAlgebra (M := K) p
  -- `1 + X` is a unit (constant coefficient `1`), so it cancels in `h`
  have hunit : IsUnit (1 + PowerSeries.X : PowerSeries K) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, PowerSeries.constantCoeff_one,
      PowerSeries.constantCoeff_X, add_zero]
    exact isUnit_one
  have hD : PowerSeries.derivativeFun F = 0 := (hunit.mul_right_eq_zero).mp h
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_C]
  | succ n =>
    have hcoeff : PowerSeries.coeff n (PowerSeries.derivativeFun F) = 0 := by rw [hD, map_zero]
    rw [PowerSeries.coeff_derivativeFun] at hcoeff
    have hne : ((n : ℕ) + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [PowerSeries.coeff_succ_C, (mul_eq_zero.mp hcoeff).resolve_right hne]

/-! ### The boundary `p`-adic logarithm via the formal log series (T618 / Washington §5.1)

The formal power series `formalLog := Σ_{n≥1} (−1)^{n−1}·n⁻¹·Xⁿ` over `K` is the
series-side avatar of `padicLog (1 + ·)`. Its key formal facts —
`(1+X)·∂(formalLog) = 1` and `phiSeries p formalLog = p·formalLog` — transport (in
`ValuesAtOne`) to the `‖z−1‖ < 1` multiplicativity `padicLog (z^p) = p·padicLog z`,
extending `padicLog`'s `p`-power law from the exp ball to the whole open unit ball
(decomposition R6.6; the single prerequisite recorded at `sum_seriesEval_Ftilde`). -/

/-- T618: the formal logarithm `Σ_{n≥1} (−1)^{n−1}·n⁻¹·Xⁿ` over `K` (constant term
`0`), the series-side of `padicLog (1 + ·)`. -/
noncomputable def formalLog (K : Type*) [NormedField K] : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1 : K) ^ (n - 1) * ((n : K))⁻¹

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem coeff_zero_formalLog : PowerSeries.coeff 0 (formalLog K) = 0 := by
  rw [formalLog, PowerSeries.coeff_mk, if_pos rfl]

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem constantCoeff_formalLog : PowerSeries.constantCoeff (formalLog K) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_formalLog]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coeff_succ_formalLog (n : ℕ) :
    PowerSeries.coeff (n + 1) (formalLog K) = (-1 : K) ^ n * ((n : K) + 1)⁻¹ := by
  rw [formalLog, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
    Nat.cast_succ]

omit [IsUltrametricDist K] [CompleteSpace K] in
include hp in
/-- T618: `(1 + X)·∂(formalLog) = 1` over `K` (char 0) — the formal geometric
identity `∂(log(1+X)) = 1/(1+X)`. Coefficient check: at `n = 0` the value is
`L₁ = 1`; at `n ≥ 1` it is `(n+1)·L_{n+1} + n·L_n = (−1)ⁿ + (−1)^{n−1} = 0`. -/
theorem one_add_mul_derivative_formalLog :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun (formalLog K) = 1 := by
  haveI := charZero_of_qpAlgebra (M := K) p
  ext n
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_one]
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, add_zero, PowerSeries.coeff_derivativeFun,
      Nat.cast_zero, zero_add, coeff_succ_formalLog, if_pos rfl]
    simp
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun,
      PowerSeries.coeff_derivativeFun, if_neg (Nat.succ_ne_zero m), coeff_succ_formalLog,
      coeff_succ_formalLog]
    have hm1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hm2 : ((m : K) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
    push_cast
    rw [show (-1 : K) ^ (m + 1) * ((m : K) + 1 + 1)⁻¹ * ((m : K) + 1 + 1)
          = (-1 : K) ^ (m + 1) from by rw [mul_assoc, inv_mul_cancel₀ hm2, mul_one],
      show (-1 : K) ^ m * ((m : K) + 1)⁻¹ * ((m : K) + 1)
          = (-1 : K) ^ m from by rw [mul_assoc, inv_mul_cancel₀ hm1, mul_one], pow_succ]
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
include hp in
/-- T618: `phiSeries p formalLog = p·formalLog` over `K` (char 0). Both sides have
the same image under `∂ = (1+X)d/dX`: `∂(φ formalLog) = p·φ(∂ formalLog) = p·φ(1) =
p·1` (using `one_add_mul_derivative_phiSeries` and `(1+X)·∂ formalLog = 1`), and
`∂(p·formalLog) = p·1`. The difference is `∂`-killed, hence constant; its constant
term is `constantCoeff(φ formalLog) − p·constantCoeff formalLog = 0`. -/
theorem phiSeries_formalLog :
    phiSeries p (formalLog K) = (p : K) • formalLog K := by
  haveI := charZero_of_qpAlgebra (M := K) p
  -- `(1+X)·∂` of both sides equals `p·1`
  have hphi1 : phiSeries p (1 : PowerSeries K) = 1 := by
    rw [phiSeries, ← PowerSeries.coe_substAlgHom (hasSubst_one_add_X_pow_sub_one p), map_one]
  have hLHS : (1 + PowerSeries.X) * PowerSeries.derivativeFun (phiSeries p (formalLog K))
      = (p : K) • (1 : PowerSeries K) := by
    rw [one_add_mul_derivative_phiSeries, one_add_mul_derivative_formalLog (p := p), hphi1]
  have hRHS : (1 + PowerSeries.X) * PowerSeries.derivativeFun ((p : K) • formalLog K)
      = (p : K) • (1 : PowerSeries K) := by
    rw [PowerSeries.derivativeFun_smul, mul_smul_comm, one_add_mul_derivative_formalLog (p := p)]
  -- the difference is `∂`-killed
  have hker : (1 + PowerSeries.X) * PowerSeries.derivativeFun
      (phiSeries p (formalLog K) - (p : K) • formalLog K) = 0 := by
    rw [show PowerSeries.derivativeFun (phiSeries p (formalLog K) - (p : K) • formalLog K)
          = PowerSeries.derivativeFun (phiSeries p (formalLog K))
            - PowerSeries.derivativeFun ((p : K) • formalLog K) from
        map_sub (PowerSeries.derivative K) _ _,
      mul_sub, hLHS, hRHS, sub_self]
  have heqC := eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero (p := p) hker
  -- the constant term of the difference is `0`
  have hc0 : PowerSeries.constantCoeff (phiSeries p (formalLog K) - (p : K) • formalLog K)
      = 0 := by
    rw [map_sub, constantCoeff_phiSeries, PowerSeries.smul_eq_C_mul, map_mul,
      PowerSeries.constantCoeff_C, constantCoeff_formalLog, mul_zero, sub_zero]
  rw [hc0, map_zero] at heqC
  exact sub_eq_zero.mp heqC

end bridge

end PadicLFunctions
