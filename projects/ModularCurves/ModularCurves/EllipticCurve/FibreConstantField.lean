/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Vendored.RiemannRoch.EllipticCurve.GenusOne
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The constant field of an elliptic function field is full (`AP2-A1e`)

For `W` elliptic over an arbitrary field `k` and `K` a fraction field of its coordinate ring,
every element of `K` algebraic over `k` is a constant: `IsFullConstantField k K`. This
discharges the standing hypothesis of the vendored Riemann–Roch endpoints
(`genus_eq_one`, `riemann_roch`, `ell_zero`, …) over every base field, as required by the
`∀`-fields quantifier of `HasDegreeOneFibreCohomology` (`AP2-A1d`).

The residue trick: an algebraic `f` is integral over both chart rings, hence lies in
`ringOfIntegers` and `infiniteIntegers` and has valuation `≤ 1` at every place. At the unique
infinite place (`infinity_heightOne_unique`) the residue field is one-dimensional over `k`
(`infinityPlace_deg_one`), so `f ≡ c` for a constant `c`; then `f - c` lies in the
Riemann–Roch space of `-[∞]`, a divisor of degree `-1 < 0`, which is trivial
(`RRspace_neg_deg` — no constant-field hypothesis). Hence `f = c`. No linear disjointness, no
base change, all characteristics.
-/

open FunctionField FunctionField.Chart WeierstrassCurve.Affine.Chart Polynomial

open scoped Polynomial RatFunc WithZero

namespace ModularCurves

namespace FibreRR

/-- Discreteness of the value group: below `1` means at most `exp (-1)`. -/
theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← WithZero.exp_log hx0] at hx ⊢
    rw [WithZero.exp_le_exp]
    have hlt : WithZero.log x < 0 := by
      rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm,
        WithZero.exp_lt_exp] at hx
      exact hx
    omega

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K]

include W

/-- **(`AP2-A1e`)** The constant field of an elliptic function field is full: every element
algebraic over the base field is a constant. -/
theorem isFullConstantField : IsFullConstantField k K := by
  classical
  constructor
  intro f hf
  -- `f` is integral over `k`, hence over both chart rings
  have hfint : IsIntegral k f := hf.isIntegral
  have hfin : f ∈ ringOfIntegers k K := by
    have : IsIntegral k[X] f := hfint.tower_top
    exact this
  letI : IsScalarTower k (inftyValuationSubring k) K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K,
        IsScalarTower.algebraMap_apply k (inftyValuationSubring k) (infiniteIntegers k K),
        ← IsScalarTower.algebraMap_apply (inftyValuationSubring k) (infiniteIntegers k K) K]
  have hinf : f ∈ infiniteIntegers k K := by
    have : IsIntegral (inftyValuationSubring k) f := hfint.tower_top
    exact this
  -- the unique infinite place and its residue field
  set v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K) :=
    infinityHeightOne (k := k) K with hv
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : Field (infiniteIntegers k K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  -- the residue field is one-dimensional over `k`
  have hdeg1 : Module.finrank k (infiniteIntegers k K ⧸ v.asIdeal) = 1 := by
    have h := infinityPlace_deg_one W K
    rw [infinityPlace, ← hv] at h
    exact h
  -- hence the residue of `f` is a constant
  obtain ⟨c, hc⟩ : ∃ c : k, Ideal.Quotient.mk v.asIdeal ⟨f, hinf⟩ =
      algebraMap k (infiniteIntegers k K ⧸ v.asIdeal) c := by
    haveI : IsSimpleModule k (infiniteIntegers k K ⧸ v.asIdeal) :=
      (isSimpleModule_iff_finrank_eq_one (R := k)
        (M := infiniteIntegers k K ⧸ v.asIdeal)).mpr hdeg1
    have hrange := eq_bot_or_eq_top
      (LinearMap.range (Algebra.linearMap k (infiniteIntegers k K ⧸ v.asIdeal)))
    rcases hrange with hbot | htop
    · exfalso
      have h1 : (1 : infiniteIntegers k K ⧸ v.asIdeal) ∈
          LinearMap.range (Algebra.linearMap k (infiniteIntegers k K ⧸ v.asIdeal)) :=
        ⟨1, by simp [Algebra.linearMap_apply]⟩
      rw [hbot, Submodule.mem_bot] at h1
      exact one_ne_zero h1
    · have hmem := htop ▸ Submodule.mem_top
        (x := Ideal.Quotient.mk v.asIdeal ⟨f, hinf⟩) (R := k)
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, by rw [← hc, Algebra.linearMap_apply]⟩
  -- so `f - c` vanishes at the infinite place and is integral everywhere
  refine ⟨c, ?_⟩
  have hmem : f - algebraMap k K c ∈
      RRspace k K (-(Finsupp.single (infinityPlace (k := k) K) 1 : DivisorA k K)) := by
    rw [mem_RRspace_iff]
    intro w
    rcases w with u | u
    · -- finite places: both terms are integral
      have hfle : placeValuation k K (Sum.inl u) f ≤ 1 := by
        simpa [placeValuation] using
          IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) u ⟨f, hfin⟩
      have hcle : placeValuation k K (Sum.inl u) (algebraMap k K c) ≤ 1 :=
        placeValuation_algebraMap_le_one k K _ c
      have hD : (-(Finsupp.single (infinityPlace (k := k) K) 1 : DivisorA k K))
          (Sum.inl u) = 0 := by
        simp [infinityPlace, Finsupp.single_apply]
      rw [hD, WithZero.exp_zero]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hfle hcle)
    · -- the (unique) infinite place: the residue of `f - c` vanishes
      have hu : u = v := infinity_heightOne_unique W K u v
      subst hu
      have hD : (-(Finsupp.single (infinityPlace (k := k) K) 1 : DivisorA k K))
          (Sum.inr v) = -1 := by
        rw [Finsupp.neg_apply, infinityPlace, ← hv, Finsupp.single_eq_same]
      rw [hD]
      -- membership in the maximal ideal from the residue computation
      have hmem' : (⟨f, hinf⟩ - algebraMap k (infiniteIntegers k K) c : infiniteIntegers k K)
          ∈ v.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hc]
        have hcq : algebraMap k (infiniteIntegers k K ⧸ v.asIdeal) c =
            Ideal.Quotient.mk v.asIdeal (algebraMap k (infiniteIntegers k K) c) := by
          rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K)
            (infiniteIntegers k K ⧸ v.asIdeal)]
          rfl
        rw [hcq]
        exact sub_self _
      have hlt : placeValuation k K (Sum.inr v) (f - algebraMap k K c) < 1 := by
        have hcast : f - algebraMap k K c = algebraMap (infiniteIntegers k K) K
            (⟨f, hinf⟩ - algebraMap k (infiniteIntegers k K) c) := by
          rw [map_sub]
          congr 1
          rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K]
        rw [hcast]
        simpa [placeValuation] using
          (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)
            v _).mpr hmem'
      exact le_exp_neg_one_of_lt_one hlt
  -- the divisor has degree `-1 < 0`, so the Riemann–Roch space is trivial
  have hdeg : deg k K (-(Finsupp.single (infinityPlace (k := k) K) 1 : DivisorA k K)) < 0 := by
    rw [deg_neg, deg_single, infinityPlace_deg_one W K]
    norm_num
  have hbot := RRspace_neg_deg (k := k) (K := K) hdeg
  have h0 : f - algebraMap k K c = 0 := by
    have hzero := hbot ▸ hmem
    simpa using hzero
  exact sub_eq_zero.mp h0

end FibreRR

end ModularCurves
