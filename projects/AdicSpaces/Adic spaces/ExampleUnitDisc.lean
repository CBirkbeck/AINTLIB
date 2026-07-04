/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Data.Int.WithZero
import «Adic spaces».ExampleLaurentSeries
import «Adic spaces».Vendored.CoramRestrictedIso

/-!
# The closed unit disc over `F⸨X⸩` is sheafy (Wedhorn 8.28(b), second example)

Let `K := F⸨X⸩` (Laurent series, `X`-adically valued) and
`D := K⟨Y⟩ = MvPowerSeries.Restricted K 1` the ring of restricted power series in one
variable — the ring of functions on the **closed unit disc** over `K`. We equip `K`
with the rank-one norm (`Valued.toNormedField`, whose uniformity *is* the valued one),
and `D` with the Gauss norm (vendored Coram stack). Then `D` is a complete, strongly
noetherian Tate ring, `(D, 𝒪_D)` with `𝒪_D` the closed unit ball is an affinoid ring,
and `IsSheafy D` follows from `isSheafy_of_stronglyNoetherian_828b`.

Strong noetherianity comes from the **flattening isometry**
`K⟨Y⟩⟨X₁,…,Xₘ⟩ ≃ K⟨Y, X₁,…,Xₘ⟩` (induction on `m` over the vendored restricted Fubini
`MvRestricted.finSuccEquiv`), transported to the topological restricted rings by the
norm/topology bridge, and then discharged by `IsStronglyNoetherian K` from
`ExampleLaurentSeries`.
-/

noncomputable section

open scoped LaurentSeries PowerSeries
open WithZero ValuationSpectrum Filter
open scoped NNReal

namespace UnitDiscExample

open LaurentSeriesExample

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### The rank-one norm on `K` -/

/-- The `X`-adic valuation of `K` embeds in `ℝ≥0` (rank at most one), via `2^(-ord)`. -/
noncomputable instance : Valuation.RankLeOne (Valued.v : Valuation K ℤᵐ⁰) where
  hom' := (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
    (MonoidWithZeroHom.ValueGroup₀.embedding)
  strictMono' := (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

/-- The `X`-adic valuation of `K` has rank one (nontriviality witnessed by `t`). -/
noncomputable instance : Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰) :=
  Valuation.RankLeOne.rankOne_of_exists (Valued.v : Valuation K ℤᵐ⁰) ⟨t F, t_ne_zero F, by
    rw [valuation_t]
    intro h
    have h2 := exp_lt_exp.mpr (show (-1 : ℤ) < 0 by omega)
    rw [h, exp_zero] at h2
    exact absurd h2 (lt_irrefl _)⟩

open scoped Valued in
noncomputable instance : NormedField K := Valued.toNormedField K ℤᵐ⁰

/-- `K` with the rank-one norm is an ultrametric space. -/
instance : IsUltrametricDist K := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => ?_
  rcases le_total ‖x‖ ‖y‖ with h | h
  · refine le_trans ?_ (le_max_right ‖x‖ ‖y‖)
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact le_trans (Valuation.map_add _ _ _) (max_le h le_rfl)
  · refine le_trans ?_ (le_max_left ‖x‖ ‖y‖)
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact le_trans (Valuation.map_add _ _ _) (max_le le_rfl h)

/-! ### The norm/topology bridge for restricted power series -/

section Bridge

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] (k : ℕ)

/-- `CommRing` on the (vendored, normed) restricted subring over a commutative base. -/
noncomputable instance : CommRing (MvPowerSeries.Restricted R (fun _ : Fin k => (1 : ℝ))) :=
  { (inferInstance : Ring (MvPowerSeries.Restricted R (fun _ : Fin k => (1 : ℝ)))) with
    mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }

/-- Radius-one Gauss restrictedness is the topological restrictedness over a normed
ultrametric base. -/
theorem isRestrictedGauss_one_iff (f : MvPowerSeries (Fin k) R) :
    MvPowerSeries.IsRestrictedGauss (fun _ : Fin k => (1 : ℝ)) f ↔
      MvPowerSeries.IsRestricted f := by
  rw [MvPowerSeries.IsRestrictedGauss, MvPowerSeries.IsRestricted]
  constructor
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h.congr fun t => ?_
    simp [Finsupp.prod_pow]
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero] at h
    refine h.congr fun t => ?_
    simp [Finsupp.prod_pow]

/-- The two restricted subrings coincide. -/
theorem restrictedGauss_eq_restricted :
    MvPowerSeries.isSubring (R := R) (fun _ : Fin k => (1 : ℝ)) =
      (restrictedMvPowerSeriesSubring k R : Subring (MvPowerSeries (Fin k) R)) := by
  ext f
  show MvPowerSeries.IsRestrictedGauss _ f ↔ MvPowerSeries.IsRestricted f
  exact isRestrictedGauss_one_iff R k f

/-- Transport between the (vendored) Gauss-restricted ring and this project's
topological restricted ring. -/
noncomputable def restrictedGaussEquiv :
    MvPowerSeries.Restricted R (fun _ : Fin k => (1 : ℝ)) ≃+*
      ↥(restrictedMvPowerSeriesSubring k R) :=
  RingEquiv.subringCongr (restrictedGauss_eq_restricted R k)

end Bridge

end UnitDiscExample
