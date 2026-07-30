/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.RestrictedGaussAdic
import «Adic spaces».Vendored.XiaMvPowerSeriesEquiv
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# The restricted Fubini: `K⟨X₁..X_{k+m}⟩ ≅ (K⟨X₁..X_m⟩)⟨T₁..T_k⟩`

([hrw-decomposition] the T_N⟨T⟩-tower leaf for `comap_headToQ_isMaximal`.)
Radius-one restricted power series in a sum of variables are restricted
power series with restricted coefficients: Xia's `sumAlgEquiv` at the
underlying series level, with the Gauss decay transported through the
sup-norm identity in both directions.  Composed with the `Fin`-sum rename,
this identifies the `k`-th Tate extension of a Tate algebra with a Tate
algebra, funneling the tower Nullstellensatz into `module_finite_residue`.

WIP frontier: the two Gauss-transport legs carry `sorry` markers.
-/

@[expose] public section

namespace FiniteJet.GraphKoszul

open MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- Radius-one restricted series transport along an index equivalence. -/
noncomputable def restrictedRenameEquiv {σ τ : Type*} (e : σ ≃ τ) :
    MvPowerSeries.Restricted K (fun _ : σ => (1 : ℝ)) ≃+*
      MvPowerSeries.Restricted K (fun _ : τ => (1 : ℝ)) := by
  sorry

/-- **The restricted sum–iterate transport**: restricted series in a sum of
variables are restricted series with restricted coefficients. -/
noncomputable def restrictedSumEquiv (m k : ℕ) :
    MvPowerSeries.Restricted K (fun _ : Fin k ⊕ Fin m => (1 : ℝ)) ≃+*
      MvPowerSeries.Restricted (P K m) (fun _ : Fin k => (1 : ℝ)) := by
  sorry

/-- **The restricted Fubini** `K⟨X₁..X_{k+m}⟩ ≅ (K⟨X₁..X_m⟩)⟨T₁..T_k⟩`. -/
noncomputable def restrictedFubini (m k : ℕ) :
    P K (k + m) ≃+* P (P K m) k :=
  (restrictedRenameEquiv (finSumFinEquiv (m := k) (n := m)).symm).trans
    (restrictedSumEquiv m k)

end FiniteJet.GraphKoszul
