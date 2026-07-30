/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.RestrictedGaussAdic
import «Adic spaces».Vendored.XiaMvPowerSeriesEquiv
import «Adic spaces».WP.ZeroHeadTate
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

/-- Double embedding along an equivalence and its inverse is the identity. -/
theorem embDomain_symm_embDomain {σ τ : Type*} (e : σ ≃ τ) (t : τ →₀ ℕ) :
    Finsupp.embDomain e.toEmbedding
      (Finsupp.embDomain e.symm.toEmbedding t) = t := by
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain,
    ← Finsupp.mapDomain_comp]
  refine (Finsupp.mapDomain_congr ?_).trans Finsupp.mapDomain_id
  intro a _
  exact e.apply_symm_apply a

/-- Coefficients of a rename along an equivalence. -/
theorem coeff_rename_equiv {σ τ : Type*} (e : σ ≃ τ)
    (F : MvPowerSeries σ K) (t : τ →₀ ℕ) :
    MvPowerSeries.coeff t (MvPowerSeries.rename (⇑e) F) =
      MvPowerSeries.coeff (Finsupp.embDomain e.symm.toEmbedding t) F := by
  conv_lhs => rw [← embDomain_symm_embDomain e t]
  exact MvPowerSeries.coeff_embDomain_rename e.toEmbedding F _

/-- Renaming along an equivalence preserves radius-one restrictedness. -/
theorem isRestrictedGauss_rename_equiv {σ τ : Type*} (e : σ ≃ τ)
    (F : MvPowerSeries σ K)
    (hF : MvPowerSeries.IsRestrictedGauss (fun _ : σ => (1 : ℝ)) F) :
    MvPowerSeries.IsRestrictedGauss (fun _ : τ => (1 : ℝ))
      (MvPowerSeries.rename e F) := by
  rw [WeightedParity.isRestrictedGauss_one_iff] at hF ⊢
  rw [funext (coeff_rename_equiv e F)]
  exact hF.comp (Finsupp.embDomain_injective _).tendsto_cofinite

/-- The restricted rename homomorphism along an equivalence. -/
noncomputable def restrictedRenameHom {σ τ : Type*} (e : σ ≃ τ) :
    MvPowerSeries.Restricted K (fun _ : σ => (1 : ℝ)) →+*
      MvPowerSeries.Restricted K (fun _ : τ => (1 : ℝ)) where
  toFun F := ⟨MvPowerSeries.rename e F.1,
    isRestrictedGauss_rename_equiv e F.1 F.2⟩
  map_one' := Subtype.ext
    (map_one (MvPowerSeries.rename (R := K) (⇑e)))
  map_mul' F G := Subtype.ext
    (map_mul (MvPowerSeries.rename (R := K) (⇑e)) F.1 G.1)
  map_zero' := Subtype.ext
    (map_zero (MvPowerSeries.rename (R := K) (⇑e)))
  map_add' F G := Subtype.ext
    (map_add (MvPowerSeries.rename (R := K) (⇑e)) F.1 G.1)

/-- Radius-one restricted series transport along an index equivalence. -/
noncomputable def restrictedRenameEquiv {σ τ : Type*} (e : σ ≃ τ) :
    MvPowerSeries.Restricted K (fun _ : σ => (1 : ℝ)) ≃+*
      MvPowerSeries.Restricted K (fun _ : τ => (1 : ℝ)) :=
  RingEquiv.ofRingHom (restrictedRenameHom e) (restrictedRenameHom e.symm)
    (RingHom.ext fun F => Subtype.ext (by
      show MvPowerSeries.rename (⇑e)
        (MvPowerSeries.rename (⇑e.symm) F.1) = F.1
      refine MvPowerSeries.ext fun t => ?_
      rw [coeff_rename_equiv e]
      exact MvPowerSeries.coeff_embDomain_rename e.symm.toEmbedding F.1 t))
    (RingHom.ext fun F => Subtype.ext (by
      show MvPowerSeries.rename (⇑e.symm)
        (MvPowerSeries.rename (⇑e) F.1) = F.1
      refine MvPowerSeries.ext fun t => ?_
      rw [coeff_rename_equiv e.symm, Equiv.symm_symm]
      exact MvPowerSeries.coeff_embDomain_rename e.toEmbedding F.1 t))

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
