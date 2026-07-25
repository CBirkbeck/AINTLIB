/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.SplitInjectiveLocalization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Nakayama

/-!
# Unit retractions of faithfully flat finitely presented algebras

**[T-YR-6 (c1) Ω-half, RETRACT]** A finitely presented faithfully flat algebra
`B/R` admits an `R`-linear retraction of its unit `R →ₗ[R] B`. Locally at a
maximal ideal this is the unimodularity of `1` in a finite free module over a
local ring (Nakayama); globally it glues by
`LinearMap.split_injective_of_localization_maximal`.
-/

open IsLocalRing

/-- Over a local ring, `1` in a nontrivial finite flat (hence free) algebra is
unimodular: some linear functional sends it to `1`. -/
theorem IsLocalRing.exists_linearMap_one_eq_one
    (L C : Type*) [CommRing L] [IsLocalRing L] [CommRing C] [Algebra L C]
    [Module.Finite L C] [Module.Flat L C] [Nontrivial C] :
    ∃ μ : C →ₗ[L] L, μ 1 = 1 := by
  haveI : Module.Free L C := Module.free_of_flat_of_isLocalRing
  set b := Module.Free.chooseBasis L C with hb
  by_cases hall : ∀ i, b.repr 1 i ∈ maximalIdeal L
  · exfalso
    have h1 : (1 : C) ∈ (maximalIdeal L) • (⊤ : Submodule L C) := by
      rw [← b.sum_repr 1]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hall i) Submodule.mem_top
    rw [Ideal.smul_top_eq_map] at h1
    have h2 : Ideal.map (algebraMap L C) (maximalIdeal L) = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr h1
    have h3 : (maximalIdeal L) • (⊤ : Submodule L C) = ⊤ := by
      rw [Ideal.smul_top_eq_map, h2]
      rfl
    have h4 := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (maximalIdeal L) ⊤ Module.Finite.fg_top h3.ge
      (maximalIdeal_le_jacobson ⊥)
    exact one_ne_zero ((Submodule.mem_bot L).mp (h4 ▸ Submodule.mem_top (x := (1 : C))))
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hu : IsUnit (b.repr 1 j) := by
      by_contra hnu
      exact hj (mem_maximalIdeal _ |>.mpr hnu)
    refine ⟨hu.unit⁻¹.val • b.coord j, ?_⟩
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    exact_mod_cast hu.val_inv_mul

open TensorProduct in
/-- **[RETRACT]** A finitely presented faithfully flat algebra admits a linear
retraction of its unit map: there is `r : B →ₗ[R] R` with `r ∘ (R → B) = id`.
Locally at each maximal ideal this is unimodularity of `1` in a finite free
module (`IsLocalRing.exists_linearMap_one_eq_one`); the local retractions glue
by `LinearMap.split_injective_of_localization_maximal`. -/
theorem Algebra.exists_retraction_of_faithfullyFlat
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.FinitePresentation R B] [Module.FaithfullyFlat R B] :
    ∃ r : B →ₗ[R] R, r.comp (Algebra.linearMap R B) = LinearMap.id := by
  haveI : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  apply LinearMap.split_injective_of_localization_maximal
  intro I hI
  haveI hlocR : IsLocalizedModule I.primeCompl
      (Algebra.linearMap R (Localization.AtPrime I)) :=
    (isLocalizedModule_iff_isLocalization' _ _).mpr inferInstance
  have e := (IsLocalizedModule.isBaseChange I.primeCompl (Localization.AtPrime I)
    (IsScalarTower.toAlgHom R B
      (Localization (Algebra.algebraMapSubmonoid B I.primeCompl))).toLinearMap).equiv
  haveI : Module.Finite (Localization.AtPrime I)
      (Localization (Algebra.algebraMapSubmonoid B I.primeCompl)) :=
    Module.Finite.equiv e
  haveI : Nontrivial (Localization (Algebra.algebraMapSubmonoid B I.primeCompl)) := by
    haveI : Nontrivial ((Localization.AtPrime I) ⊗[R] B) :=
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left R
        (Localization.AtPrime I)).mpr inferInstance
    exact e.symm.toEquiv.nontrivial
  obtain ⟨μ, hμ⟩ := IsLocalRing.exists_linearMap_one_eq_one (Localization.AtPrime I)
    (Localization (Algebra.algebraMapSubmonoid B I.primeCompl))
  refine ⟨((IsLocalizedModule.iso I.primeCompl (Algebra.linearMap R
        (Localization.AtPrime I))).extendScalarsOfIsLocalization I.primeCompl
        (Localization.AtPrime I)).symm.toLinearMap ∘ₗ μ ∘ₗ
      ((IsLocalizedModule.iso I.primeCompl (IsScalarTower.toAlgHom R B
        (Localization (Algebra.algebraMapSubmonoid B I.primeCompl))).toLinearMap
        ).extendScalarsOfIsLocalization I.primeCompl
        (Localization.AtPrime I)).toLinearMap, ?_⟩
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl R)
  · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl R)
  ext
  have hstep1 : (LocalizedModule.map I.primeCompl (Algebra.linearMap R B))
      (LocalizedModule.mk (1 : R) 1) = LocalizedModule.mk (1 : B) 1 := by
    rw [LocalizedModule.map_mk, Algebra.linearMap_apply, map_one]
  have hsymm : ((IsLocalizedModule.iso I.primeCompl (Algebra.linearMap R
      (Localization.AtPrime I))).symm) (1 : Localization.AtPrime I) =
      LocalizedModule.mk (1 : R) 1 := by
    have h := LinearMap.congr_fun (IsLocalizedModule.iso_symm_comp I.primeCompl
      (Algebra.linearMap R (Localization.AtPrime I))) (1 : R)
    simpa using h
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LocalizedModule.mkLinearMap_apply, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe,
    hstep1, LinearEquiv.extendScalarsOfIsLocalization_apply,
    LinearEquiv.extendScalarsOfIsLocalization_symm_apply,
    IsLocalizedModule.iso_mk_one, AlgHom.toLinearMap_apply, map_one, hμ, hsymm]
