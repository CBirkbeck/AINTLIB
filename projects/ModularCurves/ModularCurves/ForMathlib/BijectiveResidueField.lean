/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-D32.
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Bijectivity of linear maps is detected on residue-field fibres

For `φ : M →ₗ[R] N` with `M` finite and `N` finite flat:

* `IsLocalRing.surjective_of_surjective_lTensor_residueField`: over a local ring,
  surjectivity of `κ ⊗ φ` gives surjectivity of `φ` (Nakayama; only `N` finite needed).
* `IsLocalRing.bijective_of_bijective_lTensor_residueField`: over a local ring,
  bijectivity of `κ ⊗ φ` gives bijectivity of `φ` (injectivity via the split-injective
  characterisation, `N` free by finite + flat + local).
* `LinearMap.bijective_of_forall_bijective_lTensor_residueField`: over any commutative
  ring, bijectivity of `κ(J) ⊗ φ` at every maximal `J` gives bijectivity of `φ`
  (localize at maximals; the localized map is the base change, compared through
  `AlgebraTensorModule.cancelBaseChange`).

This is the "iso ⟺ iso on geometric fibres" detection for maps of finite locally free
modules (KM 1.4.4 (3)⟺(5) reduction, where the map `(ℤ/N) → D` between rank-`N` finite
locally free schemes is an isomorphism iff it is on fibres). The converse direction
(bijective ⟹ fibrewise bijective) is base-change functoriality and is not stated here —
consumers apply `LinearEquiv.baseChange`/`lTensor` directly.

The determinant route (iso ⟺ `det` a unit) is deliberately avoided: mathlib's
`LinearMap.det` is endomorphism-only, while `φ` here connects two different modules.

Upstream candidates: the Nakayama toolkit used (`map_tensorProduct_mk_eq_top`,
`split_injective_iff_lTensor_residueField_injective`, `bijective_of_isLocalized_maximal`)
is all in mathlib, but none of the three composed statements above is.
-/

open Function TensorProduct IsLocalRing

universe u v w

section Local

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Over a local ring, a linear map into a finite module is surjective as soon as it is
surjective after tensoring with the residue field (Nakayama). -/
theorem IsLocalRing.surjective_of_surjective_lTensor_residueField [Module.Finite R N]
    (φ : M →ₗ[R] N) (h : Surjective (φ.lTensor (ResidueField R))) :
    Surjective φ := by
  rw [← LinearMap.range_eq_top, ← IsLocalRing.map_tensorProduct_mk_eq_top, eq_top_iff]
  rintro z -
  obtain ⟨w, rfl⟩ := h z
  obtain ⟨m, rfl⟩ := TensorProduct.mk_surjective R M (ResidueField R) residue_surjective w
  exact ⟨φ m, LinearMap.mem_range_self _ m, (φ.lTensor_tmul _ _ _).symm⟩

/-- Over a local ring, a linear map from a finite module to a finite flat module is
bijective as soon as it is bijective after tensoring with the residue field. -/
theorem IsLocalRing.bijective_of_bijective_lTensor_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Flat R N]
    (φ : M →ₗ[R] N) (h : Bijective (φ.lTensor (ResidueField R))) :
    Bijective φ := by
  haveI : Module.Free R N := Module.free_of_flat_of_isLocalRing
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective φ).mpr h.injective
  exact ⟨Function.LeftInverse.injective fun x => by simpa using LinearMap.congr_fun hl' x,
    IsLocalRing.surjective_of_surjective_lTensor_residueField φ h.surjective⟩

end Local

section Global

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map from a finite module to a finite flat module is bijective as soon as it
is bijective after tensoring with the residue field of every maximal ideal. -/
theorem LinearMap.bijective_of_forall_bijective_lTensor_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] (φ : M →ₗ[R] N)
    (h : ∀ (J : Ideal R) [J.IsMaximal], Bijective (φ.lTensor J.ResidueField)) :
    Bijective φ := by
  haveI instM : ∀ (J : Ideal R) [J.IsMaximal],
      IsLocalizedModule J.primeCompl (TensorProduct.mk R (Localization.AtPrime J) M 1) :=
    fun J _ => (isLocalizedModule_iff_isBaseChange J.primeCompl (Localization.AtPrime J) _).mpr
      (TensorProduct.isBaseChange _ _ _)
  haveI instN : ∀ (J : Ideal R) [J.IsMaximal],
      IsLocalizedModule J.primeCompl (TensorProduct.mk R (Localization.AtPrime J) N 1) :=
    fun J _ => (isLocalizedModule_iff_isBaseChange J.primeCompl (Localization.AtPrime J) _).mpr
      (TensorProduct.isBaseChange _ _ _)
  refine bijective_of_isLocalized_maximal
    (fun J _ => Localization.AtPrime J ⊗[R] M)
    (fun J _ => TensorProduct.mk R (Localization.AtPrime J) M 1)
    (fun J _ => Localization.AtPrime J ⊗[R] N)
    (fun J _ => TensorProduct.mk R (Localization.AtPrime J) N 1)
    φ (fun J hJ => ?_)
  have hmap : IsLocalizedModule.map J.primeCompl
      (TensorProduct.mk R (Localization.AtPrime J) M 1)
      (TensorProduct.mk R (Localization.AtPrime J) N 1) φ
      = (φ.baseChange (Localization.AtPrime J)).restrictScalars R := by
    refine IsLocalizedModule.ext J.primeCompl (TensorProduct.mk R (Localization.AtPrime J) M 1)
      (IsLocalizedModule.map_units (TensorProduct.mk R (Localization.AtPrime J) N 1)) ?_
    rw [IsLocalizedModule.map_comp]
    ext m
    simp
  rw [hmap]
  have key : Bijective ((φ.baseChange (Localization.AtPrime J)).lTensor J.ResidueField) := by
    let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime J)
      J.ResidueField J.ResidueField M
    let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime J)
      J.ResidueField J.ResidueField N
    have hcomm : ∀ x, eN ((φ.baseChange (Localization.AtPrime J)).lTensor J.ResidueField x)
        = (φ.lTensor J.ResidueField) (eM x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a m => simp [eM, eN]
        | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hfun : ⇑((φ.baseChange (Localization.AtPrime J)).lTensor J.ResidueField)
        = ⇑eN.symm ∘ ⇑(φ.lTensor J.ResidueField) ∘ ⇑eM := by
      funext x
      rw [Function.comp_apply, Function.comp_apply, ← hcomm, LinearEquiv.symm_apply_apply]
    rw [hfun]
    exact eN.symm.bijective.comp ((h J).comp eM.bijective)
  show Function.Bijective ⇑(φ.baseChange (Localization.AtPrime J))
  exact IsLocalRing.bijective_of_bijective_lTensor_residueField
    (R := Localization.AtPrime J) _ key

end Global
