/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.LocalProperties.Projective

/-!
# Split injectivity is local at maximal ideals

The mono-mirror of `LinearMap.split_surjective_of_localization_maximal`: a
linear map out of a finitely presented module that admits left inverses after
localization at every maximal ideal admits a global left inverse.

This is the local-global engine for the unit-retraction of a finite projective
faithfully flat algebra ([RETRACT], T-YR-6 (c1) Ω-half).
-/

open LinearMap

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem LinearMap.split_injective_of_localization_maximal
    (f : M →ₗ[R] N) [Module.FinitePresentation R M]
    [Module.FinitePresentation R N]
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
      ∃ (g : _ →ₗ[Localization.AtPrime I] _),
        g.comp (LocalizedModule.map I.primeCompl f) = LinearMap.id) :
    ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id := by
  change LinearMap.id ∈ LinearMap.range ((LinearMap.llcomp R M N M).flip f)
  refine Submodule.mem_of_localization_maximal _
    (fun P _ ↦ LocalizedModule.map P.primeCompl) _ _ fun I hI ↦ ?_
  rw [LocalizedModule.map_id]
  have : LinearMap.id ∈ LinearMap.range ((LinearMap.llcomp _
      (LocalizedModule I.primeCompl M) (LocalizedModule I.primeCompl N)
      (LocalizedModule I.primeCompl M)).flip
      (LocalizedModule.map I.primeCompl f)) := by
    obtain ⟨g, hg⟩ := H I hI
    exact ⟨g, hg⟩
  convert! this
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, c, rfl⟩ := hg
    obtain ⟨h, rfl⟩ := ha
    use IsLocalizedModule.mk' (LocalizedModule.map I.primeCompl) h c
    apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
      (LocalizedModule.map I.primeCompl) c).injective
    dsimp
    conv_rhs => rw [← Submonoid.smul_def]
    conv_lhs => rw [← LinearMap.map_smul_of_tower]
    rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
    rw [LinearMap.llcomp_apply', Submonoid.smul_def, LinearMap.comp_smul,
      ← LinearMap.smul_comp, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext I.primeCompl
      (LocalizedModule.mkLinearMap I.primeCompl M)
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl M)
    ext
    simp only [LocalizedModule.map_mk, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply,
      LocalizedModule.mkLinearMap_apply, LinearMap.flip_apply,
      LinearMap.llcomp_apply, LocalizedModule.map_mk]
  · rintro ⟨g, rfl⟩
    obtain ⟨⟨g, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective I.primeCompl
        (LocalizedModule.map I.primeCompl) g
    simp only [Function.uncurry_apply_pair]
    refine ⟨g.comp f, ⟨g, rfl⟩, s, ?_⟩
    apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
       (LocalizedModule.map I.primeCompl) s).injective
    simp only [Module.algebraMap_end_apply, LinearMap.flip_apply,
      ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
    rw [LinearMap.llcomp_apply', Submonoid.smul_def, ← LinearMap.smul_comp,
      ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext I.primeCompl
      (LocalizedModule.mkLinearMap I.primeCompl M)
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl M)
    ext
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk,
      LinearMap.flip_apply, llcomp_apply]
