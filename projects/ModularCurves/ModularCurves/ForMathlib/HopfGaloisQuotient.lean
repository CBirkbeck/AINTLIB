/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.ForMathlib.HopfGalois
import ModularCurves.ForMathlib.SpecEqualizer
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-!
# The affine quotient map is a regular epimorphism

Construction support for `T-G3d-infra` Piece 3: the first, **route-independent** half of the
`@[stacks 023Q]` application. Given the co-invariant
faithful-flatness half of the Hopf-Galois property (`Module.FaithfullyFlat B^{coρ} B`), the affine
quotient map `π = specEqualizerπ ρ includeLeft : Spec B ⟶ Spec B^{coρ}` is a **regular epimorphism**
(= the coequalizer of its kernel pair), via `isRegularEpi_of_flat_of_surjective_of_isAffine`.

The chain: `Module.FaithfullyFlat B^{coρ} B` → `RingHom.FaithfullyFlat (algebraMap …)`
(`faithfullyFlat_algebraMap_iff`) → `Flat (Spec.map …) ∧ Surjective (Spec.map …)`
(`flat_and_surjective_SpecMap_iff`) → `IsRegularEpi π` (023Q; both `Spec`s affine).

The second half (`isKernelPair_specEqualizerπ` → `isColimit_of_isHopfGalois`) identifies this
regular epi's kernel pair with the translation groupoid: the tensor pushout `B ⊗_S B` gives, under
`Spec` (`isPullback_SpecMap_of_isPushout`), the kernel pair `Spec B ×_{Spec S} Spec B`; the Galois
iso `IsHopfGalois.galoisEquiv` transports it to `Spec(B ⊗_R A)` with legs `Spec ρ, Spec includeLeft`
(the `SpecEqualizer` cofork's legs, via `canonicalGaloisMap_comp_include{Left,Right}`); then
`IsKernelPair.toCoequalizer'` (regular epi ⟹ coequalizer of its kernel pair) gives the affine-local
`IsColimit`. This is the full route-independent reduction `IsHopfGalois ρ ⟹ IsColimit`, feeding
`exists_unique_lift_of_isColimit` and thence the `SubgroupQuotient` pins.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace ModularCurves

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The affine quotient map `π : Spec B ⟶ Spec B^{coρ}` is `Spec.map` of the co-invariants
inclusion, which is `algebraMap B^{coρ} B`. -/
theorem specEqualizerπ_includeLeft_eq (ρ : B →ₐ[R] B ⊗[R] A) :
    specEqualizerπ ρ Algebra.TensorProduct.includeLeft
      = Spec.map (CommRingCat.ofHom (algebraMap (coinvariants ρ) B)) := by
  rw [specEqualizerπ]
  rfl

/-- **The affine quotient map is a regular epimorphism.** If `B` is faithfully flat over its
co-invariants `S = B^{coρ}` (the flatness half of the Hopf-Galois property), then
`π = specEqualizerπ ρ includeLeft : Spec B ⟶ Spec S` is a regular epi — the coequalizer of its
kernel pair — by `@[stacks 023Q]`. -/
theorem isRegularEpi_specEqualizerπ (ρ : B →ₐ[R] B ⊗[R] A)
    (hff : Module.FaithfullyFlat (coinvariants ρ) B) :
    IsRegularEpi (specEqualizerπ ρ Algebra.TensorProduct.includeLeft) := by
  have hffRing : (CommRingCat.ofHom (algebraMap (coinvariants ρ) B)).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
    exact hff
  obtain ⟨hflat, hsurj⟩ :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap (coinvariants ρ) B))).mpr hffRing
  rw [specEqualizerπ_includeLeft_eq]
  haveI := hflat
  haveI := hsurj
  exact isRegularEpi_of_flat_of_surjective_of_isAffine
    (Spec.map (CommRingCat.ofHom (algebraMap (coinvariants ρ) B)))

/-- **The kernel pair of the affine quotient map is the translation groupoid.** Under
`IsHopfGalois`, the pair `(Spec ρ, Spec includeLeft) : Spec (B ⊗_R A) ⇉ Spec B` is a kernel pair of
`π = specEqualizerπ ρ includeLeft`: the tensor pushout `B ⊗_S B` gives the canonical kernel pair
`Spec B ×_{Spec S} Spec B` (`isPullback_SpecMap_of_isPushout`), transported to `Spec (B ⊗_R A)`
along the Galois iso `IsHopfGalois.galoisEquiv`, whose legs are exactly `Spec ρ, Spec includeLeft`
(`canonicalGaloisMap_comp_include{Right,Left}`). -/
theorem isKernelPair_specEqualizerπ (ρ : B →ₐ[R] B ⊗[R] A) (h : IsHopfGalois ρ) :
    IsKernelPair (specEqualizerπ ρ Algebra.TensorProduct.includeLeft)
      (Spec.map (CommRingCat.ofHom ρ.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] A).toRingHom)) := by
  rw [specEqualizerπ_includeLeft_eq]
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (coinvariants ρ) B B)
  set φ : CommRingCat.of (B ⊗[coinvariants ρ] B) ≅ CommRingCat.of (B ⊗[R] A) :=
    (h.galoisEquiv.toRingEquiv).toCommRingCatIso with hφ
  refine hpb.flip.of_iso (asIso (Spec.map φ.inv)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?commfst ?commsnd ?commf ?commg
  case commfst =>
    rw [Iso.refl_hom, Category.comp_id, asIso_hom, ← Spec.map_comp]
    congr 1
    rw [Iso.eq_comp_inv]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, hφ,
      RingEquiv.toCommRingCatIso_hom]
    show h.galoisEquiv ((1 : B) ⊗ₜ[coinvariants ρ] b) = ρ b
    rw [IsHopfGalois.galoisEquiv_tmul, ← Algebra.TensorProduct.one_def, one_mul]
  case commsnd =>
    rw [Iso.refl_hom, Category.comp_id, asIso_hom, ← Spec.map_comp]
    congr 1
    rw [Iso.eq_comp_inv]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, hφ,
      RingEquiv.toCommRingCatIso_hom]
    show h.galoisEquiv (b ⊗ₜ[coinvariants ρ] (1 : B)) = b ⊗ₜ[R] 1
    rw [IsHopfGalois.galoisEquiv_tmul, map_one, mul_one]
  case commf => aesop_cat
  case commg => aesop_cat

/-- **The affine quotient map is the coequalizer of the translation groupoid** — the full
route-independent 023Q reduction. If `ρ` is Hopf-Galois, the `SpecEqualizer` cofork
`(Spec ρ, Spec includeLeft) ⇉ Spec B → Spec B^{coρ}` is a colimit: `π` is a regular epi
(`isRegularEpi_specEqualizerπ`), and its kernel pair is exactly this groupoid
(`isKernelPair_specEqualizerπ`), so `IsKernelPair.toCoequalizer'` applies. Feeds
`exists_unique_lift_of_isColimit` to discharge the `SubgroupQuotient` pins. -/
noncomputable def isColimit_of_isHopfGalois (ρ : B →ₐ[R] B ⊗[R] A) (h : IsHopfGalois ρ) :
    IsColimit (Cofork.ofπ (specEqualizerπ ρ Algebra.TensorProduct.includeLeft)
      (specMap_comp_specEqualizerπ ρ Algebra.TensorProduct.includeLeft)) := by
  haveI : IsRegularEpi (specEqualizerπ ρ Algebra.TensorProduct.includeLeft) :=
    isRegularEpi_specEqualizerπ ρ h.faithfullyFlat
  exact (isKernelPair_specEqualizerπ ρ h).toCoequalizer'

/-- **The affine Hopf-Galois quotient is the categorical quotient** — the universal property
packaged from `isColimit_of_isHopfGalois`. If `ρ` is Hopf-Galois, then every map `f : Spec B ⟶ Y`
that coequalizes `Spec ρ, Spec includeLeft` (i.e. is constant on `G`-orbits) factors *uniquely*
through the quotient map `π : Spec B ⟶ Spec B^{coρ}`. This is the ready-to-consume interface for the
glue step (and, via the `ρ = act^#` geometry bridge, the `SubgroupQuotient` pins). -/
theorem existsUnique_lift_of_isHopfGalois (ρ : B →ₐ[R] B ⊗[R] A) (h : IsHopfGalois ρ)
    {Y : Scheme.{u}} (f : Spec (CommRingCat.of B) ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ f
        = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] A).toRingHom) ≫ f) :
    ∃! g : Spec (CommRingCat.of (coinvariants ρ)) ⟶ Y,
      specEqualizerπ ρ Algebra.TensorProduct.includeLeft ≫ g = f := by
  have hcolim := isColimit_of_isHopfGalois ρ h
  refine ⟨Cofork.IsColimit.desc hcolim f hf, Cofork.IsColimit.π_desc' hcolim f hf, fun g' hg' => ?_⟩
  exact Cofork.IsColimit.hom_ext hcolim
    (hg'.trans (Cofork.IsColimit.π_desc' hcolim f hf).symm)

end ModularCurves
