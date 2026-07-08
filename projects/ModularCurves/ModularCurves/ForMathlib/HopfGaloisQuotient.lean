import ModularCurves.ForMathlib.HopfGalois
import ModularCurves.ForMathlib.SpecEqualizer
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.EffectiveEpi

/-!
# The affine quotient map is a regular epimorphism

Construction support for `T-G3d-infra` Piece 3 (`.mathlib-quality/decomposition-g3d-piece3.md`): the
first, **route-independent** half of the `@[stacks 023Q]` application. Given the co-invariant
faithful-flatness half of the Hopf-Galois property (`Module.FaithfullyFlat B^{coρ} B`), the affine
quotient map `π = specEqualizerπ ρ includeLeft : Spec B ⟶ Spec B^{coρ}` is a **regular epimorphism**
(= the coequalizer of its kernel pair), via `isRegularEpi_of_flat_of_surjective_of_isAffine`.

The chain: `Module.FaithfullyFlat B^{coρ} B` → `RingHom.FaithfullyFlat (algebraMap …)`
(`faithfullyFlat_algebraMap_iff`) → `Flat (Spec.map …) ∧ Surjective (Spec.map …)`
(`flat_and_surjective_SpecMap_iff`) → `IsRegularEpi π` (023Q; both `Spec`s affine).

The *remaining* half — that this regular epi's kernel pair is the translation groupoid (via
`IsHopfGalois.galoisEquiv`), so `π` coequalizes the `SpecEqualizer` cofork as a colimit — is the
follow-up leaf; together they give the affine-local `IsColimit` feeding `exists_unique_lift_of_isColimit`.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace ModularCurves

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The affine quotient map `π : Spec B ⟶ Spec B^{coρ}` is `Spec.map` of the co-invariants inclusion,
which is `algebraMap B^{coρ} B`. -/
theorem specEqualizerπ_includeLeft_eq (ρ : B →ₐ[R] B ⊗[R] A) :
    specEqualizerπ ρ Algebra.TensorProduct.includeLeft
      = Spec.map (CommRingCat.ofHom (algebraMap (coinvariants ρ) B)) := by
  rw [specEqualizerπ]
  rfl

/-- **The affine quotient map is a regular epimorphism.** If `B` is faithfully flat over its
co-invariants `S = B^{coρ}` (the flatness half of the Hopf-Galois property), then
`π = specEqualizerπ ρ includeLeft : Spec B ⟶ Spec S` is a regular epi — the coequalizer of its kernel
pair — by `@[stacks 023Q]`. -/
theorem isRegularEpi_specEqualizerπ (ρ : B →ₐ[R] B ⊗[R] A)
    (hff : Module.FaithfullyFlat (coinvariants ρ) B) :
    IsRegularEpi (specEqualizerπ ρ Algebra.TensorProduct.includeLeft) := by
  have hffRing : (CommRingCat.ofHom (algebraMap (coinvariants ρ) B)).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
    exact hff
  obtain ⟨hflat, hsurj⟩ :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap (coinvariants ρ) B))).mpr hffRing
  rw [specEqualizerπ_includeLeft_eq]
  haveI := hflat
  haveI := hsurj
  exact isRegularEpi_of_flat_of_surjective_of_isAffine
    (Spec.map (CommRingCat.ofHom (algebraMap (coinvariants ρ) B)))

end ModularCurves
