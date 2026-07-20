/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import ModularCurves.ForMathlib.FilteredColimitCompactOpen

/-!
# Closed scalar extensions of compact open immersions

Closedness of a compact open immersion into an affine finitely presented target descends
from a filtered colimit to one later scalar-extension stage.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (S i →ₐ[R] S j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, S i →ₐ[R] A}

/-- A compact open immersion into a finitely presented affine stage target whose scalar
extension to the filtered colimit is closed is already closed after scalar extension to
one later stage. -/
theorem Scheme.Hom.exists_isClosedImmersion_scalarExtension_of_isOpenImmersion
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {i : ι} {C : Type u} [CommRing C] [Algebra (S i) C]
    [Algebra.FinitePresentation (S i) C]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of C)) [IsOpenImmersion f]
    (hcompact : IsCompact (f.opensRange : Set (Spec (.of C))))
    (hclosed :
      letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) A)))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) C)))))) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j))))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) C))))) := by
  letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
  let gA := Spec.map (CommRingCat.ofHom (algebraMap (S i) A))
  let gC := Spec.map (CommRingCat.ofHom (algebraMap (S i) C))
  let pA := pullback.snd gA gC
  let fA := pullback.snd f pA
  let eA := pullbackSpecIso (S i) A C
  letI : IsClosedImmersion fA := hclosed
  have hrange : IsClopen
      (fA.opensRange : Set ((pullback gA gC).carrier : Type u)) := by
    refine ⟨?_, fA.opensRange.isOpen⟩
    rw [Scheme.Hom.coe_opensRange]
    exact fA.isClosedEmbedding.isClosed_range
  have hopenA : eA.inv ⁻¹ᵁ fA.opensRange =
      TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight (R := S i) (A := A)).toRingHom,
          PrimeSpectrum.continuous_comap _⟩ f.opensRange := by
    rw [Scheme.Hom.opensRange_pullbackSnd, ← Scheme.Hom.comp_preimage]
    rw [pullbackSpecIso_inv_snd]
    rfl
  have hclopenA : IsClopen
      ((↑(TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight (R := S i) (A := A)).toRingHom,
          PrimeSpectrum.continuous_comap _⟩ f.opensRange) :
            Set (PrimeSpectrum (A ⊗[S i] C)))) := by
    rw [← hopenA]
    exact hrange.preimage eA.inv.continuous
  obtain ⟨j, hij, hj⟩ :=
    H.exists_isClopen_comap_tensorProduct f.opensRange hcompact hclopenA
  refine ⟨j, hij, ?_⟩
  letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
  let gj := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))
  let pj := pullback.snd gj gC
  let fj := pullback.snd f pj
  let ej := pullbackSpecIso (S i) (S j) C
  apply IsClosedImmersion.of_isPreimmersion fj
  have hopenj : ej.hom ⁻¹ᵁ
        TopologicalSpace.Opens.comap
          ⟨PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight
                (R := S i) (A := S j) (B := C)).toRingHom,
            PrimeSpectrum.continuous_comap _⟩ f.opensRange =
      fj.opensRange := by
    rw [Scheme.Hom.opensRange_pullbackSnd]
    change ej.hom ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := S i) (A := S j) (B := C)).toRingHom) ⁻¹ᵁ
          f.opensRange) = pj ⁻¹ᵁ f.opensRange
    rw [← Scheme.Hom.comp_preimage]
    have hprojection : ej.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := S i) (A := S j) (B := C)).toRingHom) = pj := by
      dsimp only [ej, pj, gj, gC]
      rw [show Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := S i) (A := S j) (B := C)).toRingHom) =
          Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
            (Algebra.TensorProduct.includeRight
              (R := S i) (A := S j) (B := C)))) from rfl]
      exact pullbackSpecIso_hom_snd (S i) (S j) C
    rw [hprojection]
  rw [← Scheme.Hom.coe_opensRange, ← hopenj]
  exact (hj.preimage ej.hom.continuous).1

end

end AlgebraicGeometry
