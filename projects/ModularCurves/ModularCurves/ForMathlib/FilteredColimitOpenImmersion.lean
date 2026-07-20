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

private theorem isClosedImmersion_pullback_snd_comp
    {X Y P Q : Scheme.{u}} (f : X ⟶ Y) (p : P ⟶ Y) (q : Q ⟶ P)
    [IsClosedImmersion (pullback.snd f p)] :
    IsClosedImmersion (pullback.snd f (q ≫ p)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f p q]
  infer_instance

/-- Closedness of a scalar extension at one stage persists after scalar extension
to any later stage. -/
theorem Scheme.Hom.isClosedImmersion_scalarExtension_of_isClosedImmersion
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    {C : Type u} [CommRing C] [Algebra (S i) C]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of C))
    (hclosed :
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j))))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) C)))))) :
    letI : Algebra (S i) (S k) :=
      (t (hij.trans hjk)).toRingHom.toAlgebra
    IsClosedImmersion
      (pullback.snd f
        (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S k))))
          (Spec.map (CommRingCat.ofHom (algebraMap (S i) C))))) := by
  letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
  letI : Algebra (S i) (S k) :=
    (t (hij.trans hjk)).toRingHom.toAlgebra
  let gj := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))
  let gk := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S k)))
  let gC := Spec.map (CommRingCat.ofHom (algebraMap (S i) C))
  let q₀ := Spec.map (CommRingCat.ofHom (t hjk).toRingHom)
  have hq₀ : q₀ ≫ gj = gk := by
    dsimp only [q₀, gj, gk]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact H.t_comp hij hjk
  let q : pullback gk gC ⟶ pullback gj gC :=
    pullback.lift (pullback.fst gk gC ≫ q₀) (pullback.snd gk gC) (by
      rw [Category.assoc, hq₀, pullback.condition])
  letI : IsClosedImmersion (pullback.snd f (pullback.snd gj gC)) := hclosed
  have h := isClosedImmersion_pullback_snd_comp f (pullback.snd gj gC) q
  have hq : q ≫ pullback.snd gj gC = pullback.snd gk gC := by
    exact pullback.lift_snd _ _ _
  rw [hq] at h
  exact h

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

/-- Finitely many compact open immersions into finitely presented affine stage targets
whose scalar extensions to the filtered colimit are closed become closed simultaneously
at one common later stage. -/
theorem Scheme.Hom.exists_common_isClosedImmersion_scalarExtension_of_isOpenImmersion
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {ρ : Type u} [Finite ρ] {i : ι}
    (C : ρ → Type u) [∀ r, CommRing (C r)] [∀ r, Algebra (S i) (C r)]
    [∀ r, Algebra.FinitePresentation (S i) (C r)]
    (X : ρ → Scheme.{u}) (f : ∀ r, X r ⟶ Spec (.of (C r)))
    [∀ r, IsOpenImmersion (f r)]
    (hcompact : ∀ r, IsCompact ((f r).opensRange : Set (Spec (.of (C r)))))
    (hclosed : ∀ r,
      letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd (f r)
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) A)))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (C r))))))) :
    ∃ (j : ι) (hij : i ≤ j), ∀ r,
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd (f r)
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j))))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (C r)))))) := by
  classical
  choose j hij hj using fun r ↦
    Scheme.Hom.exists_isClosedImmersion_scalarExtension_of_isOpenImmersion
      H (f r) (hcompact r) (hclosed r)
  letI : Fintype ρ := Fintype.ofFinite ρ
  haveI := H.directed
  haveI := H.nonempty
  obtain ⟨k, hk⟩ := (insert i (Finset.univ.image j)).exists_le
  have hik : i ≤ k := hk i (Finset.mem_insert_self i _)
  have hjk : ∀ r, j r ≤ k := fun r ↦ hk (j r)
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem j (Finset.mem_univ r)))
  refine ⟨k, hik, fun r ↦ ?_⟩
  exact Scheme.Hom.isClosedImmersion_scalarExtension_of_isClosedImmersion
    H (hij r) (hjk r) (f r) (hj r)

end

end AlgebraicGeometry
