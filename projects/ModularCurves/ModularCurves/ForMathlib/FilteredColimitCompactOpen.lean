/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FinitePresentationBaseChangeEquiv

/-!
# Compact opens over filtered colimits

A compact open in a finitely presented affine scheme whose scalar extension is clopen
is already clopen after scalar extension to one later stage.
-/

open TensorProduct TopologicalSpace

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (S i →ₐ[R] S j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, S i →ₐ[R] A}

/-- A compact open of a finitely presented stage algebra which becomes clopen after
scalar extension to a filtered colimit becomes clopen at one later scalar-extension
stage. -/
theorem IsFilteredAlgColimit.exists_isClopen_comap_tensorProduct
    (H : IsFilteredAlgColimit R S t A uA)
    {i : ι} {C : Type u} [CommRing C] [Algebra (S i) C]
    [FinitePresentation (S i) C]
    (U : TopologicalSpace.Opens (PrimeSpectrum C))
    (hcompact : IsCompact (U : Set (PrimeSpectrum C)))
    (hclopen :
      letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
      IsClopen
        ((↑(TopologicalSpace.Opens.comap
          ⟨PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight (R := S i) (A := A)).toRingHom,
            PrimeSpectrum.continuous_comap _⟩ U) :
              Set (PrimeSpectrum (A ⊗[S i] C))))) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClopen
        ((↑(TopologicalSpace.Opens.comap
          ⟨PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight (R := S i) (A := S j)).toRingHom,
            PrimeSpectrum.continuous_comap _⟩ U) :
              Set (PrimeSpectrum (S j ⊗[S i] C)))) := by
  classical
  obtain ⟨s, hU⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp
    ⟨hcompact, U.isOpen⟩
  have hU' : U = ⨆ q : s, PrimeSpectrum.basicOpen q.1 := by
    apply TopologicalSpace.Opens.ext
    rw [← hU]
    simp only [TopologicalSpace.Opens.coe_iSup,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter,
      ← PrimeSpectrum.zeroLocus_iUnion]
    congr 2
    ext x
    simp
  letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
  have hlimit : IsClopen
      ((↑(⨆ q : s, PrimeSpectrum.basicOpen
        ((1 : A) ⊗ₜ[S i] q.1)) :
          Set (PrimeSpectrum (A ⊗[S i] C)))) := by
    rw [hU', map_iSup] at hclopen
    have hinclude (q : s) :
        (Algebra.TensorProduct.includeRight (R := S i) (A := A)).toRingHom q.1 =
          (1 : A) ⊗ₜ[S i] q.1 := rfl
    simpa only [PrimeSpectrum.comap_basicOpen, hinclude] using hclopen
  obtain ⟨j, hij, hj⟩ :=
    H.exists_isClopen_iSup_basicOpen_tensorProduct (fun q : s => q.1) hlimit
  refine ⟨j, hij, ?_⟩
  letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
  rw [hU', map_iSup]
  have hinclude (q : s) :
      (Algebra.TensorProduct.includeRight (R := S i) (A := S j)).toRingHom q.1 =
        (1 : S j) ⊗ₜ[S i] q.1 := rfl
  simpa only [PrimeSpectrum.comap_basicOpen, hinclude] using hj

end Algebra
