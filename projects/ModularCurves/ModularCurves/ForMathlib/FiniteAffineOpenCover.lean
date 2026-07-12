import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite affine open covers

This file constructs the finite affine covers used to build Čech complexes over an
affine base. Properness supplies compactness, while separatedness makes every nonempty
finite intersection of the chosen affine opens affine.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A compact scheme admits an affine open cover indexed by a finite type. -/
theorem Scheme.exists_finite_affine_openCover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ ∀ i, IsAffineOpen (U i) := by
  have hU : IsOpenCover (fun U : X.affineOpens ↦ U.1) := by
    rw [IsOpenCover, iSup_affineOpens_eq_top]
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ i.1.1, hs, fun i ↦ i.1.2⟩

/-- A proper scheme over an affine base has a finite affine open cover whose every
nonempty finite intersection is affine. -/
theorem Scheme.Hom.exists_finite_affine_openCover_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        ∀ (s : Finset ι), s.Nonempty → IsAffineOpen (⨅ i ∈ (s : Set ι), U i) := by
  letI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  letI : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨ι, hι, U, hU, hUaff⟩ := X.exists_finite_affine_openCover
  letI : Finite ι := hι
  refine ⟨ι, hι, U, hU, hUaff, fun s hs ↦ ?_⟩
  exact IsAffineOpen.biInf (s : Set ι) s.finite_toSet
    (Finset.coe_nonempty.mpr hs) fun i _ ↦ hUaff i

end AlgebraicGeometry
