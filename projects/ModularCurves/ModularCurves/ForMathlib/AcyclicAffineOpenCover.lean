import ModularCurves.ForMathlib.AffineVanishing
import ModularCurves.ForMathlib.FiniteAffineOpenCover

/-!
# Acyclic finite affine covers

A proper scheme over an affine base has a finite affine cover on whose nonempty finite
intersections every quasicoherent module has vanishing positive-degree sheaf cohomology.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

/-- A quasicoherent module has vanishing positive-degree cohomology after restriction to
an affine open. -/
theorem restrict_subsingleton_H_of_isAffineOpen {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Subsingleton (H ((TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj M.sheaf)
      (n + 1)) := by
  change Subsingleton (H (M.restrict U.ι).sheaf (n + 1))
  letI : IsAffine U := hU
  exact affine_subsingleton_H (M.restrict U.ι) n

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- A proper scheme over an affine base has a finite affine cover which is acyclic for
every quasicoherent module on every nonempty finite intersection. -/
theorem Scheme.Hom.exists_finite_affine_openCover_acyclic
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S]
    (M : X.Modules) [M.IsQuasicoherent] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        ∀ (s : Finset ι), s.Nonempty → ∀ n : ℕ,
          Subsingleton (CategoryTheory.Sheaf.H
            ((TopCat.Sheaf.restrict AddCommGrpCat
              (⨅ i ∈ (s : Set ι), U i).isOpenEmbedding).obj M.sheaf) (n + 1)) := by
  obtain ⟨ι, hι, U, hU, hUaff, hinter⟩ :=
    f.exists_finite_affine_openCover_of_isProper
  letI : Finite ι := hι
  refine ⟨ι, hι, U, hU, hUaff, fun s hs n ↦ ?_⟩
  exact Scheme.Modules.restrict_subsingleton_H_of_isAffineOpen M _ (hinter s hs) n

end AlgebraicGeometry
