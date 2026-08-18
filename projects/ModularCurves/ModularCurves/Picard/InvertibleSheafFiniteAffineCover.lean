import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.AffineScheme
import ModularCurves.Picard.InvertibleSheaf

/-!
# Finite affine trivializing covers of invertible sheaves

On a compact scheme, refine the defining trivializing cover of an invertible
sheaf by the affine-open basis and then take a finite subcover.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- An invertible sheaf on a compact scheme admits a finite affine open cover
on which it is trivial. -/
theorem IsInvertible.exists_finite_affine_trivializingCover
    {X : Scheme.{u}} [CompactSpace X] {M : X.Modules}
    (hM : IsInvertible M) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        ∀ i, Nonempty
          (M.restrict (U i).ι ≅ unitObj (U i).toScheme) := by
  obtain ⟨κ, V, hV, htriv⟩ := hM
  let J := {x : X.Opens × κ //
    x.1 ∈ X.affineOpens ∧ x.1 ≤ V x.2}
  let W : J → X.Opens := fun j => j.1.1
  have hW : IsOpenCover W :=
    X.isBasis_affineOpens.isOpenCover_mem_and_le
      (show IsOpenCover V from hV)
  obtain ⟨s, hs⟩ := hW.exists_finite_of_compactSpace
  refine ⟨s, inferInstance, fun j => W j.1, hs, ?_, ?_⟩
  · intro j
    exact j.1.2.1
  · intro j
    obtain ⟨e⟩ := htriv j.1.1.2
    exact ⟨restrictIsoOfPullbackIso M (W j.1) (restrictTrivialization j.1.2.2 e)⟩

end

end AlgebraicGeometry.Scheme.Modules
