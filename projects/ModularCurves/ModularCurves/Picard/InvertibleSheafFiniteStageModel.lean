import ModularCurves.ForMathlib.ProperAffineIntersectionModel
import ModularCurves.Picard.InvertibleSheafFiniteAffineCover

/-!
# Finite-stage models adapted to invertible sheaves

An invertible sheaf on a proper family admits a finite affine trivializing cover. The same
cover can be used to spread the family's complete affine-intersection diagram to a finite
stage of a filtered presentation of the affine base.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- An invertible sheaf on a proper, locally finitely presented family admits a finite affine
trivializing cover whose affine-intersection model recovers the family after base change. -/
theorem IsInvertible.exists_affineIntersectionModelBaseChangeIso_of_isProper
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {X S : Scheme.{u}} {π : X ⟶ S} [IsProper π] [IsAffine S]
    [LocallyOfFinitePresentation π] [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    {N : X.Modules} (hN : IsInvertible N)
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens)
      (_ : IsOpenCover U) (_ : ∀ i, IsAffineOpen (U i))
      (_ : ∀ i, Nonempty (N.restrict (U i).ι ≅ unitObj (U i).toScheme))
      (_ : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
      (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
      (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
      (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor),
      Nonempty
        (letI : Algebra (𝒮 M.stage) Γ(S, (⊤ : S.Opens)) :=
            (uS M.stage).toRingHom.toAlgebra;
          CategoryTheory.Limits.pullback
              (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM)
              (Spec.map (CommRingCat.ofHom
                (algebraMap (𝒮 M.stage) Γ(S, (⊤ : S.Opens))))) ≅ X) := by
  letI : CompactSpace X := (quasiCompact_iff_compactSpace π).mp inferInstance
  obtain ⟨J, hJ, U, hcover, hUaff, htriv⟩ :=
    hN.exists_finite_affine_trivializingCover
  letI : Finite J := hJ
  obtain ⟨hU, M, hopenM, hpushM, e⟩ :=
    π.exists_affineIntersectionModelBaseChangeIso_of_isProper_of_cover
      H U hcover hUaff
  exact ⟨J, hJ, U, hcover, hUaff, htriv, hU, M, hopenM, hpushM, e⟩

end

end AlgebraicGeometry.Scheme.Modules
