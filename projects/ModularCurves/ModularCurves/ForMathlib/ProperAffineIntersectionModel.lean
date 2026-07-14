import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import ModularCurves.ForMathlib.FiniteAffineOpenCover
import ModularCurves.ForMathlib.FiniteIntersectionGlueComparison

/-!
# Finite-stage models of proper affine-intersection diagrams

A proper, locally finitely presented scheme over an affine base admits a finite
affine cover whose complete intersection diagram consists of finitely presented
base algebras. The diagram can therefore be spread to one stage of any filtered
presentation of the base ring while retaining the geometric gluing conditions.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} {J : Type u}

/-- Every object in an affine-intersection diagram is finitely presented over
the affine base when the family is locally of finite presentation. -/
theorem Scheme.Hom.affineIntersectionFunctor_obj_finitePresentation
    (π : X ⟶ S) [IsAffine S] [LocallyOfFinitePresentation π]
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (s : Finset J) :
    Algebra.FinitePresentation Γ(S, (⊤ : S.Opens))
      ((π.affineIntersectionFunctor U).obj s) := by
  classical
  by_cases hs : s.Nonempty
  · rw [π.affineIntersectionFunctor_obj_nonempty U s hs]
    letI : IsAffine (X.finiteIntersectionOpen U s).toScheme := hU s hs
    change (((X.finiteIntersectionOpen U s).ι ≫ π).appTop).hom.FinitePresentation
    exact Scheme.Hom.finitePresentation_appTop _
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [π.affineIntersectionFunctor_obj_empty U]
    exact Algebra.FinitePresentation.self _

/-- A proper, locally finitely presented family over an affine base admits a
finite affine-intersection model whose gluing conditions hold at one stage of
any filtered presentation of the base ring. -/
theorem Scheme.Hom.exists_affineIntersectionModelAtLaterStage_of_isProper
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    (π : X ⟶ S) [IsProper π] [IsAffine S] [LocallyOfFinitePresentation π]
    [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens)
      (_ : IsOpenCover U)
      (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
      (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
      (j : ι) (hMj : M.stage ≤ j),
      Scheme.GlueData.IsOpenAffineIntersectionFunctor (M.mapToStage hMj).toFunctor ∧
        Scheme.GlueData.IsPushoutAffineIntersectionFunctor (M.mapToStage hMj).toFunctor ∧
          IsIso (π.affineIntersectionGluedToOriginal U hU) := by
  obtain ⟨J, hJ, U, hcover, _, hU⟩ :=
    π.exists_finite_affine_openCover_of_isProper
  letI : Finite J := hJ
  letI : Fintype J := Fintype.ofFinite J
  letI : ∀ s : Finset J,
      Algebra.FinitePresentation Γ(S, (⊤ : S.Opens))
        ((π.affineIntersectionFunctor U).obj s) :=
    fun s => π.affineIntersectionFunctor_obj_finitePresentation U hU s
  let M := Classical.choice (H.exists_spreadFunctor (π.affineIntersectionFunctor U))
  obtain ⟨j, hMj, hopen, hpush⟩ := M.exists_affineIntersectionConditionsAtLaterStage
    (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
    (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU)
  exact ⟨J, hJ, U, hcover, hU, M, j, hMj, hopen, hpush,
    π.isIso_affineIntersectionGluedToOriginal U hcover hU⟩

end

end AlgebraicGeometry
