import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import ModularCurves.ForMathlib.FiniteAffineOpenCover
import ModularCurves.ForMathlib.FiniteIntersectionGlueComparison
import ModularCurves.ForMathlib.FinitePresentationSchemeBaseChange

/-!
# Finite-stage models of proper affine-intersection diagrams

A proper, locally finitely presented scheme over an affine base admits a finite
affine cover whose complete intersection diagram consists of finitely presented
base algebras. The diagram can therefore be spread to one stage of any filtered
presentation of the base ring while retaining the geometric gluing conditions.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} {J : Type u}

/-- A separated, locally finite-type morphism is proper if it has a surjective
cover whose composite to the target is proper. -/
lemma IsProper.of_comp_surjective {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper (f ≫ g)] [Surjective f] [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper g where
  toIsSeparated := inferInstance
  toUniversallyClosed := UniversallyClosed.of_comp_surjective f g
  toLocallyOfFiniteType := inferInstance

/-- A surjective map between two spread stages remains surjective after transport to any
common later stage. -/
theorem Algebra.SpreadData.mapAtLaterStage_surjective
    {R A : Type u} [CommRing R] [CommRing A]
    {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {A₁ A₂ : Type u} [CommRing A₁] [Algebra A A₁]
    [CommRing A₂] [Algebra A A₂]
    (D₁ : Algebra.SpreadData 𝒮 uA A₁) (D₂ : Algebra.SpreadData 𝒮 uA A₂)
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (hf : Function.Surjective f) :
    Function.Surjective (D₁.mapAtLaterStage D₂ H h₁ h₂ hij f) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  have hTensor : Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j)) f) :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hf
  intro y
  obtain ⟨y', hy'⟩ := (D₂.spreadStageBaseChangeEquiv hij h₂ H).surjective y
  obtain ⟨x', hx'⟩ := hTensor y'
  obtain ⟨x, hx⟩ := (D₁.spreadStageBaseChangeEquiv hij h₁ H).symm.surjective x'
  refine ⟨x, ?_⟩
  rw [D₁.mapAtLaterStage_apply D₂ H, hx, hx', hy']

/-- A compatible affine map which is a closed immersion over the filtered
colimit becomes a closed immersion at one later stage. -/
theorem Algebra.SpreadData.exists_isClosedImmersion_specMapAtLaterStage
    {R A : Type u} [CommRing R] [CommRing A]
    {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {A₁ A₂ : Type u} [CommRing A₁] [Algebra A A₁]
    [CommRing A₂] [Algebra A A₂]
    (D₁ : Algebra.SpreadData 𝒮 uA A₁) (D₂ : Algebra.SpreadData 𝒮 uA A₂)
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (F : A₁ →ₐ[A] A₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f x) =
      F (D₁.stageToColimit H ⟨i, h₁⟩ x))
    (hF : Function.Surjective F) :
    ∃ (j : ι) (hij : i ≤ j), IsClosedImmersion
      (Spec.map (CommRingCat.ofHom
        (D₁.mapAtLaterStage D₂ H h₁ h₂ hij f).toRingHom)) := by
  obtain ⟨j, hij, hsurj⟩ :=
    D₁.exists_surjective_mapAtLaterStage D₂ H h₁ h₂ f F hf hF
  exact ⟨j, hij, IsClosedImmersion.spec_of_surjective _ hsurj⟩

/-- The glued structural morphism attached to a spread affine-intersection functor is
locally of finite presentation over its stage ring. -/
theorem Algebra.SpreadData.FunctorModel.locallyOfFinitePresentation_affineIntersectionToSpec
    {R A : Type u} [CommRing R] [CommRing A]
    {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA}
    {F : Finset J ⥤ CommAlgCat.{u} A}
    (M : Algebra.SpreadData.FunctorModel F H)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    LocallyOfFinitePresentation
      (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopen hpush) :=
  Scheme.GlueData.locallyOfFinitePresentation_affineIntersectionToSpec
    M.toFunctor hopen hpush fun i =>
      M.toFunctor_obj_finitePresentation
        (Scheme.GlueData.affineIntersectionSingletonIndex i)

/-- The glued structural morphism attached to a spread affine-intersection functor with a
finite chart index is quasi-compact over its stage ring. -/
theorem Algebra.SpreadData.FunctorModel.quasiCompact_affineIntersectionToSpec
    {R A : Type u} [CommRing R] [CommRing A]
    {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA}
    {F : Finset J ⥤ CommAlgCat.{u} A} [Finite J]
    (M : Algebra.SpreadData.FunctorModel F H)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    QuasiCompact
      (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopen hpush) :=
  Scheme.GlueData.quasiCompact_affineIntersectionToSpec M.toFunctor hopen hpush

/-- A finite affine-intersection model over a Noetherian stage has Noetherian glued source. -/
theorem Algebra.SpreadData.FunctorModel.isNoetherian_affineIntersectionGlued
    {R A : Type u} [CommRing R] [CommRing A]
    {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA}
    {F : Finset J ⥤ CommAlgCat.{u} A} [Finite J]
    (M : Algebra.SpreadData.FunctorModel F H)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    [IsNoetherianRing (𝒮 M.stage)] :
    IsNoetherian
      (Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopen hpush).glued := by
  let p := Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopen hpush
  letI : LocallyOfFinitePresentation p :=
    _root_.AlgebraicGeometry.Algebra.SpreadData.FunctorModel.locallyOfFinitePresentation_affineIntersectionToSpec
      M hopen hpush
  letI : LocallyOfFiniteType p := inferInstance
  letI : QuasiCompact p :=
    _root_.AlgebraicGeometry.Algebra.SpreadData.FunctorModel.quasiCompact_affineIntersectionToSpec
      M hopen hpush
  letI : IsLocallyNoetherian (Spec (CommRingCat.of (𝒮 M.stage))) := inferInstance
  let hlocal : IsLocallyNoetherian
      (Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopen hpush).glued :=
    LocallyOfFiniteType.isLocallyNoetherian p
  letI : CompactSpace (Spec (CommRingCat.of (𝒮 M.stage))) := inferInstance
  let hcompact : CompactSpace
      (Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopen hpush).glued :=
    QuasiCompact.compactSpace_of_compactSpace p
  letI := hlocal
  letI := hcompact
  exact ⟨⟩

/-- Every nonempty finite intersection in an affine open cover of the source of a proper
morphism to an affine scheme is affine. -/
theorem Scheme.Hom.isAffineOpen_finiteIntersectionOpen_of_isProper
    (π : X ⟶ S) [IsProper π] [IsAffine S]
    (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : Finset J) (hs : s.Nonempty) :
    IsAffineOpen (X.finiteIntersectionOpen U s) := by
  letI : X.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  exact IsAffineOpen.biInf (s : Set J) s.finite_toSet
    (Finset.coe_nonempty.mpr hs) fun i _ ↦ hU i

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

/-- The affine-intersection functor of a proper family has surjective canonical pair maps. -/
theorem Scheme.Hom.isSeparatedAffineIntersectionFunctor_affineIntersectionFunctor_of_isProper
    (π : X ⟶ S) [IsProper π] [IsAffine S]
    (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    Scheme.GlueData.IsSeparatedAffineIntersectionFunctor
      (π.affineIntersectionFunctor U) := by
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  apply (Scheme.GlueData.isSeparated_affineIntersectionToSpec_iff
    (π.affineIntersectionFunctor U) hopen hpush).mp
  letI : IsIso (π.affineIntersectionGluedToOriginal U hU) :=
    π.isIso_affineIntersectionGluedToOriginal U hcover hU
  rw [← π.affineIntersectionGluedToOriginal_comp_toSpec U hU]
  infer_instance

/-- A spread affine-intersection model recovers the original scheme after base change
from its finite stage. -/
noncomputable def Scheme.Hom.affineIntersectionModelBaseChangeIso
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    (π : X ⟶ S) [IsAffine S] [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    {H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS}
    (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) Γ(S, (⊤ : S.Opens)) :=
      (uS M.stage).toRingHom.toAlgebra
    pullback
        (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (𝒮 M.stage) Γ(S, (⊤ : S.Opens))))) ≅ X := by
  classical
  letI : Algebra (𝒮 M.stage) Γ(S, (⊤ : S.Opens)) :=
    (uS M.stage).toRingHom.toAlgebra
  let hopenG := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpushG := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  letI : IsIso (π.affineIntersectionGluedToOriginal U hU) :=
    π.isIso_affineIntersectionGluedToOriginal U hcover hU
  exact M.affineIntersectionGluedBaseChangeIso hopenG hpushG hopenM hpushM ≪≫
    asIso (π.affineIntersectionGluedToOriginal U hU)

@[reassoc]
theorem Scheme.Hom.affineIntersectionModelBaseChangeIso_hom
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    (π : X ⟶ S) [IsAffine S] [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    {H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS}
    (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) Γ(S, (⊤ : S.Opens)) :=
      (uS M.stage).toRingHom.toAlgebra
    (π.affineIntersectionModelBaseChangeIso U hcover hU M hopenM hpushM).hom =
      (M.affineIntersectionGluedBaseChangeIso
          (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
          (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU)
          hopenM hpushM).hom ≫
        π.affineIntersectionGluedToOriginal U hU := rfl

/-- A chosen finite affine cover of a proper, locally finitely presented family spreads to
an affine-intersection model at one stage of a filtered presentation of the base ring. -/
theorem Scheme.Hom.exists_affineIntersectionModelAtLaterStage_of_isProper_of_cover
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    (π : X ⟶ S) [IsProper π] [IsAffine S] [LocallyOfFinitePresentation π]
    [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS)
    [Finite J] (U : J → X.Opens) (hcover : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    ∃ (hU : ∀ s : Finset J, s.Nonempty →
        IsAffineOpen (X.finiteIntersectionOpen U s))
      (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
      (j : ι) (hMj : M.stage ≤ j),
      Scheme.GlueData.IsOpenAffineIntersectionFunctor (M.mapToStage hMj).toFunctor ∧
        Scheme.GlueData.IsPushoutAffineIntersectionFunctor (M.mapToStage hMj).toFunctor ∧
          IsIso (π.affineIntersectionGluedToOriginal U hU) := by
  letI : Fintype J := Fintype.ofFinite J
  let hU := π.isAffineOpen_finiteIntersectionOpen_of_isProper U hUaff
  letI : ∀ s : Finset J,
      Algebra.FinitePresentation Γ(S, (⊤ : S.Opens))
        ((π.affineIntersectionFunctor U).obj s) :=
    fun s => π.affineIntersectionFunctor_obj_finitePresentation U hU s
  let M := Classical.choice (H.exists_spreadFunctor (π.affineIntersectionFunctor U))
  obtain ⟨j, hMj, hopen, hpush⟩ := M.exists_affineIntersectionConditionsAtLaterStage
    (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
    (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU)
  exact ⟨hU, M, j, hMj, hopen, hpush,
    π.isIso_affineIntersectionGluedToOriginal U hcover hU⟩

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
  obtain ⟨J, hJ, U, hcover, hUaff, _⟩ :=
    π.exists_finite_affine_openCover_of_isProper
  letI : Finite J := hJ
  obtain ⟨hU', M, j, hMj, hopen, hpush, hglue⟩ :=
    π.exists_affineIntersectionModelAtLaterStage_of_isProper_of_cover H U hcover hUaff
  exact ⟨J, hJ, U, hcover, hU', M, j, hMj, hopen, hpush, hglue⟩

/-- A chosen finite affine cover of a proper, locally finitely presented family has a
finite-stage affine-intersection model whose base change is the original scheme. -/
theorem Scheme.Hom.exists_affineIntersectionModelBaseChangeIso_of_isProper_of_cover
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    (π : X ⟶ S) [IsProper π] [IsAffine S] [LocallyOfFinitePresentation π]
    [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS)
    [Finite J] (U : J → X.Opens) (hcover : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    ∃ (_ : ∀ s : Finset J, s.Nonempty →
        IsAffineOpen (X.finiteIntersectionOpen U s))
      (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
      (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
      (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor),
      Nonempty
        (letI : Algebra (𝒮 M.stage) Γ(S, (⊤ : S.Opens)) :=
            (uS M.stage).toRingHom.toAlgebra;
          pullback
              (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM)
              (Spec.map (CommRingCat.ofHom
                (algebraMap (𝒮 M.stage) Γ(S, (⊤ : S.Opens))))) ≅ X) := by
  obtain ⟨hU, M, j, hMj, hopenM, hpushM, _⟩ :=
    π.exists_affineIntersectionModelAtLaterStage_of_isProper_of_cover H U hcover hUaff
  let M' := M.mapToStage hMj
  refine ⟨hU, M', hopenM, hpushM, ?_⟩
  exact ⟨π.affineIntersectionModelBaseChangeIso U hcover hU M' hopenM hpushM⟩

/-- A proper, locally finitely presented family over an affine filtered-colimit base is the
base change of a finite-stage affine-intersection model. -/
theorem Scheme.Hom.exists_affineIntersectionModelBaseChangeIso_of_isProper
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    (π : X ⟶ S) [IsProper π] [IsAffine S] [LocallyOfFinitePresentation π]
    [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens)
      (_ : IsOpenCover U)
      (_ : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
      (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
      (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
      (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor),
      Nonempty
        (letI : Algebra (𝒮 M.stage) Γ(S, (⊤ : S.Opens)) :=
            (uS M.stage).toRingHom.toAlgebra;
          pullback
              (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM)
              (Spec.map (CommRingCat.ofHom
                (algebraMap (𝒮 M.stage) Γ(S, (⊤ : S.Opens))))) ≅ X) := by
  obtain ⟨J, hJ, U, hcover, hUaff, _⟩ :=
    π.exists_finite_affine_openCover_of_isProper
  letI : Finite J := hJ
  obtain ⟨hU, M, hopenM, hpushM, e⟩ :=
    π.exists_affineIntersectionModelBaseChangeIso_of_isProper_of_cover
      H U hcover hUaff
  exact ⟨J, hJ, U, hcover, hU, M, hopenM, hpushM, e⟩

end

end AlgebraicGeometry
