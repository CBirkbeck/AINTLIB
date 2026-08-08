/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SchemeModuleCanonicalSupportChowLowDegreeAssembly
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechSupportInduction

/-!
# Cech finiteness for proper schemes

Canonical-support Chow comodels and closed-support induction imply
finiteness of ordered base-Cech homology in every degree for coherent
modules on a Noetherian proper scheme.

The Chow-comodel chain is stated for a base of the syntactic shape `Spec (.of R)`, because it
runs through relative projective factorizations over `MvPolynomial R`. The final results are
therefore also given for an **arbitrary** Noetherian affine base
(`orderedBaseCechHomologyFinite_of_isProper_of_isAffine`,
`orderedBaseCechLowDegreeFinite_of_isProper_of_isAffine`), obtained by transporting along
`S.isoSpec` with `OrderedBaseCechHomologyFinite.of_comp`: for `f : X ⟶ Y` and `g : Y ⟶ S` the
ordered base-Cech complex of `f ≫ g` is the ordered base-Cech complex of `f` with scalars
restricted along `g.appTop`, and `ModuleCat.restrictScalars` preserves products and homology.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section CompTransport

/-! ### Transport of ordered base-Cech finiteness along a further base morphism

For `f : X ⟶ Y` and `g : Y ⟶ S` the ordered base-Cech complex of `f ≫ g` is the ordered
base-Cech complex of `f` with its scalars restricted along `g.appTop`. Restriction of scalars
is exact and preserves products, so it commutes with the whole construction and with homology;
finiteness over the smaller ring `Γ(S, ⊤)` therefore implies finiteness over `Γ(Y, ⊤)`. -/

/-- Base-linear sections for a composite are base-linear sections for the first factor with
scalars restricted along the second. -/
private theorem baseModulePresheaf_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules) :
    baseModulePresheaf f M ⋙ ModuleCat.restrictScalars g.appTop.hom =
      baseModulePresheaf (f ≫ g) M := by
  rw [baseModulePresheaf, baseModulePresheaf, Scheme.Hom.comp_appTop]
  rfl

/-- Degreewise form of `baseModulePresheaf_comp`. -/
private noncomputable def baseModulePresheafCompAppIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules) (V : X.Opensᵒᵖ) :
    (ModuleCat.restrictScalars g.appTop.hom).obj ((baseModulePresheaf f M).obj V) ≅
      (baseModulePresheaf (f ≫ g) M).obj V :=
  eqToIso (congrArg (fun P : X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens)) => P.obj V)
    (baseModulePresheaf_comp f g M))

private theorem baseModulePresheafCompAppIso_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    {V W : X.Opensᵒᵖ} (φ : V ⟶ W) :
    (ModuleCat.restrictScalars g.appTop.hom).map ((baseModulePresheaf f M).map φ) ≫
        (baseModulePresheafCompAppIso f g M W).hom =
      (baseModulePresheafCompAppIso f g M V).hom ≫ (baseModulePresheaf (f ≫ g) M).map φ :=
  (eqToIso (baseModulePresheaf_comp f g M)).hom.naturality φ

/-- Restricting scalars along `g` turns the ordered Cech cochains of `f` into the ordered Cech
cochains of `f ≫ g`. -/
private noncomputable def orderedBaseCechObjectCompIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (ModuleCat.restrictScalars g.appTop.hom).obj (orderedBaseCechObject f M U n) ≅
      orderedBaseCechObject (f ≫ g) M U n :=
  PreservesProduct.iso (ModuleCat.restrictScalars g.appTop.hom)
      (fun i : OrderedCechIndex ι n => baseCechFactor f M U n i.1) ≪≫
    Pi.mapIso fun i : OrderedCechIndex ι n =>
      baseModulePresheafCompAppIso f g M
        (Opposite.op (∏ᶜ fun k : Fin (n + 1) => U (i.1 k)))

private theorem orderedBaseCechObjectCompIso_hom_π
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : OrderedCechIndex ι n) :
    (orderedBaseCechObjectCompIso f g M U n).hom ≫
        Pi.π (fun j : OrderedCechIndex ι n =>
          baseCechFactor (f ≫ g) M U n j.1) i =
      (ModuleCat.restrictScalars g.appTop.hom).map
          (Pi.π (fun j : OrderedCechIndex ι n => baseCechFactor f M U n j.1) i) ≫
        (baseModulePresheafCompAppIso f g M
          (Opposite.op (∏ᶜ fun k : Fin (n + 1) => U (i.1 k)))).hom := by
  let F := ModuleCat.restrictScalars g.appTop.hom
  let A : OrderedCechIndex ι n → ModuleCat.{u} Γ(Y, (⊤ : Y.Opens)) :=
    fun j => baseCechFactor f M U n j.1
  let B : OrderedCechIndex ι n → ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    fun j => baseCechFactor (f ≫ g) M U n j.1
  let p : ∀ j : OrderedCechIndex ι n, F.obj (A j) ⟶ B j := fun j =>
    (baseModulePresheafCompAppIso f g M
      (Opposite.op (∏ᶜ fun k : Fin (n + 1) => U (j.1 k)))).hom
  refine (Category.assoc (piComparison F A) (Limits.Pi.map p) (Pi.π B i)).trans ?_
  refine (congrArg (fun q => piComparison F A ≫ q) (Limits.Pi.map_π p i)).trans ?_
  refine (Category.assoc (piComparison F A) (Pi.π (fun j => F.obj (A j)) i) (p i)).symm.trans ?_
  exact congrArg (fun q => q ≫ p i) (piComparison_comp_π F A i)

private theorem orderedBaseCechObjectCompIso_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) (k : Fin (n + 2)) :
    (orderedBaseCechObjectCompIso f g M U n).hom ≫
        orderedBaseCechCoface (f ≫ g) M U n k =
      (ModuleCat.restrictScalars g.appTop.hom).map (orderedBaseCechCoface f M U n k) ≫
        (orderedBaseCechObjectCompIso f g M U (n + 1)).hom := by
  let F := ModuleCat.restrictScalars g.appTop.hom
  let eLow := orderedBaseCechObjectCompIso f g M U n
  let eHigh := orderedBaseCechObjectCompIso f g M U (n + 1)
  let sourceCoface := F.map (orderedBaseCechCoface f M U n k)
  let targetCoface := orderedBaseCechCoface (f ≫ g) M U n k
  have key : ∀ a : OrderedCechIndex ι (n + 1),
      (eLow.hom ≫ targetCoface) ≫
          Pi.π (fun b : OrderedCechIndex ι (n + 1) =>
            baseCechFactor (f ≫ g) M U (n + 1) b.1) a =
        (sourceCoface ≫ eHigh.hom) ≫
          Pi.π (fun b : OrderedCechIndex ι (n + 1) =>
            baseCechFactor (f ≫ g) M U (n + 1) b.1) a := by
    intro a
    let πAlow := Pi.π (fun b : OrderedCechIndex ι n => baseCechFactor f M U n b.1) (a.delete k)
    let πAhigh :=
      Pi.π (fun b : OrderedCechIndex ι (n + 1) => baseCechFactor f M U (n + 1) b.1) a
    let πBlow :=
      Pi.π (fun b : OrderedCechIndex ι n => baseCechFactor (f ≫ g) M U n b.1) (a.delete k)
    let πBhigh :=
      Pi.π (fun b : OrderedCechIndex ι (n + 1) => baseCechFactor (f ≫ g) M U (n + 1) b.1) a
    let φ := (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ a.1).op
    let sourceMap := (baseModulePresheaf f M).map φ
    let targetMap := (baseModulePresheaf (f ≫ g) M).map φ
    let pLow := (baseModulePresheafCompAppIso f g M
      (Opposite.op (∏ᶜ fun j : Fin (n + 1) => U ((a.delete k).1 j)))).hom
    let pHigh := (baseModulePresheafCompAppIso f g M
      (Opposite.op (∏ᶜ fun j : Fin (n + 2) => U (a.1 j)))).hom
    have hTargetCoface : targetCoface ≫ πBhigh = πBlow ≫ targetMap :=
      orderedBaseCechCoface_comp_π (f ≫ g) M U n k a
    have hSourceCoface :
        orderedBaseCechCoface f M U n k ≫ πAhigh = πAlow ≫ sourceMap :=
      orderedBaseCechCoface_comp_π f M U n k a
    have hLowIso : eLow.hom ≫ πBlow = F.map πAlow ≫ pLow :=
      orderedBaseCechObjectCompIso_hom_π f g M U n (a.delete k)
    have hHighIso : eHigh.hom ≫ πBhigh = F.map πAhigh ≫ pHigh :=
      orderedBaseCechObjectCompIso_hom_π f g M U (n + 1) a
    have hFactor : F.map sourceMap ≫ pHigh = pLow ≫ targetMap :=
      baseModulePresheafCompAppIso_naturality f g M φ
    have hTargetPath :
        (eLow.hom ≫ targetCoface) ≫ πBhigh = F.map πAlow ≫ pLow ≫ targetMap := by
      refine (Category.assoc eLow.hom targetCoface πBhigh).trans ?_
      refine (congrArg (fun q => eLow.hom ≫ q) hTargetCoface).trans ?_
      refine (Category.assoc eLow.hom πBlow targetMap).symm.trans ?_
      refine (congrArg (fun q => q ≫ targetMap) hLowIso).trans ?_
      exact Category.assoc (F.map πAlow) pLow targetMap
    have hSourcePath :
        (sourceCoface ≫ eHigh.hom) ≫ πBhigh = F.map πAlow ≫ pLow ≫ targetMap := by
      refine (Category.assoc sourceCoface eHigh.hom πBhigh).trans ?_
      refine (congrArg (fun q => sourceCoface ≫ q) hHighIso).trans ?_
      refine (Category.assoc sourceCoface (F.map πAhigh) pHigh).symm.trans ?_
      refine (congrArg (fun q => q ≫ pHigh)
        (F.map_comp (orderedBaseCechCoface f M U n k) πAhigh).symm).trans ?_
      refine (congrArg (fun q => F.map q ≫ pHigh) hSourceCoface).trans ?_
      refine (congrArg (fun q => q ≫ pHigh) (F.map_comp πAlow sourceMap)).trans ?_
      refine (Category.assoc (F.map πAlow) (F.map sourceMap) pHigh).trans ?_
      exact congrArg (fun q => F.map πAlow ≫ q) hFactor
    exact hTargetPath.trans hSourcePath.symm
  exact Limits.Pi.hom_ext _ _ key

private theorem orderedBaseCechObjectCompIso_differential_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedBaseCechObjectCompIso f g M U n).hom ≫
        orderedBaseCechDifferential (f ≫ g) M U n =
      (ModuleCat.restrictScalars g.appTop.hom).map (orderedBaseCechDifferential f M U n) ≫
        (orderedBaseCechObjectCompIso f g M U (n + 1)).hom := by
  simp only [orderedBaseCechDifferential, Functor.map_sum, Functor.map_zsmul,
    Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·) (orderedBaseCechObjectCompIso_naturality f g M U n k)

/-- Restricting scalars along `g` turns the ordered base-Cech complex of `f` into the ordered
base-Cech complex of `f ≫ g`. -/
private noncomputable def orderedBaseCechComplexCompIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    ((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (orderedBaseCechComplex f M U) ≅
      orderedBaseCechComplex (f ≫ g) M U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => orderedBaseCechObjectCompIso f g M U n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      rw [Functor.mapHomologicalComplex_obj_d, orderedBaseCechComplex_d,
        orderedBaseCechComplex_d]
      exact orderedBaseCechObjectCompIso_differential_naturality f g M U i)

/-- A module that is finite after restricting scalars is finite. -/
private theorem module_finite_of_restrictScalars_finite
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : ModuleCat.{u} S)
    (h : Module.Finite R ((ModuleCat.restrictScalars φ.hom).obj N)) :
    Module.Finite S N := by
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R N := Module.compHom (N : Type u) φ.hom
  haveI : IsScalarTower R S N := ⟨fun r s m => by
    show (φ.hom r * s) • m = φ.hom r • s • m
    rw [mul_smul]⟩
  haveI : Module.Finite R N := h
  exact Module.Finite.of_restrictScalars_finite R S N

/-- Ordered base-Cech homology finiteness descends along a further base morphism: if the
homology of the complex of `f ≫ g` is finite over `Γ(S, ⊤)`, then the homology of the complex
of `f` is finite over `Γ(Y, ⊤)`.

The two complexes differ only by restriction of scalars along `g.appTop`, which is exact and
preserves products, hence commutes with homology; `Module.Finite.of_restrictScalars_finite`
then upgrades finiteness over the smaller ring. -/
theorem OrderedBaseCechHomologyFinite.of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (h : OrderedBaseCechHomologyFinite (f ≫ g) U M) :
    OrderedBaseCechHomologyFinite f U M := by
  intro n
  let F := ModuleCat.restrictScalars g.appTop.hom
  let C := orderedBaseCechComplex f M U
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex (f ≫ g) M U).homology n) := h n
  refine module_finite_of_restrictScalars_finite g.appTop (C.homology n) ?_
  exact Module.Finite.equiv
    ((((C.sc n).mapHomologyIso F).symm ≪≫
      HomologicalComplex.homologyMapIso
        (orderedBaseCechComplexCompIso f g M U) n).symm.toLinearEquiv)

end CompTransport

private def CoherentPredicate
    {X : Scheme.{u}} (M : X.Modules) : Prop :=
  M.IsFiniteType ∧ M.IsQuasicoherent

private def HomologyFiniteGood
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M : X.Modules) : Prop :=
  M.IsFiniteType ∧ M.IsQuasicoherent ∧
    OrderedBaseCechHomologyFinite π U M

private theorem exists_zero_homologyFiniteComodel
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M : X.Modules) (hM : CoherentPredicate M)
    (hzero : IsZero M) :
    ∃ (E : X.Modules) (f : M ⟶ E),
      HomologyFiniteGood π U E ∧
      CoherentPredicate
        (kernel (Abelian.factorThruImage f)) ∧
      CoherentPredicate
        (cokernel (Abelian.image.ι f)) ∧
      (IsZero (kernel (Abelian.factorThruImage f)) ∨
        closedStalkSupport
            (kernel (Abelian.factorThruImage f)) <
          closedStalkSupport M) ∧
      (IsZero (cokernel (Abelian.image.ι f)) ∨
        closedStalkSupport
            (cokernel (Abelian.image.ι f)) <
          closedStalkSupport M) := by
  letI : M.IsFiniteType := hM.1
  letI : M.IsQuasicoherent := hM.2
  have hresidual :=
    comparisonResidual_isFiniteType_and_isQuasicoherent (𝟙 M)
  refine ⟨M, 𝟙 M, ⟨hM.1, hM.2,
    OrderedBaseCechHomologyFinite.of_isZero π U hzero⟩,
    ⟨hresidual.1.1, hresidual.1.2⟩,
    ⟨hresidual.2.1, hresidual.2.2⟩, ?_, ?_⟩
  · exact Or.inl (IsZero.of_mono
      (kernel.ι (Abelian.factorThruImage (𝟙 M))) hzero)
  · exact Or.inl (IsZero.of_epi
      (cokernel.π (Abelian.image.ι (𝟙 M))) hzero)

private theorem exists_nonzero_homologyFiniteComodel
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) (hM : CoherentPredicate M)
    (hnonzero : ¬ IsZero M) :
    ∃ (E : X.Modules) (f : M ⟶ E),
      HomologyFiniteGood xπ U E ∧
      CoherentPredicate
        (kernel (Abelian.factorThruImage f)) ∧
      CoherentPredicate
        (cokernel (Abelian.image.ι f)) ∧
      (IsZero (kernel (Abelian.factorThruImage f)) ∨
        closedStalkSupport
            (kernel (Abelian.factorThruImage f)) <
          closedStalkSupport M) ∧
      (IsZero (cokernel (Abelian.image.ι f)) ∨
        closedStalkSupport
            (cokernel (Abelian.image.ι f)) <
          closedStalkSupport M) := by
  letI : M.IsFiniteType := hM.1
  letI : M.IsQuasicoherent := hM.2
  let A := CanonicalSupportThickening.ofFiniteType M
  obtain ⟨E, f, h⟩ :=
    CanonicalSupportThickening.exists_chowComodel_orderedBaseCechHomologyFinite
      (xπ := xπ) (F := M) A U hU hUaff hnonzero
  change E.IsFiniteType ∧ E.IsQuasicoherent ∧
    OrderedBaseCechHomologyFinite xπ U E ∧
    (kernel (Abelian.factorThruImage f)).IsFiniteType ∧
    (kernel (Abelian.factorThruImage f)).IsQuasicoherent ∧
    (cokernel (Abelian.image.ι f)).IsFiniteType ∧
    (cokernel (Abelian.image.ι f)).IsQuasicoherent ∧
    (IsZero (kernel (Abelian.factorThruImage f)) ∨
      closedStalkSupport
          (kernel (Abelian.factorThruImage f)) <
        closedStalkSupport M) ∧
    (IsZero (cokernel (Abelian.image.ι f)) ∨
      closedStalkSupport
          (cokernel (Abelian.image.ι f)) <
        closedStalkSupport M) at h
  obtain ⟨hEfinite, hEqc, hEcech, hKfinite, hKqc,
      hQfinite, hQqc, hKdrop, hQdrop⟩ := h
  exact
    ⟨E, f, ⟨hEfinite, hEqc, hEcech⟩,
      ⟨hKfinite, hKqc⟩, ⟨hQfinite, hQqc⟩,
      hKdrop, hQdrop⟩

private theorem exists_homologyFiniteComodel
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) (hM : CoherentPredicate M) :
    ∃ (E : X.Modules) (f : M ⟶ E),
      HomologyFiniteGood xπ U E ∧
      CoherentPredicate
        (kernel (Abelian.factorThruImage f)) ∧
      CoherentPredicate
        (cokernel (Abelian.image.ι f)) ∧
      (IsZero (kernel (Abelian.factorThruImage f)) ∨
        closedStalkSupport
            (kernel (Abelian.factorThruImage f)) <
          closedStalkSupport M) ∧
      (IsZero (cokernel (Abelian.image.ι f)) ∨
        closedStalkSupport
            (cokernel (Abelian.image.ι f)) <
          closedStalkSupport M) := by
  by_cases hzero : IsZero M
  · exact exists_zero_homologyFiniteComodel xπ U M hM hzero
  · exact exists_nonzero_homologyFiniteComodel
      U hU hUaff M hM hzero

/-- A coherent module on a Noetherian proper scheme has finite ordered
base-Cech homology in every degree for every finite affine open cover. -/
theorem orderedBaseCechHomologyFinite_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechHomologyFinite xπ U M := by
  letI : IsNoetherianRing Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv (CommRingCat.of R)
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  refine
    OrderedBaseCechHomologyFinite.of_closedStalkSupport_comodels
      xπ U hUaff CoherentPredicate (HomologyFiniteGood xπ U)
      ?_ ?_ ?_ ?_ M ?_
  · intro N hN
    exact hN.2
  · intro E hE
    exact hE.2.1
  · intro N hN
    exact exists_homologyFiniteComodel U hU hUaff N hN
  · intro E hE
    exact hE.2.2
  · exact ⟨inferInstance, inferInstance⟩

/-- A coherent module on a Noetherian proper scheme has finite ordered
base-Cech homology in degrees zero and one for every finite affine open
cover. -/
theorem orderedBaseCechLowDegreeFinite_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechLowDegreeFinite xπ U M := by
  have h :=
    orderedBaseCechHomologyFinite_of_isProper
      (xπ := xπ) U hU hUaff M
  exact ⟨h 0, h 1⟩

/-- A coherent module on a Noetherian proper scheme over an **arbitrary** Noetherian affine
base has finite ordered base-Cech homology in every degree for every finite affine open cover.

This is `orderedBaseCechHomologyFinite_of_isProper` with the syntactic base `Spec (.of R)`
relaxed to any affine `S` with Noetherian ring of global sections: the whole Chow-comodel chain
below is stated for `Spec (.of R)` (it runs through relative projective factorizations over
`MvPolynomial R`), so the statement is transported along `S.isoSpec` using
`OrderedBaseCechHomologyFinite.of_comp`. -/
theorem orderedBaseCechHomologyFinite_of_isProper_of_isAffine
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ S}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechHomologyFinite xπ U M :=
  OrderedBaseCechHomologyFinite.of_comp xπ S.isoSpec.hom M U
    (orderedBaseCechHomologyFinite_of_isProper (R := Γ(S, (⊤ : S.Opens)))
      (xπ := xπ ≫ S.isoSpec.hom) U hU hUaff M)

/-- A coherent module on a Noetherian proper scheme over an **arbitrary** Noetherian affine
base has finite ordered base-Cech homology in degrees zero and one for every finite affine open
cover. -/
theorem orderedBaseCechLowDegreeFinite_of_isProper_of_isAffine
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ S}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechLowDegreeFinite xπ U M := by
  have h :=
    orderedBaseCechHomologyFinite_of_isProper_of_isAffine
      (xπ := xπ) U hU hUaff M
  exact ⟨h 0, h 1⟩

end AlgebraicGeometry.Scheme.Modules
