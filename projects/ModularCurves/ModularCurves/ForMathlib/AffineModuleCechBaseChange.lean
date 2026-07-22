import ModularCurves.ForMathlib.AffineModulePatchBaseChangeNaturality
import ModularCurves.ForMathlib.SheafCechCochains

/-!
# Base change for affine Cech complexes of scheme modules

The patchwise affine module base-change comparisons assemble over a finite
affine cover into a degreewise comparison, and then into an isomorphism of
base-linear Cech complexes.
-/

open AlgebraicGeometry AlgebraicTopology CategoryTheory Limits Opposite
  TopologicalSpace TensorProduct
open scoped ChangeOfRings

universe u

namespace ModuleCat

/-- Extension of scalars is additive. -/
noncomputable instance extendScalars_additive
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (extendScalars f).Additive where
  map_add := by
    intro X Y p q
    letI : Module R S := Module.compHom S f
    apply ExtendScalars.hom_ext
    intro m
    change
      (extendScalars f).map (p + q) ((1 : S) ⊗ₜ[R, f] m) =
        (extendScalars f).map p ((1 : S) ⊗ₜ[R, f] m) +
          (extendScalars f).map q ((1 : S) ⊗ₜ[R, f] m)
    rw [ExtendScalars.map_tmul, ExtendScalars.map_tmul,
      ExtendScalars.map_tmul]
    have hpq : (p + q) m = p m + q m := by
      rfl
    rw [hpq, TensorProduct.tmul_add]
    rfl

end ModuleCat

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def extendScalarsDiscreteIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type u} (P : ι → ModuleCat.{u} R) :
    Discrete.functor P ⋙ ModuleCat.extendScalars f ≅
      Discrete.functor (fun i =>
        (ModuleCat.extendScalars f).obj (P i)) :=
  Discrete.natIso fun _ => Iso.refl _

private noncomputable def extendScalarsProductIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type u} [Fintype ι] (P : ι → ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj (∏ᶜ P) ≅
      ∏ᶜ fun i => (ModuleCat.extendScalars f).obj (P i) :=
  preservesLimitIso (ModuleCat.extendScalars f) (Discrete.functor P) ≪≫
    HasLimit.isoOfNatIso (extendScalarsDiscreteIso f P)

@[reassoc]
private theorem extendScalarsProductIso_hom_π
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type u} [Fintype ι] (P : ι → ModuleCat.{u} R) (i : ι) :
    (extendScalarsProductIso f P).hom ≫
        Pi.π (fun j => (ModuleCat.extendScalars f).obj (P j)) i =
      (ModuleCat.extendScalars f).map (Pi.π P i) := by
  dsimp only [extendScalarsProductIso]
  rw [Iso.trans_hom]
  change
    (preservesLimitIso (ModuleCat.extendScalars f)
        (Discrete.functor P)).hom ≫
      ((HasLimit.isoOfNatIso (extendScalarsDiscreteIso f P)).hom ≫
        limit.π (Discrete.functor fun j =>
          (ModuleCat.extendScalars f).obj (P j)) (Discrete.mk i)) = _
  rw [HasLimit.isoOfNatIso_hom_π]
  rw [preservesLimitIso_hom_π_assoc]
  rfl

private theorem cechCoface_π
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj P).δ k ≫
        Pi.π (fun j : Fin (n + 2) → ι =>
          P.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i =
      Pi.π (fun j : Fin (n + 1) → ι =>
          P.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        P.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op := by
  rw [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    FormalCoproduct.cech_map]
  exact Pi.lift_π _ i

private noncomputable def baseCechFactorBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) (i : Fin (n + 1) → ι) :
    (ModuleCat.extendScalars t.appTop.hom).obj
        ((baseModulePresheaf f M).obj
          (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) ≅
      (baseModulePresheaf (pullback.snd f t)
        ((pullback (pullback.fst f t)).obj M)).obj
          (op (∏ᶜ fun k : Fin (n + 1) =>
            pullback.fst f t ⁻¹ᵁ U (i k))) :=
  affineModuleSectionsBaseChangeIso f t M
      (∏ᶜ fun k : Fin (n + 1) => U (i k))
      (IsAffineOpen.cechIntersection U hU n i) ≪≫
    (baseModulePresheaf (pullback.snd f t)
      ((pullback (pullback.fst f t)).obj M)).mapIso
        (eqToIso
          ((pullback.fst f t).preimage_cechIntersection U n i).symm).op

private theorem baseCechFactorBaseChangeIso_hom
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) (i : Fin (n + 1) → ι) :
    (baseCechFactorBaseChangeIso f t M U hU n i).hom =
      (affineModuleSectionsBaseChangeIso f t M
        (∏ᶜ fun k : Fin (n + 1) => U (i k))
          (IsAffineOpen.cechIntersection U hU n i)).hom ≫
        (baseModulePresheaf (pullback.snd f t)
          ((pullback (pullback.fst f t)).obj M)).map
            (eqToHom
              ((pullback.fst f t).preimage_cechIntersection U n i).symm).op := by
  rfl

private theorem pullbackUnit_restrict_transport
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (W : X.Opens) {V : (Limits.pullback f t).Opens}
    (hV : V = pullback.fst f t ⁻¹ᵁ W)
    (s : (baseModulePresheaf f M).obj (op (⊤ : X.Opens))) :
    (baseModulePresheaf (pullback.snd f t)
      ((pullback (pullback.fst f t)).obj M)).map
        (eqToHom hV).op
      ((((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
        (op W))
        ((baseModulePresheaf f M).map
          (homOfLE (show W ≤ (⊤ : X.Opens) from le_top)).op s)) =
    (baseModulePresheaf (pullback.snd f t)
      ((pullback (pullback.fst f t)).obj M)).map
        (homOfLE (show V ≤ (⊤ : (Limits.pullback f t).Opens) from le_top)).op
      ((((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
        (op (⊤ : X.Opens))) s) := by
  let g := pullback.fst f t
  let P := (pullback g).obj M
  let Q := baseModulePresheaf (pullback.snd f t) P
  let hWtop : W ≤ (⊤ : X.Opens) := le_top
  let sourceRestriction := (homOfLE hWtop).op
  let targetRestriction := (homOfLE (g.preimage_mono hWtop)).op
  let targetTransport := (eqToHom hV).op
  let finalRestriction :=
    (homOfLE (show V ≤ (⊤ : (Limits.pullback f t).Opens) from le_top)).op
  let unitTop :=
    (((pullbackPushforwardAdjunction g).unit.app M).val.app
      (op (⊤ : X.Opens))) s
  have hunitNaturality := PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction g).unit.app M).val sourceRestriction s
  have htarget :
      (((pullback g ⋙ pushforward g).obj M).val.map
        sourceRestriction) unitTop =
      Q.map targetRestriction unitTop := by
    calc
      _ = P.presheaf.map
          (((TopologicalSpace.Opens.map g.base).map
            (homOfLE hWtop)).op) unitTop := by
        rfl
      _ = P.presheaf.map
          (homOfLE (g.preimage_mono hWtop)).op unitTop :=
        P.val.congr_map_apply (Subsingleton.elim _ _) unitTop
      _ = _ := by
        rfl
  have hmaps :
      Q.map targetRestriction ≫ Q.map targetTransport =
        Q.map finalRestriction := by
    rw [← Q.map_comp]
    exact Q.congr_map (Subsingleton.elim _ _)
  calc
    _ = Q.map targetTransport
        ((((pullback g ⋙ pushforward g).obj M).val.map
          sourceRestriction) unitTop) := congrArg _ hunitNaturality
    _ = Q.map targetTransport (Q.map targetRestriction unitTop) :=
      congrArg _ htarget
    _ = (Q.map targetRestriction ≫ Q.map targetTransport) unitTop := rfl
    _ = Q.map finalRestriction unitTop :=
      ConcreteCategory.congr_hom hmaps unitTop

private theorem baseCechFactorBaseChangeIso_naturality
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    (ModuleCat.extendScalars t.appTop.hom).map
          ((baseModulePresheaf f M).map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) ≫
        (baseCechFactorBaseChangeIso f t M U hU (n + 1) i).hom =
      (baseCechFactorBaseChangeIso f t M U hU n
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
        (baseModulePresheaf (pullback.snd f t)
          ((pullback (pullback.fst f t)).obj M)).map
            (((FormalCoproduct.mk _
              (fun j => pullback.fst f t ⁻¹ᵁ U j)).mapPower
                (SimplexCategory.δ k).toOrderHom.toFun).φ i).op := by
  let sourceFace :=
    ((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i
  let targetFace :=
    ((FormalCoproduct.mk _
      (fun j => pullback.fst f t ⁻¹ᵁ U j)).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i
  let j := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  have hIntersection :
      (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
        ∏ᶜ fun a : Fin (n + 1) => U (j a) :=
    leOfHom sourceFace
  let P := baseModulePresheaf f M
  let Q := baseModulePresheaf (pullback.snd f t)
    ((pullback (pullback.fst f t)).obj M)
  have hSource :
      (ModuleCat.extendScalars t.appTop.hom).map (P.map sourceFace.op) =
        (ModuleCat.extendScalars t.appTop.hom).map
          (P.map (homOfLE hIntersection).op) := by
    exact congrArg (ModuleCat.extendScalars t.appTop.hom).map
      (P.congr_map (Subsingleton.elim _ _))
  have hPatch := affineModuleSectionsBaseChangeIso_naturality
    f t M hIntersection
      (IsAffineOpen.cechIntersection U hU n j)
      (IsAffineOpen.cechIntersection U hU (n + 1) i)
  have hPatch' :
      (ModuleCat.extendScalars t.appTop.hom).map
            (P.map (homOfLE hIntersection).op) ≫
          (affineModuleSectionsBaseChangeIso f t M
            (∏ᶜ fun a : Fin (n + 2) => U (i a))
              (IsAffineOpen.cechIntersection U hU (n + 1) i)).hom =
        (affineModuleSectionsBaseChangeIso f t M
            (∏ᶜ fun a : Fin (n + 1) => U (j a))
              (IsAffineOpen.cechIntersection U hU n j)).hom ≫
          Q.map
            (homOfLE
              ((pullback.fst f t).preimage_mono hIntersection)).op := by
    dsimp only [P, Q]
    exact hPatch
  have hPatchSource :
      (ModuleCat.extendScalars t.appTop.hom).map
            (P.map sourceFace.op) ≫
          (affineModuleSectionsBaseChangeIso f t M
            (∏ᶜ fun a : Fin (n + 2) => U (i a))
              (IsAffineOpen.cechIntersection U hU (n + 1) i)).hom =
        (affineModuleSectionsBaseChangeIso f t M
            (∏ᶜ fun a : Fin (n + 1) => U (j a))
              (IsAffineOpen.cechIntersection U hU n j)).hom ≫
          Q.map
            (homOfLE
              ((pullback.fst f t).preimage_mono hIntersection)).op := by
    exact (congrArg
      (fun q => q ≫
        (affineModuleSectionsBaseChangeIso f t M
          (∏ᶜ fun a : Fin (n + 2) => U (i a))
            (IsAffineOpen.cechIntersection U hU (n + 1) i)).hom)
      hSource).trans hPatch'
  have hTransport :
      Q.map
            (homOfLE ((pullback.fst f t).preimage_mono hIntersection)).op ≫
          Q.map
            (eqToHom ((pullback.fst f t).preimage_cechIntersection
              U (n + 1) i).symm).op =
          Q.map
            (eqToHom ((pullback.fst f t).preimage_cechIntersection
              U n j).symm).op ≫
          Q.map targetFace.op := by
    let sourceRestriction :=
      (homOfLE ((pullback.fst f t).preimage_mono hIntersection)).op
    let sourceTransport :=
      (eqToHom ((pullback.fst f t).preimage_cechIntersection
        U (n + 1) i).symm).op
    let targetTransport :=
      (eqToHom ((pullback.fst f t).preimage_cechIntersection
        U n j).symm).op
    have hMaps :
        Q.map (sourceRestriction ≫ sourceTransport) =
          Q.map (targetTransport ≫ targetFace.op) :=
      Q.congr_map (Subsingleton.elim _ _)
    exact (Q.map_comp sourceRestriction sourceTransport).symm.trans <|
      hMaps.trans (Q.map_comp targetTransport targetFace.op)
  rw [baseCechFactorBaseChangeIso_hom,
    baseCechFactorBaseChangeIso_hom]
  change
    (ModuleCat.extendScalars t.appTop.hom).map (P.map sourceFace.op) ≫
          ((affineModuleSectionsBaseChangeIso f t M
            (∏ᶜ fun a : Fin (n + 2) => U (i a))
              (IsAffineOpen.cechIntersection U hU (n + 1) i)).hom ≫
            Q.map
              (eqToHom ((pullback.fst f t).preimage_cechIntersection
                U (n + 1) i).symm).op) =
      ((affineModuleSectionsBaseChangeIso f t M
          (∏ᶜ fun a : Fin (n + 1) => U (j a))
            (IsAffineOpen.cechIntersection U hU n j)).hom ≫
        Q.map
          (eqToHom ((pullback.fst f t).preimage_cechIntersection
            U n j).symm).op) ≫
          Q.map targetFace.op
  have hPatchWhisker := congrArg
    (fun q => q ≫
      Q.map
        (eqToHom ((pullback.fst f t).preimage_cechIntersection
          U (n + 1) i).symm).op)
    hPatchSource
  have hTransportWhisker := congrArg
    (fun q =>
      (affineModuleSectionsBaseChangeIso f t M
        (∏ᶜ fun a : Fin (n + 1) => U (j a))
          (IsAffineOpen.cechIntersection U hU n j)).hom ≫ q)
    hTransport
  exact (Category.assoc _ _ _).symm |>.trans hPatchWhisker
    |>.trans (Category.assoc _ _ _) |>.trans hTransportWhisker
    |>.trans (Category.assoc _ _ _).symm

/-- In each degree, extension of scalars on the base-linear Cech complex is
identified with the corresponding term for the pulled-back module and cover. -/
noncomputable def baseCechXBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) :
    (ModuleCat.extendScalars t.appTop.hom).obj
        ((baseCechComplex f M U).X n) ≅
      (baseCechComplex (pullback.snd f t)
        ((pullback (pullback.fst f t)).obj M)
          (fun i => pullback.fst f t ⁻¹ᵁ U i)).X n :=
  extendScalarsProductIso t.appTop.hom
      (fun i : Fin (n + 1) → ι =>
        (baseModulePresheaf f M).obj
          (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) ≪≫
    Pi.mapIso (fun i => baseCechFactorBaseChangeIso f t M U hU n i)

/-- The degreewise base-change comparison is componentwise the affine-patch
comparison for the corresponding Cech intersection. -/
@[reassoc]
theorem baseCechXBaseChangeIso_hom_π
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) (i : Fin (n + 1) → ι) :
    (baseCechXBaseChangeIso f t M U hU n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (baseModulePresheaf (pullback.snd f t)
            ((pullback (pullback.fst f t)).obj M)).obj
              (op (∏ᶜ fun k : Fin (n + 1) =>
                pullback.fst f t ⁻¹ᵁ U (j k)))) i =
      (ModuleCat.extendScalars t.appTop.hom).map
          (Pi.π (fun j : Fin (n + 1) → ι =>
            (baseModulePresheaf f M).obj
              (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i) ≫
        (baseCechFactorBaseChangeIso f t M U hU n i).hom := by
  dsimp only [baseCechXBaseChangeIso]
  let productIso := extendScalarsProductIso t.appTop.hom
    (fun j : Fin (n + 1) → ι =>
      (baseModulePresheaf f M).obj
        (op (∏ᶜ fun k : Fin (n + 1) => U (j k))))
  let factorIso := Pi.mapIso (fun j : Fin (n + 1) → ι =>
    baseCechFactorBaseChangeIso f t M U hU n j)
  let targetProjection := Pi.π (fun j : Fin (n + 1) → ι =>
    (baseModulePresheaf (pullback.snd f t)
      ((pullback (pullback.fst f t)).obj M)).obj
        (op (∏ᶜ fun k : Fin (n + 1) =>
          pullback.fst f t ⁻¹ᵁ U (j k)))) i
  have hTrans :
      (productIso ≪≫ factorIso).hom ≫ targetProjection =
        productIso.hom ≫ (factorIso.hom ≫ targetProjection) :=
    (congrArg (fun q => q ≫ targetProjection)
      (Iso.trans_hom productIso factorIso)).trans (Category.assoc _ _ _)
  have hPi := Pi.mapIso_hom_π
    (fun j : Fin (n + 1) → ι =>
      baseCechFactorBaseChangeIso f t M U hU n j) i
  have hPiLift := congrArg
    (fun q =>
      (extendScalarsProductIso t.appTop.hom
        (fun j : Fin (n + 1) → ι =>
          (baseModulePresheaf f M).obj
            (op (∏ᶜ fun k : Fin (n + 1) => U (j k))))).hom ≫ q) hPi
  have hProduct := extendScalarsProductIso_hom_π_assoc t.appTop.hom
    (fun j : Fin (n + 1) → ι =>
      (baseModulePresheaf f M).obj
        (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i
    (baseCechFactorBaseChangeIso f t M U hU n i).hom
  exact hTrans.trans <| hPiLift.trans hProduct

private theorem baseCechXBaseChangeIso_comm_δ
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) (k : Fin (n + 2)) :
    (ModuleCat.extendScalars t.appTop.hom).map
          (((FormalCoproduct.cosimplicialObjectFunctor
            (FormalCoproduct.mk _ U).cech).obj
              (baseModulePresheaf f M)).δ k) ≫
        (baseCechXBaseChangeIso f t M U hU (n + 1)).hom =
      (baseCechXBaseChangeIso f t M U hU n).hom ≫
        (((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _
            (fun i => pullback.fst f t ⁻¹ᵁ U i)).cech).obj
              (baseModulePresheaf (pullback.snd f t)
                ((pullback (pullback.fst f t)).obj M))).δ k) := by
  apply Pi.hom_ext
  intro i
  let E := ModuleCat.extendScalars t.appTop.hom
  let P := baseModulePresheaf f M
  let Q := baseModulePresheaf (pullback.snd f t)
    ((pullback (pullback.fst f t)).obj M)
  let sourceDelta :=
    (((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj P).δ k)
  let targetDelta :=
    (((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _
        (fun a => pullback.fst f t ⁻¹ᵁ U a)).cech).obj Q).δ k)
  let j := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let sourceFace :=
    ((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i
  let targetFace :=
    ((FormalCoproduct.mk _
      (fun a => pullback.fst f t ⁻¹ᵁ U a)).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i
  let sourceProjectionFull :=
    Pi.π (fun a : Fin (n + 2) → ι =>
      P.obj (op (∏ᶜ fun b : Fin (n + 2) => U (a b)))) i
  let sourceProjectionDeleted :=
    Pi.π (fun a : Fin (n + 1) → ι =>
      P.obj (op (∏ᶜ fun b : Fin (n + 1) => U (a b)))) j
  let targetProjectionFull :=
    Pi.π (fun a : Fin (n + 2) → ι =>
      Q.obj (op (∏ᶜ fun b : Fin (n + 2) =>
        pullback.fst f t ⁻¹ᵁ U (a b)))) i
  let targetProjectionDeleted :=
    Pi.π (fun a : Fin (n + 1) → ι =>
      Q.obj (op (∏ᶜ fun b : Fin (n + 1) =>
        pullback.fst f t ⁻¹ᵁ U (a b)))) j
  let degreeFull :=
    (baseCechXBaseChangeIso f t M U hU (n + 1)).hom
  let degreeDeleted :=
    (baseCechXBaseChangeIso f t M U hU n).hom
  let factorFull :=
    (baseCechFactorBaseChangeIso f t M U hU (n + 1) i).hom
  let factorDeleted :=
    (baseCechFactorBaseChangeIso f t M U hU n j).hom
  let sourceRestriction := P.map sourceFace.op
  let targetRestriction := Q.map targetFace.op
  have hDegreeFull :
      degreeFull ≫ targetProjectionFull =
        E.map sourceProjectionFull ≫ factorFull := by
    dsimp only [degreeFull, targetProjectionFull, E,
      sourceProjectionFull, factorFull, P, Q]
    exact baseCechXBaseChangeIso_hom_π f t M U hU (n + 1) i
  have hDegreeDeleted :
      degreeDeleted ≫ targetProjectionDeleted =
        E.map sourceProjectionDeleted ≫ factorDeleted := by
    dsimp only [degreeDeleted, targetProjectionDeleted, E,
      sourceProjectionDeleted, factorDeleted, P, Q, j]
    exact baseCechXBaseChangeIso_hom_π f t M U hU n
      (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  have hSourceCoface :
      sourceDelta ≫ sourceProjectionFull =
        sourceProjectionDeleted ≫ sourceRestriction := by
    dsimp only [sourceDelta, sourceProjectionFull,
      sourceProjectionDeleted, sourceRestriction, sourceFace, P, j]
    exact cechCoface_π U (baseModulePresheaf f M) n k i
  have hSourceMapped :
      E.map sourceDelta ≫ E.map sourceProjectionFull =
        E.map sourceProjectionDeleted ≫ E.map sourceRestriction :=
    (E.map_comp _ _).symm |>.trans (congrArg E.map hSourceCoface)
      |>.trans (E.map_comp _ _)
  have hFactor :
      E.map sourceRestriction ≫ factorFull =
        factorDeleted ≫ targetRestriction := by
    dsimp only [E, sourceRestriction, factorFull, factorDeleted,
      targetRestriction, P, Q, sourceFace, targetFace, j]
    exact baseCechFactorBaseChangeIso_naturality f t M U hU n k i
  have hTargetCoface :
      targetDelta ≫ targetProjectionFull =
        targetProjectionDeleted ≫ targetRestriction := by
    dsimp only [targetDelta, targetProjectionFull,
      targetProjectionDeleted, targetRestriction, targetFace, Q, j]
    exact cechCoface_π
      (fun a => pullback.fst f t ⁻¹ᵁ U a)
      (baseModulePresheaf (pullback.snd f t)
        ((pullback (pullback.fst f t)).obj M)) n k i
  change (E.map sourceDelta ≫ degreeFull) ≫ targetProjectionFull =
    (degreeDeleted ≫ targetDelta) ≫ targetProjectionFull
  have hLeft :
      (E.map sourceDelta ≫ degreeFull) ≫ targetProjectionFull =
        E.map sourceProjectionDeleted ≫
          (factorDeleted ≫ targetRestriction) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => E.map sourceDelta ≫ q) hDegreeFull).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ factorFull) hSourceMapped).trans
            ((Category.assoc _ _ _).trans
              (congrArg
                (fun q => E.map sourceProjectionDeleted ≫ q) hFactor)))))
  have hRight :
      (degreeDeleted ≫ targetDelta) ≫ targetProjectionFull =
        E.map sourceProjectionDeleted ≫
          (factorDeleted ≫ targetRestriction) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => degreeDeleted ≫ q) hTargetCoface).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ targetRestriction) hDegreeDeleted).trans
            (Category.assoc _ _ _))))
  exact hLeft.trans hRight.symm

private theorem baseCechComplex_d_succ
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex f M U).d n (n + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj
            (baseModulePresheaf f M)) n := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj
      (baseModulePresheaf f M)).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ n).trans rfl

private theorem baseCechXBaseChangeIso_comm_d
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) :
    (ModuleCat.extendScalars t.appTop.hom).map
          (AlternatingCofaceMapComplex.objD
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj
                (baseModulePresheaf f M)) n) ≫
        (baseCechXBaseChangeIso f t M U hU (n + 1)).hom =
      (baseCechXBaseChangeIso f t M U hU n).hom ≫
        AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor
            (FormalCoproduct.mk _
              (fun i => pullback.fst f t ⁻¹ᵁ U i)).cech).obj
                (baseModulePresheaf (pullback.snd f t)
                  ((pullback (pullback.fst f t)).obj M))) n := by
  let source :=
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj (baseModulePresheaf f M)
  let target :=
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _
        (fun i => pullback.fst f t ⁻¹ᵁ U i)).cech).obj
          (baseModulePresheaf (pullback.snd f t)
            ((pullback (pullback.fst f t)).obj M))
  let E := ModuleCat.extendScalars t.appTop.hom
  let degreeSource := (baseCechXBaseChangeIso f t M U hU n).hom
  let degreeTarget :=
    (baseCechXBaseChangeIso f t M U hU (n + 1)).hom
  have hLeft :
      E.map (AlternatingCofaceMapComplex.objD source n) ≫ degreeTarget =
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          (E.map (source.δ k) ≫ degreeTarget) := by
    have hMap :
        E.map (AlternatingCofaceMapComplex.objD source n) =
          ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
            E.map (source.δ k) := by
      simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum,
        Functor.map_zsmul]
    have hComp := Preadditive.sum_comp Finset.univ
      (fun k : Fin (n + 2) =>
        (-1 : ℤ) ^ (k : ℕ) • E.map (source.δ k)) degreeTarget
    have hSummands :
        (∑ k : Fin (n + 2),
          ((-1 : ℤ) ^ (k : ℕ) • E.map (source.δ k)) ≫ degreeTarget) =
            ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
              (E.map (source.δ k) ≫ degreeTarget) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Preadditive.zsmul_comp
        (f := E.map (source.δ k)) (g := degreeTarget)
          ((-1 : ℤ) ^ (k : ℕ))
    exact (congrArg (fun q => q ≫ degreeTarget) hMap).trans <|
      hComp.trans hSummands
  have hTerms :
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          (E.map (source.δ k) ≫ degreeTarget)) =
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          (degreeSource ≫ target.δ k) := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
      (baseCechXBaseChangeIso_comm_δ f t M U hU n k)
  have hRight :
      degreeSource ≫ AlternatingCofaceMapComplex.objD target n =
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          (degreeSource ≫ target.δ k) := by
    rw [AlternatingCofaceMapComplex.objD]
    have hComp := Preadditive.comp_sum Finset.univ degreeSource
      (fun k : Fin (n + 2) =>
        (-1 : ℤ) ^ (k : ℕ) • target.δ k)
    have hSummands :
        (∑ k : Fin (n + 2), degreeSource ≫
          ((-1 : ℤ) ^ (k : ℕ) • target.δ k)) =
            ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
              (degreeSource ≫ target.δ k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Preadditive.comp_zsmul
        (f := degreeSource) (g := target.δ k) ((-1 : ℤ) ^ (k : ℕ))
    exact hComp.trans hSummands
  change E.map (AlternatingCofaceMapComplex.objD source n) ≫ degreeTarget =
    degreeSource ≫ AlternatingCofaceMapComplex.objD target n
  exact hLeft.trans (hTerms.trans hRight.symm)

/-- Extension of scalars identifies the base-linear Cech complex of a
quasicoherent module on a finite affine cover with the corresponding complex
after affine base change. -/
noncomputable def baseCechComplexBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent] :
    ((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
        (.up ℕ)).obj (baseCechComplex f M U) ≅
      baseCechComplex (pullback.snd f t)
        ((pullback (pullback.fst f t)).obj M)
          (fun i => pullback.fst f t ⁻¹ᵁ U i) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => baseCechXBaseChangeIso f t M U hU n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      rw [Functor.mapHomologicalComplex_obj_d]
      rw [baseCechComplex_d_succ, baseCechComplex_d_succ]
      exact (baseCechXBaseChangeIso_comm_d f t M U hU i).symm)

@[simp]
theorem baseCechComplexBaseChangeIso_hom_f
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (n : ℕ) :
    (baseCechComplexBaseChangeIso f t M U hU).hom.f n =
      (baseCechXBaseChangeIso f t M U hU n).hom :=
  rfl

end AlgebraicGeometry.Scheme.Modules
