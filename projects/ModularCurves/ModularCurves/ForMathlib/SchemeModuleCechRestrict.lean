import ModularCurves.ForMathlib.SheafModuleCechTwoCoverVerticalEdge
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechComparison

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
  TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

attribute [local instance] moduleCechSheafPreadditive

private abbrev moduleSheafSectionsFunctor (W : Opens X) :
    Sheaf (ModuleCat.{u} R) X ⥤ ModuleCat.{u} R :=
  forget (ModuleCat R) X ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)

noncomputable local instance moduleSheafSectionsFunctor_additive
    (W : Opens X) :
    (moduleSheafSectionsFunctor (R := R) W).Additive where
  map_add := by
    intro A B f g
    rfl

/-- The module-valued sheaf Cech complex evaluated on an open. -/
noncomputable def moduleCechSectionsComplex
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((moduleSheafSectionsFunctor (R := R) W).mapHomologicalComplex
    (.up ℕ)).obj (moduleCechComplex F U)

@[simp]
theorem moduleCechSectionsComplex_X
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) (n : ℕ) :
    (moduleCechSectionsComplex F U W).X n =
      (moduleCechTerm F U n).obj.obj (op W) :=
  rfl

theorem moduleCechSectionsComplex_d
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) (n : ℕ) :
    (moduleCechSectionsComplex F U W).d n (n + 1) =
      (moduleCechDifferential F U n).hom.app (op W) := by
  change ((moduleCechComplex F U).d n (n + 1)).hom.app (op W) = _
  rw [moduleCechComplex_d]

@[reassoc]
theorem moduleCechTermSectionsIso_trans_pi
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) (n : ℕ)
    (G : (Fin (n + 1) → ι) → ModuleCat.{u} R)
    (e : ∀ i : Fin (n + 1) → ι,
      F.obj.obj
        (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) ≅ G i)
    (i : Fin (n + 1) → ι) :
    (moduleCechTermSectionsIso F U n W ≪≫ Pi.mapIso e).hom ≫
        Pi.π G i =
      (Pi.π (moduleCechTermFactor F U n) i).hom.app (op W) ≫
        (moduleCechTermFactorSectionsIso F U n W i).hom ≫
        (e i).hom := by
  rw [Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π]
  rw [← Category.assoc, moduleCechTermSectionsIso_hom_π]
  exact Category.assoc _ _ _

theorem moduleCechTermFactorSectionsIso_restriction
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) (n : ℕ)
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι)
    (h : (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (n + 1) =>
        U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a)) :
    (moduleCechTermFactorRestriction F h).hom.app (op W) ≫
        (moduleCechTermFactorSectionsIso F U (n + 1) W i).hom =
      (moduleCechTermFactorSectionsIso F U n W
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
        F.obj.map (homOfLE (inf_le_inf_left W h)).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

theorem moduleCechDifferential_app_eq_sum
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) (n : ℕ) :
    (moduleCechDifferential F U n).hom.app (op W) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (moduleCechCoface F U n k).hom.app (op W) := by
  change (moduleSheafSectionsFunctor (R := R) W).map
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        moduleCechCoface F U n k) = _
  exact Functor.map_sum _ _ Finset.univ

/-- The evaluated Cech short complex is the corresponding three-term part
of the evaluated sheaf-Cech cochain complex. -/
noncomputable def moduleCechShortComplexAppIsoSectionsComplexSc'
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) (n : ℕ) :
    moduleCechShortComplexApp F U n W ≅
      (moduleCechSectionsComplex F U W).sc' n (n + 1) (n + 2) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (moduleCechSectionsComplex_d F U W n)
    (moduleCechSectionsComplex_d F U W (n + 1))

/-- Exactness of the evaluated Cech short complex is exactness in the
corresponding degree of the evaluated cochain complex. -/
theorem moduleCechShortComplexApp_exact_iff_sectionsComplex_exactAt
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u}
    (U : ι → Opens X) (W : Opens X) (n : ℕ) :
    (moduleCechShortComplexApp F U n W).Exact ↔
      (moduleCechSectionsComplex F U W).ExactAt (n + 1) :=
  (ShortComplex.exact_iff_of_iso
      (moduleCechShortComplexAppIsoSectionsComplexSc'
        F U W n)).trans
    (HomologicalComplex.exactAt_iff'
      (moduleCechSectionsComplex F U W) n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n)
      (CochainComplex.next ℕ (n + 1))).symm

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

private theorem pasteCofaceComponentSquares
    {C : Type*} [Category C]
    {A B D E G H I J K L : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : B ⟶ G) (e : G ⟶ E)
    (p : A ⟶ H) (q : H ⟶ D)
    (r : A ⟶ I) (s : I ⟶ J) (t : J ⟶ G)
    (u : H ⟶ K) (v : K ⟶ L) (w : L ⟶ E)
    (x : I ⟶ K) (y : J ⟶ L)
    (hTarget : b ≫ c = d ≫ e)
    (hLow : a ≫ d = r ≫ s ≫ t)
    (hHigh : q ≫ c = u ≫ v ≫ w)
    (hSource : p ≫ u = r ≫ x)
    (hSections : x ≫ v = s ≫ y)
    (hFactor : y ≫ w = t ≫ e) :
    (a ≫ b) ≫ c = (p ≫ q) ≫ c := by
  calc
    (a ≫ b) ≫ c = (a ≫ d) ≫ e := by
      rw [Category.assoc, hTarget, ← Category.assoc]
    _ = (r ≫ s ≫ t) ≫ e :=
      congrArg (fun f => f ≫ e) hLow
    _ = r ≫ s ≫ (t ≫ e) := by
      simp only [Category.assoc]
    _ = r ≫ s ≫ (y ≫ w) := by rw [hFactor]
    _ = r ≫ (s ≫ y) ≫ w := by
      simp only [Category.assoc]
    _ = r ≫ (x ≫ v) ≫ w := by rw [hSections]
    _ = (r ≫ x) ≫ v ≫ w := by
      simp only [Category.assoc]
    _ = (p ≫ u) ≫ v ≫ w := by rw [hSource]
    _ = p ≫ (u ≫ v ≫ w) := by
      simp only [Category.assoc]
    _ = p ≫ (q ≫ c) := by rw [hHigh]
    _ = (p ≫ q) ≫ c := by
      simp only [Category.assoc]

/-- A scheme module viewed as its associated module-valued sheaf on the
source topological space. -/
noncomputable def baseModuleTopSheaf
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    TopCat.Sheaf (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) (TopCat.of X) :=
  ⟨baseModulePresheaf π M, baseModulePresheaf_isSheaf π M⟩

private theorem image_preimage_cechIntersection
    {X : Scheme.{u}} (W : X.Opens) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    W.ι ''ᵁ (∏ᶜ fun k : Fin (n + 1) => W.ι ⁻¹ᵁ U (i k)) =
      W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k) := by
  rw [← W.ι.preimage_cechIntersection U n i,
    W.ι.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

/-- One evaluated sheaf-Cech factor is the corresponding Cech factor of the
module restricted to the evaluating open. -/
noncomputable def baseModuleCechFactorAppRestrictIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (n : ℕ) (i : Fin (n + 1) → ι) :
    (baseModuleTopSheaf π M).obj.obj
        (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) ≅
      baseCechFactor (W.ι ≫ π) (M.restrict W.ι)
        (fun j => W.ι ⁻¹ᵁ U j) n i :=
  (baseModulePresheaf π M).mapIso
      (eqToIso (image_preimage_cechIntersection W U n i)).op ≪≫
    (baseModulePresheafRestrictAppIso π W.ι M
      (∏ᶜ fun k : Fin (n + 1) => W.ι ⁻¹ᵁ U (i k))).symm

/-- Evaluation on an open of one sheaf-Cech degree agrees with the
corresponding degree after restricting the module and the cover. -/
noncomputable def baseModuleCechTermAppRestrictIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens) (n : ℕ) :
    (TopCat.Sheaf.moduleCechTerm
        (baseModuleTopSheaf π M) U n).obj.obj
          (op W) ≅
      (baseCechComplex (W.ι ≫ π) (M.restrict W.ι)
        (fun j => W.ι ⁻¹ᵁ U j)).X n :=
  TopCat.Sheaf.moduleCechTermSectionsIso
      (baseModuleTopSheaf π M) U n W ≪≫
    Pi.mapIso (fun i =>
      baseModuleCechFactorAppRestrictIso π M U W n i)

@[reassoc]
theorem baseModuleCechTermAppRestrictIso_hom_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (n : ℕ) (i : Fin (n + 1) → ι) :
    (baseModuleCechTermAppRestrictIso π M U W n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor (W.ι ≫ π) (M.restrict W.ι)
            (fun a => W.ι ⁻¹ᵁ U a) n j) i =
      (Pi.π (TopCat.Sheaf.moduleCechTermFactor
        (baseModuleTopSheaf π M) U n) i).hom.app
          (op W) ≫
        (TopCat.Sheaf.moduleCechTermFactorSectionsIso
          (baseModuleTopSheaf π M) U n W i).hom ≫
        (baseModuleCechFactorAppRestrictIso π M U W n i).hom := by
  exact TopCat.Sheaf.moduleCechTermSectionsIso_trans_pi
    (baseModuleTopSheaf π M) U W n
    (fun j => baseCechFactor (W.ι ≫ π) (M.restrict W.ι)
      (fun a => W.ι ⁻¹ᵁ U a) n j)
    (fun j => baseModuleCechFactorAppRestrictIso π M U W n j) i

private theorem baseModuleCechFactorAppRestrictIso_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    (baseModulePresheaf π M).map
          (homOfLE
            (inf_le_inf_left W
              (leOfHom (((FormalCoproduct.mk _ U).mapPower
                (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op ≫
        (baseModuleCechFactorAppRestrictIso
          π M U W (n + 1) i).hom =
      (baseModuleCechFactorAppRestrictIso π M U W n
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
        (baseModulePresheaf (W.ι ≫ π) (M.restrict W.ι)).map
          (((FormalCoproduct.mk _ (fun a => W.ι ⁻¹ᵁ U a)).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op := by
  let δ := (SimplexCategory.δ k).toOrderHom.toFun
  let j : Fin (n + 1) → ι := i ∘ δ
  let P := baseModulePresheaf π M
  let Q := baseModulePresheaf (W.ι ≫ π) (M.restrict W.ι)
  let sourceFace :=
    ((FormalCoproduct.mk _ U).mapPower δ).φ i
  let targetFace :=
    ((FormalCoproduct.mk _ (fun a => W.ι ⁻¹ᵁ U a)).mapPower δ).φ i
  let ambientHigh : X.Opens :=
    W ⊓ ∏ᶜ fun a : Fin (n + 2) => U (i a)
  let ambientLow : X.Opens :=
    W ⊓ ∏ᶜ fun a : Fin (n + 1) => U (j a)
  let restrictedHigh : W.toScheme.Opens :=
    ∏ᶜ fun a : Fin (n + 2) => W.ι ⁻¹ᵁ U (i a)
  let restrictedLow : W.toScheme.Opens :=
    ∏ᶜ fun a : Fin (n + 1) => W.ι ⁻¹ᵁ U (j a)
  let ambientRestriction : op ambientLow ⟶ op ambientHigh :=
    (homOfLE (inf_le_inf_left W (leOfHom sourceFace))).op
  let restrictedRestriction : op restrictedLow ⟶ op restrictedHigh :=
    targetFace.op
  let imageRestriction :
      op (W.ι ''ᵁ restrictedLow) ⟶ op (W.ι ''ᵁ restrictedHigh) :=
    (homOfLE (W.ι.image_mono (leOfHom targetFace))).op
  let transportLow : op ambientLow ⟶ op (W.ι ''ᵁ restrictedLow) :=
    (eqToHom (image_preimage_cechIntersection W U n j)).op
  let transportHigh : op ambientHigh ⟶ op (W.ι ''ᵁ restrictedHigh) :=
    (eqToHom (image_preimage_cechIntersection W U (n + 1) i)).op
  let eLow :=
    baseModulePresheafRestrictAppIso π W.ι M restrictedLow
  let eHigh :=
    baseModulePresheafRestrictAppIso π W.ι M restrictedHigh
  have hnat :
      Q.map restrictedRestriction ≫ eHigh.hom =
        eLow.hom ≫ P.map imageRestriction := by
    exact baseModulePresheafRestrictAppIso_hom_naturality
      π W.ι M restrictedRestriction
  have hnatInv :
      P.map imageRestriction ≫ eHigh.inv =
        eLow.inv ≫ Q.map restrictedRestriction := by
    rw [← cancel_mono eHigh.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hnat, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have htransport :
      P.map ambientRestriction ≫ P.map transportHigh =
        P.map transportLow ≫ P.map imageRestriction := by
    rw [← P.map_comp, ← P.map_comp]
    exact congrArg P.map (Subsingleton.elim _ _)
  change
    (P.map ambientRestriction ≫ P.map transportHigh) ≫ eHigh.inv =
      P.map transportLow ≫ eLow.inv ≫ Q.map restrictedRestriction
  rw [htransport, Category.assoc, hnatInv]

/-- The open-restriction comparison commutes with every Cech coface. -/
theorem baseModuleCechTermAppRestrictIso_comp_coface
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    (baseModuleCechTermAppRestrictIso π M U W n).hom ≫
        baseCechCoface (W.ι ≫ π) (M.restrict W.ι)
          (fun a => W.ι ⁻¹ᵁ U a) n k =
      (TopCat.Sheaf.moduleCechCoface
        (baseModuleTopSheaf π M) U n k).hom.app (op W) ≫
        (baseModuleCechTermAppRestrictIso π M U W (n + 1)).hom := by
  apply Pi.hom_ext
  intro i
  change Fin (n + 2) → ι at i
  let δ := (SimplexCategory.δ k).toOrderHom.toFun
  let j : Fin (n + 1) → ι := i ∘ δ
  let h :
      (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
        ∏ᶜ fun a : Fin (n + 1) => U (j a) :=
    leOfHom (((FormalCoproduct.mk _ U).mapPower δ).φ i)
  let sourceLow :=
    (TopCat.Sheaf.moduleCechTerm
      (baseModuleTopSheaf π M) U n).obj.obj (op W)
  let sourceHigh :=
    (TopCat.Sheaf.moduleCechTerm
      (baseModuleTopSheaf π M) U (n + 1)).obj.obj (op W)
  let targetLow :=
    (baseCechComplex (W.ι ≫ π) (M.restrict W.ι)
      (fun a => W.ι ⁻¹ᵁ U a)).X n
  let targetHigh :=
    (baseCechComplex (W.ι ≫ π) (M.restrict W.ι)
      (fun a => W.ι ⁻¹ᵁ U a)).X (n + 1)
  let termLow : sourceLow ≅ targetLow :=
    baseModuleCechTermAppRestrictIso π M U W n
  let termHigh : sourceHigh ≅ targetHigh :=
    baseModuleCechTermAppRestrictIso π M U W (n + 1)
  let sourceCoface : sourceLow ⟶ sourceHigh :=
    (TopCat.Sheaf.moduleCechCoface
      (baseModuleTopSheaf π M) U n k).hom.app (op W)
  let targetCoface : targetLow ⟶ targetHigh :=
    baseCechCoface (W.ι ≫ π) (M.restrict W.ι)
      (fun a => W.ι ⁻¹ᵁ U a) n k
  let sourceLowProjection : sourceLow ⟶
      (TopCat.Sheaf.moduleCechTermFactor
        (baseModuleTopSheaf π M) U n j).obj.obj (op W) :=
    (Pi.π (TopCat.Sheaf.moduleCechTermFactor
      (baseModuleTopSheaf π M) U n) j).hom.app (op W)
  let sourceHighProjection : sourceHigh ⟶
      (TopCat.Sheaf.moduleCechTermFactor
        (baseModuleTopSheaf π M) U (n + 1) i).obj.obj (op W) :=
    (Pi.π (TopCat.Sheaf.moduleCechTermFactor
      (baseModuleTopSheaf π M) U (n + 1)) i).hom.app (op W)
  let targetLowProjection : targetLow ⟶
      baseCechFactor (W.ι ≫ π) (M.restrict W.ι)
        (fun a => W.ι ⁻¹ᵁ U a) n j :=
    Pi.π (fun a : Fin (n + 1) → ι =>
      baseCechFactor (W.ι ≫ π) (M.restrict W.ι)
        (fun b => W.ι ⁻¹ᵁ U b) n a) j
  let targetHighProjection : targetHigh ⟶
      baseCechFactor (W.ι ≫ π) (M.restrict W.ι)
        (fun a => W.ι ⁻¹ᵁ U a) (n + 1) i :=
    Pi.π (fun a : Fin (n + 2) → ι =>
      baseCechFactor (W.ι ≫ π) (M.restrict W.ι)
        (fun b => W.ι ⁻¹ᵁ U b) (n + 1) a) i
  let sourceFactorRestriction :=
    (TopCat.Sheaf.moduleCechTermFactorRestriction
      (baseModuleTopSheaf π M) h).hom.app (op W)
  let ambientRestriction :=
    (baseModulePresheaf π M).map
      (homOfLE (inf_le_inf_left W h)).op
  let targetRestriction :=
    (baseModulePresheaf (W.ι ≫ π) (M.restrict W.ι)).map
      (((FormalCoproduct.mk _ (fun a => W.ι ⁻¹ᵁ U a)).mapPower
        δ).φ i).op
  let sourceLowSections :=
    (TopCat.Sheaf.moduleCechTermFactorSectionsIso
      (baseModuleTopSheaf π M) U n W j).hom
  let sourceHighSections :=
    (TopCat.Sheaf.moduleCechTermFactorSectionsIso
      (baseModuleTopSheaf π M) U (n + 1) W i).hom
  let factorLow :=
    baseModuleCechFactorAppRestrictIso π M U W n j
  let factorHigh :=
    baseModuleCechFactorAppRestrictIso π M U W (n + 1) i
  have hTargetCoface :
      targetCoface ≫ targetHighProjection =
        targetLowProjection ≫ targetRestriction :=
    baseCechCoface_comp_π
      (W.ι ≫ π) (M.restrict W.ι)
        (fun a => W.ι ⁻¹ᵁ U a) n k i
  have hTermLow :
      termLow.hom ≫ targetLowProjection =
        sourceLowProjection ≫ sourceLowSections ≫ factorLow.hom :=
    baseModuleCechTermAppRestrictIso_hom_π π M U W n j
  have hTermHigh :
      termHigh.hom ≫ targetHighProjection =
        sourceHighProjection ≫ sourceHighSections ≫ factorHigh.hom :=
    baseModuleCechTermAppRestrictIso_hom_π π M U W (n + 1) i
  have hSourceCoface :
      sourceCoface ≫ sourceHighProjection =
        sourceLowProjection ≫ sourceFactorRestriction := by
    have hcoface :
        TopCat.Sheaf.moduleCechCoface
            (baseModuleTopSheaf π M) U n k ≫
            Pi.π (TopCat.Sheaf.moduleCechTermFactor
              (baseModuleTopSheaf π M) U (n + 1)) i =
          Pi.π (TopCat.Sheaf.moduleCechTermFactor
              (baseModuleTopSheaf π M) U n) j ≫
            TopCat.Sheaf.moduleCechTermFactorRestriction
              (baseModuleTopSheaf π M) h := by
      unfold TopCat.Sheaf.moduleCechCoface
      exact Pi.lift_π _ i
    exact congrArg (fun f => f.hom.app (op W)) hcoface
  have hSourceSections :
      sourceFactorRestriction ≫ sourceHighSections =
        sourceLowSections ≫ ambientRestriction :=
    TopCat.Sheaf.moduleCechTermFactorSectionsIso_restriction
      (baseModuleTopSheaf π M) U W n k i h
  have hFactor :
      ambientRestriction ≫ factorHigh.hom =
        factorLow.hom ≫ targetRestriction :=
    baseModuleCechFactorAppRestrictIso_naturality π M U W n k i
  exact pasteCofaceComponentSquares
    termLow.hom targetCoface targetHighProjection
    targetLowProjection targetRestriction
    sourceCoface termHigh.hom
    sourceLowProjection sourceLowSections factorLow.hom
    sourceHighProjection sourceHighSections factorHigh.hom
    sourceFactorRestriction ambientRestriction
    hTargetCoface hTermLow hTermHigh hSourceCoface
    hSourceSections hFactor

/-- The open-restriction comparison commutes with the Cech differential. -/
theorem baseModuleCechTermAppRestrictIso_comp_d
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens) (n : ℕ) :
    (baseModuleCechTermAppRestrictIso π M U W n).hom ≫
        (baseCechComplex (W.ι ≫ π) (M.restrict W.ι)
          (fun a => W.ι ⁻¹ᵁ U a)).d n (n + 1) =
      (TopCat.Sheaf.moduleCechDifferential
        (baseModuleTopSheaf π M) U n).hom.app (op W) ≫
        (baseModuleCechTermAppRestrictIso π M U W (n + 1)).hom := by
  rw [baseCechComplex_d_eq_sum_cofaces,
    TopCat.Sheaf.moduleCechDifferential_app_eq_sum]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    (baseModuleCechTermAppRestrictIso_comp_coface
      π M U W n k)

/-- Evaluating the sheaf-level Cech complex on an open is the native
base-linear Cech complex after restricting the module and cover. -/
noncomputable def baseModuleCechSectionsRestrictComplexIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens) :
    TopCat.Sheaf.moduleCechSectionsComplex
        (baseModuleTopSheaf π M) U W ≅
      baseCechComplex (W.ι ≫ π) (M.restrict W.ι)
        (fun a => W.ι ⁻¹ᵁ U a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => baseModuleCechTermAppRestrictIso π M U W n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      change
        (baseModuleCechTermAppRestrictIso π M U W i).hom ≫
            (baseCechComplex (W.ι ≫ π) (M.restrict W.ι)
              (fun a => W.ι ⁻¹ᵁ U a)).d i (i + 1) =
          (TopCat.Sheaf.moduleCechSectionsComplex
            (baseModuleTopSheaf π M) U W).d i (i + 1) ≫
            (baseModuleCechTermAppRestrictIso π M U W (i + 1)).hom
      rw [TopCat.Sheaf.moduleCechSectionsComplex_d]
      exact baseModuleCechTermAppRestrictIso_comp_d π M U W i)

/-- Evaluated sheaf-Cech exactness on an open is native base-linear Cech
exactness for the restricted module and inverse-image cover. -/
theorem moduleCechShortComplexApp_exact_iff_baseCechComplex_restrict
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (W : X.Opens) (n : ℕ) :
    (TopCat.Sheaf.moduleCechShortComplexApp
      (baseModuleTopSheaf π M) U n W).Exact ↔
      (baseCechComplex (W.ι ≫ π) (M.restrict W.ι)
        (fun a => W.ι ⁻¹ᵁ U a)).ExactAt (n + 1) := by
  refine
    (TopCat.Sheaf.moduleCechShortComplexApp_exact_iff_sectionsComplex_exactAt
      (baseModuleTopSheaf π M) U W n).trans ?_
  constructor
  · intro h
    exact h.of_iso (baseModuleCechSectionsRestrictComplexIso π M U W)
  · intro h
    exact h.of_iso
      (baseModuleCechSectionsRestrictComplexIso π M U W).symm

end AlgebraicGeometry.Scheme.Modules
