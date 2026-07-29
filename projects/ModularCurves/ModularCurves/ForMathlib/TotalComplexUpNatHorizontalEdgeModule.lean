import ModularCurves.ForMathlib.TotalComplexModuleForget
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Module-valued horizontal edge maps

The degree-one quasi-isomorphism theorem for horizontal edge maps is transported
from additive commutative groups to modules. Exactness and homology are both
reflected by the forgetful functor.
-/

open CategoryTheory

noncomputable section

universe u

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]

variable (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ))

private abbrev moduleForgetComplex
    (A : CochainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (moduleForgetToAddCommGrp.mapHomologicalComplex (.up ℕ)).obj A

private theorem moduleForgetHorizontal_comm
    (A : CochainComplex (ModuleCat.{u} R) ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (q q' : ℕ) (h : (ComplexShape.up ℕ).Rel q q') :
    moduleForgetToAddCommGrp.map (e q) ≫
        ((moduleForgetBicomplex K).d q q').f 0 =
      (moduleForgetComplex A).d q q' ≫
        moduleForgetToAddCommGrp.map (e q') := by
  dsimp only [moduleForgetBicomplex, moduleForgetComplex]
  rw [Functor.mapHomologicalComplex_obj_d]
  rw [← Functor.map_comp, he q q' h, Functor.map_comp]
  rfl

private theorem moduleForgetHorizontal_zero
    {A : CochainComplex (ModuleCat.{u} R) ℕ}
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (q : ℕ) :
    moduleForgetToAddCommGrp.map (e q) ≫
        ((moduleForgetBicomplex K).X q).d 0 1 = 0 := by
  dsimp only [moduleForgetBicomplex]
  rw [← Functor.map_comp, w q, Functor.map_zero]

variable [K.HasTotal (.up ℕ)]

/-- Forgetting a module-valued horizontal edge and then comparing total
complexes gives the horizontal edge of the forgotten bicomplex. -/
theorem moduleForget_map_totalUpNatHorizontalEdge_comp
    (A : CochainComplex (ModuleCat.{u} R) ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0) :
    (moduleForgetToAddCommGrp.mapHomologicalComplex (.up ℕ)).map
        (K.totalUpNatHorizontalEdge A e he w) ≫
      (moduleTotalForgetIso K).hom =
    (moduleForgetBicomplex K).totalUpNatHorizontalEdge
      (moduleForgetComplex A)
      (fun q => moduleForgetToAddCommGrp.map (e q))
      (moduleForgetHorizontal_comm K A e he)
      (moduleForgetHorizontal_zero K e w) := by
  apply HomologicalComplex.hom_ext
  intro q
  change
    moduleForgetToAddCommGrp.map
        ((K.totalUpNatHorizontalEdge A e he w).f q) ≫
      (moduleTotalForgetIso K).hom.f q =
    ((moduleForgetBicomplex K).totalUpNatHorizontalEdge
      (moduleForgetComplex A)
      (fun q => moduleForgetToAddCommGrp.map (e q))
      (moduleForgetHorizontal_comm K A e he)
      (moduleForgetHorizontal_zero K e w)).f q
  rw [K.totalUpNatHorizontalEdge_f]
  change
    moduleForgetToAddCommGrp.map
        (e q ≫ K.ιTotal (.up ℕ) q 0 q rfl) ≫
      (moduleTotalForgetXIso K q).hom =
    moduleForgetToAddCommGrp.map (e q) ≫
      (moduleForgetBicomplex K).ιTotal (.up ℕ) q 0 q rfl
  rw [Functor.map_comp_assoc,
    moduleForget_map_ιTotal_moduleTotalForgetXIso_hom]

private theorem moduleForgetHorizontal_row_exact
    {X₁ X₂ X₃ : ModuleCat.{u} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk
      (moduleForgetToAddCommGrp.map f)
      (moduleForgetToAddCommGrp.map g)
      (by rw [← Functor.map_comp, hfg, Functor.map_zero])).Exact := by
  exact (ShortComplex.exact_iff_exact_map_forget₂
    (S := ShortComplex.mk f g hfg)).mp h

/-- The horizontal edge of a module-valued first-quadrant bicomplex is a
quasi-isomorphism in degree one under the three low-row exactness hypotheses. -/
theorem totalUpNatHorizontalEdge_quasiIsoAt_one_module
    (A : CochainComplex (ModuleCat.{u} R) ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (hrow00 : (ShortComplex.mk
      (e 0) ((K.X 0).d 0 1) (w 0)).Exact)
    (hrow10 : (ShortComplex.mk
      (e 1) ((K.X 1).d 0 1) (w 1)).Exact)
    (hrow01 : (ShortComplex.mk
      ((K.X 0).d 0 1) ((K.X 0).d 1 2)
      ((K.X 0).d_comp_d 0 1 2)).Exact)
    [Mono (e 1)] [Mono (e 2)] :
    QuasiIsoAt (K.totalUpNatHorizontalEdge A e he w) 1 := by
  let A' := moduleForgetComplex A
  let K' := moduleForgetBicomplex K
  let e' : ∀ q, A'.X q ⟶ (K'.X q).X 0 :=
    fun q => moduleForgetToAddCommGrp.map (e q)
  have he' : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e' q ≫ (K'.d q q').f 0 = A'.d q q' ≫ e' q' :=
    moduleForgetHorizontal_comm K A e he
  have w' : ∀ q, e' q ≫ (K'.X q).d 0 1 = 0 :=
    moduleForgetHorizontal_zero K e w
  have hrow00' : (ShortComplex.mk
      (e' 0) ((K'.X 0).d 0 1) (w' 0)).Exact :=
    moduleForgetHorizontal_row_exact (e 0) ((K.X 0).d 0 1)
      (w 0) hrow00
  have hrow10' : (ShortComplex.mk
      (e' 1) ((K'.X 1).d 0 1) (w' 1)).Exact :=
    moduleForgetHorizontal_row_exact (e 1) ((K.X 1).d 0 1)
      (w 1) hrow10
  have hrow01' : (ShortComplex.mk
      ((K'.X 0).d 0 1) ((K'.X 0).d 1 2)
      ((K'.X 0).d_comp_d 0 1 2)).Exact :=
    moduleForgetHorizontal_row_exact
      ((K.X 0).d 0 1) ((K.X 0).d 1 2)
      ((K.X 0).d_comp_d 0 1 2) hrow01
  letI : Mono (e' 1) := Functor.map_mono
    moduleForgetToAddCommGrp (e 1)
  letI : Mono (e' 2) := Functor.map_mono
    moduleForgetToAddCommGrp (e 2)
  let edge := K.totalUpNatHorizontalEdge A e he w
  let edge' := K'.totalUpNatHorizontalEdge A' e' he' w'
  haveI : QuasiIsoAt edge' 1 :=
    K'.totalUpNatHorizontalEdge_quasiIsoAt_one
      A' e' he' w' hrow00' hrow10' hrow01'
  let mappedEdge :=
    (moduleForgetToAddCommGrp.mapHomologicalComplex (.up ℕ)).map edge
  have hcompat :
      mappedEdge ≫ (moduleTotalForgetIso K).hom = edge' :=
    moduleForget_map_totalUpNatHorizontalEdge_comp K A e he w
  haveI : QuasiIsoAt (moduleTotalForgetIso K).hom 1 :=
    quasiIsoAt_of_isIso _ _
  haveI : QuasiIsoAt
      (mappedEdge ≫ (moduleTotalForgetIso K).hom) 1 := by
    rw [hcompat]
    infer_instance
  have hMapped : QuasiIsoAt mappedEdge 1 :=
    quasiIsoAt_of_comp_right mappedEdge
      (moduleTotalForgetIso K).hom 1
  exact
    (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
      edge moduleForgetToAddCommGrp 1).mp hMapped

end HomologicalComplex₂
