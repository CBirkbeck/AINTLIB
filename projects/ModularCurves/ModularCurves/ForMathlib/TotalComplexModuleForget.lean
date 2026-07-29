import ModularCurves.ForMathlib.TotalComplexUpNatVerticalEdge
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Forgetting scalars commutes with total complexes

The forgetful functor from modules to additive commutative groups preserves the
coproducts defining the total complex of a first-quadrant bicomplex. This file
packages the resulting isomorphism and its formulas on coproduct injections and
differentials.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]

/-- The forgetful functor from `R`-modules to additive commutative groups. -/
abbrev moduleForgetToAddCommGrp :
    ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- A module-valued bicomplex regarded as an additive-group-valued bicomplex. -/
abbrev moduleForgetBicomplex
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ)) :
    HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) where
  X i :=
    { X := fun j => moduleForgetToAddCommGrp.obj ((K.X i).X j)
      d := fun j j' => moduleForgetToAddCommGrp.map ((K.X i).d j j')
      shape := fun j j' h => by
        rw [(K.X i).shape j j' h, Functor.map_zero]
      d_comp_d' := fun j j' j'' _ _ => by
        rw [← Functor.map_comp, (K.X i).d_comp_d, Functor.map_zero] }
  d i i' :=
    { f := fun j => moduleForgetToAddCommGrp.map ((K.d i i').f j)
      comm' := fun j j' _ => by
        rw [← Functor.map_comp, ← Functor.map_comp, (K.d i i').comm] }
  shape i i' h := by
    apply HomologicalComplex.hom_ext
    intro j
    change moduleForgetToAddCommGrp.map ((K.d i i').f j) = 0
    rw [K.shape i i' h, HomologicalComplex.zero_f, Functor.map_zero]
  d_comp_d' i i' i'' _ _ := by
    apply HomologicalComplex.hom_ext
    intro j
    change
      moduleForgetToAddCommGrp.map ((K.d i i').f j) ≫
        moduleForgetToAddCommGrp.map ((K.d i' i'').f j) = 0
    rw [← Functor.map_comp, ← HomologicalComplex.comp_f,
      K.d_comp_d, HomologicalComplex.zero_f, Functor.map_zero]

variable (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ))

variable [K.HasTotal (.up ℕ)]

private def moduleTotalForgetDiagramIso (n : ℕ) :
    Discrete.functor
        (K.toGradedObject.mapObjFun
          (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) ⋙
      moduleForgetToAddCommGrp ≅
    Discrete.functor
      ((moduleForgetBicomplex K).toGradedObject.mapObjFun
        (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) :=
  Discrete.natIso fun _ => Iso.refl _

/-- The degreewise isomorphism underlying `moduleTotalForgetIso`. -/
def moduleTotalForgetXIso (n : ℕ) :
    moduleForgetToAddCommGrp.obj ((K.total (.up ℕ)).X n) ≅
      (((moduleForgetBicomplex K).total (.up ℕ)).X n) :=
  preservesColimitIso moduleForgetToAddCommGrp
      (Discrete.functor
        (K.toGradedObject.mapObjFun
          (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)) ≪≫
    HasColimit.isoOfNatIso (moduleTotalForgetDiagramIso K n)

/-- The degreewise total-complex comparison sends a forgotten coproduct
injection to the corresponding injection of the forgotten bicomplex. -/
@[reassoc]
theorem moduleForget_map_ιTotal_moduleTotalForgetXIso_hom
    (i j n : ℕ)
    (h : ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) (i, j) = n) :
    moduleForgetToAddCommGrp.map
        (K.ιTotal (.up ℕ) i j n h) ≫
      (moduleTotalForgetXIso K n).hom =
    (moduleForgetBicomplex K).ιTotal (.up ℕ) i j n h := by
  change
    moduleForgetToAddCommGrp.map
        (colimit.ι
          (Discrete.functor
            (K.toGradedObject.mapObjFun
              (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n))
          ⟨(i, j), by simpa using h⟩) ≫
      (preservesColimitIso moduleForgetToAddCommGrp
          (Discrete.functor
            (K.toGradedObject.mapObjFun
              (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)) ≪≫
        HasColimit.isoOfNatIso
          (moduleTotalForgetDiagramIso K n)).hom =
      colimit.ι
        (Discrete.functor
          ((moduleForgetBicomplex K).toGradedObject.mapObjFun
            (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n))
        ⟨(i, j), by simpa using h⟩
  rw [Iso.trans_hom, ← Category.assoc]
  rw [ι_preservesColimitIso_hom]
  rw [HasColimit.isoOfNatIso_ι_hom]
  rfl

@[reassoc]
private theorem moduleForget_ιTotal_moduleTotalForgetXIso_inv
    (i j n : ℕ)
    (h : ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) (i, j) = n) :
    (moduleForgetBicomplex K).ιTotal (.up ℕ) i j n h ≫
      (moduleTotalForgetXIso K n).inv =
    moduleForgetToAddCommGrp.map
      (K.ιTotal (.up ℕ) i j n h) := by
  rw [← moduleForget_map_ιTotal_moduleTotalForgetXIso_hom K i j n h]
  simp

@[reassoc]
private theorem moduleForget_map_ιTotalOrZero_moduleTotalForgetXIso_hom
    (i j n : ℕ) :
    moduleForgetToAddCommGrp.map
        (K.ιTotalOrZero (.up ℕ) i j n) ≫
      (moduleTotalForgetXIso K n).hom =
    (moduleForgetBicomplex K).ιTotalOrZero (.up ℕ) i j n := by
  by_cases h :
      ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) (i, j) = n
  · rw [K.ιTotalOrZero_eq (.up ℕ) i j n h,
      (moduleForgetBicomplex K).ιTotalOrZero_eq (.up ℕ) i j n h]
    exact
      moduleForget_map_ιTotal_moduleTotalForgetXIso_hom K i j n h
  · rw [K.ιTotalOrZero_eq_zero (.up ℕ) i j n h,
      (moduleForgetBicomplex K).ιTotalOrZero_eq_zero (.up ℕ) i j n h]
    rw [Functor.map_zero, zero_comp]

@[reassoc]
private theorem moduleForget_map_d₁_moduleTotalForgetXIso_hom
    {i i' : ℕ} (h : (ComplexShape.up ℕ).Rel i i') (j n : ℕ) :
    moduleForgetToAddCommGrp.map
        (K.d₁ (.up ℕ) i j n) ≫
      (moduleTotalForgetXIso K n).hom =
    (moduleForgetBicomplex K).d₁ (.up ℕ) i j n := by
  rw [K.d₁_eq' (.up ℕ) h j n,
    (moduleForgetBicomplex K).d₁_eq' (.up ℕ) h j n]
  dsimp only [moduleForgetBicomplex]
  rw [Functor.map_units_smul, Functor.map_comp]
  rw [Linear.units_smul_comp, Category.assoc,
    moduleForget_map_ιTotalOrZero_moduleTotalForgetXIso_hom]

@[reassoc]
private theorem moduleForget_map_d₂_moduleTotalForgetXIso_hom
    (i : ℕ) {j j' : ℕ} (h : (ComplexShape.up ℕ).Rel j j') (n : ℕ) :
    moduleForgetToAddCommGrp.map
        (K.d₂ (.up ℕ) i j n) ≫
      (moduleTotalForgetXIso K n).hom =
    (moduleForgetBicomplex K).d₂ (.up ℕ) i j n := by
  rw [K.d₂_eq' (.up ℕ) i h n,
    (moduleForgetBicomplex K).d₂_eq' (.up ℕ) i h n]
  dsimp only [moduleForgetBicomplex]
  rw [Functor.map_units_smul, Functor.map_comp]
  rw [Linear.units_smul_comp, Category.assoc,
    moduleForget_map_ιTotalOrZero_moduleTotalForgetXIso_hom]

@[reassoc]
private theorem moduleForget_map_D₁_moduleTotalForgetXIso_hom
    (n n' : ℕ) :
    moduleForgetToAddCommGrp.map
        (K.D₁ (.up ℕ) n n') ≫
      (moduleTotalForgetXIso K n').hom =
    (moduleTotalForgetXIso K n).hom ≫
      (moduleForgetBicomplex K).D₁ (.up ℕ) n n' := by
  apply (cancel_epi (moduleTotalForgetXIso K n).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  rw [moduleForget_ιTotal_moduleTotalForgetXIso_inv_assoc]
  rw [← Functor.map_comp_assoc, K.ι_D₁]
  rw [moduleForget_map_d₁_moduleTotalForgetXIso_hom K
    (show (ComplexShape.up ℕ).Rel i (i + 1) by rfl) j n']
  rw [(moduleForgetBicomplex K).ι_D₁]

@[reassoc]
private theorem moduleForget_map_D₂_moduleTotalForgetXIso_hom
    (n n' : ℕ) :
    moduleForgetToAddCommGrp.map
        (K.D₂ (.up ℕ) n n') ≫
      (moduleTotalForgetXIso K n').hom =
    (moduleTotalForgetXIso K n).hom ≫
      (moduleForgetBicomplex K).D₂ (.up ℕ) n n' := by
  apply (cancel_epi (moduleTotalForgetXIso K n).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  rw [moduleForget_ιTotal_moduleTotalForgetXIso_inv_assoc]
  rw [← Functor.map_comp_assoc, K.ι_D₂]
  rw [moduleForget_map_d₂_moduleTotalForgetXIso_hom K i
    (show (ComplexShape.up ℕ).Rel j (j + 1) by rfl) n']
  rw [(moduleForgetBicomplex K).ι_D₂]

@[reassoc]
private theorem moduleForget_map_total_d_moduleTotalForgetXIso_hom
    (n n' : ℕ) :
    moduleForgetToAddCommGrp.map
        ((K.total (.up ℕ)).d n n') ≫
      (moduleTotalForgetXIso K n').hom =
    (moduleTotalForgetXIso K n).hom ≫
      ((moduleForgetBicomplex K).total (.up ℕ)).d n n' := by
  rw [HomologicalComplex₂.total_d, HomologicalComplex₂.total_d,
    Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
    moduleForget_map_D₁_moduleTotalForgetXIso_hom,
    moduleForget_map_D₂_moduleTotalForgetXIso_hom]

/-- Forgetting the module structure commutes with the first-quadrant total
complex. -/
def moduleTotalForgetIso :
    (moduleForgetToAddCommGrp.mapHomologicalComplex (.up ℕ)).obj
        (K.total (.up ℕ)) ≅
      (moduleForgetBicomplex K).total (.up ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => moduleTotalForgetXIso K n)
    (fun n n' _ =>
      (moduleForget_map_total_d_moduleTotalForgetXIso_hom K n n').symm)

/-- The total-complex comparison sends a forgotten coproduct injection to the
corresponding injection of the forgotten bicomplex. -/
@[reassoc]
theorem moduleForget_map_ιTotal_moduleTotalForgetIso_hom
    (i j n : ℕ)
    (h : ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) (i, j) = n) :
    moduleForgetToAddCommGrp.map
        (K.ιTotal (.up ℕ) i j n h) ≫
      (moduleTotalForgetIso K).hom.f n =
    (moduleForgetBicomplex K).ιTotal (.up ℕ) i j n h :=
  moduleForget_map_ιTotal_moduleTotalForgetXIso_hom K i j n h

/-- The total-complex comparison sends an optional forgotten coproduct
injection to the corresponding optional injection. -/
@[reassoc]
theorem moduleForget_map_ιTotalOrZero_moduleTotalForgetIso_hom
    (i j n : ℕ) :
    moduleForgetToAddCommGrp.map
        (K.ιTotalOrZero (.up ℕ) i j n) ≫
      (moduleTotalForgetIso K).hom.f n =
    (moduleForgetBicomplex K).ιTotalOrZero (.up ℕ) i j n :=
  moduleForget_map_ιTotalOrZero_moduleTotalForgetXIso_hom K i j n

/-- The total-complex comparison intertwines the forgotten total differential
with the total differential of the forgotten bicomplex. -/
@[reassoc]
theorem moduleForget_map_total_d_moduleTotalForgetIso_hom
    (n n' : ℕ) :
    moduleForgetToAddCommGrp.map
        ((K.total (.up ℕ)).d n n') ≫
      (moduleTotalForgetIso K).hom.f n' =
    (moduleTotalForgetIso K).hom.f n ≫
      ((moduleForgetBicomplex K).total (.up ℕ)).d n n' :=
  moduleForget_map_total_d_moduleTotalForgetXIso_hom K n n'

end HomologicalComplex₂
