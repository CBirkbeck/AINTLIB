import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# The pullback pseudofunctor for scheme modules

This file exposes the left-adjoint part of mathlib's existing scheme-module pseudofunctor and
identifies its flexible composition isomorphisms with `pullbackComp` followed by `pullbackCongr`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The contravariant, `Cat`-valued pseudofunctor of sheaves of modules on schemes. This is
the left-adjoint part of `Scheme.Modules.pseudofunctor`. -/
def pullbackPseudofunctor :=
  pseudofunctor.comp Bicategory.Adj.forget₁

/-- The functor mapped by `pullbackPseudofunctor` is the usual pullback of scheme modules. -/
theorem pullbackPseudofunctor_map_toFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackPseudofunctor.map f.op.toLoc).toFunctor = pullback f := by
  rfl

/-- Mapping a module morphism by `pullbackPseudofunctor` is the usual pullback map. -/
theorem pullbackPseudofunctor_map_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (p : M ⟶ N) :
    (pullbackPseudofunctor.map f.op.toLoc).toFunctor.map p =
      (pullback f).map p := by
  rfl

/-- The hom of the flexible composition isomorphism for the pullback pseudofunctor, evaluated
on a module. -/
theorem pullbackPseudofunctor_mapComp'_hom_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) (M : Z.Modules) :
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc k.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.app M) =
      ((((pullbackComp f g).app M) ≪≫ ((pullbackCongr h).app M)).inv) := by
  subst k
  have hcomp : g.op.toLoc ≫ f.op.toLoc = (f ≫ g).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp]
  cases hcomp
  change
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc
      (g.op.toLoc ≫ f.op.toLoc) rfl).hom.toNatTrans.app M) = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  unfold pullbackPseudofunctor
  rw [Pseudofunctor.comp_mapComp,
    Bicategory.Adj.forget₁_mapComp]
  rfl

/-- The inverse of the flexible composition isomorphism for the pullback pseudofunctor,
evaluated on a module. -/
theorem pullbackPseudofunctor_mapComp'_inv_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) (M : Z.Modules) :
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc k.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans.app M) =
      ((((pullbackComp f g).app M) ≪≫ ((pullbackCongr h).app M)).hom) := by
  subst k
  have hcomp : g.op.toLoc ≫ f.op.toLoc = (f ≫ g).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp]
  cases hcomp
  change
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc
      (g.op.toLoc ≫ f.op.toLoc) rfl).inv.toNatTrans.app M) = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  unfold pullbackPseudofunctor
  rw [Pseudofunctor.comp_mapComp,
    Bicategory.Adj.forget₁_mapComp]
  rfl

/-- Pulling a morphism to a further scheme using the descent API is ordinary pullback,
conjugated by the two composition isomorphisms. -/
theorem pullbackPseudofunctor_pullHom
    {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (p : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor) p g gf₁ gf₂ hgf₁ hgf₂ =
      (((pullbackComp g f₁).app M₁) ≪≫
          ((pullbackCongr hgf₁).app M₁)).inv ≫
        (pullback g).map p ≫
      (((pullbackComp g f₂).app M₂) ≪≫
          ((pullbackCongr hgf₂).app M₂)).hom := by
  unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  rw [pullbackPseudofunctor_mapComp'_hom_app g f₁ hgf₁ M₁,
    pullbackPseudofunctor_mapComp'_inv_app g f₂ hgf₂ M₂]
  rfl

/-- The canonical comparison between two iterated pullbacks over a common map. -/
noncomputable def pullbackDescentComparisonIso
    {I : Type u} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules) {Y : Scheme.{u}}
    (q : Y ⟶ S) {i j : I} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
    (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    (pullback f₁).obj ((pullback (f i)).obj M) ≅
      (pullback f₂).obj ((pullback (f j)).obj M) :=
  (((pullbackComp f₁ (f i)).app M) ≪≫ ((pullbackCongr hf₁).app M)) ≪≫
    (((pullbackComp f₂ (f j)).app M) ≪≫ ((pullbackCongr hf₂).app M)).symm

/-- The transition morphism in the pullback descent datum is the canonical comparison between
the two iterated pullbacks. -/
theorem pullbackPseudofunctor_toDescentData_hom
    {I : Type u} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules) {Y : Scheme.{u}}
    (q : Y ⟶ S) {i j : I} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
    (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    ((pullbackPseudofunctor.toDescentData f).obj M).hom
        q f₁ f₂ hf₁ hf₂ =
      (pullbackDescentComparisonIso f M q f₁ f₂ hf₁ hf₂).hom := by
  change
    ((pullbackPseudofunctor.mapComp' (f i).op.toLoc f₁.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app M) ≫
      ((pullbackPseudofunctor.mapComp' (f j).op.toLoc f₂.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app M) = _
  change _ =
    (((pullbackComp f₁ (f i)).app M) ≪≫
        ((pullbackCongr hf₁).app M)).hom ≫
      (((pullbackComp f₂ (f j)).app M) ≪≫
        ((pullbackCongr hf₂).app M)).inv
  rw [pullbackPseudofunctor_mapComp'_inv_app f₁ (f i) hf₁ M,
    pullbackPseudofunctor_mapComp'_hom_app f₂ (f j) hf₂ M]
  rfl

/-- Compatibility with the canonical pullback comparison is the commutativity
condition for a morphism out of the pullback descent datum. -/
theorem pullbackPseudofunctorDescentIso_comm
    {I : Type u} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules)
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i₁ i₂ i₃,
      ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    (D₂ : pullbackPseudofunctor.DescentData' sq sq₃)
    (e : ∀ i, (pullback (f i)).obj M ≅ D₂.obj i)
    (h : ∀ i j,
      (pullback (sq i j).p₁).map (e i).hom ≫ D₂.hom i j =
      (pullbackDescentComparisonIso f M (sq i j).p
          (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂).hom ≫
          (pullback (sq i j).p₂).map (e j).hom)
    (i j : I) :
    (pullback (sq i j).p₁).map (e i).hom ≫ D₂.hom i j =
      (Pseudofunctor.DescentData'.ofDescentData sq sq₃
          ((pullbackPseudofunctor.toDescentData f).obj M)).hom i j ≫
        (pullback (sq i j).p₂).map (e j).hom := by
  rw [Pseudofunctor.DescentData'.ofDescentData_hom]
  have hsource := pullbackPseudofunctor_toDescentData_hom
    (f := f) (M := M) (q := (sq i j).p)
    (f₁ := (sq i j).p₁) (f₂ := (sq i j).p₂)
    (hf₁ := (sq i j).hp₁) (hf₂ := (sq i j).hp₂)
  have hdescent := congrArg
    (fun m ↦ m ≫ (pullback (sq i j).p₂).map (e j).hom) hsource
  exact (h i j).trans hdescent.symm

/-- Compatible local isomorphisms identify the pullback descent datum of a module
with a given descent datum. -/
noncomputable def pullbackPseudofunctorDescentIsoOfCompatible
    {I : Type u} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules)
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i₁ i₂ i₃,
      ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    (D₂ : pullbackPseudofunctor.DescentData' sq sq₃)
    (e : ∀ i, (pullback (f i)).obj M ≅ D₂.obj i)
    (h : ∀ i j,
      (pullback (sq i j).p₁).map (e i).hom ≫ D₂.hom i j =
        (pullbackDescentComparisonIso f M (sq i j).p
          (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂).hom ≫
          (pullback (sq i j).p₂).map (e j).hom) :
    Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData f).obj M) ≅ D₂ := by
  exact Pseudofunctor.DescentData'.isoMk e
    (fun i j ↦ pullbackPseudofunctorDescentIso_comm
      (f := f) (M := M) (sq := sq) (sq₃ := sq₃) (D₂ := D₂)
      (e := e) h i j)

/-- The transition law of an isomorphism from a pullback descent datum is expressed
using the canonical comparison between the two iterated pullbacks. -/
theorem pullbackPseudofunctorDescentIso_transition
    {I : Type u} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules)
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i₁ i₂ i₃,
      ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    (D₂ : pullbackPseudofunctor.DescentData' sq sq₃)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData f).obj M) ≅ D₂)
    (i j : I) :
    (pullback (sq i j).p₁).map (e.hom.hom i) ≫ D₂.hom i j =
      (pullbackDescentComparisonIso f M (sq i j).p
        (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂).hom ≫
        (pullback (sq i j).p₂).map (e.hom.hom j) := by
  have hsource := pullbackPseudofunctor_toDescentData_hom
    (f := f) (M := M) (q := (sq i j).p)
    (f₁ := (sq i j).p₁) (f₂ := (sq i j).p₂)
    (hf₁ := (sq i j).hp₁) (hf₂ := (sq i j).hp₂)
  have hdescent := congrArg
    (fun m ↦ m ≫ (pullback (sq i j).p₂).map (e.hom.hom j)) hsource
  exact (e.hom.comm i j).trans hdescent

end


end AlgebraicGeometry.Scheme.Modules
