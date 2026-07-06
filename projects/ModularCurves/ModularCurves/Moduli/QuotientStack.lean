/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Ticket T-W3 (quotient-stack core; reviewer v8).
-/
import ModularCurves.ForMathlib.SchemeQuotient
import Mathlib.CategoryTheory.Category.Cat

/-!
# The quotient prestack `[X/G]` of a scheme by a finite group action (T-W3)

For a (constant) group `G` acting on a scheme `X` via
`σ : AlgebraicGeometry.SchemeAction G X` (the T-W3 `GroupAction` vocabulary of
record — alias decision on the board), this file provides the minimal
quotient-stack API of reviewer v8:

* `ActionGroupoid σ S` — the value groupoid of `[X/G]` on `S`: objects are
  `S`-points `t : S ⟶ X`, morphisms `t ⟶ t'` are group elements `g` with
  `t ≫ σ.hom g = t'`.
* `QuotientStack σ : Schemeᵒᵖ ⥤ Cat` — the (strict) presheaf of groupoids
  `S ↦ [X/G](S)`, restriction by precomposition.

No algebraic-stack properties are claimed (the fppf-stack condition is T-E8
territory); the torsor description of `[X/G](S)` is stated separately.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ModularCurves

variable {G : Type u} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)

/-- The value of the quotient prestack `[X/G]` on `S`: the action groupoid of
`G` on the `S`-points of `X`. Objects are morphisms `S ⟶ X`. -/
def ActionGroupoid (_σ : SchemeAction G X) (S : Scheme.{u}) : Type u := S ⟶ X

namespace ActionGroupoid

variable {σ} {S : Scheme.{u}}

/-- Interpret an `S`-point of `X` as an object of the action groupoid. -/
def mk (t : S ⟶ X) : ActionGroupoid σ S := t

/-- The underlying `S`-point of an object of the action groupoid. -/
def pt (t : ActionGroupoid σ S) : S ⟶ X := t

@[simp] theorem pt_mk (t : S ⟶ X) : (mk (σ := σ) t).pt = t := rfl

instance : Groupoid (ActionGroupoid σ S) where
  Hom t t' := { g : G // t.pt ≫ σ.hom g = t'.pt }
  id t := ⟨1, by rw [σ.hom_one, Category.comp_id]⟩
  comp {a b c} f g := ⟨f.1 * g.1, by
    rw [σ.hom_mul, ← Category.assoc, f.2, g.2]⟩
  id_comp f := Subtype.ext (one_mul _)
  comp_id f := Subtype.ext (mul_one _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _)
  inv {a b} f := ⟨f.1⁻¹, by
    have h := congrArg (fun t => t ≫ σ.hom f.1⁻¹) f.2
    rw [Category.assoc, ← σ.hom_mul, mul_inv_cancel, σ.hom_one,
      Category.comp_id] at h
    exact h.symm⟩
  inv_comp f := Subtype.ext (inv_mul_cancel _)
  comp_inv f := Subtype.ext (mul_inv_cancel _)

@[simp]
theorem comp_val {a b c : ActionGroupoid σ S} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = f.1 * g.1 := rfl

@[simp]
theorem id_val (a : ActionGroupoid σ S) : (𝟙 a : a ⟶ a).1 = 1 := rfl

theorem eqToHom_val {a b : ActionGroupoid σ S} (h : a = b) :
    (eqToHom h).1 = 1 := by
  subst h; rfl

/-- Restriction of the action groupoid along `u : S' ⟶ S` (precomposition). -/
def restrict (σ : SchemeAction G X) {S S' : Scheme.{u}} (u : S' ⟶ S) :
    ActionGroupoid σ S ⥤ ActionGroupoid σ S' where
  obj t := mk (u ≫ t.pt)
  map {t t'} f := ⟨f.1, by
    show (u ≫ t.pt) ≫ σ.hom f.1 = u ≫ t'.pt
    rw [Category.assoc, f.2]⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

@[simp]
theorem restrict_obj_pt {S S' : Scheme.{u}} (u : S' ⟶ S)
    (t : ActionGroupoid σ S) : ((restrict σ u).obj t).pt = u ≫ t.pt := rfl

@[simp]
theorem restrict_map_val {S S' : Scheme.{u}} (u : S' ⟶ S)
    {t t' : ActionGroupoid σ S} (f : t ⟶ t') :
    ((restrict σ u).map f).1 = f.1 := rfl

end ActionGroupoid

namespace ActionGroupoid

variable {σ}

/-- Functors between action groupoids are determined by their object maps and
the group-element labels of their morphism maps. -/
private theorem functor_ext {S S' : Scheme.{u}}
    {F F' : ActionGroupoid σ S ⥤ ActionGroupoid σ S'}
    (hobj : ∀ t, F.obj t = F'.obj t)
    (hval : ∀ {t t' : ActionGroupoid σ S} (f : t ⟶ t'),
      (F.map f).1 = (F'.map f).1) : F = F' := by
  refine @CategoryTheory.Functor.ext _ _ _ _ F F' hobj fun t t' f => ?_
  refine Subtype.ext ?_
  show (F.map f).1 = (eqToHom (hobj t) ≫ F'.map f ≫ eqToHom (hobj t').symm).1
  rw [comp_val, comp_val, eqToHom_val, eqToHom_val, one_mul, mul_one]
  exact hval f

end ActionGroupoid

open ActionGroupoid in
/-- **The quotient prestack `[X/G]`** (T-W3): the strict presheaf of groupoids
sending `S` to the action groupoid of `G` on `X(S)`, with restriction by
precomposition. (Stack properties are out of scope here.) -/
def QuotientStack (σ : SchemeAction G X) : Schemeᵒᵖ ⥤ Cat.{u, u} where
  obj S := Cat.of (ActionGroupoid σ S.unop)
  map u := (restrict σ u.unop).toCatHom
  map_id S := congrArg Functor.toCatHom (by
    refine functor_ext (fun t => ?_) (fun f => rfl)
    show mk ((𝟙 S.unop) ≫ t.pt) = t
    rw [Category.id_comp]
    rfl)
  map_comp {S S' S''} u v := congrArg Functor.toCatHom (by
    refine functor_ext (fun t => ?_) (fun f => rfl)
    show mk ((v.unop ≫ u.unop) ≫ t.pt) = mk (v.unop ≫ u.unop ≫ t.pt)
    rw [Category.assoc])

@[simp]
theorem quotientStack_obj (σ : SchemeAction G X) (S : Schemeᵒᵖ) :
    (QuotientStack σ).obj S = Cat.of (ActionGroupoid σ S.unop) := rfl

section Coarse

open ActionGroupoid

variable [Finite G]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
variable (V : ↥X → X.Opens) (hVs : ∀ x : ↥X, σ.IsStableOpen (V x))
  (hVa : ∀ x : ↥X, IsAffineOpen (V x)) (hVmem : ∀ x : ↥X, x ∈ V x)

/-- **The coarse comparison** `[X/G](S) ⟶ (X/G)(S)`: composing an `S`-point with
the T-Q5 quotient projection collapses the groupoid (every morphism goes to an
identity, by the invariance `hom_quotientπ`). This is the prestack-level
`[X/G] → X/G` map feeding the T-Q7 coarse statements. -/
noncomputable def ActionGroupoid.toQuotient (S : Scheme.{u}) :
    ActionGroupoid σ S ⥤ Discrete (S ⟶ σ.quotient V hVs hVa) where
  obj t := ⟨t.pt ≫ σ.quotientπ V hVs hVa hVmem⟩
  map {t t'} f := Discrete.eqToHom (by
    show t.pt ≫ σ.quotientπ V hVs hVa hVmem =
      t'.pt ≫ σ.quotientπ V hVs hVa hVmem
    rw [← f.2, Category.assoc, σ.hom_quotientπ V hVs hVa hVmem f.1])
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end Coarse

end ModularCurves
