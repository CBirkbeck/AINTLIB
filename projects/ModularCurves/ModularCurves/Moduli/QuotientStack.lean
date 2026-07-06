/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Ticket T-W3 (quotient-stack core; reviewer v8).
-/
import ModularCurves.ForMathlib.SchemeQuotient
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

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

section TorsorPair

open AlgebraicGeometry

variable [Finite G]

/-- **A `G`-torsor pair over `S`** (T-W3b vocabulary): a finite étale `G`-torsor
`p : P ⟶ S` (in the `∐`-comparison sense of record — `TorsorData`/Stack.lean
shape) together with a `G`-equivariant map to `X`. These are the objects of the
honest (stacky) value groupoid of `[X/G]` at `S`; the prestack `ActionGroupoid`
embeds as the trivial-torsor pairs (T-W3b). -/
structure TorsorPair (σ : SchemeAction G X) (S : Scheme.{u}) where
  /-- The total space of the torsor. -/
  P : Scheme.{u}
  /-- The torsor projection. -/
  p : P ⟶ S
  /-- The `G`-action on the total space. -/
  τ : SchemeAction G P
  /-- The action lies over `S`. -/
  over_base : ∀ g : G, τ.hom g ≫ p = p
  /-- The projection is finite. -/
  finite : IsFinite p
  /-- The projection is étale. -/
  etale : AlgebraicGeometry.Etale p
  /-- The projection is surjective. -/
  surjective : Surjective p
  /-- The torsor condition: `(g, x) ↦ (g·x, x)` identifies `∐_G P` with
  `P ×_S P`. -/
  torsor : IsIso ((Limits.Sigma.desc fun g : G =>
    Limits.pullback.lift (τ.hom g) (𝟙 P)
      (by rw [Category.id_comp]; exact over_base g)) :
    (∐ fun _ : G => P) ⟶ Limits.pullback p p)
  /-- The equivariant map to `X`. -/
  u : P ⟶ X
  /-- Equivariance of `u`. -/
  equivariant : ∀ g : G, τ.hom g ≫ u = u ≫ σ.hom g

namespace TorsorPair

variable {σ} {S : Scheme.{u}}

/-- Morphisms of `G`-torsor pairs: equivariant maps over `S` compatible with the
maps to `X`. (Any such map is automatically an isomorphism — torsor pairs form a
groupoid — but that is a theorem, not part of the data.) -/
@[ext]
structure Hom (A B : TorsorPair σ S) where
  /-- The underlying map of total spaces. -/
  hom : A.P ⟶ B.P
  over : hom ≫ B.p = A.p
  equiv : ∀ g : G, A.τ.hom g ≫ hom = hom ≫ B.τ.hom g
  compat : hom ≫ B.u = A.u

instance : Category (TorsorPair σ S) where
  Hom A B := Hom A B
  id A :=
    { hom := 𝟙 A.P
      over := Category.id_comp _
      equiv := fun g => by rw [Category.comp_id, Category.id_comp]
      compat := Category.id_comp _ }
  comp {A B C} f g :=
    { hom := f.hom ≫ g.hom
      over := by rw [Category.assoc, g.over, f.over]
      equiv := fun γ => by
        rw [← Category.assoc, f.equiv γ, Category.assoc, g.equiv γ,
          Category.assoc]
      compat := by rw [Category.assoc, g.compat, f.compat] }
  id_comp f := by ext1; exact Category.id_comp _
  comp_id f := by ext1; exact Category.comp_id _
  assoc f g h := by ext1; exact Category.assoc _ _ _

omit [Finite G] in
@[simp]
theorem comp_hom {A B C : TorsorPair σ S} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

omit [Finite G] in
@[simp]
theorem id_hom (A : TorsorPair σ S) : (𝟙 A : A ⟶ A).hom = 𝟙 A.P := rfl

end TorsorPair

/-! ### The trivial torsor (T-W3b, trivialization data)

The underlying data of the trivial `G`-torsor `∐_G S → S`: the translation
action and the equivariant map attached to an `S`-point of `X`. The
morphism-property fields (`finite`/`etale`/`surjective`/`torsor`) of the
corresponding `TorsorPair` are the T-W3b remainder. -/

variable (G) in
/-- The translation action of `G` on `∐_G S`: `g` maps the `h`-summand
identically onto the `h * g`-summand. -/
noncomputable def trivialTorsorAction (S : Scheme.{u}) :
    SchemeAction G (∐ fun _ : G => S) where
  hom g := Limits.Sigma.desc fun h => Limits.Sigma.ι (fun _ : G => S) (h * g)
  hom_one := by
    refine Limits.Sigma.hom_ext _ _ fun h => ?_
    rw [Limits.Sigma.ι_desc, mul_one, Category.comp_id]
  hom_mul g g' := by
    refine Limits.Sigma.hom_ext _ _ fun h => ?_
    rw [Limits.Sigma.ι_desc, ← Category.assoc, Limits.Sigma.ι_desc,
      Limits.Sigma.ι_desc, mul_assoc]

omit [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorAction_hom (S : Scheme.{u}) (g h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ (trivialTorsorAction G S).hom g =
      Limits.Sigma.ι (fun _ : G => S) (h * g) :=
  Limits.Sigma.ι_desc _ _

/-- The projection of the trivial torsor. -/
noncomputable def trivialTorsorπ (S : Scheme.{u}) :
    (∐ fun _ : G => S) ⟶ S :=
  Limits.Sigma.desc fun _ => 𝟙 S

omit [Group G] [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorπ (S : Scheme.{u}) (h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ trivialTorsorπ S = 𝟙 S :=
  Limits.Sigma.ι_desc _ _

omit [Finite G] in
theorem trivialTorsorAction_over_base (S : Scheme.{u}) (g : G) :
    (trivialTorsorAction G S).hom g ≫ trivialTorsorπ S = trivialTorsorπ S := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [← Category.assoc, ι_trivialTorsorAction_hom, ι_trivialTorsorπ,
    ι_trivialTorsorπ]

/-- The equivariant map of the trivial torsor pair attached to an `S`-point
`t : S ⟶ X`: on the `g`-summand it is `t` translated by `g`. -/
noncomputable def trivialTorsorMap (S : Scheme.{u}) (t : S ⟶ X) :
    (∐ fun _ : G => S) ⟶ X :=
  Limits.Sigma.desc fun g => t ≫ σ.hom g

omit [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorMap (S : Scheme.{u}) (t : S ⟶ X) (h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ trivialTorsorMap σ S t =
      t ≫ σ.hom h :=
  Limits.Sigma.ι_desc _ _

omit [Finite G] in
theorem trivialTorsorMap_equivariant (S : Scheme.{u}) (t : S ⟶ X) (g : G) :
    (trivialTorsorAction G S).hom g ≫ trivialTorsorMap σ S t =
      trivialTorsorMap σ S t ≫ σ.hom g := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [← Category.assoc, ι_trivialTorsorAction_hom, ι_trivialTorsorMap,
    ← Category.assoc, ι_trivialTorsorMap, Category.assoc, ← σ.hom_mul]

variable (G) in
/-- Left translation on the trivial torsor: the `h`-summand maps identically to
the `g * h`-summand. Left translations are the torsor-pair endomorphisms of the
trivial torsor (they commute with the right-translation action). -/
noncomputable def trivialTorsorLeft (S : Scheme.{u}) (g : G) :
    (∐ fun _ : G => S) ⟶ (∐ fun _ : G => S) :=
  Limits.Sigma.desc fun h => Limits.Sigma.ι (fun _ : G => S) (g * h)

omit [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorLeft (S : Scheme.{u}) (g h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ trivialTorsorLeft G S g =
      Limits.Sigma.ι (fun _ : G => S) (g * h) :=
  Limits.Sigma.ι_desc _ _

omit [Finite G] in
/-- Left translations commute with the (right-translation) torsor action. -/
theorem trivialTorsorLeft_equivariant (S : Scheme.{u}) (g γ : G) :
    (trivialTorsorAction G S).hom γ ≫ trivialTorsorLeft G S g =
      trivialTorsorLeft G S g ≫ (trivialTorsorAction G S).hom γ := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [← Category.assoc, ι_trivialTorsorAction_hom, ι_trivialTorsorLeft,
    ← Category.assoc, ι_trivialTorsorLeft, ι_trivialTorsorAction_hom,
    mul_assoc]

omit [Finite G] in
/-- Left translations lie over the base. -/
theorem trivialTorsorLeft_over_base (S : Scheme.{u}) (g : G) :
    trivialTorsorLeft G S g ≫ trivialTorsorπ S = trivialTorsorπ S := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [← Category.assoc, ι_trivialTorsorLeft, ι_trivialTorsorπ, ι_trivialTorsorπ]

omit [Finite G] in
/-- The compatibility of left translation with the equivariant maps: if
`t ≫ σ.hom g = t'`, left translation by `g⁻¹` carries the trivial pair of `t'`
to that of `t`. -/
theorem trivialTorsorLeft_map (S : Scheme.{u}) {t t' : S ⟶ X} {g : G}
    (hg : t ≫ σ.hom g = t') :
    trivialTorsorLeft G S g⁻¹ ≫ trivialTorsorMap σ S t' =
      trivialTorsorMap σ S t := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [← Category.assoc, ι_trivialTorsorLeft, ι_trivialTorsorMap,
    ι_trivialTorsorMap, ← hg, Category.assoc, ← σ.hom_mul,
    mul_inv_cancel_left]

omit [Finite G] in
@[simp]
theorem trivialTorsorLeft_one (S : Scheme.{u}) :
    trivialTorsorLeft G S (1 : G) = 𝟙 _ := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [ι_trivialTorsorLeft, one_mul, Category.comp_id]

omit [Finite G] in
theorem trivialTorsorLeft_mul (S : Scheme.{u}) (g g' : G) :
    trivialTorsorLeft G S (g * g') =
      trivialTorsorLeft G S g' ≫ trivialTorsorLeft G S g := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [ι_trivialTorsorLeft, ← Category.assoc, ι_trivialTorsorLeft,
    ι_trivialTorsorLeft, mul_assoc]

end TorsorPair

end ModularCurves
