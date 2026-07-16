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

omit [Group G] [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- The trivial-torsor projection is étale (a coproduct of identities;
`Etale` is Zariski-local at the source). -/
theorem trivialTorsorπ_etale (S : Scheme.{u}) :
    AlgebraicGeometry.Etale (trivialTorsorπ (G := G) S) :=
  IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

omit [Finite G] in
/-- The trivial-torsor projection is surjective (any single summand already
covers). -/
theorem trivialTorsorπ_surjective (S : Scheme.{u}) :
    Surjective (trivialTorsorπ (G := G) S) := by
  refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
  refine Set.eq_univ_of_univ_subset ?_
  intro x _
  exact Set.mem_iUnion.mpr ⟨1, x, rfl⟩

/-- **The fold of a finite coproduct of copies of an affine scheme is finite**
(T-W3b-i, model case): conjugating by `sigmaSpec`, the fold is `Spec` of the
diagonal `R →+* Π_ι R`, which is module-finite for finite `ι`. -/
theorem isFinite_sigmaDesc_id_spec {ι : Type u} [Finite ι]
    (R : CommRingCat.{u}) :
    AlgebraicGeometry.IsFinite
      (Limits.Sigma.desc fun _ : ι => 𝟙 (Spec R)) := by
  have hdesc : Limits.Sigma.desc (fun _ : ι => 𝟙 (Spec R)) =
      sigmaSpec (fun _ : ι => R) ≫
        Spec.map (CommRingCat.ofHom (RingHom.pi fun _ => RingHom.id R)) := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [Limits.Sigma.ι_desc, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
    rw [show CommRingCat.ofHom (RingHom.pi fun _ : ι => RingHom.id ↑R) ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : ι => ↑R) i) = 𝟙 R from rfl]
    exact (Spec.map_id R).symm
  rw [hdesc]
  haveI : AlgebraicGeometry.IsFinite
      (Spec.map (CommRingCat.ofHom (RingHom.pi fun _ : ι => RingHom.id ↑R))) := by
    rw [AlgebraicGeometry.IsFinite.SpecMap_iff]
    show (RingHom.pi fun _ : ι => RingHom.id ↑R).Finite
    show Module.Finite ↑R (ι → ↑R)
    exact Module.Finite.pi
  infer_instance

/-- **The fold of a finite coproduct of copies of any scheme is a finite
morphism** (T-W3b-i): it is the base change of the affine model
(`isFinite_sigmaDesc_id_spec` over `Spec ℤ`) along `S ⟶ Spec ℤ`, via the
extensivity of `Scheme` (pullbacks distribute over finite coproducts). -/
theorem isFinite_sigmaDesc_id {ι : Type u} [Finite ι] (S : Scheme.{u}) :
    AlgebraicGeometry.IsFinite (Limits.Sigma.desc fun _ : ι => 𝟙 S) := by
  have hsq := (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (Limits.coproductIsCoproduct
        (fun _ : ι => Spec (CommRingCat.of (ULift.{u} ℤ))))
      ).isPullback_of_isColimit_left
    (f := fun _ : ι => 𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (u := Limits.Sigma.desc fun _ : ι => 𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (v := specULiftZIsTerminal.from S)
    (q₁ := fun _ : ι => 𝟙 S) (q₂ := fun _ : ι => specULiftZIsTerminal.from S)
    (fun _ => IsPullback.of_horiz_isIso
      ⟨by rw [Category.id_comp, Category.comp_id]⟩)
    (Limits.coproductIsCoproduct (fun _ : ι => S))
    (fun i => Limits.Sigma.ι_desc _ _)
  have hdesc : Limits.Cofan.IsColimit.desc
      (Limits.coproductIsCoproduct (fun _ : ι => S)) (fun _ => 𝟙 S) =
      Limits.Sigma.desc (fun _ : ι => 𝟙 S) := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [Limits.Sigma.ι_desc]
    exact Limits.Cofan.IsColimit.fac _ _ i
  rw [← hdesc]
  exact MorphismProperty.of_isPullback hsq.flip
    (isFinite_sigmaDesc_id_spec (CommRingCat.of (ULift.{u} ℤ)))

omit [Group G] [Finite G] in
/-- The trivial-torsor projection is a finite morphism. -/
theorem trivialTorsorπ_finite [Finite G] (S : Scheme.{u}) :
    AlgebraicGeometry.IsFinite (trivialTorsorπ (G := G) S) :=
  isFinite_sigmaDesc_id S

section TorsorComparison

variable (S : Scheme.{u})

omit [Group G] in
/-- Stage A of the trivial-torsor comparison: distributing the pullback of the
trivial projection over the second coproduct factor. The square exhibits
`∐_k (∐_G S)` as `(∐_G S) ×_S (∐_G S)` via `(k, x) ↦ (x, π(x)-in-k-copy)`. -/
private theorem trivialTorsor_distrib :
    IsPullback
      (Limits.Cofan.IsColimit.desc
        (Limits.coproductIsCoproduct (fun _ : G => ∐ fun _ : G => S))
        (fun _ => 𝟙 (∐ fun _ : G => S)))
      (Limits.Cofan.IsColimit.desc
        (Limits.coproductIsCoproduct (fun _ : G => ∐ fun _ : G => S))
        (fun k => trivialTorsorπ S ≫
          (Limits.Cofan.mk (∐ fun _ : G => S)
            (Limits.Sigma.ι (fun _ : G => S))).inj k))
      (trivialTorsorπ S) (trivialTorsorπ S) :=
  (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (Limits.coproductIsCoproduct (fun _ : G => S))
      ).isPullback_of_isColimit_left
    (f := fun _ : G => 𝟙 S)
    (u := trivialTorsorπ S)
    (v := trivialTorsorπ S)
    (q₁ := fun _ : G => 𝟙 (∐ fun _ : G => S))
    (q₂ := fun _ : G => trivialTorsorπ S)
    (fun _ => IsPullback.of_horiz_isIso
      ⟨by rw [Category.id_comp, Category.comp_id]⟩)
    (Limits.coproductIsCoproduct (fun _ : G => ∐ fun _ : G => S))
    (fun i => Limits.Sigma.ι_desc _ _)

/-- The reindexing `(γ, h) ↦ (h, h·γ)` of the double coproduct. -/
private noncomputable def trivialTorsorReindex :
    (∐ fun _ : G => (∐ fun _ : G => S)) ⟶ (∐ fun _ : G => (∐ fun _ : G => S)) :=
  Limits.Sigma.desc fun γ => Limits.Sigma.desc fun h =>
    Limits.Sigma.ι (fun _ : G => S) (h * γ) ≫
      Limits.Sigma.ι (fun _ : G => ∐ fun _ : G => S) h

/-- The inverse reindexing `(k, m) ↦ (k⁻¹·m, k)`. -/
private noncomputable def trivialTorsorReindexInv :
    (∐ fun _ : G => (∐ fun _ : G => S)) ⟶ (∐ fun _ : G => (∐ fun _ : G => S)) :=
  Limits.Sigma.desc fun k => Limits.Sigma.desc fun m =>
    Limits.Sigma.ι (fun _ : G => S) k ≫
      Limits.Sigma.ι (fun _ : G => ∐ fun _ : G => S) (k⁻¹ * m)

private instance : IsIso (trivialTorsorReindex (G := G) S) := by
  rw [trivialTorsorReindex]
  refine ⟨trivialTorsorReindexInv S, ?_, ?_⟩
  · rw [trivialTorsorReindexInv]
    refine Limits.Sigma.hom_ext _ _ fun γ => ?_
    rw [Category.comp_id, ← Category.assoc, Limits.Sigma.ι_desc]
    refine Limits.Sigma.hom_ext _ _ fun h => ?_
    rw [← Category.assoc, Limits.Sigma.ι_desc, Category.assoc,
      Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, inv_mul_cancel_left]
  · rw [trivialTorsorReindexInv]
    refine Limits.Sigma.hom_ext _ _ fun k => ?_
    rw [Category.comp_id, ← Category.assoc, Limits.Sigma.ι_desc]
    refine Limits.Sigma.hom_ext _ _ fun m => ?_
    rw [← Category.assoc, Limits.Sigma.ι_desc, Category.assoc,
      Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, mul_inv_cancel_left]

/-- The trivial-torsor comparison map factors as the reindexing followed by the
distributivity identification. -/
private theorem trivialTorsor_comparison_eq :
    (Limits.Sigma.desc fun γ : G =>
      Limits.pullback.lift ((trivialTorsorAction G S).hom γ)
        (𝟙 (∐ fun _ : G => S))
        (by rw [Category.id_comp]; exact trivialTorsorAction_over_base S γ)) =
    trivialTorsorReindex S ≫ (trivialTorsor_distrib S).isoPullback.hom := by
  have hfac1 : ∀ k : G, Limits.Sigma.ι (fun _ : G => ∐ fun _ : G => S) k ≫
      Limits.Cofan.IsColimit.desc
        (Limits.coproductIsCoproduct (fun _ : G => ∐ fun _ : G => S))
        (fun _ => 𝟙 (∐ fun _ : G => S)) = 𝟙 (∐ fun _ : G => S) :=
    fun k => Limits.Cofan.IsColimit.fac _ _ k
  have hfac2 : ∀ k : G, Limits.Sigma.ι (fun _ : G => ∐ fun _ : G => S) k ≫
      Limits.Cofan.IsColimit.desc
        (Limits.coproductIsCoproduct (fun _ : G => ∐ fun _ : G => S))
        (fun k => trivialTorsorπ S ≫
          (Limits.Cofan.mk (∐ fun _ : G => S)
            (Limits.Sigma.ι (fun _ : G => S))).inj k) =
      trivialTorsorπ S ≫ Limits.Sigma.ι (fun _ : G => S) k :=
    fun k => Limits.Cofan.IsColimit.fac _ _ k
  rw [trivialTorsorReindex]
  refine Limits.Sigma.hom_ext _ _ fun γ => ?_
  rw [Limits.Sigma.ι_desc]
  erw [Limits.Sigma.ι_desc_assoc]
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  erw [Limits.Sigma.ι_desc_assoc]
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Limits.pullback.lift_fst, ι_trivialTorsorAction_hom,
      Category.assoc, Category.assoc]
    erw [(trivialTorsor_distrib S).isoPullback_hom_fst]
    rw [hfac1, Category.comp_id]
  · rw [Category.assoc, Limits.pullback.lift_snd, Category.comp_id,
      Category.assoc, Category.assoc]
    erw [(trivialTorsor_distrib S).isoPullback_hom_snd]
    erw [hfac2]
    rw [ι_trivialTorsorπ_assoc]

/-- **The trivial torsor satisfies the torsor condition** (the last property
field of the trivial `TorsorPair`): `(γ, x) ↦ (γ·x, x)` identifies
`∐_G (∐_G S)` with `(∐_G S) ×_S (∐_G S)`. -/
theorem trivialTorsor_torsor :
    IsIso ((Limits.Sigma.desc fun γ : G =>
      Limits.pullback.lift ((trivialTorsorAction G S).hom γ)
        (𝟙 (∐ fun _ : G => S))
        (by rw [Category.id_comp]; exact trivialTorsorAction_over_base S γ)) :
      (∐ fun _ : G => (∐ fun _ : G => S)) ⟶
        Limits.pullback (trivialTorsorπ S) (trivialTorsorπ S)) := by
  rw [trivialTorsor_comparison_eq]
  exact IsIso.comp_isIso' inferInstance inferInstance

end TorsorComparison

omit [Finite G] in
theorem trivialTorsorLeft_mul (S : Scheme.{u}) (g g' : G) :
    trivialTorsorLeft G S (g * g') =
      trivialTorsorLeft G S g' ≫ trivialTorsorLeft G S g := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  rw [ι_trivialTorsorLeft, ← Category.assoc, ι_trivialTorsorLeft,
    ι_trivialTorsorLeft, mul_assoc]

section Trivialize

/-- **The trivial torsor pair** attached to an `S`-point `t : S ⟶ X`: the
split torsor `∐_G S → S` with the translation action and the equivariant map
`(g, s) ↦ σ(g)(t(s))`. -/
noncomputable def trivialTorsorPair (S : Scheme.{u}) (t : S ⟶ X) :
    TorsorPair σ S where
  P := ∐ fun _ : G => S
  p := trivialTorsorπ S
  τ := trivialTorsorAction G S
  over_base := trivialTorsorAction_over_base S
  finite := trivialTorsorπ_finite S
  etale := trivialTorsorπ_etale S
  surjective := trivialTorsorπ_surjective S
  torsor := trivialTorsor_torsor S
  u := trivialTorsorMap σ S t
  equivariant := trivialTorsorMap_equivariant σ S t

/-- **The trivialization functor** (T-W3b): the prestack `[X/G](S)` maps to the
groupoid of `G`-torsor pairs by sending an `S`-point to its trivial torsor pair
and a group element `f : t ⟶ t'` to left translation by `f⁻¹`. Fully faithful
for connected nonempty `S` (see the attack log — NOT in general); the essential
image is the locally trivial pairs (descent-gated). -/
noncomputable def trivialize (S : Scheme.{u}) :
    ActionGroupoid σ S ⥤ TorsorPair σ S where
  obj t := trivialTorsorPair σ S t.pt
  map {t t'} f :=
    { hom := trivialTorsorLeft G S f.1⁻¹
      over := trivialTorsorLeft_over_base S f.1⁻¹
      equiv := fun g => trivialTorsorLeft_equivariant S f.1⁻¹ g
      compat := trivialTorsorLeft_map σ S f.2 }
  map_id t := by
    refine TorsorPair.Hom.ext ?_
    show trivialTorsorLeft G S (1 : G)⁻¹ = 𝟙 _
    rw [inv_one, trivialTorsorLeft_one]
  map_comp {t t' t''} f g := by
    refine TorsorPair.Hom.ext ?_
    show trivialTorsorLeft G S (f.1 * g.1)⁻¹ =
      trivialTorsorLeft G S f.1⁻¹ ≫ trivialTorsorLeft G S g.1⁻¹
    rw [mul_inv_rev, trivialTorsorLeft_mul]

/-- The range of a coproduct component is clopen: open as an open immersion,
closed because the complement is the (open) union of the other components.
(T-W3b fullness ingredient: the clopen pieces a pair-endomorphism cuts out of a
connected base.) -/
theorem isClopen_range_sigmaι {σ' : Type u} (g : σ' → Scheme.{u}) (i : σ') :
    IsClopen (Set.range (Limits.Sigma.ι g i).base) := by
  -- the range is the image, under the homeomorphism `sigmaMk`, of the `i`-th summand of the
  -- underlying sigma type — which is clopen there (`isClopen_range_sigmaMk`)
  have hrange : Set.range (Limits.Sigma.ι g i).base = sigmaMk g '' Set.range (Sigma.mk i) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun x => (sigmaMk_mk g i x).symm)
  rw [hrange]
  exact ⟨(sigmaMk g).isClosed_image.mpr isClopen_range_sigmaMk.1,
    (sigmaMk g).isOpen_image.mpr isClopen_range_sigmaMk.2⟩

/-- **The trivialization functor is faithful over a nonempty base** (the
`S = ∅` counterexample in the attack log is the only obstruction; fullness
additionally needs `S` connected). -/
theorem trivialize_faithful (S : Scheme.{u}) [Nonempty S] :
    (trivialize σ S).Faithful where
  map_injective {t t'} {f g} hfg := by
    obtain ⟨x⟩ := ‹Nonempty S›
    have hhom : trivialTorsorLeft G S f.1⁻¹ = trivialTorsorLeft G S g.1⁻¹ :=
      congrArg TorsorPair.Hom.hom hfg
    have hpt : (trivialTorsorLeft G S f.1⁻¹).base
        ((Limits.Sigma.ι (fun _ : G => S) (1 : G)).base x) =
        (trivialTorsorLeft G S g.1⁻¹).base
        ((Limits.Sigma.ι (fun _ : G => S) (1 : G)).base x) := by
      rw [hhom]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      ι_trivialTorsorLeft, ι_trivialTorsorLeft, mul_one, mul_one] at hpt
    have hmk := (sigmaι_eq_iff _ _ _ _ _).mp hpt
    exact Subtype.ext (inv_injective (congrArg Sigma.fst hmk))

omit [Finite G] in
/-- On a connected base, a scheme endomorphism `f` of the trivial torsor `∐_G S`
that lies over `S` sends the identity summand identically onto a *single*
summand: there is `γ₀ : G` with `ι 1 ≫ f = ι γ₀`. The image of the identity
summand meets the (clopen) `γ₀`-summand, and connectedness forces that clopen
preimage to be everything. (T-W3b fullness, geometric core.) -/
private theorem exists_sigmaι_one_comp_eq {S : Scheme.{u}} [ConnectedSpace S]
    {f : (∐ fun _ : G => S) ⟶ (∐ fun _ : G => S)}
    (hover : f ≫ trivialTorsorπ S = trivialTorsorπ S) :
    ∃ γ₀ : G, Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f =
      Limits.Sigma.ι (fun _ : G => S) γ₀ := by
  haveI him : ∀ j : G, IsOpenImmersion (Limits.Sigma.ι (fun _ : G => S) j) :=
    fun j => inferInstanceAs
      (IsOpenImmersion (Limits.colimit.ι (Discrete.functor fun _ : G => S) ⟨j⟩))
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  obtain ⟨γ₀, y₀, hy₀'⟩ : ∃ (γ₀ : G) (y₀ : S),
      (Limits.Sigma.ι (fun _ : G => S) γ₀).base y₀ =
      (Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f).base x₀ := by
    obtain ⟨y₀, hy₀⟩ := (sigmaOpenCover (fun _ : G => S)).covers
      ((Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f).base x₀)
    exact ⟨_, y₀, hy₀⟩
  refine ⟨γ₀, ?_⟩
  have hrange : Set.range ⇑(Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f) ⊆
      Set.range ⇑(Limits.Sigma.ι (fun _ : G => S) γ₀) := by
    rcases isClopen_iff.mp
      ((isClopen_range_sigmaι (fun _ : G => S) γ₀).preimage
        (Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f).continuous) with h | h
    · exfalso
      exact Set.eq_empty_iff_forall_notMem.mp h x₀ ⟨y₀, hy₀'⟩
    · rintro _ ⟨x, rfl⟩
      exact Set.eq_univ_iff_forall.mp h x
  have hfac := IsOpenImmersion.lift_fac
    (Limits.Sigma.ι (fun _ : G => S) γ₀)
    (Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f) hrange
  have h1 := congrArg (fun k => k ≫ trivialTorsorπ S) hfac
  rw [Category.assoc, ι_trivialTorsorπ, Category.comp_id, Category.assoc]
    at h1
  erw [hover] at h1
  rw [ι_trivialTorsorπ] at h1
  erw [← hfac]
  rw [h1, Category.id_comp]

omit [Finite G] in
/-- Equivariance upgrades the single-summand identification to the whole map: a
scheme endomorphism `f` of `∐_G S` that commutes with the translation action and
sends the identity summand to the `γ₀`-summand is left translation by `γ₀`. -/
private theorem eq_trivialTorsorLeft_of_ι_one {S : Scheme.{u}}
    {f : (∐ fun _ : G => S) ⟶ (∐ fun _ : G => S)} {γ₀ : G}
    (hequiv : ∀ h : G, (trivialTorsorAction G S).hom h ≫ f =
      f ≫ (trivialTorsorAction G S).hom h)
    (hι1 : Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f =
      Limits.Sigma.ι (fun _ : G => S) γ₀) :
    f = trivialTorsorLeft G S γ₀ := by
  refine Limits.Sigma.hom_ext _ _ fun h => ?_
  have h2 : Limits.Sigma.ι (fun _ : G => S) h =
      Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫
        (trivialTorsorAction G S).hom h := by
    rw [ι_trivialTorsorAction_hom, one_mul]
  erw [ι_trivialTorsorLeft]
  rw [h2, Category.assoc, hequiv h]
  erw [reassoc_of% hι1]
  erw [ι_trivialTorsorAction_hom]

omit [Finite G] in
/-- Compatibility with the equivariant maps reads off the group element: if `f`
sends the identity summand to the `γ₀`-summand and intertwines the trivial
equivariant maps of `t` and `t'`, then `t ≫ σ(γ₀⁻¹) = t'`. -/
private theorem trivialTorsorMap_pt_eq {S : Scheme.{u}}
    {f : (∐ fun _ : G => S) ⟶ (∐ fun _ : G => S)} {t t' : S ⟶ X} {γ₀ : G}
    (hcompat : f ≫ trivialTorsorMap σ S t' = trivialTorsorMap σ S t)
    (hι1 : Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ f =
      Limits.Sigma.ι (fun _ : G => S) γ₀) :
    t ≫ σ.hom γ₀⁻¹ = t' := by
  have h3 := congrArg
    (fun k => Limits.Sigma.ι (fun _ : G => S) (1 : G) ≫ k) hcompat
  rw [reassoc_of% hι1] at h3
  rw [ι_trivialTorsorMap] at h3
  erw [ι_trivialTorsorMap, σ.hom_one, Category.comp_id] at h3
  rw [← h3, Category.assoc, ← σ.hom_mul, mul_inv_cancel, σ.hom_one,
    Category.comp_id]

/-- **The trivialization functor is full over a connected base** (T-W3b): a
torsor-pair morphism between trivial pairs restricts on the identity summand to
a map into a single summand (the clopen pieces it cuts out of the connected
base collapse to one), and equivariance then forces it to be a left
translation. -/
theorem trivialize_full (S : Scheme.{u}) [ConnectedSpace S] :
    (trivialize σ S).Full where
  map_surjective {t t'} m := by
    -- restrict `m.hom` to the identity summand: connectedness lands it in a
    -- single summand `γ₀` (`ι 1 ≫ m.hom = ι γ₀`)
    obtain ⟨γ₀, hι1⟩ := exists_sigmaι_one_comp_eq (f := m.hom) m.over
    -- equivariance identifies `m.hom` with left translation by `γ₀`
    have hall : m.hom = trivialTorsorLeft G S γ₀ :=
      eq_trivialTorsorLeft_of_ι_one (f := m.hom) m.equiv hι1
    -- compatibility with the maps to `X` yields the groupoid morphism `γ₀⁻¹`
    have hpt : t.pt ≫ σ.hom γ₀⁻¹ = t'.pt :=
      trivialTorsorMap_pt_eq (σ := σ) (f := m.hom) m.compat hι1
    refine ⟨⟨γ₀⁻¹, hpt⟩, ?_⟩
    refine TorsorPair.Hom.ext ?_
    show trivialTorsorLeft G S γ₀⁻¹⁻¹ = m.hom
    rw [inv_inv, hall]

section PullbackTorsor

variable {σ} {S S' : Scheme.{u}} (q : S' ⟶ S)

/-- The base-changed action on the pulled-back torsor total space (T-W3c). -/
noncomputable def TorsorPair.pullbackAction (A : TorsorPair σ S) :
    SchemeAction G (Limits.pullback A.p q) where
  hom g := Limits.pullback.map A.p q A.p q (A.τ.hom g) (𝟙 S') (𝟙 S)
    (by rw [A.over_base, Category.comp_id])
    (by rw [Category.id_comp, Category.comp_id])
  hom_one := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Limits.pullback.lift_fst, A.τ.hom_one, Category.comp_id,
        Category.id_comp]
    · rw [Limits.pullback.lift_snd, Category.comp_id, Category.id_comp]
  hom_mul g h := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Limits.pullback.lift_fst, A.τ.hom_mul, Category.assoc]
      erw [Limits.pullback.lift_fst]
      conv_rhs => rw [← Category.assoc]
      erw [Limits.pullback.lift_fst]
      rw [Category.assoc]
    · rw [Limits.pullback.lift_snd,
        Category.comp_id (Limits.pullback.snd A.p q), Category.assoc]
      erw [Limits.pullback.lift_snd]
      rw [Category.comp_id (Limits.pullback.snd A.p q)]
      erw [Limits.pullback.lift_snd]
      rw [Category.comp_id (Limits.pullback.snd A.p q)]

omit [Finite G] in
@[reassoc (attr := simp)]
theorem TorsorPair.pullbackAction_hom_fst (A : TorsorPair σ S) (g : G) :
    (A.pullbackAction q).hom g ≫ Limits.pullback.fst A.p q =
      Limits.pullback.fst A.p q ≫ A.τ.hom g :=
  Limits.pullback.lift_fst _ _ _

omit [Finite G] in
@[reassoc (attr := simp)]
theorem TorsorPair.pullbackAction_hom_snd (A : TorsorPair σ S) (g : G) :
    (A.pullbackAction q).hom g ≫ Limits.pullback.snd A.p q =
      Limits.pullback.snd A.p q := by
  rw [show (A.pullbackAction q).hom g ≫ Limits.pullback.snd A.p q =
      Limits.pullback.snd A.p q ≫ 𝟙 S' from Limits.pullback.lift_snd _ _ _,
    Category.comp_id (Limits.pullback.snd A.p q)]

omit [Finite G] in
/-- The base-changed action lies over the new base. -/
theorem TorsorPair.pullbackAction_over_base (A : TorsorPair σ S) (g : G) :
    (A.pullbackAction q).hom g ≫ Limits.pullback.snd A.p q =
      Limits.pullback.snd A.p q :=
  A.pullbackAction_hom_snd q g

/-! ### Pullback-juggling for the base-changed torsor field (T-W3c-i)

The `torsor` field of `A.pullback q` is `A.torsor` base-changed along `q`. Two
geometric identifications carry it there: the *pasting* iso
`(P ×_S S') ×_{S'} (P ×_S S') ≅ (P ×_S P) ×_S S'` (`isPullback_pullbackSnd_map`)
and the *distributivity* iso `∐_G (P ×_S S') ≅ (∐_G P) ×_S S'`
(`isPullback_sigma_pullbackSnd`, via extensivity). Composed by pasting-cancellation
they exhibit the base-changed shear map as the base change of the original, hence an
isomorphism. -/

/-- **Pasting identification.** The double pullback
`(P ×_S S') ×_{S'} (P ×_S S')` is the base change of `(P ×_S P) → S` along `q`:
the square with `pullback (pullback.snd p q) (pullback.snd p q)` as apex,
`pullback.map …` to `P ×_S P`, and `pullback.fst p p ≫ p` / `q` as the cospan. -/
private theorem isPullback_pullbackSnd_map {P : Scheme.{u}} (p : P ⟶ S) :
    IsPullback
      (Limits.pullback.fst (Limits.pullback.snd p q) (Limits.pullback.snd p q) ≫
        Limits.pullback.snd p q)
      (Limits.pullback.map (Limits.pullback.snd p q) (Limits.pullback.snd p q) p p
        (Limits.pullback.fst p q) (Limits.pullback.fst p q) q
        Limits.pullback.condition.symm Limits.pullback.condition.symm)
      q (Limits.pullback.fst p p ≫ p) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    { hom := Limits.pullback.lift
        (Limits.pullback.fst (Limits.pullback.snd p q) (Limits.pullback.snd p q) ≫
          Limits.pullback.snd p q)
        (Limits.pullback.map (Limits.pullback.snd p q) (Limits.pullback.snd p q) p p
          (Limits.pullback.fst p q) (Limits.pullback.fst p q) q
          Limits.pullback.condition.symm Limits.pullback.condition.symm) ?_
      inv := Limits.pullback.lift
        (Limits.pullback.lift
          (Limits.pullback.snd q (Limits.pullback.fst p p ≫ p) ≫ Limits.pullback.fst p p)
          (Limits.pullback.fst q (Limits.pullback.fst p p ≫ p)) ?_)
        (Limits.pullback.lift
          (Limits.pullback.snd q (Limits.pullback.fst p p ≫ p) ≫ Limits.pullback.snd p p)
          (Limits.pullback.fst q (Limits.pullback.fst p p ≫ p)) ?_) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ } ?_ ?_
  · -- CommSq: (fst ≫ p') ≫ q = map ≫ (fst_pp ≫ p)
    simp only [Limits.pullback.map, Category.assoc, Limits.pullback.lift_fst_assoc]
    rw [← Limits.pullback.condition]
  · -- forward CommSq of the lift (same identity)
    simp only [Limits.pullback.map, Category.assoc, Limits.pullback.lift_fst_assoc]
    rw [← Limits.pullback.condition]
  · -- cond1
    rw [Category.assoc, ← Limits.pullback.condition]
  · -- cond2
    rw [Category.assoc, ← Limits.pullback.condition, ← Limits.pullback.condition]
  · -- hlegs: both legs equal on p' = snd p q
    rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd]
  · -- hom_inv_id
    ext <;>
      simp only [Limits.pullback.map, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
        Limits.pullback.lift_snd_assoc,
        Limits.pullback.condition, Category.assoc, Category.id_comp]
  · -- inv_hom_id
    ext <;>
      simp only [Limits.pullback.map, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
        Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd_assoc,
        Limits.pullback.condition, Category.assoc, Category.id_comp]
  · exact Limits.pullback.lift_fst _ _ _
  · exact Limits.pullback.lift_snd _ _ _

omit [Group G] in
/-- **Distributivity identification.** Finite coproducts distribute over the base
change: `∐_G (P ×_S S')` is the base change of `∐_G P → S` along `q`, via the
extensivity of `Scheme` (`FinitaryPreExtensive`). -/
private theorem isPullback_sigma_pullbackSnd {P : Scheme.{u}} (p : P ⟶ S) :
    IsPullback
      (Limits.Sigma.desc (fun _ : G => Limits.pullback.snd p q))
      (Limits.Sigma.desc (fun g : G =>
        Limits.pullback.fst p q ≫ Limits.Sigma.ι (fun _ : G => P) g))
      q (Limits.Sigma.desc (fun _ : G => p)) := by
  have key := (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (Limits.coproductIsCoproduct (fun _ : G => P))).isPullback_of_isColimit_left
    (f := fun _ : G => p) (u := Limits.Sigma.desc fun _ : G => p) (v := q)
    (q₁ := fun _ : G => Limits.pullback.snd p q)
    (q₂ := fun _ : G => Limits.pullback.fst p q)
    (fun _ => (IsPullback.of_hasPullback p q).flip)
    (Limits.coproductIsCoproduct (fun _ : G => Limits.pullback p q))
    (fun i => Limits.Sigma.ι_desc _ _)
  exact key

/-- **The base-changed shear map is an isomorphism** (T-W3c-i, the `torsor` field of
`A.pullback q`). The shear of the base-changed action is the base change of `A`'s
shear map (`A.torsor`) along `q`: the pasting (`isPullback_pullbackSnd_map`) and
distributivity (`isPullback_sigma_pullbackSnd`) squares cancel to exhibit it as such,
and isomorphisms are stable under base change. -/
theorem TorsorPair.pullback_shear_isIso (A : TorsorPair σ S) :
    IsIso (Limits.Sigma.desc fun g : G => Limits.pullback.lift ((A.pullbackAction q).hom g)
        (𝟙 (Limits.pullback A.p q))
        (by rw [Category.id_comp]; exact A.pullbackAction_over_base q g) :
      (∐ fun _ : G => Limits.pullback A.p q) ⟶
        Limits.pullback (Limits.pullback.snd A.p q) (Limits.pullback.snd A.p q)) := by
  set Φ' := Limits.Sigma.desc (fun g : G => Limits.pullback.lift ((A.pullbackAction q).hom g)
      (𝟙 (Limits.pullback A.p q))
      (by rw [Category.id_comp]; exact A.pullbackAction_over_base q g)) with hΦ'
  set Φ := Limits.Sigma.desc (fun g : G => Limits.pullback.lift (A.τ.hom g) (𝟙 A.P)
      (by rw [Category.id_comp]; exact A.over_base g)) with hΦ
  have hπ : Φ' ≫ (Limits.pullback.fst (Limits.pullback.snd A.p q) (Limits.pullback.snd A.p q) ≫
        Limits.pullback.snd A.p q) = Limits.Sigma.desc fun _ : G => Limits.pullback.snd A.p q := by
    refine Limits.Sigma.hom_ext _ _ fun g => ?_
    simp only [hΦ', Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc,
      Limits.pullback.lift_fst_assoc, TorsorPair.pullbackAction_hom_snd]
  have hpp : Φ ≫ (Limits.pullback.fst A.p A.p ≫ A.p) = Limits.Sigma.desc fun _ : G => A.p := by
    refine Limits.Sigma.hom_ext _ _ fun g => ?_
    simp only [hΦ, Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc,
      Limits.pullback.lift_fst_assoc, A.over_base]
  have hcomm : Φ' ≫ Limits.pullback.map (Limits.pullback.snd A.p q) (Limits.pullback.snd A.p q)
        A.p A.p (Limits.pullback.fst A.p q) (Limits.pullback.fst A.p q) q
        Limits.pullback.condition.symm Limits.pullback.condition.symm =
      (Limits.Sigma.desc fun g : G =>
        Limits.pullback.fst A.p q ≫ Limits.Sigma.ι (fun _ : G => A.P) g) ≫ Φ := by
    refine Limits.Sigma.hom_ext _ _ fun g => ?_
    refine Limits.pullback.hom_ext ?_ ?_ <;>
      simp only [hΦ', hΦ, Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, Category.assoc,
        Limits.pullback.map, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
        Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc,
        TorsorPair.pullbackAction_hom_fst, Category.id_comp, Category.comp_id]
  have s : IsPullback (Φ' ≫ (Limits.pullback.fst (Limits.pullback.snd A.p q)
        (Limits.pullback.snd A.p q) ≫ Limits.pullback.snd A.p q))
      (Limits.Sigma.desc fun g : G =>
        Limits.pullback.fst A.p q ≫ Limits.Sigma.ι (fun _ : G => A.P) g)
      q (Φ ≫ (Limits.pullback.fst A.p A.p ≫ A.p)) := by
    rw [hπ, hpp]; exact isPullback_sigma_pullbackSnd q A.p
  have hLeft := s.of_right hcomm (isPullback_pullbackSnd_map q A.p)
  exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
    hLeft.flip A.torsor

set_option backward.isDefEq.respectTransparency false in
/-- **Base change of a torsor pair** (T-W3c-i): pull `A : TorsorPair σ S` back along
`q : S' ⟶ S`. Total space `P ×_S S'`, projection `pullback.snd`, action by
functoriality (`pullbackAction`); the property fields are base-change stability and
`pullback_shear_isIso`, and the equivariant map factors through `A.u`. -/
noncomputable def TorsorPair.pullback (A : TorsorPair σ S) : TorsorPair σ S' where
  P := Limits.pullback A.p q
  p := Limits.pullback.snd A.p q
  τ := A.pullbackAction q
  over_base := A.pullbackAction_over_base q
  finite := by haveI := A.finite; infer_instance
  etale := MorphismProperty.pullback_snd A.p q A.etale
  surjective := MorphismProperty.pullback_snd A.p q A.surjective
  torsor := A.pullback_shear_isIso q
  u := Limits.pullback.fst A.p q ≫ A.u
  equivariant := fun g => by
    rw [← Category.assoc, TorsorPair.pullbackAction_hom_fst, Category.assoc,
      A.equivariant g, Category.assoc]

/-! ### Self-trivialization (T-W3c-ii)

Pulling a torsor pair back along its own projection trivializes it: the comparison
`∐_G P ≅ P ×_S P` (`A.torsor`) *is* the trivialization. This is NOT descent-gated —
the `torsor` field already witnesses local triviality along `p`. -/

/-- A torsor-pair morphism whose underlying scheme map is an isomorphism has an
inverse morphism of torsor pairs (torsor pairs form a groupoid). -/
noncomputable def TorsorPair.homInv {T : Scheme.{u}} {A' B' : TorsorPair σ T}
    (f : A' ⟶ B') [IsIso f.hom] : B' ⟶ A' where
  hom := inv f.hom
  over := by rw [← f.over, IsIso.inv_hom_id_assoc]
  equiv := fun g => by
    rw [IsIso.comp_inv_eq, Category.assoc, f.equiv g, IsIso.inv_hom_id_assoc]
  compat := by rw [← f.compat, IsIso.inv_hom_id_assoc]

/-- A torsor-pair morphism with isomorphic underlying map is an isomorphism. -/
noncomputable def TorsorPair.isoOfHom {T : Scheme.{u}} {A' B' : TorsorPair σ T}
    (f : A' ⟶ B') [IsIso f.hom] : A' ≅ B' where
  hom := f
  inv := TorsorPair.homInv f
  hom_inv_id := by
    refine TorsorPair.Hom.ext ?_
    show f.hom ≫ inv f.hom = 𝟙 _
    exact IsIso.hom_inv_id _
  inv_hom_id := by
    refine TorsorPair.Hom.ext ?_
    show inv f.hom ≫ f.hom = 𝟙 _
    exact IsIso.inv_hom_id _

/-- **Self-trivialization** (T-W3c-ii): the base change of a torsor pair `A` along
its own projection `A.p` is the trivial torsor pair over the total space `A.P`
(attached to the equivariant map `A.u`). The comparison is `A.torsor`'s shear
`∐_G A.P ≅ A.P ×_S A.P`, read as a morphism of torsor pairs. -/
noncomputable def TorsorPair.selfTrivialization (A : TorsorPair σ S) :
    A.pullback A.p ≅ trivialTorsorPair σ A.P A.u := by
  let f : trivialTorsorPair σ A.P A.u ⟶ A.pullback A.p :=
    { hom := Limits.Sigma.desc fun g : G => Limits.pullback.lift (A.τ.hom g)
        (𝟙 A.P) (by rw [Category.id_comp]; exact A.over_base g)
      over := by
        refine Limits.Sigma.hom_ext _ _ fun g => ?_
        simp only [TorsorPair.pullback, trivialTorsorPair, Limits.Sigma.ι_desc_assoc,
          Limits.pullback.lift_snd, ι_trivialTorsorπ]
      equiv := fun g => by
        refine Limits.Sigma.hom_ext _ _ fun h => ?_
        refine Limits.pullback.hom_ext ?_ ?_ <;>
          simp only [TorsorPair.pullback, trivialTorsorPair, ι_trivialTorsorAction_hom_assoc,
            Limits.Sigma.ι_desc_assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
            Limits.pullback.lift_snd,
            TorsorPair.pullbackAction_hom_fst, TorsorPair.pullbackAction_hom_snd,
            SchemeAction.hom_mul, Category.assoc]
      compat := by
        refine Limits.Sigma.hom_ext _ _ fun g => ?_
        simp only [TorsorPair.pullback, trivialTorsorPair, Limits.Sigma.ι_desc_assoc,
          Limits.pullback.lift_fst_assoc, ι_trivialTorsorMap, A.equivariant] }
  haveI : IsIso f.hom := A.torsor
  exact (TorsorPair.isoOfHom f).symm

end PullbackTorsor

end Trivialize

end TorsorPair

end ModularCurves

