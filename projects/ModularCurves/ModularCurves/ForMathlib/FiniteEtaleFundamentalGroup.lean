/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology

import ModularCurves.ForMathlib.FiniteEtaleFiberFunctor

/-!
# The absolute Galois group is the fundamental group of `FiniteEtale k`

We show `Gal(k^sep/k) = (SeparableClosure k ≃ₐ[k] SeparableClosure k)` with its Krull
topology is a fundamental group (in the sense of
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`) for the fiber functor of
`(FiniteEtale k)ᵒᵖ` at the separable closure:

* the natural action is post-composition on points;
* connected objects are fields (`isField_of_isConnected`), so transitivity on Galois
  objects is conjugacy of embeddings (`AlgEquiv.liftNormal`);
* stabilisers of points are fixing subgroups of finite-dimensional intermediate
  fields, which are open in the Krull topology;
* an automorphism acting trivially on all fibers fixes every element of the
  separable closure.
-/

universe u

open CategoryTheory Limits CommAlgCat

open scoped TensorProduct CategoryTheory.PreGaloisCategory FintypeCatDiscrete

namespace ModularCurves

namespace FiniteEtaleGalois

variable (k : Type u) [Field k]

/- Named compatibility instances for downstream code that refers directly to the
`SeparableClosure` abbreviation. -/

section InstanceBridges

instance (priority := high) isSepClosure_sepClosure :
    IsSepClosure k (SeparableClosure k) := inferInstance

instance (priority := high) isGalois_sepClosure :
    IsGalois k (SeparableClosure k) := inferInstance

instance (priority := high) normal_sepClosure :
    Normal k (SeparableClosure k) := inferInstance

instance (priority := high) isSepClosed_sepClosure :
    IsSepClosed (SeparableClosure k) := inferInstance

instance (priority := high) isSeparable_sepClosure :
    Algebra.IsSeparable k (SeparableClosure k) := inferInstance

instance (priority := high) compactSpace_galSepClosure :
    CompactSpace (SeparableClosure k ≃ₐ[k] SeparableClosure k) := inferInstance

end InstanceBridges

section Action

variable {k}

variable (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- The Galois group of the geometric point acts on the fibers by post-composition.
Stated for a general coefficient field `Ω` so that the instance head stays free of
`SeparableClosure`'s instance chains (unification on those gets stuck). -/
noncomputable instance fiberMulAction (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    MulAction (Ω ≃ₐ[k] Ω) ((CommAlgCat.FiniteEtale.fiber k Ω).obj X) where
  smul σ x := σ.toAlgHom.comp x
  one_smul _x := AlgHom.ext fun _a => rfl
  mul_smul _σ _τ _x := AlgHom.ext fun _a => rfl

/-- The action on a fiber is post-composition by a field automorphism. -/
lemma fiber_smul_def (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (σ : Ω ≃ₐ[k] Ω)
    (x : (CommAlgCat.FiniteEtale.fiber k Ω).obj X) :
    σ • x = σ.toAlgHom.comp x :=
  rfl

instance : PreGaloisCategory.IsNaturalSMul
    (CommAlgCat.FiniteEtale.fiber k Ω) (Ω ≃ₐ[k] Ω) where
  naturality _σ {_X _Y} _f _x := AlgHom.ext fun _a => rfl

end Action

section Connected

variable {k}

/-- The `k`-algebra map into a subsingleton algebra. -/
private noncomputable def algHomToSubsingleton {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] [Subsingleton B] : A →ₐ[k] B where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- A finite étale algebra with subsingleton carrier is terminal. -/
private noncomputable def isTerminalOfSubsingleton (T : CommAlgCat.FiniteEtale.{u} k)
    [Subsingleton (T : Type u)] : IsTerminal T :=
  haveI : ∀ B : CommAlgCat.FiniteEtale.{u} k, Unique (B ⟶ T) := fun B =>
    { default := ObjectProperty.homMk (CommAlgCat.ofHom algHomToSubsingleton)
      uniq := fun f => by ext b; exact Subsingleton.elim _ _ }
  IsTerminal.ofUnique _

/-- The carrier of a connected object of `(FiniteEtale k)ᵒᵖ` is nontrivial. -/
theorem nontrivial_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X] : Nontrivial (X.unop : Type u) := by
  rcases subsingleton_or_nontrivial (X.unop : Type u) with hsub | h
  · exfalso
    apply PreGaloisCategory.IsConnected.notInitial (X := X)
    exact initialOpOfTerminal (isTerminalOfSubsingleton X.unop)
  · exact h

/-- A nontrivial finite étale algebra's opposite object is not initial: an initial
opposite would force the object to be terminal, hence isomorphic to the subsingleton
`Fin 0 → k`, contradicting nontriviality. -/
private lemma not_isInitial_op_of_nontrivial (Y : CommAlgCat.FiniteEtale.{u} k)
    [Nontrivial (Y : Type u)] (hini : IsInitial (Opposite.op Y)) : False := by
  have hterm : IsTerminal Y := terminalUnopOfInitial hini
  haveI : Algebra.FinitePresentation k (Fin 0 → k) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale k (Fin 0 → k) := ⟨inferInstance, inferInstance⟩
  have hiso2 := hterm.uniqueUpToIso
    (isTerminalOfSubsingleton (CommAlgCat.FiniteEtale.of k (Fin 0 → k)))
  haveI : Subsingleton (Y : Type u) :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso hiso2.hom).1.subsingleton
  exact false_of_nontrivial_of_subsingleton (Y : Type u)

/-- Connected finite étale algebras over a field are fields. -/
theorem isField_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X] : IsField (X.unop : Type u) := by
  haveI hnt : Nontrivial (X.unop : Type u) := nontrivial_of_isConnected X
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal (X.unop : Type u)
  haveI := hm₀
  haveI : Algebra.Etale k ((X.unop : Type u) ⧸ m₀) := etale_quotient m₀
  haveI : Module.Finite k ((X.unop : Type u) ⧸ m₀) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m₀).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Field ((X.unop : Type u) ⧸ m₀) := Ideal.Quotient.field m₀
  set q : X.unop ⟶ CommAlgCat.FiniteEtale.of k ((X.unop : Type u) ⧸ m₀) :=
    ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k m₀)) with hq
  haveI : Epi ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q) :=
    CategoryTheory.ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Epi q := (ObjectProperty.ι (CommAlgCat.finiteEtale k)).epi_of_epi_map
    inferInstance
  haveI hmono : Mono q.op := inferInstance
  haveI : Nontrivial (CommAlgCat.FiniteEtale.of k ((X.unop : Type u) ⧸ m₀) : Type u) :=
    inferInstanceAs (Nontrivial ((X.unop : Type u) ⧸ m₀))
  have hiso : IsIso q.op :=
    PreGaloisCategory.IsConnected.noTrivialComponent _ q.op
      (not_isInitial_op_of_nontrivial _)
  haveI : IsIso q := (isIso_op_iff q).mp hiso
  haveI : IsIso ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q) :=
    Functor.map_isIso _ q
  have hbij : Function.Bijective (Ideal.Quotient.mkₐ k m₀) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q)
  exact (AlgEquiv.ofBijective (Ideal.Quotient.mkₐ k m₀) hbij).toMulEquiv.isField
    (Field.toIsField ((X.unop : Type u) ⧸ m₀))

end Connected

section FundamentalGroup

variable {k}

/-- The range of a point of a finite étale algebra is a finite field extension inside
the separable closure. -/
private lemma isField_range {A : CommAlgCat.FiniteEtale.{u} k}
    (x : (A : Type u) →ₐ[k] SeparableClosure k) : IsField x.range :=
  x.range.isField_of_algebraic

/-- The Galois group acts transitively on the points of a connected finite étale
algebra: any two embeddings into the separable closure are conjugate. -/
theorem exists_smul_eq_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X]
    (x y : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, σ • x = y := by
  letI : Field (X.unop : Type u) := (isField_of_isConnected X).toField
  let x' : (X.unop : Type u) →ₐ[k] SeparableClosure k := x
  let y' : (X.unop : Type u) →ₐ[k] SeparableClosure k := y
  letI : Field x'.range := (isField_range x').toField
  letI : Field y'.range := (isField_range y').toField
  set χ : (x'.range : Subalgebra k (SeparableClosure k)) ≃ₐ[k] y'.range :=
    (AlgEquiv.ofInjectiveField x').symm.trans (AlgEquiv.ofInjectiveField y') with hχ
  refine ⟨χ.liftNormal (SeparableClosure k), AlgHom.ext fun a => ?_⟩
  change (χ.liftNormal (SeparableClosure k)) (x' a) = y' a
  convert χ.liftNormal_commutes (SeparableClosure k) (AlgEquiv.ofInjectiveField x' a) using 1
  · rfl
  · simp only [hχ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rfl

/-- The stabiliser of a point is the fixing subgroup of a finite-dimensional
intermediate field, hence open. -/
theorem stabilizer_isOpen (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (x : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) :
    IsOpen {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k | σ • x = x} := by
  let x' : (X.unop : Type u) →ₐ[k] SeparableClosure k := x
  have hinv : ∀ ω ∈ x'.range, ω⁻¹ ∈ x'.range := by
    intro ω hω
    rcases eq_or_ne ω 0 with rfl | hne
    · rw [inv_zero]; exact zero_mem _
    obtain ⟨⟨b, hb⟩, hb'⟩ := (isField_range x').mul_inv_cancel
      (a := ⟨ω, hω⟩) (fun h => hne (congrArg Subtype.val h))
    have : ω * b = 1 := congrArg Subtype.val hb'
    rw [inv_eq_of_mul_eq_one_right this]
    exact hb
  set E : IntermediateField k (SeparableClosure k) := x'.range.toIntermediateField hinv
  haveI : Module.Finite k x'.range :=
    Module.Finite.of_surjective x'.rangeRestrict.toLinearMap x'.rangeRestrict_surjective
  haveI : FiniteDimensional k E := inferInstanceAs (Module.Finite k x'.range)
  have hset : {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k | σ • x = x} =
      (E.fixingSubgroup : Set (SeparableClosure k ≃ₐ[k] SeparableClosure k)) := by
    ext σ
    constructor
    · intro hσ
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      intro ω hω
      obtain ⟨a, rfl⟩ := hω
      exact AlgHom.congr_fun (show σ.toAlgHom.comp x' = x' from hσ) a
    · intro hσ
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
      show σ.toAlgHom.comp x' = x'
      exact AlgHom.ext fun a => hσ (x' a) ⟨a, rfl⟩
  rw [hset]
  exact E.fixingSubgroup_isOpen

/-- An automorphism of the separable closure acting trivially on all fibers is the
identity. -/
theorem eq_one_of_smul_eq (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (h : ∀ (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (x : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X), σ • x = x) :
    σ = 1 := by
  refine AlgEquiv.ext fun ω => ?_
  set L : IntermediateField k (SeparableClosure k) :=
    IntermediateField.adjoin k ({ω} : Set (SeparableClosure k))
  haveI : FiniteDimensional k L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ω)
  haveI : Algebra.IsSeparable k L :=
    Algebra.isSeparable_tower_bot_of_isSeparable k L (SeparableClosure k)
  haveI : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  haveI : Algebra.FinitePresentation k L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale k L := ⟨inferInstance, inferInstance⟩
  exact AlgHom.congr_fun (h (Opposite.op (CommAlgCat.FiniteEtale.of k L)) L.val)
    ⟨ω, IntermediateField.mem_adjoin_simple_self k ω⟩

instance : GaloisCategory (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ where
  hasFiberFunctor :=
    ⟨CommAlgCat.FiniteEtale.fiber k (SeparableClosure k), inferInstance⟩

/-- The absolute Galois group of `k` is a fundamental group for the fiber functor of
`(FiniteEtale k)ᵒᵖ` at the separable closure. -/
noncomputable instance isFundamentalGroup_galSepClosure :
    PreGaloisCategory.IsFundamentalGroup
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u})
    (SeparableClosure k ≃ₐ[k] SeparableClosure k) where
  naturality σ {X Y} f x := AlgHom.ext fun a => rfl
  transitive_of_isGalois X _ := ⟨fun x y => exists_smul_eq_of_isConnected X x y⟩
  continuous_smul X := by
    constructor
    letI : TopologicalSpace
        ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) := ⊥
    refine continuous_discrete_rng.mpr fun y => ?_
    have hdecomp : (fun p : (SeparableClosure k ≃ₐ[k] SeparableClosure k) ×
          ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) =>
        p.1 • p.2) ⁻¹' {y} =
        ⋃ x₀ : ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X),
          {σ | σ • x₀ = y} ×ˢ ({x₀} : Set _) := by
      ext ⟨σ, x₀⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_prod,
        Set.mem_setOf_eq, exists_eq_right']
    rw [hdecomp]
    refine isOpen_iUnion fun x₀ => IsOpen.prod ?_ trivial
    rcases Set.eq_empty_or_nonempty {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k |
      σ • x₀ = y} with hemp | ⟨σ₀, hσ₀⟩
    · rw [hemp]; exact isOpen_empty
    · change σ₀ • x₀ = y at hσ₀
      have hcoset : {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k | σ • x₀ = y} =
          (fun σ => σ₀⁻¹ * σ) ⁻¹' {σ | σ • x₀ = x₀} := by
        ext σ
        simp only [Set.mem_setOf_eq, Set.mem_preimage, mul_smul, inv_smul_eq_iff, hσ₀]
      rw [hcoset]
      exact (stabilizer_isOpen X x₀).preimage (continuous_const.mul continuous_id)
  non_trivial' σ h := eq_one_of_smul_eq σ h

end FundamentalGroup

section Correspondence

variable {k}

open PreGaloisCategory in
/-- The comparison isomorphism of a fundamental group with `Aut F`, bundled as a
continuous multiplicative equivalence. -/
noncomputable def toAutContinuousMulEquiv {C : Type*} [Category C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{u}) [FiberFunctor F] (G : Type*) [Group G]
    [∀ X, MulAction G (F.obj X)] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [IsFundamentalGroup F G] : G ≃ₜ* Aut F :=
  (toAutMulEquiv F G).toContinuousMulEquiv fun _ =>
    (toAutMulEquiv_isHomeomorph F G).isQuotientMap.isOpen_preimage

variable (k)

/-- **The Galois correspondence for finite étale algebras**: the opposite of the
category of finite étale `k`-algebras is equivalent to the category of finite
discrete sets with continuous action of the absolute Galois group `Gal(k^sep/k)`. -/
noncomputable def finiteEtaleEquivContAction :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ≌
      ContAction FintypeCat.{u} (SeparableClosure k ≃ₐ[k] SeparableClosure k) :=
  (PreGaloisCategory.functorToContAction
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u})).asEquivalence.trans
    (ContAction.resEquiv FintypeCat.{u}
      (toAutContinuousMulEquiv
        (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k))
        (SeparableClosure k ≃ₐ[k] SeparableClosure k)))

/-- The fiber of the finite étale algebra corresponding to a continuous Galois set
recovers the set: the counit of the Galois correspondence, at the level of underlying
finite sets. -/
noncomputable def pointsEquivOfContAction
    (X : ContAction FintypeCat.{u} (SeparableClosure k ≃ₐ[k] SeparableClosure k)) :
    ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj
      ((finiteEtaleEquivContAction k).inverse.obj X) : Type u) ≃ (X.obj.V : Type u) :=
  FintypeCat.equivEquivIso.symm
    ((CategoryTheory.forget₂ (ContAction FintypeCat.{u}
        (SeparableClosure k ≃ₐ[k] SeparableClosure k)) FintypeCat.{u}).mapIso
      ((finiteEtaleEquivContAction k).counitIso.app X))

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit points-equivalence is Galois-equivariant: the fiber action (by
post-composition) corresponds to the action of the continuous Galois set. -/
lemma pointsEquivOfContAction_smul
    (X : ContAction FintypeCat.{u} (SeparableClosure k ≃ₐ[k] SeparableClosure k))
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (x : ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj
      ((finiteEtaleEquivContAction k).inverse.obj X) : Type u)) :
    pointsEquivOfContAction k X (σ • x) =
      (show X.obj.V ⟶ X.obj.V from X.obj.ρ σ) (pointsEquivOfContAction k X x) := by
  have hc := ((finiteEtaleEquivContAction k).counitIso.hom.app X).hom.comm σ
  have h2 := congrArg (fun q => q x) hc
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  exact h2

/-- The functor of the Galois correspondence acts on morphisms by the fiber functor
(the `resEquiv`/`functorToContAction` layers only re-index the group side). -/
lemma finiteEtaleEquivContAction_functor_map_hom
    {X Y : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ} (f : X ⟶ Y) :
    ((finiteEtaleEquivContAction k).functor.map f).hom.hom =
      (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).map f := rfl

end Correspondence

end FiniteEtaleGalois

end ModularCurves
