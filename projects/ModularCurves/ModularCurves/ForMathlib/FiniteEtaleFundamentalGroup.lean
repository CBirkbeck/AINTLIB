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

/-! Instance bridges: mathlib's instances for `separableClosure` are keyed on the
`↥(separableClosure F E)` spelling and do not fire against the `SeparableClosure F`
abbreviation (the `CoeSort` paths differ), so we re-register the ones downstream
consumers need, keyed on the abbreviation. -/

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

/-! The natural action of the Galois group on the fibers (leaf AG-GG-3a). -/

section Action

variable {k}

variable (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- The Galois group of the geometric point acts on the fibers by post-composition.
Stated for a general coefficient field `Ω` so that the instance head stays free of
`SeparableClosure`'s instance chains (unification on those gets stuck). -/
noncomputable instance fiberMulAction (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    MulAction (Ω ≃ₐ[k] Ω) ((CommAlgCat.FiniteEtale.fiber k Ω).obj X) where
  smul σ x := σ.toAlgHom.comp x
  one_smul x := AlgHom.ext fun a => rfl
  mul_smul σ τ x := AlgHom.ext fun a => rfl

lemma fiber_smul_def (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (σ : Ω ≃ₐ[k] Ω)
    (x : (CommAlgCat.FiniteEtale.fiber k Ω).obj X) :
    σ • x = σ.toAlgHom.comp x :=
  rfl

instance : PreGaloisCategory.IsNaturalSMul
    (CommAlgCat.FiniteEtale.fiber k Ω) (Ω ≃ₐ[k] Ω) where
  naturality σ {X Y} f x := AlgHom.ext fun a => rfl

end Action

/-! Connected finite étale algebras are fields (leaf AG-GG-3d). -/

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
  have hiso : IsIso q.op := by
    refine PreGaloisCategory.IsConnected.noTrivialComponent _ q.op ?_
    intro hini
    have hterm : IsTerminal (CommAlgCat.FiniteEtale.of k ((X.unop : Type u) ⧸ m₀)) :=
      terminalUnopOfInitial hini
    haveI : Algebra.FinitePresentation k (Fin 0 → k) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    haveI : Algebra.Etale k (Fin 0 → k) := ⟨inferInstance, inferInstance⟩
    have hiso2 := hterm.uniqueUpToIso
      (isTerminalOfSubsingleton (CommAlgCat.FiniteEtale.of k (Fin 0 → k)))
    have hcarrier : ((X.unop : Type u) ⧸ m₀) ≃ (Fin 0 → k) :=
      ⟨hiso2.hom.hom.hom, hiso2.inv.hom.hom,
        fun a => congrArg (fun (t : CommAlgCat.FiniteEtale.of k
          ((X.unop : Type u) ⧸ m₀) ⟶ CommAlgCat.FiniteEtale.of k
          ((X.unop : Type u) ⧸ m₀)) => t.hom.hom a) hiso2.hom_inv_id,
        fun a => congrArg (fun (t : CommAlgCat.FiniteEtale.of k (Fin 0 → k) ⟶
          CommAlgCat.FiniteEtale.of k (Fin 0 → k)) => t.hom.hom a)
          hiso2.inv_hom_id⟩
    haveI : Subsingleton ((X.unop : Type u) ⧸ m₀) := hcarrier.subsingleton
    exact false_of_nontrivial_of_subsingleton ((X.unop : Type u) ⧸ m₀)
  haveI : IsIso q := (isIso_op_iff q).mp hiso
  haveI : IsIso ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q) :=
    Functor.map_isIso _ q
  have hbij : Function.Bijective (Ideal.Quotient.mkₐ k m₀) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q)
  refine ⟨exists_pair_ne _, mul_comm, ?_⟩
  intro a ha
  have hea : Ideal.Quotient.mkₐ k m₀ a ≠ 0 := by
    intro h0
    exact ha (hbij.1 (h0.trans (map_zero _).symm))
  obtain ⟨b', hb'⟩ := IsUnit.exists_right_inv (Ne.isUnit hea)
  obtain ⟨b, rfl⟩ := hbij.2 b'
  refine ⟨b, hbij.1 ?_⟩
  rw [map_mul, map_one]
  exact hb'

end Connected

/-! Transitivity on connected objects (leaf AG-GG-3e), open stabilisers (leaf
AG-GG-3c), non-triviality (leaf AG-GG-3f), and the `IsFundamentalGroup` instance. -/

section FundamentalGroup

variable {k}

/-- The range of a point of a finite étale algebra is a finite field extension inside
the separable closure. -/
private lemma isField_range {A : CommAlgCat.FiniteEtale.{u} k}
    (x : (A : Type u) →ₐ[k] SeparableClosure k) : IsField x.range := by
  haveI : Module.Finite k x.range :=
    Module.Finite.of_surjective x.rangeRestrict.toLinearMap x.rangeRestrict_surjective
  exact isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)

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
  refine ⟨χ.liftNormal (SeparableClosure k), ?_⟩
  show (χ.liftNormal (SeparableClosure k)).toAlgHom.comp x' = y'
  refine AlgHom.ext fun a => ?_
  have h1 : (χ.liftNormal (SeparableClosure k))
      (algebraMap x'.range (SeparableClosure k) (AlgEquiv.ofInjectiveField x' a)) =
      algebraMap y'.range (SeparableClosure k) (χ (AlgEquiv.ofInjectiveField x' a)) :=
    χ.liftNormal_commutes (SeparableClosure k) _
  have h2 : χ (AlgEquiv.ofInjectiveField x' a) = AlgEquiv.ofInjectiveField y' a := by
    show (AlgEquiv.ofInjectiveField y') ((AlgEquiv.ofInjectiveField x').symm
      (AlgEquiv.ofInjectiveField x' a)) = _
    rw [AlgEquiv.symm_apply_apply]
  show (χ.liftNormal (SeparableClosure k)) (x' a) = y' a
  calc (χ.liftNormal (SeparableClosure k)) (x' a)
      = (χ.liftNormal (SeparableClosure k))
        (algebraMap x'.range (SeparableClosure k) (AlgEquiv.ofInjectiveField x' a)) := rfl
    _ = algebraMap y'.range (SeparableClosure k) (χ (AlgEquiv.ofInjectiveField x' a)) := h1
    _ = y' a := by rw [h2]; rfl

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
    with hE
  haveI : Module.Finite k x'.range :=
    Module.Finite.of_surjective x'.rangeRestrict.toLinearMap x'.rangeRestrict_surjective
  haveI : FiniteDimensional k E := inferInstanceAs (Module.Finite k x'.range)
  have hopen := E.fixingSubgroup_isOpen
  have hset : {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k | σ • x = x} =
      (E.fixingSubgroup : Set (SeparableClosure k ≃ₐ[k] SeparableClosure k)) := by
    ext σ
    constructor
    · intro hσ
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      intro ω hω
      obtain ⟨a, rfl⟩ := hω
      have hσ' : σ.toAlgHom.comp x' = x' := hσ
      exact AlgHom.congr_fun hσ' a
    · intro hσ
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
      show σ.toAlgHom.comp x' = x'
      refine AlgHom.ext fun a => ?_
      exact hσ (x' a) ⟨a, rfl⟩
  rw [hset]
  exact hopen

/-- An automorphism of the separable closure acting trivially on all fibers is the
identity. -/
theorem eq_one_of_smul_eq (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (h : ∀ (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (x : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X), σ • x = x) :
    σ = 1 := by
  refine AlgEquiv.ext fun ω => ?_
  have hint : IsIntegral k ω := Algebra.IsIntegral.isIntegral ω
  set L : IntermediateField k (SeparableClosure k) :=
    IntermediateField.adjoin k ({ω} : Set (SeparableClosure k)) with hL
  haveI : FiniteDimensional k L := IntermediateField.adjoin.finiteDimensional hint
  haveI : Algebra.IsSeparable k L :=
    Algebra.isSeparable_tower_bot_of_isSeparable k L (SeparableClosure k)
  haveI : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  haveI : Algebra.FinitePresentation k L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale k L := ⟨inferInstance, inferInstance⟩
  have hx := h (Opposite.op (CommAlgCat.FiniteEtale.of k L)) L.val
  have hω : ω ∈ L := IntermediateField.mem_adjoin_simple_self k ω
  exact AlgHom.congr_fun hx ⟨ω, hω⟩

instance : GaloisCategory (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ where
  hasFiberFunctor :=
    ⟨CommAlgCat.FiniteEtale.fiber k (SeparableClosure k), ⟨inferInstance⟩⟩

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
      simp
    rw [hdecomp]
    refine isOpen_iUnion fun x₀ => IsOpen.prod ?_ trivial
    rcases Set.eq_empty_or_nonempty {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k |
      σ • x₀ = y} with hemp | ⟨σ₀, hσ₀⟩
    · rw [hemp]; exact isOpen_empty
    · have hcoset : {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k | σ • x₀ = y} =
          (fun σ => σ₀⁻¹ * σ) ⁻¹' {σ | σ • x₀ = x₀} := by
        ext σ
        constructor
        · intro hσ
          show (σ₀⁻¹ * σ) • x₀ = x₀
          rw [mul_smul, hσ, ← hσ₀, inv_smul_smul]
        · intro hσ
          have : (σ₀⁻¹ * σ) • x₀ = x₀ := hσ
          rw [mul_smul] at this
          calc σ • x₀ = σ₀ • σ₀⁻¹ • σ • x₀ := (smul_inv_smul σ₀ _).symm
            _ = σ₀ • x₀ := by rw [this]
            _ = y := hσ₀
      rw [hcoset]
      exact (stabilizer_isOpen X x₀).preimage (continuous_const.mul continuous_id)
  non_trivial' σ h := eq_one_of_smul_eq σ h

end FundamentalGroup

/-! The Galois correspondence (leaf AG-GG-4a): `(FiniteEtale k)ᵒᵖ` is equivalent to
the category of finite discrete sets with continuous `Gal(k^sep/k)`-action. -/

section Correspondence

variable {k}

open PreGaloisCategory in
/-- The comparison isomorphism of a fundamental group with `Aut F`, bundled as a
continuous multiplicative equivalence. -/
noncomputable def toAutContinuousMulEquiv {C : Type*} [Category C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{u}) [FiberFunctor F] (G : Type*) [Group G]
    [∀ X, MulAction G (F.obj X)] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [IsFundamentalGroup F G] : G ≃ₜ* Aut F :=
  { toAutMulEquiv F G with
    continuous_toFun := (toAut_isHomeomorph F G).continuous
    continuous_invFun := by
      have h := (toAut_isHomeomorph F G).homeomorph.symm.continuous
      have heq : ⇑(toAutMulEquiv F G).symm =
          ⇑(toAut_isHomeomorph F G).homeomorph.symm := by
        funext a
        apply (toAutMulEquiv F G).injective
        rw [MulEquiv.apply_symm_apply]
        exact ((toAut_isHomeomorph F G).homeomorph.apply_symm_apply a).symm
      show Continuous ⇑(toAutMulEquiv F G).symm
      rw [heq]
      exact h }

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
