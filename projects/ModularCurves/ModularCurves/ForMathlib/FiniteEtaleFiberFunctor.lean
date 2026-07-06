import Mathlib.RingTheory.TensorProduct.Pi
import ModularCurves.ForMathlib.FiniteEtaleGalois

/-!
# The fiber functor on finite étale algebras is a Galois fiber functor

Mathlib provides the fiber functor `CommAlgCat.FiniteEtale.fiber k Ω :
(FiniteEtale k)ᵒᵖ ⥤ FintypeCat` (homs into a geometric point `Ω`), the factorisation
`fiberIsoBaseChangeFiber : fiber k Ω ≅ (baseChange k Ω).op ⋙ fiber Ω Ω`, and — for `Ω`
separably closed — the fact that `fiber Ω Ω` is an equivalence.  Consequently every
axiom of `CategoryTheory.PreGaloisCategory.FiberFunctor` for `fiber k (SeparableClosure k)`
reduces to an exactness property of the base change functor
`baseChange k Ω : FiniteEtale k ⥤ FiniteEtale Ω`, which is what this file proves:

* base change preserves the initial object (`Ω ⊗[k] k ≅ Ω`);
* base change preserves finite products (`Algebra.TensorProduct.piRight`);
* base change preserves the tensor-product pushouts;
* base change preserves monomorphisms (kernel-pair subalgebra + flatness);
* base change preserves `SingleObj`-shaped limits (fixed points commute with flat
  base change);
* the fiber functor reflects isomorphisms (counting via `natCard_algHom_sepClosure`).
-/

universe u

open CategoryTheory Limits CommAlgCat

open scoped TensorProduct

namespace ModularCurves

namespace FiniteEtaleGalois

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]

/-- The base change functor with both algebra universes pinned to `u`.  `baseChange`
has a free object-universe parameter which otherwise leaks into every statement. -/
noncomputable abbrev baseChangeU :
    CommAlgCat.FiniteEtale.{u} k ⥤ CommAlgCat.FiniteEtale.{u} Ω :=
  CommAlgCat.FiniteEtale.baseChange k Ω

/-! Base change preserves the initial object (leaf AG-GG-2a). -/

section Initial

/-- `Ω ⊗[k] k` is the initial finite étale `Ω`-algebra. -/
noncomputable def baseChangeInitialIso :
    (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k k) ≅
      CommAlgCat.FiniteEtale.of Ω Ω :=
  CommAlgCat.FiniteEtale.isoMk (Algebra.TensorProduct.rid k Ω Ω)

/-- `FiniteEtale.of k k` is initial. -/
noncomputable def isInitialOfSelf : IsInitial (CommAlgCat.FiniteEtale.of k k) :=
  haveI : ∀ A : CommAlgCat.FiniteEtale.{u} k,
      Unique (CommAlgCat.FiniteEtale.of k k ⟶ A) := fun _ =>
    ⟨⟨Nonempty.some inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
  IsInitial.ofUnique _

lemma preservesInitial_baseChange :
    PreservesColimit (Functor.empty.{0} (CommAlgCat.FiniteEtale.{u} k))
      (baseChangeU k Ω) := by
  refine preservesInitial_of_iso _ ?_
  refine (initialIsoIsInitial (isInitialOfSelf Ω)).trans ?_
  refine (baseChangeInitialIso k Ω).symm.trans ?_
  exact ((baseChangeU k Ω).mapIso
    (initialIsoIsInitial (isInitialOfSelf k))).symm

lemma preservesColimitsOfShapePEmpty_baseChange :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (baseChangeU k Ω) :=
  haveI := preservesInitial_baseChange k Ω
  preservesColimitsOfShape_pempty_of_preservesInitial (baseChangeU k Ω)

end Initial

/-! Base change preserves finite products (leaf AG-GG-2c): `Ω ⊗[k] ∏ᵢ Aᵢ ≅ ∏ᵢ (Ω ⊗[k] Aᵢ)`
via `Algebra.TensorProduct.piRight`. -/

section Products

variable {k Ω}

/-- Evaluating a base-changed product at a coordinate is the `piRight` coordinate. -/
lemma map_eval_eq_piRight_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) (i : ι) (x : Ω ⊗[k] (Π j, A j)) :
    Algebra.TensorProduct.map (AlgHom.id Ω Ω)
        (Pi.evalAlgHom k (fun j => (A j : Type u)) i) x =
      Algebra.TensorProduct.piRight k Ω Ω (fun j => (A j : Type u)) x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul ω f => simp [Algebra.TensorProduct.piRight_tmul]
  | add a b ha hb => simp [map_add, ha, hb]

/-- Two maps into a base-changed product agreeing on all coordinate projections are
equal. -/
lemma baseChangePi_hom_ext {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) {W : CommAlgCat.FiniteEtale.{u} Ω}
    {u v : W ⟶ (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k (Π j, A j))}
    (h : ∀ i, u ≫ (baseChangeU k Ω).map ((productFan A).π.app ⟨i⟩) =
      v ≫ (baseChangeU k Ω).map ((productFan A).π.app ⟨i⟩)) : u = v := by
  ext x
  apply (Algebra.TensorProduct.piRight k Ω Ω (fun j => (A j : Type u))).injective
  refine funext fun i => ?_
  rw [← map_eval_eq_piRight_apply A i, ← map_eval_eq_piRight_apply A i]
  exact congrArg (fun q => q.hom.hom x) (h i)

/-- The base change of the product fan is a limit fan: `Ω ⊗[k] ∏ᵢ Aᵢ` is the product
of the `Ω ⊗[k] Aᵢ`, via `piRight`. -/
noncomputable def isLimitMapConeProductFan {ι : Type} [Finite ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) :
    IsLimit ((baseChangeU k Ω).mapCone (productFan A)) := by
  haveI := Fintype.ofFinite ι
  haveI := Classical.decEq ι
  have hfac : ∀ (s : Cone (Discrete.functor A ⋙ baseChangeU k Ω)) (i : ι),
      (ObjectProperty.homMk (CommAlgCat.ofHom
        ((Algebra.TensorProduct.piRight k Ω Ω
            (fun j => (A j : Type u))).symm.toAlgHom.comp
          (AlgHom.pi (fun i => (s.π.app ⟨i⟩).hom.hom)))) :
          s.pt ⟶ (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k (Π j, A j))) ≫
        ((baseChangeU k Ω).mapCone (productFan A)).π.app ⟨i⟩ = s.π.app ⟨i⟩ := by
    intro s i
    ext x
    show Algebra.TensorProduct.map (AlgHom.id Ω Ω)
        (Pi.evalAlgHom k (fun j => (A j : Type u)) i)
        ((Algebra.TensorProduct.piRight k Ω Ω _).symm
          (fun j => (s.π.app ⟨j⟩).hom.hom x)) =
      (s.π.app ⟨i⟩).hom.hom x
    rw [map_eval_eq_piRight_apply, AlgEquiv.apply_symm_apply]
  refine IsLimit.mk
    (fun s => ObjectProperty.homMk (CommAlgCat.ofHom
      ((Algebra.TensorProduct.piRight k Ω Ω
          (fun j => (A j : Type u))).symm.toAlgHom.comp
        (AlgHom.pi (fun i => (s.π.app ⟨i⟩).hom.hom)))))
    (fun s => by rintro ⟨i⟩; exact hfac s i)
    (fun s m hm => baseChangePi_hom_ext A fun i => (hm ⟨i⟩).trans (hfac s i).symm)

lemma preservesLimitsOfShapeDiscrete_baseChange (ι : Type) [Finite ι] :
    PreservesLimitsOfShape (Discrete ι) (baseChangeU k Ω) where
  preservesLimit {K} :=
    haveI : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) (baseChangeU k Ω) :=
      preservesLimit_of_preserves_limit_cone
        (productFanIsLimit (K.obj ∘ Discrete.mk))
        (isLimitMapConeProductFan (K.obj ∘ Discrete.mk))
    preservesLimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm

end Products

/-! Base change preserves the tensor-product pushouts (leaf AG-GG-2b):
`Ω ⊗[k] (B ⊗[A] C)` is the pushout of `Ω ⊗[k] B ← Ω ⊗[k] A → Ω ⊗[k] C`. -/

section Pushouts

variable {k Ω}

variable {X Y Z : CommAlgCat.FiniteEtale.{u} k} (f : X ⟶ Y) (g : X ⟶ Z)

/-- The base change of the tensor-product pushout cocone is a colimit cocone. -/
noncomputable def isColimitMapCoconeSpanPushout :
    IsColimit ((baseChangeU k Ω).mapCocone (spanPushoutCocone f g)) := by
  letI : Algebra X.obj Y.obj := f.hom.hom.toRingHom.toAlgebra
  letI : Algebra X.obj Z.obj := g.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower k X.obj Y.obj :=
    IsScalarTower.of_algebraMap_eq fun r => (f.hom.hom.commutes r).symm
  haveI : IsScalarTower k X.obj Z.obj :=
    IsScalarTower.of_algebraMap_eq fun r => (g.hom.hom.commutes r).symm
  refine (isColimitMapCoconePushoutCoconeEquiv (baseChangeU k Ω) _).symm ?_
  refine PushoutCocone.isColimitAux' _ fun s => ?_
  letI : Algebra k s.pt.obj :=
    ((algebraMap Ω s.pt.obj).comp (algebraMap k Ω)).toAlgebra
  haveI : IsScalarTower k Ω s.pt.obj := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hinl : (Ω ⊗[k] (Y.obj : Type u)) →ₐ[Ω] s.pt.obj := s.inl.hom.hom
  have hinr : (Ω ⊗[k] (Z.obj : Type u)) →ₐ[Ω] s.pt.obj := s.inr.hom.hom
  set β : (Y.obj : Type u) →ₐ[k] s.pt.obj :=
    ((s.inl.hom.hom : (Ω ⊗[k] (Y.obj : Type u)) →ₐ[Ω] s.pt.obj).restrictScalars k).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := Ω)) with hβ
  set γ : (Z.obj : Type u) →ₐ[k] s.pt.obj :=
    ((s.inr.hom.hom : (Ω ⊗[k] (Z.obj : Type u)) →ₐ[Ω] s.pt.obj).restrictScalars k).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := Ω)) with hγ
  have hβ_apply : ∀ y : Y.obj, β y = s.inl.hom.hom ((1 : Ω) ⊗ₜ[k] y) := fun _ => rfl
  have hγ_apply : ∀ z : Z.obj, γ z = s.inr.hom.hom ((1 : Ω) ⊗ₜ[k] z) := fun _ => rfl
  have hcond : ∀ a : X.obj, β (f.hom.hom a) = γ (g.hom.hom a) := by
    intro a
    have h := congrArg (fun q => q.hom.hom ((1 : Ω) ⊗ₜ[k] a)) s.condition
    exact h
  letI : Algebra X.obj s.pt.obj := (β.comp f.hom.hom).toRingHom.toAlgebra
  haveI : IsScalarTower k X.obj s.pt.obj :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap k s.pt.obj r = β (f.hom.hom (algebraMap k X.obj r))
      rw [f.hom.hom.commutes r, β.commutes r]
  let f' : (Y.obj : Type u) →ₐ[X.obj] s.pt.obj := { β with commutes' := fun a => rfl }
  let g' : (Z.obj : Type u) →ₐ[X.obj] s.pt.obj :=
    { γ with commutes' := fun a => (hcond a).symm }
  set d0 : (↑Y.obj ⊗[↑X.obj] ↑Z.obj) →ₐ[k] s.pt.obj :=
    (Algebra.TensorProduct.productMap f' g').restrictScalars k with hd0
  have hd0_left : ∀ y : Y.obj, d0 (y ⊗ₜ 1) = β y := by
    intro y
    show Algebra.TensorProduct.productMap f' g' (y ⊗ₜ 1) = β y
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  have hd0_right : ∀ z : Z.obj, d0 ((1 : Y.obj) ⊗ₜ z) = γ z := by
    intro z
    show Algebra.TensorProduct.productMap f' g' (1 ⊗ₜ z) = γ z
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl
  set desc : (Ω ⊗[k] (↑Y.obj ⊗[↑X.obj] ↑Z.obj)) →ₐ[Ω] s.pt.obj :=
    Algebra.TensorProduct.liftEquivRight k Ω (↑Y.obj ⊗[↑X.obj] ↑Z.obj) s.pt.obj d0
    with hdesc
  have hdesc_tmul : ∀ (ω : Ω) (w : ↑Y.obj ⊗[↑X.obj] ↑Z.obj),
      desc (ω ⊗ₜ[k] w) = algebraMap Ω s.pt.obj ω * d0 w := by
    intro ω w
    simp [hdesc, Algebra.TensorProduct.liftEquivRight, Algebra.ofId_apply]
  have hdesc_left : ∀ (ω : Ω) (y : Y.obj),
      desc (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) = s.inl.hom.hom (ω ⊗ₜ[k] y) := by
    intro ω y
    rw [hdesc_tmul, hd0_left]
    have h3 : (ω ⊗ₜ[k] y : Ω ⊗[k] Y.obj) =
        (ω ⊗ₜ[k] (1 : Y.obj)) * ((1 : Ω) ⊗ₜ[k] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hβ_apply, h3, map_mul]
    congr 1
    exact ((s.inl.hom.hom : (Ω ⊗[k] (Y.obj : Type u)) →ₐ[Ω] s.pt.obj).commutes ω).symm
  have hdesc_right : ∀ (ω : Ω) (z : Z.obj),
      desc (ω ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z)) = s.inr.hom.hom (ω ⊗ₜ[k] z) := by
    intro ω z
    rw [hdesc_tmul, hd0_right]
    have h3 : (ω ⊗ₜ[k] z : Ω ⊗[k] Z.obj) =
        (ω ⊗ₜ[k] (1 : Z.obj)) * ((1 : Ω) ⊗ₜ[k] z) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hγ_apply, h3, map_mul]
    congr 1
    exact ((s.inr.hom.hom : (Ω ⊗[k] (Z.obj : Type u)) →ₐ[Ω] s.pt.obj).commutes ω).symm
  refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom desc), ?_, ?_, ?_⟩
  · ext x
    show desc (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      Algebra.TensorProduct.includeLeft x) = s.inl.hom.hom x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul ω y =>
      rw [show Algebra.TensorProduct.map (AlgHom.id Ω Ω)
          (Algebra.TensorProduct.includeLeft (R := ↑X.obj) (S := k)) (ω ⊗ₜ[k] y) =
          ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj)) from rfl]
      exact hdesc_left ω y
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  · ext x
    show desc (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      ((Algebra.TensorProduct.includeRight (R := ↑X.obj)).restrictScalars k) x) =
      s.inr.hom.hom x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul ω z =>
      rw [show Algebra.TensorProduct.map (AlgHom.id Ω Ω)
          ((Algebra.TensorProduct.includeRight (R := ↑X.obj)).restrictScalars k)
          (ω ⊗ₜ[k] z) = ω ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z) from rfl]
      exact hdesc_right ω z
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  · intro m hm1 hm2
    have hml : ∀ (ω : Ω) (y : Y.obj), m.hom.hom (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) =
        s.inl.hom.hom (ω ⊗ₜ[k] y) :=
      fun ω y => congrArg (fun q => q.hom.hom (ω ⊗ₜ[k] y)) hm1
    have hmr : ∀ (ω : Ω) (z : Z.obj), m.hom.hom (ω ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z)) =
        s.inr.hom.hom (ω ⊗ₜ[k] z) :=
      fun ω z => congrArg (fun q => q.hom.hom (ω ⊗ₜ[k] z)) hm2
    ext x
    show m.hom.hom x = desc x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul ω w =>
      induction w using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | tmul y z =>
        have hsplit : (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] z) : Ω ⊗[k] (↑Y.obj ⊗[↑X.obj] ↑Z.obj)) =
            (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) *
              ((1 : Ω) ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]
        rw [hsplit, map_mul, map_mul, hml ω y, hmr 1 z, hdesc_left ω y, hdesc_right 1 z]
      | add w₁ w₂ ih₁ ih₂ =>
        rw [TensorProduct.tmul_add, map_add, map_add, ih₁, ih₂]
    | add a b ha hb => rw [map_add, map_add, ha, hb]

lemma preservesColimitsOfShapeWalkingSpan_baseChange :
    PreservesColimitsOfShape WalkingSpan (baseChangeU k Ω) where
  preservesColimit {K} :=
    haveI : PreservesColimit (span (K.map WalkingSpan.Hom.fst)
        (K.map WalkingSpan.Hom.snd)) (baseChangeU k Ω) :=
      preservesColimit_of_preserves_colimit_cocone
        (spanPushoutCoconeIsColimit _ _) (isColimitMapCoconeSpanPushout _ _)
    preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm

end Pushouts

end FiniteEtaleGalois

end ModularCurves
