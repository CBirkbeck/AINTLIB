/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
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

set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency.types false in
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
  letI : Algebra k (((baseChangeU k Ω).obj Y).obj : Type u) :=
    inferInstanceAs (Algebra k (Ω ⊗[k] (Y.obj : Type u)))
  letI : Algebra k (((baseChangeU k Ω).obj Z).obj : Type u) :=
    inferInstanceAs (Algebra k (Ω ⊗[k] (Z.obj : Type u)))
  haveI : IsScalarTower k Ω (((baseChangeU k Ω).obj Y).obj : Type u) :=
    inferInstanceAs (IsScalarTower k Ω (Ω ⊗[k] (Y.obj : Type u)))
  haveI : IsScalarTower k Ω (((baseChangeU k Ω).obj Z).obj : Type u) :=
    inferInstanceAs (IsScalarTower k Ω (Ω ⊗[k] (Z.obj : Type u)))
  set β : (Y.obj : Type u) →ₐ[k] s.pt.obj :=
    (s.inl.hom.hom.restrictScalars k).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := Ω)) with hβ
  set γ : (Z.obj : Type u) →ₐ[k] s.pt.obj :=
    (s.inr.hom.hom.restrictScalars k).comp
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
    rw [hdesc_tmul, hd0_left, hβ_apply]
    calc algebraMap Ω s.pt.obj ω * s.inl.hom.hom ((1 : Ω) ⊗ₜ[k] y)
        = s.inl.hom.hom (ω ⊗ₜ[k] (1 : Y.obj)) * s.inl.hom.hom ((1 : Ω) ⊗ₜ[k] y) :=
          congrArg (· * s.inl.hom.hom ((1 : Ω) ⊗ₜ[k] y))
            (s.inl.hom.hom.commutes ω).symm
      _ = s.inl.hom.hom ((ω ⊗ₜ[k] (1 : Y.obj)) * ((1 : Ω) ⊗ₜ[k] y)) :=
          (map_mul s.inl.hom.hom _ _).symm
      _ = s.inl.hom.hom (ω ⊗ₜ[k] y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hdesc_right : ∀ (ω : Ω) (z : Z.obj),
      desc (ω ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z)) = s.inr.hom.hom (ω ⊗ₜ[k] z) := by
    intro ω z
    rw [hdesc_tmul, hd0_right, hγ_apply]
    calc algebraMap Ω s.pt.obj ω * s.inr.hom.hom ((1 : Ω) ⊗ₜ[k] z)
        = s.inr.hom.hom (ω ⊗ₜ[k] (1 : Z.obj)) * s.inr.hom.hom ((1 : Ω) ⊗ₜ[k] z) :=
          congrArg (· * s.inr.hom.hom ((1 : Ω) ⊗ₜ[k] z))
            (s.inr.hom.hom.commutes ω).symm
      _ = s.inr.hom.hom ((ω ⊗ₜ[k] (1 : Z.obj)) * ((1 : Ω) ⊗ₜ[k] z)) :=
          (map_mul s.inr.hom.hom _ _).symm
      _ = s.inr.hom.hom (ω ⊗ₜ[k] z) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom desc), ?_, ?_, ?_⟩
  · ext x
    show desc (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      Algebra.TensorProduct.includeLeft x) = s.inl.hom.hom x
    induction x using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg desc (map_zero _)).trans (map_zero desc)).trans
        (map_zero s.inl.hom.hom).symm
    | tmul ω y =>
      rw [show Algebra.TensorProduct.map (AlgHom.id Ω Ω)
          (Algebra.TensorProduct.includeLeft (R := ↑X.obj) (S := k)) (ω ⊗ₜ[k] y) =
          ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj)) from rfl]
      exact hdesc_left ω y
    | add a b ha hb =>
      exact ((congrArg desc (map_add _ a b)).trans (map_add desc _ _)).trans
        ((congrArg₂ (· + ·) ha hb).trans (map_add s.inl.hom.hom a b).symm)
  · ext x
    show desc (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      ((Algebra.TensorProduct.includeRight (R := ↑X.obj)).restrictScalars k) x) =
      s.inr.hom.hom x
    induction x using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg desc (map_zero _)).trans (map_zero desc)).trans
        (map_zero s.inr.hom.hom).symm
    | tmul ω z =>
      rw [show Algebra.TensorProduct.map (AlgHom.id Ω Ω)
          ((Algebra.TensorProduct.includeRight (R := ↑X.obj)).restrictScalars k)
          (ω ⊗ₜ[k] z) = ω ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z) from rfl]
      exact hdesc_right ω z
    | add a b ha hb =>
      exact ((congrArg desc (map_add _ a b)).trans (map_add desc _ _)).trans
        ((congrArg₂ (· + ·) ha hb).trans (map_add s.inr.hom.hom a b).symm)
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
    | zero => exact (map_zero m.hom.hom).trans (map_zero desc).symm
    | tmul ω w =>
      induction w using TensorProduct.induction_on with
      | zero =>
        exact ((congrArg m.hom.hom (TensorProduct.tmul_zero _ ω)).trans
          ((map_zero m.hom.hom).trans (map_zero desc).symm)).trans
          (congrArg desc (TensorProduct.tmul_zero _ ω)).symm
      | tmul y z =>
        have hsplit : (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] z) : Ω ⊗[k] (↑Y.obj ⊗[↑X.obj] ↑Z.obj)) =
            (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) *
              ((1 : Ω) ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]
        calc m.hom.hom (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] z))
            = m.hom.hom ((ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) *
                ((1 : Ω) ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z))) :=
              congrArg m.hom.hom hsplit
          _ = m.hom.hom (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) *
              m.hom.hom ((1 : Ω) ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z)) :=
              map_mul m.hom.hom _ _
          _ = s.inl.hom.hom (ω ⊗ₜ[k] y) * s.inr.hom.hom ((1 : Ω) ⊗ₜ[k] z) :=
              congrArg₂ (· * ·) (hml ω y) (hmr 1 z)
          _ = desc (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) *
              desc ((1 : Ω) ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z)) :=
              (congrArg₂ (· * ·) (hdesc_left ω y) (hdesc_right 1 z)).symm
          _ = desc ((ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] (1 : Z.obj))) *
              ((1 : Ω) ⊗ₜ[k] ((1 : Y.obj) ⊗ₜ[↑X.obj] z))) :=
              (map_mul desc _ _).symm
          _ = desc (ω ⊗ₜ[k] (y ⊗ₜ[↑X.obj] z)) := (congrArg desc hsplit).symm
      | add w₁ w₂ ih₁ ih₂ =>
        exact ((congrArg m.hom.hom (TensorProduct.tmul_add ω w₁ w₂)).trans
          ((map_add m.hom.hom _ _).trans ((congrArg₂ (· + ·) ih₁ ih₂).trans
            (map_add desc _ _).symm))).trans
          (congrArg desc (TensorProduct.tmul_add ω w₁ w₂)).symm
    | add a b ha hb =>
      exact (map_add m.hom.hom a b).trans
        ((congrArg₂ (· + ·) ha hb).trans (map_add desc a b).symm)

lemma preservesColimitsOfShapeWalkingSpan_baseChange :
    PreservesColimitsOfShape WalkingSpan (baseChangeU k Ω) where
  preservesColimit {K} :=
    haveI : PreservesColimit (span (K.map WalkingSpan.Hom.fst)
        (K.map WalkingSpan.Hom.snd)) (baseChangeU k Ω) :=
      preservesColimit_of_preserves_colimit_cocone
        (spanPushoutCoconeIsColimit _ _) (isColimitMapCoconeSpanPushout _ _)
    preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm

end Pushouts

/-! Base change preserves monomorphisms (leaf AG-GG-2d): a mono of finite étale
`k`-algebras is injective — the kernel pair is a finite étale subalgebra of the square,
and its two projections are equalised — and injectivity survives flat base change. -/

section Monos

variable {k Ω}

/-- Monomorphisms of finite étale algebras over a field are injective. -/
theorem injective_of_mono {A B : CommAlgCat.FiniteEtale.{u} k} (j : A ⟶ B) [Mono j] :
    Function.Injective j.hom.hom := by
  intro x y hxy
  set P : Subalgebra k (Π _ : Fin 2, (A.obj : Type u)) :=
    AlgHom.equalizer
      (j.hom.hom.comp (Pi.evalAlgHom k (fun _ : Fin 2 => (A.obj : Type u)) 0))
      (j.hom.hom.comp (Pi.evalAlgHom k (fun _ : Fin 2 => (A.obj : Type u)) 1)) with hP
  haveI : Algebra.Etale k P := etale_subalgebra P
  haveI : Module.Finite k P := inferInstanceAs (Module.Finite k P.toSubmodule)
  set U : CommAlgCat.FiniteEtale.of k P ⟶ A := ObjectProperty.homMk (CommAlgCat.ofHom
    ((Pi.evalAlgHom k (fun _ : Fin 2 => (A.obj : Type u)) 0).comp P.val)) with hU
  set V : CommAlgCat.FiniteEtale.of k P ⟶ A := ObjectProperty.homMk (CommAlgCat.ofHom
    ((Pi.evalAlgHom k (fun _ : Fin 2 => (A.obj : Type u)) 1).comp P.val)) with hV
  have hUV : U ≫ j = V ≫ j := by
    ext p
    exact p.2
  have hUV' : U = V := (cancel_mono j).mp hUV
  have hmem : (![x, y] : Fin 2 → (A.obj : Type u)) ∈ P := by
    show j.hom.hom (![x, y] 0) = j.hom.hom (![x, y] 1)
    simpa using hxy
  have h := congrArg (fun q : CommAlgCat.FiniteEtale.of k P ⟶ A =>
    q.hom.hom ⟨![x, y], hmem⟩) hUV'
  exact h

/-- Base change preserves monomorphisms of finite étale algebras. -/
lemma preservesMonomorphisms_baseChange :
    (baseChangeU k Ω).PreservesMonomorphisms where
  preserves {A B} j hj := by
    have hinj : Function.Injective j.hom.hom := injective_of_mono j
    have hinj2 : Function.Injective
        (((baseChangeU k Ω).map j).hom.hom : Ω ⊗[k] (A.obj : Type u) → Ω ⊗[k] B.obj) :=
      Module.Flat.lTensor_preserves_injective_linearMap
        (M := Ω) j.hom.hom.toLinearMap hinj
    have hmono : Mono ((ObjectProperty.ι (CommAlgCat.finiteEtale Ω)).map
        ((baseChangeU k Ω).map j)) :=
      ConcreteCategory.mono_of_injective _ hinj2
    exact (ObjectProperty.ι (CommAlgCat.finiteEtale Ω)).mono_of_mono_map hmono

end Monos

/-! The fiber functor reflects isomorphisms (leaf AG-GG-2f): counting.  An algebra map
inducing a bijection on `k̄`-points has zero kernel (else points would factor through a
smaller quotient) and full range (else points would be determined by a smaller
subalgebra), by `natCard_algHom_sepClosure` on both sides. -/

section ReflectsIso

variable {k}

/-- Hom-sets into the separable closure are finite. -/
lemma finite_algHom_sepClosure (W : Type u) [CommRing W] [Algebra k W]
    [Module.Finite k W] [Algebra.Etale k W] :
    Finite (W →ₐ[k] SeparableClosure k) := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact Finite.of_fintype _
  · refine Nat.finite_of_card_ne_zero ?_
    rw [natCard_algHom_sepClosure]
    have : 0 < Module.finrank k W := Module.finrank_pos
    omega

/-- An algebra map inducing a bijection on separable-closure points has trivial kernel:
else the points would factor through the strictly smaller quotient by the kernel. -/
lemma ker_eq_bot_of_bijective_comp_sepClosure {B C : Type u} [CommRing B] [Algebra k B]
    [Module.Finite k B] [Algebra.Etale k B] [CommRing C] [Algebra k C] (φ : B →ₐ[k] C)
    (hbij : Function.Bijective (fun g : C →ₐ[k] SeparableClosure k => g.comp φ)) :
    RingHom.ker φ = ⊥ := by
  set I := RingHom.ker φ with hI
  haveI : Algebra.Etale k (B ⧸ I) := etale_quotient I
  haveI : Module.Finite k (B ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I).toLinearMap
      Ideal.Quotient.mk_surjective
  have hcompinj : Function.Injective
      (fun h : (B ⧸ I) →ₐ[k] SeparableClosure k =>
        h.comp (Ideal.Quotient.mkₐ k I)) := by
    intro h₁ h₂ hh
    refine AlgHom.ext fun b => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact AlgHom.congr_fun hh x
  have hcompsurj : Function.Surjective
      (fun h : (B ⧸ I) →ₐ[k] SeparableClosure k =>
        h.comp (Ideal.Quotient.mkₐ k I)) := by
    intro h
    obtain ⟨g, hg⟩ := hbij.2 h
    have hkill : ∀ a ∈ I, h a = 0 := by
      intro a ha
      have h1 : φ a = 0 := ha
      calc h a = g (φ a) := (AlgHom.congr_fun hg a).symm
        _ = g 0 := by rw [h1]
        _ = 0 := map_zero g
    refine ⟨Ideal.Quotient.liftₐ I h hkill, ?_⟩
    refine AlgHom.ext fun a => ?_
    exact Ideal.Quotient.lift_mk I h.toRingHom hkill
  have hcard : Nat.card ((B ⧸ I) →ₐ[k] SeparableClosure k) =
      Nat.card (B →ₐ[k] SeparableClosure k) :=
    Nat.card_congr (Equiv.ofBijective _ ⟨hcompinj, hcompsurj⟩)
  rw [natCard_algHom_sepClosure, natCard_algHom_sepClosure] at hcard
  have hmkinj : Function.Injective (Ideal.Quotient.mkₐ k I).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcard.symm).mpr
      Ideal.Quotient.mk_surjective
  have : RingHom.ker (Ideal.Quotient.mk I) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hmkinj
  rwa [Ideal.mk_ker] at this

/-- An algebra map inducing a bijection on separable-closure points has full range:
else the points would be determined by the strictly smaller subalgebra `φ.range`. -/
lemma range_eq_top_of_bijective_comp_sepClosure {B C : Type u} [CommRing B] [Algebra k B]
    [CommRing C] [Algebra k C] [Module.Finite k C] [Algebra.Etale k C] (φ : B →ₐ[k] C)
    (hbij : Function.Bijective (fun g : C →ₐ[k] SeparableClosure k => g.comp φ)) :
    φ.range = ⊤ := by
  by_contra hne
  haveI : Algebra.Etale k (φ.range : Subalgebra k C) := etale_subalgebra _
  haveI : Module.Finite k (φ.range : Subalgebra k C) :=
    inferInstanceAs (Module.Finite k φ.range.toSubmodule)
  haveI : Finite ((φ.range : Subalgebra k C) →ₐ[k] SeparableClosure k) :=
    finite_algHom_sepClosure _
  have hres_inj : Function.Injective
      (fun g : C →ₐ[k] SeparableClosure k => g.comp φ.range.val) := by
    intro g₁ g₂ hg
    apply hbij.1
    refine AlgHom.ext fun b => ?_
    exact AlgHom.congr_fun hg ⟨φ b, ⟨b, rfl⟩⟩
  have hle := Nat.card_le_card_of_injective _ hres_inj
  rw [natCard_algHom_sepClosure, natCard_algHom_sepClosure] at hle
  have hlt : Module.finrank k (φ.range : Subalgebra k C) < Module.finrank k C := by
    have hsub : φ.range.toSubmodule ≠ ⊤ := fun h =>
      hne (Subalgebra.toSubmodule_injective (by simpa using h))
    exact Submodule.finrank_lt hsub
  omega

variable (k)

/-- The fiber functor of `FiniteEtale k` at the separable closure reflects
isomorphisms. -/
lemma reflectsIsomorphisms_fiber :
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}).ReflectsIsomorphisms := by
  constructor
  intro X Y ψ hψ
  set φ : (Y.unop.obj : Type u) →ₐ[k] (X.unop.obj : Type u) := ψ.unop.hom.hom with hφ
  have hbij : Function.Bijective
      (fun g : (X.unop.obj : Type u) →ₐ[k] SeparableClosure k => g.comp φ) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).map ψ)
  -- Step 1: φ is injective (zero kernel); Step 2: φ is surjective (full range).
  have hker : RingHom.ker φ = ⊥ := ker_eq_bot_of_bijective_comp_sepClosure φ hbij
  have hrange : φ.range = ⊤ := range_eq_top_of_bijective_comp_sepClosure φ hbij
  -- Assemble the isomorphism.
  have hφbij : Function.Bijective φ :=
    ⟨(RingHom.injective_iff_ker_eq_bot φ.toRingHom).mpr hker, fun a => by
      have : a ∈ φ.range := hrange ▸ Algebra.mem_top
      exact this⟩
  set e := AlgEquiv.ofBijective φ hφbij with he
  have hiso : IsIso ψ.unop := by
    refine ⟨⟨ObjectProperty.homMk (CommAlgCat.ofHom (e.symm : (X.unop.obj : Type u) ≃ₐ[k]
      (Y.unop.obj : Type u)).toAlgHom), ?_, ?_⟩⟩
    · ext b
      exact e.symm_apply_apply b
    · ext a
      exact e.apply_symm_apply a
  exact (isIso_unop_iff ψ).mp hiso

end ReflectsIso

/-! Base change preserves fixed points of finite monoid actions (leaf AG-GG-2e):
`Ω ⊗[k] A^H ≅ (Ω ⊗[k] A)^H`.  The fixed points are the equaliser of the action map
against the diagonal, and flat base change commutes with equalisers
(`Module.Flat.eqLocus_lTensor_eq`). -/

section FixedPointsBaseChange

variable {k Ω}

variable {H : Type u} [Monoid H] [Finite H]
  (F : SingleObj H ⥤ CommAlgCat.FiniteEtale.{u} k)

/-- The action map `a ↦ (h • a)ₕ`. -/
private noncomputable def actionDelta :
    (F.obj (SingleObj.star H) : Type u) →ₗ[k]
      (H → (F.obj (SingleObj.star H) : Type u)) :=
  LinearMap.pi fun h =>
    ((F.map (show SingleObj.star H ⟶ SingleObj.star H from h)).hom.hom).toLinearMap

/-- The diagonal map `a ↦ (a)ₕ`. -/
private noncomputable def actionDiag :
    (F.obj (SingleObj.star H) : Type u) →ₗ[k]
      (H → (F.obj (SingleObj.star H) : Type u)) :=
  LinearMap.pi fun _ => LinearMap.id

omit [Finite H] in
private lemma eqLocus_actionDelta :
    LinearMap.eqLocus (actionDelta F) (actionDiag F) =
      Subalgebra.toSubmodule (actionFixedPoints F) := by
  ext a
  show actionDelta F a = actionDiag F a ↔ _
  constructor
  · intro ha h
    exact congrFun ha h
  · intro ha
    exact funext fun h => ha h

/-- The comparison map `Ω ⊗[k] A^H →ₐ[Ω] (Ω ⊗[k] A)^H`. -/
private noncomputable def fixedPointsCompare :
    (Ω ⊗[k] ((actionFixedPoints F : Subalgebra k _) : Type u)) →ₐ[Ω]
      ((actionFixedPoints (F ⋙ baseChangeU k Ω) : Subalgebra Ω _) : Type u) :=
  AlgHom.codRestrict
    (Algebra.TensorProduct.map (AlgHom.id Ω Ω) (actionFixedPoints F).val)
    (actionFixedPoints (F ⋙ baseChangeU k Ω))
    (by
      intro x h
      induction x using TensorProduct.induction_on with
      | zero =>
        exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
      | tmul ω a => exact congrArg (ω ⊗ₜ[k] ·) (a.2 h)
      | add x y hx hy =>
        exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)))

/-- The fixed points of the base-changed action are the base change of the fixed
points. -/
private noncomputable def fixedPointsCompareEquiv :
    (Ω ⊗[k] ((actionFixedPoints F : Subalgebra k _) : Type u)) ≃ₐ[Ω]
      ((actionFixedPoints (F ⋙ baseChangeU k Ω) : Subalgebra Ω _) : Type u) :=
  AlgEquiv.ofBijective (fixedPointsCompare F) (by
    constructor
    · have hval : Function.Injective
          (Algebra.TensorProduct.map (AlgHom.id Ω Ω) (actionFixedPoints F).val) :=
        Module.Flat.lTensor_preserves_injective_linearMap (M := Ω)
          (actionFixedPoints F).val.toLinearMap Subtype.val_injective
      intro x y hxy
      exact hval (congrArg Subtype.val hxy)
    · haveI := Fintype.ofFinite H
      haveI := Classical.decEq H
      have hcomp1 : ∀ (x : Ω ⊗[k] (F.obj (SingleObj.star H) : Type u)) (h : H),
          TensorProduct.piRightHom k Ω Ω
          (fun _ : H => (F.obj (SingleObj.star H) : Type u))
          (TensorProduct.AlgebraTensorModule.lTensor Ω Ω (actionDelta F) x) h =
          ((F ⋙ baseChangeU k Ω).map
            (show SingleObj.star H ⟶ SingleObj.star H from h)).hom.hom x := by
        intro x h
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]; rfl
        | tmul ω a => rfl
        | add a b ha hb =>
          exact (congrArg (fun t => TensorProduct.piRightHom k Ω Ω
              (fun _ : H => (F.obj (SingleObj.star H) : Type u)) t h)
              (map_add _ a b)).trans
            (((congrFun (map_add (TensorProduct.piRightHom k Ω Ω
              (fun _ : H => (F.obj (SingleObj.star H) : Type u))) _ _) h).trans
              (congrArg₂ (· + ·) ha hb)).trans (map_add _ a b).symm)
      have hcomp2 : ∀ (x : Ω ⊗[k] (F.obj (SingleObj.star H) : Type u)) (h : H),
          TensorProduct.piRightHom k Ω Ω
          (fun _ : H => (F.obj (SingleObj.star H) : Type u))
          (TensorProduct.AlgebraTensorModule.lTensor Ω Ω (actionDiag F) x) h = x := by
        intro x h
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero]; rfl
        | tmul ω a => rfl
        | add a b ha hb =>
          exact (congrArg (fun t => TensorProduct.piRightHom k Ω Ω
              (fun _ : H => (F.obj (SingleObj.star H) : Type u)) t h)
              (map_add _ a b)).trans
            ((congrFun (map_add (TensorProduct.piRightHom k Ω Ω
              (fun _ : H => (F.obj (SingleObj.star H) : Type u))) _ _) h).trans
              (congrArg₂ (· + ·) ha hb))
      rintro ⟨x, hx⟩
      have hmem : x ∈ LinearMap.eqLocus
          (TensorProduct.AlgebraTensorModule.lTensor Ω Ω (actionDelta F))
          (TensorProduct.AlgebraTensorModule.lTensor Ω Ω (actionDiag F)) := by
        show TensorProduct.AlgebraTensorModule.lTensor Ω Ω (actionDelta F) x =
          TensorProduct.AlgebraTensorModule.lTensor Ω Ω (actionDiag F) x
        apply (TensorProduct.piRight k Ω Ω
          (fun _ : H => (F.obj (SingleObj.star H) : Type u))).injective
        refine funext fun h => ?_
        exact (hcomp1 x h).trans ((hx h).trans (hcomp2 x h).symm)
      rw [Module.Flat.eqLocus_lTensor_eq, eqLocus_actionDelta] at hmem
      obtain ⟨y, hy⟩ := hmem
      exact ⟨y, Subtype.ext hy⟩)

/-- The base change of the fixed-point cone is a limit cone. -/
noncomputable def isLimitMapConeFixedPoints :
    IsLimit ((baseChangeU k Ω).mapCone (actionFixedPointsCone F)) := by
  refine IsLimit.ofIsoLimit (actionFixedPointsConeIsLimit (F ⋙ baseChangeU k Ω)) ?_
  refine Cone.ext (CommAlgCat.FiniteEtale.isoMk (fixedPointsCompareEquiv F).symm) ?_
  intro j
  ext u
  exact (congrArg Subtype.val
    ((fixedPointsCompareEquiv F).apply_symm_apply u)).symm

lemma preservesLimitsOfShapeSingleObj_baseChange (H : Type u) [Monoid H] [Finite H] :
    PreservesLimitsOfShape (SingleObj H) (baseChangeU k Ω) where
  preservesLimit {K} :=
    preservesLimit_of_preserves_limit_cone
      (actionFixedPointsConeIsLimit K) (isLimitMapConeFixedPoints K)

end FixedPointsBaseChange

/-! Assembly (leaf AG-GG-2g): the fiber functor of `FiniteEtale k` at the separable
closure satisfies the axioms (G4)–(G6) of a Galois fiber functor.  Everything is
transported along `fiberIsoBaseChangeFiber` — the equivalence part (`fiber Ω Ω` for
`Ω` separably closed) preserves and reflects everything, so each axiom reduces to the
corresponding exactness statement for `baseChangeU k Ω` proved above. -/

section Assembly

/-- The factorisation of the fiber functor through base change to the separable
closure, with universes pinned. -/
noncomputable def fiberFactorization :
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}) ≅
    (baseChangeU k (SeparableClosure k)).op ⋙
      CommAlgCat.FiniteEtale.fiber (SeparableClosure k) (SeparableClosure k) :=
  CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber k (SeparableClosure k) (SeparableClosure k)

/-- The fiber functor at the separable closure is a Galois fiber functor. -/
noncomputable instance : PreGaloisCategory.FiberFunctor
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}) where
  preservesTerminalObjects := by
    haveI := preservesColimitsOfShapePEmpty_baseChange k (SeparableClosure k)
    haveI : PreservesColimitsOfShape (Discrete PEmpty.{1})ᵒᵖ
        (baseChangeU k (SeparableClosure k)) :=
      preservesColimitsOfShape_of_equiv (Discrete.opposite PEmpty.{1}).symm _
    haveI : PreservesLimitsOfShape (Discrete PEmpty.{1})
        (baseChangeU k (SeparableClosure k)).op :=
      preservesLimitsOfShape_op _ _
    exact preservesLimitsOfShape_of_natIso (fiberFactorization k).symm
  preservesPullbacks := by
    haveI := preservesColimitsOfShapeWalkingSpan_baseChange (k := k)
      (Ω := SeparableClosure k)
    haveI : PreservesColimitsOfShape WalkingCospanᵒᵖ
        (baseChangeU k (SeparableClosure k)) :=
      preservesColimitsOfShape_of_equiv walkingCospanOpEquiv.symm _
    haveI : PreservesLimitsOfShape WalkingCospan
        (baseChangeU k (SeparableClosure k)).op :=
      preservesLimitsOfShape_op _ _
    exact preservesLimitsOfShape_of_natIso (fiberFactorization k).symm
  preservesFiniteCoproducts := by
    constructor
    intro n
    haveI := preservesLimitsOfShapeDiscrete_baseChange (k := k)
      (Ω := SeparableClosure k) (Fin n)
    haveI : PreservesLimitsOfShape (Discrete (Fin n))ᵒᵖ
        (baseChangeU k (SeparableClosure k)) :=
      preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm _
    haveI : PreservesColimitsOfShape (Discrete (Fin n))
        (baseChangeU k (SeparableClosure k)).op :=
      preservesColimitsOfShape_op _ _
    exact preservesColimitsOfShape_of_natIso (fiberFactorization k).symm
  preservesEpis := by
    haveI hbc : (baseChangeU k (SeparableClosure k)).op.PreservesEpimorphisms := by
      constructor
      intro X Y f hf
      haveI : (baseChangeU k (SeparableClosure k)).PreservesMonomorphisms :=
        preservesMonomorphisms_baseChange
      haveI : Mono f.unop := inferInstance
      haveI : Mono ((baseChangeU k (SeparableClosure k)).map f.unop) :=
        Functor.PreservesMonomorphisms.preserves _
      exact inferInstanceAs
        (Epi ((baseChangeU k (SeparableClosure k)).map f.unop).op)
    exact Functor.preservesEpimorphisms.of_iso (fiberFactorization k).symm
  preservesQuotientsByFiniteGroups G _ _ := by
    haveI : Finite Gᵐᵒᵖ := Finite.of_equiv G MulOpposite.opEquiv
    haveI := preservesLimitsOfShapeSingleObj_baseChange (k := k)
      (Ω := SeparableClosure k) Gᵐᵒᵖ
    haveI : PreservesLimitsOfShape (SingleObj G)ᵒᵖ
        (baseChangeU k (SeparableClosure k)) :=
      preservesLimitsOfShape_of_equiv (singleObjOpEquiv G) _
    haveI : PreservesColimitsOfShape (SingleObj G)
        (baseChangeU k (SeparableClosure k)).op :=
      preservesColimitsOfShape_op _ _
    exact preservesColimitsOfShape_of_natIso (fiberFactorization k).symm
  reflectsIsos := reflectsIsomorphisms_fiber k

end Assembly

end FiniteEtaleGalois

end ModularCurves
