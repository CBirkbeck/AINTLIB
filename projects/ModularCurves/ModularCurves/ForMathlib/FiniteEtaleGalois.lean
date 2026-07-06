import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.RingTheory.Etale.Finite

/-!
# Towards `PreGaloisCategory ((CommAlgCat.FiniteEtale k)ᵒᵖ)` (AG-GG-1)

The category of finite étale schemes over a field `k` — presented as the opposite of
mathlib's `CommAlgCat.FiniteEtale k` — is a Galois category (Lenstra 3.1, (G1)–(G3));
together with the fiber functor `CommAlgCat.FiniteEtale.fiber k k̄` this yields the
Grothendieck–Galois correspondence via mathlib's abstract
`CategoryTheory.Galois` machinery. This file builds the categorical
infrastructure leaf by leaf (ticket AG-GG-1):

* ambient (co)limit instances for `CommAlgCat k`, transported along
  `commAlgCatEquivUnder` from `Under (CommRingCat.of k)` (leaf 1.0);
* closure of the `finiteEtale` object property under the relevant (co)limits
  (leaves 1.1–1.4) and the direct-summand axiom (leaf 1.5).

Upstream candidate: `Mathlib.RingTheory.Etale.Finite` (nothing imports that file yet;
if mathlib lands this instance at a later bump, swap this file out for it).
-/

universe u

open CategoryTheory Limits

namespace ModularCurves

namespace CommAlgCatLimits

variable (k : Type u) [Field k]

instance hasFiniteLimits : HasFiniteLimits (CommAlgCat.{u} k) where
  out _ _ _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (commAlgCatEquivUnder (.of k)).functor

instance hasFiniteColimits : HasFiniteColimits (CommAlgCat.{u} k) where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (commAlgCatEquivUnder (.of k)).functor

instance hasColimitsOfShapeSingleObjCommRingCat (G : Type u) [Group G] :
    HasColimitsOfShape (SingleObj G) CommRingCat.{u} :=
  have : HasColimitsOfSize.{u, 0} CommRingCat.{u} := hasColimitsOfSizeShrink.{u, 0, u, u} CommRingCat.{u}
  inferInstance

instance hasColimitsOfShapeSingleObjUnder (G : Type u) [Group G] :
    HasColimitsOfShape (SingleObj G) (Under (CommRingCat.of k)) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Under.forget _)

instance hasColimitsOfShapeSingleObj (G : Type u) [Group G] :
    HasColimitsOfShape (SingleObj G) (CommAlgCat.{u} k) :=
  Adjunction.hasColimitsOfShape_of_equivalence (commAlgCatEquivUnder (.of k)).functor

end CommAlgCatLimits

namespace FiniteEtaleGalois

open CommAlgCat

open scoped TensorProduct

variable (k : Type u) [Field k]

/-! `k` is initial in `FiniteEtale k` (leaf AG-GG-1.3a). -/

instance subsingletonHomFromSelf (A : CommAlgCat.FiniteEtale.{u} k) :
    Subsingleton (CommAlgCat.FiniteEtale.of k k ⟶ A) :=
  ⟨fun f g => by ext⟩

instance nonemptyHomFromSelf (A : CommAlgCat.FiniteEtale.{u} k) :
    Nonempty (CommAlgCat.FiniteEtale.of k k ⟶ A) :=
  ⟨ObjectProperty.homMk
    (show CommAlgCat.of k k ⟶ A.obj from CommAlgCat.ofHom (Algebra.ofId k A.obj))⟩

instance hasInitial : HasInitial (CommAlgCat.FiniteEtale.{u} k) :=
  hasInitial_of_unique (CommAlgCat.FiniteEtale.of k k)

/-! Finite products in `FiniteEtale k` (leaf AG-GG-1.1): the product of finitely many
finite étale algebras is their pointwise product algebra. -/

variable {k}

/-- The product fan on a finite family of finite étale algebras, with pointwise-product
vertex. -/
noncomputable def productFan {ι : Type} [Finite ι] (A : ι → CommAlgCat.FiniteEtale.{u} k) :
    Fan A :=
  Fan.mk (CommAlgCat.FiniteEtale.of k (Π i, A i))
    (fun i => ObjectProperty.homMk
      (show CommAlgCat.of k (Π j, A j) ⟶ (A i).obj from
        CommAlgCat.ofHom (Pi.evalAlgHom k (fun j => (A j : Type u)) i)))

/-- The product fan is a limit fan. -/
noncomputable def productFanIsLimit {ι : Type} [Finite ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) : IsLimit (productFan A) :=
  Fan.IsLimit.mk _
    (fun s => ObjectProperty.homMk
      (show s.pt.obj ⟶ CommAlgCat.of k (Π j, A j) from
        CommAlgCat.ofHom (AlgHom.pi (fun i => (s.proj i).hom.hom))))
    (fun s i => by
      ext x
      rfl)
    (fun s m hm => by
      ext x
      refine funext fun i => ?_
      exact congrArg (fun q => q.hom.hom x) (hm i))

instance hasFiniteProducts : HasFiniteProducts (CommAlgCat.FiniteEtale.{u} k) where
  out n :=
    { has_limit := fun F => by
        haveI : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
          HasLimit.mk ⟨_, productFanIsLimit (F.obj ∘ Discrete.mk)⟩
        exact hasLimit_of_iso (Discrete.natIsoFunctor (F := F)).symm }

/-! Pushouts in `FiniteEtale k` (leaf AG-GG-1.2): the pushout of finite étale algebras
along finite étale algebras is the tensor product, which is again finite étale. -/

section Pushout

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  [Algebra A B] [Algebra A C] [IsScalarTower k A B] [IsScalarTower k A C]

/-- The tensor product of finite étale `k`-algebras over a finite étale `k`-algebra is
étale over `k` (uses the two-out-of-three property for étale maps). -/
theorem etale_tensorProduct [Algebra.Etale k A] [Algebra.Etale k B] [Algebra.Etale k C] :
    Algebra.Etale k (B ⊗[A] C) := by
  haveI : Algebra.Etale A C := Algebra.Etale.of_restrictScalars k A C
  haveI : Algebra.Etale B (B ⊗[A] C) := inferInstance
  exact Algebra.Etale.comp k B (B ⊗[A] C)

/-- The tensor product of finite `k`-algebras over a `k`-algebra is finite over `k`. -/
theorem finite_tensorProduct [Module.Finite k B] [Module.Finite k C] :
    Module.Finite k (B ⊗[A] C) := by
  haveI : Module.Finite A C := Module.Finite.of_restrictScalars_finite k A C
  haveI : Module.Finite B (B ⊗[A] C) := inferInstance
  exact Module.Finite.trans B (B ⊗[A] C)

end Pushout

section PushoutCat

variable {X Y Z : CommAlgCat.FiniteEtale.{u} k} (f : X ⟶ Y) (g : X ⟶ Z)

/-- The pushout cocone on a span of finite étale `k`-algebras, with the tensor product
as vertex (the `X`-algebra structures on `Y` and `Z` come from the span legs). -/
noncomputable def spanPushoutCocone : PushoutCocone f g :=
  letI : Algebra X.obj Y.obj := f.hom.hom.toRingHom.toAlgebra
  letI : Algebra X.obj Z.obj := g.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower k X.obj Y.obj :=
    IsScalarTower.of_algebraMap_eq fun r => (f.hom.hom.commutes r).symm
  haveI : IsScalarTower k X.obj Z.obj :=
    IsScalarTower.of_algebraMap_eq fun r => (g.hom.hom.commutes r).symm
  haveI := etale_tensorProduct (k := k) X.obj Y.obj Z.obj
  haveI := finite_tensorProduct (k := k) X.obj Y.obj Z.obj
  PushoutCocone.mk
    (W := CommAlgCat.FiniteEtale.of k (↑Y.obj ⊗[↑X.obj] ↑Z.obj))
    (ObjectProperty.homMk
      (show Y.obj ⟶ CommAlgCat.of k (↑Y.obj ⊗[↑X.obj] ↑Z.obj) from
        CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (S := k))))
    (ObjectProperty.homMk
      (show Z.obj ⟶ CommAlgCat.of k (↑Y.obj ⊗[↑X.obj] ↑Z.obj) from
        CommAlgCat.ofHom
          ((Algebra.TensorProduct.includeRight (R := ↑X.obj)).restrictScalars k)))
    (by
      ext a
      show (f.hom.hom a) ⊗ₜ (1 : Z.obj) = (1 : Y.obj) ⊗ₜ (g.hom.hom a)
      exact ((Algebra.TensorProduct.includeLeft (S := (↑X.obj : Type u))).commutes a).trans
        ((Algebra.TensorProduct.includeRight (R := (↑X.obj : Type u))).commutes a).symm)

/-- The tensor-product cocone is a colimit cocone: `FiniteEtale k` has pushouts. -/
noncomputable def spanPushoutCoconeIsColimit : IsColimit (spanPushoutCocone f g) :=
  PushoutCocone.isColimitAux' _ fun s => by
    letI : Algebra X.obj Y.obj := f.hom.hom.toRingHom.toAlgebra
    letI : Algebra X.obj Z.obj := g.hom.hom.toRingHom.toAlgebra
    letI : Algebra X.obj s.pt.obj := (s.inl.hom.hom.comp f.hom.hom).toRingHom.toAlgebra
    haveI : IsScalarTower k X.obj Y.obj :=
      IsScalarTower.of_algebraMap_eq fun r => (f.hom.hom.commutes r).symm
    haveI : IsScalarTower k X.obj Z.obj :=
      IsScalarTower.of_algebraMap_eq fun r => (g.hom.hom.commutes r).symm
    haveI : IsScalarTower k X.obj s.pt.obj :=
      IsScalarTower.of_algebraMap_eq fun r => by
        show algebraMap k s.pt.obj r = s.inl.hom.hom (f.hom.hom (algebraMap k X.obj r))
        rw [f.hom.hom.commutes r, s.inl.hom.hom.commutes r]
    have hcond : ∀ a : X.obj, s.inl.hom.hom (f.hom.hom a) = s.inr.hom.hom (g.hom.hom a) :=
      fun a => congrArg (fun q => q.hom.hom a) s.condition
    let f' : Y.obj →ₐ[X.obj] s.pt.obj :=
      { s.inl.hom.hom with commutes' := fun a => rfl }
    let g' : Z.obj →ₐ[X.obj] s.pt.obj :=
      { s.inr.hom.hom with commutes' := fun a => (hcond a).symm }
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom
      ((Algebra.TensorProduct.productMap f' g').restrictScalars k)), ?_, ?_, ?_⟩
    · ext x
      exact Algebra.TensorProduct.productMap_left_apply f' g' x
    · ext x
      exact Algebra.TensorProduct.productMap_right_apply f' g' x
    · intro m hm1 hm2
      have hml : ∀ y : Y.obj, m.hom.hom (y ⊗ₜ 1) = s.inl.hom.hom y :=
        fun y => congrArg (fun q => q.hom.hom y) hm1
      have hmr : ∀ z : Z.obj, m.hom.hom ((1 : Y.obj) ⊗ₜ z) = s.inr.hom.hom z :=
        fun z => congrArg (fun q => q.hom.hom z) hm2
      ext x
      induction x using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul y z =>
        have h1 : (y ⊗ₜ z : ↑Y.obj ⊗[↑X.obj] ↑Z.obj) = (y ⊗ₜ 1) * ((1 : Y.obj) ⊗ₜ z) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have h2 : m.hom.hom (y ⊗ₜ z) = s.inl.hom.hom y * s.inr.hom.hom z :=
          (congrArg m.hom.hom h1).trans ((map_mul m.hom.hom _ _).trans
            (congrArg₂ (· * ·) (hml y) (hmr z)))
        have h3 : ((Algebra.TensorProduct.productMap f' g').restrictScalars k) (y ⊗ₜ z) =
            s.inl.hom.hom y * s.inr.hom.hom z := by
          show Algebra.TensorProduct.productMap f' g' (y ⊗ₜ z) = _
          rw [Algebra.TensorProduct.productMap_apply_tmul]
          rfl
        exact h2.trans h3.symm
      | add x₁ x₂ ih₁ ih₂ =>
        exact (map_add _ _ _).trans
          (((congrArg₂ (· + ·) ih₁ ih₂).trans (map_add _ _ _).symm))

instance hasPushouts : HasPushouts (CommAlgCat.FiniteEtale.{u} k) where
  has_colimit F := by
    haveI : HasColimit (span (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)) :=
      HasColimit.mk ⟨_, spanPushoutCoconeIsColimit
        (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)⟩
    exact hasColimit_of_iso (diagramIsoSpan F)

end PushoutCat

end FiniteEtaleGalois

end ModularCurves
