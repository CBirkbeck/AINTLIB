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

/-! The heart of leaf AG-GG-1.4: subalgebras of finite étale algebras over a field are
finite étale. Route: every element of a finite étale algebra is separable
(via the product-of-separable-extensions classification and a distinct-minimal-polynomials
annihilator), and a reduced artinian algebra all of whose elements are separable is
formally étale (via `IsArtinianRing.equivPi` and the field case). -/

section EtaleSubalgebra

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]

/-- Every element of a finite étale algebra over a field is separable. -/
theorem isSeparable_of_etale [Module.Finite k A] [Algebra.Etale k A] (x : A) :
    IsSeparable k x := by
  classical
  obtain ⟨I, hI, L, hfield, halg, e, hLi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k A).mp inferInstance
  haveI := fun i => (hLi i).1
  haveI := fun i => (hLi i).2
  haveI : Fintype I := Fintype.ofFinite I
  have hint : ∀ i, IsIntegral k (e x i) := fun i =>
    Algebra.IsIntegral.isIntegral (R := k) (e x i)
  set S : Finset (Polynomial k) :=
    Finset.image (fun i => minpoly k (e x i)) Finset.univ with hS
  have hFsep : Polynomial.Separable (S.prod id) := by
    refine Polynomial.separable_prod' ?_ ?_
    · intro p hp q hq hpq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
      refine (minpoly.irreducible (hint i)).coprime_iff_not_dvd.mpr ?_
      intro hdvd
      exact hpq (Polynomial.eq_of_monic_of_associated (minpoly.monic (hint i))
        (minpoly.monic (hint j))
        ((minpoly.irreducible (hint i)).associated_of_dvd
          (minpoly.irreducible (hint j)) hdvd))
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact Algebra.IsSeparable.isSeparable k (e x i)
  have hann : Polynomial.aeval x (S.prod id) = 0 := by
    apply e.injective
    rw [map_zero]
    refine Eq.trans (Polynomial.aeval_algHom_apply e.toAlgHom x (S.prod id)).symm ?_
    funext i
    refine Eq.trans (Polynomial.aeval_algHom_apply (Pi.evalAlgHom k L i) (e x)
      (S.prod id)).symm ?_
    show Polynomial.aeval (e x i) (S.prod id) = 0
    obtain ⟨F, hFS⟩ : ∃ F, S.prod id = minpoly k (e x i) * F :=
      (Finset.dvd_prod_of_mem id (Finset.mem_image_of_mem _ (Finset.mem_univ i))).elim
        fun F hF => ⟨F, hF⟩
    rw [hFS, map_mul, minpoly.aeval, zero_mul]
  exact Polynomial.Separable.of_dvd hFsep (minpoly.dvd k x hann)

/-- A subalgebra of a finite étale algebra over a field is étale. -/
theorem etale_subalgebra [Module.Finite k A] [Algebra.Etale k A] (B : Subalgebra k A) :
    Algebra.Etale k B := by
  classical
  haveI : Module.Finite k B := inferInstanceAs (Module.Finite k B.toSubmodule)
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  haveI : IsReduced B := ⟨fun x hx => by
    have h2 : ((x : A)) = 0 := (hx.map (B.subtype)).eq_zero
    exact Subtype.ext h2⟩
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
  have hsepB : ∀ x : B, IsSeparable k x := fun x => by
    have h1 : minpoly k (B.val x) = minpoly k x :=
      minpoly.algHom_eq B.val (fun _ _ h => Subtype.ext h) x
    have h2 := isSeparable_of_etale (k := k) (B.val x)
    rwa [IsSeparable, h1] at h2
  haveI hFE : Algebra.FormallyEtale k B := by
    letI _ (m : MaximalSpectrum B) : Field (B ⧸ m.asIdeal) :=
      Ideal.Quotient.field m.asIdeal
    rw [Algebra.FormallyEtale.iff_of_equiv ((IsArtinianRing.equivPi B).restrictScalars k),
      Algebra.FormallyEtale.pi_iff]
    intro m
    haveI : Algebra.IsSeparable k (B ⧸ m.asIdeal) := ⟨fun y => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hann : Polynomial.aeval (Ideal.Quotient.mk m.asIdeal b) (minpoly k b) = 0 := by
        have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k m.asIdeal) b
          (minpoly k b)
        rwa [minpoly.aeval, map_zero] at h
      exact Polynomial.Separable.of_dvd (hsepB b) (minpoly.dvd k _ hann)⟩
    exact Algebra.FormallyEtale.of_isSeparable k (B ⧸ m.asIdeal)
  haveI : Algebra.FinitePresentation k B :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

end EtaleSubalgebra

/-! Limits of shape `SingleObj H` in `FiniteEtale k` (leaf AG-GG-1.4, categorical part):
the limit of an `H`-action on a finite étale algebra is the fixed-point subalgebra,
finite étale by `etale_subalgebra`. -/

section FixedPoints

variable {k : Type u} [Field k] {H : Type u} [Monoid H]

variable (F : SingleObj H ⥤ CommAlgCat.FiniteEtale.{u} k)

/-- The fixed points of a monoid action (by `k`-algebra endomorphisms) on a finite
étale algebra, as a subalgebra. -/
def actionFixedPoints : Subalgebra k (F.obj (SingleObj.star H)).obj where
  carrier := {a | ∀ h : H,
    (F.map (h : SingleObj.star H ⟶ SingleObj.star H)).hom.hom a = a}
  mul_mem' := fun ha hb h => by rw [map_mul, ha h, hb h]
  add_mem' := fun ha hb h => by rw [map_add, ha h, hb h]
  algebraMap_mem' := fun r h =>
    (F.map (h : SingleObj.star H ⟶ SingleObj.star H)).hom.hom.commutes r

/-- The fixed-point cone on an `H`-action. -/
noncomputable def actionFixedPointsCone : Cone F where
  pt :=
    haveI : Algebra.Etale k (actionFixedPoints F) :=
      etale_subalgebra (actionFixedPoints F)
    haveI : Module.Finite k (actionFixedPoints F) :=
      inferInstanceAs (Module.Finite k (actionFixedPoints F).toSubmodule)
    CommAlgCat.FiniteEtale.of k (actionFixedPoints F)
  π :=
    { app := fun _ => ObjectProperty.homMk
        (show _ ⟶ (F.obj (SingleObj.star H)).obj from
          CommAlgCat.ofHom (actionFixedPoints F).val)
      naturality := fun _ _ h => by
        ext ⟨a, ha⟩
        exact (ha h).symm }

/-- The fixed-point cone is a limit cone. -/
noncomputable def actionFixedPointsConeIsLimit : IsLimit (actionFixedPointsCone F) where
  lift s := ObjectProperty.homMk (CommAlgCat.ofHom
    (AlgHom.codRestrict (s.π.app (SingleObj.star H)).hom.hom (actionFixedPoints F)
      (fun t h => by
        have hnat := congrArg (fun q => q.hom.hom t)
          (s.π.naturality (show SingleObj.star H ⟶ SingleObj.star H from h))
        exact hnat.symm)))
  fac s j := by
    ext t
    rfl
  uniq s m hm := by
    ext t
    have h := congrArg (fun q => q.hom.hom t) (hm (SingleObj.star H))
    exact Subtype.ext h

instance hasLimitsOfShapeSingleObj :
    HasLimitsOfShape (SingleObj H) (CommAlgCat.FiniteEtale.{u} k) where
  has_limit F := HasLimit.mk ⟨_, actionFixedPointsConeIsLimit F⟩

end FixedPoints

end FiniteEtaleGalois

end ModularCurves
