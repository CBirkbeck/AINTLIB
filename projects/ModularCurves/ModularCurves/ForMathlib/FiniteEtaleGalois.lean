/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
import Mathlib.RingTheory.Etale.Finite
import ModularCurves.ForMathlib.EtaleSectionsCount

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
  have : HasColimitsOfSize.{u, 0} CommRingCat.{u} :=
    hasColimitsOfSizeShrink.{u, 0, u, u} CommRingCat.{u}
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

/-- A finite reduced algebra over a field all of whose elements are separable is étale.
This is the common core of `etale_subalgebra` and `etale_quotient`. -/
theorem etale_of_isSeparable (B : Type u) [CommRing B] [Algebra k B] [Module.Finite k B]
    [IsReduced B] (hsep : ∀ x : B, IsSeparable k x) : Algebra.Etale k B := by
  classical
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
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
      exact Polynomial.Separable.of_dvd (hsep b) (minpoly.dvd k _ hann)⟩
    exact Algebra.FormallyEtale.of_isSeparable k (B ⧸ m.asIdeal)
  haveI : Algebra.FinitePresentation k B :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- A subalgebra of a finite étale algebra over a field is étale. -/
theorem etale_subalgebra [Module.Finite k A] [Algebra.Etale k A] (B : Subalgebra k A) :
    Algebra.Etale k B := by
  haveI : Module.Finite k B := inferInstanceAs (Module.Finite k B.toSubmodule)
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  haveI : IsReduced B := ⟨fun x hx => by
    have h2 : ((x : A)) = 0 := (hx.map (B.subtype)).eq_zero
    exact Subtype.ext h2⟩
  refine etale_of_isSeparable B fun x => ?_
  have h1 : minpoly k (B.val x) = minpoly k x :=
    minpoly.algHom_eq B.val (fun _ _ h => Subtype.ext h) x
  have h2 := isSeparable_of_etale (k := k) (B.val x)
  rwa [IsSeparable, h1] at h2

/-- Every quotient of a finite étale algebra over a field is étale.  Every ideal is
complemented (the algebra is semisimple), which forces it to be radical, so the quotient
is reduced; separability of elements descends along the quotient map. -/
theorem etale_quotient [Module.Finite k A] [Algebra.Etale k A] (J : Ideal A) :
    Algebra.Etale k (A ⧸ J) := by
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  haveI : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  obtain ⟨I, hIJ⟩ := exists_isCompl J
  have hrad2 : ∀ x : A, x * x ∈ J → x ∈ J := by
    intro x hx2
    have hxIJ : x ∈ I ⊔ J := hIJ.symm.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hxIJ
    have hij0 : i * j = 0 := by
      have hmem : i * j ∈ I ⊓ J := ⟨Ideal.mul_mem_right j I hi, Ideal.mul_mem_left J i hj⟩
      simpa [hIJ.symm.inf_eq_bot] using hmem
    have hii : i * i ∈ I ⊓ J := by
      refine ⟨Ideal.mul_mem_right i I hi, ?_⟩
      have hexp : i * i = x * x - j * j - 2 * (i * j) := by rw [← hij]; ring
      rw [hexp, hij0, mul_zero, sub_zero]
      exact J.sub_mem hx2 (Ideal.mul_mem_left J j hj)
    have hi0 : i = 0 := by
      have hnil : IsNilpotent i := ⟨2, by rw [pow_two]; simpa [hIJ.symm.inf_eq_bot] using hii⟩
      exact hnil.eq_zero
    rw [← hij, hi0, zero_add]
    exact hj
  have hradJ : J.IsRadical := by
    have key : ∀ n, ∀ x : A, x ^ n ∈ J → n ≠ 0 → x ∈ J := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro x hxn hn0
        rcases Nat.lt_or_ge n 2 with h2 | h2
        · interval_cases n
          · exact absurd rfl hn0
          · simpa using hxn
        · have hm2 : x ^ (2 * ((n + 1) / 2)) ∈ J := by
            have hsplit : x ^ (2 * ((n + 1) / 2)) = x ^ n * x ^ (2 * ((n + 1) / 2) - n) := by
              rw [← pow_add]
              congr 1
              omega
            rw [hsplit]
            exact J.mul_mem_right _ hxn
          have hxm : x ^ ((n + 1) / 2) ∈ J := by
            refine hrad2 _ ?_
            rwa [← pow_two, ← pow_mul, mul_comm]
          exact ih ((n + 1) / 2) (by omega) x hxm (by omega)
    intro x hx
    obtain ⟨n, hn⟩ := hx
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [pow_zero] at hn
      exact ((Ideal.eq_top_iff_one J).mpr hn).symm ▸ (Submodule.mem_top : x ∈ ⊤)
    · exact key n x hn hn0.ne'
  haveI : IsReduced (A ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp hradJ
  haveI : Module.Finite k (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k J).toLinearMap
      Ideal.Quotient.mk_surjective
  refine etale_of_isSeparable (A ⧸ J) fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hann : Polynomial.aeval (Ideal.Quotient.mk J x) (minpoly k x) = 0 := by
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k J) x (minpoly k x)
    rwa [minpoly.aeval, map_zero] at h
  exact Polynomial.Separable.of_dvd (isSeparable_of_etale (k := k) x) (minpoly.dvd k _ hann)

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

/-! Epimorphisms in `FiniteEtale k` are surjective (leaf AG-GG-1.5, part (i)):
counting homomorphisms into the separable closure — `Nat.card (A →ₐ[k] Ω) = finrank k A`
— plus a pigeonhole against the range subalgebra. -/

section EpiSurjective

variable {k : Type u} [Field k]

/-- A finite étale algebra over `k` has exactly `finrank` many homomorphisms into the
separable closure of `k`. -/
theorem natCard_algHom_sepClosure (A : Type u) [CommRing A] [Algebra k A]
    [Module.Finite k A] [Algebra.Etale k A] :
    Nat.card (A →ₐ[k] SeparableClosure k) = Module.finrank k A := by
  rw [Nat.card_congr (Algebra.TensorProduct.liftEquivRight k (SeparableClosure k) A
    (SeparableClosure k)),
    natCard_algHom_eq_finrank (SeparableClosure k) (SeparableClosure k ⊗[k] A)]
  exact Module.finrank_baseChange

/-- Epimorphisms in the category of finite étale algebras over a field are surjective. -/
theorem surjective_of_epi {X Y : CommAlgCat.FiniteEtale.{u} k} (π : Y ⟶ X) [Epi π] :
    Function.Surjective π.hom.hom := by
  classical
  rcases subsingleton_or_nontrivial (X.obj : Type u) with hsub | hnt
  · exact fun x => ⟨0, Subsingleton.elim _ _⟩
  by_contra hns
  set X' : Subalgebra k X.obj := π.hom.hom.range with hX'
  have hne : X' ≠ ⊤ := fun h => hns ((AlgHom.range_eq_top _).mp h)
  haveI : Algebra.Etale k X' := etale_subalgebra X'
  haveI : Module.Finite k X' := inferInstanceAs (Module.Finite k X'.toSubmodule)
  have hcard1 := natCard_algHom_sepClosure (k := k) X.obj
  have hcard2 := natCard_algHom_sepClosure (k := k) X'
  have hlt : Module.finrank k X' < Module.finrank k X.obj := by
    have hsub : X'.toSubmodule ≠ ⊤ := fun h =>
      hne (Subalgebra.toSubmodule_injective (by simpa using h))
    exact Submodule.finrank_lt hsub
  haveI hfinX : Finite (X.obj →ₐ[k] SeparableClosure k) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard1]
    have : 0 < Module.finrank k X.obj := Module.finrank_pos
    omega
  haveI : Fintype (X.obj →ₐ[k] SeparableClosure k) := Fintype.ofFinite _
  haveI : Nontrivial X' := ⟨⟨1, 0, fun h =>
    one_ne_zero (α := X.obj) (congrArg Subtype.val h)⟩⟩
  haveI hfinX' : Finite (X' →ₐ[k] SeparableClosure k) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard2]
    have : 0 < Module.finrank k X' := Module.finrank_pos
    omega
  haveI : Fintype (X' →ₐ[k] SeparableClosure k) := Fintype.ofFinite _
  obtain ⟨g₁, g₂, hg, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun g : X.obj →ₐ[k] SeparableClosure k => g.comp X'.val)
    (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard1, hcard2]
      exact hlt)
  set W : Subalgebra k (SeparableClosure k) := g₁.range ⊔ g₂.range with hW
  haveI : Module.Finite k W := by
    have hr : (Algebra.TensorProduct.productMap g₁.range.val g₂.range.val).range = W := by
      rw [Algebra.TensorProduct.productMap_range, Subalgebra.range_val, Subalgebra.range_val]
    haveI : Module.Finite k g₁.range :=
      Module.Finite.of_surjective g₁.rangeRestrict.toLinearMap g₁.rangeRestrict_surjective
    haveI : Module.Finite k g₂.range :=
      Module.Finite.of_surjective g₂.rangeRestrict.toLinearMap g₂.rangeRestrict_surjective
    rw [← hr]
    exact Module.Finite.of_surjective
      (Algebra.TensorProduct.productMap g₁.range.val g₂.range.val).rangeRestrict.toLinearMap
      (AlgHom.rangeRestrict_surjective _)
  have hWfield : IsField W :=
    isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)
  letI : Field W := hWfield.toField
  haveI : Algebra.IsSeparable k W := ⟨fun x => by
    have h1 : minpoly k (W.val x) = minpoly k x :=
      minpoly.algHom_eq W.val (fun _ _ h => Subtype.ext h) x
    have h2 := Algebra.IsSeparable.isSeparable k (W.val x)
    rwa [IsSeparable, h1] at h2⟩
  haveI : Algebra.FormallyEtale k W := Algebra.FormallyEtale.of_isSeparable k W
  haveI : Algebra.FinitePresentation k W :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale k W := ⟨inferInstance, inferInstance⟩
  have hmem₁ : ∀ x, g₁ x ∈ W := fun x => (le_sup_left : g₁.range ≤ W) ⟨x, rfl⟩
  have hmem₂ : ∀ x, g₂ x ∈ W := fun x => (le_sup_right : g₂.range ≤ W) ⟨x, rfl⟩
  have hcomp : π ≫ (ObjectProperty.homMk (CommAlgCat.ofHom
        (g₁.codRestrict W hmem₁)) : X ⟶ CommAlgCat.FiniteEtale.of k W) =
      π ≫ (ObjectProperty.homMk (CommAlgCat.ofHom (g₂.codRestrict W hmem₂))) := by
    ext y
    simpa using congrArg (fun q : X' →ₐ[k] SeparableClosure k =>
      q ⟨π.hom.hom y, ⟨y, rfl⟩⟩) heq
  have hG := (cancel_epi π).mp hcomp
  refine hg (AlgHom.ext fun x => ?_)
  exact congrArg (fun q : X ⟶ CommAlgCat.FiniteEtale.of k W =>
    (q.hom.hom x : SeparableClosure k)) hG

end EpiSurjective

/-! Monomorphisms in `(FiniteEtale k)ᵒᵖ` induce isomorphisms on direct summands
(axiom G3, leaf AG-GG-1.5 part (ii)): a mono in the opposite category is an epi of
algebras, hence surjective; its kernel is complemented (the algebra is semisimple),
and the Chinese remainder theorem splits the source as a binary product. -/

section EpiSplitting

variable {k : Type u} [Field k]

/-- Chinese remainder bijectivity: if `φ : B →ₐ[k] C` is surjective and the ideal `J`
is a complement of `ker φ`, then `(φ, mkₐ J) : B → C × (B ⧸ J)` is bijective. The
idempotent `e + f = 1` splitting `ker φ ⊕ J` gives both directions. -/
theorem bijective_algHom_prod_mkₐ_of_isCompl {B C : Type u} [CommRing B] [Algebra k B]
    [CommRing C] [Algebra k C] (φ : B →ₐ[k] C) (hsurj : Function.Surjective φ)
    {J : Ideal B} (hIJ : IsCompl (RingHom.ker φ) J) :
    Function.Bijective (φ.prod (Ideal.Quotient.mkₐ k J)) := by
  classical
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp
    (show (1 : B) ∈ RingHom.ker φ ⊔ J from hIJ.sup_eq_top ▸ Submodule.mem_top)
  have hπe : φ e = 0 := he
  have hπf : φ f = 1 := by
    have h := congrArg φ hef
    rw [map_add, map_one, hπe, zero_add] at h
    exact h
  have hqf : Ideal.Quotient.mk J f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hqe : Ideal.Quotient.mk J e = 1 := by
    have h := congrArg (Ideal.Quotient.mk J) hef
    rw [map_add, map_one, hqf, add_zero] at h
    exact h
  constructor
  · intro x y hxy
    have h1 : φ (x - y) = 0 := by
      have := congrArg Prod.fst hxy
      simpa [map_sub, sub_eq_zero] using this
    have h2 : x - y ∈ J := by
      have := congrArg Prod.snd hxy
      rw [show (φ.prod (Ideal.Quotient.mkₐ k J)) x =
        (φ x, Ideal.Quotient.mk J x) from rfl] at hxy
      have h2' : (Ideal.Quotient.mk J) x = (Ideal.Quotient.mk J) y :=
        congrArg Prod.snd hxy
      exact Ideal.Quotient.eq.mp h2'
    have hmem : x - y ∈ RingHom.ker φ ⊓ J := ⟨h1, h2⟩
    rw [hIJ.inf_eq_bot] at hmem
    exact sub_eq_zero.mp (by simpa using hmem)
  · rintro ⟨a', z⟩
    obtain ⟨a, ha⟩ := hsurj a'
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨a * f + b * e, Prod.ext ?_ ?_⟩
    · show φ (a * f + b * e) = a'
      rw [map_add, map_mul, map_mul, hπf, hπe, mul_one, mul_zero, add_zero, ha]
    · show Ideal.Quotient.mk J (a * f + b * e) = Ideal.Quotient.mk J b
      rw [map_add, map_mul, map_mul, hqf, hqe, mul_zero, zero_add, mul_one]

/-- Chinese remainder splitting along an epimorphism of finite étale algebras: the
source is the binary product of the target and the quotient by a complement of the
kernel.  This is the content of axiom (G3) for `(FiniteEtale k)ᵒᵖ`. -/
theorem monoInducesIsoOnDirectSummand_op {X Y : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ}
    (i : X ⟶ Y) [Mono i] : ∃ (Z : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  classical
  set π := i.unop with hπdef
  have hsurj : Function.Surjective π.hom.hom := surjective_of_epi π
  set I : Ideal (Y.unop.obj : Type u) := RingHom.ker π.hom.hom with hIdef
  haveI : IsReduced (Y.unop.obj : Type u) :=
    Algebra.FormallyUnramified.isReduced_of_field k _
  haveI : IsArtinianRing (Y.unop.obj : Type u) := isArtinian_of_tower k inferInstance
  haveI : IsSemisimpleRing (Y.unop.obj : Type u) :=
    IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨J, hIJ⟩ := exists_isCompl I
  haveI : Algebra.Etale k ((Y.unop.obj : Type u) ⧸ J) := etale_quotient J
  haveI : Module.Finite k ((Y.unop.obj : Type u) ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k J).toLinearMap
      Ideal.Quotient.mk_surjective
  set Zobj : CommAlgCat.FiniteEtale.{u} k :=
    CommAlgCat.FiniteEtale.of k ((Y.unop.obj : Type u) ⧸ J) with hZdef
  set q : Y.unop ⟶ Zobj :=
    ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k J)) with hqdef
  have hbij := bijective_algHom_prod_mkₐ_of_isCompl π.hom.hom hsurj (hIdef ▸ hIJ)
  set Φ := AlgEquiv.ofBijective ((π.hom.hom).prod (Ideal.Quotient.mkₐ k J)) hbij
    with hΦdef
  have hlim : IsLimit (BinaryFan.mk π q) := by
    refine BinaryFan.isLimitMk
      (fun s => ObjectProperty.homMk (CommAlgCat.ofHom
        (Φ.symm.toAlgHom.comp ((s.fst.hom.hom).prod (s.snd.hom.hom))))) ?_ ?_ ?_
    · intro s
      ext w
      exact congrArg Prod.fst
        (Φ.apply_symm_apply (s.fst.hom.hom w, s.snd.hom.hom w))
    · intro s
      ext w
      exact congrArg Prod.snd
        (Φ.apply_symm_apply (s.fst.hom.hom w, s.snd.hom.hom w))
    · intro s m h₁ h₂
      ext w
      apply Φ.injective
      refine Prod.ext ?_ ?_
      · have := congrArg (fun (t : s.pt ⟶ X.unop) => t.hom.hom w) h₁
        exact this.trans (congrArg Prod.fst
          (Φ.apply_symm_apply (s.fst.hom.hom w, s.snd.hom.hom w))).symm
      · have := congrArg (fun (t : s.pt ⟶ Zobj) => t.hom.hom w) h₂
        exact this.trans (congrArg Prod.snd
          (Φ.apply_symm_apply (s.fst.hom.hom w, s.snd.hom.hom w))).symm
  exact ⟨Opposite.op Zobj, q.op, ⟨BinaryFan.IsLimit.op hlim⟩⟩

end EpiSplitting

/-! Assembly: `(FiniteEtale k)ᵒᵖ` is a PreGalois category.  Axioms (G1)/(G2) are the
op-duals of the initial object, finite products, pushouts and `SingleObj`-shaped limits
established above; (G3) is `monoInducesIsoOnDirectSummand_op`. -/

section PreGalois

open Opposite

variable {k : Type u} [Field k]

/-- The opposite of the one-object category of a monoid is the one-object category of
the opposite monoid. -/
def singleObjOpEquiv (M : Type*) [Monoid M] : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ where
  functor :=
    { obj := fun _ => op (SingleObj.star M)
      map := fun g => Quiver.Hom.op
        (show SingleObj.star M ⟶ SingleObj.star M from MulOpposite.unop g)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  inverse :=
    { obj := fun _ => SingleObj.star Mᵐᵒᵖ
      map := fun u => show SingleObj.star Mᵐᵒᵖ ⟶ SingleObj.star Mᵐᵒᵖ from
        MulOpposite.op (show M from Quiver.Hom.unop u)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.id_comp _

instance hasQuotientsByFiniteGroupsOp (G : Type u) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ :=
  haveI : HasLimitsOfShape (SingleObj G)ᵒᵖ (CommAlgCat.FiniteEtale.{u} k) :=
    hasLimitsOfShape_of_equivalence (C := CommAlgCat.FiniteEtale.{u} k) (singleObjOpEquiv G)
  hasColimitsOfShape_op_of_hasLimitsOfShape

/-- The opposite of the category of finite étale algebras over a field is a PreGalois
category in the sense of SGA1/Lenstra: axioms (G1)–(G3) hold.  Together with the fibre
functor to `FintypeCat` this exhibits the absolute Galois group as the fundamental group
of `Spec k`. -/
instance : PreGaloisCategory (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ where
  hasQuotientsByFiniteGroups G _ _ := inferInstance
  monoInducesIsoOnDirectSummand i := monoInducesIsoOnDirectSummand_op i

end PreGalois

/-! The tensor product is the binary coproduct of finite étale algebras (used to
transport group structures through the Galois correspondence, T-F1c). -/

section TensorCoproduct

variable {k : Type u} [Field k]

variable (A B : CommAlgCat.FiniteEtale.{u} k)

instance : Algebra.Etale k ((A : Type u) ⊗[k] (B : Type u)) := by
  haveI h1 : Algebra.Etale (A : Type u) ((A : Type u) ⊗[k] (B : Type u)) :=
    Algebra.Etale.baseChange k (B : Type u) (A : Type u)
  exact Algebra.Etale.comp k (A : Type u) ((A : Type u) ⊗[k] (B : Type u))

instance : Module.Finite k ((A : Type u) ⊗[k] (B : Type u)) := by
  haveI : Module.Finite (A : Type u) ((A : Type u) ⊗[k] (B : Type u)) :=
    inferInstance
  exact Module.Finite.trans (A : Type u) ((A : Type u) ⊗[k] (B : Type u))

/-- The tensor product of two finite étale algebras, as an object. -/
noncomputable def tensorObj : CommAlgCat.FiniteEtale.{u} k :=
  CommAlgCat.FiniteEtale.of k ((A : Type u) ⊗[k] (B : Type u))

/-- The coproduct cofan on the tensor product. -/
noncomputable def tensorBinaryCofan : BinaryCofan A B :=
  BinaryCofan.mk
    (ObjectProperty.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) :
        (A : Type u) →ₐ[k] (A : Type u) ⊗[k] (B : Type u))) :
      A ⟶ tensorObj A B)
    (ObjectProperty.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) :
        (B : Type u) →ₐ[k] (A : Type u) ⊗[k] (B : Type u))))

/-- The tensor product is the binary coproduct of finite étale algebras. -/
noncomputable def tensorBinaryCofanIsColimit :
    IsColimit (tensorBinaryCofan A B) := by
  refine BinaryCofan.isColimitMk
    (fun s => ObjectProperty.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.productMap s.inl.hom.hom s.inr.hom.hom)))
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)
  · ext a
    exact Algebra.TensorProduct.productMap_left_apply _ _ a
  · ext b
    exact Algebra.TensorProduct.productMap_right_apply _ _ b
  · have hml : ∀ a : (A : Type u), m.hom.hom (a ⊗ₜ[k] 1) = s.inl.hom.hom a :=
      fun a => congrArg (fun q : A ⟶ s.pt => q.hom.hom a) h₁
    have hmr : ∀ b : (B : Type u), m.hom.hom ((1 : (A : Type u)) ⊗ₜ[k] b) =
        s.inr.hom.hom b :=
      fun b => congrArg (fun q : B ⟶ s.pt => q.hom.hom b) h₂
    ext x
    show m.hom.hom x = Algebra.TensorProduct.productMap s.inl.hom.hom s.inr.hom.hom x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul a b =>
      have hsplit : (a ⊗ₜ[k] b : (A : Type u) ⊗[k] (B : Type u)) =
          (a ⊗ₜ[k] 1) * ((1 : (A : Type u)) ⊗ₜ[k] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      calc m.hom.hom (a ⊗ₜ[k] b)
          = m.hom.hom ((a ⊗ₜ[k] 1) * ((1 : (A : Type u)) ⊗ₜ[k] b)) :=
            congrArg m.hom.hom hsplit
        _ = m.hom.hom (a ⊗ₜ[k] 1) * m.hom.hom ((1 : (A : Type u)) ⊗ₜ[k] b) :=
            map_mul m.hom.hom _ _
        _ = Algebra.TensorProduct.productMap s.inl.hom.hom s.inr.hom.hom (a ⊗ₜ[k] b) := by
            rw [hml a, hmr b]
            exact (Algebra.TensorProduct.productMap_apply_tmul _ _ a b).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- The op of the tensor cofan is a binary product fan in `(FiniteEtale k)ᵒᵖ`. -/
noncomputable def tensorBinaryFanOpIsLimit :
    IsLimit ((tensorBinaryCofan A B).op) :=
  BinaryCofan.IsColimit.op (tensorBinaryCofanIsColimit A B)

end TensorCoproduct

end FiniteEtaleGalois

end ModularCurves
