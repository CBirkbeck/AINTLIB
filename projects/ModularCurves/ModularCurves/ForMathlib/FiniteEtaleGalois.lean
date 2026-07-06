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

end FiniteEtaleGalois

end ModularCurves
