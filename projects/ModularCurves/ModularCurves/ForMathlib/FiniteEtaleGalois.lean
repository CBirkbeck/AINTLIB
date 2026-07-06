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

end ModularCurves
