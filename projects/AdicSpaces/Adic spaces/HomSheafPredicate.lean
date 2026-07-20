/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».CompleteTopCommRingCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The sheaf-of-topological-rings condition for an arbitrary bundled presheaf

Wedhorn Remark 8.20's condition, stated for an **arbitrary** presheaf
`F : TopCat.Presheaf CompleteTopCommRingCat X` (P5 of the repair campaign):

* `TopCat.Presheaf.IsSheafOfTopologicalRings F` — for every topological commutative
  unital test ring `T` **in the working universe** (see the universe note below),
  the presheaf of sets `V ↦ Hom_cont(T, F(V))` has unique gluing for every open
  cover.
* `TopCat.Presheaf.IsSheafOfTopologicalRings.isSheaf` — the condition implies
  mathlib's categorical sheaf condition for `F` ([Stacks 00VR]: the categorical
  condition *is* the `Hom(E, −)`-by-`E` condition tested along the objects of
  `CompleteTopCommRingCat`, which are among the test rings).

`VObj` (`StructureSheaf.lean`) stores this condition — not merely the underlying
ring-presheaf's categorical `IsSheaf` (which forgets the topological-embedding
half of Remark 8.20).

## Universe note

The test rings `T` range over `Type u` for `X : TopCat.{u}` — "every test ring in
the working universe". This matches the categorical sheaf condition (whose test
objects are the category's objects, in `Type u`) and the cover-index universe of
mathlib's unique-gluing translation. A cross-universe generalization would require
universe-polymorphic Hom-types; the campaign records this as a deliberate policy,
not an accident (P6).
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (F : TopCat.Presheaf CompleteTopCommRingCat.{u} X)

/-- The set of continuous ring homomorphisms from a topological ring `T` into a
value of `F`. For `T` an object of the category this is literally the Hom-set. -/
abbrev ContHom (T : Type u) [CommRing T] [TopologicalSpace T]
    (W : Opens X) : Type u :=
  {g : T →+* (F.obj (op W) : Type u) // Continuous g}

/-- **Wedhorn Remark 8.20 for an arbitrary bundled presheaf**: for every
topological commutative test ring `T` (in the working universe — no completeness,
separation, or discreteness assumed) and every open cover, compatible families of
continuous ring homomorphisms into the members glue uniquely. -/
def IsSheafOfTopologicalRings : Prop :=
  ∀ (T : Type u) (_ : CommRing T) (_ : TopologicalSpace T) (_ : IsTopologicalRing T),
    ∀ {ι : Type u} (U : ι → Opens X)
      (f : ∀ i, {g : T →+* (F.obj (op (U i)) : Type u) // Continuous g}),
      (∀ i j : ι,
        (F.map (homOfLE (inf_le_left (a := U i) (b := U j))).op).1.comp (f i).1 =
        (F.map (homOfLE (inf_le_right (a := U i) (b := U j))).op).1.comp (f j).1) →
      ∃! g : {g : T →+* (F.obj (op (iSup U)) : Type u) // Continuous g},
        ∀ i, (F.map (homOfLE (le_iSup U i)).op).1.comp g.1 = (f i).1

/-- The Hom-sheaf condition implies mathlib's categorical sheaf condition
([Stacks 00VR]): the categorical condition tests `Hom(E, −)` along the objects `E`
of the category, which are among the topological test rings. -/
theorem IsSheafOfTopologicalRings.isSheaf
    (h : F.IsSheafOfTopologicalRings) : F.IsSheaf := by
  intro E
  rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr ?_
  intro ι U sf hsf
  obtain ⟨g, hg, hguniq⟩ := h E.α E.instCommRing
    (E.instUniformSpace.toTopologicalSpace) E.instIsTopologicalRing U
    (fun i => ⟨(sf i).1, (sf i).2⟩)
    (fun i j => congrArg Subtype.val (hsf i j))
  refine ⟨⟨g.1, g.2⟩, fun i => Subtype.ext (hg i), fun s' hs' => ?_⟩
  have := hguniq ⟨s'.1, s'.2⟩ (fun i => congrArg Subtype.val (hs' i))
  exact Subtype.ext (congrArg Subtype.val this)


/-- The Hom-sheaf condition implies the categorical sheaf condition of the
**underlying ring presheaf** (values in `CommRingCat`, topology forgotten): the
`CommRingCat`-condition tests `Hom(E, −)` along plain commutative rings `E`, and
equipping `E` with the discrete topology makes every ring homomorphism continuous,
so those tests are among the topological ones. -/
theorem IsSheafOfTopologicalRings.ringPresheaf_isSheaf
    (h : F.IsSheafOfTopologicalRings) :
    TopCat.Presheaf.IsSheaf (F ⋙ CompleteTopCommRingCat.forgetToCommRingCat) := by
  intro E
  rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr ?_
  intro ι U sf hsf
  letI : TopologicalSpace E.carrier := ⊥
  haveI : DiscreteTopology E.carrier := ⟨rfl⟩
  haveI : IsTopologicalRing E.carrier :=
    { continuous_add := continuous_of_discreteTopology
      continuous_mul := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  obtain ⟨g, hg, hguniq⟩ := h E.carrier inferInstance ⊥ inferInstance U
    (fun i => ⟨(sf i).hom, continuous_of_discreteTopology⟩)
    (fun i j => by
      have := hsf i j
      exact congrArg CommRingCat.Hom.hom this)
  refine ⟨CommRingCat.ofHom g.1, fun i => ?_, fun s' hs' => ?_⟩
  · exact CommRingCat.hom_ext (hg i)
  · have := hguniq ⟨s'.hom, continuous_of_discreteTopology⟩
      (fun i => congrArg CommRingCat.Hom.hom (hs' i))
    exact CommRingCat.hom_ext (congrArg Subtype.val this)

end TopCat.Presheaf
