/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DualPullback.OverRestriction

/-!
# Over-site restriction of restrict-site isos: the commutation square

The general over-iso induced by a restrict-site iso (`overIsoOfRestrictIso`), the
restriction of an over-site iso along an over-object (`restrictOverIso`), the native
restriction of a restrict-site iso to a smaller open (`restrictRestrictIsoNative`),
and the commutation square tying the three together
(`restrictOverIso_overIsoOfRestrictIso`).

Hoisted from `WeilPairing/FieldLeaf.lean`: the square's proof runs through the
Stage-machinery coherence `overRestrictModuleIso_comp_overFunctorEquiv`, which lives
in this file's spelling-world and default transparency; under `FieldLeaf`'s file-wide
v4.33 opacity options the assembled goal is not type-correct at the `implicit`
transparency level and every goal rewrite fails there.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **(U5-L1a 3c-iii C-rest-3a)** The general over-iso induced by a restrict-site iso
between two modules (the non-unit-target sibling of `overTrivializationOfRestrictIso`). -/
noncomputable def overIsoOfRestrictIso {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (φ : M.restrict U.ι ≅ N.restrict U.ι) :
    M.over U ≅ N.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((overFunctorEquiv U).app M ≪≫ φ ≪≫ ((overFunctorEquiv U).app N).symm)

/-- **(U5-L1a 3c-iii)** Restriction of a general over-site iso from `U` to an object
`V ⟶ U` (the non-unit-target sibling of `restrictOverTrivialization`, same three-leg
shape with the target comparison in place of the unit comparison). -/
noncomputable def restrictOverIso {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : M.over U ≅ N.over U) (V : CategoryTheory.Over U) :
    M.over V.left ≅ N.over V.left :=
  ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app M).symm ≪≫
    (_root_.SheafOfModules.overMap X.ringCatSheaf V.hom).mapIso e ≪≫
    (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf V.hom).app N

/-- **(U5-L1a 3c-iii)** The restrict-native restriction of a restrict-site iso to a
smaller open: conjugation by `restrictOpenCompIso` around the restriction functor's
image (the tree's own restriction species — the Stage-machinery's home ground). -/
noncomputable def restrictRestrictIsoNative {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (φ : M.restrict U.ι ≅ N.restrict U.ι) :
    M.restrict V.ι ≅ N.restrict V.ι :=
  (restrictOpenCompIso i).app M ≪≫
    (restrictFunctor (X.homOfLE (leOfHom i))).mapIso φ ≪≫
    ((restrictOpenCompIso i).app N).symm

/-- **(U5-L1a 3c-iii, THE COMMUTATION SQUARE)** Restricting the over-form of a
restrict-site iso is the over-form of its native restriction. Assembly from the
Stage-proven coherence `overRestrictModuleIso_comp_overFunctorEquiv` at `M` and `N`
plus naturality of `overMapCompOverEquiv`. -/
theorem restrictOverIso_overIsoOfRestrictIso {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (φ : M.restrict U.ι ≅ N.restrict U.ι) :
    restrictOverIso M N U (overIsoOfRestrictIso M N U φ) (CategoryTheory.Over.mk i) =
      overIsoOfRestrictIso M N V (restrictRestrictIsoNative M N i φ) := by
  refine Iso.ext ?_
  apply (Scheme.Modules.overEquiv V).functor.map_injective
  simp only [restrictOverIso, overIsoOfRestrictIso, restrictRestrictIsoNative,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  have hnat := (overMapCompOverEquiv (X := X) i).hom.naturality
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimage
      ((overFunctorEquiv U).hom.app M ≫ φ.hom ≫ (overFunctorEquiv U).inv.app N))
  simp only [Functor.comp_map, Functor.FullyFaithful.map_preimage,
    Functor.map_comp] at hnat
  have hcompM := overRestrictModuleIso_comp_overFunctorEquiv (X := X) M i
  have hcompN := overRestrictModuleIso_comp_overFunctorEquiv (X := X) N i
  simp only [overRestrictModuleIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc] at hcompM hcompN
  -- Blur-proof endgame: every collapse is a term-applied lemma spliced by `congrArg`
  -- under a prefix-lambda (no pattern-matching at `overFunctorEquiv`-headed nodes),
  -- and the goal is closed by defeq `exact`.
  have hcompM' : (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app M) ≫
      (overMapCompOverEquiv i).hom.app (_root_.SheafOfModules.over M U) ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).hom.app M) =
      (overFunctorEquiv V).hom.app M ≫ (restrictOpenCompIso i).hom.app M := hcompM
  have hcompN' : (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app N) ≫
      (overMapCompOverEquiv i).hom.app (_root_.SheafOfModules.over N U) ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).hom.app N) =
      (overFunctorEquiv V).hom.app N ≫ (restrictOpenCompIso i).hom.app N := hcompN
  -- hmid: the middle factor through the omc-conjugate (omc-pair collapse is safe-headed)
  have hmid := congrArg
    (fun t => t ≫ (overMapCompOverEquiv i).inv.app (_root_.SheafOfModules.over N U)) hnat
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hmid
  -- segment base equalities (term-built, no matching)
  have s1base : (restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).hom.app N) ≫
      (restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).inv.app N) = 𝟙 _ :=
    ((restrictFunctor (X.homOfLE (leOfHom i))).map_comp _ _).symm.trans
      ((congrArg (restrictFunctor (X.homOfLE (leOfHom i))).map
        (Iso.hom_inv_id_app (overFunctorEquiv U) N)).trans
          ((restrictFunctor (X.homOfLE (leOfHom i))).map_id _))
  have s2 : (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app N) ≫
      (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N) = 𝟙 _ :=
    (((Scheme.Modules.overEquiv V).functor.map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.overEquiv V).functor.map
        (Iso.inv_hom_id_app (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i) N)).trans
          ((Scheme.Modules.overEquiv V).functor.map_id _)))
  -- hFRX : (FN ≫ rocN) ≫ X = 𝟙, where X := restr gN ≫ omcN_inv ≫ G.map aN
  have hFRX := ((reassoc_of% hcompN')
      ((restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).inv.app N) ≫
        (overMapCompOverEquiv i).inv.app (_root_.SheafOfModules.over N U) ≫
        (Scheme.Modules.overEquiv V).functor.map
          ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N))).symm.trans
    ((congrArg (fun t => (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app N) ≫
        (overMapCompOverEquiv i).hom.app (_root_.SheafOfModules.over N U) ≫ t)
      ((reassoc_of% s1base)
        ((overMapCompOverEquiv i).inv.app (_root_.SheafOfModules.over N U) ≫
          (Scheme.Modules.overEquiv V).functor.map
            ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N)))).trans
      ((congrArg (fun t => (Scheme.Modules.overEquiv V).functor.map
          ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app N) ≫ t)
        (Iso.hom_inv_id_app_assoc (overMapCompOverEquiv i) (_root_.SheafOfModules.over N U)
          ((Scheme.Modules.overEquiv V).functor.map
            ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N)))).trans s2))
  -- htail : X = rocN_inv ≫ FN_inv  (flat trans-chain, all term-level)
  have tA := (Iso.inv_hom_id_app_assoc (restrictOpenCompIso i) N
    ((restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).inv.app N) ≫
      (overMapCompOverEquiv i).inv.app (_root_.SheafOfModules.over N U) ≫
      (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N))).symm
  have tB := congrArg (fun t => (restrictOpenCompIso i).inv.app N ≫ t)
    ((Iso.inv_hom_id_app_assoc (overFunctorEquiv V) N
      ((restrictOpenCompIso i).hom.app N ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).inv.app N) ≫
        (overMapCompOverEquiv i).inv.app (_root_.SheafOfModules.over N U) ≫
        (Scheme.Modules.overEquiv V).functor.map
          ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N))).symm)
  have tC := congrArg
    (fun t => (restrictOpenCompIso i).inv.app N ≫ (overFunctorEquiv V).inv.app N ≫ t) hFRX
  have tD := congrArg (fun t => (restrictOpenCompIso i).inv.app N ≫ t)
    (Category.comp_id ((overFunctorEquiv V).inv.app N))
  have htail := tA.trans (tB.trans (tC.trans tD))
  -- master chain
  have m1 := congrArg
    (fun t => (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app M) ≫ t ≫
      (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N)) hmid
  simp only [Category.assoc] at m1
  have m2 := (reassoc_of% hcompM')
    ((restrictFunctor (X.homOfLE (leOfHom i))).map φ.hom ≫
      (restrictFunctor (X.homOfLE (leOfHom i))).map ((overFunctorEquiv U).inv.app N) ≫
      (overMapCompOverEquiv i).inv.app (_root_.SheafOfModules.over N U) ≫
      (Scheme.Modules.overEquiv V).functor.map
        ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N))
  have m3 := congrArg
    (fun t => (overFunctorEquiv V).hom.app M ≫ (restrictOpenCompIso i).hom.app M ≫
      (restrictFunctor (X.homOfLE (leOfHom i))).map φ.hom ≫ t) htail
  have hfinal := m1.trans (m2.trans m3)
  -- regroup to the goal's (B ≫ C ≫ D)-bracketing and close by defeq
  have r1 := Category.assoc ((restrictOpenCompIso i).hom.app M)
    ((restrictFunctor (X.homOfLE (leOfHom i))).map φ.hom ≫ (restrictOpenCompIso i).inv.app N)
    ((overFunctorEquiv V).inv.app N)
  have r2 := congrArg (fun t => (restrictOpenCompIso i).hom.app M ≫ t)
    (Category.assoc ((restrictFunctor (X.homOfLE (leOfHom i))).map φ.hom)
      ((restrictOpenCompIso i).inv.app N) ((overFunctorEquiv V).inv.app N))
  have bridge := congrArg (fun t => (overFunctorEquiv V).hom.app M ≫ t) (r1.trans r2)
  exact hfinal.trans bridge.symm
