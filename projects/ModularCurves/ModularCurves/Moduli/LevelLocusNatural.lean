/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.CombinationLevel
import ModularCurves.Moduli.Representability

/-!
# Pinning and naturality of the full-level locus points dictionary (T-G3b brick 1)

**(T-E14-NAT prerequisite.)** `fullLevelLocusPointsEquiv` translates a `T`-point of the
full-level locus into a naive full level-`N` structure on the base-changed curve. The
Legendre naturality leaf ([T-E14-NAT]) needs this dictionary to be **natural in `T`**;
following the level-3 leg (`YFull.exists_pointsEquiv_family`, which threads naturality by
*pinning* rather than by an abstract chase), we record the pinning identity: the two
sections produced by the dictionary are, on the nose,

    w ≫ ι ≫ pullback.fst ≫ torsionι    and    w ≫ ι ≫ pullback.snd ≫ torsionι

read through `pullback.fst` of the base-changed curve. Naturality in `T` is then a
one-line consequence (both sides are pinned to the same morphism).
-/

-- v4.33 bump: component types coming from semireducible `baseChange*`/`pullback` defs are
-- defeq only after delta, which `rw`/`simp`/`calc` will not do at `implicit` transparency.
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- **(pinning, first component)** The first section produced by the locus dictionary is
`w ≫ ι ≫ pr₁ ≫ torsionι`, read through the base-change projection. -/
theorem fullLevelLocusPointsEquiv_fst_comp_fst (h : NIsInvertible S N) {T : Scheme.{u}}
    (g : T ⟶ S) (w : { h' : T ⟶ E.fullLevelLocus N h // h' ≫ E.fullLevelLocusπ N h = g }) :
    ((E.fullLevelLocusPointsEquiv N h g w).1.1 : T ⟶ (E.baseChange g).E) ≫
        pullback.fst E.π g =
      w.1 ≫ E.fullLevelLocusι N h ≫
        pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N := by
  rw [show ((E.fullLevelLocusPointsEquiv N h g w).1.1 : (E.baseChange g).Section) =
      E.torsionMapSection N g
        ((w.1 ≫ E.fullLevelLocusι N h) ≫ pullback.fst (E.torsionπ N) (E.torsionπ N))
        (E.pairFstπ N (w.1 ≫ E.fullLevelLocusι N h) (by rw [Category.assoc]; exact w.2))
      from rfl]
  rw [E.torsionMapSection_fst N g _ _]
  simp only [Category.assoc]

/-- **(pinning, second component)** The second section produced by the locus dictionary is
`w ≫ ι ≫ pr₂ ≫ torsionι`, read through the base-change projection. -/
theorem fullLevelLocusPointsEquiv_snd_comp_fst (h : NIsInvertible S N) {T : Scheme.{u}}
    (g : T ⟶ S) (w : { h' : T ⟶ E.fullLevelLocus N h // h' ≫ E.fullLevelLocusπ N h = g }) :
    ((E.fullLevelLocusPointsEquiv N h g w).1.2 : T ⟶ (E.baseChange g).E) ≫
        pullback.fst E.π g =
      w.1 ≫ E.fullLevelLocusι N h ≫
        pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N := by
  rw [show ((E.fullLevelLocusPointsEquiv N h g w).1.2 : (E.baseChange g).Section) =
      E.torsionMapSection N g
        ((w.1 ≫ E.fullLevelLocusι N h) ≫ pullback.snd (E.torsionπ N) (E.torsionπ N))
        (E.pairSndπ N (w.1 ≫ E.fullLevelLocusι N h) (by rw [Category.assoc]; exact w.2))
      from rfl]
  rw [E.torsionMapSection_fst N g _ _]
  simp only [Category.assoc]

/-- **(T-G3b brick 1 ★)** Naturality in `T` of the full-level locus dictionary, in the
form consumers need: restricting the locus point along `k : T' ⟶ T` restricts both
sections of the associated level structure (compared through the base-change projection,
which determines a section). -/
theorem fullLevelLocusPointsEquiv_natural_fst (h : NIsInvertible S N)
    {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (w : { h' : T ⟶ E.fullLevelLocus N h // h' ≫ E.fullLevelLocusπ N h = g }) :
    ((E.fullLevelLocusPointsEquiv N h (k ≫ g)
          ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩).1.1 :
        T' ⟶ (E.baseChange (k ≫ g)).E) ≫ pullback.fst E.π (k ≫ g) =
      k ≫ ((E.fullLevelLocusPointsEquiv N h g w).1.1 : T ⟶ (E.baseChange g).E) ≫
        pullback.fst E.π g := by
  rw [E.fullLevelLocusPointsEquiv_fst_comp_fst N h (k ≫ g)
      ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩,
    E.fullLevelLocusPointsEquiv_fst_comp_fst N h g w]
  simp only [Category.assoc]

/-- **(T-G3b brick 1 ★)** Naturality in `T`, second component. -/
theorem fullLevelLocusPointsEquiv_natural_snd (h : NIsInvertible S N)
    {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (w : { h' : T ⟶ E.fullLevelLocus N h // h' ≫ E.fullLevelLocusπ N h = g }) :
    ((E.fullLevelLocusPointsEquiv N h (k ≫ g)
          ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩).1.2 :
        T' ⟶ (E.baseChange (k ≫ g)).E) ≫ pullback.fst E.π (k ≫ g) =
      k ≫ ((E.fullLevelLocusPointsEquiv N h g w).1.2 : T ⟶ (E.baseChange g).E) ≫
        pullback.fst E.π g := by
  rw [E.fullLevelLocusPointsEquiv_snd_comp_fst N h (k ≫ g)
      ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩,
    E.fullLevelLocusPointsEquiv_snd_comp_fst N h g w]
  simp only [Category.assoc]

end EllipticCurve

/-! ## The level component of the funnel naturality square -/

section EllObj

variable {R : CommRingCat.{u}}

/-- A section of a base-changed curve is determined by its composite with the projection
to the original curve (the other component is forced to be the identity). -/
theorem section_ext_comp_fst (X : EllObj R) {T : Scheme.{u}} {g : T ⟶ X.base}
    {P Q : (X.pullbackAlong g).curve.Section}
    (hfst : (P.1 : T ⟶ pullback X.curve.π g) ≫ pullback.fst X.curve.π g =
      (Q.1 : T ⟶ pullback X.curve.π g) ≫ pullback.fst X.curve.π g) : P = Q := by
  refine Subtype.ext (pullback.hom_ext hfst ?_)
  show (P.1 : T ⟶ (X.pullbackAlong g).curve.E) ≫ (X.pullbackAlong g).curve.π =
    (Q.1 : T ⟶ (X.pullbackAlong g).curve.E) ≫ (X.pullbackAlong g).curve.π
  rw [P.2, Q.2]

/-- **(pinning of `pullSection` along a base-change comparison)** Pulling a section back
along `X.pullbackAlongMap g k` is, through the projection, precomposition with `k`. -/
theorem pullSection_pullbackAlongMap_comp_fst (X : EllObj R) {T T' : Scheme.{u}}
    (g : T ⟶ X.base) (k : T' ⟶ T) (P : (X.pullbackAlong g).curve.Section) :
    ((EllHom.pullSection R (X.pullbackAlongMap g k) P).1 : T' ⟶ pullback X.curve.π (k ≫ g)) ≫
        pullback.fst X.curve.π (k ≫ g) =
      k ≫ (P.1 : T ⟶ pullback X.curve.π g) ≫ pullback.fst X.curve.π g := by
  have htop : (X.pullbackAlongMap g k).top ≫ pullback.fst X.curve.π g =
      pullback.fst X.curve.π (k ≫ g) := by
    show pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _) (by simp) (by simp) ≫
      pullback.fst X.curve.π g = pullback.fst X.curve.π (k ≫ g)
    rw [pullback.lift_fst, Category.comp_id]
  have hlift : ((EllHom.pullSection R (X.pullbackAlongMap g k) P).1 :
        T' ⟶ (X.pullbackAlong (k ≫ g)).curve.E) ≫ (X.pullbackAlongMap g k).top =
      k ≫ (P.1 : T ⟶ (X.pullbackAlong g).curve.E) :=
    (X.pullbackAlongMap g k).isPullback.lift_fst _ _ _
  calc ((EllHom.pullSection R (X.pullbackAlongMap g k) P).1 :
          T' ⟶ pullback X.curve.π (k ≫ g)) ≫ pullback.fst X.curve.π (k ≫ g)
      = (((EllHom.pullSection R (X.pullbackAlongMap g k) P).1 :
            T' ⟶ (X.pullbackAlong (k ≫ g)).curve.E) ≫ (X.pullbackAlongMap g k).top) ≫
          pullback.fst X.curve.π g := by
        rw [Category.assoc, htop]
    _ = k ≫ (P.1 : T ⟶ pullback X.curve.π g) ≫ pullback.fst X.curve.π g := by
        rw [hlift]
        exact Category.assoc _ _ _

/-- **(T-G3b brick 2 ★)** The level component of the funnel naturality square: the locus
dictionary commutes with the base-change comparison `X.pullbackAlongMap g k`, i.e. with
`(gammaFullNaiveProblem R N).map`. -/
theorem fullLevelLocusPointsEquiv_pullSection_fst (X : EllObj R) (N : ℕ) [NeZero N]
    (h : NIsInvertible X.base N) {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (w : { h' : T ⟶ X.curve.fullLevelLocus N h //
      h' ≫ X.curve.fullLevelLocusπ N h = g }) :
    (X.curve.fullLevelLocusPointsEquiv N h (k ≫ g)
        ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩).1.1 =
      EllHom.pullSection R (X.pullbackAlongMap g k)
        (X.curve.fullLevelLocusPointsEquiv N h g w).1.1 := by
  refine section_ext_comp_fst X ?_
  rw [pullSection_pullbackAlongMap_comp_fst X g k]
  exact X.curve.fullLevelLocusPointsEquiv_natural_fst N h g k w

/-- **(T-G3b brick 2 ★)** The level component of the funnel naturality square, second
section. -/
theorem fullLevelLocusPointsEquiv_pullSection_snd (X : EllObj R) (N : ℕ) [NeZero N]
    (h : NIsInvertible X.base N) {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (w : { h' : T ⟶ X.curve.fullLevelLocus N h //
      h' ≫ X.curve.fullLevelLocusπ N h = g }) :
    (X.curve.fullLevelLocusPointsEquiv N h (k ≫ g)
        ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩).1.2 =
      EllHom.pullSection R (X.pullbackAlongMap g k)
        (X.curve.fullLevelLocusPointsEquiv N h g w).1.2 := by
  refine section_ext_comp_fst X ?_
  rw [pullSection_pullbackAlongMap_comp_fst X g k]
  exact X.curve.fullLevelLocusPointsEquiv_natural_snd N h g k w

/-- **(WP-D2c-3-H3)** The `symm` form of the two lemmas above: the locus point classifying
a base-changed level structure is the base change of the locus point classifying the
original.

This is the direction the representability naturality actually consumes, and it is where
the `symm` route is cast-free: `Equiv.sigmaCongrLeft'` (used forward in
`sigmaHomForgetEquiv`) transports the fibre predicate along `homEquiv.symm_apply_apply`, so
the *forward* composite is not definitional, whereas its inverse is. -/
theorem fullLevelLocusPointsEquiv_symm_natural (X : EllObj R) (N : ℕ) [NeZero N]
    (h : NIsInvertible X.base N) {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (L : (gammaFullNaiveProblem R N).obj (Opposite.op (X.pullbackAlong g))) :
    ((X.curve.fullLevelLocusPointsEquiv N h (k ≫ g)).symm
        ((gammaFullNaiveProblem R N).map (X.pullbackAlongMap g k).op L)).1 =
      k ≫ ((X.curve.fullLevelLocusPointsEquiv N h g).symm L).1 := by
  set w := (X.curve.fullLevelLocusPointsEquiv N h g).symm L with hw
  have hL : X.curve.fullLevelLocusPointsEquiv N h g w = L := by
    rw [hw, Equiv.apply_symm_apply]
  have hkey : X.curve.fullLevelLocusPointsEquiv N h (k ≫ g)
      ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩ =
      (gammaFullNaiveProblem R N).map (X.pullbackAlongMap g k).op L := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [← hL]
      exact fullLevelLocusPointsEquiv_pullSection_fst X N h g k w
    · rw [← hL]
      exact fullLevelLocusPointsEquiv_pullSection_snd X N h g k w
  rw [← hkey, Equiv.symm_apply_apply]

end EllObj

end ModularCurves
