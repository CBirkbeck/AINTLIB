/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LegendreDeltaRelRep
import ModularCurves.Moduli.LegendreDatumSymmetry
import ModularCurves.Moduli.AbscissaDifference
import ModularCurves.Moduli.LevelMarking
import ModularCurves.Moduli.E3DatumAssembly
import ModularCurves.GroupScheme.SqrtUnitCover
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! ## ⚠ QUARANTINED SUBTREE (B2-DECISION, board v10.342/v10.343, 2026-07-20)

This file belongs to the **Legendre D(2)-mouth subtree**, removed from every
receipt cone by the adjudicated B2 resolution: the engine's D(2) leg now runs on
the naive level-4 rigidifier (`Moduli/UniversalLevelFour.lean` +
`Moduli/LevelFourTorsor.lean`; `EngineWiring.representable_baseChange_two`).
KM 4.6.2's constant-group torsor claim for the Legendre problem is FALSE as
stated (b2_log `B2-DECISION`: over the universal Legendre base the six
marking-components are pairwise non-isomorphic quadratic étale algebras, so no
constant finite group acts fibre-transitively; the honest torsor group is a
twisted μ₂-extension of GL₂(𝔽₂)). The sorried declarations below are DOCUMENTED
NON-GOALS (kept per statement-protection protocol; a groupoid-descent engine
would be required to make the Legendre route viable — see decomposition-e4.md).
Do NOT work these sorries as receipt leaves. -/



/-!
# The `±ω` scale-torsor: gluing the square-root cover over the level-`2` locus (T-E14-AX2)

**(CHARTER-G, the terminal (G1) increment.)** This file assembles the finite étale
**scale-torsor** `Z₂ → fullLevelLocus 2` feeding the funnel
`legendreDelta_relRep_finiteEtale_of_scaleTorsor` (`Moduli/LegendreDeltaRelRep.lean`),
thereby closing `legendreDelta_relativelyRepresentable_finiteEtale`
(`Moduli/Bootstrap.lean`, KM 4.6.2's engine axiom 2 for the Legendre `δ`).

## Mathematical picture

Over `W := fullLevelLocus 2` of the universal curve, the tautological naive full
level-`2` pair `(P, Q)` is fibrewise nonzero (`pull_ne_zero_left/right_of_isNaiveFullLevel`),
so OMEGA's canonical `ω^{⊗-2}`-valued **abscissa difference** `d = x(Q) − x(P)`
(`abscissaDiff`, `Moduli/AbscissaDifference.lean`) is defined; over an atlas chart in
which `ω` is trivialized by a basis `b`, `d` trivializes to a unit `d_b ∈ Γ(W, V)ˣ`, and
`(L, b)` is a Legendre datum iff `d_b = 1` (the marking pins `x(P) = 0, x(Q) = 1`).

The `±ω` bases completing `(P, Q)` to a Legendre datum are hence the square roots
`u² = d_b⁻¹` of the twist relating two chart trivializations
(`u ↦ u·b` scales `d_b` by `u²`, `IsLegendreDatum.unit_sq_eq_one`); locally this is the
finite étale double cover `SqrtUnitCover` (`GroupScheme/SqrtUnitCover.lean`), and the
covers glue along the `ω`-cocycle by the twist `sqrtPairCongr`. The glued
`RelativeGluingData.glued` over the affine-opens-inside-charts cover of `W` is `Z₂`; it
is finite étale over `W` (locally so, `IsZariskiLocalAtTarget`) and its sections
classify the completing bases.

## Status

The funnel-assembly is proven here (`legendreDelta_relRep_finiteEtale`): given the
scale-torsor package (`ScaleTorsorData`, the funnel's four inputs bundled with the
sections classification as `Nonempty`-equivalences), `Bootstrap`'s AX2 statement
follows by `Classical`-extraction and the funnel. The geometric construction of the
package — the glued cover and the per-fibre sections classification — is isolated as the
single residual `exists_scaleTorsorData` (the `(2b)/(3)/(4)` build map: the Spec-pullback
squares, the `RelativeGluingData` over the chart cover, and the sheaf-glued
square-root/`b`↔`u` dictionary).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

open EllipticCurve

variable (R : CommRingCat.{u})

/-! ## The universal abscissa difference over the level-`2` locus (build-step 4 entry)

The geometric data feeding the residual's (unbuilt) proof: over `W := fullLevelLocus 2`,
the tautological naive full level-`2` pair `(P, Q)` is fibrewise nonzero
(`pull_ne_zero_left/right_of_isNaiveFullLevel`, `Moduli/LevelMarking.lean`), so OMEGA's
`ω^{⊗-2}`-valued abscissa difference `d = x(Q) − x(P)` (`abscissaDiff`,
`Moduli/AbscissaDifference.lean`) is defined. Its chart trivializations are the units
`d_b` whose square roots are the completing `±ω` bases; `univAbscissaDiff` is that `d`,
axiom-clean. -/

/-- The universal curve over the level-`2` locus `W := fullLevelLocus 2`: the base change
of `X.curve` along the finite étale structure map `W → X.base`. -/
noncomputable def locusCurve (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    EllipticCurve (X.curve.fullLevelLocus 2 h2) :=
  X.curve.baseChange (X.curve.fullLevelLocusπ 2 h2)

/-- The tautological naive full level-`2` pair over the locus: the image of the identity
locus point under the classifying equivalence. -/
noncomputable def tautPair (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    { PQ : (locusCurve R X h2).Section × (locusCurve R X h2).Section //
      (locusCurve R X h2).IsNaiveFullLevel 2 PQ.1 PQ.2 } :=
  X.curve.fullLevelLocusPointsEquiv 2 h2 (X.curve.fullLevelLocusπ 2 h2)
    ⟨𝟙 _, Category.id_comp _⟩

/-- **The universal abscissa difference** `d = x(Q) − x(P)` over the level-`2` locus: the
canonical `ω^{⊗-2}`-valued section of OMEGA's `abscissaDiff` for the tautological pair
(fibrewise nonzero by the locus condition). This is the section whose glued square-root
cover is the `±ω` scale-torsor `Z₂` of `ScaleTorsorData`. Axiom-clean. -/
noncomputable def univAbscissaDiff (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    ((omegaCocycle (locusCurve R X h2).toEllipticCurveGeom).zpow (-2)).sections ⊤ :=
  abscissaDiff (G := (locusCurve R X h2).toEllipticCurveGeom)
    (σP := ((tautPair R X h2).1.1 : _ ⟶ _))
    (σQ := ((tautPair R X h2).1.2 : _ ⟶ _))
    (tautPair R X h2).1.1.2 (tautPair R X h2).1.2.2
    (fun k _ _ t => (locusCurve R X h2).pull_ne_zero_left_of_isNaiveFullLevel 2
      one_lt_two (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2)
      (tautPair R X h2).2 k t)
    (fun k _ _ t => (locusCurve R X h2).pull_ne_zero_right_of_isNaiveFullLevel 2
      one_lt_two (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2)
      (tautPair R X h2).2 k t)

/-! ## The scale-torsor package and the funnel assembly -/

/-- **(T-G3b)** The **natural** sections-classification family of a scale-torsor: for each
`g` and each locus point `w` over `g`, a bijection between the `T`-sections of `Z₂` over
`w` and the `ω`-bases completing the corresponding level structure to a Legendre datum,
*compatible with restriction along `k : T' ⟶ T`*. The naturality clause is stated in
congr-friendly form (the restricted locus point and section are supplied together with the
equations identifying them) so that no dependent rewrite across
`(k ≫ h) ≫ q = k ≫ (h ≫ q)` is needed downstream. -/
structure ScaleTorsorSpec (X : EllObj R) (h2 : NIsInvertible X.base 2)
    (Z₂ : Scheme.{u}) (q : Z₂ ⟶ X.curve.fullLevelLocus 2 h2) where
  /-- The classifying bijections. -/
  toFun : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
    (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
      w ≫ X.curve.fullLevelLocusπ 2 h2 = g }),
    { s : T ⟶ Z₂ // s ≫ q = w.1 } ≃
      { b : OmegaBasis (X.pullbackAlong g).curve.toEllipticCurveGeom //
        IsLegendreDatum (X.pullbackAlong g)
          (X.curve.fullLevelLocusPointsEquiv 2 h2 g w) b }
  /-- Naturality in `T`. -/
  nat : ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
      w ≫ X.curve.fullLevelLocusπ 2 h2 = g })
    (s : { s : T ⟶ Z₂ // s ≫ q = w.1 })
    (w' : { w : T' ⟶ X.curve.fullLevelLocus 2 h2 //
      w ≫ X.curve.fullLevelLocusπ 2 h2 = k ≫ g })
    (_ : w'.1 = k ≫ w.1)
    (s' : { s : T' ⟶ Z₂ // s ≫ q = w'.1 })
    (_ : s'.1 = k ≫ s.1),
    (toFun (k ≫ g) w' s').1 =
      omegaBasisMap (X.pullbackAlongMap g k) (toFun g w s).1

/-- **The scale-torsor package** feeding the funnel `legendreDelta_relRep_finiteEtale_of_scaleTorsor`:
a finite étale cover `Z₂ → fullLevelLocus 2` whose `T`-sections over a locus point `w`
(lying over `g : T ⟶ X.base`) classify the `ω`-bases completing the corresponding level
structure to a Legendre datum. The sections classification is packaged as a family of
`Nonempty`-equivalences (the honest witnesses are produced by the sheaf-glued
square-root dictionary; `Classical.choice` promotes them to the funnel's `Equiv`
family). -/
structure ScaleTorsorData (X : EllObj R) (h2 : NIsInvertible X.base 2) where
  /-- The total space of the scale-torsor. -/
  Z₂ : Scheme.{u}
  /-- The finite étale structure map to the level-`2` locus. -/
  q : Z₂ ⟶ X.curve.fullLevelLocus 2 h2
  /-- Finiteness of the cover. -/
  isFinite : IsFinite q
  /-- Étaleness of the cover. -/
  etale : Etale q
  /-- The per-fibre sections classification, as a **natural** family: sections of `Z₂` over
  a locus point `w` correspond to the `ω`-bases making `(L_w, b)` a Legendre datum, and the
  correspondence commutes with restriction along `k : T' ⟶ T` (T-G3b: without this the
  funnel produces only a `Nonempty`-per-`g` family, which cannot be assembled into a
  `RelRepData`). -/
  spec : Nonempty (ScaleTorsorSpec R X h2 Z₂ q)

/-! ## Step-(iv) assembly infrastructure (banked)

The sections classification `scaleTorsor_spec` is a bijection between two `μ₂`-pseudotorsors
— on the left the `T`-sections of the glued square-root cover (the two sheets of the double
cover, `IsLegendreDatum.neg` on the datum side), on the right the `ω`-bases completing the
level structure to a Legendre datum (pinned to a `μ₂`-torsor by
`IsLegendreDatum.unit_sq_eq_one` + `OmegaBasis.existsUnique_unit_smul`). The two helpers
below are the generic and the right-hand-side halves of that final assembly, both
sorry-free; see the note on `scaleTorsor_spec` for the residual left-hand-side gap. -/

/-- A type carrying a free, transitive `M`-action (a torsor, once a basepoint is fixed) is
equivalent to `M`: `a ↦ the unique m with m • a₀ = a`. Only freeness and transitivity
*at the basepoint* `a₀` are used. -/
noncomputable def Equiv.ofBasepointTorsor {M A : Type*} (act : M → A → A) (a₀ : A)
    (free : ∀ m m' : M, act m a₀ = act m' a₀ → m = m')
    (trans : ∀ a : A, ∃ m, act m a₀ = a) : A ≃ M where
  toFun a := (trans a).choose
  invFun m := act m a₀
  left_inv a := (trans a).choose_spec
  right_inv m := free _ _ (trans (act m a₀)).choose_spec

/-- **(Step (iv) — the generic torsor-matching combinator.)** Two `M`-torsors that are
simultaneously (non)empty are equinumerous. This reduces the sections classification to:
each side is a free transitive `μ₂`-set, and one side is nonempty iff the other is. -/
theorem nonempty_equiv_of_pseudotorsor {M A B : Type*}
    (actA : M → A → A) (actB : M → B → B)
    (freeA : ∀ (a₀ : A) (m m' : M), actA m a₀ = actA m' a₀ → m = m')
    (transA : ∀ a a' : A, ∃ m, actA m a = a')
    (freeB : ∀ (b₀ : B) (m m' : M), actB m b₀ = actB m' b₀ → m = m')
    (transB : ∀ b b' : B, ∃ m, actB m b = b')
    (hAB : Nonempty A ↔ Nonempty B) : Nonempty (A ≃ B) := by
  by_cases hA : Nonempty A
  · obtain ⟨a₀⟩ := hA
    obtain ⟨b₀⟩ := hAB.mp ⟨a₀⟩
    exact ⟨(Equiv.ofBasepointTorsor actA a₀ (freeA a₀) (fun a => transA a₀ a)).trans
      (Equiv.ofBasepointTorsor actB b₀ (freeB b₀) (fun b => transB b₀ b)).symm⟩
  · have hB : ¬ Nonempty B := fun h => hA (hAB.mpr h)
    rw [not_nonempty_iff] at hA hB
    exact ⟨Equiv.equivOfIsEmpty A B⟩

/-- **(Step (iv) — the right-hand-side `μ₂`-torsor pinning.)** Any two `ω`-bases completing
the same level structure to a Legendre datum are connected by a unique global unit `g`
(`OmegaBasis.existsUnique_unit_smul`), and that unit is a square root of one
(`IsLegendreDatum.unit_sq_eq_one`): the transitivity input of `nonempty_equiv_of_pseudotorsor`
for the basis side. -/
theorem isLegendreDatum_exists_connecting_sqrtOne {X : EllObj R}
    (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    {L : X.curve.FullLevelPt 2} {b b' : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (hD' : IsLegendreDatum X L b') :
    ∃ g : Γ(X.base, ⊤)ˣ, g • b = b' ∧ g ^ 2 = 1 := by
  obtain ⟨g, hg, -⟩ := OmegaBasis.existsUnique_unit_smul b b'
  exact ⟨g, hg, IsLegendreDatum.unit_sq_eq_one h2 hD hD' g hg⟩

/-- **(Step (iv) — the right-hand-side `μ₂`-action.)** The subgroup `μ₂ = {g : Γ(S,⊤)ˣ // g² = 1}`
acts on the `ω`-bases completing a level structure `L` to a Legendre datum: `g • b`, which stays
a Legendre datum by sublemma B1 (`IsLegendreDatum.smul_of_sq_eq_one`). This is the `actB` input of
`nonempty_equiv_of_pseudotorsor` for the basis side. -/
noncomputable def rhsMuTwoAct {X : EllObj R} (L : X.curve.FullLevelPt 2) :
    {g : Γ(X.base, ⊤)ˣ // g ^ 2 = 1} →
      {b : OmegaBasis X.curve.toEllipticCurveGeom // IsLegendreDatum X L b} →
      {b : OmegaBasis X.curve.toEllipticCurveGeom // IsLegendreDatum X L b} :=
  fun g b => ⟨g.1 • b.1, b.2.smul_of_sq_eq_one g.1 g.2⟩

/-- **(Step (iv) — RHS freeness.)** The `μ₂`-action on Legendre-completing bases is free: if
`g • b₀ = g' • b₀` then `g = g'`, since the `ω`-bases form a pseudotorsor under the global units
(`OmegaBasis.existsUnique_unit_smul`). -/
theorem rhsMuTwoAct_free {X : EllObj R} (L : X.curve.FullLevelPt 2)
    (b₀ : {b : OmegaBasis X.curve.toEllipticCurveGeom // IsLegendreDatum X L b})
    (g g' : {g : Γ(X.base, ⊤)ˣ // g ^ 2 = 1})
    (h : rhsMuTwoAct R L g b₀ = rhsMuTwoAct R L g' b₀) : g = g' := by
  apply Subtype.ext
  have h1 : g.1 • b₀.1 = g'.1 • b₀.1 := congrArg Subtype.val h
  exact (OmegaBasis.existsUnique_unit_smul b₀.1 (g.1 • b₀.1)).unique rfl h1.symm

/-- **(Step (iv) — RHS transitivity.)** The `μ₂`-action on Legendre-completing bases is
transitive: any two are connected by a square root of one
(`isLegendreDatum_exists_connecting_sqrtOne`). Together with `rhsMuTwoAct_free` this exhibits the
basis side as a free transitive `μ₂`-set. -/
theorem rhsMuTwoAct_trans {X : EllObj R} (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (L : X.curve.FullLevelPt 2)
    (b b' : {b : OmegaBasis X.curve.toEllipticCurveGeom // IsLegendreDatum X L b}) :
    ∃ g, rhsMuTwoAct R L g b = b' := by
  obtain ⟨g, hg, hg2⟩ := isLegendreDatum_exists_connecting_sqrtOne R h2 b.2 b'.2
  exact ⟨⟨g, hg2⟩, Subtype.ext hg⟩

/-- **(Piece 1 — the per-piece deck involution.)** The `A`-algebra automorphism `u ↦ -u`
of a single square-root piece `(sqrtPair d).Ring`: the `μ₂`-deck generator of the sqrt
double cover (`(-u)² = u² = d`, so `-u` is again a square root). This is the local
`sqrtPairCongr`-style sign flip that glues to the deck involution of the scale-torsor. -/
noncomputable def sqrtNegAut {A : Type u} [CommRing A] (d : Aˣ) (h2 : IsUnit (2 : A)) :
    (sqrtPair d).Ring ≃ₐ[A] (sqrtPair d).Ring := by
  have h2R : IsUnit (2 : (sqrtPair d).Ring) := by
    have := h2.map (algebraMap A (sqrtPair d).Ring); rwa [map_ofNat] at this
  have hmap : (sqrtPair d).HasMap (-(sqrtPair d).X) := by
    rw [sqrtPair_hasMap_iff _ h2R, show (-(sqrtPair d).X) ^ 2 = (sqrtPair d).X ^ 2 from by ring,
      sqrtPair_X_sq]
  refine AlgEquiv.ofAlgHom ((sqrtPair d).lift (-(sqrtPair d).X) hmap)
    ((sqrtPair d).lift (-(sqrtPair d).X) hmap) ?_ ?_ <;>
    · refine StandardEtalePair.algHom_ext ?_
      rw [AlgHom.comp_apply, StandardEtalePair.lift_X, map_neg, StandardEtalePair.lift_X,
        neg_neg, AlgHom.id_apply]

/-- `sqrtNegAut` sends the root to its negative. -/
theorem sqrtNegAut_X {A : Type u} [CommRing A] (d : Aˣ) (h2 : IsUnit (2 : A)) :
    sqrtNegAut d h2 (sqrtPair d).X = -(sqrtPair d).X := by
  have h2R : IsUnit (2 : (sqrtPair d).Ring) := by
    have := h2.map (algebraMap A (sqrtPair d).Ring); rwa [map_ofNat] at this
  have hmap : (sqrtPair d).HasMap (-(sqrtPair d).X) := by
    rw [sqrtPair_hasMap_iff _ h2R, show (-(sqrtPair d).X) ^ 2 = (sqrtPair d).X ^ 2 from by ring,
      sqrtPair_X_sq]
  exact (sqrtPair d).lift_X (-(sqrtPair d).X) hmap

/-- `sqrtNegAut` fixes the base ring (it is an `A`-algebra map). -/
theorem sqrtNegAut_algebraMap {A : Type u} [CommRing A] (d : Aˣ) (h2 : IsUnit (2 : A))
    (a : A) : sqrtNegAut d h2 (algebraMap A (sqrtPair d).Ring a) =
      algebraMap A (sqrtPair d).Ring a :=
  AlgEquiv.commutes _ a

/-! ## The build: the glued square-root cover

The carrier of the scale-torsor is built as a mathlib `RelativeGluingData` over the
locally directed cover of `W := fullLevelLocus 2` by the affine opens contained in
`ω`-atlas charts. Over an index `(V, i)` (an affine open `V` inside the chart `U i`),
the piece is the affine square-root cover `Spec (Γ(V)[u]/(u² − d_i|_V))` of the `i`-th
chart component of the universal abscissa difference; for `(V, i) ≤ (V', j)` the
transition map rescales the root by the `ω`-cocycle unit `u_{ij}` (which conjugates the
two trivializations of `d`, `chartUnit_compat`). Functoriality is the cocycle identity,
and each transition square over `V ≤ V'` is a base-change square of affines. -/

section TorsorBuild

open TopologicalSpace Scheme

variable (X : EllObj R) (h2 : NIsInvertible X.base 2)

/-- The level-`2` locus (reducible shorthand for the build). -/
private noncomputable abbrev locusW : Scheme.{u} := X.curve.fullLevelLocus 2 h2

/-- The `ω`-transition cocycle of the locus curve (reducible shorthand). -/
private noncomputable abbrev locusCocycle : Scheme.UnitCocycle (locusW R X h2) :=
  omegaCocycle (locusCurve R X h2).toEllipticCurveGeom

/-- `2` is a unit in every section ring of the level-`2` locus (transfer of
`NIsInvertible X.base 2` along the structure map, then restriction). -/
private theorem isUnit_two_res (V : (locusW R X h2).Opens) :
    IsUnit (2 : Γ(locusW R X h2, V)) := by
  have h := (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2).map
    (Scheme.resLE (le_top : V ≤ ⊤))
  rwa [map_natCast] at h

/-- **(LEAF-U, discharged.)** Each chart component of the universal abscissa
difference is a unit: `d_i = x(Q)_i − x(P)_i` is fibrewise nonvanishing on the
level-`2` locus, because at a geometric point `t` a vanishing abscissa difference
forces `Q̄ ∈ {±P̄}` (two points of a Weierstrass fibre with equal `x` are equal or
negative, `WeierstrassCurve.Affine.Y_eq_of_X_eq`), which contradicts the locus
condition (`pull_ne_pm_of_isNaiveFullLevel`).

Proof: reduce to residue-field nonvanishing (`isUnit_of_forall_algebraMap_residueField_ne_zero`
after `IsUnit.map` through the chart restriction), read the marked chart coordinates as
the model points via `markedCoordsAt_marksAt` + the `chartPointsEquiv`/`modelPointAddEquiv`
dictionary, then apply the general marked-pair certificate `isUnit_x_diff_of_marked_pair`
(the general-marking analogue of `isUnit_x_of_marked_pair`). -/
private theorem isUnit_univAbscissaDiff_component (i : (locusCocycle R X h2).ι) :
    IsUnit ((univAbscissaDiff R X h2).1 i) := by
  rw [univAbscissaDiff, abscissaDiff_component]
  refine IsUnit.map (Scheme.resLE _) ?_
  obtain ⟨heqP, hMeqP⟩ := markedCoordsAt_marksAt
    (G := (locusCurve R X h2).toEllipticCurveGeom) (tautPair R X h2).1.1.2
    (fun k _ _ t => (locusCurve R X h2).pull_ne_zero_left_of_isNaiveFullLevel 2
      one_lt_two (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2)
      (tautPair R X h2).2 k t) i
  obtain ⟨heqQ, hMeqQ⟩ := markedCoordsAt_marksAt
    (G := (locusCurve R X h2).toEllipticCurveGeom) (tautPair R X h2).1.2.2
    (fun k _ _ t => (locusCurve R X h2).pull_ne_zero_right_of_isNaiveFullLevel 2
      one_lt_two (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2)
      (tautPair R X h2).2 k t) i
  refine isUnit_x_diff_of_marked_pair _ heqP hMeqP heqQ hMeqQ (fun k _ _ t => ?_)
  exact (locusCurve R X h2).pull_ne_pm_of_isNaiveFullLevel 2 one_lt_two
    (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2) (tautPair R X h2).2 k t

/-- The index of the square-root gluing cover: an affine open of the locus together
with an `ω`-atlas chart containing it. -/
private noncomputable def glueIdx : Type u :=
  { p : (locusW R X h2).affineOpens × (locusCocycle R X h2).ι //
    p.1.1 ≤ (locusCocycle R X h2).U p.2 }

/-- Indices are ordered by inclusion of the underlying affine opens (the chart choice
is not part of the order). -/
private noncomputable instance : Preorder (glueIdx R X h2) :=
  Preorder.lift (fun p => p.1.1)

/-- The locally directed open cover of the level-`2` locus by the affine opens
contained in `ω`-atlas charts. -/
private noncomputable def glueCover : (locusW R X h2).OpenCover where
  I₀ := glueIdx R X h2
  X p := p.1.1.1
  f p := p.1.1.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := (locusCocycle R X h2).covers x
    obtain ⟨V₀, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (locusCocycle R X h2).U i from hi)
    exact ⟨⟨(⟨V₀, hVaff⟩, i), hVle⟩, ⟨x, hxV⟩, rfl⟩

private theorem glueCover_f_opensRange (p : glueIdx R X h2) :
    ((glueCover R X h2).f p).opensRange = p.1.1.1 :=
  Scheme.Opens.opensRange_ι _

private instance : Preorder (glueCover R X h2).I₀ :=
  inferInstanceAs (Preorder (glueIdx R X h2))

/-- The cover is locally directed: its images form a basis (affine opens inside charts
are cofinal in all opens, since the charts cover and affine opens are a basis). -/
private noncomputable instance : (glueCover R X h2).LocallyDirected := by
  refine Scheme.Cover.LocallyDirected.ofIsBasisOpensRange (fun {p q} => ?_) ?_
  · rw [glueCover_f_opensRange, glueCover_f_opensRange]
    exact Iff.rfl
  · rw [Opens.isBasis_iff_nbhd]
    intro U x hxU
    obtain ⟨i, hi⟩ := (locusCocycle R X h2).covers x
    obtain ⟨V₀, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ U ⊓ (locusCocycle R X h2).U i from ⟨hxU, hi⟩)
    refine ⟨V₀, ⟨⟨(⟨V₀, hVaff⟩, i), hVle.trans inf_le_right⟩, ?_⟩, hxV,
      hVle.trans inf_le_left⟩
    exact glueCover_f_opensRange R X h2 _

/-- The chart unit of an index: the universal abscissa difference, trivialized in the
`i`-th chart and restricted to `V`, as a unit (`isUnit_univAbscissaDiff_component`). -/
private noncomputable def chartUnit (p : glueIdx R X h2) : Γ(locusW R X h2, p.1.1.1)ˣ :=
  ((isUnit_univAbscissaDiff_component R X h2 p.1.2).map
    (Scheme.resLE (le_inf le_top p.2))).unit

private theorem chartUnit_val (p : glueIdx R X h2) :
    (chartUnit R X h2 p).val =
      Scheme.resLE (le_inf le_top p.2) ((univAbscissaDiff R X h2).1 p.1.2) :=
  rfl

/-- The transition twist of a pair of indices `p ≤ q`: the `ω`-cocycle unit
`u_{i_p, i_q}` restricted to the smaller open `V_p`. -/
private noncomputable def twistUnit (p q : glueIdx R X h2) (h : p ≤ q) :
    Γ(locusW R X h2, p.1.1.1)ˣ :=
  Scheme.resUnit (le_inf p.2 ((show p.1.1.1 ≤ q.1.1.1 from h).trans q.2))
    ((locusCocycle R X h2).u p.1.2 q.1.2)

/-- **(LEAF-COMPAT, discharged.)** The trivialization comparison: on the smaller open,
the `q`-chart unit is the square of the transition twist times the `p`-chart unit — the
`ω^{⊗-2}`-cocycle compatibility of the universal abscissa difference, restricted to `V_p`.

Proof: restrict the `Compatible ⊤` field `(univAbscissaDiff R X h2).2 p.1.2 q.1.2` (i.e.
`abscissaDiff_compatible`) to `V_p` via `congrArg (resLE hVp)`, normalizing the nested
restrictions (`Scheme.resLE_resLE`, `Scheme.resLE_resUnit_val`, `UnitCocycle.zpow_u`). The
compat gives `d_p = (c.u p q)^{⊗-2} · d_q`, whence the unit identity
`chartUnit p = twistUnit^{-2} · resUnit (chartUnit q)` (via `Units.ext`, matching through a
term-mode `map_zpow` to sidestep the `presheaf`-transparency landmine); the goal is its
`group`-rearrangement `resUnit (chartUnit q) = twistUnit² · chartUnit p`. -/
private theorem chartUnit_compat (p q : glueIdx R X h2) (h : p ≤ q) :
    Scheme.resUnit (show p.1.1.1 ≤ q.1.1.1 from h) (chartUnit R X h2 q) =
      twistUnit R X h2 p q h ^ 2 * chartUnit R X h2 p := by
  have key : chartUnit R X h2 p =
      twistUnit R X h2 p q h ^ (-2 : ℤ) *
        Scheme.resUnit (show p.1.1.1 ≤ q.1.1.1 from h) (chartUnit R X h2 q) := by
    apply Units.ext
    set c := (omegaCocycle (locusCurve R X h2).toEllipticCurveGeom).zpow (-2) with hc_def
    have hVp : p.1.1.1 ≤ (⊤ ⊓ c.U p.1.2) ⊓ c.U q.1.2 :=
      le_inf (le_inf le_top p.2) ((show p.1.1.1 ≤ q.1.1.1 from h).trans q.2)
    have hc := congrArg (⇑(Scheme.resLE hVp)) ((univAbscissaDiff R X h2).2 p.1.2 q.1.2)
    rw [Scheme.resLE_resLE, map_mul, Scheme.resLE_resUnit_val, Scheme.resLE_resLE,
      UnitCocycle.zpow_u] at hc
    have hz := map_zpow
      (Scheme.resUnit (le_inf p.2 ((show p.1.1.1 ≤ q.1.1.1 from h).trans q.2)))
      ((locusCocycle R X h2).u p.1.2 q.1.2) (-2 : ℤ)
    rw [Units.val_mul, chartUnit_val, Scheme.resUnit_val, chartUnit_val, Scheme.resLE_resLE,
      twistUnit, ← hz]
    exact hc
  rw [key]; group

/-! ### The transition ring maps and the piece functor -/

/-- `2` is a unit in each square-root piece ring. -/
private theorem isUnit_two_sqrtRing (p : glueIdx R X h2) :
    IsUnit (2 : (sqrtPair (chartUnit R X h2 p)).Ring) := by
  have h := (isUnit_two_res R X h2 p.1.1.1).map
    (algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring)
  rwa [map_ofNat] at h

/-- The transition ring map of the square-root pieces for `p ≤ q`: the
`Γ(V_q)`-algebra map determined by `X_q ↦ u_{pq}·X_p` (rescaling the root by the
`ω`-cocycle twist), over the restriction `Γ(V_q) → Γ(V_p)`; well-defined by
`chartUnit_compat`. -/
private noncomputable def transRingHom (p q : glueIdx R X h2) (h : p ≤ q) :
    (sqrtPair (chartUnit R X h2 q)).Ring →+* (sqrtPair (chartUnit R X h2 p)).Ring :=
  letI : Algebra ↥Γ(locusW R X h2, q.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring :=
    ((algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring).comp
      (Scheme.resLE (show p.1.1.1 ≤ q.1.1.1 from h))).toAlgebra
  ((sqrtPair (chartUnit R X h2 q)).lift
    (algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring
        (twistUnit R X h2 p q h).val *
      (sqrtPair (chartUnit R X h2 p)).X)
    (by
      rw [sqrtPair_hasMap_iff _ (isUnit_two_sqrtRing R X h2 p)]
      rw [mul_pow, sqrtPair_X_sq, ← map_pow, ← map_mul]
      show _ = ((algebraMap ↥Γ(locusW R X h2, p.1.1.1)
          (sqrtPair (chartUnit R X h2 p)).Ring).comp
        (Scheme.resLE (show p.1.1.1 ≤ q.1.1.1 from h))) (chartUnit R X h2 q).val
      rw [RingHom.comp_apply]
      congr 1
      have hc := congrArg Units.val (chartUnit_compat R X h2 p q h)
      rw [Scheme.resUnit_val, Units.val_mul, Units.val_pow_eq_pow_val] at hc
      exact hc.symm)).toRingHom

private theorem transRingHom_algebraMap (p q : glueIdx R X h2) (h : p ≤ q)
    (a : ↥Γ(locusW R X h2, q.1.1.1)) :
    transRingHom R X h2 p q h
        (algebraMap ↥Γ(locusW R X h2, q.1.1.1) (sqrtPair (chartUnit R X h2 q)).Ring a) =
      algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring
        (Scheme.resLE (show p.1.1.1 ≤ q.1.1.1 from h) a) := by
  letI : Algebra ↥Γ(locusW R X h2, q.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring :=
    ((algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring).comp
      (Scheme.resLE (show p.1.1.1 ≤ q.1.1.1 from h))).toAlgebra
  exact AlgHom.commutes _ a

private theorem transRingHom_comp_algebraMap (p q : glueIdx R X h2) (h : p ≤ q) :
    (transRingHom R X h2 p q h).comp
        (algebraMap ↥Γ(locusW R X h2, q.1.1.1) (sqrtPair (chartUnit R X h2 q)).Ring) =
      (algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring).comp
        (Scheme.resLE (show p.1.1.1 ≤ q.1.1.1 from h)) :=
  RingHom.ext fun a => transRingHom_algebraMap R X h2 p q h a

private theorem transRingHom_X (p q : glueIdx R X h2) (h : p ≤ q) :
    transRingHom R X h2 p q h (sqrtPair (chartUnit R X h2 q)).X =
      algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring
          (twistUnit R X h2 p q h).val *
        (sqrtPair (chartUnit R X h2 p)).X := by
  letI : Algebra ↥Γ(locusW R X h2, q.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring :=
    ((algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring).comp
      (Scheme.resLE (show p.1.1.1 ≤ q.1.1.1 from h))).toAlgebra
  exact (sqrtPair (chartUnit R X h2 q)).lift_X
    (algebraMap ↥Γ(locusW R X h2, p.1.1.1) (sqrtPair (chartUnit R X h2 p)).Ring
        (twistUnit R X h2 p q h).val *
      (sqrtPair (chartUnit R X h2 p)).X) _

/-- Two ring maps out of a square-root algebra agreeing on the base ring and on the
root coincide (`StandardEtalePair.hom_ext` after transporting both to algebra maps
over the base via `RingHom.toAlgebra`). -/
private theorem sqrtRingHom_ext {A S : Type u} [CommRing A] [CommRing S] {d : Aˣ}
    {f g : (sqrtPair d).Ring →+* S}
    (halg : ∀ a : A,
      f (algebraMap A (sqrtPair d).Ring a) = g (algebraMap A (sqrtPair d).Ring a))
    (hX : f (sqrtPair d).X = g (sqrtPair d).X) : f = g := by
  letI : Algebra A S := (f.comp (algebraMap A (sqrtPair d).Ring)).toAlgebra
  have hfg : (⟨f, fun a => rfl⟩ : (sqrtPair d).Ring →ₐ[A] S) =
      ⟨g, fun a => (halg a).symm⟩ :=
    StandardEtalePair.hom_ext hX
  exact congrArg AlgHom.toRingHom hfg

/-- The value form of the twist cocycle: restricting the `(q,r)`-twist to `V_p` and
multiplying by the `(p,q)`-twist gives the `(p,r)`-twist (`u_cocycle`, restricted). -/
private theorem twistUnit_cocycle (p q r : glueIdx R X h2) (hpq : p ≤ q) (hqr : q ≤ r) :
    Scheme.resLE (show p.1.1.1 ≤ q.1.1.1 from hpq) (twistUnit R X h2 q r hqr).val *
      (twistUnit R X h2 p q hpq).val = (twistUnit R X h2 p r (hpq.trans hqr)).val := by
  have hV : p.1.1.1 ≤ ((locusCocycle R X h2).U p.1.2 ⊓ (locusCocycle R X h2).U q.1.2)
      ⊓ (locusCocycle R X h2).U r.1.2 :=
    le_inf (le_inf p.2 ((show p.1.1.1 ≤ q.1.1.1 from hpq).trans q.2))
      ((show p.1.1.1 ≤ r.1.1.1 from hpq.trans hqr).trans r.2)
  have hcoc := congrArg (fun u : Γ(locusW R X h2, _)ˣ => Scheme.resLE hV u.val)
    ((locusCocycle R X h2).u_cocycle p.1.2 q.1.2 r.1.2)
  simp only [twistUnit, Units.val_mul, Scheme.resUnit_val, map_mul,
    Scheme.resLE_resLE] at hcoc ⊢
  rw [mul_comm]
  exact hcoc

private theorem transRingHom_refl (p : glueIdx R X h2) :
    transRingHom R X h2 p p le_rfl = RingHom.id _ := by
  refine sqrtRingHom_ext (fun a => ?_) ?_
  · rw [transRingHom_algebraMap, RingHom.id_apply, Scheme.resLE_rfl]
  · rw [transRingHom_X, RingHom.id_apply]
    have ht : twistUnit R X h2 p p le_rfl = 1 := by
      simp only [twistUnit, (locusCocycle R X h2).u_self p.1.2, map_one]
    rw [ht, Units.val_one, map_one, one_mul]

private theorem transRingHom_comp (p q r : glueIdx R X h2) (hpq : p ≤ q) (hqr : q ≤ r) :
    (transRingHom R X h2 p q hpq).comp (transRingHom R X h2 q r hqr) =
      transRingHom R X h2 p r (hpq.trans hqr) := by
  refine sqrtRingHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, transRingHom_algebraMap, transRingHom_algebraMap,
      transRingHom_algebraMap, Scheme.resLE_resLE]
  · rw [RingHom.comp_apply, transRingHom_X, map_mul, transRingHom_algebraMap,
      transRingHom_X, transRingHom_X, ← mul_assoc, ← map_mul,
      twistUnit_cocycle R X h2 p q r hpq hqr]

/-- The piece functor of the gluing datum: over the index `(V, i)`, the affine
square-root cover `Spec (Γ(V)[u]/(u² − d_i|_V))`; transitions by `transRingHom`. -/
private noncomputable def glueFunctor : glueIdx R X h2 ⥤ Scheme.{u} where
  obj p := Spec (CommRingCat.of (sqrtPair (chartUnit R X h2 p)).Ring)
  map {p q} f := Spec.map (CommRingCat.ofHom (transRingHom R X h2 p q (leOfHom f)))
  map_id p := by
    rw [transRingHom_refl, CommRingCat.ofHom_id, Spec.map_id]
  map_comp {p q r} f g := by
    rw [← transRingHom_comp R X h2 p q r (leOfHom f) (leOfHom g), CommRingCat.ofHom_comp,
      Spec.map_comp]

/-! ### The natural transformation to the cover and the gluing datum -/

/-- Restriction-compatibility of the affine-open `Spec` presentations: `Spec` of the
restriction map composes with `fromSpec` to `fromSpec` (mathlib's
`IsAffineOpen.map_fromSpec`). -/
private theorem specMap_resLE_fromSpec {W' : Scheme.{u}} {V V' : W'.affineOpens}
    (h : V.1 ≤ V'.1) :
    Spec.map (CommRingCat.ofHom (Scheme.resLE h)) ≫ V'.2.fromSpec = V.2.fromSpec := by
  rw [show CommRingCat.ofHom (Scheme.resLE h) = W'.presheaf.map (homOfLE h).op from
    CommRingCat.ofHom_hom _]
  exact V'.2.map_fromSpec V.2 (homOfLE h).op

/-- The structure maps of the pieces: the affine square-root cover map, followed by
the affine-open presentation isomorphism. -/
private noncomputable def glueNatTrans :
    glueFunctor R X h2 ⟶ (glueCover R X h2).functorOfLocallyDirected where
  app p := sqrtCoverπ (chartUnit R X h2 p) ≫ p.1.1.2.isoSpec.inv
  naturality {p q} f := by
    have hpq : p.1.1.1 ≤ q.1.1.1 := leOfHom f
    show (glueFunctor R X h2).map f ≫ sqrtCoverπ (chartUnit R X h2 q) ≫ q.1.1.2.isoSpec.inv
        = (sqrtCoverπ (chartUnit R X h2 p) ≫ p.1.1.2.isoSpec.inv) ≫ (glueCover R X h2).trans f
    refine (cancel_mono (q.1.1.1.ι)).mp ?_
    have htr : (glueCover R X h2).trans f ≫ q.1.1.1.ι = p.1.1.1.ι :=
      (glueCover R X h2).trans_map f
    simp only [Category.assoc, htr, IsAffineOpen.isoSpec_inv_ι]
    have hsq : (glueFunctor R X h2).map f ≫ sqrtCoverπ (chartUnit R X h2 q)
        = sqrtCoverπ (chartUnit R X h2 p)
          ≫ Spec.map (CommRingCat.ofHom (Scheme.resLE (X := locusW R X h2) hpq)) := by
      show Spec.map (CommRingCat.ofHom (transRingHom R X h2 p q hpq))
            ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(locusW R X h2, q.1.1.1)
              (sqrtPair (chartUnit R X h2 q)).Ring))
          = Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(locusW R X h2, p.1.1.1)
              (sqrtPair (chartUnit R X h2 p)).Ring))
            ≫ Spec.map (CommRingCat.ofHom (Scheme.resLE hpq))
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, transRingHom_comp_algebraMap R X h2 p q hpq]
    erw [Category.assoc, Category.assoc, htr]
    rw [IsAffineOpen.isoSpec_inv_ι, ← Category.assoc, hsq]
    erw [Category.assoc, specMap_resLE_fromSpec hpq]

/-- **The relative gluing datum of the scale-torsor**: the square-root pieces over the
locally directed affine-in-chart cover of the level-`2` locus, glued along the
`ω`-cocycle twists. -/
private noncomputable def glueData : (glueCover R X h2).RelativeGluingData where
  functor := glueFunctor R X h2
  natTrans := glueNatTrans R X h2
  -- **(LEAF-EF, quarantined — tractable, deprioritized.)** Equifiberedness: for each
  -- `p ⟶ q` the naturality square (`glueFunctor.map f`, `natTrans.app p`, `natTrans.app q`,
  -- `functorOfLocallyDirected.map f`) is a pullback. It is the affine base-change square of
  -- the square-root cover. Concrete API path (single-session, not multi-week):
  --  • The pure-`Spec` core is `AlgebraicGeometry.isPullback_SpecMap_of_isPushout`
  --    (`Mathlib/AlgebraicGeometry/Pullbacks.lean`) applied to the CommRingCat pushout
  --      A = Γ(V_q), B = Γ(V_p) (via `Scheme.resLE hpq`), C = (sqrtPair (chartUnit q)).Ring
  --      (via `algebraMap`), P = (sqrtPair (chartUnit p)).Ring; `inl = algebraMap`,
  --      `inr = transRingHom p q` — commutativity is `transRingHom_comp_algebraMap`.
  --  • The pushout itself: `P ≅ Γ(V_p) ⊗_{Γ(V_q)} C` via `StandardEtalePair.baseChangeEquiv`
  --    (`= sqrtPair (Units.map resLE (chartUnit q)).Ring` by `sqrtPair_map`) composed with
  --    `sqrtPairCongr` + `chartUnit_compat` (`resUnit hpq (chartUnit q) = twistUnit² · chartUnit p`);
  --    then transport the tensor pushout (`AlgebraicGeometry.pullbackSpecIso` / an
  --    `Algebra.IsPushout`) along that AlgEquiv, checking `transRingHom` matches by
  --    `transRingHom_X`/`transRingHom_algebraMap`.
  --  • Finally re-point the two bottom corners `Spec Γ(V_p) → V_p`, `Spec Γ(V_q) → V_q`
  --    through `IsAffineOpen.isoSpec` (`natTrans.app = sqrtCoverπ ≫ isoSpec.inv`,
  --    `specMap_resLE_fromSpec`) and `IsPullback.flip` to match the goal's orientation.
  equifibered := by
    intro p q f
    sorry

/-! ### Finiteness, étaleness, and the sections classification of the carrier -/

/-- The `p`-th square-root piece structure map into its chart is **finite** (`2` a unit on
the base makes the rank-`2` square-root algebra module-finite). -/
private theorem natTrans_app_finite (p : glueIdx R X h2) :
    IsFinite ((glueData R X h2).natTrans.app p) := by
  show IsFinite (sqrtCoverπ (chartUnit R X h2 p) ≫ p.1.1.2.isoSpec.inv)
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite)]
  exact sqrtCoverπ_isFinite _ (isUnit_two_res R X h2 p.1.1.1)

/-- The `p`-th square-root piece structure map into its chart is **étale** (standard
étale presentation of the double cover). -/
private theorem natTrans_app_etale (p : glueIdx R X h2) :
    Etale ((glueData R X h2).natTrans.app p) := by
  show Etale (sqrtCoverπ (chartUnit R X h2 p) ≫ p.1.1.2.isoSpec.inv)
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @Etale)]
  exact sqrtCoverπ_etale _

/-- A morphism property that is Zariski-local at the target holds for the glued structure
map `toBase` as soon as it holds for every square-root piece: by the gluing datum each
piece structure map is the pullback of `toBase` along a chart-cover map
(`isPullback_natTrans_ι_toBase`), and the chart cover covers the locus. -/
private theorem toBase_localAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P]
    (hP : ∀ p : glueIdx R X h2, P ((glueData R X h2).natTrans.app p)) :
    P (glueData R X h2).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (glueCover R X h2)]
  intro p
  refine (P.arrow_mk_iso_iff (Arrow.isoMk
    (((glueData R X h2).isPullback_natTrans_ι_toBase p).flip.isoIsPullback _ _
      (IsPullback.of_hasPullback (glueData R X h2).toBase ((glueCover R X h2).f p)))
    (Iso.refl _) ?_)).mp (hP p)
  simp only [Scheme.Cover.pullbackHom, Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
  exact (((glueData R X h2).isPullback_natTrans_ι_toBase p).flip).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback (glueData R X h2).toBase ((glueCover R X h2).f p))

/-- **The scale-torsor carrier is finite over the level-`2` locus.** -/
private theorem toBase_isFinite : IsFinite (glueData R X h2).toBase :=
  toBase_localAtTarget R X h2 (@IsFinite) (natTrans_app_finite R X h2)

/-- **The scale-torsor carrier is étale over the level-`2` locus.** -/
private theorem toBase_etale : Etale (glueData R X h2).toBase :=
  toBase_localAtTarget R X h2 (@Etale) (natTrans_app_etale R X h2)

/-- **(LEAF-SPEC, quarantined.)** The per-fibre sections classification of the glued
square-root cover: `T`-sections of `glued` over a locus point `w` (lying over
`g : T ⟶ X.base`) correspond to the `ω`-bases completing the level structure to a
Legendre datum.

Recipe (build-step 4). A section `s : T ⟶ glued` with `s ≫ toBase = w.1`:
(i) restricts, over the affine-in-chart cover `glueCover` pulled back along `w.1`, to a
`sqrtCoverSectionsEquiv` family — in chart `i` a square root `u_i` of the pulled-back
abscissa-difference component `d_i = w.1 ^* (univAbscissaDiff.1 i)`
(`sqrtCoverSectionsEquiv`, `GroupScheme/SqrtUnitCover`);
(ii) the `u_i` are cocycle-compatible — the gluing datum's transitions are exactly the
`sqrtPairCongr` twists, so `u_i = u_{ij} · u_j` — hence glue (`Scheme.exists_unit_glue`
/ `UnitCocycle.sections`) to the chart coordinates of a single `ω`-basis `b` with
`d_b = u^{-2}`;
(iii) the `b`↔`u` dictionary (`basisUnitAt` / `abscissaDiff`, `Moduli/AdaptedModel`):
`(L_w, b)` is a Legendre datum iff `basisUnitAt b = 1` in every chart (the marking pins
`x(P) = 0`, `x(Q) = 1`), i.e. iff `u_i² = d_i⁻¹`, which is exactly the square-root
condition;
(iv) the resulting map is a bijection, the two sheets of the double cover matching the
`±ω` pair (`IsLegendreDatum.neg`) and pinned by `IsLegendreDatum.unit_sq_eq_one`
(`Moduli/LegendreDatumSymmetry`). -/
private theorem scaleTorsor_spec :
    Nonempty (ScaleTorsorSpec R X h2 (glueData R X h2).glued (glueData R X h2).toBase) := by
  -- (T-G3b) The family must be produced **naturally in `T`** (the `nat` field), which is
  -- how the funnel assembles it into a `RelRepData`; the plan below produces the
  -- bijections uniformly in `w`, so naturality comes from the same construction.
  -- **Assembly plan (via `nonempty_equiv_of_pseudotorsor`, `M := {ε : Γ(T,⊤)ˣ // ε² = 1}`).**
  -- Write `L_w := X.curve.fullLevelLocusPointsEquiv 2 h2 g w` and
  -- `h2T : IsUnit (2 : Γ(T,⊤))` (from `NIsInvertible.of_hom g h2`, `Nat.cast_ofNat`).
  -- Apply `nonempty_equiv_of_pseudotorsor` with:
  --   • RHS (basis side) — BANKED: `actB := rhsMuTwoAct R L_w`,
  --     `freeB := rhsMuTwoAct_free R L_w`, `transB := rhsMuTwoAct_trans R h2T L_w`.
  --   • LHS (section side) — Piece 1, OUTSTANDING: `actA`, `freeA`, `transA`. The `μ₂`-action
  --     twists a section by a locally-constant sign; its `ε = -1` generator is the deck
  --     involution glued from the banked per-piece `sqrtNegAut` (`u ↦ -u`). Building it needs
  --     the scheme-level descent: base-change `glueCover` along `w.1` (`𝒰.pullback₁ w.1`,
  --     auto-`LocallyDirected`), read a section on each piece as a map into
  --     `Xᵢ ≅ Uᵢ ×_W glued` (`(glueData …).isPullback_natTrans_ι_toBase i |>.flip.isoPullback`),
  --     translate to a square root via `sqrtCoverSectionsEquiv`, and glue with
  --     `glueMorphismsOverOfLocallyDirected` (`Cover/Directed.lean`). There is NO packaged
  --     sections `homEquiv` for a `RelativeGluingData.glued` — this is a genuine hand descent.
  --   • `hAB : Nonempty (sections) ↔ Nonempty (Legendre bases)` — Pieces 2+3, OUTSTANDING.
  --     Piece 2 (the `b`↔`u` dictionary): `IsLegendreDatum X' L_w b ↔ basisUnitAt b = 1` in
  --     every chart `↔ uᵢ² = dᵢ⁻¹`. Ingredients all exist (`e3_markChase`,
  --     `basisUnitAt_transUnit`, `basisUnitAt_smul`, `legendreCurve_vc_marked`; a Legendre
  --     marking pins the abscissae to `0`,`1` so `d = 1`), but the missing glue is an operator
  --     "trivialize a `(ω^{⊗-2})`-section by a basis `b`" turning `abscissaDiff` into a scalar
  --     `d_b`. Piece 3 (`w.1 ^* univAbscissaDiff = abscissaDiff` of the pulled tautological
  --     pair): needs a pullback/naturality of `abscissaDiff`/`markedCoordsAt` (via
  --     `MarksAt.transport` + `marksAt_coords_unique`) plus a base-change iso of the
  --     `omegaCocycle` — neither exists yet.
  sorry

end TorsorBuild

/-- **(T-E14-AX2 — the geometric residual.)** For every elliptic curve over a base in
which `2` is invertible, the `±ω` scale-torsor over the level-`2` locus exists: the glued
square-root cover of the abscissa difference. This is the sole remaining geometric input
to `legendreDelta_relativelyRepresentable_finiteEtale`; the build map is
`(2b)` the Spec-pullback squares of the base-changed `sqrtPair` covers, `(3)` their
`RelativeGluingData` over the chart cover of `fullLevelLocus 2` (`glued`, finite étale via
`toBase_preimage_eq_opensRange_ι` + `IsZariskiLocalAtTarget`), and `(4)` the sections
classification via `sqrtCoverSectionsEquiv` + the `b`↔`u` dictionary
(`abscissaDiff`/`basisUnitAt` + `IsLegendreDatum.neg`/`unit_sq_eq_one`). -/
theorem exists_scaleTorsorData (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    Nonempty (ScaleTorsorData R X h2) :=
  ⟨{ Z₂ := (glueData R X h2).glued
     q := (glueData R X h2).toBase
     isFinite := toBase_isFinite R X h2
     etale := toBase_etale R X h2
     spec := scaleTorsor_spec R X h2 }⟩

/-- **(T-E14-AX2, KM engine axiom 2 for the Legendre `δ` — the funnel assembly.)** For
every elliptic curve `E/S` over a base in which `2` is invertible, the `S`-scheme
relatively representing the Legendre-marked problem is finite étale over `S`. This is
`Bootstrap`'s `legendreDelta_relativelyRepresentable_finiteEtale`, proved by feeding the
scale-torsor package (`exists_scaleTorsorData`) through the funnel
`legendreDelta_relRep_finiteEtale_of_scaleTorsor`. -/
theorem legendreDelta_relRepData_finiteEtale (hR : IsUnit (2 : R)) (X : EllObj R) :
    ∃ D : ModuliProblem.RelRepData (legendreDeltaProblem R) X,
      IsFinite D.f ∧ Etale D.f := by
  have h2 : NIsInvertible X.base 2 :=
    nIsInvertible_base_of_isUnit R (by simpa using hR) X
  obtain ⟨D⟩ := exists_scaleTorsorData R X h2
  obtain ⟨sp⟩ := D.spec
  exact legendreDelta_relRepData_of_scaleTorsor R X h2 D.Z₂ D.q sp.toFun sp.nat
    D.isFinite D.etale

end ModularCurves
