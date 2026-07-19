/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LegendreDeltaRelRep
import ModularCurves.Moduli.LegendreDatumSymmetry
import ModularCurves.Moduli.AbscissaDifference
import ModularCurves.Moduli.LevelMarking
import ModularCurves.GroupScheme.SqrtUnitCover
import Mathlib.AlgebraicGeometry.RelativeGluing

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
  /-- The per-fibre sections classification: sections of `Z₂` over a locus point `w`
  correspond to the `ω`-bases making `(L_w, b)` a Legendre datum. -/
  spec : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
    (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
      w ≫ X.curve.fullLevelLocusπ 2 h2 = g }),
    Nonempty ({ s : T ⟶ Z₂ // s ≫ q = w.1 } ≃
      { b : OmegaBasis (X.pullbackAlong g).curve.toEllipticCurveGeom //
        IsLegendreDatum (X.pullbackAlong g)
          (X.curve.fullLevelLocusPointsEquiv 2 h2 g w) b })

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

/-- **(LEAF-U, quarantined.)** Each chart component of the universal abscissa
difference is a unit: `d_i = x(Q)_i − x(P)_i` is fibrewise nonvanishing on the
level-`2` locus, because at a geometric point `t` a vanishing abscissa difference
forces `Q̄ ∈ {±P̄}` (two points of a Weierstrass fibre with equal `x` are equal or
negative), which contradicts the locus condition (the `(1, ±1)`-combinations of the
tautological pair avoid the zero section; `pull_ne_pm`-style level-`2` distinctness).

Recipe: (i) read the marked chart coordinates at `t` through the marking pipeline
(`markedCoordsAt_marksAt` + the `MarksAt`-to-fibre dictionary of
`Moduli/SectionMarking`, as in `isUnit_x_of_marked_pair`/`e3_markChase` at level `3`);
(ii) equal fibre abscissae give `t ≫ σQ = t ≫ σP` or `t ≫ σQ = t ≫ (σP ≫ neg)`;
(iii) both are excluded by `IsNaiveFullLevel 2` (the combination conditions at
`v = (1,1)` and `v = (1,-1)` avoid zero, via `tautPair`'s property); (iv) a section of
`𝒪_W` over an open that is nonzero in every residue field is a unit
(`Scheme.basicOpen`: `x ∈ X.basicOpen f ↔ IsUnit (germ f x)`, and
`RingedSpace.isUnit_of_isUnit_germ`). -/
private theorem isUnit_univAbscissaDiff_component (i : (locusCocycle R X h2).ι) :
    IsUnit ((univAbscissaDiff R X h2).1 i) := by
  sorry

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

/-- **(LEAF-COMPAT, quarantined.)** The trivialization comparison: on the smaller open,
the `q`-chart unit is the square of the transition twist times the `p`-chart unit — the
`ω^{⊗-2}`-cocycle compatibility of the universal abscissa difference, restricted to `V_p`.

Recipe: this is exactly `(univAbscissaDiff R X h2).2 p.1.2 q.1.2` (the `Compatible ⊤`
field of `abscissaDiff`, i.e. `abscissaDiff_compatible`) restricted to `V_p` and read in
`Γ(V_p)ˣ`. Reduce to values via `Units.ext`, expand `chartUnit` by `chartUnit_val` and
`twistUnit` by its definition. The compat gives `d_i = ((c.u i j)^{⊗-2}) · d_j` (with
`c = locusCocycle`, `c.zpow (-2)` via `UnitCocycle.zpow_u`); the desired identity is its
`{±}`-rearrangement `d_j = (c.u i j)² · d_i`, obtained by multiplying through by the unit
`twistUnit² = (resUnit (c.u i j))²` and cancelling `((c.u i j)²)·((c.u i j)^{-2}) = 1`
(`Units.mul_inv`/`zpow` bookkeeping). The only friction is normalizing the nested
`Scheme.resLE`/`resUnit` restrictions to `V_p` (proof-irrelevant `≤` witnesses) and the
`(-2 : ℤ)` unit power — a `simp only [Scheme.resLE_resLE, Scheme.resUnit_val,
Units.val_mul, Units.val_zpow, map_zpow]` followed by `linear_combination`/`ring` on the
unit values closes it (cf. the value-level `abscissaDiff_compatible` proof). -/
private theorem chartUnit_compat (p q : glueIdx R X h2) (h : p ≤ q) :
    Scheme.resUnit (show p.1.1.1 ≤ q.1.1.1 from h) (chartUnit R X h2 q) =
      twistUnit R X h2 p q h ^ 2 * chartUnit R X h2 p := by
  sorry

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
  -- **(LEAF-EF, quarantined.)** Equifiberedness: for each `p ⟶ q` the naturality square
  -- (`glueFunctor.map f`, `natTrans.app p`, `natTrans.app q`, `functorOfLocallyDirected.map f`)
  -- is a pullback. Recipe: this is the affine base-change square of the square-root cover.
  -- Over the restriction `Scheme.resLE hpq : Γ(V_q) → Γ(V_p)`, the transition ring map
  -- `transRingHom` exhibits `(sqrtPair (chartUnit q)).Ring ⊗_{Γ(V_q)} Γ(V_p) ≅
  -- (sqrtPair (chartUnit p)).Ring` — the base change of the sqrt algebra of `d_q` is the
  -- sqrt algebra of `d_p`, twisted by `sqrtPairCongr` (`chartUnit_compat` says
  -- `d_q|_{V_p} = u² · d_p`, and `sqrtPairCongr` identifies the `u²·d`-cover with the
  -- `d`-cover). Concretely: `StandardEtalePair.baseChangeEquiv` (`GroupScheme/SqrtUnitCover`)
  -- gives `Γ(V_p) ⊗ sqrtPair(chartUnit q).Ring ≅ (sqrtPair (chartUnit q)).map (resLE).Ring
  -- = sqrtPair (Units.map (resLE) (chartUnit q)).Ring` (`sqrtPair_map`), and
  -- `chartUnit_compat` + `sqrtPairCongr` identify the latter with `sqrtPair (chartUnit p).Ring`;
  -- transport that ring iso to the pullback square via `AlgebraicGeometry.Spec` sending
  -- pushouts of rings to pullbacks of affines (`IsPullback` of `Spec` on a tensor-product
  -- square, e.g. `AlgebraicGeometry.isPullback_Spec_map_of_isPushout`-style), matching the
  -- top map to `glueFunctor.map f = Spec.map transRingHom` by `transRingHom_X`/`_algebraMap`.
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
private theorem scaleTorsor_spec {T : Scheme.{u}} (g : T ⟶ X.base)
    (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
      w ≫ X.curve.fullLevelLocusπ 2 h2 = g }) :
    Nonempty ({ s : T ⟶ (glueData R X h2).glued // s ≫ (glueData R X h2).toBase = w.1 } ≃
      { b : OmegaBasis (X.pullbackAlong g).curve.toEllipticCurveGeom //
        IsLegendreDatum (X.pullbackAlong g)
          (X.curve.fullLevelLocusPointsEquiv 2 h2 g w) b }) := by
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
     spec := fun {T} g w => scaleTorsor_spec R X h2 g w }⟩

/-- **(T-E14-AX2, KM engine axiom 2 for the Legendre `δ` — the funnel assembly.)** For
every elliptic curve `E/S` over a base in which `2` is invertible, the `S`-scheme
relatively representing the Legendre-marked problem is finite étale over `S`. This is
`Bootstrap`'s `legendreDelta_relativelyRepresentable_finiteEtale`, proved by feeding the
scale-torsor package (`exists_scaleTorsorData`) through the funnel
`legendreDelta_relRep_finiteEtale_of_scaleTorsor`. -/
theorem legendreDelta_relRep_finiteEtale (hR : IsUnit (2 : R)) (X : EllObj R) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
        ({ h : T ⟶ Z // h ≫ f = g } ≃
          (legendreDeltaProblem R).obj (Opposite.op (X.pullbackAlong g))) := by
  have h2 : NIsInvertible X.base 2 :=
    nIsInvertible_base_of_isUnit R (by simpa using hR) X
  obtain ⟨D⟩ := exists_scaleTorsorData R X h2
  exact legendreDelta_relRep_finiteEtale_of_scaleTorsor R X h2 D.Z₂ D.q D.isFinite D.etale
    (fun g w => (D.spec g w).some)

end ModularCurves
