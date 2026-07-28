/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ExactOrderRigidity
import ModularCurves.EllipticCurve.TorsionRestrict
import ModularCurves.GroupScheme.SubgroupQuotient

/-!
# [T-G3d] `N`-divisibility of torsion-fixing endomorphisms (KM 2.7.2 proof)

KM (verbatim, proof of Cor 2.7.2): *"ε−1 kills E[N], so it factors as ε−1 = g·N for some
g ∈ End(E). Then ε = 1 + gN."* This file executes the factorization against STREAM-G0's
categorical quotient `E/E[N]` (`GroupScheme/SubgroupQuotient.lean`):

* `sub_one_isInvariant_torsionSubgroup` — the difference `δ = ε − 1` of an endomorphism fixing
  `E[N]` is invariant under `E[N]`-translation (additivity of the pointed `δ` + `δ` kills the
  torsion points). This is the descent condition of the quotient's universal property.
* `exists_eq_one_add_mulBy_comp_of_fixesTorsion_of_isIso` — the divisibility itself, modulo the
  single tracked box `[IsIso (E.torsionQuotientToSelf N)]` (**T-G3d-Niso**, `E/E[N] ≅ E` — the
  degree-fact half, whose engine `Scheme.Hom.finrank_comp`/`isIso_iff_finrank_eq` is now in
  `ForMathlib/FinrankComp.lean` and which closes when the quotient isogeny's finite-flat-rank
  substrate lands): `δ` descends through `π : E ⟶ E/E[N]`, the iso re-expresses the descent as a
  factorization through `[N] = π ≫ toSelf`, and pointedness of the factor `g` (forced by
  pointedness of `δ` and of `[N]`) turns `δ = [N] ≫ g` into the KM form `δ = g ≫ [N]` via
  `mulBy_comp_comm`.

This discharges the `exists_eq_one_add_mulBy_comp_of_fixesTorsion` pin of
`EndomorphismDegree.lean` up to the Niso box.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

-- v4.33 bump: neither the category instances nor the semireducible component types are
-- transparent enough for the rewrites and instance searches below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **([T-G3d] invariance leg)** The difference `δ = ε * 𝟙⁻¹` (`Hom.commGroup` spelling of
`ε − 1`) of a **pointed** endomorphism `ε` fixing the `N`-torsion inclusion is invariant under
translation by the torsion subgroup scheme: on `T`-points, `δ(x + t) = δ(x)·δ(t) = δ(x)`, since
`δ` is additive (a pointed endomorphism is a homomorphism, KM 2.5.1) and kills every torsion
point (`t` factors through `torsionι`, which `ε` fixes). -/
theorem sub_one_isInvariant_torsionSubgroup [IsLocallyNoetherian S] (N : ℕ) [NeZero N]
    (ε : E.asOver ⟶ E.asOver) (hη : η[E.asOver] ≫ ε = η[E.asOver])
    (hfix : E.torsionι N ≫ ε.left = E.torsionι N) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    (E.torsionSubgroup N).IsInvariant (ε * (𝟙 E.asOver)⁻¹).left := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  intro T g x t ht
  letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
  -- `δ` is pointed, hence a monoid homomorphism
  have hδη : η[E.asOver] ≫ (ε * (𝟙 E.asOver)⁻¹) = η[E.asOver] := E.sub_one_pointed ε hη
  haveI : IsMonHom (ε * (𝟙 E.asOver)⁻¹) :=
    { one_hom := hδη, mul_hom := E.endMonHom (ε * (𝟙 E.asOver)⁻¹) hδη }
  -- `t` factors through the torsion inclusion, so `ε` fixes it
  obtain ⟨h, hh⟩ := (FiniteLocallyFreeSubgroup.mem_pointSubgroup (G := E.torsionSubgroup N)).mp ht
  have hfix' : (E.torsionSubgroup N).ι ≫ ε.left = (E.torsionSubgroup N).ι := hfix
  have htfix : (E.pointEquivOverHom g) t ≫ ε = (E.pointEquivOverHom g) t := by
    apply Over.OverMorphism.ext
    show t.1 ≫ ε.left = t.1
    rw [← hh, Category.assoc, hfix']
  -- `δ` kills `t`
  have htkill : (E.pointEquivOverHom g) t ≫ (ε * (𝟙 E.asOver)⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, htfix, _root_.mul_inv_cancel]
  -- expand the sum through the monoid homomorphism and cancel
  have key : (E.pointEquivOverHom g) (x + t) ≫ (ε * (𝟙 E.asOver)⁻¹)
      = (E.pointEquivOverHom g) x ≫ (ε * (𝟙 E.asOver)⁻¹) := by
    have hmul := map_mul (IsMonHom.monoidHom (ε * (𝟙 E.asOver)⁻¹) (Over.mk g))
      ((E.pointEquivOverHom g) x) ((E.pointEquivOverHom g) t)
    simp only [IsMonHom.monoidHom_apply] at hmul
    rw [E.pointEquivOverHom_add, hmul, htkill, _root_.mul_one]
  have keyl := congrArg CommaMorphism.left key
  exact keyl

/-- **([T-G3d] divisibility, KM 2.7.2 proof — modulo T-G3d-Niso)** An endomorphism `ε` of `E/S`
fixing the `N`-torsion subscheme factors as `ε = 1 + g∘[N]`, GIVEN the tracked box
`[IsIso (E.torsionQuotientToSelf N)]` (`E/E[N] ≅ E`, the degree-fact half of the `[N]`-isogeny
picture). Route: `δ = ε − 1` is `E[N]`-invariant (`sub_one_isInvariant_torsionSubgroup`), hence
descends through the quotient isogeny (`quotient_lift`); composing with the inverse of
`toSelf : E/E[N] ≅ E` factors `δ` through `[N] = π ≫ toSelf`; the factor is pointed, so it
commutes with `[N]` (`mulBy_comp_comm`), giving KM's `ε = 1 + g·N`. Pointedness of `ε` is not
assumed — it follows from `hfix` (the zero section lies in `E[N]`). -/
theorem exists_eq_one_add_mulBy_comp_of_fixesTorsion_of_isIso [IsLocallyNoetherian S]
    (N : ℕ) [NeZero N] [IsIso (E.torsionQuotientToSelf N)]
    (ε : E.asOver ⟶ E.asOver) (hfix : E.torsionι N ≫ ε.left = E.torsionι N) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    ∃ g : E.asOver ⟶ E.asOver, ε = 𝟙 E.asOver * (g ≫ E.mulBy (N : ℤ)) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  -- the zero section factors through `E[N]`, so `hfix` forces `ε` pointed
  have hz0 : E.zero ≫ E.mulByHom (N : ℕ) = 𝟙 S ≫ E.zero := by
    have h : (η[E.asOver]).left ≫ (E.mulBy ((N : ℕ) : ℤ)).left = (η[E.asOver]).left :=
      congrArg CommaMorphism.left (E.mulBy_pointed ((N : ℕ) : ℤ))
    rw [E.one_eq_zero] at h
    have h2 : (𝟙 S ≫ E.zero) ≫ E.mulByHom ((N : ℕ) : ℤ) = 𝟙 S ≫ E.zero := h
    rw [Category.id_comp] at h2
    rw [Category.id_comp]
    exact h2
  have hzε : E.zero ≫ ε.left = E.zero := by
    have hw0 : pullback.lift E.zero (𝟙 S) hz0 ≫ pullback.fst (E.mulByHom (N : ℕ)) E.zero
        = E.zero := pullback.lift_fst E.zero (𝟙 S) hz0
    have hfix'' : pullback.fst (E.mulByHom (N : ℕ)) E.zero ≫ ε.left
        = pullback.fst (E.mulByHom (N : ℕ)) E.zero := hfix
    rw [← hw0, Category.assoc, hfix'']
  have hη : η[E.asOver] ≫ ε = η[E.asOver] := by
    apply Over.OverMorphism.ext
    show (η[E.asOver]).left ≫ ε.left = (η[E.asOver]).left
    rw [E.one_eq_zero]
    show (𝟙 S ≫ E.zero) ≫ ε.left = 𝟙 S ≫ E.zero
    rw [Category.id_comp, hzε]
  -- descend `δ` through the quotient
  have hinv := E.sub_one_isInvariant_torsionSubgroup N ε hη hfix
  set δl : E.E ⟶ E.E := (ε * (𝟙 E.asOver)⁻¹).left with hδl
  have hinv' : (E.torsionSubgroup N).IsInvariant δl := hinv
  obtain ⟨w, hw, -⟩ := (E.torsionSubgroup N).quotient_lift δl hinv'
  -- factor through `[N] = π ≫ toSelf`
  have hfacpre : δl = E.mulByHom (N : ℤ) ≫ (inv (E.torsionQuotientToSelf N) ≫ w) := by
    rw [← hw, ← E.torsionQuotientπ_comp_toSelf N, Category.assoc,
      ← Category.assoc (E.torsionQuotientToSelf N), IsIso.hom_inv_id, Category.id_comp]
  set gl : E.E ⟶ E.E := inv (E.torsionQuotientToSelf N) ≫ w with hgl
  have hfac : δl = E.mulByHom (N : ℤ) ≫ gl := hfacpre
  -- the factor lies over `S`
  have hglπ : gl ≫ E.π = E.π := by
    have hδπ : δl ≫ E.π = E.π := Over.w (ε * (𝟙 E.asOver)⁻¹ : E.asOver ⟶ E.asOver)
    have h1 : E.mulByHom (N : ℤ) ≫ gl ≫ E.π = E.mulByHom (N : ℤ) ≫ E.π := by
      rw [← Category.assoc, ← hfac, hδπ, E.mulByHom_π]
    rw [← E.torsionQuotientπ_comp_toSelf N] at h1
    simp only [Category.assoc] at h1
    have h3 := (E.torsionSubgroup N).quotientπ_hom_ext _ _ h1
    exact (cancel_epi (E.torsionQuotientToSelf N)).mp h3
  -- package as an `Over`-endomorphism and commute past `[N]`
  show ∃ g : E.asOver ⟶ E.asOver, ε = 𝟙 E.asOver * (g ≫ E.mulBy (N : ℤ))
  refine ⟨Over.homMk (U := E.asOver) (V := E.asOver) gl hglπ, ?_⟩
  have hδover : (ε * (𝟙 E.asOver)⁻¹)
      = E.mulBy (N : ℤ) ≫ Over.homMk (U := E.asOver) (V := E.asOver) gl hglπ := by
    apply Over.OverMorphism.ext
    show δl = E.mulByHom (N : ℤ) ≫ gl
    exact hfac
  have hgη : η[E.asOver] ≫ Over.homMk (U := E.asOver) (V := E.asOver) gl hglπ
      = η[E.asOver] := by
    have hδη : η[E.asOver] ≫ (ε * (𝟙 E.asOver)⁻¹) = η[E.asOver] := E.sub_one_pointed ε hη
    rw [hδover, ← Category.assoc, E.mulBy_pointed] at hδη
    exact hδη
  have hcomm := E.mulBy_comp_comm (Over.homMk (U := E.asOver) (V := E.asOver) gl hglπ)
    hgη (N : ℤ)
  rw [← hcomm, ← hδover, _root_.mul_comm]
  exact (inv_mul_cancel_right ε (𝟙 E.asOver)).symm

end EllipticCurve

end ModularCurves
