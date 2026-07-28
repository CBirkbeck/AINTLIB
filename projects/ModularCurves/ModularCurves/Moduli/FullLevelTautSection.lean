/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.LevelSpaces
import ModularCurves.ForMathlib.OpenImmersionOfSection
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The tautological full-level section (YFULL route γ, [YF-TAUT])

Over the ambient `E[N] ×_S E[N] = pullback (torsionπ N) (torsionπ N)` the two projections
carry the **tautological pair** of `N`-torsion points `(u₁, u₂)`. On any open `U` of the
ambient over which this pair is a Drinfeld full-level structure, the classifying section
of the pair reconstructs the inclusion `U.ι`: there is `s : U ⟶ levelSpaceΓ E N` with
`s ≫ levelSpaceΓι E N = U.ι`.

This is the section datum of the open-immersion criterion
`isOpenImmersion_of_range_subset_of_section` (`ForMathlib/OpenImmersionOfSection.lean`):
combined with the clopen "classifier-is-an-iso" locus (`isClopen_finrank_eq`,
`ForMathlib/FiniteLocallyFreeIsoLocus.lean`) and the image bound `[YF-RANGE]`, it upgrades
the closed immersion `levelSpaceΓι` to an open immersion — the `Y(N)` clopen leaf
`isOpenImmersion_levelSpaceΓι`. The full-level hypothesis over `U` is supplied by the
classifier leaf `[YF-CLASSIFIER]` (the divisor↔iso dictionary); this file is the
construction-free plumbing that turns it into a section.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- Structure map of the ambient `E[N] ×_S E[N]` to `S` (first projection to `S`). -/
noncomputable def tautBase : pullback (E.torsionπ N) (E.torsionπ N) ⟶ S :=
  pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N

/-- The first tautological `N`-torsion point over `E[N] ×_S E[N]` (first projection into
`E[N]`, then included into `E`). -/
noncomputable def tautPt₁ : E.Point (tautBase E N) :=
  ⟨pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N, by
    simp only [tautBase]; rw [Category.assoc, E.torsionι_π]⟩

/-- The second tautological `N`-torsion point over `E[N] ×_S E[N]`. -/
noncomputable def tautPt₂ : E.Point (tautBase E N) :=
  ⟨pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N, by
    simp only [tautBase]; rw [Category.assoc, E.torsionι_π]; exact pullback.condition.symm⟩

omit [NeZero N] in
/-- Both tautological points are killed by `[N]` for the same reason: they factor through
`torsionι`, whose defining square says `torsionι ≫ [N] = torsionπ ≫ 0`. The only difference
between `tautPt₁` and `tautPt₂` is which projection recomputes `tautBase`. -/
private theorem comp_torsionι_killed
    (f : pullback (E.torsionπ N) (E.torsionπ N) ⟶ E.torsion N)
    (hf : f ≫ E.torsionπ N = tautBase E N) :
    (f ≫ E.torsionι N) ≫ E.mulByHom N = tautBase E N ≫ E.zero := by
  rw [Category.assoc,
    show E.torsionι N ≫ E.mulByHom N = E.torsionπ N ≫ E.zero from pullback.condition,
    ← Category.assoc, hf]

theorem tautPt₁_killed :
    (tautPt₁ E N).1 ≫ E.mulByHom N = tautBase E N ≫ E.zero :=
  comp_torsionι_killed E N (pullback.fst (E.torsionπ N) (E.torsionπ N)) rfl

theorem tautPt₂_killed :
    (tautPt₂ E N).1 ≫ E.mulByHom N = tautBase E N ≫ E.zero :=
  comp_torsionι_killed E N (pullback.snd (E.torsionπ N) (E.torsionπ N))
    pullback.condition.symm

/-- **[YF-TAUT]** Over an open `U` of `E[N] ×_S E[N]` on which the restricted tautological
pair is a full-level structure, the classifying section reconstructs the inclusion: there
is a section `s : U ⟶ levelSpaceΓ E N` of `levelSpaceΓι E N` equal to `U.ι`. -/
theorem exists_tautSection_of_isFullLevel
    (U : (pullback (E.torsionπ N) (E.torsionπ N)).Opens)
    (hfull : (E.baseChange (U.ι ≫ tautBase E N)).IsFullLevel N
      (Point.asSection E (U.ι ≫ tautBase E N) (Point.restrict E U.ι (tautPt₁ E N)))
      (Point.asSection E (U.ι ≫ tautBase E N) (Point.restrict E U.ι (tautPt₂ E N)))) :
    ∃ s : (U : Scheme.{u}) ⟶ levelSpaceΓ E N, s ≫ levelSpaceΓι E N = U.ι := by
  -- the killing conditions of the restricted taut points (restriction is precomposition)
  have hkill : ∀ P : E.Point (tautBase E N),
      P.1 ≫ E.mulByHom N = tautBase E N ≫ E.zero →
      (Point.restrict E U.ι P).1 ≫ E.mulByHom N = (U.ι ≫ tautBase E N) ≫ E.zero := by
    intro P hP
    show (U.ι ≫ P.1) ≫ E.mulByHom N = (U.ι ≫ tautBase E N) ≫ E.zero
    rw [Category.assoc, hP, ← Category.assoc]
  -- the classifying section from the level-space universal property
  obtain ⟨s, hs⟩ := (levelSpaceΓ_spec E N (U.ι ≫ tautBase E N)
    (Point.restrict E U.ι (tautPt₁ E N)) (Point.restrict E U.ι (tautPt₂ E N))
    (hkill _ (tautPt₁_killed E N)) (hkill _ (tautPt₂_killed E N))).mpr hfull
  refine ⟨s, ?_⟩
  rw [hs]
  -- the classifying map of the taut pair reconstructs `U.ι`
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst]
    apply (cancel_mono (E.torsionι N)).mp
    rw [E.pointToTorsion_torsionι, Category.assoc]
    show U.ι ≫ (tautPt₁ E N).1 =
      U.ι ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N
    rfl
  · rw [pullback.lift_snd]
    apply (cancel_mono (E.torsionι N)).mp
    rw [E.pointToTorsion_torsionι, Category.assoc]
    show U.ι ≫ (tautPt₂ E N).1 =
      U.ι ≫ pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N
    rfl

/-- **[YF-CLOPEN assembly]** The `Y(N)` clopen leaf, reduced to the classifier-produced
data. Given an open `U` of `E[N] ×_S E[N]` that (i) contains the image of the full-level
closed immersion `levelSpaceΓι` and (ii) over which the tautological pair is a full-level
structure, the closed immersion `levelSpaceΓι E N` is an **open immersion**.

The remaining leaf `[YF-CLASSIFIER]` supplies such a `U` (the clopen locus where the
`N²`-section classifier `[a]P + [b]Q` is an isomorphism, from `isClopen_finrank_eq`): the
image bound is the forward "full-level ⟹ classifier iso" direction, and the full-level
hypothesis over `U` is the reverse. This theorem consumes `[YF-TAUT]`
(`exists_tautSection_of_isFullLevel`) and the open-immersion criterion
`isOpenImmersion_of_range_subset_of_section`. -/
theorem isOpenImmersion_levelSpaceΓι_of_taut
    (U : (pullback (E.torsionπ N) (E.torsionπ N)).Opens)
    (hrange : Set.range (levelSpaceΓι E N).base ⊆ (U : Set _))
    (hfull : (E.baseChange (U.ι ≫ tautBase E N)).IsFullLevel N
      (Point.asSection E (U.ι ≫ tautBase E N) (Point.restrict E U.ι (tautPt₁ E N)))
      (Point.asSection E (U.ι ≫ tautBase E N) (Point.restrict E U.ι (tautPt₂ E N)))) :
    IsOpenImmersion (levelSpaceΓι E N) := by
  haveI : IsClosedImmersion (levelSpaceΓι E N) :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.subschemeι _))
  obtain ⟨s, hs⟩ := exists_tautSection_of_isFullLevel E N U hfull
  exact AlgebraicGeometry.isOpenImmersion_of_range_subset_of_section
    (levelSpaceΓι E N) U hrange s hs

end EllipticCurve

end ModularCurves
