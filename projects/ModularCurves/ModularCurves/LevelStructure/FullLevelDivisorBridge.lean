/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.LevelStructure.SectionsDivisorBaseChange
import ModularCurves.LevelStructure.TorsionFibreCount
import ModularCurves.LevelStructure.FullLevelFibre

/-!
# The full-level divisor bridge, `⟹` direction (T-D8-⟹ assembly)

Assembles the counting pieces: from the divisor equality `sectionsDivisor(P).ideal = torsionIdeal`,
the `N²` base-changed sections have pairwise-distinct base-points over any geometric point — because
their images cover the `N²`-point fibre torsion locus (`natCard_fibre_torsion_locus`), so the
pigeonhole (`injective_of_range_eq_of_natCard_eq`) forces distinctness.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(T-D8-⟹, pieces (a)+(b)+(c))** From the divisor equality, the `N²` base-changed sections
have pairwise-distinct base-points over the geometric point. -/
theorem baseChange_sections_base_injective {N : ℕ} [NeZero N]
    (P : Fin (N ^ 2) → E.Point (𝟙 S))
    (hdiv : (RelEffCartierDiv.sectionsDivisor E.π P).ideal = E.torsionIdeal N)
    {k : Type u} [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Function.Injective
      (fun i => (RelEffCartierDiv.sectionBaseChange (P i) t).1.base default) := by
  haveI : IsSeparated E.π := E.proper.toIsSeparated
  apply injective_of_range_eq_of_natCard_eq
    (T := (pullback.fst E.π t).base ⁻¹' ((E.torsionIdeal N).support : Set E.E))
  · rw [← iUnion_range_eq_range_eval,
      ← RelEffCartierDiv.sectionsDivisor_comap_support E.smooth P t, hdiv,
      Scheme.IdealSheafData.support_comap]
    rfl
  · rw [E.natCard_fibre_torsion_locus N t hN, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **(T-D8-⟹, piece (d))** Distinct base-points of the base-changed sections force the pulled
points themselves to be distinct: if `pull (Pᵢ) = pull (Pⱼ)` then `t ≫ (Pᵢ).1 = t ≫ (Pⱼ).1`, so
the base-changed sections coincide, so their base-points coincide, so `i = j`. -/
theorem pull_injective_of_baseChange_base_injective {N : ℕ}
    (P : Fin (N ^ 2) → E.Point (𝟙 S)) {k : Type u} [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ S)
    (hinj : Function.Injective
      (fun i => (RelEffCartierDiv.sectionBaseChange (P i) t).1.base default)) :
    Function.Injective (fun i => Point.pull E t (P i)) := by
  intro i j hij
  apply hinj
  have h1 : t ≫ (P i).1 = t ≫ (P j).1 := congrArg Subtype.val hij
  have h2 : (RelEffCartierDiv.sectionBaseChange (P i) t).1
      = (RelEffCartierDiv.sectionBaseChange (P j) t).1 := by
    show pullback.lift (t ≫ (P i).1) (𝟙 _) _ = pullback.lift (t ≫ (P j).1) (𝟙 _) _
    apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, h1]
  show (RelEffCartierDiv.sectionBaseChange (P i) t).1.base default
    = (RelEffCartierDiv.sectionBaseChange (P j) t).1.base default
  rw [h2]

end EllipticCurve

end ModularCurves
