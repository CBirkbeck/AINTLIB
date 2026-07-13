/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.FullLevelSupset
import ModularCurves.Moduli.FullLevelTautSection
import ModularCurves.EllipticCurve.ModelRecord

/-!
# The Y(N) clopen leaf, assembled (YFULL route γ, [YF-CLOPEN])

Wires the `[YF-⊇]` divisor chain (`sectionsDivisor_ideal_eq_torsionIdeal`) and the openness
engine (`fullLevelOpens`) into the open-immersion criterion
`isOpenImmersion_levelSpaceΓι_of_taut`: over the open locus `fullLevelOpens` where every
nonzero combination `[c]P + [d]Q` is nonvanishing, the `N²` tautological combinations are
pairwise pointwise-distinct (residue-field agreement of the base-changed **sections** upgrades
topological agreement, `sections_residue_eq_of_base_eq`, and then a nonzero combination would
have to vanish, `base_mem_pointVanishSet_of_comp_eq`), so the tautological pair is a full-level
structure `[YF-⊇]`. Combined with the image bound `[YF-⊆]` this upgrades the closed immersion
`levelSpaceΓι` to an open immersion.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-! ### Point-algebra API: `restrict` and `asSection` are additive -/

/-- `Point.restrict` intertwines integer scalar multiplication (precomposition commutes with
`[n]`, `point_smul_eq_comp_mulBy` + associativity). -/
theorem restrict_zsmul {T T' : Scheme.{u}} {g : T ⟶ S} (m : T' ⟶ T) (a : ℤ) (P : E.Point g) :
    Point.restrict E m (a • P) = a • Point.restrict E m P := by
  refine Subtype.ext ?_
  show m ≫ ((a • P : E.Point g) : T ⟶ E.E)
    = ((a • Point.restrict E m P : E.Point (m ≫ g)) : T' ⟶ E.E)
  rw [E.point_smul_eq_comp_mulBy, E.point_smul_eq_comp_mulBy]
  exact (Category.assoc m P.1 (E.mulByHom a)).symm

/-- `Point.asSection` is additive: a section of the base-changed curve is determined by its
first projection, and that projection (`baseChangeEquiv`) is an additive equivalence; the sum
is transported across the base equality `𝟙 T ≫ g = g` by `point_add_val_congr_base`. Written
term-mode to sidestep the semireducible-`baseChange.E` `kabstract` wall (the `asSection_zsmul`
idiom). -/
theorem Point.asSection_add {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    Point.asSection E g (P + Q) = Point.asSection E g P + Point.asSection E g Q := by
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · -- fst legs: both compose with `pullback.fst E.π g` to `(P + Q).1`
    have lhs : (Point.asSection E g (P + Q)).1 ≫ pullback.fst E.π g = (P + Q).1 :=
      Point.asSection_val_fst E g (P + Q)
    have rhs : (Point.asSection E g P + Point.asSection E g Q).1 ≫ pullback.fst E.π g = (P + Q).1 :=
      (Point.baseChangeEquiv_apply_coe E g (𝟙 T)
          (Point.asSection E g P + Point.asSection E g Q)).symm.trans <|
        (congrArg (·.1) (map_add (Point.baseChangeEquiv E g (𝟙 T))
          (Point.asSection E g P) (Point.asSection E g Q))).trans <|
          point_add_val_congr_base E (Category.id_comp g) _ P _ Q
            ((Point.baseChangeEquiv_apply_coe E g (𝟙 T) (Point.asSection E g P)).trans
              (Point.asSection_val_fst E g P))
            ((Point.baseChangeEquiv_apply_coe E g (𝟙 T) (Point.asSection E g Q)).trans
              (Point.asSection_val_fst E g Q))
    exact lhs.trans rhs.symm
  · -- snd legs: both compose with `pullback.snd E.π g` to `𝟙 T`
    exact (Point.asSection_val_snd E g (P + Q)).trans
      ((Point.asSection E g P + Point.asSection E g Q).2).symm

/-- **Sub-lemma A.** The tautological combination `[a]P + [b]Q` of the base-changed taut
sections is the base-changed section of the ambient combination point `combPoint a b`. -/
theorem combo_eq_asSection_restrict {T : Scheme.{u}}
    (k : T ⟶ pullback (E.torsionπ N) (E.torsionπ N)) (a b : ℤ) :
    a • Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (tautPt₁ E N))
      + b • Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (tautPt₂ E N))
    = Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (combPoint E N a b)) := by
  rw [combPoint, E.restrict_add, E.restrict_zsmul, E.restrict_zsmul, Point.asSection_add,
    Point.asSection_zsmul, Point.asSection_zsmul]

end EllipticCurve

end ModularCurves
