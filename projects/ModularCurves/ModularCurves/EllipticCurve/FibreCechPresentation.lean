/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.FibreDivisorDictionary
import ModularCurves.EllipticCurve.PoleFiltration
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward

/-!
# Čech presentations of invertible sheaves on the projective Weierstrass model (`AP2-A1a/b`)

The scheme half of the `AP2-A1` dictionary. Over a field `F`, the projective Weierstrass model
`projModel W` of an elliptic `W` is covered by the two affine charts `Y`/`Z`
(`chartY_sup_chartZ_eq_top`, PoleFiltration). A `FractionalCechPresentation` of an invertible
module `M` identifies the three section modules of this cover — two charts and their overlap —
with `memRRspaceOn`-submodules of the function field carved out by a single divisor `D`,
compatibly with restriction. The two fibre facts then transport across the identification:

* `H⁰`: the degree-zero kernel of the ordered Čech complex is `baseSections`
  (`baseSectionsIsoKernelOrderedBaseCechDifferential`, M-generic), which the presentation
  matches with `RRspace D` — of dimension `1` for `deg D = 1` (`ell_eq_one_of_deg_eq_one`).
* `H¹`: exactness at degree one is surjectivity of the difference map on chart sections onto
  the overlap sections, which the presentation converts into the two-chart splitting
  `exists_sub_of_memRRspaceOn_inter` (strong approximation).

The place sets of the cover: the `Z`-chart sees exactly the finite places (`finitePlaces`,
proved for the trivial divisor in `memRRspaceOn_finitePlaces_zero_iff_coordinateRing`); the
`Y`-chart sees the infinite place and the finite places away from the vanishing of `y`; the
overlap misses only finitely many places from each — the `(S₀ \ S₁).Finite` input of the
splitting.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open FunctionField FunctionField.Chart Polynomial

open scoped Polynomial RatFunc WithZero

universe u

namespace ModularCurves

namespace FibreRR

variable {k K : Type u} [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

/-- The place-set combinatorics of a two-chart affine cover: the two sets cover all places and
each chart misses only finitely many places of the other. `S₀`/`S₁` are the places at which the
first/second chart's sections are constrained. -/
structure TwoChartPlaces (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
    [Algebra.IsSeparable k⟮X⟯ K] : Type u where
  /-- The places constrained on the first chart. -/
  S₀ : Set (PlaceA k K)
  /-- The places constrained on the second chart. -/
  S₁ : Set (PlaceA k K)
  /-- Every place lies on one of the charts. -/
  union_eq : S₀ ∪ S₁ = Set.univ
  /-- The first chart misses only finitely many places of the second. -/
  diff_finite₀ : (S₀ \ S₁).Finite
  /-- The second chart misses only finitely many places of the first. -/
  diff_finite₁ : (S₁ \ S₀).Finite

namespace TwoChartPlaces

variable (P : TwoChartPlaces k K)

/-- A function bounded on both charts is bounded everywhere: the `H⁰` matching. -/
theorem memRRspace_iff_memRRspaceOn_and (D : DivisorA k K) (f : K) :
    memRRspace k K D f ↔
      memRRspaceOn k K P.S₀ D f ∧ memRRspaceOn k K P.S₁ D f := by
  constructor
  · exact fun hf => ⟨fun v _ => hf v, fun v _ => hf v⟩
  · rintro ⟨h₀, h₁⟩ v
    rcases (Set.eq_univ_iff_forall.mp P.union_eq v : v ∈ P.S₀ ∪ P.S₁) with hv | hv
    · exact h₀ v hv
    · exact h₁ v hv

/-- The `H¹` splitting for a degree-one divisor on an elliptic function field: strong
approximation across the two charts. -/
theorem exists_sub_of_overlap (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
    [IsScalarTower k[X] W.CoordinateRing K]
    {D : DivisorA k K} (hD : deg k K D = 1) {g : K}
    (hg : memRRspaceOn k K (P.S₀ ∩ P.S₁) D g) :
    ∃ a b : K, memRRspaceOn k K P.S₀ D a ∧ memRRspaceOn k K P.S₁ D b ∧ g = a - b := by
  have hfull : topAdeleSubmodule k K = adeleFilt k K D + diagonalSubmodule k K :=
    adeleSubmodule_top_eq_adeleFilt_add_diagonal (k := k) (K := K)
      (defect_eq_genus_of_deg_eq_one W hD)
  exact exists_sub_of_memRRspaceOn_inter hfull P.diff_finite₀ hg

end TwoChartPlaces

end FibreRR

end ModularCurves
