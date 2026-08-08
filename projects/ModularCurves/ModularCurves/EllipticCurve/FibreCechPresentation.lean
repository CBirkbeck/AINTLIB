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

open scoped Polynomial Polynomial.Bivariate RatFunc WithZero

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

section EllipticYZ

variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
  [IsScalarTower k[X] W.CoordinateRing K]

/-- The place set of the `Y`-chart of the projective Weierstrass model: the infinite place
together with the finite places at which the coordinate `y` is a unit. -/
def yChartPlaces : Set (PlaceA k K) :=
  Set.range Sum.inr ∪
    Sum.inl '' {v | placeValuation k K (Sum.inl v) (W.yCoord K) = 1}

/-- The `y`-coordinate is nonzero in the function field. -/
theorem yCoord_ne_zero : W.yCoord K ≠ 0 := fun h0 =>
  WeierstrassCurve.Affine.yCoord_notMem_range W K
    ⟨0, by rw [map_zero, h0]⟩

/-- The `y`-coordinate is integral at every finite place. -/
theorem placeValuation_yCoord_le_one
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    placeValuation k K (Sum.inl v) (W.yCoord K) ≤ 1 := by
  have htrans := algebraMap_coordinateRingEquivIntegers (K := K) W
    (WeierstrassCurve.Affine.CoordinateRing.mk W Y)
  have h1 : W.yCoord K = algebraMap (ringOfIntegers k K) K
      (WeierstrassCurve.Affine.Chart.coordinateRingEquivIntegers W K
        (WeierstrassCurve.Affine.CoordinateRing.mk W Y)) := by
    rw [htrans]
    rfl
  rw [h1]
  simpa [placeValuation] using
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) v _

/-- **(`AP2-A1a-ii`)** The `(Y, Z)`-cover place combinatorics of the projective Weierstrass
model of an elliptic curve: the `Z`-chart carries the finite places, the `Y`-chart the
(unique) infinite place and the finite places off `y = 0`; each chart misses only finitely
many places of the other. -/
noncomputable def ellipticYZ : TwoChartPlaces k K where
  S₀ := finitePlaces k K
  S₁ := yChartPlaces W
  union_eq := by
    rw [Set.eq_univ_iff_forall]
    rintro (v | v)
    · exact Or.inl ⟨v, rfl⟩
    · exact Or.inr (Or.inl ⟨v, rfl⟩)
  diff_finite₀ := by
    have hfin := (IsDedekindDomain.HeightOneSpectrum.Support.finite
      (R := ringOfIntegers k K) ((W.yCoord K)⁻¹)).image
      (Sum.inl : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K) → PlaceA k K)
    refine hfin.subset ?_
    rintro w ⟨⟨v, rfl⟩, hw⟩
    refine ⟨v, ?_, rfl⟩
    have hne : placeValuation k K (Sum.inl v) (W.yCoord K) ≠ 1 := fun h1 =>
      hw (Or.inr ⟨v, h1, rfl⟩)
    have hlt : placeValuation k K (Sum.inl v) (W.yCoord K) < 1 :=
      lt_of_le_of_ne (placeValuation_yCoord_le_one W v) hne
    have h0 : placeValuation k K (Sum.inl v) (W.yCoord K) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (yCoord_ne_zero (K := K) W)
    show 1 < v.valuation K ((W.yCoord K)⁻¹)
    have hv : v.valuation K (W.yCoord K) < 1 := by
      simpa [placeValuation] using hlt
    have hv0 : v.valuation K (W.yCoord K) ≠ 0 := by
      simpa [placeValuation] using h0
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv0, hv⟩
  diff_finite₁ := by
    letI : Subsingleton
        (IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :=
      ⟨fun v w =>
        WeierstrassCurve.Affine.Chart.infinity_heightOne_unique W K v w⟩
    refine (Set.finite_range (Sum.inr :
      IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K) → PlaceA k K)).subset ?_
    rintro w ⟨hw, hnot⟩
    rcases hw with ⟨v, rfl⟩ | ⟨v, -, rfl⟩
    · exact ⟨v, rfl⟩
    · exact absurd ⟨v, rfl⟩ hnot

@[simp]
theorem ellipticYZ_S₀ : (ellipticYZ (K := K) W).S₀ = finitePlaces k K := rfl

@[simp]
theorem ellipticYZ_S₁ : (ellipticYZ (K := K) W).S₁ = yChartPlaces W := rfl

end EllipticYZ

section SurjectivityTransport

/-- **(`AP2-A1b`, abstract transport)** Surjectivity of the two-chart Čech difference map,
transported from the function-field splitting along additive identifications of the two chart
section modules and the overlap section module with `rrspaceOn`-submodules. The `Prop`-level
compatibilities say the identifications intertwine the restriction maps with the submodule
inclusions into `K`. -/
theorem surjective_sub_of_addEquiv_rrspaceOn
    {A₀ A₁ C : Type*} [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup C]
    (r₀ : A₀ →+ C) (r₁ : A₁ →+ C)
    {S₀ S₁ : Set (PlaceA k K)} {D : DivisorA k K}
    (e₀ : A₀ ≃+ rrspaceOn k K S₀ D) (e₁ : A₁ ≃+ rrspaceOn k K S₁ D)
    (eC : C ≃+ rrspaceOn k K (S₀ ∩ S₁) D)
    (h₀ : ∀ a, (eC (r₀ a) : K) = (e₀ a : K))
    (h₁ : ∀ a, (eC (r₁ a) : K) = (e₁ a : K))
    (split : ∀ g : K, memRRspaceOn k K (S₀ ∩ S₁) D g →
      ∃ a b : K, memRRspaceOn k K S₀ D a ∧ memRRspaceOn k K S₁ D b ∧ g = a - b) :
    Function.Surjective (fun p : A₀ × A₁ => r₁ p.2 - r₀ p.1) := by
  intro c
  obtain ⟨a, b, ha, hb, hab⟩ := split (eC c : K) (eC c).2
  refine ⟨⟨e₀.symm ⟨-a, neg_mem ha⟩, e₁.symm ⟨-b, neg_mem hb⟩⟩, ?_⟩
  apply eC.injective
  apply Subtype.ext
  have hr₀ : (eC (r₀ (e₀.symm ⟨-a, neg_mem ha⟩)) : K) = -a := by
    rw [h₀, e₀.apply_symm_apply]
  have hr₁ : (eC (r₁ (e₁.symm ⟨-b, neg_mem hb⟩)) : K) = -b := by
    rw [h₁, e₁.apply_symm_apply]
  calc (eC (r₁ (e₁.symm ⟨-b, neg_mem hb⟩) - r₀ (e₀.symm ⟨-a, neg_mem ha⟩)) : K)
      = (eC (r₁ (e₁.symm ⟨-b, neg_mem hb⟩)) : K) -
          (eC (r₀ (e₀.symm ⟨-a, neg_mem ha⟩)) : K) := by
        rw [map_sub]
        rfl
    _ = -b - -a := by rw [hr₀, hr₁]
    _ = (eC c : K) := by rw [hab]; ring

end SurjectivityTransport

end FibreRR

/-! ## Ordered Čech indices of a two-element cover -/

namespace TwoCoverIndex

open AlgebraicGeometry.Scheme.Modules

/-- Degree-zero ordered Čech indices of a two-element cover are the two singletons. -/
def zeroEquiv : Scheme.Modules.OrderedCechIndex (Fin 2) 0 ≃ Fin 2 where
  toFun i := i.1 0
  invFun j := ⟨fun _ => j, fun a b hab => absurd hab (by omega)⟩
  left_inv i := by
    apply Subtype.ext
    funext a
    have : a = 0 := by omega
    rw [this]
  right_inv j := rfl

/-- The unique degree-one ordered Čech index of a two-element cover: the full tuple `(0, 1)`. -/
instance : Unique (Scheme.Modules.OrderedCechIndex (Fin 2) 1) where
  default := ⟨fun a => a, fun _ _ h => h⟩
  uniq i := by
    apply Subtype.ext
    funext a
    show i.1 a = a
    have b0 : (i.1 0 : ℕ) < 2 := (i.1 0).isLt
    have b1 : (i.1 1 : ℕ) < 2 := (i.1 1).isLt
    have h01 : (i.1 0 : ℕ) < (i.1 1 : ℕ) := i.2 (by norm_num : (0 : Fin 2) < 1)
    refine Fin.cases ?_ ?_ a
    · exact Fin.ext (by omega : ((i.1 0 : ℕ)) = ((0 : Fin 2) : ℕ))
    · intro a1
      have ha1 : a1 = 0 := Subsingleton.elim _ _
      subst ha1
      exact Fin.ext (by omega : ((i.1 1 : ℕ)) = ((1 : Fin 2) : ℕ))

end TwoCoverIndex

end ModularCurves
