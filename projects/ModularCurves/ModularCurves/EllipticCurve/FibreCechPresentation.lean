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

/-! ## Ordered Čech indices of a two-element cover

The Čech machinery indexes covers by a `Type u`, so the two-element cover is indexed by
`ULift.{u} (Fin 2)`. -/

namespace TwoCoverIndex

open AlgebraicGeometry.Scheme.Modules

/-- Degree-zero ordered Čech indices of a two-element cover are the two singletons. -/
def zeroEquiv : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 ≃ Fin 2 where
  toFun i := (i.1 0).down
  invFun j := ⟨fun _ => ⟨j⟩, fun a b hab => absurd hab (by omega)⟩
  left_inv i := by
    apply Subtype.ext
    funext a
    have : a = 0 := by omega
    rw [this]
  right_inv j := rfl

/-- The unique degree-one ordered Čech index of a two-element cover: the full tuple `(0, 1)`. -/
instance : Unique (Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1) where
  default := ⟨fun a => ⟨a⟩, fun a b h => show (a : ℕ) < b from h⟩
  uniq i := by
    apply Subtype.ext
    funext a
    show i.1 a = ⟨a⟩
    have b0 : ((i.1 0).down : ℕ) < 2 := (i.1 0).down.isLt
    have b1 : ((i.1 1).down : ℕ) < 2 := (i.1 1).down.isLt
    have h01 : ((i.1 0).down : ℕ) < ((i.1 1).down : ℕ) :=
      i.2 (by norm_num : (0 : Fin 2) < 1)
    have hcomp : ∀ (b : Fin 2), (i.1 b).down = b → i.1 b = ⟨b⟩ := by
      intro b hb
      cases hi : i.1 b
      rw [← hb, hi]
    refine Fin.cases ?_ ?_ a
    · exact hcomp 0 (Fin.ext (by omega : (((i.1 0).down : ℕ)) = ((0 : Fin 2) : ℕ)))
    · intro a1
      have ha1 : a1 = 0 := Subsingleton.elim _ _
      subst ha1
      exact hcomp 1 (Fin.ext (by omega : (((i.1 1).down : ℕ)) = ((1 : Fin 2) : ℕ)))

end TwoCoverIndex

namespace FibreRR

section TwoCoverCech

open AlgebraicGeometry Scheme.Modules

variable {k K : Type u} [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
  (U : ULift.{u} (Fin 2) → X.Opens)

/-- The unique degree-one ordered index of a two-element cover. -/
noncomputable abbrev twoCoverIdx1 :
    Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 := default

/-- The restriction from the `k`-th deleted chart factor to the overlap factor — the exact
morphism appearing in the `k`-th coface of the ordered Čech differential. -/
noncomputable def twoCoverRes (k : Fin 2) :
    baseCechFactor π M U 0 ((twoCoverIdx1.delete k)).1 ⟶
      baseCechFactor π M U 1 twoCoverIdx1.1 :=
  (baseModulePresheaf π M).map
    (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ twoCoverIdx1.1).op

theorem zeroEquiv_delete_one :
    TwoCoverIndex.zeroEquiv (twoCoverIdx1.delete 1) = 0 := rfl

theorem zeroEquiv_delete_zero :
    TwoCoverIndex.zeroEquiv (twoCoverIdx1.delete 0) = 1 := rfl

/-- Every degree-zero index of a two-element cover is one of the two deletions of the unique
degree-one index. -/
theorem idx0_eq_delete_or (i : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0) :
    i = twoCoverIdx1.delete 1 ∨ i = twoCoverIdx1.delete 0 := by
  rcases Fin.exists_fin_two.mp ⟨TwoCoverIndex.zeroEquiv i, rfl⟩ with h0 | h1
  · left
    apply TwoCoverIndex.zeroEquiv.injective
    rw [h0, zeroEquiv_delete_one]
  · right
    apply TwoCoverIndex.zeroEquiv.injective
    rw [h1, zeroEquiv_delete_zero]

/-- **(`AP2-A1b`, scheme form)** The degree-zero ordered Čech differential of a two-element
cover is surjective, given identifications of the two chart factors and the overlap factor
with `rrspaceOn` spaces intertwining the coface restrictions, and the function-field
splitting. -/
theorem twoCover_d01_surjective
    {S₀ S₁ : Set (PlaceA k K)} {D : DivisorA k K}
    (e₀ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 1)).1 : Type u) ≃+
      rrspaceOn k K S₀ D)
    (e₁ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 0)).1 : Type u) ≃+
      rrspaceOn k K S₁ D)
    (eC : (baseCechFactor π M U 1 twoCoverIdx1.1 : Type u) ≃+
      rrspaceOn k K (S₀ ∩ S₁) D)
    (h₀ : ∀ x, (eC ((twoCoverRes π M U 1).hom x) : K) = (e₀ x : K))
    (h₁ : ∀ x, (eC ((twoCoverRes π M U 0).hom x) : K) = (e₁ x : K))
    (split : ∀ g : K, memRRspaceOn k K (S₀ ∩ S₁) D g →
      ∃ a b : K, memRRspaceOn k K S₀ D a ∧ memRRspaceOn k K S₁ D b ∧ g = a - b) :
    Function.Surjective
      ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom := by
  classical
  -- surjectivity of the pair-to-overlap difference map, from the abstract transport
  have habstract := surjective_sub_of_addEquiv_rrspaceOn (k := k) (K := K)
    ((twoCoverRes π M U 1).hom.toAddMonoidHom) ((twoCoverRes π M U 0).hom.toAddMonoidHom)
    e₀ e₁ eC h₀ h₁ split
  -- reduce the categorical statement to the concrete one through the product isos
  intro y
  -- the overlap component of the target
  obtain ⟨⟨p₀, p₁⟩, hp⟩ := habstract
    ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
      baseCechFactor π M U 1 j.1) twoCoverIdx1).hom y)
  -- assemble the degree-zero cochain from the two components
  let x : Scheme.Modules.orderedBaseCechTerm π M U 0 := fun i =>
    if h : i = twoCoverIdx1.delete 1 then h ▸ p₀
    else (idx0_eq_delete_or i).resolve_left h ▸ p₁
  refine ⟨(Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).inv.hom x, ?_⟩
  -- the two degree-zero indices are distinct, and the assembled components read off
  have hne : (twoCoverIdx1 : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1).delete 0 ≠
      twoCoverIdx1.delete 1 := by
    intro h
    have h' := congrArg (TwoCoverIndex.zeroEquiv.{u}) h
    rw [zeroEquiv_delete_zero, zeroEquiv_delete_one] at h'
    exact absurd h' (by decide)
  -- iso components are the categorical projections; projections read off the cochain
  have hbridge : ∀ z : (Scheme.Modules.orderedBaseCechObject π M U 1 : Type u),
      (Scheme.Modules.orderedBaseCechObjectIsoPi π M U 1).toLinearEquiv z twoCoverIdx1 =
        (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
          baseCechFactor π M U 1 j.1) twoCoverIdx1).hom z := fun z =>
    ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_hom_ker_subtype
        (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
          baseCechFactor π M U 1 j.1) twoCoverIdx1) z
  have hproj : ∀ i : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0,
      (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) i).hom
          ((Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).inv.hom x) = x i := fun i =>
    ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_inv_kernel_ι
        (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) i) x
  -- compare componentwise through the pi iso at the unique degree-one index
  apply (Scheme.Modules.orderedBaseCechObjectIsoPi π M U 1).toLinearEquiv.injective
  funext j
  have hj : j = twoCoverIdx1 := Subsingleton.elim _ _
  subst hj
  refine (hbridge _).trans (Eq.trans ?_ (hbridge y).symm)
  rw [Scheme.Modules.orderedBaseCechComplex_d]
  refine Eq.trans (show _ = ((Scheme.Modules.orderedBaseCechDifferential π M U 0) ≫
    Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
      baseCechFactor π M U 1 j.1) twoCoverIdx1).hom
        ((Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).inv.hom x) from rfl) ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (Scheme.Modules.orderedBaseCechDifferential_zero_comp_π_sub π M U twoCoverIdx1)
    ((Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).inv.hom x)) ?_
  refine Eq.trans (show _ = (twoCoverRes π M U 0).hom
      ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 0)).hom
          ((Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).inv.hom x)) -
      (twoCoverRes π M U 1).hom
        ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom
            ((Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).inv.hom x)) from rfl) ?_
  rw [hproj, hproj,
    show x (twoCoverIdx1.delete 0) = p₁ from by simp only [x, dif_neg hne],
    show x (twoCoverIdx1.delete 1) = p₀ from by simp only [x, dif_pos]]
  exact hp

/-- Membership in the kernel of the degree-zero two-cover differential is agreement of the two
coface restrictions at the unique overlap index. -/
theorem twoCover_mem_ker_iff
    (w : (Scheme.Modules.orderedBaseCechObject π M U 0 : Type u)) :
    ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w = 0 ↔
      (twoCoverRes π M U 0).hom
        ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 0)).hom w) =
      (twoCoverRes π M U 1).hom
        ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w) := by
  have hbridge : ∀ z : (Scheme.Modules.orderedBaseCechObject π M U 1 : Type u),
      (Scheme.Modules.orderedBaseCechObjectIsoPi π M U 1).toLinearEquiv z twoCoverIdx1 =
        (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
          baseCechFactor π M U 1 j.1) twoCoverIdx1).hom z := fun z =>
    ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_hom_ker_subtype
        (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
          baseCechFactor π M U 1 j.1) twoCoverIdx1) z
  have hcomp : (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
        baseCechFactor π M U 1 j.1) twoCoverIdx1).hom
          (((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w) =
      (twoCoverRes π M U 0).hom
        ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 0)).hom w) -
      (twoCoverRes π M U 1).hom
        ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w) := by
    rw [Scheme.Modules.orderedBaseCechComplex_d]
    refine Eq.trans (show _ = ((Scheme.Modules.orderedBaseCechDifferential π M U 0) ≫
      Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
        baseCechFactor π M U 1 j.1) twoCoverIdx1).hom w from rfl) ?_
    exact ConcreteCategory.congr_hom
      (Scheme.Modules.orderedBaseCechDifferential_zero_comp_π_sub π M U twoCoverIdx1) w
  constructor
  · intro h0
    have hz : (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
        baseCechFactor π M U 1 j.1) twoCoverIdx1).hom
          (((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w) = 0 := by
      rw [h0]
      exact map_zero _
    exact sub_eq_zero.mp (hcomp.symm.trans hz)
  · intro heq
    have hcomp0 : (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1 =>
        baseCechFactor π M U 1 j.1) twoCoverIdx1).hom
          (((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w) = 0 :=
      hcomp.trans (sub_eq_zero.mpr heq)
    apply (Scheme.Modules.orderedBaseCechObjectIsoPi π M U 1).toLinearEquiv.injective
    funext j
    have hj : j = twoCoverIdx1 := Subsingleton.elim _ _
    subst hj
    exact ((hbridge _).trans hcomp0).trans
      (congrFun (map_zero
        ((Scheme.Modules.orderedBaseCechObjectIsoPi π M U 1).toLinearEquiv))
        twoCoverIdx1).symm

/-- The `H⁰` reading of a kernel element: through the chart identifications, a Čech cocycle in
degree zero is a single function satisfying both charts' bounds — a Riemann–Roch space element.
Stated for the `U 0`-component; the kernel condition and the compatibilities force the
`U 1`-component to read off the same function. -/
theorem mem_RRspace_of_mem_ker
    (P : TwoChartPlaces k K) {D : DivisorA k K}
    (e₀ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 1)).1 : Type u) ≃+
      rrspaceOn k K P.S₀ D)
    (e₁ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 0)).1 : Type u) ≃+
      rrspaceOn k K P.S₁ D)
    (eC : (baseCechFactor π M U 1 twoCoverIdx1.1 : Type u) ≃+
      rrspaceOn k K (P.S₀ ∩ P.S₁) D)
    (h₀ : ∀ x, (eC ((twoCoverRes π M U 1).hom x) : K) = (e₀ x : K))
    (h₁ : ∀ x, (eC ((twoCoverRes π M U 0).hom x) : K) = (e₁ x : K))
    (w : (Scheme.Modules.orderedBaseCechObject π M U 0 : Type u))
    (hw : ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w = 0) :
    memRRspace k K D
      ((e₀ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w) : K)) := by
  have hker := (twoCover_mem_ker_iff π M U w).mp hw
  -- the two chart readings agree in `K`
  have hagree : ((e₁ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
      baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 0)).hom w) : K)) =
      ((e₀ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w) : K)) := by
    rw [← h₁, ← h₀, hker]
  rw [(P.memRRspace_iff_memRRspaceOn_and D _)]
  constructor
  · exact (e₀ _).2
  · rw [← hagree]
    exact (e₁ _).2

/-- Components of a cochain assembled through the product iso. -/
theorem isoPiInv_component (n : ℕ) (x : Scheme.Modules.orderedBaseCechTerm π M U n)
    (i : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) n) :
    (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) n =>
      baseCechFactor π M U n j.1) i).hom
        ((Scheme.Modules.orderedBaseCechObjectIsoPi π M U n).inv.hom x) = x i :=
  ConcreteCategory.congr_hom
    (ModuleCat.piIsoPi_inv_kernel_ι
      (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) n =>
        baseCechFactor π M U n j.1) i) x

/-- A degree-zero cochain of a two-element cover is determined by its two components. -/
theorem twoCover_cochain_ext
    {w w' : (Scheme.Modules.orderedBaseCechObject π M U 0 : Type u)}
    (h1 : (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
      baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w =
      (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w')
    (h0 : (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
      baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 0)).hom w =
      (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 0)).hom w') :
    w = w' := by
  have hbridge0 : ∀ (i : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0)
      (z : (Scheme.Modules.orderedBaseCechObject π M U 0 : Type u)),
      (Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).toLinearEquiv z i =
        (Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) i).hom z := fun i z =>
    ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_hom_ker_subtype
        (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
          baseCechFactor π M U 0 j.1) i) z
  apply (Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).toLinearEquiv.injective
  funext i
  rcases idx0_eq_delete_or i with rfl | rfl
  · exact (hbridge0 _ w).trans (h1.trans (hbridge0 _ w').symm)
  · exact (hbridge0 _ w).trans (h0.trans (hbridge0 _ w').symm)

/-- The `H⁰` reading is injective on kernel elements: two cocycles with the same function-field
reading agree in both components. -/
theorem twoCover_ker_reading_injective
    {S₀ S₁ : Set (PlaceA k K)} {D : DivisorA k K}
    (e₀ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 1)).1 : Type u) ≃+
      rrspaceOn k K S₀ D)
    (e₁ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 0)).1 : Type u) ≃+
      rrspaceOn k K S₁ D)
    (eC : (baseCechFactor π M U 1 twoCoverIdx1.1 : Type u) ≃+
      rrspaceOn k K (S₀ ∩ S₁) D)
    (h₀ : ∀ x, (eC ((twoCoverRes π M U 1).hom x) : K) = (e₀ x : K))
    (h₁ : ∀ x, (eC ((twoCoverRes π M U 0).hom x) : K) = (e₁ x : K))
    {w w' : (Scheme.Modules.orderedBaseCechObject π M U 0 : Type u)}
    (hw : ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w = 0)
    (hw' : ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w' = 0)
    (heq : ((e₀ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
      baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w) : K)) =
      ((e₀ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w') : K))) :
    w = w' := by
  have hagree : ∀ {z : (Scheme.Modules.orderedBaseCechObject π M U 0 : Type u)},
      ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom z = 0 →
      ((e₁ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 0)).hom z) : K)) =
      ((e₀ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom z) : K)) := by
    intro z hz
    have hker := (twoCover_mem_ker_iff π M U z).mp hz
    rw [← h₁, ← h₀, hker]
  apply twoCover_cochain_ext π M U
  · exact e₀.injective (Subtype.ext heq)
  · refine e₁.injective (Subtype.ext ?_)
    rw [hagree hw, hagree hw', heq]

/-- The `H⁰` reading is surjective onto the Riemann–Roch space: every function satisfying both
charts' bounds assembles into a kernel cocycle reading off to it. -/
theorem twoCover_ker_reading_surjective
    {S₀ S₁ : Set (PlaceA k K)} {D : DivisorA k K}
    (e₀ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 1)).1 : Type u) ≃+
      rrspaceOn k K S₀ D)
    (e₁ : (baseCechFactor π M U 0 ((twoCoverIdx1.delete 0)).1 : Type u) ≃+
      rrspaceOn k K S₁ D)
    (eC : (baseCechFactor π M U 1 twoCoverIdx1.1 : Type u) ≃+
      rrspaceOn k K (S₀ ∩ S₁) D)
    (h₀ : ∀ x, (eC ((twoCoverRes π M U 1).hom x) : K) = (e₀ x : K))
    (h₁ : ∀ x, (eC ((twoCoverRes π M U 0).hom x) : K) = (e₁ x : K))
    (f : K) (hf : memRRspace k K D f) :
    ∃ w : (Scheme.Modules.orderedBaseCechObject π M U 0 : Type u),
      ((Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom w = 0 ∧
      ((e₀ ((Pi.π (fun j : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 0 =>
        baseCechFactor π M U 0 j.1) (twoCoverIdx1.delete 1)).hom w) : K)) = f := by
  classical
  have hne : (twoCoverIdx1 : Scheme.Modules.OrderedCechIndex (ULift.{u} (Fin 2)) 1).delete 0 ≠
      twoCoverIdx1.delete 1 := by
    intro h
    have h' := congrArg (TwoCoverIndex.zeroEquiv.{u}) h
    rw [zeroEquiv_delete_zero, zeroEquiv_delete_one] at h'
    exact absurd h' (by decide)
  let x : Scheme.Modules.orderedBaseCechTerm π M U 0 := fun i =>
    if h : i = twoCoverIdx1.delete 1 then h ▸ (e₀.symm ⟨f, fun v _ => hf v⟩)
    else (idx0_eq_delete_or i).resolve_left h ▸ (e₁.symm ⟨f, fun v _ => hf v⟩)
  have hx1 : x (twoCoverIdx1.delete 1) = e₀.symm ⟨f, fun v _ => hf v⟩ := by
    simp only [x, dif_pos]
  have hx0 : x (twoCoverIdx1.delete 0) = e₁.symm ⟨f, fun v _ => hf v⟩ := by
    simp only [x, dif_neg hne]
  refine ⟨(Scheme.Modules.orderedBaseCechObjectIsoPi π M U 0).inv.hom x, ?_, ?_⟩
  · rw [twoCover_mem_ker_iff, isoPiInv_component, isoPiInv_component, hx0, hx1]
    apply eC.injective
    apply Subtype.ext
    rw [h₁, h₀, e₀.apply_symm_apply, e₁.apply_symm_apply]
  · rw [isoPiInv_component, hx1, e₀.apply_symm_apply]

end TwoCoverCech

end FibreRR

end ModularCurves
