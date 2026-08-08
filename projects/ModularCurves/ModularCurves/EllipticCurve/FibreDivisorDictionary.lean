/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Vendored.RiemannRoch.EllipticCurve.GenusOne
import ModularCurves.Vendored.RiemannRoch.Genus.AdeleQuotient

/-!
# Function-field facts for the degree-one fibre package (`AP2-A1b/c`, field level)

The two Riemann–Roch inputs of `AP2-A1`, stated in the vendored function-field vocabulary
(`ModularCurves/Vendored/RiemannRoch`, `FunctionField.Chart` track) for an elliptic function
field `K = Frac(W.CoordinateRing)`:

* `ell_eq_one_of_deg_eq_one` — `ℓ(D) = 1` for every degree-one divisor (`h⁰ = 1`, `AP2-A1c`);
* `exists_sub_of_memRRspaceOn_inter` — the two-chart Čech splitting: a function satisfying the
  `D`-bounds only on an overlap set of places splits as a difference of functions satisfying
  the bounds on each chart's places (`AP2-A1b` core).

The splitting is strong approximation in disguise: for `deg D = 1` on a genus-one field the
defect equals the genus on the nose, so the vendored
`adeleSubmodule_top_eq_adeleFilt_add_diagonal` gives `A = A(D) + K`; splitting the adele
carrying `g` on the places missing from one chart hands back the two chart sections. No
pole-peeling induction is needed.

`memRRspaceOn P D` restricts the vendored `memRRspace` bound to a set `P` of places — the
section spaces of the two affine charts and of their overlap in the Čech complex of a
presented invertible sheaf (`AP2-A1a`, `FibreCechPresentation` downstream).
-/

open FunctionField FunctionField.Chart Polynomial

open scoped Polynomial RatFunc WithZero

namespace ModularCurves

namespace FibreRR

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

/-- The `memRRspace` bound restricted to a set of places: `ord_v f ≥ -D v` for `v ∈ P` only.
For `P = Set.univ` this is the vendored `memRRspace`; for the place sets of the two affine
charts of the projective Weierstrass model it is the chart-section space of `𝒪(D)`. -/
def memRRspaceOn (P : Set (PlaceA k K)) (D : DivisorA k K) (f : K) : Prop :=
  ∀ v ∈ P, placeValuation k K v f ≤ WithZero.exp (D v)

theorem memRRspaceOn_univ_iff (D : DivisorA k K) (f : K) :
    memRRspaceOn k K Set.univ D f ↔ memRRspace k K D f :=
  ⟨fun h v => h v trivial, fun h v _ => h v⟩

theorem memRRspaceOn_mono {P Q : Set (PlaceA k K)} (hPQ : P ⊆ Q) {D : DivisorA k K} {f : K}
    (hf : memRRspaceOn k K Q D f) : memRRspaceOn k K P D f :=
  fun v hv => hf v (hPQ hv)

/-- The chart-section space: functions obeying the `D`-bound at the places of `P`, as a
`k`-submodule of `K`. For `P = Set.univ` this is the vendored `RRspace`. -/
def rrspaceOn (P : Set (PlaceA k K)) (D : DivisorA k K) : Submodule k K where
  carrier := {f | memRRspaceOn k K P D f}
  zero_mem' := fun v _ => by
    rw [map_zero]
    exact zero_le'
  add_mem' {f g} hf hg := fun v hv =>
    le_trans (Valuation.map_add _ f g) (max_le (hf v hv) (hg v hv))
  smul_mem' c f hf := fun v hv => by
    rw [Algebra.smul_def, map_mul]
    calc placeValuation k K v (algebraMap k K c) * placeValuation k K v f
        ≤ 1 * WithZero.exp (D v) :=
          mul_le_mul' (placeValuation_algebraMap_le_one k K v c) (hf v hv)
      _ = WithZero.exp (D v) := one_mul _

@[simp]
theorem mem_rrspaceOn_iff (P : Set (PlaceA k K)) (D : DivisorA k K) (f : K) :
    f ∈ rrspaceOn k K P D ↔ memRRspaceOn k K P D f :=
  Iff.rfl

section Elliptic

variable {k K}
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
  [IsScalarTower k[X] W.CoordinateRing K]

include W

/-- **(`AP2-A1c`)** On an elliptic function field, every degree-one divisor has `ℓ(D) = 1`:
Riemann–Roch with the invariant differential's zero canonical divisor and `ℓ(-D) = 0`. -/
theorem ell_eq_one_of_deg_eq_one {D : DivisorA k K} (hD : deg k K D = 1) :
    ell k K D = 1 := by
  have hcan : IsCanonical k K (0 : DivisorA k K) :=
    WeierstrassCurve.Affine.Chart.divOmega_invariant_differential W K
  have hRR := riemann_roch (k := k) (K := K) hcan D
  have hgen := WeierstrassCurve.Affine.Chart.genus_eq_one W K
  have hneg : ell k K ((0 : DivisorA k K) - D) = 0 := by
    apply RRspace_neg_deg_ell (k := k) (K := K)
    rw [deg_sub, deg_zero, hD]
    norm_num
  rw [hgen, hneg, hD] at hRR
  omega

/-- **(`AP2-A1b` input)** On an elliptic function field, every divisor of positive degree is
nonspecial: `i(D) = 0`. Genus one makes `deg D ≥ 1 = 2g - 1` the sharp bound. -/
theorem indexOfSpecialty_eq_zero_of_one_le_deg {D : DivisorA k K} (hD : 1 ≤ deg k K D) :
    indexOfSpecialty k K D = 0 := by
  have hcan : IsCanonical k K (0 : DivisorA k K) :=
    WeierstrassCurve.Affine.Chart.divOmega_invariant_differential W K
  have hdual := indexOfSpecialty_eq_ell_sub (k := k) (K := K) hcan D
  have hneg : ell k K ((0 : DivisorA k K) - D) = 0 := by
    apply RRspace_neg_deg_ell (k := k) (K := K)
    rw [deg_sub, deg_zero]
    omega
  omega

/-- **(`AP2-A1b` input)** Degree-one divisors on an elliptic function field realise the genus
as their defect, which is what the vendored strong approximation consumes. -/
theorem defect_eq_genus_of_deg_eq_one {D : DivisorA k K} (hD : deg k K D = 1) :
    defect k K D = genus k K := by
  have hgen := WeierstrassCurve.Affine.Chart.genus_eq_one W K
  have hell := ell_eq_one_of_deg_eq_one W hD
  dsimp only [defect]
  rw [hD, hell, hgen]
  norm_num

end Elliptic

section Split

variable {k K}

/-- **(`AP2-A1b` core: the two-chart Čech splitting)** If the full adele space satisfies
`A = A(D) + K` (vendored strong approximation, available whenever `defect D = genus`), then a
function `g` obeying the `D`-bounds on the overlap `S₀ ∩ S₁` of two place sets, the first of
which misses only finitely many places outside `S₁`, splits as `g = a - b` with `a` obeying
the bounds on all of `S₀` and `b` on all of `S₁`.

Proof: split the adele carrying `g` at the places of `S₀ \ S₁` and `0` elsewhere as
`β + diag c` with `β ∈ A(D)`; then `a := g - c` and `b := -c` work, reading the component
equations at each place. -/
theorem exists_sub_of_memRRspaceOn_inter {D : DivisorA k K}
    (hfull : topAdeleSubmodule k K = adeleFilt k K D + diagonalSubmodule k K)
    {S₀ S₁ : Set (PlaceA k K)} (hfin : (S₀ \ S₁).Finite)
    {g : K} (hg : memRRspaceOn k K (S₀ ∩ S₁) D g) :
    ∃ a b : K, memRRspaceOn k K S₀ D a ∧ memRRspaceOn k K S₁ D b ∧ g = a - b := by
  classical
  -- the adele carrying `g` exactly on the places missing from `S₁`
  have hmem : (fun v => if v ∈ S₀ \ S₁ then g else 0) ∈ adeleSubmodule k K := by
    change ∀ᶠ v in Filter.cofinite, _ ∈ placeValuationSubring k K v
    rw [Filter.eventually_cofinite]
    refine hfin.subset ?_
    intro v hv
    by_contra hvS
    apply hv
    rw [if_neg hvS]
    exact zero_mem _
  set α : AdeleSpace k K := ⟨fun v => if v ∈ S₀ \ S₁ then g else 0, hmem⟩ with hα
  have hαtop : α ∈ topAdeleSubmodule k K := trivial
  rw [hfull] at hαtop
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hαtop
  obtain ⟨c, rfl⟩ := hγ
  -- component equations: `α v = β v + c` for every place
  have hcomp : ∀ v : PlaceA k K, α.val v = β.val v + c := fun v =>
    congrFun (congrArg Subtype.val hβγ.symm) v
  have hβbound : ∀ v : PlaceA k K, placeValuation k K v (β.val v) ≤ WithZero.exp (D v) := hβ
  refine ⟨g - c, -c, ?_, ?_, by ring⟩
  · -- `a = g - c` on `S₀`
    intro v hv
    by_cases hvS : v ∈ S₁
    · -- overlap: `α v = 0`, so `c = -β v`, and `g` obeys the bound
      have h0 : α.val v = 0 := by
        rw [hα]
        exact if_neg (fun h => h.2 hvS)
      have hc : c = -β.val v := by
        have h := hcomp v
        rw [h0] at h
        linear_combination -h
      have hcv : placeValuation k K v c ≤ WithZero.exp (D v) := by
        rw [hc, Valuation.map_neg]
        exact hβbound v
      calc placeValuation k K v (g - c)
          ≤ max (placeValuation k K v g) (placeValuation k K v c) :=
            Valuation.map_sub _ _ _
        _ ≤ WithZero.exp (D v) := max_le (hg v ⟨hv, hvS⟩) hcv
    · -- missing from `S₁`: `α v = g`, so `g - c = β v`
      have hgv : α.val v = g := by
        rw [hα]
        exact if_pos ⟨hv, hvS⟩
      have hgc : g - c = β.val v := by
        have h := hcomp v
        rw [hgv] at h
        linear_combination h
      rw [hgc]
      exact hβbound v
  · -- `b = -c` on `S₁`: there `α v = 0`, so `c = -β v`
    intro v hv
    have h0 : α.val v = 0 := by
      rw [hα]
      exact if_neg (fun h => h.2 hv)
    have hc : c = -β.val v := by
      have h := hcomp v
      rw [h0] at h
      linear_combination -h
    rw [Valuation.map_neg, hc, Valuation.map_neg]
    exact hβbound v

end Split

section ChartPlaces

/-- The finite places — the points of the affine (`Z`-)chart of the projective Weierstrass
model, as coordinate places. -/
def finitePlaces : Set (PlaceA k K) := Set.range Sum.inl

/-- **(`AP2-A1a-i`)** The trivial-divisor `finitePlaces` bound carves out exactly the ring of
integers: `⋂_{v finite} O_v = ringOfIntegers` inside `K`. Forward is
`mem_integers_of_valuation_le_one` (Dedekind), backward is integrality of the image. -/
theorem memRRspaceOn_finitePlaces_zero_iff (f : K) :
    memRRspaceOn k K (finitePlaces k K) 0 f ↔
      f ∈ (algebraMap (ringOfIntegers k K) K).range := by
  constructor
  · intro hf
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have h := hf (Sum.inl v) ⟨v, rfl⟩
    simpa [placeValuation] using h
  · rintro ⟨g, rfl⟩ v hv
    obtain ⟨v, rfl⟩ := hv
    simpa [placeValuation] using
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) v g

variable {k K}
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
  [IsScalarTower k[X] W.CoordinateRing K]

/-- The vendored integral-closure identification commutes with the maps to `K`:
`algebraMap (ringOfIntegers) K (coordinateRingEquivIntegers r) = algebraMap CoordinateRing K r`. -/
theorem algebraMap_coordinateRingEquivIntegers (r : W.CoordinateRing) :
    algebraMap (ringOfIntegers k K) K
        (WeierstrassCurve.Affine.Chart.coordinateRingEquivIntegers W K r) =
      algebraMap W.CoordinateRing K r := by
  have hemb := IsIntegralClosure.algebraMap_equiv k[X] W.CoordinateRing K
    (ringOfIntegers k K) r
  exact hemb

/-- **(`AP2-A1a-i`, coordinate-ring form)** The finite-place bound carves out the coordinate
ring of the affine Weierstrass chart, through the vendored integral-closure identification. -/
theorem memRRspaceOn_finitePlaces_zero_iff_coordinateRing (f : K) :
    memRRspaceOn k K (finitePlaces k K) 0 f ↔
      f ∈ (algebraMap W.CoordinateRing K).range := by
  rw [memRRspaceOn_finitePlaces_zero_iff]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨(WeierstrassCurve.Affine.Chart.coordinateRingEquivIntegers W K).symm g, ?_⟩
    rw [← algebraMap_coordinateRingEquivIntegers W
      ((WeierstrassCurve.Affine.Chart.coordinateRingEquivIntegers W K).symm g),
      AlgEquiv.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    exact ⟨WeierstrassCurve.Affine.Chart.coordinateRingEquivIntegers W K g,
      algebraMap_coordinateRingEquivIntegers W g⟩

end ChartPlaces

end FibreRR

end ModularCurves
