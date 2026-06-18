/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.GoodFiber
import HasseWeil.WeilPairing.GenericCovarianceGeneral
import HasseWeil.EC.IsogenyKernel
import HasseWeil.Curves.Differentials

/-!
# `#ker β = deg β` for a separable isogeny with a coordinate witness (ROUTE-W, W-3)

**Silverman III.4.10(c), the good-fibre count**: for a separable endomorphism isogeny
`β` (the `Basic` structure with stored `toAddMonoidHom`) over an algebraically closed
field, with a coordinate-ring witness `cd` for the pullback and the cofinite
pullback-evaluation coherence `PullbackEvaluation β bad` between the stored point map
and the stored pullback, the kernel has exactly `deg β` elements:

  `Nat.card β.kernel = β.degree`.

The proof is the classical good-fibre argument:
1. layer 1 (`Curves/GoodFiber.lean`) produces a smooth point `Q` — avoiding the images
   of the finite coherence bad set — whose `toPointMap cd`-fibre has `β.degree`
   elements (Σ e·f = deg, with `f = 1` over `K̄` and `e = 1` away from the finite
   different-ideal locus of W-1/W-2);
2. at such `Q` the stored point-map fibre over `Q` coincides with the
   `toPointMap cd`-fibre (`PullbackEvaluation` + value uniqueness), so it also has
   `β.degree` elements;
3. every nonempty fibre is a kernel coset (`Isogeny.fiber_card_eq_kernel_card`),
   transporting the count to the kernel.

## Main statements

* `Isogeny.endCurveMap` — the endomorphism `CurveMap` underlying a Basic `Isogeny`.
* `card_kernel_eq_degree_of_separable_coordHom` — the headline count.
* `card_kernel_eq_degree_of_separable_coordHom_hom` — the `bad = ∅` corollary in the
  `(φE, cd, h_pb, h_hom)` witness shape of `pullbackEvaluation_of_coordHom`.
* `finite_kernel_of_separable_coordHom` — kernel finiteness, a byproduct.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b), II.2.7, III.4.10(c).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- The endomorphism `CurveMap` underlying a Basic `Isogeny` (same pullback). -/
noncomputable def Isogeny.endCurveMap (β : Isogeny W.toAffine W.toAffine) :
    Curves.CurveMap (W_smooth W) (W_smooth W) :=
  ⟨β.pullback⟩

@[simp] theorem Isogeny.endCurveMap_pullback (β : Isogeny W.toAffine W.toAffine) :
    (β.endCurveMap W).pullback = β.pullback := rfl

/-- The `CurveMap` degree of `endCurveMap` is the isogeny degree (both are
`[K(E) : β^*K(E)]` for the same pullback-induced module structure). -/
theorem Isogeny.endCurveMap_degree (β : Isogeny W.toAffine W.toAffine) :
    (β.endCurveMap W).degree = β.degree :=
  rfl

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `toAffinePoint` is injective on smooth points (same proof as the private lemma in
`GenericCovarianceGeneral`). -/
theorem smoothPoint_toAffinePoint_injective :
    Function.Injective
      (fun P : (W_smooth W).SmoothPoint ↦ P.toAffinePoint) := by
  intro P Q h
  simp only [Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def] at h
  obtain ⟨hx, hy⟩ := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp h
  cases P; cases Q
  simp_all

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- A coordinate-ring element evaluates (in the `EvaluatesTo` valuation idiom) to its
residue `evalAt P` at every smooth point: `v_P(u − u(P)) < 1`.  Extracted from the
inline argument of `pullbackEvaluation_of_coordHom`. -/
theorem evaluatesTo_algebraMap_evalAt (P : (W_smooth W).SmoothPoint)
    (v : W.toAffine.CoordinateRing) :
    WeilPairing.EvaluatesTo W P (algebraMap W.toAffine.CoordinateRing KE v)
      ((W_smooth W).evalAt P v) := by
  have h0 : (W_smooth W).evalAt P
      (v - algebraMap F W.toAffine.CoordinateRing ((W_smooth W).evalAt P v)) = 0 :=
    (map_sub ((W_smooth W).evalAt P) _ _).trans
      (sub_eq_zero_of_eq ((W_smooth W).evalAt_algebraMap P _).symm)
  have hmem : v - algebraMap F W.toAffine.CoordinateRing ((W_smooth W).evalAt P v) ∈
      (W_smooth W).maximalIdealAt P :=
    (W_smooth W).ker_evalAt P ▸ RingHom.mem_ker.mpr h0
  have hrw : algebraMap W.toAffine.CoordinateRing KE v -
      algebraMap F KE ((W_smooth W).evalAt P v) =
      algebraMap W.toAffine.CoordinateRing KE
        (v - algebraMap F W.toAffine.CoordinateRing ((W_smooth W).evalAt P v)) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
  unfold WeilPairing.EvaluatesTo
  rw [hrw]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := W_smooth W) _ P).mpr hmem

/-- **Stored point map = coordinate point map at good points**: given the cofinite
pullback-evaluation witness and a coordinate-ring witness for the same pullback, the
stored `toAddMonoidHom` agrees with `toPointMap cd` at every point outside `bad`.
The witness gives `β P = (x', y')` with `x', y'` the values of `β^*x_gen, β^*y_gen` at
`P`; by `cd.compat` these pullbacks are coordinate-ring elements whose values are the
coordinates of `toPointMap cd P`, and values are unique (`EvaluatesTo.unique`). -/
theorem PullbackEvaluation.stored_eq_toPointMap {β : Isogeny W.toAffine W.toAffine}
    {bad : Set (W_smooth W).SmoothPoint}
    (hw : WeilPairing.PullbackEvaluation W β bad) (cd : (β.endCurveMap W).CoordHom)
    {P : (W_smooth W).SmoothPoint} (hP : P ∉ bad) :
    haveI : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
    β.toAddMonoidHom P.toAffinePoint =
      (Curves.CurveMap.toPointMap cd P).toAffinePoint := by
  haveI : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  obtain ⟨x', y', h', heq, hx, hy⟩ := hw P hP
  set Q := Curves.CurveMap.toPointMap cd P with hQdef
  -- the value of the pulled-back coordinate functions at `P` is the coordinate of `Q`
  -- (the `hvalx`/`hvaly` blocks of `pullbackEvaluation_of_coordHom`)
  have hvalx : (W_smooth W).evalAt P
      (cd.toAlgHom (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)) =
      Q.x := by
    have h1 := (Curves.CurveMap.evalAt_toPointMap cd P
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)).symm
    rw [Curves.CurveMap.evalAtPullback_apply] at h1
    refine h1.trans ?_
    rw [show algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X =
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C Polynomial.X) from rfl]
    exact (W_smooth W).evalAt_x Q
  have hvaly : (W_smooth W).evalAt P
      (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial)) = Q.y := by
    have h1 := (Curves.CurveMap.evalAt_toPointMap cd P
      (AdjoinRoot.root W.toAffine.polynomial)).symm
    rw [Curves.CurveMap.evalAtPullback_apply] at h1
    refine h1.trans ?_
    rw [show AdjoinRoot.root W.toAffine.polynomial =
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X from rfl]
    exact (W_smooth W).evalAt_y Q
  -- `β^*x_gen` and `β^*y_gen` are the coordinate-ring elements `cd.toAlgHom _`
  have hxgen : β.pullback (x_gen W) =
      algebraMap W.toAffine.CoordinateRing KE
        (cd.toAlgHom (algebraMap (Polynomial F) W.toAffine.CoordinateRing
          Polynomial.X)) :=
    cd.compat _
  have hygen : β.pullback (y_gen W) =
      algebraMap W.toAffine.CoordinateRing KE
        (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial)) :=
    cd.compat _
  -- value uniqueness identifies the witness coordinates with `Q`'s
  have hxx : x' = Q.x := by
    refine hx.unique ?_
    rw [hxgen, ← hvalx]
    exact evaluatesTo_algebraMap_evalAt W P _
  have hyy : y' = Q.y := by
    refine hy.unique ?_
    rw [hygen, ← hvaly]
    exact evaluatesTo_algebraMap_evalAt W P _
  rw [heq]
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxx, hyy⟩

/-- **III.4.10(c), good-fibre form — the W-3 headline**: a separable isogeny `β` over an
algebraically closed field, with a coordinate-ring witness `cd` for its pullback
(module-finite) and the cofinite pullback-evaluation coherence for its stored point
map, has `Nat.card β.kernel = β.degree`. -/
theorem card_kernel_eq_degree_of_separable_coordHom [IsAlgClosed F]
    [IsIntegrallyClosed W.toAffine.CoordinateRing]
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    (cd : (β.endCurveMap W).CoordHom)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Nat.card β.kernel = β.degree := by
  classical
  haveI hEll : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  haveI hIC : IsIntegrallyClosed (W_smooth W).CoordinateRing :=
    ‹IsIntegrallyClosed W.toAffine.CoordinateRing›
  -- separability in the `Algebra.IsSeparable` form consumed by the layer-1 engine
  have hsepAlg : @Algebra.IsSeparable (W_smooth W).FunctionField (W_smooth W).FunctionField
      _ _ (β.endCurveMap W).toAlgebra := hsep
  -- the finite set of points of the target to avoid: images of the coherence bad set
  -- under the coordinate point map and under the stored point map
  set avoid : Set (W_smooth W).SmoothPoint :=
    (Curves.CurveMap.toPointMap cd '' bad) ∪
      ((fun Q : (W_smooth W).SmoothPoint ↦ Q.toAffinePoint) ⁻¹'
        (β.toAddMonoidHom ''
          ((fun P : (W_smooth W).SmoothPoint ↦ P.toAffinePoint) '' bad)))
    with havoid_def
  have havoid : avoid.Finite :=
    (hbad.image _).union
      (Set.Finite.preimage (smoothPoint_toAffinePoint_injective W).injOn
        ((hbad.image _).image _))
  obtain ⟨Q, hQavoid, hQcard⟩ :=
    Curves.CurveMap.exists_good_fiber_card_eq_degree (β.endCurveMap W) cd
      hsepAlg havoid
  rw [havoid_def, Set.mem_union, not_or] at hQavoid
  obtain ⟨hQ1, hQ2⟩ := hQavoid
  -- every point of the `toPointMap`-fibre over `Q` is good, and the stored map agrees there
  have hforward : ∀ P : {P : (W_smooth W).SmoothPoint //
      Curves.CurveMap.toPointMap cd P = Q},
      β.toAddMonoidHom P.1.toAffinePoint = Q.toAffinePoint := by
    rintro ⟨P, hP⟩
    have hPgood : P ∉ bad := fun hmem ↦ hQ1 ⟨P, hmem, hP⟩
    have hco : β.toAddMonoidHom P.toAffinePoint =
        (Curves.CurveMap.toPointMap cd P).toAffinePoint :=
      PullbackEvaluation.stored_eq_toPointMap W hw cd hPgood
    rw [hco, hP]
  -- conversely every stored-fibre point comes from the `toPointMap`-fibre
  have hbackward : ∀ R : {R : W.toAffine.Point //
      β.toAddMonoidHom R = Q.toAffinePoint},
      ∃ P : {P : (W_smooth W).SmoothPoint //
        Curves.CurveMap.toPointMap cd P = Q}, P.1.toAffinePoint = R.1 := by
    rintro ⟨R, hR⟩
    rcases R with _ | ⟨x, y, hns⟩
    · -- the basepoint is not in the fibre: `β O = O ≠ Q`
      exfalso
      have hβ0 : β.toAddMonoidHom WeierstrassCurve.Affine.Point.zero = 0 :=
        (congrArg β.toAddMonoidHom WeierstrassCurve.Affine.Point.zero_def.symm).trans
          (map_zero β.toAddMonoidHom)
      rw [hβ0, WeierstrassCurve.Affine.Point.zero_def,
        Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def] at hR
      simp at hR
    · -- an affine fibre point is good, and coherence puts it in the `toPointMap`-fibre
      have hPgood : (⟨x, y, hns⟩ : (W_smooth W).SmoothPoint) ∉ bad := by
        intro hmem
        exact hQ2 ⟨(⟨x, y, hns⟩ : (W_smooth W).SmoothPoint).toAffinePoint,
          ⟨_, hmem, rfl⟩, hR⟩
      have hco : β.toAddMonoidHom
          (⟨x, y, hns⟩ : (W_smooth W).SmoothPoint).toAffinePoint =
          (Curves.CurveMap.toPointMap cd ⟨x, y, hns⟩).toAffinePoint :=
        PullbackEvaluation.stored_eq_toPointMap W hw cd hPgood
      refine ⟨⟨⟨x, y, hns⟩, ?_⟩, rfl⟩
      apply smoothPoint_toAffinePoint_injective W
      change (Curves.CurveMap.toPointMap cd ⟨x, y, hns⟩).toAffinePoint = Q.toAffinePoint
      rw [← hco]
      exact hR
  -- the two fibres have the same cardinality
  have hfib : Nat.card {P : (W_smooth W).SmoothPoint //
      Curves.CurveMap.toPointMap cd P = Q} =
      Nat.card {R : W.toAffine.Point // β.toAddMonoidHom R = Q.toAffinePoint} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun P ↦ ⟨P.1.toAffinePoint, hforward P⟩) ⟨?_, ?_⟩)
    · intro P P' h
      exact Subtype.ext (smoothPoint_toAffinePoint_injective W
        (congrArg Subtype.val h))
    · intro R
      obtain ⟨P, hP⟩ := hbackward R
      exact ⟨P, Subtype.ext hP⟩
  -- transport the good-fibre count to the kernel through the coset structure
  have hcard_fib : Nat.card {R : W.toAffine.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} = β.degree := by
    rw [← hfib, hQcard]
    exact Isogeny.endCurveMap_degree W β
  have hpos : 0 < Nat.card {R : W.toAffine.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} := by
    rw [hcard_fib]
    exact isogeny_degree_pos W β
  obtain ⟨⟨P₀, hP₀⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  rw [← Isogeny.fiber_card_eq_kernel_card β hP₀]
  exact hcard_fib

/-- Kernel finiteness, a byproduct of the count (`deg β > 0`). -/
theorem finite_kernel_of_separable_coordHom [IsAlgClosed F]
    [IsIntegrallyClosed W.toAffine.CoordinateRing]
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    (cd : (β.endCurveMap W).CoordHom)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Finite β.kernel := by
  have h := card_kernel_eq_degree_of_separable_coordHom W β hsep cd hbad hw
  refine Nat.finite_of_card_ne_zero ?_
  rw [h]
  exact (isogeny_degree_pos W β).ne'

/-- **III.4.10(c) in the `(φE, cd, h_pb, h_hom)` witness shape** of
`pullbackEvaluation_of_coordHom`: an `EC.Isogeny` carrying a `CoordHom` whose pullback
and point map agree with `β`'s discharges the coherence with `bad = ∅`, so the count
follows from the headline. -/
theorem card_kernel_eq_degree_of_separable_coordHom_hom [IsAlgClosed F]
    [IsIntegrallyClosed W.toAffine.CoordinateRing]
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    (φE : EC.Isogeny W.toAffine W.toAffine) (cd : φE.toCurveMap.CoordHom)
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φE.toPointMap cd P) :
    Nat.card β.kernel = β.degree := by
  have hw := WeilPairing.pullbackEvaluation_of_coordHom W φE cd β h_pb h_hom
  have compat' : ∀ u : W.toAffine.CoordinateRing,
      (β.endCurveMap W).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField u) =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (cd.toAlgHom u) :=
    fun u ↦ by
      have h := cd.compat u
      rw [h_pb] at h
      exact h
  exact card_kernel_eq_degree_of_separable_coordHom W β hsep ⟨cd.toAlgHom, compat'⟩
    Set.finite_empty hw

end HasseWeil
