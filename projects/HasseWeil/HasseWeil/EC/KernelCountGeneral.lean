/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.LocalizedDictionary
import HasseWeil.EC.KernelCount
import HasseWeil.EC.SeparableKernelTorsor
import HasseWeil.EC.IsogenyAG.DualGaloisDataUnconditional
import HasseWeil.WeilPairing.IsogenyWitnessReductions
import Mathlib.FieldTheory.Fixed

/-!
# `#ker β = deg β` for general separable isogenies (ROUTE-W, ticket W-3b)

**Silverman III.4.10(c) without a global coordinate-ring witness.**  A separable isogeny of
degree `> 1` has affine kernel points, where its pullback has poles — so no global
`CoordHom` exists and `EC/KernelCount.lean` does not apply.  This file closes the count for
the *general* separable class: the only witnesses are the finite coherence set `bad` and
the cofinite pullback-evaluation coherence `PullbackEvaluation β bad` between the stored
point map and the stored pullback (the irreducible tie between the two independent fields
of the abstract `Isogeny`).

* `≥` (the localized dictionary, `Curves/LocalizedDictionary.lean`): localizing the target
  coordinate ring away from a denominator `f₀` of the minimal polynomials of `x, y` over
  `β^*K(E)` produces a Dedekind pair `(Af, D)` with `Σ e·f = deg β`, `e = 1` off the
  finite different-ideal locus and `f = 1` over `K̄`; each maximal ideal of `D` over a
  good point `Q` *is* a smooth point evaluating the pulled-back coordinates to the
  coordinates of `Q`, distinct primes giving distinct points.  Through the coherence
  witness these are `deg β` distinct points of the *stored* fibre over `Q`.
* `≤` (the kernel-translation torsor): the same witness yields the generic-point
  covariance (`mapTranslateGenericPoint_of_pullbackEvaluation`), hence the kernel
  translation action `ker β ↪ Aut(K(E)/β^*K(E))` (`kernelTranslateForwardAut`), and
  `#Aut ≤ [K(E) : β^*K(E)] = deg β` (mathlib's `AlgEquiv.card_le`).
* Fibres are kernel cosets (`Isogeny.fiber_card_eq_kernel_card`), so
  `deg β ≤ #fibre = #ker β ≤ deg β`.

## Main statements

* `card_kernel_eq_degree_of_separable` — **the W-3b headline**: over an algebraically
  closed field, a separable `β` with the cofinite pullback-evaluation coherence has
  `Nat.card β.kernel = β.degree`.
* `finite_kernel_of_separable` — kernel finiteness, restated in the same witness shape.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b), III.4.10(c).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

set_option backward.isDefEq.respectTransparency false in
-- Instance resolution must identify `Module`/`Algebra` structures along different paths
-- (`FractionRing` vs `OreLocalization`), as in `HasseWeil/Curves/GoodAffineLocus.lean`.
set_option synthInstance.maxHeartbeats 400000 in
-- Typeclass search through the pinned `β.toAlgebra` structures is heartbeat-heavy,
-- exactly as in `HasseWeil/Curves/GoodFiber.lean` (same bumps).
set_option maxHeartbeats 1600000 in
-- The instantiation of the localized dictionary needs the matching elaboration budget.
/-- **III.4.10(c) for the general separable class — the W-3b headline**: a separable
isogeny `β` over an algebraically closed field, with only the cofinite
pullback-evaluation coherence `hw` for its stored point map (no global `CoordHom`), has
`Nat.card β.kernel = β.degree`. -/
theorem card_kernel_eq_degree_of_separable [IsAlgClosed F]
    [IsIntegrallyClosed W.toAffine.CoordinateRing]
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Nat.card β.kernel = β.degree := by
  classical
  haveI hEll : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  haveI hIC : IsIntegrallyClosed (W_smooth W).CoordinateRing :=
    ‹IsIntegrallyClosed W.toAffine.CoordinateRing›
  -- ===== the `≤` direction: kernel ↪ Aut(K(E)/β^*K(E)), #Aut ≤ deg =====
  have hgcomm := WeilPairing.mapTranslateGenericPoint_of_pullbackEvaluation W β hbad hw
  have hcov : ∀ k : β.kernel, ∀ z : KE,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
    fun k z ↦ WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β hgcomm k z
  have hker_fin : Finite β.kernel := finite_kernel_of_hcov W β hcov
  letI βAlg : Algebra KE KE := β.toAlgebra
  haveI hfd : @FiniteDimensional KE KE _ _ β.toAlgebra.toModule :=
    isogeny_finiteDimensional W β
  haveI hAutFin : Finite (@AlgEquiv KE KE KE _ _ _ β.toAlgebra β.toAlgebra) :=
    Finite.of_fintype _
  have hle1 : Nat.card β.kernel ≤
      Nat.card (@AlgEquiv KE KE KE _ _ _ β.toAlgebra β.toAlgebra) :=
    Nat.card_le_card_of_injective _ (kernelTranslateForwardAut_injective W β hcov)
  have hle2 : Nat.card (@AlgEquiv KE KE KE _ _ _ β.toAlgebra β.toAlgebra) ≤ β.degree := by
    have h := @AlgEquiv.card_le KE KE _ _ β.toAlgebra hfd
    rwa [← Nat.card_eq_fintype_card] at h
  have hle : Nat.card β.kernel ≤ β.degree := le_trans hle1 hle2
  -- ===== the `≥` direction: the localized fibre dictionary =====
  haveI hsepAlg : @Algebra.IsSeparable (W_smooth W).FunctionField (W_smooth W).FunctionField
      _ _ β.toAlgebra := hsep
  haveI twFKL : @IsScalarTower F KE KE _ β.toAlgebra.toSMul _ :=
    @IsScalarTower.of_algebraMap_eq F KE KE _ _ _ _ β.toAlgebra _
      fun c ↦ (β.pullback.commutes c).symm
  -- the denominator of the minimal polynomials of `x, y` over `β^*K(E)`
  obtain ⟨f₀, hf₀, hdx, hdy⟩ := @Curves.LocalizedDictionary.exists_denominator F _
    (W_smooth W) (W_smooth W) β.toAlgebra
  -- the good affine localization
  set Af := Localization.Away f₀ with hAf_def
  letI algAfK : Algebra Af (W_smooth W).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra (W_smooth W) f₀ hf₀
  haveI twAfK : letI := algAfK
      IsScalarTower (W_smooth W).CoordinateRing Af (W_smooth W).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra_isScalarTower (W_smooth W) f₀ hf₀
  letI algAfL : Algebra Af KE :=
    ((β.pullback.toRingHom).comp (algebraMap Af (W_smooth W).FunctionField)).toAlgebra
  haveI twAfKL : @IsScalarTower Af KE KE algAfK.toSMul β.toAlgebra.toSMul algAfL.toSMul :=
    @IsScalarTower.of_algebraMap_eq Af KE KE _ _ _ algAfK β.toAlgebra algAfL fun _ ↦ rfl
  -- the finite set of target points to avoid: possible images of the coherence bad set
  set badT : Set (W_smooth W).SmoothPoint := {Q' | ∃ p ∈ bad,
    WeilPairing.EvaluatesTo W p (β.pullback (x_gen W)) Q'.x ∧
    WeilPairing.EvaluatesTo W p (β.pullback (y_gen W)) Q'.y} with hbadT_def
  have hbadTfin : badT.Finite := by
    have hsub : badT ⊆ ⋃ p ∈ bad, {Q' : (W_smooth W).SmoothPoint |
        WeilPairing.EvaluatesTo W p (β.pullback (x_gen W)) Q'.x ∧
        WeilPairing.EvaluatesTo W p (β.pullback (y_gen W)) Q'.y} := by
      rintro Q' ⟨p, hp, h1, h2⟩
      exact Set.mem_biUnion hp ⟨h1, h2⟩
    refine Set.Finite.subset (Set.Finite.biUnion hbad fun p _ ↦ ?_) hsub
    refine Set.Subsingleton.finite ?_
    rintro Q₁ ⟨hx₁, hy₁⟩ Q₂ ⟨hx₂, hy₂⟩
    exact Curves.SmoothPlaneCurve.SmoothPoint.ext (hx₁.unique hx₂) (hy₁.unique hy₂)
  -- the localized good fibre
  obtain ⟨Q, hQbadT, S, hScard, hSpts⟩ :=
    @Curves.LocalizedDictionary.exists_good_fiber_points F _ (W_smooth W) f₀ Af _ _ _
      (W_smooth W) β.toAlgebra hfd algAfK twAfK algAfL twAfKL twFKL hEll hEll hsepAlg
      _ hIC hf₀ hdx hdy badT hbadTfin
  -- each produced point is in the *stored* fibre over `Q`
  have hfibmem : ∀ pt ∈ S, β.toAddMonoidHom pt.toAffinePoint = Q.toAffinePoint := by
    intro pt hpt
    obtain ⟨hvx, hvy⟩ := hSpts pt hpt
    have hex : WeilPairing.EvaluatesTo W pt (β.pullback (x_gen W)) Q.x := hvx
    have hey : WeilPairing.EvaluatesTo W pt (β.pullback (y_gen W)) Q.y := hvy
    have hptgood : pt ∉ bad := fun hmem ↦ hQbadT ⟨pt, hmem, hex, hey⟩
    obtain ⟨x', y', h', heq, hx, hy⟩ := hw pt hptgood
    have hxx : x' = Q.x := hx.unique hex
    have hyy : y' = Q.y := hy.unique hey
    rw [heq, Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]
    exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxx, hyy⟩
  -- the fibre has at least `deg β` elements
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hScard]
    exact isogeny_degree_pos W β
  obtain ⟨pt₀, hpt₀⟩ := hSne
  haveI hfib_fin : Finite {R : W.toAffine.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} :=
    Isogeny.fiber_finite_of_kernel_finite β hker_fin
  have hinj : Function.Injective (fun p : {x // x ∈ S} ↦
      (⟨p.1.toAffinePoint, hfibmem p.1 p.2⟩ :
        {R : W.toAffine.Point // β.toAddMonoidHom R = Q.toAffinePoint})) := by
    intro p₁ p₂ h
    exact Subtype.ext (smoothPoint_toAffinePoint_injective W (congrArg Subtype.val h))
  have hge : β.degree ≤ Nat.card {R : W.toAffine.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} := by
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe, hScard] at h1
  -- close: fibres are kernel cosets
  have hkereq : Nat.card {R : W.toAffine.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} = Nat.card β.kernel :=
    Isogeny.fiber_card_eq_kernel_card β (hfibmem pt₀ hpt₀)
  rw [hkereq] at hge
  exact le_antisymm hle hge

/-- Kernel finiteness for the general separable class, a byproduct (in fact it needs
neither separability nor algebraic closure of the count — only the coherence witness;
recorded in the W-3b witness shape for symmetry with `KernelCount`). -/
theorem finite_kernel_of_separable [IsAlgClosed F]
    (β : Isogeny W.toAffine W.toAffine)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Finite β.kernel :=
  finite_kernel_of_hcov W β fun k z ↦
    WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β
      (WeilPairing.mapTranslateGenericPoint_of_pullbackEvaluation W β hbad hw) k z

/-! ## The wall cascade for the general separable class

With `#ker β = deg β` now a theorem for any separable `β` carrying only the cofinite
coherence witness, the field-general W-4 cores make the Galois package unconditional
for the whole class: no `CoordHom`, no module-finiteness, no carried `h_normal`/`hdesc`. -/

section Cascade

variable [IsAlgClosed F] [IsIntegrallyClosed W.toAffine.CoordinateRing]

omit [IsIntegrallyClosed W.toAffine.CoordinateRing] in
/-- The kernel-translation covariance `xy_family` for the class (the generic-point engine
applied at the two generators). -/
theorem xy_family_of_pullbackEvaluation (β : Isogeny W.toAffine W.toAffine)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)) :=
  fun k ↦
    ⟨WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β
      (WeilPairing.mapTranslateGenericPoint_of_pullbackEvaluation W β hbad hw) k _,
     WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β
      (WeilPairing.mapTranslateGenericPoint_of_pullbackEvaluation W β hbad hw) k _⟩

/-- **`h_normal` is a theorem for the general separable class** (Silverman III.4.10c):
`K(E)/β^*K(E)` is normal for any separable `β` with the coherence witness. -/
theorem normal_of_separable_general (β : Isogeny W.toAffine W.toAffine)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    letI := β.toAlgebra
    Normal W.toAffine.FunctionField W.toAffine.FunctionField :=
  normal_of_xy_family_card W β (xy_family_of_pullbackEvaluation W β hbad hw)
    (card_kernel_eq_degree_of_separable W β hsep hbad hw)

/-- **`hdesc` is a theorem for the general separable class** (Silverman III.4.10c, the
generic-point translation torsor): every `σ ∈ Aut(K(E)/β^*K(E))` translates the generic
point by an `F`-rational kernel point. -/
theorem hdesc_of_separable_general (β : Isogeny W.toAffine W.toAffine)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W :=
  hdesc_of_xy_family_card W β (xy_family_of_pullbackEvaluation W β hbad hw)
    (card_kernel_eq_degree_of_separable W β hsep hbad hw)

/-- **`DualGaloisData φ` for the general separable class — fully unconditional**
(Silverman III.4.10–4.11, III.6.1): compared to the W-4
`dualGaloisData_of_pullbackEvaluation_unconditional`, the `CoordHom` and its
module-finiteness are gone.  Residuals: only `{h_pb, hsep, bad, hw}`. -/
noncomputable def dualGaloisData_of_pullbackEvaluation_general
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    EC.Isogeny.DualGaloisData φ :=
  dualGaloisData_of_pullbackEvaluation W φ β h_pb hsep
    (isogeny_degree_pos W β).ne' hbad hw
    (normal_of_separable_general W β hsep hbad hw)
    (hdesc_of_separable_general W β hsep hbad hw)
    (hν_mulByInt W (β.degree : ℤ)
      (by exact_mod_cast (isogeny_degree_pos W β).ne'))

/-- **`exists_dual` for the general separable class** (Silverman III.6.1): a separable
isogeny with only the cofinite pullback-evaluation coherence over `K̄` admits a reverse
isogeny — no `CoordHom`, no carried Galois witnesses. -/
theorem exists_dual_of_pullbackEvaluation_general
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) :=
  φ.exists_dual_of_witness
    (φ.hasDualWitness_of_galoisData
      (dualGaloisData_of_pullbackEvaluation_general W φ β h_pb hsep hbad hw))

end Cascade

end HasseWeil
