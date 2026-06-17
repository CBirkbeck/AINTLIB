/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TwoCurveGenericCovariance
import HasseWeil.EC.IsogenyAG.TwoCurveFixedField
import HasseWeil.EC.IsogenyAG.TwoCurveNormConorm
import HasseWeil.EC.KernelCount
import HasseWeil.Curves.LocalizedDictionary
import Mathlib.FieldTheory.Fixed

/-!
# `#ker β = deg β` for a general separable **two-curve** isogeny (ticket T-B1)

This is the two-curve port of `HasseWeil.card_kernel_eq_degree_of_separable`
(`HasseWeil/EC/KernelCountGeneral.lean`).  For a separable two-curve isogeny `β : Isogeny W₁ W₂`
over an algebraically closed field, carrying only the cofinite two-curve pullback-evaluation
coherence `PullbackEvaluation_twoCurve W₁ W₂ β bad`, we prove `Nat.card β.kernel = β.degree`.

The proof has the two standard halves (Silverman III.4.10(a,c)):

* **`≤` direction** (`kernel ↪ Aut(K(E₁)/β^*K(E₂))`, `#Aut ≤ deg β`): the committed two-curve PE-2
  `xy_family_of_pullbackEvaluation_twoCurve` gives the kernel-translation covariance on the two
  pullback generators; the two-curve generator extensionality
  `Isogeny.translate_pullback_invariance_of_xy_twoCurve` extends it to all of `K(E₂)`, giving the
  full covariance `hcov`.  The kernel then embeds injectively into the (finite, because
  `K(E₁)/β^*K(E₂)` is finite-dimensional by `isogeny_finiteDimensional_twoCurve`) automorphism
  group `Aut(K(E₁)/β^*K(E₂))`, and mathlib's `AlgEquiv.card_le` bounds `#Aut ≤ deg β`.
* **`≥` direction** (a good fibre has `≥ deg β` points): `Curves.LocalizedDictionary`'s
  `exists_good_fiber_points` is already two-curve; instantiated with `C₁ = W_smooth W₁`,
  `C₂ = W_smooth W₂`, `β.toAlgebra`, it produces a point `Q` of `E₂` with `deg β` distinct smooth
  points of `E₁` evaluating the pulled-back generators to `Q.x`, `Q.y`.  Through the coherence
  witness `hw` these are `deg β` distinct points of the *stored* fibre over `Q`, finite by
  `finite_fiber_twoCurve`.
* **Combine**: `Nat.card β.kernel ≤ deg β` (the `≤` direction) and `≥ deg β` (fibres are kernel
  cosets, `Isogeny.fiber_card_eq_kernel_card`) give equality.

## Main statements

* `card_kernel_eq_degree_twoCurve` — the ticket headline.
* `finite_fiber_twoCurve` — two-curve port of `PullbackEvaluation.finite_fiber`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b), III.4.10(a,c).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-! ### The `≤` direction: `kernel ↪ Aut(K(E₁)/β^*K(E₂))`, `#Aut ≤ deg β` -/

/-- **The full kernel-translation covariance from PE-2** (two-curve): the committed
`xy_family_of_pullbackEvaluation_twoCurve` gives covariance on the two pullback generators; the
two-curve generator extensionality extends it to all of `K(E₂)`. -/
theorem hcov_of_pullbackEvaluation_twoCurve [IsAlgClosed F]
    (β : Isogeny W₁ W₂) {bad : Set (W_smooth W₁).SmoothPoint}
    (hbad : bad.Finite) (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad) :
    ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z :=
  fun k z =>
    Isogeny.translate_pullback_invariance_of_xy_twoCurve β k.val
      (WeilPairing.xy_family_of_pullbackEvaluation_twoCurve W₁ W₂ β hbad hw k).1
      (WeilPairing.xy_family_of_pullbackEvaluation_twoCurve W₁ W₂ β hbad hw k).2 z

/-- **The kernel-translation forward map into `Aut(K(E₁)/β^*K(E₂))`** (two-curve), injective from
the covariance `hcov`.  This packages the injective map already used inside
`Isogeny.finite_kernel_of_hcov_twoCurve`. -/
noncomputable def kernelTranslateForwardAut_twoCurve
    (β : Isogeny W₁ W₂)
    (hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z) :
    β.kernel → (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      β.toAlgebra β.toAlgebra) :=
  fun k =>
    letI := β.toAlgebra
    AlgEquiv.ofRingEquiv (f := (translateAlgEquivOfPoint W₁ k.val).toRingEquiv)
      (fun r => hcov k r)

theorem kernelTranslateForwardAut_twoCurve_injective
    (β : Isogeny W₁ W₂)
    (hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z) :
    Function.Injective (kernelTranslateForwardAut_twoCurve β hcov) := by
  intro k₁ k₂ h
  apply Subtype.ext
  apply translateAlgEquivOfPoint_injective W₁
  refine AlgEquiv.ext fun z => ?_
  exact DFunLike.congr_fun h z

/-! ### The `≥` direction: a good fibre has `≥ deg β` points -/

/-- **All fibres of the stored point map are finite, two-curve** (port of
`WeilPairing.PullbackEvaluation.finite_fiber`).  The affine kernel is trapped inside `bad`, and a
fibre is a kernel coset; the proof references only the source curve `W₁` and the stored point
map. -/
theorem finite_fiber_twoCurve {β : Isogeny W₁ W₂}
    {bad : Set (W_smooth W₁).SmoothPoint}
    (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad)
    (hbad : bad.Finite) (Q : W₂.Point) :
    {P : (W_smooth W₁).SmoothPoint | β.toAddMonoidHom P.toAffinePoint = Q}.Finite := by
  -- the point-level kernel is finite: `0` plus the affine kernel, which lies inside `bad`.
  have hker : {R : W₁.Point | β.toAddMonoidHom R = 0}.Finite := by
    refine (Set.Finite.insert (0 : W₁.Point)
      ((hbad.image (fun P : (W_smooth W₁).SmoothPoint => P.toAffinePoint)))).subset ?_
    rintro (_ | ⟨x, y, hns⟩) hR
    · exact Set.mem_insert_iff.mpr (Or.inl WeierstrassCurve.Affine.Point.zero_def.symm)
    · refine Set.mem_insert_iff.mpr (Or.inr ⟨⟨x, y, hns⟩, ?_, rfl⟩)
      by_contra hnotbad
      obtain ⟨x', y', h', heq, -, -⟩ := hw ⟨x, y, hns⟩ hnotbad
      rw [Set.mem_setOf_eq] at hR
      have hcontra := WeierstrassCurve.Affine.Point.zero_def.symm.trans (hR.symm.trans heq)
      simp at hcontra
  -- a nonempty fibre injects into the kernel via subtraction of a base point.
  rcases Set.eq_empty_or_nonempty
    {P : (W_smooth W₁).SmoothPoint | β.toAddMonoidHom P.toAffinePoint = Q} with hemp | ⟨P₀, hP₀⟩
  · rw [hemp]; exact Set.finite_empty
  · refine Set.Finite.of_finite_image (f := fun P : (W_smooth W₁).SmoothPoint =>
      P.toAffinePoint - P₀.toAffinePoint) ?_ ?_
    · refine hker.subset ?_
      rintro R ⟨P, hP, rfl⟩
      rw [Set.mem_setOf_eq] at hP hP₀ ⊢
      change β.toAddMonoidHom (P.toAffinePoint - P₀.toAffinePoint) = 0
      exact (map_sub β.toAddMonoidHom P.toAffinePoint P₀.toAffinePoint).trans
        (sub_eq_zero_of_eq (hP.trans hP₀.symm))
    · intro P _ P' _ hPP'
      exact smoothPoint_toAffinePoint_injective W₁ (sub_left_injective (G := W₁.Point) hPP')

/-! ### The headline -/

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **T-B1 — `#ker β = deg β` for a general separable two-curve isogeny**: over an algebraically
closed field, a separable `β : Isogeny W₁ W₂` carrying only the cofinite two-curve
pullback-evaluation coherence `hw` (no global `CoordHom`) has `Nat.card β.kernel = β.degree`. -/
theorem card_kernel_eq_degree_twoCurve [IsAlgClosed F]
    [IsIntegrallyClosed W₂.toAffine.CoordinateRing]
    (β : Isogeny W₁ W₂) (hsep : β.IsSeparable)
    {bad : Set (W_smooth W₁).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad) :
    Nat.card β.kernel = β.degree := by
  classical
  haveI hIC : IsIntegrallyClosed (W_smooth W₂).CoordinateRing :=
    ‹IsIntegrallyClosed W₂.toAffine.CoordinateRing›
  -- ===== the `≤` direction: kernel ↪ Aut(K(E₁)/β^*K(E₂)), #Aut ≤ deg =====
  have hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z :=
    hcov_of_pullbackEvaluation_twoCurve β hbad hw
  have hker_fin : Finite β.kernel := Isogeny.finite_kernel_of_hcov_twoCurve β hcov
  letI βAlg : Algebra W₂.FunctionField W₁.FunctionField := β.toAlgebra
  haveI hfd : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra.toModule :=
    Isogeny.finiteDimensional_toAlgebra_twoCurve β
  haveI hAutFin : Finite (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      β.toAlgebra β.toAlgebra) := Finite.of_fintype _
  have hle1 : Nat.card β.kernel ≤
      Nat.card (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
        β.toAlgebra β.toAlgebra) :=
    Nat.card_le_card_of_injective _ (kernelTranslateForwardAut_twoCurve_injective β hcov)
  have hle2 : Nat.card (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      β.toAlgebra β.toAlgebra) ≤ β.degree := by
    have h := @AlgEquiv.card_le W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra hfd
    rwa [← Nat.card_eq_fintype_card] at h
  have hle : Nat.card β.kernel ≤ β.degree := le_trans hle1 hle2
  -- ===== the `≥` direction: the localized fibre dictionary =====
  haveI hsepAlg : @Algebra.IsSeparable (W_smooth W₂).FunctionField (W_smooth W₁).FunctionField
      _ _ β.toAlgebra := hsep
  haveI twFKL : @IsScalarTower F W₂.FunctionField W₁.FunctionField _ β.toAlgebra.toSMul _ :=
    @IsScalarTower.of_algebraMap_eq F W₂.FunctionField W₁.FunctionField _ _ _ _ β.toAlgebra _
      fun c => (β.pullback.commutes c).symm
  -- the denominator of the minimal polynomials of `x₁, y₁` over `β^*K(E₂)`
  obtain ⟨f₀, hf₀, hdx, hdy⟩ := @Curves.LocalizedDictionary.exists_denominator F _
    (W_smooth W₂) (W_smooth W₁) β.toAlgebra
  -- the good affine localization
  set Af := Localization.Away f₀ with hAf_def
  letI algAfK : Algebra Af (W_smooth W₂).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra (W_smooth W₂) f₀ hf₀
  haveI twAfK : letI := algAfK
      IsScalarTower (W_smooth W₂).CoordinateRing Af (W_smooth W₂).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra_isScalarTower (W_smooth W₂) f₀ hf₀
  letI algAfL : Algebra Af W₁.FunctionField :=
    ((β.pullback.toRingHom).comp (algebraMap Af (W_smooth W₂).FunctionField)).toAlgebra
  haveI twAfKL : @IsScalarTower Af W₂.FunctionField W₁.FunctionField algAfK.toSMul
      β.toAlgebra.toSMul algAfL.toSMul :=
    @IsScalarTower.of_algebraMap_eq Af W₂.FunctionField W₁.FunctionField _ _ _ algAfK β.toAlgebra
      algAfL fun _ => rfl
  -- the finite set of target points to avoid: possible images of the coherence bad set
  set badT : Set (W_smooth W₂).SmoothPoint := {Q' | ∃ p ∈ bad,
    WeilPairing.EvaluatesTo W₁ p (β.pullback (x_gen W₂)) Q'.x ∧
    WeilPairing.EvaluatesTo W₁ p (β.pullback (y_gen W₂)) Q'.y} with hbadT_def
  have hbadTfin : badT.Finite := by
    have hsub : badT ⊆ ⋃ p ∈ bad, {Q' : (W_smooth W₂).SmoothPoint |
        WeilPairing.EvaluatesTo W₁ p (β.pullback (x_gen W₂)) Q'.x ∧
        WeilPairing.EvaluatesTo W₁ p (β.pullback (y_gen W₂)) Q'.y} := by
      rintro Q' ⟨p, hp, h1, h2⟩
      exact Set.mem_biUnion hp ⟨h1, h2⟩
    refine Set.Finite.subset (Set.Finite.biUnion hbad fun p _ => ?_) hsub
    refine Set.Subsingleton.finite ?_
    rintro Q₁ ⟨hx₁, hy₁⟩ Q₂ ⟨hx₂, hy₂⟩
    exact Curves.SmoothPlaneCurve.SmoothPoint.ext (hx₁.unique hx₂) (hy₁.unique hy₂)
  -- the localized good fibre
  obtain ⟨Q, hQbadT, S, hScard, hSpts⟩ :=
    @Curves.LocalizedDictionary.exists_good_fiber_points F _ (W_smooth W₂) f₀ Af _ _ _
      (W_smooth W₁) β.toAlgebra hfd algAfK twAfK algAfL twAfKL twFKL ‹_› ‹_› hsepAlg
      _ hIC hf₀ hdx hdy badT hbadTfin
  -- each produced point is in the *stored* fibre over `Q`
  have hfibmem : ∀ pt ∈ S, β.toAddMonoidHom pt.toAffinePoint = Q.toAffinePoint := by
    intro pt hpt
    obtain ⟨hvx, hvy⟩ := hSpts pt hpt
    have hex : WeilPairing.EvaluatesTo W₁ pt (β.pullback (x_gen W₂)) Q.x := hvx
    have hey : WeilPairing.EvaluatesTo W₁ pt (β.pullback (y_gen W₂)) Q.y := hvy
    have hptgood : pt ∉ bad := fun hmem => hQbadT ⟨pt, hmem, hex, hey⟩
    obtain ⟨x', y', h', heq, hx, hy⟩ := hw pt hptgood
    have hxx : x' = Q.x := hx.unique hex
    have hyy : y' = Q.y := hy.unique hey
    rw [heq, Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]
    exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxx, hyy⟩
  -- the fibre has at least `deg β` elements
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hScard]
    exact Isogeny.degree_pos_twoCurve β
  obtain ⟨pt₀, hpt₀⟩ := hSne
  haveI hfib_fin : Finite {R : W₁.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} :=
    Isogeny.fiber_finite_of_kernel_finite β hker_fin
  have hinj : Function.Injective (fun p : {x // x ∈ S} =>
      (⟨p.1.toAffinePoint, hfibmem p.1 p.2⟩ :
        {R : W₁.Point // β.toAddMonoidHom R = Q.toAffinePoint})) := by
    intro p₁ p₂ h
    exact Subtype.ext (smoothPoint_toAffinePoint_injective W₁ (congrArg Subtype.val h))
  have hge : β.degree ≤ Nat.card {R : W₁.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} := by
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe, hScard] at h1
  -- close: fibres are kernel cosets
  have hkereq : Nat.card {R : W₁.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} = Nat.card β.kernel :=
    Isogeny.fiber_card_eq_kernel_card β (hfibmem pt₀ hpt₀)
  rw [hkereq] at hge
  exact le_antisymm hle hge

end HasseWeil
