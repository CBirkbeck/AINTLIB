/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.Fiber.AFConditional
import HasseWeil.Foundation.Curves.Valuation.NormValuation
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# No-finite-poles bridge: from `ord_P ≥ 0` everywhere to CR-image

This file ships `NoFinitePolesBridge W` for elliptic curves over an
algebraically closed field with integrally-closed coordinate ring.

The bridge composes:
1. `smoothPointEquivMaxIdeal` (worker-I) — bijection
   `SmoothPoint ↔ MaxSpec(F[C])`.
2. Maximal ideals of a 1-dim Dedekind domain are exactly height-one
   primes (mathlib).
3. `pointValuation P` = `HeightOneSpectrum.valuation v` for matching
   `v.asIdeal = maximalIdealAt P` (the technical bridge — both come from
   the same local DVR).
4. `mem_coordinateRing_of_valuation_le_one` (project) — concludes
   `f ∈ CR-image` from "valuation ≤ 1 at every height-one prime".

## Outstanding sub-pieces

The valuation identification (3) is the technical core. Mathlib's
`HeightOneSpectrum.valuation` and the project's `pointValuation` both
come from the same DVR (Localization.AtPrime), so they are equal as
valuations on `K(C)`. Proving the equality in Lean requires unfolding
through the `extendToLocalization` framework + matching with the project's
`IsDiscreteValuationRing.maximalIdeal`-based definition.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.1.2
-/

open WeierstrassCurve IsDedekindDomain

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]

/-- The `SmoothPoint → HeightOneSpectrum` coercion: send `P` to the
height-one prime `maximalIdealAt P`. Requires `[IsDedekindDomain CR]`
(via `[IsIntegrallyClosed CR]`). -/
noncomputable def smoothPointToHeightOne
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    HeightOneSpectrum (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing where
  asIdeal := (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P
  isPrime := ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal P).isPrime
  ne_bot := (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt_ne_bot P

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
@[simp] theorem smoothPointToHeightOne_asIdeal
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (smoothPointToHeightOne W P).asIdeal =
      (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P := rfl

/-! ### Surjection: every height-one prime is `maximalIdealAt P` for some `P` -/

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
/-- Under `[IsAlgClosed F]` and `[IsElliptic]` plus the Dedekind structure,
the `smoothPointToHeightOne` map is surjective: every height-one prime
of `F[C]` is of the form `maximalIdealAt P` for some smooth point `P`.

Combines worker-I's `maximalIdealAt_range` (range = MaxSpec) with the
fact that height-one primes in a 1-dim Dedekind domain are exactly the
nonzero maximal ideals. -/
theorem smoothPointToHeightOne_surjective
    [IsAlgClosed F] [(⟨W⟩ : SmoothPlaneCurve F).toAffine.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (v : HeightOneSpectrum (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) :
    ∃ P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint,
      smoothPointToHeightOne W P = v := by
  -- v.asIdeal is a height-one prime, hence maximal in 1-dim Dedekind.
  have h_max : v.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime v.ne_bot v.isPrime
  -- Use maximalIdealAt_range: every maximal ideal is some maximalIdealAt P.
  have h_in_range : v.asIdeal ∈
      Set.range (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt_range]
    exact h_max
  obtain ⟨P, hP⟩ := h_in_range
  refine ⟨P, ?_⟩
  -- HeightOneSpectrum equality is by Subtype-style: same asIdeal
  apply HeightOneSpectrum.ext
  exact hP

/-! ### Outstanding: the valuation identification

The remaining piece for full `NoFinitePolesBridge`:

```
theorem pointValuation_eq_heightOneValuation
    [IsDedekindDomain CR] (P : SmoothPoint) (f : FunctionField) :
    pointValuation P f = (smoothPointToHeightOne W P).valuation _ f
```

Both valuations come from the same DVR (Localization.AtPrime
(maximalIdealAt P)). The mathlib `HeightOneSpectrum.valuation` is
defined via `intValuation.extendToLocalization`; the project's
`pointValuation` is via `IsDiscreteValuationRing.maximalIdeal.valuation`.

Proving them equal requires unfolding through:
- `IsLocalization.valuation_uniqueness` (or analog)
- `IsDiscreteValuationRing.maximalIdeal_eq` for the localization
- Compatibility of the two extension paths to the function field

Estimated 80-150 LOC of mathlib API navigation. Once shipped, the
bridge composes mechanically:

```
NoFinitePolesBridge of_valuation_id : ∀ f ≠ 0,
    (∀ P, ord_P f ≥ 0) → ∃ u : CR, algMap u = f := fun f hf hord ↦
  mem_coordinateRing_of_valuation_le_one f fun v ↦ by
    obtain ⟨P, hP⟩ := smoothPointToHeightOne_surjective W v
    rw [← hP, ← pointValuation_eq_heightOneValuation]
    exact (project's pointValuation_le_one_iff_ord_nonneg).mpr (hord P)
```
-/

/-! ### Conditional bridge: takes the valuation identification as hypothesis -/

/-- The valuation identification: project's `pointValuation P` agrees
with mathlib's `HeightOneSpectrum.valuation` for the corresponding
height-one prime `smoothPointToHeightOne W P`.

Mathematically true because both are derived from the same local DVR
`Localization.AtPrime (maximalIdealAt P)`. Proof requires careful
mathlib-API navigation through `extendToLocalization` and the project's
DVR construction. -/
def PointValuationEqHeightOneValuation
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] : Prop :=
  ∀ (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField),
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P f =
      (smoothPointToHeightOne W P).valuation
        (⟨W⟩ : SmoothPlaneCurve F).FunctionField f

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
/-- Bridge from `ord_P f ≥ 0` everywhere to `pointValuation P f ≤ 1`
everywhere. Uses the relationship between `ord_P` and `pointValuation`
defined in the project. -/
theorem pointValuation_le_one_of_ord_nonneg
    {f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField} (_hf : f ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (h_ord : 0 ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P f) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P f ≤ 1 := by
  -- Unfold ord_P: it's defined via -toAdd of the multiplicative valuation.
  -- ord_P f ≥ 0 ↔ pointValuation P f ≤ 1 (when f ≠ 0).
  simp only [SmoothPlaneCurve.ord_P] at h_ord
  by_cases h_zero : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P f = 0
  · rw [h_zero]; exact zero_le_one' _
  · rw [dif_neg h_zero] at h_ord
    -- h_ord : 0 ≤ -↑((WithZero.unzero h_zero).toAdd : ℤ)
    have h_nonpos : ((WithZero.unzero h_zero).toAdd : ℤ) ≤ 0 := by
      have : (-((WithZero.unzero h_zero).toAdd : ℤ) : WithTop ℤ) ∈
        Set.range ((↑) : ℤ → WithTop ℤ) := ⟨_, rfl⟩
      have h_le : (0 : WithTop ℤ) ≤ ((-((WithZero.unzero h_zero).toAdd : ℤ) : ℤ) :
          WithTop ℤ) := h_ord
      exact_mod_cast (by
        have := WithTop.coe_le_coe.mp h_le
        omega : (WithZero.unzero h_zero).toAdd ≤ 0)
    -- Goal: pointValuation P f ≤ 1, i.e., its WithZero value is ≤ ofAdd 0.
    -- We have toAdd ≤ 0, so ofAdd toAdd ≤ ofAdd 0 = 1.
    rw [← WithZero.coe_unzero h_zero]
    exact WithZero.coe_le_coe.mpr (by
      change (WithZero.unzero h_zero).toAdd ≤ (1 : Multiplicative ℤ).toAdd
      simpa using h_nonpos)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
/-- **Conditional NoFinitePolesBridge** — given the valuation
identification (the technical bridge whose proof is outstanding),
the no-finite-poles bridge follows immediately by composing:
1. surjection `smoothPointToHeightOne_surjective`
2. valuation identification `h_id`
3. mathlib's `mem_coordinateRing_of_valuation_le_one`. -/
theorem noFinitePolesBridge_of_valuationEq
    [IsAlgClosed F] [(⟨W⟩ : SmoothPlaneCurve F).toAffine.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (h_id : PointValuationEqHeightOneValuation W) :
    NoFinitePolesBridge W := by
  intro f hf h_ord
  apply (⟨W⟩ : SmoothPlaneCurve F).mem_coordinateRing_of_valuation_le_one f
  intro v
  obtain ⟨P, hP⟩ := smoothPointToHeightOne_surjective W v
  rw [← hP, ← h_id P]
  exact pointValuation_le_one_of_ord_nonneg W hf P (h_ord P)

/-! ### Unconditional valuation identification (using count_preservation_localization)

The shipped `pointValuation_algebraMap_eq_exp_count` and
`count_preservation_localization` give the per-element identification on
`algebraMap u` for `u ∈ F[C]`. Extending to all of `F(C)` via
`IsFractionRing.div_surjective` and `Valuation.map_div` discharges the
`PointValuationEqHeightOneValuation` predicate unconditionally. -/

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
/-- **Per-element valuation identification on `algMap u`**: for any
    `u ∈ F[C]`, both project's `pointValuation P` and mathlib's
    `(smoothPointToHeightOne W P).valuation F(C)` evaluate to the same
    value at `algMap u ∈ F(C)`. Both equal
    `exp(-count_M (Ideal.span {u}))` for nonzero `u`, and both are `0`
    when `u = 0`. -/
theorem pointValuation_eq_heightOneValuation_algebraMap
    [IsAlgClosed F] [(⟨W⟩ : SmoothPlaneCurve F).toAffine.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (u : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap _ (⟨W⟩ : SmoothPlaneCurve F).FunctionField u) =
      (smoothPointToHeightOne W P).valuation
        (⟨W⟩ : SmoothPlaneCurve F).FunctionField
        (algebraMap _ _ u) := by
  classical
  by_cases hu : u = 0
  · subst hu
    simp only [map_zero]
  · -- For nonzero u, both equal exp(-count_M (Ideal.span {u})).
    rw [(⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_eq_exp_count P hu,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hu,
      smoothPointToHeightOne_asIdeal]

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
/-- **Valuation identification (unconditional)**: project's `pointValuation P`
    agrees with mathlib's `(smoothPointToHeightOne W P).valuation F(C)`
    everywhere on `F(C)`. Discharges `PointValuationEqHeightOneValuation`.

    Proof: both LHS and RHS are valuations on `F(C)`. They agree on the
    image of `algebraMap` (the `pointValuation_eq_heightOneValuation_algebraMap`
    lemma). For general `f = algMap u / algMap v`, multiplicativity (via
    `Valuation.map_div`) reduces to the algMap case. -/
theorem pointValuation_eq_heightOneValuation
    [IsAlgClosed F] [(⟨W⟩ : SmoothPlaneCurve F).toAffine.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    PointValuationEqHeightOneValuation W := by
  intro P f
  classical
  by_cases hf : f = 0
  · subst hf
    simp only [map_zero]
  -- f ≠ 0: write f = algMap u / algMap v.
  obtain ⟨u, v, hv_mem, h_eq⟩ :=
    IsFractionRing.div_surjective (A := (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) f
  rw [← h_eq, Valuation.map_div, Valuation.map_div,
    pointValuation_eq_heightOneValuation_algebraMap W P u,
    pointValuation_eq_heightOneValuation_algebraMap W P v]

omit [DecidableEq F] [WeierstrassCurve.IsElliptic W] in
/-- **NoFinitePolesBridge unconditional** (composes
    `pointValuation_eq_heightOneValuation` with `noFinitePolesBridge_of_valuationEq`). -/
theorem noFinitePolesBridge_unconditional
    [IsAlgClosed F] [(⟨W⟩ : SmoothPlaneCurve F).toAffine.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    NoFinitePolesBridge W :=
  noFinitePolesBridge_of_valuationEq W (pointValuation_eq_heightOneValuation W)

omit [WeierstrassCurve.IsElliptic W] in
/-- **PointMinusOPrincipalEqZero unconditional** (composes
    `noFinitePolesBridge_unconditional` with `pointMinusO_of_bridge`).
    If `(P) − (O)` is principal on a smooth-plane elliptic curve over an
    algebraically closed field with integrally-closed coordinate ring,
    then `P = 0`. This is the second of the two AF witnesses needed for
    the §5/Pic⁰ chain (the first being DivZeroReduce, gated on Miller). -/
theorem pointMinusOPrincipalEqZero_unconditional
    [IsAlgClosed F] [(⟨W⟩ : SmoothPlaneCurve F).toAffine.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    PointMinusOPrincipalEqZero W :=
  pointMinusO_of_bridge W (noFinitePolesBridge_unconditional W)

/-- **AddHomProperty wrapper with reduced witnesses**: given
    `MillerHypothesis` and `DivZeroReduce` for both curves, plus the
    pushforward-preserves-principal hypothesis, the universal hom property
    follows. The remaining unconditional pieces — `noFinitePolesBridge`
    (just shipped) and `principal_mem_degZero` (II.3.1(b) consequence) —
    are filled in automatically.

    The remaining gates are now:
    - `MillerHypothesis` for both W₁ and W₂ (geometric chord/tangent — the
      BIG mathematical piece);
    - `DivZeroReduce` for both W₁ and W₂ (combinatorial reduction via
      list-induction from Miller);
    - `h_pres` (T-PIC-C-003 = norm-divisor identity for pushforward).

    All three are independent geometric/combinatorial pieces; the algebraic
    plumbing is fully discharged. -/
theorem AddHomProperty_of_miller_divZeroReduce
    {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : HasseWeil.EC.Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (h_miller₁ : MillerHypothesis W₁) (h_miller₂ : MillerHypothesis W₂)
    (h_dzr₁ : DivZeroReduce W₁) (h_dzr₂ : DivZeroReduce W₂)
    (h_pres : ∀ D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor φ cd D ∈
        (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    φ.AddHomProperty cd :=
  AddHomProperty_of_AFInputs φ cd
    ⟨h_miller₁, h_dzr₁, noFinitePolesBridge_unconditional W₁⟩
    ⟨h_miller₂, h_dzr₂, noFinitePolesBridge_unconditional W₂⟩
    (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W₁⟩) hD)
    (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W₂⟩) hD)
    h_pres

/-! ### T-III-3-004 (Pic⁰(E) ≅ E) witness-parametric on Miller + DivZeroReduce

The full Silverman III.3.4 isomorphism `Pic⁰(E) ≃+ E` is constructed
witness-parametric on `MillerHypothesis W` and `DivZeroReduce W` (bundled
into `AFInputs W`). When Worker D's Miller + DivZeroReduce land
unconditional, this iso discharges to unconditional.

Naming: `picZeroIsoE_of_AFInputs` — the "_of_AFInputs" suffix marks the
witness-parametric layer per Conditional namespacing convention. -/

/-- **T-III-3-004 (Pic⁰(E) ≅ E) witness-parametric on AFInputs**: under
    `[IsAlgClosed F]` + `[IsElliptic]` + `[IsIntegrallyClosed C.CoordinateRing]`,
    given `AFInputs W` (= MillerHypothesis + DivZeroReduce + NoFinitePolesBridge,
    where the last is now `noFinitePolesBridge_unconditional`), the project's
    `PicProj₀` is naturally `AddEquiv`-isomorphic to `W.Point` (the elliptic
    curve's group of `F`-rational points).

    Components:
    - `toFun = σ̄ = picZeroSumOfWitness W (a.h_van principal_mem_degZero)`
    - `invFun = κ = picZeroOfPoint W`
    - `left_inv : κ (σ̄ D) = D` — uses DivZeroReduce via `h_inj_of_divZeroReduce`.
    - `right_inv : σ̄ (κ P) = P` — divisor-level via `picZeroSumOfWitness_picZeroOfPoint`.
    - `map_add'` — automatic since `picZeroSumOfWitness` is a `→+`.

    Naming: `picZeroIsoE_of_AFInputs` (suffix marks witness-parametric layer). -/
noncomputable def picZeroIsoE_of_AFInputs
    {W : Affine F} [W.IsElliptic]
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (a : AFInputs W) :
    SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) ≃+ W.Point :=
  let h_van : ∀ D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W D = 0 :=
    a.h_van (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W⟩) hD)
  let sigmaBar : SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) →+ W.Point :=
    HasseWeil.EC.Isogeny.picZeroSumOfWitness W h_van
  { toFun := sigmaBar
    invFun := picZeroOfPoint W
    left_inv := fun D ↦
      h_inj_of_divZeroReduce W a.divZeroReduce h_van D
    right_inv := fun P ↦
      HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint W h_van P
    map_add' := sigmaBar.map_add }

/-- `(W.baseChange L).IsElliptic` from `[W.IsElliptic]`.  In mathlib v4.31 the
`WeierstrassCurve.baseChange` def no longer auto-propagates the `IsElliptic` instance through to
the base-changed curve; mathlib only ships `(W.map f).IsElliptic`.  Since
`WeierstrassCurve.baseChange W L = W.map (algebraMap F L)` definitionally, we transfer it. -/
instance baseChange_isElliptic {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
    (W : Affine F) [W.IsElliptic] : (W.baseChange L).IsElliptic :=
  inferInstanceAs (W.map (algebraMap F L)).IsElliptic

/-! ### Alg-closure-descend strategy: T-III-3-004 over `AlgebraicClosure F`

Per reviewer round-4 reframe (2026-05-13): build the §5 cascade
(T-III-6-002 → §5.4 keystone → III.6.3) over `L = AlgebraicClosure F`
where `[IsAlgClosed L]` is valid by mathlib's instance, then descend
the integer degree inequality `qf_nonneg` to `F = F_q`.

The shipped `picZeroIsoE_of_AFInputs` applies directly with
`L = AlgebraicClosure F`; the wrapper below is the explicit instantiation.
The downstream cascade (T-III-6-002, §5.4) is still witness-parametric
on `AFInputs (W.baseChange L)` (= Miller over L), to be discharged when
Worker D's Miller lands. -/

/-- **T-III-3-004 over the algebraic closure**: `picZeroIsoE_of_AFInputs`
    instantiated at `L = AlgebraicClosure F`. Provides
    `Pic⁰_proj((W.baseChange L)) ≃+ (W.baseChange L).Point` witness-parametric
    on `AFInputs (W.baseChange L)`. -/
noncomputable def picZeroIsoE_baseChange_of_AFInputs
    {F : Type*} [Field F]
    {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)]
    (W : Affine F) [W.IsElliptic]
    [IsDedekindDomain (⟨W.baseChange L⟩ : SmoothPlaneCurve L).CoordinateRing]
    (a : AFInputs (W.baseChange L)) :
    SmoothPlaneCurve.PicProj₀ (⟨W.baseChange L⟩ : SmoothPlaneCurve L) ≃+
      WeierstrassCurve.Affine.Point (W.baseChange L) :=
  picZeroIsoE_of_AFInputs (W := W.baseChange L) a

end HasseWeil.Curves
