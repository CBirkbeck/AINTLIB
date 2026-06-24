/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.TwoCurveGroupHom
import HasseWeil.Curves.LocalizedDictionary
import HasseWeil.Curves.PushforwardDivisor
import HasseWeil.Curves.NormConormIntegralClosure

/-!
# The CoordHom-free norm–conorm: `PlaceRestrictionPreservesPrincipal` (Silverman II.3.6)

This file discharges the single remaining wall of char-0 isogeny symmetry,
`PlaceRestrictionPreservesPrincipal φ` (`TwoCurveGroupHom.lean`): for a separable two-curve
isogeny `φ : Isogeny W₁ W₂` over `[IsAlgClosed F]`, the CoordHom-free place-restriction
pushforward carries principal projective divisors to principal projective divisors — Silverman
II.3.6/II.3.7 (norm–conorm), *without* an affine coordinate-ring comorphism `F[E₂] → F[E₁]`
(which a genuine isogeny lacks, since `φ^*(x_gen₂)` has poles on the affine kernel).

## The integral-closure route (Silverman's actual II.3.6)

The CoordHom-gated `EC.Isogeny.pushforward_preserves_principal` (`PushforwardDivisor.lean`) routes
through `Ideal.relNorm C₂.CoordinateRing (C₁.maximalIdealAt R)`, i.e. the affine coordinate-ring
extension `F[E₂] → F[E₁]` — unavailable here.  Instead we use the **field norm** `N_φ f =
Algebra.norm_{K(E₁)/φ*K(E₂)} f ∈ K(E₂)` and the per-place identity (Silverman II.3.6, every
ramification `e = 1` by III.4.10c over `[IsAlgClosed F]`)

  `ord_Q(N_φ f) = Σ_{P : φ(P) = Q} ord_P(f)`,

which says exactly `div(N_φ f) = placeRestrictionPushforward φ (div f)`.  Since `N_φ f ∈ K(E₂)`,
the pushforward of a principal divisor is principal.

The fibre structure (places of `E₁` over a place of `E₂`) is supplied CoordHom-free by the
integral closure `B := integralClosure (localized φ*F[E₂]) K(E₁)` of `HasseWeil/Curves/
LocalizedDictionary.lean`, whose maximal ideals ↔ ALL places of `E₁` (including the affine-kernel
poles of `φ^*x_gen₂`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6, II.3.6, II.3.7, III.4.10(c).
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]
variable [IsAlgClosed F]

/-! ### The field-norm conorm `N_φ f ∈ K(E₂)`

The conorm of a function `f ∈ K(E₁)` is the field norm `N_φ f = Algebra.norm_{K(E₁)/φ*K(E₂)} f`,
landing in `K(E₂)` (mathlib's `Algebra.norm` already lands in the base, as for `CurveMap.pushforward`).
This is the principal-divisor witness: `div(N_φ f) = placeRestrictionPushforward φ (div f)`. -/

/-- **The conorm** `N_φ : K(E₁) →* K(E₂)`, the field norm of the pullback algebra structure. -/
noncomputable def conorm (φ : HasseWeil.Isogeny W₁ W₂) :
    W₁.toAffine.FunctionField →* W₂.toAffine.FunctionField :=
  @Algebra.norm W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _ φ.toAlgebra

omit [IsAlgClosed F] in
@[simp] theorem conorm_mul (φ : HasseWeil.Isogeny W₁ W₂) (f g : W₁.toAffine.FunctionField) :
    conorm φ (f * g) = conorm φ f * conorm φ g :=
  (conorm φ).map_mul f g

omit [IsAlgClosed F] in
@[simp] theorem conorm_one (φ : HasseWeil.Isogeny W₁ W₂) :
    conorm φ (1 : W₁.toAffine.FunctionField) = 1 :=
  (conorm φ).map_one

omit [IsAlgClosed F] in
/-- The conorm of a nonzero function is nonzero (a monoid hom sends a unit to a unit). -/
theorem conorm_ne_zero (φ : HasseWeil.Isogeny W₁ W₂) {f : W₁.toAffine.FunctionField}
    (hf : f ≠ 0) : conorm φ f ≠ 0 :=
  (IsUnit.map (conorm φ) (isUnit_iff_ne_zero.mpr hf)).ne_zero

/-! ### Finite-dimensionality of `K(E₁)/φ*K(E₂)` (two-curve, unconditional)

For *any* two-curve isogeny `φ : Isogeny W₁ W₂`, `K(E₁)` is finite-dimensional over `φ*K(E₂)` — the
two-curve analogue of `HasseWeil.isogeny_finiteDimensional`.  Proof: `K(E₁)/φ*K(E₂)` is essentially
of finite type (`K(E₁)` is so over `F`, and `φ*K(E₂) ⊇ F`) and algebraic (both function fields have
transcendence degree `1` over `F`, so `trdeg_{φ*K(E₂)} K(E₁) = 0`), hence finite by
`Algebra.finite_of_essFiniteType_of_isAlgebraic`.  This discharges the `hfin` hypothesis of the
norm–conorm leaf automatically; only `hsep` (genuine separability) remains carried. -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
omit [IsAlgClosed F] in
/-- **Two-curve isogeny finite-dimensionality (unconditional)**: `K(E₁)` is finite-dimensional over
`K(E₂)` via `φ.pullback`, for any two-curve isogeny `φ`. -/
theorem isogeny_finiteDimensional_twoCurve (φ : HasseWeil.Isogeny W₁ W₂) :
    @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule := by
  letI : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField := φ.toAlgebra
  haveI tower : IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.pullback.commutes c).symm
  haveI hfaith : FaithfulSMul W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    (faithfulSMul_iff_algebraMap_injective W₂.toAffine.FunctionField
      W₁.toAffine.FunctionField).mpr φ.pullback_injective
  haveI hfaithF2 : FaithfulSMul F W₂.toAffine.FunctionField :=
    (faithfulSMul_iff_algebraMap_injective F W₂.toAffine.FunctionField).mpr
      (algebraMap F W₂.toAffine.FunctionField).injective
  -- essentially of finite type: `F → K(E₂) → K(E₁)` with `K(E₁)/F` ess. finite type.
  haveI hessF1 : Algebra.EssFiniteType F W₁.toAffine.FunctionField :=
    HasseWeil.functionField_essFiniteType_F W₁
  haveI hess : Algebra.EssFiniteType W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    Algebra.EssFiniteType.of_comp F W₂.toAffine.FunctionField W₁.toAffine.FunctionField
  -- algebraic: trdeg additivity `F → K(E₂) → K(E₁)`, both legs trdeg 1.
  haveI halg : Algebra.IsAlgebraic W₂.toAffine.FunctionField W₁.toAffine.FunctionField := by
    rw [← trdeg_eq_zero_iff]
    have h_add : Algebra.trdeg F W₂.toAffine.FunctionField +
        Algebra.trdeg W₂.toAffine.FunctionField W₁.toAffine.FunctionField =
        Algebra.trdeg F W₁.toAffine.FunctionField :=
      trdeg_add_eq F W₂.toAffine.FunctionField
    rw [HasseWeil.weierstrass_functionField_trdeg_eq_one W₂,
      HasseWeil.weierstrass_functionField_trdeg_eq_one W₁] at h_add
    refine Cardinal.add_one_inj.mp ?_
    rw [zero_add, add_comm]; exact h_add
  exact @Algebra.finite_of_essFiniteType_of_isAlgebraic W₂.toAffine.FunctionField _
    W₁.toAffine.FunctionField _ _ hess halg

/-! ### The `f = u/v` reduction (structural)

The norm–conorm identity `div(N_φ f) = φ_∗(div f)` is proven for all `f` from the `algebraMap`
case by the standard `f = u/v` (`u, v ∈ F[E₁]`) reduction: both sides are additive
(`placeRestrictionPushforward` is an `AddMonoidHom`; `projectiveDivisorOf`/`conorm` are
multiplicative), so `div(N_φ (u/v)) = div(N_φ u) − div(N_φ v)` and `φ_∗(div(u/v)) =
φ_∗(div u) − φ_∗(div v)`, matched termwise by the `algebraMap` case.  This mirrors the tail of
`CurveMap.projectiveDivisorOf_pushforward_eq_pushforwardDivisorVal`. -/

/-- **The `f = u/v` reduction** (CoordHom-free): the norm–conorm identity for all `f` follows from
its `algebraMap` case `key`, given that `K(E₁)/φ*K(E₂)` is finite (for the `f = 0` branch via
`Algebra.norm_zero`). -/
theorem placeRestrictionPushforward_projectiveDivisorOf_of_algebraMap
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (key : ∀ w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing, w ≠ 0 →
      placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) =
        (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ
          (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
            (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)))
    (f : W₁.toAffine.FunctionField) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) := by
  classical
  letI : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField := φ.toAlgebra
  haveI := hfin
  by_cases hf : f = 0
  · subst hf
    haveI : Module.Free W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
      Module.Free.of_divisionRing _ _
    rw [(⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_zero, map_zero,
      show conorm φ (0 : W₁.toAffine.FunctionField) = 0 from Algebra.norm_zero,
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_zero]
  · obtain ⟨u, v, hv_mem, hf_eq⟩ :=
      IsFractionRing.div_surjective (A := (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing) f
    have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_mem
    set au := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField u with hau
    set av := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField v with hav
    have hav_ne : av ≠ 0 := by
      rw [hav]; intro h
      exact hv_ne ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
    have hu_ne : u ≠ 0 := by
      intro hu; apply hf; rw [← hf_eq, hau, hu, map_zero, zero_div]
    have hf_av : f * av = au := by rw [← hf_eq, div_mul_cancel₀ _ hav_ne]
    have hpf_ne : conorm φ f ≠ 0 := conorm_ne_zero φ hf
    have hpav_ne : conorm φ av ≠ 0 := conorm_ne_zero φ hav_ne
    -- LHS additivity over `f * av = au`.
    have hLHS_split : placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) +
        placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf av) =
        placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf au) := by
      rw [← map_add, ← (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hf hav_ne, hf_av]
    -- RHS additivity over `f * av = au`.
    have hRHS_split : (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) +
        (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ av) =
        (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ au) := by
      rw [← (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hpf_ne hpav_ne,
        ← conorm_mul, hf_av]
    have hau_eq := key u hu_ne
    have hav_eq := key v hv_ne
    have hgoalL : placeRestrictionPushforward φ
        ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) =
        placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf au) -
        placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf av) := by
      rw [← hLHS_split]; abel
    have hgoalR : (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) =
        (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ au) -
        (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ av) := by
      rw [← hRHS_split]; abel
    rw [hgoalL, hgoalR, hau_eq, hav_eq]

/-! ### The RHS fibre-sum reduction (structural, CoordHom-free)

The coefficient of `placeRestrictionPushforward φ D` at an affine place `Q` of `E₂` is the
`Finsupp.mapDomain` fibre sum: `Σ_{x ∈ D.support, placeRestrictionPlaceImage φ x = affine Q} D x`.
This is pure `Finsupp` combinatorics (no `φ`-geometry), valid for any divisor `D`.  It exposes the
RHS of the deep leaf as a fibre sum to be matched against the field-norm count. -/

/-- **The pushforward coefficient as a fibre sum** (structural): for any divisor `D` of `E₁` and any
affine place `Q` of `E₂`, the coefficient of `placeRestrictionPushforward φ D` at `affine Q` is the
sum of `D x` over the support points `x` whose place-restriction image is `affine Q`. -/
theorem placeRestrictionPushforward_apply_affine
    (φ : HasseWeil.Isogeny W₁ W₂) (D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F))
    (Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint) :
    placeRestrictionPushforward φ D (ProjectiveSmoothPoint.affine Q) =
      ∑ x ∈ D.support.filter
        (fun x => placeRestrictionPlaceImage φ x = ProjectiveSmoothPoint.affine Q), D x := by
  classical
  rw [placeRestrictionPushforward_apply, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.single_apply]

/-! ### The comap-center → point-valuation lemma (the place dictionary on `E₂`)

The crux of the fibre matching is to identify, from a `B`-prime `v` over `m_Q`, the *target*
place `Q` of `E₂`.  The valuation `v` restricts (via `φ.pullback`) to a valuation on `K(E₂)` whose
center on `F[E₂]` is exactly `m_Q`; such a valuation *is* `pointValuation Q` — the place dictionary
for the smooth curve `E₂`, in its general (non-`B`) form.  The proof is the same DVR-domination as
`NormConormIntegralClosure.bPrime_valuation_eq_pointValuation_of_coordGen_le_one`, transcribed to a
generic surjective `ℤᵐ⁰`-valued valuation with prescribed affine center. -/

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The valuation subring of a surjective `ℤᵐ⁰`-valued valuation is proper** (`≠ ⊤`).  A surjective
`w` is nontrivial — it hits `exp 1 ≠ 0, 1` — so by `Valuation.valuationSubring_eq_top_iff` its
valuation subring cannot be all of `K`.  (Local helper for `eq_pointValuation_of_center`; the
`NormConormIntegralClosure` analogue is private to its file.) -/
private theorem valuationSubring_ne_top_of_surjective_withZeroInt {K : Type*} [Field K]
    (w : Valuation K (WithZero (Multiplicative ℤ))) (hwsurj : Function.Surjective w) :
    w.valuationSubring ≠ ⊤ := by
  have hNontriv : w.IsNontrivial := by
    refine ⟨?_⟩
    obtain ⟨z, hz⟩ := hwsurj (WithZero.exp (1 : ℤ))
    refine ⟨z, ?_, ?_⟩
    · rw [hz]; exact WithZero.exp_ne_zero
    · rw [hz, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
        (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]; norm_num
  intro htop
  exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
omit [DecidableEq F] [IsAlgClosed F] in
/-- **`O_Q ⊆ O_w` for a valuation with affine center `m_Q`** (the DVR-domination containment, downward
half).  If `w ≤ 1` on the coordinate ring `F[C]` and has center exactly `m_Q`, then every
`pointValuation Q`-integer is a `w`-integer: write such an `f = a / s` with `a ∈ F[C]`,
`s ∉ m_Q`; then `w(s) = 1` (it is `≤ 1` by `hle` and not `< 1` since `s ∉ m_Q` via `hcenter`), so
`w(f) = w(a) / 1 = w(a) ≤ 1`.  (Local helper for `eq_pointValuation_of_center`.) -/
private theorem pointValuationSubring_le_valuationSubring_of_center
    (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing]
    (Q : C.SmoothPoint)
    (w : Valuation C.FunctionField (WithZero (Multiplicative ℤ)))
    (hle : ∀ b : C.CoordinateRing, w (algebraMap C.CoordinateRing C.FunctionField b) ≤ 1)
    (hcenter : ∀ b : C.CoordinateRing,
      w (algebraMap C.CoordinateRing C.FunctionField b) < 1 ↔ b ∈ C.maximalIdealAt Q) :
    (C.pointValuation Q).valuationSubring ≤ w.valuationSubring := by
  classical
  intro f hf
  obtain ⟨x, hx_eq⟩ := (SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one f).mpr
    ((Valuation.mem_valuationSubring_iff _ f).mp hf)
  obtain ⟨a, s, hxas⟩ := IsLocalization.exists_mk'_eq (C.maximalIdealAt Q).primeCompl x
  set sv : C.CoordinateRing := (s : C.CoordinateRing) with hsv
  have hs_notin : sv ∉ C.maximalIdealAt Q := Ideal.mem_primeCompl_iff.mp s.2
  have hs_ne : sv ≠ 0 := fun h => hs_notin (h ▸ Submodule.zero_mem _)
  have hs_map_ne : algebraMap C.CoordinateRing C.FunctionField sv ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C.CoordinateRing C.FunctionField)).mpr hs_ne
  have hf_eq : f = algebraMap C.CoordinateRing C.FunctionField a /
      algebraMap C.CoordinateRing C.FunctionField sv := by
    rw [eq_div_iff hs_map_ne, ← hx_eq, ← hxas,
      IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt Q) C.FunctionField sv,
      IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt Q) C.FunctionField a,
      ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec (C.localRingAt Q) a s
  have hws : w (algebraMap C.CoordinateRing C.FunctionField sv) = 1 := by
    refine le_antisymm (hle sv) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hs_notin ((hcenter sv).mp hlt)
  refine (Valuation.mem_valuationSubring_iff _ f).mpr ?_
  rw [hf_eq, map_div₀ w, hws, div_one]
  exact hle a

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
omit [DecidableEq F] [IsAlgClosed F] in
/-- **A surjective valuation on `K(C)` with affine center `m_Q` is `pointValuation Q`** (the place
dictionary for a smooth curve, general form).  If `w : K(C) → ℤᵐ⁰` is surjective, is `≤ 1` on the
coordinate ring `F[C]`, and has center exactly `m_Q` (i.e. `w(algebraMap b) < 1 ↔ b ∈ m_Q`), then
`w = pointValuation Q`.  This is the DVR-domination argument of
`bPrime_valuation_eq_pointValuation_of_coordGen_le_one` for a generic valuation: the local ring
`O_Q = F[C]_{m_Q}` dominates downward into `O_w`, so the two rank-one DVR valuation subrings agree,
hence the two surjective `ℤᵐ⁰`-valuations are equal. -/
theorem eq_pointValuation_of_center
    (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing]
    (Q : C.SmoothPoint)
    (w : Valuation C.FunctionField (WithZero (Multiplicative ℤ)))
    (hwsurj : Function.Surjective w)
    (hle : ∀ b : C.CoordinateRing, w (algebraMap C.CoordinateRing C.FunctionField b) ≤ 1)
    (hcenter : ∀ b : C.CoordinateRing,
      w (algebraMap C.CoordinateRing C.FunctionField b) < 1 ↔ b ∈ C.maximalIdealAt Q) :
    w = C.pointValuation Q := by
  classical
  -- `O_w` is a rank-one DVR (`w` surjective onto `ℤᵐ⁰`).
  haveI : IsDiscreteValuationRing w.valuationSubring :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ hwsurj
  -- `O_Q := O_{pointValuation Q}` is a rank-one DVR.
  have hpvsurj : Function.Surjective (C.pointValuation Q) :=
    (IsDiscreteValuationRing.maximalIdeal (C.localRingAt Q)).valuation_surjective C.FunctionField
  set A : ValuationSubring C.FunctionField := w.valuationSubring with hA
  set Bv : ValuationSubring C.FunctionField := (C.pointValuation Q).valuationSubring with hBv
  haveI : IsDiscreteValuationRing Bv :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ hpvsurj
  -- `Bv ⊆ A`: every `pointValuation Q`-integer is a `w`-integer (write `f = a / s`, `s ∉ m_Q`).
  have hBA : Bv ≤ A := pointValuationSubring_le_valuationSubring_of_center C Q w hle hcenter
  -- `A ≠ ⊤`: `w` is nontrivial (surjective onto `ℤᵐ⁰`).
  have hAtop : A ≠ ⊤ := valuationSubring_ne_top_of_surjective_withZeroInt w hwsurj
  have hEq : Bv = A := rankOne_valuationSubring_le_eq_of_ne_top Bv A hBA hAtop
  have h_isEquiv : w.IsEquiv (C.pointValuation Q) := by
    rw [Valuation.isEquiv_iff_valuationSubring]; rw [hA, hBv] at hEq; exact hEq.symm
  exact Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj hpvsurj h_isEquiv

/-! ### The reverse place dictionary: a regular point gives a `B`-prime (surjectivity)

The fibre bijection also needs the *reverse* of `bPrime_valuation_eq_pointValuation`: a point `P`
at which both pulled-back generators are regular (`P ∉ poleLocus`, equivalently its place-restriction
image is an *affine* place of `E₂`) is cut out by *some* `B`-prime.  At such a `P` the whole image of
`F[E₂]` lands in the local ring `O_P` (the generators are regular there), so the integral closure `B`
lands in `O_P` (integrally closed); the contraction of `m_P` is then a height-one prime of `B` whose
adic valuation is `pointValuation P`. -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
omit [IsAlgClosed F] in
/-- **The pulled-back coordinate ring of `E₂` is `≤ 1` at a regular point `P`** (value bound, the
generator induction).  If `φ^*(x_gen₂)`, `φ^*(y_gen₂)` are `≤ 1` at `P`, then `φ^*(algebraMap c)` is
`≤ 1` at `P` for every `c ∈ F[E₂]` (it is a polynomial in the two generators with `F`-constant — i.e.
unit — coefficients).  This is the `E₁`-point analogue of
`valuation_algebraMap_coordinateRing_C₁_le_one`, transported through `φ^*`. -/
theorem pointValuation_le_one_pullback_coordinateRing
    (φ : HasseWeil.Isogeny W₁ W₂) (P : (W_smooth W₁).SmoothPoint)
    (hx : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (φ.pullback (x_gen W₂)) ≤ 1)
    (hy : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (φ.pullback (y_gen W₂)) ≤ 1)
    (c : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
      (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField c)) ≤ 1 := by
  classical
  set w := (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P with hw
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    exact le_trans (w.map_add _ _) (max_le hp hq)
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, w.map_mul]
    -- the `X`-power leg is `φ^*(y_gen₂)^n`
    have hXeq : φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial Polynomial.X)) =
        φ.pullback (y_gen W₂) := rfl
    refine mul_le_one' ?_ (by rw [hXeq]; exact pow_le_one₀ zero_le hy)
    induction a using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.C_add, map_add, map_add, map_add]
      exact le_trans (w.map_add _ _) (max_le hp hq)
    | monomial m d =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow]
      simp only [map_mul, map_pow, w.map_mul]
      -- the `C X`-power leg is `φ^*(x_gen₂)^m`
      have hXgen : φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial
            (Polynomial.C Polynomial.X))) = φ.pullback (x_gen W₂) := rfl
      refine mul_le_one' ?_ (by rw [hXgen]; exact pow_le_one₀ zero_le hx)
      -- the `F`-constant leg `φ^*(algMap_F d) = algMap_F d` is regular at `P` (constant).
      have hdconst : φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial
            (Polynomial.C (Polynomial.C d)))) =
          algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField
            (algebraMap F (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing d) := by
        rw [show (AdjoinRoot.mk W₂.toAffine.polynomial (Polynomial.C (Polynomial.C d)) :
              (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) =
            algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing d from rfl,
          ← IsScalarTower.algebraMap_apply F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
            W₂.toAffine.FunctionField d, φ.pullback.commutes d,
          ← IsScalarTower.algebraMap_apply F (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
            W₁.toAffine.FunctionField d]
      rw [hdconst]
      exact (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one _ P

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
omit [IsAlgClosed F] in
/-- **A regular point with a vanishing `B`-function is cut out by a `B`-prime** (reverse place
dictionary / surjectivity).  If both pulled-back generators are regular at `P` (`P ∉ poleLocus`) and
some nonzero `z ∈ B` vanishes at `P` (`pointValuation P (algebraMap_B z) < 1`), then there is a
height-one prime `v` of `B` with `v.valuation = pointValuation P`.

Proof: the integral closure `B` lands in the (integrally closed) local ring `O_P` because `F[E₂]`
does (`pointValuation_le_one_pullback_coordinateRing`), so `pointValuation P ≤ 1` on `B`.  The
center `q = {b ∈ B : pointValuation P (algebraMap_B b) < 1}` is then an ideal (regularity ⟹ absorbs
`B`), prime (`pointValuation P` multiplicative), nonzero (`z ∈ q`) and proper, hence a height-one
prime `v`.  Its adic-valuation subring satisfies `O_v ⊆ O_P` (an `O_v`-integer `x = n/d` with
`d ∉ q` has `pointValuation P (algebraMap_B d) = 1`, `exists_primeCompl_mul_eq_of_integer`), so by
rank-one DVR domination `O_v = O_P`, i.e. `v.valuation = pointValuation P`. -/
theorem exists_bPrime_eq_pointValuation_of_notMem_poleLocus
    (φ : HasseWeil.Isogeny W₁ W₂)
    [algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))]
    [IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    (halg : ∀ g : W₂.toAffine.FunctionField,
      algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField g = φ.pullback g)
    (P : (W_smooth W₁).SmoothPoint) (hP : P ∉ twoCurvePoleLocus φ)
    {z : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))} (hz_ne : z ≠ 0)
    (hzvanish : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
      (algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField z) < 1) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))),
      v.valuation W₁.toAffine.FunctionField =
        (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P := by
  classical
  let Bb := NormConormIntegralClosure.B
    (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))
  let pv := (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
  haveI : IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  haveI hmPprime : ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P).IsPrime :=
    ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal P).isPrime
  haveI hDVR : IsDiscreteValuationRing ((⟨W₁⟩ : SmoothPlaneCurve F).localRingAt P) :=
    (⟨W₁⟩ : SmoothPlaneCurve F).localRing_isDVR_of_smooth P
  have hxle : pv (φ.pullback (x_gen W₂)) ≤ 1 := by by_contra h; exact hP (Or.inl h)
  have hyle : pv (φ.pullback (y_gen W₂)) ≤ 1 := by by_contra h; exact hP (Or.inr h)
  -- the image of `F[E₂]` lands in the valuation integers `O_P = pv.integer`.
  have hImOP : ∀ c : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField c ∈
        pv.integer := by
    intro c
    rw [Valuation.mem_integer_iff]
    have hceq : algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField c =
        φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField c) := by
      rw [← halg, IsScalarTower.algebraMap_apply (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField W₁.toAffine.FunctionField c]
    rw [hceq]
    exact pointValuation_le_one_pullback_coordinateRing φ P hxle hyle c
  -- the algebra `F[E₂] → O_P = pv.integer` (image lands in the integers).
  letI algCR_int : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing pv.integer :=
    (((algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField)).codRestrict
      pv.integer.toSubsemiring hImOP).toAlgebra
  haveI twCR_int : IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing pv.integer
      W₁.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- (1) regularity: every `b ∈ B` has `pv (algebraMap_B b) ≤ 1`.
  have hregB : ∀ b : Bb, pv (algebraMap Bb W₁.toAffine.FunctionField b) ≤ 1 := by
    intro b
    -- `b` integral over `F[E₂]` (image ⊆ `O_P`) ⟹ `b` integral over `O_P` ⟹ `pv b ≤ 1`.
    have hbint : IsIntegral (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (algebraMap Bb W₁.toAffine.FunctionField b) := b.2
    have hbint_int : IsIntegral pv.integer (algebraMap Bb W₁.toAffine.FunctionField b) :=
      hbint.tower_top
    exact (Valuation.integer.integers pv).isIntegral_iff_v_le_one.mp hbint_int
  -- (2) the center `q = {b ∈ B : pv (algebraMap_B b) < 1}` as an ideal.
  set q : Ideal Bb :=
    { carrier := {b : Bb | pv (algebraMap Bb W₁.toAffine.FunctionField b) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add] at *
        exact lt_of_le_of_lt (pv.map_add _ _) (max_lt ha hb)
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, pv.map_zero]; exact zero_lt_one
      smul_mem' := by
        intro c b hb
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, pv.map_mul] at *
        calc pv (algebraMap Bb W₁.toAffine.FunctionField c) *
              pv (algebraMap Bb W₁.toAffine.FunctionField b)
            ≤ 1 * pv (algebraMap Bb W₁.toAffine.FunctionField b) := by gcongr; exact hregB c
          _ = pv (algebraMap Bb W₁.toAffine.FunctionField b) := one_mul _
          _ < 1 := hb } with hq_def
  have hq_mem_iff : ∀ b : Bb, b ∈ q ↔
      pv (algebraMap Bb W₁.toAffine.FunctionField b) < 1 := fun b => Iff.rfl
  -- `q` is prime.
  have hq_prime : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hq_mem_iff, map_one, pv.map_one]; exact lt_irrefl 1
    · intro a b hab
      rw [hq_mem_iff, map_mul, pv.map_mul] at hab
      by_contra h
      push Not at h
      obtain ⟨ha, hb⟩ := h
      rw [hq_mem_iff, not_lt] at ha hb
      have ha1 : pv (algebraMap Bb W₁.toAffine.FunctionField a) = 1 := le_antisymm (hregB a) ha
      have hb1 : pv (algebraMap Bb W₁.toAffine.FunctionField b) = 1 := le_antisymm (hregB b) hb
      rw [ha1, hb1, one_mul] at hab
      exact lt_irrefl 1 hab
  -- `q ≠ ⊥`: `z ∈ q` (the vanishing hypothesis) and `z ≠ 0`.
  have hz_mem : z ∈ q := (hq_mem_iff z).mpr hzvanish
  have hq_ne : q ≠ ⊥ := fun h => hz_ne ((Submodule.mem_bot _).mp (h ▸ hz_mem))
  -- the height-one prime `v`.
  set v : IsDedekindDomain.HeightOneSpectrum Bb := ⟨q, hq_prime, hq_ne⟩ with hv_def
  refine ⟨v, ?_⟩
  -- (3) domination: `O_v ⊆ O_P`, then equality (both rank-one DVR, `O_P ≠ ⊤`).
  have hwsurj : Function.Surjective (v.valuation W₁.toAffine.FunctionField) :=
    v.valuation_surjective W₁.toAffine.FunctionField
  have hpvsurj : Function.Surjective pv :=
    (IsDiscreteValuationRing.maximalIdeal ((⟨W₁⟩ : SmoothPlaneCurve F).localRingAt P)).valuation_surjective
      W₁.toAffine.FunctionField
  haveI : IsDiscreteValuationRing (v.valuation W₁.toAffine.FunctionField).valuationSubring :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ hwsurj
  -- `O_v ⊆ O_P`: an `O_v`-integer `f = n/d` with `d ∉ q` has `pv (algebraMap_B d) = 1`.
  have hsub : (v.valuation W₁.toAffine.FunctionField).valuationSubring ≤ pv.valuationSubring := by
    intro f hf
    rw [Valuation.mem_valuationSubring_iff] at hf ⊢
    obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      v f hf
    -- `d ∉ q = v.asIdeal`, so `pv (algebraMap_B d) = 1`.
    have hd_notin : (d : Bb) ∉ q := Ideal.mem_primeCompl_iff.mp d.2
    have hd_ge : ¬ pv (algebraMap Bb W₁.toAffine.FunctionField (d : Bb)) < 1 := by
      rw [← hq_mem_iff]; exact hd_notin
    have hd1 : pv (algebraMap Bb W₁.toAffine.FunctionField (d : Bb)) = 1 :=
      le_antisymm (hregB _) (not_lt.mp hd_ge)
    -- from `f · algMap_B d = algMap_B n`: `pv f = pv (algMap_B n) / pv (algMap_B d) ≤ 1`.
    have hfn : f = algebraMap Bb W₁.toAffine.FunctionField n /
        algebraMap Bb W₁.toAffine.FunctionField (d : Bb) := by
      have hd_ne : algebraMap Bb W₁.toAffine.FunctionField (d : Bb) ≠ 0 := by
        rw [Ne, ← pv.zero_iff, hd1]; exact one_ne_zero
      rw [eq_div_iff hd_ne, hnd]
    rw [hfn, map_div₀ pv, hd1, div_one]
    exact hregB n
  have hAtop : pv.valuationSubring ≠ ⊤ := by
    have hNontriv : pv.IsNontrivial := by
      refine ⟨?_⟩
      obtain ⟨t, ht⟩ := hpvsurj (WithZero.exp (1 : ℤ))
      refine ⟨t, ?_, ?_⟩
      · rw [ht]; exact WithZero.exp_ne_zero
      · rw [ht, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
          (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]; norm_num
    intro htop
    exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
  have hEq : (v.valuation W₁.toAffine.FunctionField).valuationSubring = pv.valuationSubring :=
    rankOne_valuationSubring_le_eq_of_ne_top _ _ hsub hAtop
  have h_isEquiv : (v.valuation W₁.toAffine.FunctionField).IsEquiv pv := by
    rw [Valuation.isEquiv_iff_valuationSubring]; rw [hEq]
  exact Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj hpvsurj h_isEquiv

/-! ### The point-map image of a `B`-prime over `m_Q` is `Q` (the fibre matching, value-level)

For a `B`-prime `v` lying over the affine place `m_Q` of `E₂`, the point `P` of `E₁` cut out by
`v` (place dictionary) satisfies `placeRestrictionPointMap φ P = Q`.  Crucially this is proved at the
*value* level — `φ^*(x_gen₂)`, `φ^*(y_gen₂)` evaluate at `P` to `Q.x`, `Q.y` — which needs **only**
`v` over `m_Q` (a generator `x_gen₂ − Q.x = algebraMap(b)` with `b ∈ m_Q` pulls back to a `B`-element
in `v.asIdeal`), *not* the exact comap-valuation equality (and hence not the ramification index
`e = 1`).  The image is then read off by `placeRestrictionPointMap_residue_agreement`. -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **The place-restriction image of a `B`-prime over `m_Q` is `Q`** (the fibre matching).  Given a
`B`-prime `v` whose point `P` (place dictionary: `v.valuation = pointValuation P`) lies over the
affine place `m_Q` of `E₂` (`v.asIdeal.under = m_Q`), the place-restriction point map sends `P` to
`Q`: `placeRestrictionPlaceImage φ (affine P) = affine Q`.  Value-level (no `e = 1`). -/
theorem placeRestrictionPlaceImage_affine_eq_of_bPrime
    (φ : HasseWeil.Isogeny W₁ W₂)
    [algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))]
    [IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    (halg : ∀ g : W₂.toAffine.FunctionField,
      algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField g = φ.pullback g)
    (v : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))
    (P : (W_smooth W₁).SmoothPoint) (Q : (W_smooth W₂).SmoothPoint)
    (hP : v.valuation W₁.toAffine.FunctionField = (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P)
    (hQ : v.asIdeal.under (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing =
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q) :
    placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P) =
      ProjectiveSmoothPoint.affine Q := by
  classical
  -- the scalar tower `F[E₂] → B → K(E₁)` (mathlib's integral-closure tower) — for `hviaB` below.
  haveI tw1B : IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField := inferInstance
  -- the `algCR1`-via-B vs `φ.pullback`-via-`K(E₂)` agreement on `F[E₂]` (both equal `algCR1`).
  have halgB : ∀ b : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField b) =
      algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField
        (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) b) := by
    intro b
    rw [← IsScalarTower.algebraMap_apply (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField b, ← halg,
      IsScalarTower.algebraMap_apply (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField W₁.toAffine.FunctionField b]
  -- A coordinate-ring element `b ∈ m_Q` pulls back to a `B`-element of `v.asIdeal`, so it has
  -- `pointValuation P`-value `< 1`.
  have hkey : ∀ b : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      b ∈ (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q →
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
        (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField b)) < 1 := by
    intro b hb
    -- `algebraMap_{F[E₂]→B} b ∈ v.asIdeal` (since `b ∈ m_Q = v.asIdeal.under`)
    have hmem : algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) b ∈ v.asIdeal := by
      have : b ∈ v.asIdeal.under (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing := by rw [hQ]; exact hb
      rwa [Ideal.mem_under] at this
    -- `φ^*(algebraMap b) = algebraMap_B (algebraMap_{F[E₂]→B} b)`, value `< 1 ↔ ∈ v.asIdeal`.
    rw [halgB b, ← hP, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  -- `x_gen₂ − Q.x = algebraMap (X − Q.x)`, `X − Q.x ∈ m_Q`; pull back ⟹ `EvaluatesTo P (φ^*x_gen₂) Q.x`.
  have hbx_mem : (algebraMap (Polynomial F) (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Polynomial.X -
      algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.x) ∈
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q := by
    have hx : (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q
        (algebraMap (Polynomial F) W₂.toAffine.CoordinateRing Polynomial.X) = Q.x := by
      rw [show algebraMap (Polynomial F) W₂.toAffine.CoordinateRing Polynomial.X =
        WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X) from rfl]
      exact (⟨W₂⟩ : SmoothPlaneCurve F).evalAt_x Q
    have h0 : (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q
        (algebraMap (Polynomial F) W₂.toAffine.CoordinateRing Polynomial.X -
          algebraMap F W₂.toAffine.CoordinateRing Q.x) = 0 :=
      (map_sub ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q) _ _).trans
        (by rw [hx]; exact sub_eq_zero_of_eq ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt_algebraMap Q Q.x).symm)
    exact (⟨W₂⟩ : SmoothPlaneCurve F).ker_evalAt Q ▸ RingHom.mem_ker.mpr h0
  have hby_mem : (AdjoinRoot.root W₂.toAffine.polynomial -
      algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.y) ∈
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q := by
    have hy : (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q (AdjoinRoot.root W₂.toAffine.polynomial) = Q.y :=
      (⟨W₂⟩ : SmoothPlaneCurve F).evalAt_y Q
    have h0 : (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q
        (AdjoinRoot.root W₂.toAffine.polynomial -
          algebraMap F W₂.toAffine.CoordinateRing Q.y) = 0 :=
      (map_sub ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q) _ _).trans
        (by rw [hy]; exact sub_eq_zero_of_eq ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt_algebraMap Q Q.y).symm)
    exact (⟨W₂⟩ : SmoothPlaneCurve F).ker_evalAt Q ▸ RingHom.mem_ker.mpr h0
  -- the two `EvaluatesTo` facts at `P`
  -- `x_gen₂ = algebraMap_{F[E₂]→K(E₂)} (algebraMap_{F[X]→F[E₂]} X)`; `y_gen₂ = algebraMap (root)`.
  have hxgen : x_gen W₂ = algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField
      (algebraMap (Polynomial F) (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Polynomial.X) := rfl
  have hygen : y_gen W₂ = algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField (AdjoinRoot.root W₂.toAffine.polynomial) := rfl
  have hEvX : EvaluatesTo W₁ P (φ.pullback (x_gen W₂)) Q.x := by
    unfold EvaluatesTo
    have hrw : φ.pullback (x_gen W₂) - algebraMap F W₁.toAffine.FunctionField Q.x =
        φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField
          (algebraMap (Polynomial F) (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Polynomial.X -
            algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.x)) := by
      rw [map_sub, map_sub, hxgen, ← φ.pullback.commutes Q.x,
        ← IsScalarTower.algebraMap_apply F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField Q.x]
    rw [hrw]
    exact hkey _ hbx_mem
  have hEvY : EvaluatesTo W₁ P (φ.pullback (y_gen W₂)) Q.y := by
    unfold EvaluatesTo
    have hrw : φ.pullback (y_gen W₂) - algebraMap F W₁.toAffine.FunctionField Q.y =
        φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField
          (AdjoinRoot.root W₂.toAffine.polynomial -
            algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.y)) := by
      rw [map_sub, map_sub, hygen, ← φ.pullback.commutes Q.y,
        ← IsScalarTower.algebraMap_apply F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField Q.y]
    rw [hrw]
    exact hkey _ hby_mem
  -- regularity of the pulled-back generators at `P` (both `≤ 1`): `x_gen₂`, `y_gen₂` are
  -- `algebraMap`-images, so their pullbacks are `B`-elements, hence `v`-integral.
  have hregGen : ∀ b : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
        (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField b)) ≤ 1 := by
    intro b
    rw [halgB b, ← hP]
    exact v.valuation_le_one (K := W₁.toAffine.FunctionField) _
  -- `P ∉ poleLocus` (both generators are regular at `P`), and the residue agreement gives the image.
  have hPnotMem : P ∉ twoCurvePoleLocus φ := by
    intro hmem
    rcases hmem with hx | hy
    · exact hx (by rw [hxgen]; exact hregGen _)
    · exact hy (by rw [hygen]; exact hregGen _)
  obtain ⟨h', himg⟩ := placeRestrictionPointMap_residue_agreement φ P hPnotMem hEvX hEvY
  -- `placeRestrictionPlaceImage φ (affine P) = (placeRestrictionPointMap φ P.toAffinePoint).toProj`
  have hgoal : placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P) =
      (placeRestrictionPointMap φ P.toAffinePoint).toProjectiveSmoothPoint := rfl
  rw [hgoal, himg]
  rfl

/-! ### The affine count identity (the per-place norm–conorm, the deep leaf)

The mathematical content of Silverman II.3.6, CoordHom-free, is the per-affine-place identity: for
`w ∈ F[E₁]` nonzero and an affine place `Q` of `E₂`, the order of the conorm `N_φ (algebraMap w)`
at `Q` equals the fibre sum of the orders of `algebraMap w` over the points `P` of `E₁` whose
place-restriction image is `Q` (all ramification `e = 1`, Silverman III.4.10c).  This is the place-
valuation form of `count_relNorm_eq_sum_fiber`, but over the integral closure `B := integralClosure
(localized φ*F[E₂]) K(E₁)` (whose maximal ideals ↔ ALL places of `E₁`) rather than the affine
`F[E₁]` (which would need a CoordHom).

The fibre `{P : placeRestrictionPointMap φ P.toAffinePoint = Q.toAffinePoint}` is finite (it sits
inside the support of `divisorOf (algebraMap w)` together with the pole locus), and the identity is
matched, term by term, to the `mapDomain` fibre sum of `placeRestrictionPushforward`
(`placeRestrictionPushforward_apply_affine`).

**Route map for the remaining leaf** (the integral-closure re-derivation):
* The localized-`D` *setup* is templated verbatim by `EC.KernelCountGeneral.card_kernel_eq_degree_of_separable`
  (the `βAlg`/`algAfK`/`algAfL`/`twAfKL`/`twFKL` instance dance + `exists_denominator` +
  `Localization.Away f₀`): take `f₀` clearing the minpoly denominators of `x_gen₁, y_gen₁` over
  `φ*K(E₂)`, then `F[E₁] ⊆ D := integralClosure Af K(E₁)` by
  `LocalizedDictionary.coordRing_mem_integralClosure`, so `algebraMap w ∈ D` (via `coordRingToClosure`).
* The *weighted* count `count_{q_Q}(relNorm_Af(span{w})) = Σ_{P' | q_Q} count_{P'}(span{w})` and the
  `s = 1` core `relNorm_Af(m_{P'}) = q_{φP'}` must be **re-derived over `D`** — these are
  `CurveMap.count_relNorm_eq_sum_fiber` / `relNorm_maximalIdealAt_eq` (`PushforwardDivisor.lean`)
  with `Af → D` in place of `F[E₂] → F[E₁]`, using `LocalizedDictionary.inertiaDeg_eq_one_of_under_eq`
  (`f = 1`) + `Ideal.sum_ramification_inertia` (`Σ ef = deg`).  `LocalizedDictionary` supplies the
  *cardinality* count but NOT this *per-element weighted* count — that is the genuine new work.
* The `pointAt`/place-identification (`LocalizedDictionary.pointAt`,
  `pointValuation_lt_one_of_mem_prime`) gives `D`-prime ↔ point-of-`E₁`, and the under-map to `Af`
  ↔ `Q`; matching it to `placeRestrictionPointMap` is `residueValue_algebraMap` +
  `twoCurve_evaluatesTo_x/y_gen_of_comap_eq` (`TwoCurvePointImage.lean`).
* **Honest gap**: the localized `D` only has residue-triviality for `Q` off the (finite) zero
  locus of `f₀` (`f₀ ∉ m_Q`).  Covering *all* `Q` (including `f₀`-zeros) needs either a global `B =
  integralClosure F[E₂] K(E₁)` re-derivation of the place-identification, or a denominator chosen to
  also avoid the fixed target `Q` (possible iff `Q` is not below a pole of `x_gen₁/y_gen₁`). -/

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
/-- **The affine count identity — Silverman II.3.6, per-place, CoordHom-free (THE DEEP LEAF).**
For `w ∈ F[E₁]` nonzero and an affine place `Q` of `E₂`, the order of the conorm `N_φ(algebraMap w)`
at `Q` equals the sum, over the points `P` of `E₁` with `placeRestrictionPointMap φ P = Q`, of the
orders of `algebraMap w` at `P`.

This is the place-valuation form of `CurveMap.count_relNorm_eq_sum_fiber` over the integral closure
`B = integralClosure (localized φ*F[E₂]) K(E₁)` (Silverman's actual II.3.6 via II.2.6a
fibre-ramification, all `e = 1` by III.4.10c over `[IsAlgClosed F]`).  It is the single genuine
deep input; everything else in this file is structural. -/
theorem twoCurve_ord_conorm_eq_sum_fiber
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f))
    {w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing} (hw : w ≠ 0)
    (Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨W₂⟩ : SmoothPlaneCurve F).ord_P Q (conorm φ
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) =
      (((placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
            (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
              (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)))
        (ProjectiveSmoothPoint.affine Q) : ℤ) : WithTop ℤ) := by
  classical
  -- ## Phase 1: set up the `NormConormIntegralClosure` section instances from `φ`.
  letI algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField := φ.toAlgebra
  haveI twF : IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.pullback.commutes c).symm
  haveI finKL : FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField := hfin
  haveI sepKL : Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField := hsep
  -- the composite algebra `F[E₂] → K(E₂) → K(E₁)`
  letI algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField :=
    ((algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField).comp
      (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField)).toAlgebra
  haveI tw1 : IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Bring the toolkit's `B`-instances explicitly into scope (they are `set_option`-gated
  -- instances in `NormConormIntegralClosure`, so re-establish them here to avoid synth timeouts).
  haveI instDed : IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instDedekindB
  haveI instFin : Module.Finite (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instModuleFiniteB
  haveI instFracB : IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField :=
    NormConormIntegralClosure.instFractionRingB
  haveI instTF : Module.IsTorsionFree (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instTorsionFreeB
  haveI instIntClosedB : IsIntegrallyClosed (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    inferInstance
  haveI instIntegralAB : Algebra.IsIntegral (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    inferInstance
  -- `hreg` in the `OrdAtInftyReg` form (the abstract algebra `algKL = φ.toAlgebra` has
  -- `algebraMap = φ.pullback`).
  have hregB : NormConormIntegralClosure.OrdAtInftyReg
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)) := hreg
  -- ## Phase 2: the LHS bridge — `ord_P Q (conorm φ (aw)) = count_{m_Q}(relNorm (span {w_B}))`.
  set aw := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w with haw
  -- `aw ∈ B` by curve-completeness (`coordRing_mem_B_of_reg`); package as `w_B : B`.
  have haw_mem : aw ∈ NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)) :=
    NormConormIntegralClosure.coordRing_mem_B_of_reg hregB w
  set wB : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)) :=
    ⟨aw, haw_mem⟩ with hwB
  have hwB_ne : wB ≠ 0 := by
    rw [hwB, Ne, Subtype.ext_iff]
    simp only [ZeroMemClass.coe_zero]
    rw [haw]
    intro h
    exact hw ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
  -- `conorm φ aw = algebraMap_{F[E₂]→K(E₂)} (intNorm F[E₂] B wB)`.
  have hconorm_eq : conorm φ aw =
      algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField
        (Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB) := by
    rw [Algebra.algebraMap_intNorm (K := (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField)
      (L := (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)]
    show conorm φ aw = Algebra.norm (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField
      (algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField wB)
    rfl
  have hintNorm_ne : Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB ≠ 0 := by
    have hconorm_ne : conorm φ aw ≠ 0 := by
      apply conorm_ne_zero φ
      rw [haw]
      intro h
      exact hw ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
    intro hzero
    rw [hconorm_eq, hzero, map_zero] at hconorm_ne
    exact hconorm_ne rfl
  -- LHS = count of `m_Q` in `span {intNorm wB}`.
  have hLHS : (⟨W₂⟩ : SmoothPlaneCurve F).ord_P Q (conorm φ aw) =
      (((Associates.mk ((⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q)).count
        (Associates.mk (Ideal.span {Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB})).factors
          : ℤ) : WithTop ℤ) := by
    rw [hconorm_eq, (⟨W₂⟩ : SmoothPlaneCurve F).ord_P_algebraMap_eq_count Q hintNorm_ne]
  -- `span {intNorm wB} = relNorm (span {wB})`, so the LHS count is over `relNorm`.
  have hrelN : Ideal.span ({Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB} :
        Set (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) =
      Ideal.relNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (Ideal.span ({wB} : Set (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))) :=
    (Ideal.relNorm_singleton (R := (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) wB).symm
  -- ## Phase 3-4: the fibre bijection (`B`-primes over `m_Q` ↔ points `P` with image `Q`) + count.
  haveI : IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  set D := (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf aw with hD_def
  set p : Ideal (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing :=
    (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q with hp_def
  have hp_ne : p ≠ ⊥ := (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt_ne_bot Q
  haveI hpMax : p.IsMaximal := (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal Q
  -- place dictionary on `E₁`: every `B`-prime `≤ 1` on the coordinate generators.
  have hcoordLE := NormConormIntegralClosure.bPrimeValuationCoordGenLeOne_of_reg hregB
  -- For each `B`-prime over `m_Q`, the point `P` it cuts out, with image `Q` and the count match.
  -- (a) the point assignment.
  have hpoint : ∀ vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))),
      vP.asIdeal ∈ IsDedekindDomain.primesOverFinset p (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) →
      ∃ P : (W_smooth W₁).SmoothPoint,
        vP.valuation W₁.toAffine.FunctionField = (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P ∧
        placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P) =
          ProjectiveSmoothPoint.affine Q := by
    intro vP hvP
    obtain ⟨P, hP⟩ := NormConormIntegralClosure.bPrime_valuation_eq_pointValuation_of_coordGen_le_one
      vP (hcoordLE vP).1 (hcoordLE vP).2
    rw [IsDedekindDomain.mem_primesOverFinset_iff (B := NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne] at hvP
    have hunder : vP.asIdeal.under (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing = p := hvP.2.over.symm
    refine ⟨P, hP, ?_⟩
    exact placeRestrictionPlaceImage_affine_eq_of_bPrime φ
      (fun g => rfl) vP P Q hP hunder
  -- (b) the count match: for a `B`-prime `vP` with point `P`, `count_{vP}(wB) = D (affine P)`.
  have hcountMatch : ∀ (vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))
      (P : (W_smooth W₁).SmoothPoint),
      vP.valuation W₁.toAffine.FunctionField = (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P →
      ((Associates.mk vP.asIdeal).count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ) =
        D (ProjectiveSmoothPoint.affine P) := by
    intro vP P hPval
    -- `vP.intValuation wB = exp(-count_vP)` and `pointValuation P aw = exp(-count_{m_P})`,
    -- equal via `vP.valuation = pointValuation P` (both applied to `aw = algebraMap_B wB`).
    have h1 : vP.valuation W₁.toAffine.FunctionField aw =
        WithZero.exp (-((Associates.mk vP.asIdeal).count
          (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ)) := by
      have hawB : aw = algebraMap (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
          W₁.toAffine.FunctionField wB := rfl
      rw [hawB, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        vP.intValuation_if_neg hwB_ne]
    have h2 : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P aw =
        WithZero.exp (-((Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P)).count
          (Associates.mk (Ideal.span {w})).factors : ℤ)) :=
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_eq_exp_count P hw
    have hcounts : ((Associates.mk vP.asIdeal).count
          (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ) =
        ((Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P)).count
          (Associates.mk (Ideal.span {w})).factors : ℤ) := by
      have : WithZero.exp (-((Associates.mk vP.asIdeal).count
            (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ)) =
          WithZero.exp (-((Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P)).count
            (Associates.mk (Ideal.span {w})).factors : ℤ)) := by
        rw [← h1, ← h2, hPval]
      rw [WithZero.exp_inj, neg_inj] at this
      exact this
    rw [hcounts, hD_def, (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine,
      (⟨W₁⟩ : SmoothPlaneCurve F).ord_P_algebraMap_eq_count P hw, WithTop.untopD_coe]
  -- ## Phase 4: assemble.  LHS = count over `relNorm` = Σ over `B`-primes; RHS = fibre sum.
  rw [hLHS, hrelN, NormConormIntegralClosure.count_relNorm_eq_sum_fiber_B hwB_ne Q]
  -- the point of a `B`-prime over `m_Q`.
  set primesB := IsDedekindDomain.primesOverFinset p (NormConormIntegralClosure.B
    (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) with hprimesB
  -- the `HeightOneSpectrum` of a member ideal + its chosen point.
  have hPrimeData : ∀ P' ∈ primesB, ∃ vP : IsDedekindDomain.HeightOneSpectrum
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))),
      vP.asIdeal = P' ∧ ∃ pt : (W_smooth W₁).SmoothPoint,
        vP.valuation W₁.toAffine.FunctionField = (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation pt ∧
        placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine pt) =
          ProjectiveSmoothPoint.affine Q := by
    intro P' hP'
    rw [hprimesB, IsDedekindDomain.mem_primesOverFinset_iff (B := NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne] at hP'
    have hP'_ne : P' ≠ ⊥ := by
      intro h; apply hp_ne
      have := hP'.2.over; rw [h, Ideal.under_bot] at this; exact this
    set vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
      ⟨P', hP'.1, hP'_ne⟩ with hvP_def
    have hmem : vP.asIdeal ∈ primesB := by
      rw [hprimesB, IsDedekindDomain.mem_primesOverFinset_iff (B := NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne]
      exact hP'
    obtain ⟨pt, hpt1, hpt2⟩ := hpoint vP hmem
    exact ⟨vP, rfl, pt, hpt1, hpt2⟩
  -- the point assignment `ptF : primesB → SmoothPoint`.
  let ptF : (P' : Ideal (NormConormIntegralClosure.B
    (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))) → P' ∈ primesB →
      (W_smooth W₁).SmoothPoint := fun P' hP' => (hPrimeData P' hP').choose_spec.2.choose
  have hptF_val : ∀ P' (hP' : P' ∈ primesB),
      (hPrimeData P' hP').choose.valuation W₁.toAffine.FunctionField =
        (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation (ptF P' hP') := fun P' hP' =>
    (hPrimeData P' hP').choose_spec.2.choose_spec.1
  have hptF_id : ∀ P' (hP' : P' ∈ primesB), (hPrimeData P' hP').choose.asIdeal = P' :=
    fun P' hP' => (hPrimeData P' hP').choose_spec.1
  have hptF_img : ∀ P' (hP' : P' ∈ primesB),
      placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine (ptF P' hP')) =
        ProjectiveSmoothPoint.affine Q := fun P' hP' =>
    (hPrimeData P' hP').choose_spec.2.choose_spec.2
  -- the count of `P'` matches `D (affine (ptF P'))`.
  have hcount_ptF : ∀ P' (hP' : P' ∈ primesB),
      ((Associates.mk P').count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ) =
        D (ProjectiveSmoothPoint.affine (ptF P' hP')) := by
    intro P' hP'
    have hcm := hcountMatch (hPrimeData P' hP').choose (ptF P' hP') (hptF_val P' hP')
    rw [hptF_id P' hP'] at hcm
    exact hcm
  -- `ptF` is injective (distinct primes ⟹ distinct valuations ⟹ distinct points).
  have hptF_inj : ∀ P₁ (h₁ : P₁ ∈ primesB) P₂ (h₂ : P₂ ∈ primesB),
      ptF P₁ h₁ = ptF P₂ h₂ → P₁ = P₂ := by
    intro P₁ h₁ P₂ h₂ heq
    have hv1 := hptF_val P₁ h₁
    have hv2 := hptF_val P₂ h₂
    rw [heq] at hv1
    -- `(hPrimeData P₁ _).choose` and `(hPrimeData P₂ _).choose` have equal valuations ⟹ equal ideals
    have hvaleq : (hPrimeData P₁ h₁).choose.valuation W₁.toAffine.FunctionField =
        (hPrimeData P₂ h₂).choose.valuation W₁.toAffine.FunctionField := by rw [hv1, hv2]
    -- equal valuations ⟹ equal `asIdeal` (both are the `< 1`-locus of the valuation).
    have hideq : (hPrimeData P₁ h₁).choose.asIdeal = (hPrimeData P₂ h₂).choose.asIdeal := by
      ext a
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
          (K := W₁.toAffine.FunctionField),
        ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
          (K := W₁.toAffine.FunctionField), hvaleq]
    rw [← hptF_id P₁ h₁, ← hptF_id P₂ h₂, hideq]
  -- the fibre image finset.
  let fibreImg : Finset (ProjectiveSmoothPoint (⟨W₁⟩ : SmoothPlaneCurve F)) :=
    primesB.attach.image (fun P' => ProjectiveSmoothPoint.affine (ptF P'.1 P'.2))
  -- Step 1: `Σ_{primesB} count = Σ_{fibreImg} D`.
  have hstep1 : (∑ P' ∈ primesB,
      ((Associates.mk P').count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ)) =
      ∑ x ∈ fibreImg, D x := by
    rw [← Finset.sum_attach primesB (fun P' =>
      ((Associates.mk P').count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ))]
    rw [Finset.sum_image (by
      rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
      simp only [ProjectiveSmoothPoint.affine.injEq] at hab
      exact Subtype.ext (hptF_inj a ha b hb hab))]
    apply Finset.sum_congr rfl
    rintro ⟨P', hP'⟩ _
    exact hcount_ptF P' hP'
  -- Step 2: `Σ_{fibreImg} D = Σ_{D.support.filter} D` (`sum_subset`, surjectivity).
  -- reduce `WithTop ℤ` goal to the `ℤ`-level fibre-sum equality, pushing the `ℕ → ℤ` cast.
  rw [placeRestrictionPushforward_apply_affine]
  refine congrArg (fun n : ℤ => (n : WithTop ℤ)) ?_
  rw [Nat.cast_sum, hstep1]
  symm
  apply Finset.sum_subset
  · -- `D.support.filter(placeImage = affine Q) ⊆ fibreImg`: surjectivity via `exists_bPrime`.
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hx_supp, hx_img⟩ := hx
    cases x with
    | infinity =>
      refine absurd hx_img ?_
      show (placeRestrictionPointMap φ
        (ProjectiveSmoothPoint.infinity : ProjectiveSmoothPoint
          (⟨W₁⟩ : SmoothPlaneCurve F)).toAffinePoint).toProjectiveSmoothPoint ≠ _
      simp only [Curves.ProjectiveSmoothPoint.toAffinePoint_infinity]
      exact fun h => by cases h
    | affine P' =>
      -- `P' ∉ poleLocus` (its image is affine `Q`), and `aw` vanishes at `P'` (it's in support).
      have hP'_notpole : P' ∉ twoCurvePoleLocus φ := by
        intro hpole
        have himg : placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P') =
            ProjectiveSmoothPoint.infinity := by
          show (placeRestrictionPointMap φ
            (ProjectiveSmoothPoint.affine P').toAffinePoint).toProjectiveSmoothPoint = _
          rw [Curves.ProjectiveSmoothPoint.toAffinePoint_affine]
          rcases P' with ⟨px, py, ph⟩
          rw [SmoothPlaneCurve.SmoothPoint.toAffinePoint_def,
            placeRestrictionPointMap_some_of_mem φ hpole]
          rfl
        rw [himg] at hx_img
        exact absurd hx_img (by simp)
      -- `aw` vanishes at `P'` (`P' ∈ support`): `ord ≠ 0` + `ord ≥ 0` (regular) ⟹ `pv < 1`.
      have hP'_vanish : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P'
          (algebraMap (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
            W₁.toAffine.FunctionField wB) < 1 := by
        rw [Finsupp.mem_support_iff, hD_def,
          (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine] at hx_supp
        have haw_ne : aw ≠ 0 := by
          rw [haw]; intro h
          exact hw ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
            (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
        show (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P' aw < 1
        rw [← (⟨W₁⟩ : SmoothPlaneCurve F).one_le_ord_P_iff_pointValuation_lt_one haw_ne]
        -- `ord_P P' aw = count ≥ 0`, and `≠ 0`, so `≥ 1`.
        rw [(⟨W₁⟩ : SmoothPlaneCurve F).ord_P_algebraMap_eq_count P' hw] at hx_supp ⊢
        have hcount_ne : (Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P')).count
            (Associates.mk (Ideal.span {w})).factors ≠ 0 := by
          intro h0; exact hx_supp (by rw [h0]; rfl)
        rw [show (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcount_ne
      obtain ⟨vP, hvP⟩ := exists_bPrime_eq_pointValuation_of_notMem_poleLocus φ
        (fun g => rfl) P' hP'_notpole hwB_ne hP'_vanish
      -- `vP` lies over the affine place `m_{Q'}` of its point's image `Q'`; `Q' = Q` (from `hx_img`).
      obtain ⟨Q', hQ'⟩ := NormConormIntegralClosure.exists_smoothPoint_under vP
      have himg' : placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P') =
          ProjectiveSmoothPoint.affine Q' :=
        placeRestrictionPlaceImage_affine_eq_of_bPrime φ (fun g => rfl) vP P' Q' hvP hQ'
      have hQeq : Q' = Q := by
        have h := himg'.symm.trans hx_img
        exact ProjectiveSmoothPoint.affine.inj h
      -- so `vP.asIdeal ∈ primesB`; the chosen point of `vP` (which has the same valuation) is `P'`.
      have hvP_mem : vP.asIdeal ∈ primesB := by
        rw [hprimesB, IsDedekindDomain.mem_primesOverFinset_iff (B := NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne]
        exact ⟨vP.isPrime, ⟨by rw [hp_def, ← hQeq]; exact hQ'.symm⟩⟩
      -- `ptF vP.asIdeal = P'` (same valuation ⟹ same point), so `affine P' ∈ fibreImg`.
      simp only [fibreImg, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      refine ⟨vP.asIdeal, hvP_mem, ?_⟩
      congr 1
      -- `(hPrimeData vP.asIdeal).choose` has `asIdeal = vP.asIdeal`, hence equals `vP`.
      have hchoose_eq : (hPrimeData vP.asIdeal hvP_mem).choose = vP :=
        IsDedekindDomain.HeightOneSpectrum.ext (hptF_id vP.asIdeal hvP_mem)
      -- so `pointValuation (ptF vP.asIdeal) = vP.valuation = pointValuation P'`.
      have hval_eq : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation (ptF vP.asIdeal hvP_mem) =
          (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P' := by
        rw [← hptF_val vP.asIdeal hvP_mem, hchoose_eq, hvP]
      -- `pointValuation` is injective on points (`maximalIdealAt` recovers the prime).
      have hmIeq : (⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt (ptF vP.asIdeal hvP_mem) =
          (⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P' := by
        ext a
        rw [← (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt a,
          ← (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt a,
          hval_eq]
      exact SmoothPlaneCurve.SmoothPoint.ext
        (congrArg (fun (P : (⟨W₁⟩ : SmoothPlaneCurve F).SmoothPoint) => P.x)
          ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt_injective hmIeq))
        (congrArg (fun (P : (⟨W₁⟩ : SmoothPlaneCurve F).SmoothPoint) => P.y)
          ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt_injective hmIeq))
  · -- the extra `fibreImg` points (not in `support.filter`) have `D = 0`.
    intro x hx_img hx_notin
    simp only [fibreImg, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx_img
    obtain ⟨P', hP', hxeq⟩ := hx_img
    rw [Finset.mem_filter, not_and] at hx_notin
    by_contra hDx
    exact hx_notin (Finsupp.mem_support_iff.mpr hDx) (by rw [← hxeq]; exact hptF_img P' hP')

/-! ### The `algebraMap` case of the norm–conorm identity (assembly)

From the per-place affine identity `twoCurve_ord_conorm_eq_sum_fiber`, the full `algebraMap` case
follows structurally: affine coefficients are matched directly, and the infinity coefficient is
forced by both projective divisors having degree `0` (and `placeRestrictionPushforward` preserving
degree, `degree_placeRestrictionPushforward`).  Mirrors
`CurveMap.projectiveDivisorOf_pushforward_algebraMap_eq`. -/

/-- **The `algebraMap` case of the norm–conorm identity (CoordHom-free)**: for `w ∈ F[E₁]` nonzero,
`div(N_φ(algebraMap w)) = placeRestrictionPushforward φ (div(algebraMap w))`.  Affine coefficients
via `twoCurve_ord_conorm_eq_sum_fiber`; infinity coefficient forced by degree `0`. -/
theorem placeRestrictionPushforward_projectiveDivisorOf_algebraMap
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f))
    {w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing} (hw : w ≠ 0) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) := by
  classical
  set aw := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w with haw
  have haw_ne : aw ≠ 0 := by
    rw [haw]; intro h
    exact hw ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
  set LHS := placeRestrictionPushforward φ
    ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf aw) with hLHS_def
  set RHS := (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ aw) with hRHS_def
  -- Affine coefficient agreement.
  have h_aff : ∀ Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint,
      RHS (ProjectiveSmoothPoint.affine Q) = LHS (ProjectiveSmoothPoint.affine Q) := by
    intro Q
    rw [hRHS_def, (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine,
      twoCurve_ord_conorm_eq_sum_fiber φ hfin hsep hreg hw Q, WithTop.untopD_coe, hLHS_def]
  -- Infinity coefficient forced by degree (both projective divisors have degree 0).
  apply Finsupp.ext
  intro v
  cases v with
  | affine Q => exact (h_aff Q).symm
  | infinity =>
    have hLHS_deg : LHS.degree = 0 := by
      rw [hLHS_def, degree_placeRestrictionPushforward]
      exact (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_degree_eq_zero _
    have hRHS_deg : RHS.degree = 0 := by
      rw [hRHS_def]; exact (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_degree_eq_zero _
    -- `E := LHS - RHS` is supported only at infinity, with degree 0.
    set E : ProjectiveDivisor (⟨W₂⟩ : SmoothPlaneCurve F) := LHS - RHS with hE_def
    have hE_aff : ∀ Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint,
        E (ProjectiveSmoothPoint.affine Q) = 0 := by
      intro Q; rw [hE_def, Finsupp.sub_apply, h_aff Q, sub_self]
    have hE_supp : E.support ⊆ {ProjectiveSmoothPoint.infinity} := by
      intro x hx
      rw [Finsupp.mem_support_iff] at hx
      cases x with
      | affine Q => exact absurd (hE_aff Q) hx
      | infinity => exact Finset.mem_singleton_self _
    have hE_single : E = Finsupp.single ProjectiveSmoothPoint.infinity
        (E ProjectiveSmoothPoint.infinity) :=
      (Finsupp.support_subset_singleton.mp hE_supp)
    have hE_deg : E.degree = 0 := by
      rw [hE_def]; unfold ProjectiveDivisor.degree
      rw [show (LHS - RHS).sum (fun _ n => n) = LHS.degree - RHS.degree from
        (ProjectiveDivisor.degree_sub LHS RHS), hLHS_deg, hRHS_deg, sub_zero]
    have hEinf : E ProjectiveSmoothPoint.infinity = 0 := by
      have : E.degree = E ProjectiveSmoothPoint.infinity := by
        conv_lhs => rw [hE_single]
        unfold ProjectiveDivisor.degree
        rw [Finsupp.sum_single_index rfl]
      rw [this] at hE_deg; exact hE_deg
    have hdiff : LHS ProjectiveSmoothPoint.infinity - RHS ProjectiveSmoothPoint.infinity = 0 := by
      rw [← Finsupp.sub_apply]; exact hEinf
    linarith [hdiff]

/-! ### The norm–conorm identity and `PlaceRestrictionPreservesPrincipal` -/

/-- **The CoordHom-free norm–conorm identity (Silverman II.3.6)**: for a separable two-curve
isogeny `φ` over `[IsAlgClosed F]`, `div(N_φ f) = placeRestrictionPushforward φ (div f)` for all
`f ∈ K(E₁)`.  The `algebraMap` case is `placeRestrictionPushforward_projectiveDivisorOf_algebraMap`;
the general case is the `f = u/v` reduction. -/
theorem placeRestrictionPushforward_projectiveDivisorOf
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f))
    (f : W₁.toAffine.FunctionField) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) :=
  placeRestrictionPushforward_projectiveDivisorOf_of_algebraMap φ hfin
    (fun _ hw => placeRestrictionPushforward_projectiveDivisorOf_algebraMap φ hfin hsep hreg hw) f

/-- **`PlaceRestrictionPreservesPrincipal` (Silverman II.3.6/II.3.7), separable case** — the single
remaining wall of char-0 isogeny symmetry, CoordHom-free.  Given that `K(E₁)/φ*K(E₂)` is finite and
separable, the place-restriction pushforward carries principal projective divisors to principal
projective divisors: if `D = div f` (`f ≠ 0`), then `placeRestrictionPushforward φ D = div(N_φ f)`
with `N_φ f ∈ K(E₂)` nonzero. -/
theorem placeRestrictionPreservesPrincipal_of_finite_separable
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f)) :
    PlaceRestrictionPreservesPrincipal φ := by
  intro D hD
  obtain ⟨f, hf_ne, hfD⟩ := hD
  refine ⟨conorm φ f, conorm_ne_zero φ hf_ne, ?_⟩
  rw [← hfD]
  exact (placeRestrictionPushforward_projectiveDivisorOf φ hfin hsep hreg f).symm

/-- **`PlaceRestrictionPreservesPrincipal` from separability alone (the wall's clean form).**  The
finite-dimensionality hypothesis is automatic (`isogeny_finiteDimensional_twoCurve`), so the single
remaining wall of char-0 isogeny symmetry rests on *separability* of `φ` alone (over
`[IsAlgClosed F]`) — exactly Silverman III.4.10c's hypothesis.  This is the form to wire into
`placeRestrictionRealizationOfPreservesPrincipal` at the `twoCurveGeometricDualData` call site. -/
theorem placeRestrictionPreservesPrincipal_of_separable
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f)) :
    PlaceRestrictionPreservesPrincipal φ :=
  placeRestrictionPreservesPrincipal_of_finite_separable φ
    (isogeny_finiteDimensional_twoCurve φ) hsep hreg

/-- **`PlaceRestrictionPreservesPrincipal` from separability alone, char-zero form.**  In
characteristic zero the `PerfectField (FractionRing F[E₂])` instance is automatic (`K(E₂)` has
characteristic zero, hence is perfect), so the norm–conorm wall holds with no instance side-condition
beyond the standing `[IsAlgClosed F]` (the III.4.10c setting).  This is the convenient form to wire
into `placeRestrictionRealizationOfPreservesPrincipal` at the `twoCurveGeometricDualData` call site
(where the ambient field is `CharZero`). -/
theorem placeRestrictionPreservesPrincipal_of_separable_charZero [CharZero F]
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f)) :
    PlaceRestrictionPreservesPrincipal φ := by
  haveI : CharZero (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing :=
    charZero_of_injective_algebraMap (R := F) (algebraMap F _).injective
  haveI : CharZero (FractionRing (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) :=
    charZero_of_injective_algebraMap (R := (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing)
      (IsFractionRing.injective (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing _)
  exact placeRestrictionPreservesPrincipal_of_separable φ hsep hreg

end HasseWeil.WeilPairing
