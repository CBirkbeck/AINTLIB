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

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

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

@[simp] theorem conorm_mul (φ : HasseWeil.Isogeny W₁ W₂) (f g : W₁.toAffine.FunctionField) :
    conorm φ (f * g) = conorm φ f * conorm φ g :=
  (conorm φ).map_mul f g

@[simp] theorem conorm_one (φ : HasseWeil.Isogeny W₁ W₂) :
    conorm φ (1 : W₁.toAffine.FunctionField) = 1 :=
  (conorm φ).map_one

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

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
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
  have hBA : Bv ≤ A := by
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
  -- `A ≠ ⊤`: `w` is nontrivial (surjective onto `ℤᵐ⁰`).
  have hAtop : A ≠ ⊤ := by
    have hNontriv : w.IsNontrivial := by
      refine ⟨?_⟩
      obtain ⟨z, hz⟩ := hwsurj (WithZero.exp (1 : ℤ))
      refine ⟨z, ?_, ?_⟩
      · rw [hz]; exact WithZero.exp_ne_zero
      · rw [hz, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
          (WithZero.exp_zero).symm, Ne, WithZero.exp_inj]; norm_num
    intro htop
    rw [hA] at htop
    exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
  have hEq : Bv = A := rankOne_valuationSubring_le_eq_of_ne_top Bv A hBA hAtop
  have h_isEquiv : w.IsEquiv (C.pointValuation Q) := by
    rw [Valuation.isEquiv_iff_valuationSubring]; rw [hA, hBv] at hEq; exact hEq.symm
  exact Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj hpvsurj h_isEquiv

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
    [PerfectField (FractionRing (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing)]
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
  sorry

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
    [PerfectField (FractionRing (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing)]
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
    [PerfectField (FractionRing (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing)]
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
    (fun w hw => placeRestrictionPushforward_projectiveDivisorOf_algebraMap φ hfin hsep hreg hw) f

/-- **`PlaceRestrictionPreservesPrincipal` (Silverman II.3.6/II.3.7), separable case** — the single
remaining wall of char-0 isogeny symmetry, CoordHom-free.  Given that `K(E₁)/φ*K(E₂)` is finite and
separable, the place-restriction pushforward carries principal projective divisors to principal
projective divisors: if `D = div f` (`f ≠ 0`), then `placeRestrictionPushforward φ D = div(N_φ f)`
with `N_φ f ∈ K(E₂)` nonzero. -/
theorem placeRestrictionPreservesPrincipal_of_finite_separable
    [PerfectField (FractionRing (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing)]
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
    [PerfectField (FractionRing (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing)]
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
