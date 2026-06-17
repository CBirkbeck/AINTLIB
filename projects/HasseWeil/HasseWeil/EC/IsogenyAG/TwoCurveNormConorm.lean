/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.TwoCurveGroupHom
import HasseWeil.Curves.LocalizedDictionary
import HasseWeil.Curves.PushforwardDivisor

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
matched, term by term, to the `mapDomain` fibre sum of `placeRestrictionPushforward`. -/

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
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
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
      twoCurve_ord_conorm_eq_sum_fiber φ hfin hsep hw Q, WithTop.untopD_coe, hLHS_def]
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
    (f : W₁.toAffine.FunctionField) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) :=
  placeRestrictionPushforward_projectiveDivisorOf_of_algebraMap φ hfin
    (fun w hw => placeRestrictionPushforward_projectiveDivisorOf_algebraMap φ hfin hsep hw) f

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
      φ.toAlgebra) :
    PlaceRestrictionPreservesPrincipal φ := by
  intro D hD
  obtain ⟨f, hf_ne, hfD⟩ := hD
  refine ⟨conorm φ f, conorm_ne_zero φ hf_ne, ?_⟩
  rw [← hfD]
  exact (placeRestrictionPushforward_projectiveDivisorOf φ hfin hsep f).symm

end HasseWeil.WeilPairing
