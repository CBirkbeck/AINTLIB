/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.MulByIntSamePlace
import HasseWeil.EC.MulByIntUnramified
import HasseWeil.EC.TranslateOrdInfty
import HasseWeil.WeilPairing.SigmaBridge
import HasseWeil.WeilPairing.TorsionGeometric

/-!
# Divisor-pullback functoriality for the separable multiplication-by-`ℓ` isogeny

For a separable isogeny `φ = [ℓ]` (`(ℓ : F) ≠ 0`, `[IsAlgClosed F]`) and a nonzero rational
function `h ∈ K(E)`, the divisor of the pulled-back function `φ.pullback h` equals the geometric
pullback of `div h`:
```
divisorOf (φ.pullback h) = pullback-of-divisor (divisorOf h).
```
Because `[ℓ]` is **separable** (unramified — every fibre is étale, multiplicity `1`), the pullback
of a single place `(Q)` is the multiplicity-free fibre sum `Σ_{φP=Q} (P)` (the repo's
`pullbackDiv`, `WeilPairing/Pullback.lean`). The geometric heart is the per-place
**unramified order-transport**
```
ord_P (φ.pullback h) = ord_{φ(P)} (h)        (no ramification factor `e_P > 1`),
```
which, summed over all places, yields the divisor identity. This is Silverman III.4.10c /
III.8.1–2 in divisor language: the geometric content of the separability of `[ℓ]`.

## Architecture

* **Item 1 — the core (`OrdTransport` / `ordTransport_mulByInt`).** The per-place transport
  `ord_P P (φ.pullback h) = (ord of h at φ(P))` is the deep geometric unramifiedness statement.
  It is the exact isogeny analogue of the translation order-transport proven in
  `EC/TranslateValuation.lean` + `EC/TranslateOrdInfty.lean` (≈5000 lines): a valuation on `K(E)`
  pinned by its values on `x_gen`, `y_gen`. For an isogeny the base values
  `ord_P P (φ.pullback x_gen)`, `ord_P P (φ.pullback y_gen)` are the `ℓ`-division-polynomial orders,
  whose computation is the genuine ramification content. We **isolate** this as the named predicate
  `OrdTransport` (a per-`(P, φ)` hypothesis bundling the projective place transport) and prove the
  full divisor assembly on top of it.

* **Item 2 — the assembly (`projectiveDivisorOf_pullback_eq_pullbackDivisor`).** Given the core
  for every place, the projective divisor of `φ.pullback h` equals the fibre-pullback of the
  projective divisor of `h`. This is a pure `Finsupp` computation: every coefficient matches by
  the core, and the supports are related by the (finite) fibre structure. Fully proven modulo the
  core.

* **Item 3 — the pairing-facing corollaries.** `pullback_divisorOf_eq_of_divisorOf_eq` (the
  shape bilinearity-in-`T` and nondegeneracy consume) and the III.8.1 relation
  `weilFunction_pow_mem_pullback_range`-style statement, parametric on the core.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.4.10c, III.8.1, III.8.2.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing.DivisorPullback

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- Local abbreviation for the function field `K(E)` (`= (⟨W⟩ : SmoothPlaneCurve F).FunctionField`),
used to keep the infinity-transport proof's `algebraMap` expressions within the line limit. -/
local notation3 "KE" => W.toAffine.FunctionField

/-- The coefficient of `projectiveDivisorOf f` at the projective place coming from an
`Affine.Point` `Q`: `ord_Q f` for a finite point, `ordAtInfty f` for the zero point. -/
noncomputable def projOrdAt (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (Q : W.Point) : ℤ :=
  (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f Q.toProjectiveSmoothPoint

theorem projOrdAt_some (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) {x y : F}
    (h : W.Nonsingular x y) :
    projOrdAt f (Affine.Point.some x y h) =
      ((⟨W⟩ : SmoothPlaneCurve F).ord_P ⟨x, y, h⟩ f).untopD 0 := by
  rw [projOrdAt, Affine.Point.toProjectiveSmoothPoint_some,
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine f ⟨x, y, h⟩]

theorem projOrdAt_zero (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) :
    projOrdAt f (0 : W.Point) = ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f).untopD 0 := by
  rw [projOrdAt, Affine.Point.toProjectiveSmoothPoint_zero,
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_infinity f]

/-- **The per-place unramified order-transport predicate** for `φ` at the smooth point `P`:
the order of `φ.pullback h` at `P` equals the order of `h` at the image point `φ(P)`
(`projOrdAt h (φ.toAddMonoidHom P.toAffinePoint)`), for every `h`.

For `φ = [ℓ]` separable this is the unramified (multiplicity-`1`) order transport — the geometric
content of the separability of `[ℓ]` (Silverman III.4.10c). It carries no `e_P` factor precisely
because `[ℓ]` is separable. -/
def OrdTransport (φ : Isogeny W W) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) : Prop :=
  ∀ h : (⟨W⟩ : SmoothPlaneCurve F).FunctionField,
    ((⟨W⟩ : SmoothPlaneCurve F).ord_P P (φ.pullback h)).untopD 0 =
      projOrdAt h (φ.toAddMonoidHom P.toAffinePoint)

/-- The order-transport at the level of the projective-divisor coefficient: under `OrdTransport`,
the coefficient of `projectiveDivisorOf (φ.pullback h)` at the affine place `P` equals the
coefficient of `projectiveDivisorOf h` at the image place `φ(P)`. -/
theorem coeff_affine_pullback_eq {φ : Isogeny W W}
    {P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint} (hP : OrdTransport φ P)
    (h : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) :
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf (φ.pullback h) (ProjectiveSmoothPoint.affine P) =
      projOrdAt h (φ.toAddMonoidHom P.toAffinePoint) := by
  rw [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine (φ.pullback h) P]
  exact hP h

/-- **The fibre-pullback of a projective divisor** under a point-map endomorphism with finite
kernel: `φ*(D) = Σ_v D(v) · pullbackDiv(v)`, the `ℤ`-linear extension of the multiplicity-free
fibre pullback `pullbackDiv` (`WeilPairing/Pullback.lean`) over the (projective) places of `D`.
The place at infinity pulls back to `pullbackDiv f h 0 = Σ_{φP=O}(P)` (the kernel). -/
noncomputable def pullbackDivisor (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) :=
  D.sum fun v n => n • pullbackDiv f hf v.toAffinePoint

@[simp] theorem pullbackDivisor_zero (f : W.Point →+ W.Point) (hf : Finite f.ker) :
    pullbackDivisor f hf 0 = 0 := by
  simp [pullbackDivisor]

@[simp] theorem pullbackDivisor_single (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (v : ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (n : ℤ) :
    pullbackDivisor f hf (Finsupp.single v n) = n • pullbackDiv f hf v.toAffinePoint := by
  rw [pullbackDivisor, Finsupp.sum_single_index]
  rw [zero_smul]

@[simp] theorem pullbackDivisor_add (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (D₁ D₂ : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    pullbackDivisor f hf (D₁ + D₂) = pullbackDivisor f hf D₁ + pullbackDivisor f hf D₂ := by
  rw [pullbackDivisor, pullbackDivisor, pullbackDivisor, Finsupp.sum_add_index']
  · intro v
    rw [zero_smul]
  · intro v m n
    rw [add_smul]

/-- `pullbackDivisor` bundled as an additive group homomorphism. -/
noncomputable def pullbackDivisorHom (f : W.Point →+ W.Point) (hf : Finite f.ker) :
    ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) →+
      ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) where
  toFun := pullbackDivisor f hf
  map_zero' := pullbackDivisor_zero f hf
  map_add' := pullbackDivisor_add f hf

@[simp] theorem pullbackDivisorHom_apply (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    pullbackDivisorHom f hf D = pullbackDivisor f hf D := rfl

/-- The coefficient of `pullbackDiv f hf Q` at *any* projective place `w` is `1` if
`φ(w.toAffinePoint) = Q`, else `0`. This holds uniformly at affine and infinity places, because the
`pullbackDiv` support is `{R.toProjectiveSmoothPoint : f R = Q}` and the round-trip
`w.toAffinePoint.toProjectiveSmoothPoint = w` identifies a place with its `Affine.Point`. The
infinity place is the image of `0 : W.Point`, which lies in the fibre over `Q` iff `Q = 0`. -/
theorem pullbackDiv_apply (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (Q : W.Point) (w : ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) :
    pullbackDiv f hf Q w = if f w.toAffinePoint = Q then 1 else 0 := by
  classical
  letI : Fintype {R : W.Point // f R = Q} := @Fintype.ofFinite _ (fiber_finite f hf Q)
  rw [pullbackDiv, Finsupp.finset_sum_apply]
  by_cases hwQ : f w.toAffinePoint = Q
  · rw [if_pos hwQ]
    have hwproj : (⟨w.toAffinePoint, hwQ⟩ : {R : W.Point // f R = Q}).val.toProjectiveSmoothPoint =
        w := Affine.Point.toAffinePoint_toProjectiveSmoothPoint w
    rw [Finset.sum_eq_single (⟨w.toAffinePoint, hwQ⟩ : {R : W.Point // f R = Q})]
    · rw [hwproj, Finsupp.single_eq_same]
    · intro R _ hR
      rw [Finsupp.single_eq_of_ne]
      intro hcontra
      apply hR
      have hRval : R.val = w.toAffinePoint := by
        have h1 := congrArg ProjectiveSmoothPoint.toAffinePoint hcontra
        rw [Affine.Point.toProjectiveSmoothPoint_toAffinePoint] at h1
        exact h1.symm
      exact Subtype.ext hRval
    · intro hni
      exact absurd (Finset.mem_univ _) hni
  · rw [if_neg hwQ]
    refine Finset.sum_eq_zero (fun R _ => ?_)
    rw [Finsupp.single_eq_of_ne]
    intro hcontra
    apply hwQ
    have hRval : R.val = w.toAffinePoint := by
      have h1 := congrArg ProjectiveSmoothPoint.toAffinePoint hcontra
      rw [Affine.Point.toProjectiveSmoothPoint_toAffinePoint] at h1
      exact h1.symm
    rw [← hRval]
    exact R.property

/-- The coefficient of `pullbackDiv f hf Q` at an affine place `P` is `1` if `φ(P) = Q`, else `0`.
This is the multiplicity-free / étale fibre structure (separable case); a specialization of
`pullbackDiv_apply` to an affine place via `ProjectiveSmoothPoint.toAffinePoint_affine`. -/
theorem pullbackDiv_apply_affine (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (Q : W.Point) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    pullbackDiv f hf Q (ProjectiveSmoothPoint.affine P) =
      if f P.toAffinePoint = Q then 1 else 0 := by
  rw [pullbackDiv_apply, ProjectiveSmoothPoint.toAffinePoint_affine]

/-- **The coefficient of `pullbackDivisor f hf D` at any place `w` is the coefficient of `D` at the
image place `φ(w)`** (`= D ((φ w.toAffinePoint).toProjectiveSmoothPoint)`). The fibre-pullback
divisor "transports" coefficients along `φ`. Uniform at affine and infinity places. -/
theorem pullbackDivisor_apply (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F))
    (w : ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) :
    pullbackDivisor f hf D w = D (f w.toAffinePoint).toProjectiveSmoothPoint := by
  classical
  rw [pullbackDivisor, Finsupp.sum_apply, Finsupp.sum]
  have hterm : ∀ v ∈ D.support,
      (D v • pullbackDiv f hf v.toAffinePoint) w =
        if (f w.toAffinePoint).toProjectiveSmoothPoint = v then D v else 0 := by
    intro v _
    rw [Finsupp.coe_smul, Pi.smul_apply, pullbackDiv_apply, smul_eq_mul]
    by_cases hv : f w.toAffinePoint = v.toAffinePoint
    · rw [if_pos hv, mul_one, if_pos]
      rw [hv, Affine.Point.toAffinePoint_toProjectiveSmoothPoint]
    · rw [if_neg hv, mul_zero, if_neg]
      intro hcontra
      apply hv
      have := congrArg ProjectiveSmoothPoint.toAffinePoint hcontra
      rwa [Affine.Point.toProjectiveSmoothPoint_toAffinePoint] at this
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq D.support (f w.toAffinePoint).toProjectiveSmoothPoint (fun v => D v)]
  by_cases hmem : (f w.toAffinePoint).toProjectiveSmoothPoint ∈ D.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem]

/-- **The per-place core, projective form.** For the isogeny `φ`, the coefficient of
`projectiveDivisorOf (φ.pullback h)` at the projective place `w` equals the coefficient of
`projectiveDivisorOf h` at the image place `φ(w.toAffinePoint)`. This is the unramified
order-transport at affine places (`OrdTransport`) and at infinity (`φ(∞) = ∞`), packaged uniformly.

For `φ = [ℓ]` separable, this is the geometric content of the multiplicity-free divisor pullback. -/
def ProjOrdTransport (φ : Isogeny W W) : Prop :=
  ∀ (h : (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (w : ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)),
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf (φ.pullback h) w =
      projOrdAt h (φ.toAddMonoidHom w.toAffinePoint)

/-- **Item 2 — divisor functoriality.** Under the per-place projective order-transport core
(`ProjOrdTransport φ`, the geometric unramifiedness of `φ`), the projective divisor of
`φ.pullback h` equals the fibre-pullback of the projective divisor of `h`:
```
projectiveDivisorOf (φ.pullback h) = pullbackDivisor φ (projectiveDivisorOf h).
```
This is the divisor-pullback functoriality: `div(φ*h) = φ*(div h)` (Silverman III.4.10c / III.8). -/
theorem projectiveDivisorOf_pullback_eq_pullbackDivisor {φ : Isogeny W W}
    [Finite φ.toAddMonoidHom.ker] (hcore : ProjOrdTransport φ)
    (h : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) :
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf (φ.pullback h) =
      pullbackDivisor φ.toAddMonoidHom inferInstance
        ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf h) := by
  refine Finsupp.ext fun w => ?_
  rw [hcore h w,
    pullbackDivisor_apply φ.toAddMonoidHom inferInstance
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf h) w]
  rfl

/-- **The order-transport at infinity** for `φ`: the `∞`-coefficient of
`projectiveDivisorOf (φ.pullback h)` equals the `∞`-coefficient of `projectiveDivisorOf h`, since
`φ(∞) = ∞`. As `φ(O) = O` always (group homomorphism), this is `ord_∞(φ.pullback h) = ord_∞ h`. -/
def InftyOrdTransport (φ : Isogeny W W) : Prop :=
  ∀ h : (⟨W⟩ : SmoothPlaneCurve F).FunctionField,
    ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback h)).untopD 0 =
      ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty h).untopD 0

/-- **Bridge to the uniform core.** `ProjOrdTransport φ` follows from the affine order-transport at
every smooth point (`OrdTransport φ P`) together with the infinity transport
(`InftyOrdTransport φ`). A projective place is either an affine point (`OrdTransport`) or `∞`
(`InftyOrdTransport`, noting `φ(∞) = ∞`). -/
theorem projOrdTransport_of_affine_of_infinity {φ : Isogeny W W}
    (haff : ∀ P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint, OrdTransport φ P)
    (hinf : InftyOrdTransport φ) :
    ProjOrdTransport φ := by
  intro h w
  cases w with
  | affine P =>
    rw [coeff_affine_pullback_eq (haff P) h]
    rfl
  | infinity =>
    rw [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_infinity (φ.pullback h), hinf h,
      ProjectiveSmoothPoint.toAffinePoint_infinity, map_zero, projOrdAt_zero]

/-- **The infinity transport for `[ℓ]`**: `ord_∞([ℓ].pullback h) = ord_∞ h` for every `h`, since
`[ℓ]` fixes the place at infinity (`[ℓ]·O = O`). -/
theorem inftyOrdTransport_mulByInt (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    InftyOrdTransport (mulByInt W ℓ) := by
  set τ := (mulByInt W ℓ).pullback
  set w := ((⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation).comap τ.toRingHom
  have hw_apply : ∀ g, w g = (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation (τ g) := fun g =>
    Valuation.comap_apply _ _ _
  have hx : w (x_gen W) = WithZero.exp 2 := by
    rw [hw_apply, show τ (x_gen W) = mulByInt_x W ℓ from mulByInt_pullback_x W ℓ hℓ]
    rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq
      (mulByInt_x_ne_zero W ℓ hℓ) (ordAtInfty_mulByInt_x W ℓ hℓ hℓF)]
    norm_num
  have hy : w (y_gen W) = WithZero.exp 3 := by
    have hy_ne : mulByInt_y W ℓ ≠ 0 := by
      intro h0
      have := ordAtInfty_mulByInt_y_eq_neg_three_general (W := W) ℓ hℓ hℓF
      rw [h0, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_zero] at this
      exact WithTop.top_ne_coe this
    rw [hw_apply, show τ (y_gen W) = mulByInt_y W ℓ from mulByInt_pullback_y W ℓ hℓ]
    rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq
      hy_ne (ordAtInfty_mulByInt_y_eq_neg_three_general ℓ hℓ hℓF)]
    norm_num
  have hc : ∀ c : F, c ≠ 0 →
      w (algebraMap F KE c) = 1 := fun c hc => by
    rw [hw_apply, show τ (algebraMap F KE c) =
        algebraMap F KE c from τ.commutes c]
    have h_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
        (algebraMap F KE c) = ((0 : ℤ) : WithTop ℤ) := by
      rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_algebraMap_F_nonzero hc]
      rfl
    have h_ne : algebraMap F KE c ≠ 0 :=
      fun h => hc (FaithfulSMul.algebraMap_injective F _ (h.trans (map_zero _).symm))
    rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq h_ne h_ord]
    norm_num
  have hval : w = (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation :=
    eq_ordAtInftyValuation_of_x_y W w hx hy hc
  intro h
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_zero]
  · have hτh_ne : τ h ≠ 0 := fun h0 => hh (τ.injective (h0.trans (map_zero τ).symm))
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (τ h) = (m : WithTop ℤ) :=
      ⟨_, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_of_ne hτh_ne⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty h = (n : WithTop ℤ) :=
      ⟨_, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_of_ne hh⟩
    have hval_at : (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation (τ h) =
        (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation h := by
      have hwh := congrFun (congrArg DFunLike.coe hval) h
      rw [hw_apply] at hwh
      exact hwh
    rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hτh_ne hm,
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hh hn,
      WithZero.exp_inj] at hval_at
    change ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (τ h)).untopD 0 =
      ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty h).untopD 0
    rw [hm, hn, WithTop.untopD_coe, WithTop.untopD_coe]
    omega

/-- **Comap-valuation identity, affine-image case** (proven, axiom-clean). The comap of
`pointValuation P` along `[ℓ].pullback` equals `pointValuation` at the affine image smooth point
`⟨x, y, h_ns⟩`. This is the unramifiedness of `[ℓ]` at an affine image (Silverman III.4.10c). -/
theorem comap_pointValuation_mulByInt_eq_affine [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).comap (mulByInt W ℓ).pullback.toRingHom =
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  by_cases h2 : y = W.negY x y
  · have he1 : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        ((mulByInt W ℓ).pullback (y_gen W - algebraMap F KE y)) = ((1 : ℤ) : WithTop ℤ) := by
      rw [map_sub, (mulByInt W ℓ).pullback.commutes,
        show (mulByInt W ℓ).pullback (y_gen W) = mulByInt_y W ℓ from mulByInt_pullback_y W ℓ hℓ0]
      exact ord_P_mulByInt_y_sub_const_eq_one (W := W) ℓ hℓ0 hℓ P h_ns h2 hQ
    exact Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one
      (⟨W⟩ : SmoothPlaneCurve F) (mulByInt W ℓ).pullback.toRingHom P
      ((⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩)
      ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_surjective' ⟨x, y, h_ns⟩)
      (mulByInt_comap_pointValuation_isEquiv_affine (W := W) ℓ hℓ P h_ns hQ) he1
  · have he1 : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        ((mulByInt W ℓ).pullback (x_gen W - algebraMap F KE x)) = ((1 : ℤ) : WithTop ℤ) := by
      rw [map_sub, (mulByInt W ℓ).pullback.commutes,
        show (mulByInt W ℓ).pullback (x_gen W) = mulByInt_x W ℓ from mulByInt_pullback_x W ℓ hℓ0]
      exact ord_P_mulByInt_x_sub_const_eq_one W ℓ hℓ0 hℓ P h_ns h2 hQ
    exact Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one
      (⟨W⟩ : SmoothPlaneCurve F) (mulByInt W ℓ).pullback.toRingHom P
      ((⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩)
      ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_surjective' ⟨x, y, h_ns⟩)
      (mulByInt_comap_pointValuation_isEquiv_affine (W := W) ℓ hℓ P h_ns hQ) he1

/-- **The `[ℓ]`-order-transport, affine-image case.** For `φ = [ℓ]` separable and an affine smooth
point `P` whose image `[ℓ]·P` is the finite point `some x y h_ns`, the order of `[ℓ].pullback f` at
`P` equals the order of `f` at `⟨x, y, h_ns⟩`, for every nonzero `f` — *with no ramification factor*
(the unramifiedness of `[ℓ]`, Silverman III.4.10c). -/
theorem ord_P_mulByInt_pullback_eq_affine [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P ((mulByInt W ℓ).pullback f) =
      (⟨W⟩ : SmoothPlaneCurve F).ord_P ⟨x, y, h_ns⟩ f := by
  have hval := comap_pointValuation_mulByInt_eq_affine (W := W) ℓ hℓ P h_ns hQ
  have hτf_ne : (mulByInt W ℓ).pullback f ≠ 0 :=
    fun h0 => hf ((mulByInt W ℓ).pullback_injective (h0.trans (map_zero _).symm))
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P ⟨x, y, h_ns⟩ f = (n : WithTop ℤ) := by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (P := ⟨x, y, h_ns⟩) f).not.mpr hf)
    exact ⟨n, hn.symm⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P ((mulByInt W ℓ).pullback f) = (m : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (P := P) _).not.mpr hτf_ne)
    exact ⟨m, hm.symm⟩
  have h_at : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback f) =
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ f := by
    have := congrFun (congrArg DFunLike.coe hval) f
    rwa [Valuation.comap_apply] at this
  rw [pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W⟩ : SmoothPlaneCurve F)) (P := P) hτf_ne hm,
    pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W⟩ : SmoothPlaneCurve F))
      (P := (⟨x, y, h_ns⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)) hf hn,
    WithZero.exp_inj] at h_at
  rw [hm, hn]
  exact_mod_cast (by omega : m = n)

/-- **The `[ℓ]`-order-transport, infinity-image case.** For `φ = [ℓ]` separable and an affine smooth
point `P` that is an `ℓ`-torsion point (`[ℓ]·P = O`), the order of `[ℓ].pullback f` at `P` equals
`ord_∞ f`, for every nonzero `f` (the unramifiedness of `[ℓ]`, Silverman III.4.10c). -/
theorem ord_P_mulByInt_pullback_eq_infty [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = (0 : W.Point))
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P ((mulByInt W ℓ).pullback f) =
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f := by
  have hval := comap_pointValuation_mulByInt_eq_infty (W := W) ℓ hℓ P hQ
  have hτf_ne : (mulByInt W ℓ).pullback f ≠ 0 :=
    fun h0 => hf ((mulByInt W ℓ).pullback_injective (h0.trans (map_zero _).symm))
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f = (n : WithTop ℤ) :=
    ⟨_, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_of_ne hf⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P ((mulByInt W ℓ).pullback f) = (m : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (P := P) _).not.mpr hτf_ne)
    exact ⟨m, hm.symm⟩
  have h_at : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback f) =
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation f := by
    have := congrFun (congrArg DFunLike.coe hval) f
    rwa [Valuation.comap_apply] at this
  rw [pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W⟩ : SmoothPlaneCurve F)) (P := P) hτf_ne hm,
    (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hf hn,
    WithZero.exp_inj] at h_at
  rw [hm, hn]
  exact_mod_cast (by omega : m = n)

/-- **The AFFINE per-place order-transport for `[ℓ]`.** For `φ = [ℓ]` separable
(`(ℓ : F) ≠ 0`, `[IsAlgClosed F]`), the order of `φ.pullback h` at any *affine* smooth point `P`
equals the order of `h` at `φ(P) = [ℓ]·P` — *with no ramification factor*. This is the geometric
unramifiedness of `[ℓ]` (Silverman III.4.10c). -/
theorem ordTransport_affine_mulByInt [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    OrdTransport (mulByInt W ℓ) P := by
  intro h
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero, (⟨W⟩ : SmoothPlaneCurve F).ord_P_zero, WithTop.untopD_top]
    rw [projOrdAt, (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_zero]
    rfl
  set τ := (mulByInt W ℓ).pullback
  have hτh_ne : τ h ≠ 0 :=
    fun h0 => hh ((mulByInt W ℓ).pullback_injective (h0.trans (map_zero _).symm))
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (⟨W⟩ : SmoothPlaneCurve F).ord_P P (τ h) = (m : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (τ h)).not.mpr hτh_ne)
    exact ⟨m, hm.symm⟩
  have hlhs_exp : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (τ h) = WithZero.exp (-m) :=
    pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W⟩ : SmoothPlaneCurve F)) (P := P) hτh_ne hm
  rcases hQcase : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint with _ | ⟨x, y, h_ns⟩
  · have hval := comap_pointValuation_mulByInt_eq_infty (W := W) ℓ hℓ P hQcase
    have h_at : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (τ h) =
        (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation h := by
      have := congrFun (congrArg DFunLike.coe hval) h
      rwa [Valuation.comap_apply] at this
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty h = (n : WithTop ℤ) :=
      ⟨_, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_of_ne hh⟩
    rw [hlhs_exp, (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hh hn,
      WithZero.exp_inj] at h_at
    change ((⟨W⟩ : SmoothPlaneCurve F).ord_P P (τ h)).untopD 0 = projOrdAt h (0 : W.Point)
    rw [projOrdAt_zero, hm, hn, WithTop.untopD_coe, WithTop.untopD_coe]
    omega
  · have hval := comap_pointValuation_mulByInt_eq_affine (W := W) ℓ hℓ P h_ns hQcase
    have h_at : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (τ h) =
        (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ h := by
      have := congrFun (congrArg DFunLike.coe hval) h
      rwa [Valuation.comap_apply] at this
    obtain ⟨n, hn⟩ : ∃ n : ℤ,
        (⟨W⟩ : SmoothPlaneCurve F).ord_P ⟨x, y, h_ns⟩ h = (n : WithTop ℤ) := by
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (P := ⟨x, y, h_ns⟩) h).not.mpr hh)
      exact ⟨n, hn.symm⟩
    rw [hlhs_exp, pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W⟩ : SmoothPlaneCurve F))
        (P := (⟨x, y, h_ns⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)) hh hn,
      WithZero.exp_inj] at h_at
    rw [projOrdAt_some, hm, hn, WithTop.untopD_coe, WithTop.untopD_coe]
    omega

/-- **The per-place core for `[ℓ]`**: the affine order-transport `ordTransport_affine_mulByInt` at
every smooth point together with the infinity transport `inftyOrdTransport_mulByInt`. -/
theorem ordTransport_mulByInt [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    (∀ P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint, OrdTransport (mulByInt W ℓ) P) ∧
      InftyOrdTransport (mulByInt W ℓ) := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  exact ⟨ordTransport_affine_mulByInt ℓ hℓ, inftyOrdTransport_mulByInt ℓ hℓ0 hℓ⟩

/-- **`ProjOrdTransport [ℓ]`** assembled from the affine core and the infinity transport via the
affine/infinity bridge. -/
theorem projOrdTransport_mulByInt [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    ProjOrdTransport (mulByInt W ℓ) :=
  projOrdTransport_of_affine_of_infinity (ordTransport_mulByInt ℓ hℓ).1
    (ordTransport_mulByInt ℓ hℓ).2

/-- **General divisor-pullback functoriality, ready to consume.** If `k : K(E)` has projective
divisor `D`, then `φ.pullback k` has projective divisor the fibre-pullback `φ*(D)`. This is the
shape bilinearity-in-`T` and nondegeneracy use: transport a known divisor through `φ.pullback`. -/
theorem pullback_divisorOf_eq_of_divisorOf_eq {φ : Isogeny W W}
    [Finite φ.toAddMonoidHom.ker] (hcore : ProjOrdTransport φ)
    {k : (⟨W⟩ : SmoothPlaneCurve F).FunctionField}
    {D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)}
    (hk : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf k = D) :
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf (φ.pullback k) =
      pullbackDivisor φ.toAddMonoidHom inferInstance D := by
  rw [projectiveDivisorOf_pullback_eq_pullbackDivisor hcore k, hk]

/-- **Pure-algebra identity (no core needed): `φ*(ℓ(T) − ℓ(O)) = ℓ·(φ*(T) − φ*(O))`.** The
fibre-pullback of the Weil divisor `ℓ·(T) − ℓ·(O)` (Silverman III.8.1, `WeilFunction.weilDivisor`)
equals `ℓ` times the fibre-difference divisor `φ*(T) − φ*(O)` (the divisor of `g_T`,
`Pairing.weilFunction_divisor`). This is the divisor-level form of the III.8.1 relation
`f_T ∘ [ℓ] = g_T^ℓ`: pulling back `div f_T` gives `ℓ · div g_T`. -/
theorem pullbackDivisor_weilDivisor (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (T : W.Point) (ℓ : ℤ) :
    pullbackDivisor f hf (Finsupp.single T.toProjectiveSmoothPoint ℓ -
        Finsupp.single (0 : W.Point).toProjectiveSmoothPoint ℓ) =
      ℓ • (pullbackDiv f hf T - pullbackDiv f hf 0) := by
  rw [← pullbackDivisorHom_apply f hf, map_sub, pullbackDivisorHom_apply,
    pullbackDivisorHom_apply, pullbackDivisor_single, pullbackDivisor_single,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint, smul_sub]

/-- **The III.8.1 divisor identity for `[ℓ]` (core-parametric).** For `T ∈ E[ℓ]`, the function
`φ.pullback (f_T)` — where `f_T` has divisor the Weil divisor `ℓ(T) − ℓ(O)` — has projective
divisor `ℓ·(φ*(T) − φ*(O))`, which is `ℓ · div(g_T)` (Silverman III.8.1, `weilFunction_divisor`).
Hence `φ.pullback f_T` and `g_T^ℓ` have the *same* divisor, so they differ by a constant
(`Constancy`): the relation `f_T ∘ [ℓ] = c · g_T^ℓ` that nondegeneracy consumes.

Parametric on the per-place core `ProjOrdTransport [ℓ]` (`= projOrdTransport_mulByInt`), and on the
finiteness of `ker[ℓ]` (the caller supplies `mulByInt_ker_finite`, keeping this file decoupled from
`Pairing.lean`/`TorsionCardEll`). The conclusion's right side is exactly `ℓ • (div g_T)`. -/
theorem projectiveDivisorOf_pullback_weilFunction (ℓ : ℤ)
    [hker : Finite (mulByInt W ℓ).toAddMonoidHom.ker] (hcore : ProjOrdTransport (mulByInt W ℓ))
    (T : W.Point) {fT : (⟨W⟩ : SmoothPlaneCurve F).FunctionField}
    (hfT : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf fT =
      Finsupp.single T.toProjectiveSmoothPoint ℓ -
        Finsupp.single (0 : W.Point).toProjectiveSmoothPoint ℓ) :
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf ((mulByInt W ℓ).pullback fT) =
      ℓ • (pullbackDiv (mulByInt W ℓ).toAddMonoidHom hker T -
        pullbackDiv (mulByInt W ℓ).toAddMonoidHom hker 0) := by
  rw [pullback_divisorOf_eq_of_divisorOf_eq hcore hfT, pullbackDivisor_weilDivisor]

/-- **Pure-algebra identity for the bilinearity-in-`T` divisor** (no core needed):
`φ*((T₁+T₂) − (T₁) − (T₂) + (O)) = φ*(T₁+T₂) − φ*(T₁) − φ*(T₂) + φ*(O)`. The fibre-pullback of the
degree-`0` Abel–Jacobi divisor `D = (T₁+T₂) − (T₁) − (T₂) + (O)` distributes over the four fibre
sums. This is the divisor-level form of bilinearity in the second slot (Silverman III.8.1b): pulling
back the function `k` with `div k = D` gives `div(g_{T₁+T₂}) − div(g_{T₁}) − div(g_{T₂})`. -/
theorem pullbackDivisor_bilinDivisor (f : W.Point →+ W.Point) (hf : Finite f.ker)
    (T₁ T₂ : W.Point) :
    pullbackDivisor f hf (Finsupp.single (T₁ + T₂).toProjectiveSmoothPoint 1 -
          Finsupp.single T₁.toProjectiveSmoothPoint 1 -
          Finsupp.single T₂.toProjectiveSmoothPoint 1 +
        Finsupp.single (0 : W.Point).toProjectiveSmoothPoint 1) =
      pullbackDiv f hf (T₁ + T₂) - pullbackDiv f hf T₁ - pullbackDiv f hf T₂ +
        pullbackDiv f hf 0 := by
  rw [← pullbackDivisorHom_apply f hf, map_add, map_sub, map_sub, pullbackDivisorHom_apply,
    pullbackDivisorHom_apply, pullbackDivisorHom_apply, pullbackDivisorHom_apply,
    pullbackDivisor_single, pullbackDivisor_single, pullbackDivisor_single,
    pullbackDivisor_single, one_smul, one_smul, one_smul, one_smul,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint]

/-- **The bilinearity-in-`T` divisor identity for `[ℓ]` (core-parametric).** For a function `k` with
divisor the Abel–Jacobi divisor `D = (T₁+T₂) − (T₁) − (T₂) + (O)`, the pulled-back function
`[ℓ].pullback k` has projective divisor `φ*(T₁+T₂) − φ*(T₁) − φ*(T₂) + φ*(O)` — which is exactly
`div(g_{T₁+T₂}) − div(g_{T₁}) − div(g_{T₂})` (each `div(g_T) = φ*(T) − φ*(O)`, the cancelling
`φ*(O)` terms collapsing). This is the divisor identity behind bilinearity in the second slot
(Silverman III.8.1b): `g_{T₁+T₂}` and `g_{T₁}·g_{T₂}·([ℓ].pullback k)` have the *same* divisor, so
they differ by a constant.

Parametric on the per-place core `ProjOrdTransport [ℓ]` (`= projOrdTransport_mulByInt`) and the
finiteness of `ker[ℓ]` (caller-supplied, decoupling this file from `Pairing.lean`). -/
theorem projectiveDivisorOf_pullback_bilinFunction (ℓ : ℤ)
    [hker : Finite (mulByInt W ℓ).toAddMonoidHom.ker] (hcore : ProjOrdTransport (mulByInt W ℓ))
    (T₁ T₂ : W.Point) {k : (⟨W⟩ : SmoothPlaneCurve F).FunctionField}
    (hk : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf k =
      Finsupp.single (T₁ + T₂).toProjectiveSmoothPoint 1 -
          Finsupp.single T₁.toProjectiveSmoothPoint 1 -
          Finsupp.single T₂.toProjectiveSmoothPoint 1 +
        Finsupp.single (0 : W.Point).toProjectiveSmoothPoint 1) :
    (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf ((mulByInt W ℓ).pullback k) =
      pullbackDiv (mulByInt W ℓ).toAddMonoidHom hker (T₁ + T₂) -
          pullbackDiv (mulByInt W ℓ).toAddMonoidHom hker T₁ -
          pullbackDiv (mulByInt W ℓ).toAddMonoidHom hker T₂ +
        pullbackDiv (mulByInt W ℓ).toAddMonoidHom hker 0 := by
  rw [pullback_divisorOf_eq_of_divisorOf_eq hcore hk, pullbackDivisor_bilinDivisor]

end HasseWeil.WeilPairing.DivisorPullback
