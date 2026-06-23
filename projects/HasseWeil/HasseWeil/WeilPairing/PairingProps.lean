/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.DivisorPullback
import HasseWeil.WeilPairing.Pairing

/-!
# Weil-pairing properties: bilinearity in the second slot and alternating (Silverman III.8.1)

This file proves the two remaining structural properties of the finite-level Weil pairing
`e_ℓ : E[ℓ] × E[ℓ] → F` (ticket `T-R2-PAIRING-PROPS`), over an algebraically closed field `F`,
extending the slot-1 bilinearity `weilPairing_mul_left` from `Pairing.lean`:

* `weilPairing_mul_right` — **bilinearity in the second slot** (Silverman III.8.1b):
  `e_ℓ(S, T₁ + T₂) = e_ℓ(S, T₁) · e_ℓ(S, T₂)`.
* `weilPairing_self` / `weilPairing_alternating` — **alternating** (Silverman III.8.1d):
  `e_ℓ(T, T) = 1`, whence antisymmetry `e_ℓ(S, T) · e_ℓ(T, S) = 1`.

## The construction (Silverman III.8.1b)

Unlike slot-1 bilinearity — where all three relations `τ_{Sᵢ} g_T = e_ℓ(Sᵢ, T)·g_T` use the *same*
Weil function `g_T` and the multiplicativity is `pairing_const_mul` — slot-2 bilinearity relates the
*different* functions `g_{T₁}`, `g_{T₂}`, `g_{T₁+T₂}` via the **divisor-pullback functoriality**.

The Abel–Jacobi divisor `D := (T₁+T₂) − (T₁) − (T₂) + (O)` is principal (degree `0`, group-sum `O`),
say `D = div(k)`. Pulling back, `div([ℓ]^* k) = [ℓ]^*(D) = [ℓ]^*(T₁+T₂) − [ℓ]^*(T₁) − [ℓ]^*(T₂) +
[ℓ]^*(O)` (`DivisorPullback.projectiveDivisorOf_pullback_bilinFunction`). Combined with
`div(g_T) = [ℓ]^*(T) − [ℓ]^*(O)` (`weilFunction_divisor`), this gives

```
div(g_{T₁} · g_{T₂} · [ℓ]^* k) = [ℓ]^*(T₁+T₂) − [ℓ]^*(O) = div(g_{T₁+T₂}),
```

so `g_{T₁+T₂} = c · g_{T₁} · g_{T₂} · [ℓ]^* k` for a constant `c ∈ F^×`
(`const_unit_of_projectiveDivisorOf_eq_zero`). Applying `τ_S` (`S ∈ E[ℓ]`), which fixes `c` and the
covariant factor `[ℓ]^* k` (`hcov_mulByInt_of_xy`), the value-multiplicativity engine
`pairing_const_mul_invariant_factor` yields `e_ℓ(S, T₁+T₂) = e_ℓ(S, T₁) · e_ℓ(S, T₂)`.

## The construction (Silverman III.8.1d)

`e_ℓ(T, T) = 1` is the standard telescoping/translation argument, but here we use the slick route
available once both-slot bilinearity is in hand: bilinearity in slot 2 plus the root-of-unity
core `weilPairing_pow_eq_one` reduce `e_ℓ(T, T)` to a power that collapses.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Prop 8.1b, 8.1d).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric HasseWeil.WeilPairing.DivisorPullback

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

section Bilinearity

variable [IsAlgClosed F]

omit [IsAlgClosed F] in
/-- **The Abel–Jacobi divisor `D = (T₁+T₂) − (T₁) − (T₂) + (O)` is principal.** Degree `0`
(`1 − 1 − 1 + 1`) and group-sum `(T₁+T₂) − T₁ − T₂ + O = O`, hence principal by Abel–Jacobi
(`projIsPrincipal_of_degZero_of_sigma_eq_zero`). This is the function `k` relating the three Weil
functions `g_{T₁}, g_{T₂}, g_{T₁+T₂}` in slot-2 bilinearity. -/
theorem bilinDivisor_isPrincipal (T₁ T₂ : W.toAffine.Point) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
      (Finsupp.single (T₁ + T₂).toProjectiveSmoothPoint 1 -
          Finsupp.single T₁.toProjectiveSmoothPoint 1 -
          Finsupp.single T₂.toProjectiveSmoothPoint 1 +
        Finsupp.single (0 : W.toAffine.Point).toProjectiveSmoothPoint 1) := by
  refine projIsPrincipal_of_degZero_of_sigma_eq_zero _ ?_ ?_
  · rw [← Curves.ProjectiveDivisor.degreeHom_apply, map_add, map_sub, map_sub]
    simp only [Curves.ProjectiveDivisor.degreeHom_apply, degree_single]
    ring
  · simp only [Curves.projectiveDivisorSum_add, Curves.projectiveDivisorSum_sub,
      Curves.projectiveDivisorSum_single, Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
      one_zsmul, smul_zero]
    abel

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] [IsAlgClosed F] in
/-- **The covariance of the pullback factor**: for `S ∈ E[ℓ]`, the translation `τ_S` fixes any
function in the image of `[ℓ].pullback`. This is `hcov_mulByInt_of_xy` (the function-field shadow of
`[ℓ] ∘ (·+S) = [ℓ]`, via the division-function invariance `hxy_mulByInt`). -/
theorem translate_pullback_fixed (ℓ : ℤ) (hℓ0 : ℓ ≠ 0) (S : W.toAffine.Point) (hS : ℓ • S = 0)
    (z : KE) :
    translateAlgEquivOfPoint W S ((mulByInt W.toAffine ℓ).pullback z) =
      (mulByInt W.toAffine ℓ).pullback z := by
  have hSker : S ∈ (mulByInt W.toAffine ℓ).kernel := by
    rwa [HasseWeil.Isogeny.mem_kernel_iff, mulByInt_apply]
  exact hcov_mulByInt_of_xy W ℓ hℓ0 (hxy_mulByInt W ℓ hℓ0) ⟨S, hSker⟩ z

/-- **Bilinearity of the Weil pairing in the second slot** (Silverman III.8.1b):
`e_ℓ(S, T₁ + T₂) = e_ℓ(S, T₁) · e_ℓ(S, T₂)`.

The three Weil functions `g_{T₁}, g_{T₂}, g_{T₁+T₂}` are related by the divisor-pullback
functoriality: the Abel–Jacobi divisor `(T₁+T₂) − (T₁) − (T₂) + (O) = div(k)` pulls back so that
`g_{T₁+T₂}` and `g_{T₁}·g_{T₂}·([ℓ]^*k)` have the same divisor, hence differ by a constant
`c ∈ F^×`. Applying `τ_S` — which fixes `c` and the covariant factor `[ℓ]^*k`
(`translate_pullback_fixed`) — the value-multiplicativity engine
`pairing_const_mul_invariant_factor` collapses to `e_ℓ(S, T₁+T₂) = e_ℓ(S, T₁)·e_ℓ(S, T₂)`. -/
theorem weilPairing_mul_right (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T₁ T₂ : W.toAffine.Point) (hS : ℓ • S = 0) (hT₁ : ℓ • T₁ = 0) (hT₂ : ℓ • T₂ = 0)
    (h₁₂ : ℓ • (T₁ + T₂) = 0) :
    weilPairing W ℓ hℓ S (T₁ + T₂) hS h₁₂ =
      weilPairing W ℓ hℓ S T₁ hS hT₁ * weilPairing W ℓ hℓ S T₂ hS hT₂ := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  haveI hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker := mulByInt_ker_finite W ℓ hℓ
  obtain ⟨k, hk_ne, hk_div⟩ := bilinDivisor_isPrincipal W T₁ T₂
  set u : KE := (mulByInt W.toAffine ℓ).pullback k
  have hu_ne : u ≠ 0 :=
    fun h0 ↦ hk_ne ((mulByInt W.toAffine ℓ).pullback_injective (h0.trans (map_zero _).symm))
  have hu_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf u =
      pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker (T₁ + T₂) -
          pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker T₁ -
          pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker T₂ +
        pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0 :=
    projectiveDivisorOf_pullback_bilinFunction (W := W.toAffine) ℓ
      (projOrdTransport_mulByInt ℓ hℓ) T₁ T₂ hk_div
  set g₁ := weilFunction W ℓ hℓ T₁ hT₁
  set g₂ := weilFunction W ℓ hℓ T₂ hT₂
  set g₁₂ := weilFunction W ℓ hℓ (T₁ + T₂) h₁₂
  have hg₁_ne : g₁ ≠ 0 := weilFunction_ne_zero W ℓ hℓ T₁ hT₁
  have hg₂_ne : g₂ ≠ 0 := weilFunction_ne_zero W ℓ hℓ T₂ hT₂
  have hg₁₂_ne : g₁₂ ≠ 0 := weilFunction_ne_zero W ℓ hℓ (T₁ + T₂) h₁₂
  have hg₁_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf g₁ =
      pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker T₁ -
        pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0 :=
    weilFunction_divisor W ℓ hℓ T₁ hT₁
  have hg₂_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf g₂ =
      pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker T₂ -
        pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0 :=
    weilFunction_divisor W ℓ hℓ T₂ hT₂
  have hg₁₂_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf g₁₂ =
      pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker (T₁ + T₂) -
        pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0 :=
    weilFunction_divisor W ℓ hℓ (T₁ + T₂) h₁₂
  have hprod_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (g₁ * g₂ * u) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf g₁₂ := by
    rw [(⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul
        (mul_ne_zero hg₁_ne hg₂_ne) hu_ne,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hg₁_ne hg₂_ne,
      hg₁_div, hg₂_div, hu_div, hg₁₂_div]
    abel
  have hquot_ne : g₁₂ / (g₁ * g₂ * u) ≠ 0 :=
    div_ne_zero hg₁₂_ne (mul_ne_zero (mul_ne_zero hg₁_ne hg₂_ne) hu_ne)
  have hquot_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
      (g₁₂ / (g₁ * g₂ * u)) = 0 := by
    rw [div_eq_mul_inv, (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hg₁₂_ne
        (inv_ne_zero (mul_ne_zero (mul_ne_zero hg₁_ne hg₂_ne) hu_ne)),
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_inv
        (mul_ne_zero (mul_ne_zero hg₁_ne hg₂_ne) hu_ne), hprod_div]
    abel
  obtain ⟨c, _, hc⟩ :=
    const_unit_of_projectiveDivisorOf_eq_zero (W := W.toAffine) (g₁₂ / (g₁ * g₂ * u))
      hquot_ne hquot_div
  have hfact : g₁₂ = algebraMap F KE c * (g₁ * g₂ * u) :=
    (div_eq_iff (mul_ne_zero (mul_ne_zero hg₁_ne hg₂_ne) hu_ne)).mp hc
  refine pairing_const_mul_invariant_factor (W := W.toAffine)
    (τ := (translateAlgEquivOfPoint W S).toRingEquiv) g₁ g₂ g₁₂ u hg₁₂_ne
    (hτF := fun a ↦ (translateAlgEquivOfPoint W S).commutes a)
    (hτu := translate_pullback_fixed W ℓ hℓ0 S hS k)
    (hfact := hfact)
    (hc₁ := weilPairing_translate W ℓ hℓ S T₁ hS hT₁)
    (hc₂ := weilPairing_translate W ℓ hℓ S T₂ hS hT₂)
    (hc₁₂ := weilPairing_translate W ℓ hℓ S (T₁ + T₂) hS h₁₂)

end Bilinearity

section Alternating

variable [IsAlgClosed F]

omit [DecidableEq F] [W.toAffine.IsElliptic]
    [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] [IsAlgClosed F] in
/-- **The projective divisor of a finite product** (over `Finset.range n`) of nonzero functions is
the sum of the divisors. Pure `projectiveDivisorOf_mul` induction (each factor nonzero). -/
theorem projectiveDivisorOf_prod_range (n : ℕ) (h : ℕ → KE) (hh : ∀ i ∈ Finset.range n, h i ≠ 0) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (∏ i ∈ Finset.range n, h i) =
      ∑ i ∈ Finset.range n, (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (h i) := by
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, Finset.sum_range_zero,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_one]
  | succ k ih =>
    have hk_ne : ∀ i ∈ Finset.range k, h i ≠ 0 := fun i hi ↦
      hh i (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self k)))
    have hprod_ne : (∏ i ∈ Finset.range k, h i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hk_ne
    have hlast_ne : h k ≠ 0 := hh k (Finset.mem_range.mpr (Nat.lt_succ_self k))
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hprod_ne hlast_ne, ih hk_ne]

/-- **`ℓ`-torsion product is nonzero**: each factor `τ_{[i]P₀} g_T` is nonzero (translation is a
ring automorphism, `g_T ≠ 0`). -/
theorem weilFunction_translate_prod_ne_zero (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T P₀ : W.toAffine.Point)
    (hT : ℓ • T = 0) (n : ℕ) :
    (∏ i ∈ Finset.range n, translateAlgEquivOfPoint W ((i : ℕ) • P₀) (weilFunction W ℓ hℓ T hT))
      ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
    (map_ne_zero_iff _ (translateAlgEquivOfPoint W ((i : ℕ) • P₀)).injective).mpr
      (weilFunction_ne_zero W ℓ hℓ T hT)

/-- **The divisor of a translated Weil function** (`g_T`-translation law). For any point `S`,
`div(τ_S g_T) = [ℓ]^*(T − ℓ•S) − [ℓ]^*(−ℓ•S)`: translating the fibre-difference divisor of `g_T` by
`S` shifts both fibres by `−ℓ•S` (`equivMapDomain_placeTranslate_pullbackDiv`, the general law). -/
theorem weilFunction_translate_div (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point)
    (hT : ℓ • T = 0) (S : W.toAffine.Point) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT)) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (T - ℓ • S) -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (0 - ℓ • S) := by
  -- `⟨W.toAffine⟩` is opaque to `rw`, so the two structural facts are introduced via `:=`.
  have htr : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT)) =
      Finsupp.equivMapDomain (placeTranslate W S).symm
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (weilFunction W ℓ hℓ T hT)) :=
    HasseWeil.projectiveDivisorOf_translate W S (weilFunction W ℓ hℓ T hT)
  have hdiv : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (weilFunction W ℓ hℓ T hT) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) T -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) 0 :=
    weilFunction_divisor W ℓ hℓ T hT
  rw [htr, hdiv]
  have hfS : (mulByInt W.toAffine ℓ).toAddMonoidHom S = ℓ • S := by rw [mulByInt_apply]
  refine Finsupp.ext fun w ↦ ?_
  change (pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) T -
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) 0) (placeTranslate W S w) =
    (pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) (T - ℓ • S) -
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) (0 - ℓ • S)) w
  rw [Finsupp.sub_apply, Finsupp.sub_apply,
    HasseWeil.pullbackDiv_placeTranslate_apply_general W S
      (mulByInt W.toAffine ℓ).toAddMonoidHom (mulByInt_ker_finite W ℓ hℓ) T w,
    HasseWeil.pullbackDiv_placeTranslate_apply_general W S
      (mulByInt W.toAffine ℓ).toAddMonoidHom (mulByInt_ker_finite W ℓ hℓ) 0 w, hfS]

/-- **Alternating: `e_ℓ(T, T) = 1`** (Silverman III.8.1d). The telescoping argument:
`g = ∏_{i<ℓ} τ_{[i]P₀} g_T` is a nonzero constant (its divisor telescopes to `0`), and
`τ_{P₀} g = e_ℓ(T,T)·g` (reindexing), so `e_ℓ(T,T) = 1`. -/
theorem weilPairing_self (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    weilPairing W ℓ hℓ T T hT hT = 1 := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  set n := ℓ.natAbs with hn
  have hnT : (n : ℕ) • T = 0 := by
    have hz : ((n : ℤ)) • T = 0 := by
      rcases Int.natAbs_eq ℓ with h | h
      · rw [← h]; exact hT
      · rw [show ((n : ℤ)) = -ℓ by lia, neg_smul, hT, neg_zero]
    rwa [natCast_zsmul] at hz
  obtain ⟨P₀, hP₀_eq, _⟩ := exists_preimage_of_torsion W ℓ hℓ T hT
  set g_T := weilFunction W ℓ hℓ T hT with hg_T
  set g := ∏ i ∈ Finset.range n, translateAlgEquivOfPoint W ((i : ℕ) • P₀) g_T with hg_def
  have hg_ne : g ≠ 0 := weilFunction_translate_prod_ne_zero W ℓ hℓ T P₀ hT n
  have hfiP₀ : ∀ i : ℕ, ℓ • ((i : ℕ) • P₀) = (i : ℕ) • T := by
    intro i; rw [smul_comm, hP₀_eq]
  -- the telescoping sequence `gₛ(i) = [ℓ]^*((1−i)•T)`
  let gs : ℕ → ProjectiveDivisor (⟨W.toAffine⟩ : SmoothPlaneCurve F) := fun i ↦
    pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
      (mulByInt_ker_finite W ℓ hℓ) (((1 : ℤ) - (i : ℤ)) • T)
  have hpt0 : ((1 : ℤ) - ((0 : ℕ) : ℤ)) • T = T := by norm_num
  have hptn : ((1 : ℤ) - ((n : ℕ) : ℤ)) • T = T := by
    rw [sub_smul, one_smul, natCast_zsmul, hnT, sub_zero]
  have hptnum : ∀ i : ℕ, T - (i : ℕ) • T = ((1 : ℤ) - (i : ℤ)) • T := fun i ↦ by
    rw [sub_smul, one_smul, natCast_zsmul]
  have hptden : ∀ i : ℕ, (0 : W.toAffine.Point) - (i : ℕ) • T = ((1 : ℤ) - ((i : ℤ) + 1)) • T :=
    fun i ↦ by
      rw [zero_sub, show ((1 : ℤ) - ((i : ℤ) + 1)) = -(i : ℤ) by ring, neg_smul, natCast_zsmul]
  have hg_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf g = 0 := by
    rw [hg_def, projectiveDivisorOf_prod_range W n _
      (fun i _ ↦ (map_ne_zero_iff _ (translateAlgEquivOfPoint W ((i : ℕ) • P₀)).injective).mpr
        (weilFunction_ne_zero W ℓ hℓ T hT))]
    have hterm : ∀ i ∈ Finset.range n,
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
          (translateAlgEquivOfPoint W ((i : ℕ) • P₀) g_T) = gs i - gs (i + 1) := by
      intro i _
      change _ = pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (((1 : ℤ) - (i : ℤ)) • T) -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (((1 : ℤ) - ((i : ℤ) + 1)) • T)
      rw [hg_T, weilFunction_translate_div W ℓ hℓ T hT ((i : ℕ) • P₀), hfiP₀, hptnum i, hptden i]
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' gs n]
    change pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (((1 : ℤ) - ((0 : ℕ) : ℤ)) • T) -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (((1 : ℤ) - ((n : ℕ) : ℤ)) • T) = 0
    rw [hpt0, hptn, sub_self]
  obtain ⟨a, ha⟩ := const_of_projectiveDivisorOf_eq_zero (W := W.toAffine) g hg_ne hg_div
  have hnP₀_tor : ℓ • ((n : ℕ) • P₀) = 0 := by rw [hfiP₀, hnT]
  have hstep : ∀ i : ℕ,
      translateAlgEquivOfPoint W P₀ (translateAlgEquivOfPoint W ((i : ℕ) • P₀) g_T) =
      translateAlgEquivOfPoint W (((i : ℕ) + 1) • P₀) g_T := by
    intro i
    rw [← translateAlgEquivOfPoint_add_apply W ((i : ℕ) • P₀) P₀ g_T, succ_nsmul]
  have hτP₀g : translateAlgEquivOfPoint W P₀ g =
      algebraMap F KE (weilPairing W ℓ hℓ ((n : ℕ) • P₀) T hnP₀_tor hT) * g := by
    let Fseq : ℕ → KE := fun i ↦ translateAlgEquivOfPoint W ((i : ℕ) • P₀) g_T
    have hg_eq : g = ∏ i ∈ Finset.range n, Fseq i := hg_def
    have hτg : translateAlgEquivOfPoint W P₀ g = ∏ i ∈ Finset.range n, Fseq (i + 1) := by
      rw [hg_eq, map_prod]
      exact Finset.prod_congr rfl (fun i _ ↦ hstep i)
    have hbdry : (∏ i ∈ Finset.range n, Fseq (i + 1)) * Fseq 0 =
        (∏ i ∈ Finset.range n, Fseq i) * Fseq n := by
      rw [← Finset.prod_range_succ' Fseq n, ← Finset.prod_range_succ Fseq n]
    have hF0 : Fseq 0 = g_T := by
      change translateAlgEquivOfPoint W ((0 : ℕ) • P₀) g_T = g_T
      rw [zero_nsmul]
      rfl
    have hFn : Fseq n =
        algebraMap F KE (weilPairing W ℓ hℓ ((n : ℕ) • P₀) T hnP₀_tor hT) * g_T := by
      change translateAlgEquivOfPoint W ((n : ℕ) • P₀) g_T = _
      rw [hg_T]
      exact weilPairing_translate W ℓ hℓ ((n : ℕ) • P₀) T hnP₀_tor hT
    have hgT_ne : g_T ≠ 0 := weilFunction_ne_zero W ℓ hℓ T hT
    have hbdry' : (∏ i ∈ Finset.range n, Fseq (i + 1)) * g_T =
        g * (algebraMap F KE (weilPairing W ℓ hℓ ((n : ℕ) • P₀) T hnP₀_tor hT) * g_T) :=
      calc (∏ i ∈ Finset.range n, Fseq (i + 1)) * g_T
          = (∏ i ∈ Finset.range n, Fseq (i + 1)) * Fseq 0 := by rw [hF0]
        _ = (∏ i ∈ Finset.range n, Fseq i) * Fseq n := hbdry
        _ = g * (algebraMap F KE (weilPairing W ℓ hℓ ((n : ℕ) • P₀) T hnP₀_tor hT) * g_T) := by
            rw [← hg_eq, hFn]
    rw [hτg]
    refine mul_right_cancel₀ hgT_ne ?_
    rw [hbdry']; ring
  have hτP₀g_eq : translateAlgEquivOfPoint W P₀ g = g := by
    rw [ha, (translateAlgEquivOfPoint W P₀).commutes]
  rw [hτP₀g_eq] at hτP₀g
  have hkey : weilPairing W ℓ hℓ ((n : ℕ) • P₀) T hnP₀_tor hT = 1 :=
    pairing_const_refl (W := W.toAffine) g hg_ne hτP₀g
  rcases Int.natAbs_eq ℓ with hsgn | hsgn
  · have hnP₀T : (n : ℕ) • P₀ = T := by rw [← natCast_zsmul, hn, ← hsgn, hP₀_eq]
    rwa [weilPairing_congr_left W ℓ hℓ hnP₀_tor hT hT hnP₀T] at hkey
  · have hnP₀negT : (n : ℕ) • P₀ = -T := by
      rw [← natCast_zsmul, hn, show ((ℓ.natAbs : ℤ)) = -ℓ by lia, neg_smul, hP₀_eq]
    have hnegTtor : ℓ • (-T) = 0 := by rw [smul_neg, hT, neg_zero]
    rw [weilPairing_congr_left W ℓ hℓ hnP₀_tor hnegTtor hT hnP₀negT] at hkey
    have hsum : ℓ • (-T + T) = 0 := by rw [neg_add_cancel, smul_zero]
    have hmul := weilPairing_mul_left W ℓ hℓ (-T) T T hnegTtor hT hT hsum
    rw [weilPairing_congr_left W ℓ hℓ hsum (by simp : ℓ • (0 : W.toAffine.Point) = 0) hT
        (neg_add_cancel T), weilPairing_refl_left W ℓ hℓ T hT _, hkey, one_mul] at hmul
    exact hmul.symm

/-- **Alternating** (alias of `weilPairing_self`, Silverman III.8.1d): `e_ℓ(T, T) = 1`. -/
theorem weilPairing_alternating (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    weilPairing W ℓ hℓ T T hT hT = 1 :=
  weilPairing_self W ℓ hℓ T hT

/-- **Antisymmetry** (Silverman III.8.1c): `e_ℓ(S, T) · e_ℓ(T, S) = 1`. From alternating applied to
`S + T` and bilinearity in both slots: `1 = e_ℓ(S+T, S+T) = e_ℓ(S,S)·e_ℓ(S,T)·e_ℓ(T,S)·e_ℓ(T,T) =
e_ℓ(S,T)·e_ℓ(T,S)` (the diagonal terms `e_ℓ(S,S) = e_ℓ(T,T) = 1`). -/
theorem weilPairing_antisymm (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (S T : W.toAffine.Point)
    (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    weilPairing W ℓ hℓ S T hS hT * weilPairing W ℓ hℓ T S hT hS = 1 := by
  have hST : ℓ • (S + T) = 0 := by rw [smul_add, hS, hT, add_zero]
  have h1 : (1 : F) = weilPairing W ℓ hℓ (S + T) (S + T) hST hST :=
    (weilPairing_self W ℓ hℓ (S + T) hST).symm
  rw [weilPairing_mul_right W ℓ hℓ (S + T) S T hST hS hT,
    weilPairing_mul_left W ℓ hℓ S T S hS hT hS hST,
    weilPairing_mul_left W ℓ hℓ S T T hS hT hT hST,
    weilPairing_self W ℓ hℓ S hS, weilPairing_self W ℓ hℓ T hT] at h1
  rw [one_mul, mul_one] at h1
  rw [mul_comm]
  exact h1.symm

end Alternating

end HasseWeil.WeilPairing
