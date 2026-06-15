/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.DetDeg
import HasseWeil.WeilPairing.HfactLemma
import HasseWeil.WeilPairing.PicDualDivisorClassLemma

/-!
# CoordHom-free Weil-pairing scaling for separable genuine isogenies (Silverman III.8.2/8.6.1)

This file builds the Weil-pairing **scaling** `e_ℓ(φS, φT) = e_ℓ(S, T) ^ (deg φ)` for separable
isogenies `φ` **without** ever requiring a coordinate-ring restriction `ch : φ.CoordHom`.

## Why a CoordHom-free route is needed

The shipped scaling `weilPairing_scaling` (`PairingAdjoint.lean`) and the adjoint
`weilPairing_adjoint_of_naturality` (`PicDualDivisorClassLemma.lean`) both name the dual point
through `φ.picDual ch hinj hfin`, which is defined as `classTransport (classMap ch …)` and therefore
**requires a `CoordHom`** — an `F`-algebra hom `R → R` (`R := E.CoordinateRing`) restricting
`φ.pullback`. For the **separable** isogenies `1 − π` and `rπ − s` over `𝔽_q`, `(1 − π).pullback x`
has *poles at the affine kernel* `E(𝔽_q) = Fix(π)`, so `(1 − π).pullback x ∉ image(R)` and **no
`CoordHom` exists** (recorded in `GapSpines.lean`). Those theorems are thus *vacuously* parametric
for these `φ`.

## The CoordHom-free observation

The genuinely geometric lemma `weilPairing_adjoint_core` (`PairingAdjoint.lean`) takes the dual
point `U` **abstractly** (not as `picDual φ T`): it proves `e_ℓ(φS, T) = e_ℓ(S, U)` from
* `hcomm` — the translation covariance `τ_S^*(φ^* g_T) = φ^*(τ_{φS}^* g_T)`, and
* `hfact` — the divisor factorisation `φ^* g_T = c · g_U · ([ℓ]^* k)`.

Likewise the `hfact`-producing divisor computation `hfact_projectiveDivisorOf_eq`
(`HfactLemma.lean`) takes `U` abstractly, and the Abel discharge
`picDualDivisorClass_of_picDualComp` (`PicDualDivisorClassLemma.lean`) uses `picDual φ` *only*
through the **dual relation**
`(picDual φ) ∘ φ = [#ker φ]` — a pure point-map identity.

So the dual can be supplied as **any** point endomorphism `δ : E.Point →+ E.Point` satisfying the
dual relation `δ ∘ φ = [#ker φ]` (e.g. the Verschiebung `V` for `φ = π`, or `rV − s` for
`φ = rπ − s`). The whole adjoint/scaling chain then goes through with `δ` in place of `picDual φ`,
**entirely CoordHom-free**, the dual relation being the one carried datum (Silverman III.6.2(a), the
divisor *pushforward* dual — which genuine separable isogenies possess).

## What this file builds

The CoordHom-free analogues, mirroring the `picDual`-keyed chain but parametric on an abstract `δ`:

* `pullbackDivisorClass_of_dualComp` — Silverman III.6.1b in projective-divisor form, for an
  abstract `δ`: `pullbackDivisor φ ((T) − (O)) ∼ (δ T) − (O)`, from `δ ∘ φ = [#ker φ]` (Abel
  σ-machinery, char-free). *No CoordHom.* (Mirror of `picDualDivisorClass_of_picDualComp`.)
* `hfact_of_dualComp` — the divisor factorisation `φ^* g_T = c · g_{δT} · ([ℓ]^* k)`. *No CoordHom.*
  (Mirror of `hfact_of_picDualDivisorClass`.)
* `weilPairing_adjoint_of_dualComp` — the separable adjoint `e_ℓ(φS, T) = e_ℓ(S, δT)`. No CoordHom.
* `pullbackDivisorClass_of_dualComp_image` / `hfact_of_dualComp_image` /
  `weilPairing_adjoint_of_dualComp_image` — the **image-restricted** variants taking an *explicit
  preimage* `P₀` of `T` instead of surjectivity (`hsurj`).  These are what the scaling uses (at the
  image `φT`, preimage `T`), so the scaling needs **no point-map surjectivity**
  (reviewer round-20 Q2).
* `weilPairing_scaling_of_dualComp` — the scaling `e_ℓ(φS, φT) = e_ℓ(S, T) ^ (deg φ)`, from the
  *image-restricted* adjoint at `φT` (preimage `T`) + the dual relation `δ ∘ φ = [#ker φ]` + the
  separable degree match `#ker φ = deg φ`.  *No CoordHom, no surjectivity.*  This is the corollary
  the genuine `1 − π` / `rπ − s` leaves want.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.1(b) (`φ̂ = κ⁻¹ ∘ φ^* ∘ κ`),
  III.6.2(a) (`φ̂ ∘ φ = [deg φ]`), III.8.2 (the separable adjoint via the multiplicity-free
  pullback), III.8.6 (`det φ_ℓ = deg φ` via the scaling).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

/-- **The σ-point-identity for an abstract dual `δ`** (Silverman III.6.1b/III.6.2(a),
CoordHom-free). From the σ-bridge `σ(φ^*((T) − (O))) = #ker(φ) · P₀`
(`sigma_pullbackDivisor_kappaDivisor`) and the
dual relation `hdc : δ ∘ φ = [#ker φ]` at a preimage `P₀` (`φ P₀ = T`):
`σ(φ^*((T) − (O))) = δ T`, because `δ T = δ(φ P₀) = #ker(φ) · P₀`. -/
theorem sigma_pullbackDivisor_kappaDivisor_eq_dual
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    {T P₀ : W.toAffine.Point} (hP₀ : φ.toAddMonoidHom P₀ = T) :
    Curves.projectiveDivisorSum W.toAffine
        (pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance
          (Curves.kappaDivisor W.toAffine T)) =
      δ T := by
  rw [sigma_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance hP₀]
  have hval := DFunLike.congr_fun hdc P₀
  rw [AddMonoidHom.comp_apply, hP₀, mulByInt_apply] at hval
  rw [hval, natCast_zsmul]

/-- **Projective divisor-class identity for an abstract dual `δ`** (Silverman III.6.1b,
CoordHom-free). For an isogeny `φ` with finite kernel, an abstract point endomorphism `δ` with the
dual relation `hdc : δ ∘ φ = [#ker φ]` (Silverman III.6.2(a)), and surjectivity of `φ` on points
`hsurj` (automatic over `K̄`, Silverman III.4.10a), the fibre-pullback divisor `φ^*((T) − (O))` is
linearly equivalent to `(δ T) − (O)`:
```
(⟨W⟩).ProjIsPrincipal (pullbackDivisor φ ((T) − (O)) − ((δ T) − (O)))   for every T.
```

This is `picDualDivisorClass_of_picDualComp` with `δ` in place of `picDual φ` — **no `CoordHom`**.
The difference `Δ_T` has degree `0` and `σ Δ_T = δ T − δ T = 0`, so Abel
(`projIsPrincipal_of_degZero_of_sigma_eq_zero`, char-free) makes it principal. -/
theorem pullbackDivisorClass_of_dualComp
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hsurj : Function.Surjective φ.toAddMonoidHom) (T : W.toAffine.Point) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
      (pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance
          (Curves.kappaDivisor W.toAffine T) -
        Curves.kappaDivisor W.toAffine (δ T)) := by
  obtain ⟨P₀, hP₀⟩ := hsurj T
  refine projIsPrincipal_of_degZero_of_sigma_eq_zero (W := W.toAffine) _ ?_ ?_
  · rw [← Curves.ProjectiveDivisor.degreeHom_apply, map_sub,
      Curves.ProjectiveDivisor.degreeHom_apply, Curves.ProjectiveDivisor.degreeHom_apply,
      degree_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance hP₀,
      Curves.kappaDivisor_degree, sub_self]
  · rw [Curves.projectiveDivisorSum_sub,
      sigma_pullbackDivisor_kappaDivisor_eq_dual W φ δ hdc hP₀,
      Curves.projectiveDivisorSum_kappaDivisor, sub_self]

/-- **Image-restricted projective divisor-class identity for an abstract dual `δ`** (Silverman
III.6.1b, CoordHom-free, **no surjectivity**). The same statement as
`pullbackDivisorClass_of_dualComp` but with an *explicit preimage* `P₀` of `T` supplied directly
(`hP₀ : φ P₀ = T`) instead of obtaining one from surjectivity. This is the version the scaling uses
at `T = φ T'`, where the preimage is `T'` itself (`φ T' = φ T'`, `rfl`) — so the symplectic scaling
needs **no** point-map surjectivity.

The proof is identical to `pullbackDivisorClass_of_dualComp` (degree `0` and `σ = 0` via Abel), but
takes `P₀`/`hP₀` as hypotheses rather than `obtain`ing them from `hsurj`. -/
theorem pullbackDivisorClass_of_dualComp_image
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    {T P₀ : W.toAffine.Point} (hP₀ : φ.toAddMonoidHom P₀ = T) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
      (pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance
          (Curves.kappaDivisor W.toAffine T) -
        Curves.kappaDivisor W.toAffine (δ T)) := by
  refine projIsPrincipal_of_degZero_of_sigma_eq_zero (W := W.toAffine) _ ?_ ?_
  · rw [← Curves.ProjectiveDivisor.degreeHom_apply, map_sub,
      Curves.ProjectiveDivisor.degreeHom_apply, Curves.ProjectiveDivisor.degreeHom_apply,
      degree_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance hP₀,
      Curves.kappaDivisor_degree, sub_self]
  · rw [Curves.projectiveDivisorSum_sub,
      sigma_pullbackDivisor_kappaDivisor_eq_dual W φ δ hdc hP₀,
      Curves.projectiveDivisorSum_kappaDivisor, sub_self]

variable [IsAlgClosed F]

/-- **The separable divisor factorisation `hfact` for an abstract dual `δ`** (Silverman III.8.2,
CoordHom-free). For a separable isogeny `φ` with the divisor-pullback functoriality
`hφ : ProjOrdTransport φ`, the commutation `[ℓ] ∘ φ = φ ∘ [ℓ]` (`hcomm`, automatic), an abstract
dual `δ` with the dual relation `δ ∘ φ = [#ker φ]` (`hdc`) and surjectivity of `φ` (`hsurj`), there
exist `c ∈ Fˣ` and `k ∈ K(E)` with
```
φ^* g_T = c · (g_{δT} · ([ℓ]^* k)).
```
This is exactly the `hfact` hypothesis of `weilPairing_adjoint_core`, with `U := δ T` — **no
`CoordHom`**. -/
theorem hfact_of_dualComp (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcomm : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hsurj : Function.Surjective φ.toAddMonoidHom)
    (T : W.toAffine.Point) (hT : ℓ • T = 0) (hU : ℓ • δ T = 0) :
    ∃ (c : F) (k : KE), c ≠ 0 ∧
      φ.pullback (weilFunction W ℓ hℓ T hT) =
        algebraMap F KE c *
          (weilFunction W ℓ hℓ (δ T) hU *
            (mulByInt W.toAffine ℓ).pullback k) := by
  haveI : IsDedekindDomain (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  obtain ⟨k₀, hk₀_ne, hk₀_div⟩ := pullbackDivisorClass_of_dualComp W φ δ hdc hsurj T
  have hdiv_key := hfact_projectiveDivisorOf_eq W ℓ hℓ φ hφ hcomm hT hU
    (k₀ := k₀) hk₀_ne hk₀_div
  have hgU_ne : weilFunction W ℓ hℓ (δ T) hU ≠ 0 := weilFunction_ne_zero W ℓ hℓ _ hU
  have hu_ne : (mulByInt W.toAffine ℓ).pullback k₀ ≠ 0 :=
    fun h0 => hk₀_ne ((mulByInt W.toAffine ℓ).pullback_injective (h0.trans (map_zero _).symm))
  have hpb_ne : φ.pullback (weilFunction W ℓ hℓ T hT) ≠ 0 :=
    fun h0 => weilFunction_ne_zero W ℓ hℓ T hT
      (φ.pullback_injective (h0.trans (map_zero _).symm))
  set rhs := weilFunction W ℓ hℓ (δ T) hU * (mulByInt W.toAffine ℓ).pullback k₀
  have hrhs_ne : rhs ≠ 0 := mul_ne_zero hgU_ne hu_ne
  have htransport : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
      (φ.pullback (weilFunction W ℓ hℓ T hT) / rhs) = 0 := by
    rw [div_eq_mul_inv,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hpb_ne (inv_ne_zero hrhs_ne),
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_inv hrhs_ne, hdiv_key,
      add_neg_cancel]
  obtain ⟨c, hc0, hc⟩ := const_unit_of_projectiveDivisorOf_eq_zero
    (φ.pullback (weilFunction W ℓ hℓ T hT) / rhs) (div_ne_zero hpb_ne hrhs_ne) htransport
  refine ⟨c, k₀, hc0, ?_⟩
  rw [div_eq_iff hrhs_ne] at hc
  rw [hc]

/-- **Image-restricted separable divisor factorisation `hfact` for an abstract dual `δ`** (Silverman
III.8.2, CoordHom-free, **no surjectivity**). Same statement as `hfact_of_dualComp`, but takes an
*explicit preimage* `P₀` of `T` (`hP₀ : φ P₀ = T`) in place of `hsurj`. It routes through
`pullbackDivisorClass_of_dualComp_image`; this is the form the scaling consumes at `T = φ T'`
(preimage `T'`). -/
theorem hfact_of_dualComp_image (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcomm : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    {T P₀ : W.toAffine.Point} (hP₀ : φ.toAddMonoidHom P₀ = T)
    (hT : ℓ • T = 0) (hU : ℓ • δ T = 0) :
    ∃ (c : F) (k : KE), c ≠ 0 ∧
      φ.pullback (weilFunction W ℓ hℓ T hT) =
        algebraMap F KE c *
          (weilFunction W ℓ hℓ (δ T) hU *
            (mulByInt W.toAffine ℓ).pullback k) := by
  haveI : IsDedekindDomain (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  obtain ⟨k₀, hk₀_ne, hk₀_div⟩ := pullbackDivisorClass_of_dualComp_image W φ δ hdc hP₀
  have hdiv_key := hfact_projectiveDivisorOf_eq W ℓ hℓ φ hφ hcomm hT hU
    (k₀ := k₀) hk₀_ne hk₀_div
  have hgU_ne : weilFunction W ℓ hℓ (δ T) hU ≠ 0 := weilFunction_ne_zero W ℓ hℓ _ hU
  have hu_ne : (mulByInt W.toAffine ℓ).pullback k₀ ≠ 0 :=
    fun h0 => hk₀_ne ((mulByInt W.toAffine ℓ).pullback_injective (h0.trans (map_zero _).symm))
  have hpb_ne : φ.pullback (weilFunction W ℓ hℓ T hT) ≠ 0 :=
    fun h0 => weilFunction_ne_zero W ℓ hℓ T hT
      (φ.pullback_injective (h0.trans (map_zero _).symm))
  set rhs := weilFunction W ℓ hℓ (δ T) hU * (mulByInt W.toAffine ℓ).pullback k₀
  have hrhs_ne : rhs ≠ 0 := mul_ne_zero hgU_ne hu_ne
  have htransport : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
      (φ.pullback (weilFunction W ℓ hℓ T hT) / rhs) = 0 := by
    rw [div_eq_mul_inv,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hpb_ne (inv_ne_zero hrhs_ne),
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_inv hrhs_ne, hdiv_key,
      add_neg_cancel]
  obtain ⟨c, hc0, hc⟩ := const_unit_of_projectiveDivisorOf_eq_zero
    (φ.pullback (weilFunction W ℓ hℓ T hT) / rhs) (div_ne_zero hpb_ne hrhs_ne) htransport
  refine ⟨c, k₀, hc0, ?_⟩
  rw [div_eq_iff hrhs_ne] at hc
  rw [hc]

/-- **The separable Weil-pairing adjoint for an abstract dual `δ`** (Silverman III.8.2,
CoordHom-free). For a separable isogeny `φ` of `E`, an abstract dual `δ` with the dual relation `hdc
: δ ∘ φ = [#ker φ]` and surjectivity `hsurj`, the geometric witnesses `hφ : ProjOrdTransport φ`, the
commutation `hcommφ : [ℓ] ∘ φ = φ ∘ [ℓ]`, and the translation covariance `hcomm'`: `e_ℓ(φS, T) =
e_ℓ(S, δT)`.

This is `weilPairing_adjoint_of_picDualDivisorClass` with `δ T` replacing `picDual φ T` and the
`hfact` produced by `hfact_of_dualComp` — **no `CoordHom`**. The dual point lies in `E[ℓ]`
automatically (`hU` below: `ℓ • δT = δ(ℓ • T) = δ 0 = 0`). -/
theorem weilPairing_adjoint_of_dualComp (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hsurj : Function.Surjective φ.toAddMonoidHom)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hU : ℓ • δ T = 0)
    (hcomm' : translateAlgEquivOfPoint W S (φ.pullback (weilFunction W ℓ hℓ T hT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) (weilFunction W ℓ hℓ T hT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT =
      weilPairing W ℓ hℓ S (δ T) hS hU := by
  obtain ⟨c, k, _hc0, hfact⟩ :=
    hfact_of_dualComp W ℓ hℓ φ hφ hcommφ δ hdc hsurj T hT hU
  exact weilPairing_adjoint_core W ℓ hℓ φ S T (δ T) hS hT hU hφS hcomm' hfact

/-- **Image-restricted separable Weil-pairing adjoint for an abstract dual `δ`** (Silverman III.8.2,
CoordHom-free, **no surjectivity**). Same as `weilPairing_adjoint_of_dualComp`, but with the second
argument supplied as the image `φ P₀` of an *explicit* preimage `P₀` (so `T := φ P₀`), removing the
surjectivity hypothesis: the σ-identity preimage is `P₀` itself.

This is what the symplectic scaling invokes (at `P₀ := T`, giving the second argument `φ T`), so the
scaling needs **no** point-map surjectivity. Routes through `hfact_of_dualComp_image`. -/
theorem weilPairing_adjoint_of_dualComp_image (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (S P₀ : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • φ.toAddMonoidHom P₀ = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hU : ℓ • δ (φ.toAddMonoidHom P₀) = 0)
    (hcomm' : translateAlgEquivOfPoint W S
        (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
        (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom P₀) hφS hT =
      weilPairing W ℓ hℓ S (δ (φ.toAddMonoidHom P₀)) hS hU := by
  obtain ⟨c, k, _hc0, hfact⟩ :=
    hfact_of_dualComp_image W ℓ hℓ φ hφ hcommφ δ hdc (T := φ.toAddMonoidHom P₀) (P₀ := P₀) rfl hT hU
  exact weilPairing_adjoint_core W ℓ hℓ φ S (φ.toAddMonoidHom P₀) (δ (φ.toAddMonoidHom P₀))
    hS hT hU hφS hcomm' hfact

/-- **The CoordHom-free symplectic scaling of the Weil pairing** (Silverman III.8.6.1): for a
separable isogeny `φ` of `E` and `S, T ∈ E[ℓ]`,
```
e_ℓ(φS, φT) = e_ℓ(S, T) ^ (deg φ).
```

Inputs — **all CoordHom-free**, carried per isogeny exactly as `ProjOrdTransport`/`Naturality` are
throughout the project:
* `hφ`/`hcommφ`/`hcomm'` — the adjoint witnesses (divisor-pullback functoriality, `[ℓ] ∘ φ = φ ∘
  [ℓ]`, translation covariance) at the point `φT`;
* `δ` with `hdc : δ ∘ φ = [#ker φ]` — the **divisor-pushforward dual** and Silverman III.6.2(a)
  relation;
* `hdeg : #ker φ = deg φ` — the separable degree match (Silverman III.4.10c, `#ker = deg` for
  separable `φ`).

**No point-map surjectivity is required**: the adjoint is invoked only at the *image* `φT`, whose
preimage is the explicit point `T` itself (`φ T = φ T`, `rfl`); the σ-identity of
`pullbackDivisorClass_of_dualComp_image` therefore takes `P₀ := T` and never needs `hsurj`
(reviewer round-20 Q2). -/
theorem weilPairing_scaling_of_dualComp (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hdeg : Nat.card φ.toAddMonoidHom.ker = φ.degree)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hφT : ℓ • φ.toAddMonoidHom T = 0)
    (hcomm' : translateAlgEquivOfPoint W S
        (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
        (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom T) hφS hφT =
      weilPairing W ℓ hℓ S T hS hT ^ φ.degree := by
  have hδφT_tor : ℓ • δ (φ.toAddMonoidHom T) = 0 := by
    rw [← map_zsmul, hφT, map_zero]
  rw [weilPairing_adjoint_of_dualComp_image W ℓ hℓ φ hφ hcommφ δ hdc S T
    hS hφT hφS hδφT_tor hcomm']
  have hδφT : δ (φ.toAddMonoidHom T) = (φ.degree : ℕ) • T := by
    have hval := DFunLike.congr_fun hdc T
    rw [AddMonoidHom.comp_apply, mulByInt_apply] at hval
    rw [hval, hdeg, natCast_zsmul]
  have hdegN_tor : ℓ • ((φ.degree : ℕ) • T) = 0 := smul_nsmul_eq_zero_right W ℓ T hT φ.degree
  rw [weilPairing_congr_right W ℓ hℓ hS hδφT_tor hdegN_tor hδφT]
  exact weilPairing_nsmul_right W ℓ hℓ S T hS hT φ.degree hdegN_tor

section WeilScalesBridge

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **The `WeilScales` bridge from the CoordHom-free scaling** (Silverman III.8.6.1, the
`FrobMatrixData`-facing form). For a prime `ℓ`, a separable isogeny `φ` over `E` realising the bare
hom `ψ` (`hψ : φ.toAddMonoidHom = ψ`) with `φ.degree = d` (`hd`), an abstract dual `δ` with the dual
relation `hdc : δ ∘ φ = [#ker φ]`, the separable degree match `hdeg : #ker φ = deg φ`, and the
per-`(S, T)` adjoint witnesses `hφ`/`hcommφ` and the translation covariance `hcomm'` (supplied for
every torsion `S, T`), the predicate `WeilScales W ℓ hℓF ψ d` holds — **CoordHom-free** and with
**no point-map surjectivity** (the underlying scaling invokes the adjoint only at images `φT`, so
the σ-identity preimage is explicit; reviewer round-20 Q2).

This is the bridge a caller uses to discharge `OneSubFrobeniusScaling`/`PencilScaling`: take `φ = (1
− π)_{K̄}` resp `(rπ − s)_{K̄}` (the base-changed genuine isogeny), `ψ` the corresponding bare hom,
`δ` the divisor-pushforward dual (`V`-based), and supply the per-isogeny geometric witnesses.
(Surjectivity may still be needed to *construct* a divisor-pushforward `δ`, but it is no longer a
hypothesis of the scaling itself.) -/
theorem weilScales_of_dualComp (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ψ : W.toAffine.Point →+ W.toAffine.Point) (hψ : φ.toAddMonoidHom = ψ)
    (d : ℕ) (hd : φ.degree = d) (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom)
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hdeg : Nat.card φ.toAddMonoidHom.ker = φ.degree)
    (hcomm' : ∀ (S T : W.toAffine.Point) (hS : ((ℓ : ℕ) : ℤ) • S = 0)
        (hφT : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom T = 0),
      translateAlgEquivOfPoint W S
          (φ.pullback (weilFunction W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
            (φ.toAddMonoidHom T) hφT)) =
        φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
          (weilFunction W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) (φ.toAddMonoidHom T) hφT))) :
    WeilScales W ℓ hℓF ψ d := by
  subst hψ hd
  intro S T
  have hSt := zsmul_eq_zero_of_mem_torsion W ℓ S
  have hTt := zsmul_eq_zero_of_mem_torsion W ℓ T
  have hφSt : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom S.val = 0 := by
    rw [← map_zsmul, hSt, map_zero]
  have hφTt : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom T.val = 0 := by
    rw [← map_zsmul, hTt, map_zero]
  exact weilPairing_scaling_of_dualComp W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) φ hφ hcommφ δ hdc
    hdeg S.val T.val hSt hTt hφSt hφTt (hcomm' S.val T.val hSt hφTt)

end WeilScalesBridge

section NoDelta

omit [IsAlgClosed F] in
/-- **`δ`-free image-restricted projective divisor-class identity** (Silverman III.6.1b,
CoordHom-free, **no dual `δ`, no surjectivity**). For an isogeny `φ` with finite kernel and an
*explicit* preimage `P₀` of the target `φ P₀`, the fibre-pullback divisor `φ^*((φ P₀) − (O))` is
linearly equivalent to `(#ker(φ) • P₀) − (O)`:
```
(⟨W⟩).ProjIsPrincipal (pullbackDivisor φ ((φ P₀) − (O)) − ((#ker(φ) • P₀) − (O))).
```

This is `pullbackDivisorClass_of_dualComp_image` with the dual point `δ (φ P₀)` replaced by the
explicit `#ker(φ) • P₀`, so the σ-identity is the **primitive** bridge
`sigma_pullbackDivisor_kappaDivisor` (`σ(φ^*((φ P₀) − (O))) = #ker(φ) • P₀`, preimage `P₀`) — no
abstract dual `δ`, no dual relation `hdc`. Degree `0` (both fibres have degree `#ker`) and `σ = 0`
(`#ker • P₀ − #ker • P₀`), so Abel (`projIsPrincipal_of_degZero_of_sigma_eq_zero`, char-free) makes
it principal. -/
theorem pullbackDivisorClass_image_noδ
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (P₀ : W.toAffine.Point) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
      (pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance
          (Curves.kappaDivisor W.toAffine (φ.toAddMonoidHom P₀)) -
        Curves.kappaDivisor W.toAffine (Nat.card φ.toAddMonoidHom.ker • P₀)) := by
  refine projIsPrincipal_of_degZero_of_sigma_eq_zero (W := W.toAffine) _ ?_ ?_
  · rw [← Curves.ProjectiveDivisor.degreeHom_apply, map_sub,
      Curves.ProjectiveDivisor.degreeHom_apply, Curves.ProjectiveDivisor.degreeHom_apply,
      degree_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance (P₀ := P₀) rfl,
      Curves.kappaDivisor_degree, sub_self]
  · rw [Curves.projectiveDivisorSum_sub,
      sigma_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance (P₀ := P₀) rfl,
      Curves.projectiveDivisorSum_kappaDivisor, sub_self]

/-- **`δ`-free image-restricted separable divisor factorisation `hfact`** (Silverman III.8.2,
CoordHom-free, **no dual `δ`, no surjectivity**).  Same shape as `hfact_of_dualComp_image`, but the
dual point is the explicit `#ker(φ) • P₀` (not `δ (φ P₀)`), routed through
`pullbackDivisorClass_image_noδ`:
```
φ^* g_{φ P₀} = c · g_{#ker(φ)•P₀} · ([ℓ]^* k).
```
Needs only `hφ : ProjOrdTransport φ` and the `[ℓ]`-commutation `hcomm` (automatic, `map_zsmul`).  No
`δ`, no `hdc`, no `hsurj`. -/
theorem hfact_image_noδ (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcomm : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (P₀ : W.toAffine.Point)
    (hT : ℓ • φ.toAddMonoidHom P₀ = 0) (hU : ℓ • (Nat.card φ.toAddMonoidHom.ker • P₀) = 0) :
    ∃ (c : F) (k : KE), c ≠ 0 ∧
      φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT) =
        algebraMap F KE c *
          (weilFunction W ℓ hℓ (Nat.card φ.toAddMonoidHom.ker • P₀) hU *
            (mulByInt W.toAffine ℓ).pullback k) := by
  haveI : IsDedekindDomain (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  obtain ⟨k₀, hk₀_ne, hk₀_div⟩ := pullbackDivisorClass_image_noδ W φ P₀
  have hdiv_key := hfact_projectiveDivisorOf_eq W ℓ hℓ φ hφ hcomm hT hU
    (k₀ := k₀) hk₀_ne hk₀_div
  have hgU_ne : weilFunction W ℓ hℓ (Nat.card φ.toAddMonoidHom.ker • P₀) hU ≠ 0 :=
    weilFunction_ne_zero W ℓ hℓ _ hU
  have hu_ne : (mulByInt W.toAffine ℓ).pullback k₀ ≠ 0 :=
    fun h0 => hk₀_ne ((mulByInt W.toAffine ℓ).pullback_injective (h0.trans (map_zero _).symm))
  have hpb_ne : φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT) ≠ 0 :=
    fun h0 => weilFunction_ne_zero W ℓ hℓ (φ.toAddMonoidHom P₀) hT
      (φ.pullback_injective (h0.trans (map_zero _).symm))
  set rhs := weilFunction W ℓ hℓ (Nat.card φ.toAddMonoidHom.ker • P₀) hU *
    (mulByInt W.toAffine ℓ).pullback k₀
  have hrhs_ne : rhs ≠ 0 := mul_ne_zero hgU_ne hu_ne
  have htransport : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
      (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT) / rhs) = 0 := by
    rw [div_eq_mul_inv,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hpb_ne (inv_ne_zero hrhs_ne),
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_inv hrhs_ne, hdiv_key,
      add_neg_cancel]
  obtain ⟨c, hc0, hc⟩ := const_unit_of_projectiveDivisorOf_eq_zero
    (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT) / rhs)
    (div_ne_zero hpb_ne hrhs_ne) htransport
  refine ⟨c, k₀, hc0, ?_⟩
  rw [div_eq_iff hrhs_ne] at hc
  rw [hc]

/-- **`δ`-free image-restricted separable Weil-pairing adjoint** (Silverman III.8.2, CoordHom-free,
**no dual `δ`, no surjectivity**).  Same as `weilPairing_adjoint_of_dualComp_image`, but the second
argument is the explicit `#ker(φ) • P₀` rather than `δ (φ P₀)`:
```
e_ℓ(φ S, φ P₀) = e_ℓ(S, #ker(φ) • P₀).
```
Via `weilPairing_adjoint_core` (abstract `U := #ker(φ) • P₀`) fed by `hfact_image_noδ` and the
translation covariance `hcomm'`.  No `δ`, no `hdc`, no `hsurj`. -/
theorem weilPairing_adjoint_image_noδ (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (S P₀ : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • φ.toAddMonoidHom P₀ = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hU : ℓ • (Nat.card φ.toAddMonoidHom.ker • P₀) = 0)
    (hcomm' : translateAlgEquivOfPoint W S
        (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
        (weilFunction W ℓ hℓ (φ.toAddMonoidHom P₀) hT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom P₀) hφS hT =
      weilPairing W ℓ hℓ S (Nat.card φ.toAddMonoidHom.ker • P₀) hS hU := by
  obtain ⟨c, k, _hc0, hfact⟩ :=
    hfact_image_noδ W ℓ hℓ φ hφ hcommφ P₀ hT hU
  exact weilPairing_adjoint_core W ℓ hℓ φ S (φ.toAddMonoidHom P₀)
    (Nat.card φ.toAddMonoidHom.ker • P₀) hS hT hU hφS hcomm' hfact

/-- **The `δ`-free, surjectivity-free symplectic scaling** (Silverman III.8.6.1), CoordHom-free.
For a separable isogeny `φ` of `E` and `S, T ∈ E[ℓ]`,
```
e_ℓ(φ S, φ T) = e_ℓ(S, T) ^ (deg φ),
```
**with no abstract dual `δ`, no dual relation `hdc`, and no point-map surjectivity** (reviewer
round-22 Q3, image-restricted route).

Inputs — all CoordHom-free, carried per isogeny exactly as `ProjOrdTransport`/`Naturality`:
* `hφ`/`hcommφ`/`hcomm'` — the adjoint witnesses at the image `φ T` (divisor-pullback functoriality,
  `[ℓ] ∘ φ = φ ∘ [ℓ]`, translation covariance);
* `hdeg : #ker φ = deg φ` — the separable degree match (Silverman III.4.10c).

The dual point at the image `φ T` is the **explicit** `#ker(φ) • T`, read off the *primitive*
σ-bridge `sigma_pullbackDivisor_kappaDivisor` (preimage `T`); there is no `δ`, no `δ ∘ φ = [#ker
φ]`, no surjectivity. -/
theorem weilPairing_scaling_noδ (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (hdeg : Nat.card φ.toAddMonoidHom.ker = φ.degree)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hφT : ℓ • φ.toAddMonoidHom T = 0)
    (hcomm' : translateAlgEquivOfPoint W S
        (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
        (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom T) hφS hφT =
      weilPairing W ℓ hℓ S T hS hT ^ φ.degree := by
  have hkerT_tor : ℓ • (Nat.card φ.toAddMonoidHom.ker • T) = 0 :=
    smul_nsmul_eq_zero_right W ℓ T hT (Nat.card φ.toAddMonoidHom.ker)
  rw [weilPairing_adjoint_image_noδ W ℓ hℓ φ hφ hcommφ S T hS hφT hφS hkerT_tor hcomm',
    weilPairing_nsmul_right W ℓ hℓ S T hS hT (Nat.card φ.toAddMonoidHom.ker) hkerT_tor, hdeg]

set_option linter.unusedVariables false in
/-- **The `δ`-free, surjectivity-free `WeilScales` bridge** (Silverman III.8.6.1, the
`FrobMatrixData`-facing form).  For a prime `ℓ`, a separable isogeny `φ` over `E` realising the bare
hom `ψ` (`hψ : φ.toAddMonoidHom = ψ`) with `φ.degree = d` (`hd`), the separable degree match
`hdeg : #ker φ = deg φ`, the divisor-pullback functoriality `hφ : ProjOrdTransport φ`, the
`[ℓ]`-commutation `hcommφ`, and the per-`(S, T)` translation covariance `hcomm'`, the predicate
`WeilScales W ℓ hℓF ψ d` holds — **CoordHom-free, with no abstract dual `δ`, no dual relation `hdc`,
and no point-map surjectivity** (reviewer round-22 Q3).

This is `weilScales_of_dualComp` with the `δ`/`hdc` arguments *dropped*: the underlying scaling
`weilPairing_scaling_noδ` reads the dual point at each image `φ T` off the primitive σ-bridge as the
explicit `#ker(φ) • T`, so neither a dual endomorphism nor surjectivity is ever needed. -/
theorem weilScales_noδ (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ψ : W.toAffine.Point →+ W.toAffine.Point) (hψ : φ.toAddMonoidHom = ψ)
    (d : ℕ) (hd : φ.degree = d) (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom)
    (hdeg : Nat.card φ.toAddMonoidHom.ker = φ.degree)
    (hcomm' : ∀ (S T : W.toAffine.Point) (hS : ((ℓ : ℕ) : ℤ) • S = 0)
        (hφT : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom T = 0),
      translateAlgEquivOfPoint W S
          (φ.pullback (weilFunction W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
            (φ.toAddMonoidHom T) hφT)) =
        φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
          (weilFunction W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) (φ.toAddMonoidHom T) hφT))) :
    WeilScales W ℓ hℓF ψ d := by
  subst hψ hd
  intro S T
  have hSt := zsmul_eq_zero_of_mem_torsion W ℓ S
  have hTt := zsmul_eq_zero_of_mem_torsion W ℓ T
  have hφSt : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom S.val = 0 := by
    rw [← map_zsmul, hSt, map_zero]
  have hφTt : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom T.val = 0 := by
    rw [← map_zsmul, hTt, map_zero]
  exact weilPairing_scaling_noδ W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) φ hφ hcommφ
    hdeg S.val T.val hSt hTt hφSt hφTt (hcomm' S.val T.val hSt hφTt)

/-- **The `δ`-free, surjectivity-free symplectic scaling with the `#ker` exponent** (Silverman
III.8.6.1), CoordHom-free.  For a separable isogeny `φ` of `E` and `S, T ∈ E[ℓ]`,
```
e_ℓ(φ S, φ T) = e_ℓ(S, T) ^ (#ker φ),
```
**with no abstract dual `δ`, no dual relation `hdc`, no point-map surjectivity, and — crucially — no
degree match `#ker φ = deg φ`**. This is `weilPairing_scaling_noδ` with the final `hdeg`-rewrite
`#ker → degree` removed: the dual point at the image `φ T` is the explicit `#ker(φ) • T` (read off
the primitive σ-bridge `sigma_pullbackDivisor_kappaDivisor`, preimage `T`), and
`weilPairing_nsmul_right` delivers the `#ker(φ)`-power directly. The exponent is the *cardinality*
of the kernel, automatically `≥ 0`. -/
theorem weilPairing_scaling_noδ_card (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hφT : ℓ • φ.toAddMonoidHom T = 0)
    (hcomm' : translateAlgEquivOfPoint W S
        (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
        (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom T) hφS hφT =
      weilPairing W ℓ hℓ S T hS hT ^ Nat.card φ.toAddMonoidHom.ker := by
  have hkerT_tor : ℓ • (Nat.card φ.toAddMonoidHom.ker • T) = 0 :=
    smul_nsmul_eq_zero_right W ℓ T hT (Nat.card φ.toAddMonoidHom.ker)
  rw [weilPairing_adjoint_image_noδ W ℓ hℓ φ hφ hcommφ S T hS hφT hφS hkerT_tor hcomm',
    weilPairing_nsmul_right W ℓ hℓ S T hS hT (Nat.card φ.toAddMonoidHom.ker) hkerT_tor]

set_option linter.unusedVariables false in
/-- **The `δ`-free, surjectivity-free `WeilScales` bridge with the `#ker` exponent** (Silverman
III.8.6.1, the `FrobMatrixData`-facing form). For a prime `ℓ`, a separable isogeny `φ` over `E`
realising the bare hom `ψ` (`hψ : φ.toAddMonoidHom = ψ`), the divisor-pullback functoriality `hφ :
ProjOrdTransport φ`, the `[ℓ]`-commutation `hcommφ`, and the per-`(S, T)` translation covariance
`hcomm'`, the predicate `WeilScales W ℓ hℓF ψ (Nat.card φ.toAddMonoidHom.ker)` holds —
**CoordHom-free, with no abstract dual `δ`, no dual relation `hdc`, no point-map surjectivity, and
no degree match `#ker = deg`** (the `hdeg : #ker φ = deg φ` and `d`/`hd : φ.degree = d` arguments of
`weilScales_noδ` are both *dropped*).

The output exponent is the **cardinality** `Nat.card φ.toAddMonoidHom.ker`, automatically `≥ 0`, so
a caller can use this with `deg r s := (#ker (rπ − s)_{K̄} : ℤ)` and discharge the bound's
`hdeg_nonneg` by `Nat.cast_nonneg`, never needing the AG-frontier `#ker = deg`. -/
theorem weilScales_noδ_card (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ψ : W.toAffine.Point →+ W.toAffine.Point) (hψ : φ.toAddMonoidHom = ψ) (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom)
    (hcomm' : ∀ (S T : W.toAffine.Point) (hS : ((ℓ : ℕ) : ℤ) • S = 0)
        (hφT : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom T = 0),
      translateAlgEquivOfPoint W S
          (φ.pullback (weilFunction W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
            (φ.toAddMonoidHom T) hφT)) =
        φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
          (weilFunction W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) (φ.toAddMonoidHom T) hφT))) :
    WeilScales W ℓ hℓF ψ (Nat.card φ.toAddMonoidHom.ker) := by
  subst hψ
  intro S T
  have hSt := zsmul_eq_zero_of_mem_torsion W ℓ S
  have hTt := zsmul_eq_zero_of_mem_torsion W ℓ T
  have hφSt : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom S.val = 0 := by
    rw [← map_zsmul, hSt, map_zero]
  have hφTt : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom T.val = 0 := by
    rw [← map_zsmul, hTt, map_zero]
  exact weilPairing_scaling_noδ_card W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) φ hφ hcommφ
    S.val T.val hSt hTt hφSt hφTt (hcomm' S.val T.val hSt hφTt)

end NoDelta

end HasseWeil.WeilPairing
