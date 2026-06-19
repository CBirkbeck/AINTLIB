/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PairingAdjoint
import HasseWeil.WeilPairing.DivisorPullback
import HasseWeil.WeilPairing.Constancy
import HasseWeil.Pic0.PicDual

/-!
# The separable divisor factorisation `hfact` (Silverman III.8.2 / III.6.1b)

This file discharges the **divisor factorisation hypothesis** `hfact` of
`HasseWeil.WeilPairing.weilPairing_adjoint_core` (the separable adjoint, Silverman III.8.2): for a
separable isogeny `φ : E → E`, the Weil functions `g_T = weilFunction W ℓ T`, `g_U = weilFunction
W ℓ U` (with `U = picDual φ T = φ̂ T`), and an appropriate `k ∈ K(E)`,
```
φ^* g_T = c · (g_U · ([ℓ]^* k))      for some c ∈ Fˣ.
```

## The mathematics (Silverman III.8.2 proof, divisor language)

Write `div g_T = [ℓ]^*((T) − (O))` (`weilFunction_divisor`, the fibre-difference divisor). Then

* `div(φ^* g_T) = φ^*(div g_T) = φ^*([ℓ]^*((T) − (O)))` — the divisor-pullback functoriality
  `div(φ^* h) = φ^*(div h)` for the separable `φ` (`DivisorPullback.ProjOrdTransport φ`, the
  analogue of `projOrdTransport_mulByInt` for `[ℓ]`);
* `φ^* ∘ [ℓ]^* = [ℓ]^* ∘ φ^*` on divisors (the function-field shadow of `[ℓ] ∘ φ = φ ∘ [ℓ]`, which
  holds for *any* additive point maps: `[ℓ]` commutes with every homomorphism) — proven here as
  `pullbackDivisor_comm`;
* the **`picDual` divisor-class identity** (Silverman III.6.1b, the genuine separability content)
  `φ^*((T) − (O)) ∼ (U) − (O)` with `U = φ̂ T`, i.e. `φ^*(kappaDivisor T) − kappaDivisor U` is
  principal `= div k₀` — isolated below as the single minimal hypothesis `PicDualDivisorClass φ`
  (a projective-divisor avatar of `PicDual.Naturality`, see the residual note).

Combining: `div(φ^* g_T) = [ℓ]^*(φ^*(kappaDivisor T)) = [ℓ]^*(kappaDivisor U + div k₀) = div(g_U) +
div([ℓ]^* k₀) = div(g_U · [ℓ]^* k₀)`. Two functions with the same projective divisor differ by a
nonzero constant `c ∈ Fˣ` (`Constancy.const_unit_of_projectiveDivisorOf_eq_zero`), which is exactly
`hfact`.

## The isolated minimal residual `PicDualDivisorClass`

The decisive ingredient is the divisor-class identity `φ^*((T) − (O)) ∼ (φ̂ T) − (O)` *expressed in
the projective-divisor model* `ProjectiveDivisor` (where `weilFunction_divisor`/`hfact` speak),
namely `(⟨W⟩).ProjIsPrincipal (pullbackDivisor φ (kappaDivisor T) − kappaDivisor (φ̂ T))`.

This is the **honest frontier**: `picDual = κ⁻¹ ∘ classMap ∘ κ` is defined in the *affine ideal
class group* model `ClassGroup R` (`PicDual.lean`), where `classMap = ClassGroup.map` is the ideal
extension `𝔪 ↦ 𝔪·𝒪` — Silverman's divisor pullback `φ^*`. But `hfact` lives in the *projective
divisor* model `PicProj₀`/`projectiveDivisorOf`. The two `Pic⁰(E)` models are connected by `κ`
(the canonical `E ≅ Pic⁰(E)` of III.3.4), but the repo carries no bridge `ClassGroup.map ↔
pullbackDivisor`; building it is exactly the `comap`-vs-`relNorm` (residue-degree) bookkeeping that
`PicDual.Naturality` documents as carried per-isogeny data. We therefore isolate the divisor-class
identity as the one minimal hypothesis `PicDualDivisorClass φ ch hinj hfin`, dischargeable per
isogeny just as `ProjOrdTransport`/`Naturality` are throughout the project, and prove the *entire*
`hfact` factorisation on top of it.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.1 (the dual isogeny, `φ̂ = κ⁻¹ ∘ φ^* ∘ κ`),
  III.8.2 (Prop 8.2, the separable adjoint via the multiplicity-free pullback).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

/-! ### Commutation of fibre-pullback divisors `φ^* ∘ ψ^* = (ψ ∘ φ)^*`

The fibre-pullback `pullbackDivisor f` (`DivisorPullback.lean`) transports a coefficient along the
point map `f`: `(pullbackDivisor f D) w = D (f w)` (`pullbackDivisor_apply`). Hence two such
pullbacks compose by composing the point maps in the *opposite* order:
`pullbackDivisor f (pullbackDivisor g D) w = D (g (f w))`. We only need the special case where the
two maps **commute** as point endomorphisms (`g ∘ f = f ∘ g`), which is automatic when one of them
is `[ℓ]` (multiplication-by-`ℓ` commutes with every additive hom). -/

/-- **Fibre-pullback divisors of commuting point maps commute.** If `f g : E.Point →+ E.Point`
commute (`g.comp f = f.comp g` — automatic when one is `[ℓ]`), then their fibre-pullback divisor
operators commute: `pullbackDivisor f (pullbackDivisor g D) = pullbackDivisor g (pullbackDivisor f
D)`. Both coefficients at a place `w` are `D` evaluated at the common image `g (f w) = f (g w)`. -/
theorem pullbackDivisor_comm {f g : W.toAffine.Point →+ W.toAffine.Point}
    (hf : Finite f.ker) (hg : Finite g.ker) (hfg : g.comp f = f.comp g)
    (D : ProjectiveDivisor (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :
    pullbackDivisor f hf (pullbackDivisor g hg D) =
      pullbackDivisor g hg (pullbackDivisor f hf D) := by
  refine Finsupp.ext fun w ↦ ?_
  rw [pullbackDivisor_apply, pullbackDivisor_apply, pullbackDivisor_apply, pullbackDivisor_apply,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint]
  -- `D (g (f w)) = D (f (g w))` from `g ∘ f = f ∘ g`.
  have : g (f w.toAffinePoint) = f (g w.toAffinePoint) := by
    have := DFunLike.congr_fun hfg w.toAffinePoint
    simpa only [AddMonoidHom.comp_apply] using this
  rw [this]

/-! ### `div g_T` as the fibre-pullback of `(T) − (O)`

`div(g_T) = [ℓ]^*(T) − [ℓ]^*(O)` (`weilFunction_divisor`), and the right side is the fibre-pullback
`pullbackDivisor [ℓ] (kappaDivisor T)` of the Abel–Jacobi divisor `(T) − (O) = kappaDivisor T`
(`pullbackDivisor` distributes over the difference of the two `single`s; `∞.toAffinePoint = O`). -/

/-- **The fibre-pullback of `(T) − (O)` is `[ℓ]^*(T) − [ℓ]^*(O)`** (= `div g_T`). The fibre-pullback
`pullbackDivisor [ℓ]` of `kappaDivisor T = (T) − (O)` equals `pullbackDiv [ℓ] T − pullbackDiv [ℓ]
O`. (Local copy of `PairingNondeg.pullbackDivisor_kappaDivisor`, kept here to avoid the import;
named `…_local` to avoid the cross-file name clash with the `PairingNondeg` copy, so that downstream
files importing both `HfactLemma` and `DetDeg`/`PairingNondeg` — e.g. `SeparableScaling` — compile.) -/
theorem pullbackDivisor_kappaDivisor_local (ℓ : ℤ)
    [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] (T : W.toAffine.Point) :
    pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker
        (Curves.kappaDivisor W.toAffine T) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker T -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0 := by
  rw [Curves.kappaDivisor, ← pullbackDivisorHom_apply, map_sub, pullbackDivisorHom_apply,
    pullbackDivisorHom_apply, pullbackDivisor_single, pullbackDivisor_single, one_smul, one_smul,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    ProjectiveSmoothPoint.toAffinePoint_infinity]

/-- **`div g_T = [ℓ]^*((T) − (O))`** in fibre-pullback form: the projective divisor of the Weil
function `g_T` equals `pullbackDivisor [ℓ] (kappaDivisor T)`. Combines `weilFunction_divisor`
(`= pullbackDiv [ℓ] T − pullbackDiv [ℓ] O`) with `pullbackDivisor_kappaDivisor_local`. -/
theorem weilFunction_divisor_eq_pullbackDivisor_kappaDivisor [IsAlgClosed F]
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (weilFunction W ℓ hℓ T hT) =
      pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (Curves.kappaDivisor W.toAffine T) := by
  haveI : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker := mulByInt_ker_finite W ℓ hℓ
  rw [show (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (weilFunction W ℓ hℓ T hT) =
      (W_smooth W).projectiveDivisorOf (weilFunction W ℓ hℓ T hT) from rfl,
    weilFunction_divisor W ℓ hℓ T hT, pullbackDivisor_kappaDivisor_local W ℓ T]

/-! ### The isolated minimal residual: the `picDual` divisor-class identity (projective form)

`PicDualDivisorClass φ` packages Silverman III.6.1b in the projective-divisor model: the
fibre-pullback `φ^*((T) − (O))` is *linearly equivalent* to `(φ̂ T) − (O)` (with `φ̂ = picDual φ`),
i.e. their difference `pullbackDivisor φ (kappaDivisor T) − kappaDivisor (φ̂ T)` is principal. This
is the one ingredient that cannot be assembled from the project's *projective*-model API: `picDual`
is built from the *affine* ideal-class-group divisor pullback `classMap` (`PicDual.lean`), and the
ClassGroup↔ProjectiveDivisor bridge is the carried `PicDual.Naturality` data (the `comap`-vs-
`relNorm`/residue-degree bookkeeping). Everything else in `hfact` is proven on top of this. -/

/-- **The `picDual` divisor-class identity, projective form** (Silverman III.6.1b, the genuine
separability content). For an isogeny `φ` of `E` with `picDual` data `ch`/`hinj`/`hfin`, the
fibre-pullback divisor `φ^*((T) − (O)) = pullbackDivisor φ (kappaDivisor T)` is linearly equivalent
to `(φ̂ T) − (O) = kappaDivisor (picDual φ T)`, for every torsion point `T`.

This is the projective-divisor avatar of `PicDual.Naturality`: `picDual = κ⁻¹ ∘ classMap ∘ κ` is
defined in the affine ideal class group, where `classMap = ClassGroup.map` is the ideal-extension
divisor pullback; the identity here is that pullback transported to the projective `ProjectiveDivisor`
model along `κ : E ≅ Pic⁰(E)`. It is dischargeable per isogeny exactly as `ProjOrdTransport` and
`Naturality` are throughout the project. -/
def PicDualDivisorClass (φ : Isogeny W.toAffine W.toAffine)
    [Finite φ.toAddMonoidHom.ker]
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule) : Prop :=
  ∀ T : W.toAffine.Point,
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
      (pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance
          (Curves.kappaDivisor W.toAffine T) -
        Curves.kappaDivisor W.toAffine ((φ.picDual ch hinj hfin) T))

/-! ### The `hfact` discharge

We now assemble the divisor factorisation. The proof computes `div(φ^* g_T)` and shows it equals
`div(g_U · [ℓ]^* k₀)` for the Abel–Jacobi function `k₀` of the `picDual` divisor-class identity,
then concludes by "same divisor ⟹ constant" (`const_unit_of_projectiveDivisorOf_eq_zero`). -/

variable [IsAlgClosed F]

/-- **The key divisor equality behind `hfact`** (Silverman III.8.2, divisor language). For a
separable isogeny `φ` with the divisor-pullback functoriality `hφ : ProjOrdTransport φ`, the
commutation `[ℓ] ∘ φ = φ ∘ [ℓ]`, and a function `k₀` realising the `picDual` divisor-class identity
`φ^*((T) − (O)) = (U) − (O) + div k₀` (`hk₀_div`, with `U = φ̂ T`), the projective divisors of
`φ^* g_T` and `g_U · ([ℓ]^* k₀)` agree:
```
div(φ^* g_T) = div(g_U · [ℓ]^* k₀).
```
This isolates the divisor computation (the heavy part) from the constant-extraction in
`hfact_of_picDualDivisorClass`.

`div(φ^* g_T) = φ^*([ℓ]^* κT) = [ℓ]^*(φ^* κT)` (`weilFunction_divisor` + `pullbackDivisor_comm`),
and `φ^* κT = κU + div k₀` (`hk₀_div`), so `= [ℓ]^* κU + [ℓ]^*(div k₀) = div(g_U) + div([ℓ]^* k₀)`. -/
theorem hfact_projectiveDivisorOf_eq (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcomm : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    {T U : W.toAffine.Point} (hT : ℓ • T = 0) (hU : ℓ • U = 0)
    {k₀ : KE} (hk₀_ne : k₀ ≠ 0)
    (hk₀_div : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf k₀ =
      pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance
          (Curves.kappaDivisor W.toAffine T) -
        Curves.kappaDivisor W.toAffine U) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (φ.pullback (weilFunction W ℓ hℓ T hT)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (weilFunction W ℓ hℓ U hU * (mulByInt W.toAffine ℓ).pullback k₀) := by
  haveI hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker := mulByInt_ker_finite W ℓ hℓ
  have hcoreℓ : ProjOrdTransport (mulByInt W.toAffine ℓ) := projOrdTransport_mulByInt ℓ hℓ
  set κT := Curves.kappaDivisor W.toAffine T
  set κU := Curves.kappaDivisor W.toAffine U with hκU
  have hgU_ne : weilFunction W ℓ hℓ U hU ≠ 0 := weilFunction_ne_zero W ℓ hℓ U hU
  have hu_ne : (mulByInt W.toAffine ℓ).pullback k₀ ≠ 0 :=
    fun h0 ↦ hk₀_ne ((mulByInt W.toAffine ℓ).pullback_injective (h0.trans (map_zero _).symm))
  -- LHS: `div(φ^* g_T) = φ^*(div g_T) = φ^*([ℓ]^* κT) = [ℓ]^*(φ^* κT)`.
  have hLHS : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (φ.pullback (weilFunction W ℓ hℓ T hT)) =
      pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker
        (pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance κT) := by
    rw [pullback_divisorOf_eq_of_divisorOf_eq hφ
        (weilFunction_divisor_eq_pullbackDivisor_kappaDivisor W ℓ hℓ T hT)]
    exact pullbackDivisor_comm W (f := φ.toAddMonoidHom)
      (g := (mulByInt W.toAffine ℓ).toAddMonoidHom) inferInstance hker hcomm κT
  -- `φ^* κT = κU + div k₀` from `hk₀_div`.
  have hφκT : pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance κT =
      κU + (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf k₀ := by
    rw [hk₀_div, hκU]; abel
  -- RHS: `div(g_U · u) = div(g_U) + div(u) = [ℓ]^* κU + [ℓ]^*(div k₀)`.
  have hRHS : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (weilFunction W ℓ hℓ U hU * (mulByInt W.toAffine ℓ).pullback k₀) =
      pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker κU +
        pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker
          ((⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf k₀) := by
    rw [(⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hgU_ne hu_ne,
      weilFunction_divisor_eq_pullbackDivisor_kappaDivisor W ℓ hℓ U hU,
      pullback_divisorOf_eq_of_divisorOf_eq (φ := mulByInt W.toAffine ℓ) hcoreℓ
        (k := k₀) (D := (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf k₀) rfl]
  rw [hLHS, hRHS, hφκT, ← pullbackDivisorHom_apply, map_add, pullbackDivisorHom_apply,
    pullbackDivisorHom_apply]

/-- **The separable divisor factorisation `hfact`** (Silverman III.8.2 / III.6.1b). For a separable
isogeny `φ` of `E` with the divisor-pullback functoriality witness `hφ : ProjOrdTransport φ`, finite
kernel `[Finite φ.ker]`, the commutation `[ℓ] ∘ φ = φ ∘ [ℓ]` (`hcomm`, automatic — `[ℓ]` commutes
with every hom), the `picDual` data `ch`/`hinj`/`hfin`, and the `picDual` divisor-class identity
`hpd : PicDualDivisorClass φ` (the single carried residual, Silverman III.6.1b), there exist a
nonzero constant `c ∈ Fˣ` and a function `k ∈ K(E)` with
```
φ^* g_T = c · (g_U · ([ℓ]^* k)),     U = picDual φ T = φ̂ T.
```
This is exactly the `hfact` hypothesis of `weilPairing_adjoint_core` / `weilPairing_adjoint_picDual`.

Proof. `hfact_projectiveDivisorOf_eq` gives `div(φ^* g_T) = div(g_U · ([ℓ]^* k₀))` for the
Abel–Jacobi function `k₀` of `hpd`; two functions with the same projective divisor differ by a
nonzero constant `c` (`const_unit_of_projectiveDivisorOf_eq_zero`), giving `hfact` with `k := k₀`. -/
theorem hfact_of_picDualDivisorClass (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : ProjOrdTransport φ)
    (hcomm : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hpd : PicDualDivisorClass W φ ch hinj hfin)
    (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    ∃ (c : F) (k : KE), c ≠ 0 ∧
      φ.pullback (weilFunction W ℓ hℓ T hT) =
        algebraMap F KE c *
          (weilFunction W ℓ hℓ ((φ.picDual ch hinj hfin) T)
              (by rw [← map_zsmul, hT, map_zero]) *
            (mulByInt W.toAffine ℓ).pullback k) := by
  haveI : IsDedekindDomain (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  have hU : ℓ • (φ.picDual ch hinj hfin) T = 0 := by rw [← map_zsmul, hT, map_zero]
  -- The Abel–Jacobi function `k₀` of the `picDual` divisor-class identity, and its divisor.
  obtain ⟨k₀, hk₀_ne, hk₀_div⟩ := hpd T
  -- The key divisor equality.
  have hdiv_key := hfact_projectiveDivisorOf_eq W ℓ hℓ φ hφ hcomm hT hU
    (k₀ := k₀) hk₀_ne hk₀_div
  -- nonzero-ness of the two sides.
  have hgU_ne : weilFunction W ℓ hℓ ((φ.picDual ch hinj hfin) T) hU ≠ 0 :=
    weilFunction_ne_zero W ℓ hℓ _ hU
  have hu_ne : (mulByInt W.toAffine ℓ).pullback k₀ ≠ 0 :=
    fun h0 ↦ hk₀_ne ((mulByInt W.toAffine ℓ).pullback_injective (h0.trans (map_zero _).symm))
  have hpb_ne : φ.pullback (weilFunction W ℓ hℓ T hT) ≠ 0 :=
    fun h0 ↦ weilFunction_ne_zero W ℓ hℓ T hT
      (φ.pullback_injective (h0.trans (map_zero _).symm))
  set rhs := weilFunction W ℓ hℓ ((φ.picDual ch hinj hfin) T) hU *
    (mulByInt W.toAffine ℓ).pullback k₀ with hrhs
  have hrhs_ne : rhs ≠ 0 := mul_ne_zero hgU_ne hu_ne
  -- Same divisor ⟹ the ratio is a nonzero constant `c`.
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

/-! ### The unconditional separable adjoint (modulo the isolated `PicDualDivisorClass`)

Wiring `hfact_of_picDualDivisorClass` into `weilPairing_adjoint_core` (Silverman III.8.2): the
existential factorisation produced above is exactly the `hfact` hypothesis, so the adjoint
`e_ℓ(φS, T) = e_ℓ(S, φ̂T)` follows from the geometric witnesses `hφ`/`hcomm` and the *single* carried
residual `hpd : PicDualDivisorClass φ` (the projective-form `picDual` divisor-class identity,
Silverman III.6.1b) — together with the translation covariance `hcomm'` of `weilPairing_adjoint_core`. -/

/-- **The separable adjoint, `hfact` discharged via `PicDualDivisorClass`** (Silverman III.8.2). For
a separable isogeny `φ` of `E`, the `picDual` data `ch`/`hinj`/`hfin`, the divisor-pullback
functoriality `hφ : ProjOrdTransport φ`, the commutation `[ℓ] ∘ φ = φ ∘ [ℓ]` (`hcommφ`), the
translation covariance `hcomm'` (`weilPairing_adjoint_core`'s `hcomm`), and the **single carried
residual** `hpd : PicDualDivisorClass φ` (the projective `picDual` divisor-class identity, III.6.1b),
the Weil pairing satisfies the adjoint relation `e_ℓ(φS, T) = e_ℓ(S, φ̂T)` with `φ̂ = picDual φ`.

The `hfact` hypothesis of `weilPairing_adjoint_core` is supplied by `hfact_of_picDualDivisorClass`
(extracting the constant `c` and function `k`). This is the form `weilPairing_scaling_of_genuine`
consumes: `hfact` is no longer a bare hypothesis but is *derived* from the geometric data + the one
isolated divisor-class identity. -/
theorem weilPairing_adjoint_of_picDualDivisorClass (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (hpd : PicDualDivisorClass W φ ch hinj hfin)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0)
    (hcomm' : translateAlgEquivOfPoint W S (φ.pullback (weilFunction W ℓ hℓ T hT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) (weilFunction W ℓ hℓ T hT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT =
      weilPairing W ℓ hℓ S ((φ.picDual ch hinj hfin) T) hS
        (by rw [← map_zsmul, hT, map_zero]) := by
  obtain ⟨c, k, _hc0, hfact⟩ :=
    hfact_of_picDualDivisorClass W ℓ hℓ φ hφ hcommφ ch hinj hfin hpd T hT
  exact weilPairing_adjoint_picDual W ℓ hℓ φ ch hinj hfin S T hS hT hφS hcomm' hfact

end HasseWeil.WeilPairing
