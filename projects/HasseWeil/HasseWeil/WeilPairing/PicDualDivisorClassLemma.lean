/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.HfactLemma

/-!
# Discharging `PicDualDivisorClass` via Abel (Silverman III.6.1b)

This file **discharges** the isolated residual `PicDualDivisorClass φ` of
`HasseWeil.WeilPairing.HfactLemma` — the projective-divisor form of Silverman III.6.1b
`φ^*((T) − (O)) ∼ (φ̂ T) − (O)` (with `φ̂ = picDual φ`) — via the **Abel–Jacobi σ-machinery**,
turning the separable Weil-pairing adjoint into an *unconditional* consequence of the standard
per-isogeny data (the same `Naturality`/surjectivity/tower witnesses carried throughout the
project), with **no** new geometric input.

## The Abel route (Silverman III.3.5: degree-0 + `σ = O` ⟺ principal)

`PicDualDivisorClass φ T` asks that
```
Δ_T := pullbackDivisor φ ((T) − (O)) − ((φ̂ T) − (O))
```
be principal.  By Abel (`projIsPrincipal_of_degZero_of_sigma_eq_zero`, char-free, shipped) a
degree-`0` divisor is principal as soon as its `σ`-image (group sum `projectiveDivisorSum`) is `O`.
We verify both:

1. **`deg Δ_T = 0`.**  `pullbackDivisor φ ((T) − (O)) = φ^*(T) − φ^*(O)` is the fibre-difference
   `pullbackDiv φ T − pullbackDiv φ O` (`pullbackDivisor_kappaDivisor_eq`), each fibre summand
   having degree `#ker φ` (`degree_pullbackDiv`, given a preimage `P₀` of `T`); and
   `deg((φ̂ T) − (O)) = 0` (`kappaDivisor_degree`).  So `deg Δ_T = (#ker − #ker) − 0 = 0`.

2. **`σ Δ_T = O`** — the **σ-point-identity** `σ(pullbackDivisor φ ((T) − (O))) = φ̂ T`.  The
   σ-bridge `sigma_pullbackDiv_sub` (Silverman III.6.1b, pure kernel-coset group theory) gives
   `σ(φ^*(T) − φ^*(O)) = #ker(φ) · P₀` for any `P₀` with `φ P₀ = T`.  This equals `φ̂ T` precisely
   by the **dual relation `φ̂ ∘ φ = [#ker φ]`** (Silverman III.6.2(a)) evaluated at `P₀`
   (`φ P₀ = T`): `φ̂ T = φ̂(φ P₀) = #ker(φ) · P₀`.  Then `σ((φ̂ T) − (O)) = φ̂ T`
   (`projectiveDivisorSum_kappaDivisor`), so `σ Δ_T = φ̂ T − φ̂ T = O`.

So the Abel half (`σ = O ⟹ principal`) is discharged **completely char-free**, and the
σ-point-identity is **reduced exactly** to the dual relation `φ̂ ∘ φ = [#ker φ]`.

## The carried residual is the *standard* III.6.2(a) dual relation — no new content

The single hypothesis `picDualDivisorClass_of_picDualComp` consumes is the dual relation
`hpdc : (picDual φ).comp φ.toAddMonoidHom = [Nat.card φ.ker]` — Silverman III.6.2(a) `φ̂ ∘ φ = [deg]`
(with `#ker = deg` for separable `φ` over `K̄`).  This is **already shipped** as
`Isogeny.picDual_comp_toAddMonoidHom_of_surjective` from the project's standard per-isogeny
witnesses (the III.3.4 `Naturality` `hnat`, surjectivity of `φ̂`/`φ`, and the function-field tower),
*identical* to how `ProjOrdTransport`/`Naturality` are carried elsewhere.  For `φ = [ℓ]` we
instantiate it directly (`picDualDivisorClass_mulByInt`), using the shipped `#ker[ℓ] = ℓ²`
(`nat_card_mulByInt_ker`) and the point-surjectivity of `[ℓ]` (`mulByInt_point_surjective`).

This **completes** III.6.1b: the separable adjoint `weilPairing_adjoint_of_picDualDivisorClass`
needs no bare divisor-class hypothesis — only the geometric witnesses plus the standard dual
relation, both of which the project already supplies per isogeny.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.3.5 (Abel: degree-0 ∧ `σ = O` ⟺ principal),
  III.6.1(b) (`φ̂ = κ⁻¹ ∘ φ^* ∘ κ`), III.6.2(a) (`φ̂ ∘ φ = [deg φ]`).
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

/-! ### Step 0 — `pullbackDivisor φ ((T) − (O))` is the fibre difference `φ^*(T) − φ^*(O)`

`kappaDivisor T = (T) − (O)` is the difference of two `single`s, so its fibre-pullback distributes
into `pullbackDiv φ T − pullbackDiv φ O` (`∞.toAffinePoint = O`).  This is the general-`φ` analogue
of `HfactLemma.pullbackDivisor_kappaDivisor` (which is stated for `[ℓ]`); the proof is identical and
field-agnostic. -/

/-- **`pullbackDivisor φ ((T) − (O)) = φ^*(T) − φ^*(O)`** (general isogeny / point map). The
fibre-pullback of `kappaDivisor T = (T) − (O)` is the multiplicity-free fibre difference
`pullbackDiv φ T − pullbackDiv φ O`. -/
theorem pullbackDivisor_kappaDivisor_eq
    (f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker) (T : W.toAffine.Point) :
    pullbackDivisor (W := W.toAffine) f hf (Curves.kappaDivisor W.toAffine T) =
      pullbackDiv (W := W.toAffine) f hf T - pullbackDiv (W := W.toAffine) f hf 0 := by
  rw [Curves.kappaDivisor, ← pullbackDivisorHom_apply, map_sub, pullbackDivisorHom_apply,
    pullbackDivisorHom_apply, pullbackDivisor_single, pullbackDivisor_single, one_smul, one_smul,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    ProjectiveSmoothPoint.toAffinePoint_infinity]

/-! ### Step 1 — degree and σ of `pullbackDivisor φ ((T) − (O))`

Both read off the fibre-difference form via the shipped per-fibre facts `degree_pullbackDiv`
(degree `#ker`) and `sigma_pullbackDiv_sub` (the III.6.1b σ-bridge `σ = #ker · P₀`). They need a
preimage `P₀` of `T` under `φ` — supplied over `K̄` by surjectivity of `φ`. -/

/-- **`deg(pullbackDivisor φ ((T) − (O))) = 0`** given a preimage `P₀` of `T`. Both fibre summands
`φ^*(T)`, `φ^*(O)` have degree `#ker φ` (`degree_pullbackDiv`), so the difference has degree `0`. -/
theorem degree_pullbackDivisor_kappaDivisor
    (f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker)
    {T P₀ : W.toAffine.Point} (hP₀ : f P₀ = T) :
    (pullbackDivisor (W := W.toAffine) f hf (Curves.kappaDivisor W.toAffine T)).degree = 0 := by
  rw [pullbackDivisor_kappaDivisor_eq, ← Curves.ProjectiveDivisor.degreeHom_apply, map_sub,
    Curves.ProjectiveDivisor.degreeHom_apply, Curves.ProjectiveDivisor.degreeHom_apply,
    degree_pullbackDiv (W := W.toAffine) f hf hP₀,
    degree_pullbackDiv (W := W.toAffine) f hf (map_zero f), sub_self]

/-- **The σ-point-identity, geometric half** (Silverman III.6.1b σ-bridge):
`σ(pullbackDivisor φ ((T) − (O))) = #ker(φ) · P₀` for any `P₀` with `φ P₀ = T`. Read off the
fibre-difference form via `sigma_pullbackDiv_sub`. -/
theorem sigma_pullbackDivisor_kappaDivisor
    (f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker)
    {T P₀ : W.toAffine.Point} (hP₀ : f P₀ = T) :
    Curves.projectiveDivisorSum W.toAffine
        (pullbackDivisor (W := W.toAffine) f hf (Curves.kappaDivisor W.toAffine T)) =
      Nat.card f.ker • P₀ := by
  rw [pullbackDivisor_kappaDivisor_eq, Curves.projectiveDivisorSum_sub,
    sigma_pullbackDiv_sub (W := W.toAffine) f hf hP₀]

/-! ### Step 2 — the σ-point-identity from the dual relation `φ̂ ∘ φ = [#ker φ]`

Combining the geometric half (`σ = #ker · P₀`) with the **dual relation** `φ̂ ∘ φ = [#ker φ]`
(Silverman III.6.2(a)) evaluated at the preimage `P₀` (`φ P₀ = T`) gives the full σ-point-identity
`σ(pullbackDivisor φ ((T) − (O))) = φ̂ T`. -/

/-- **The σ-point-identity** `σ(pullbackDivisor φ ((T) − (O))) = φ̂ T` (Silverman III.6.1b/III.6.2(a)).
From the σ-bridge `σ = #ker(φ) · P₀` (`sigma_pullbackDivisor_kappaDivisor`) and the dual relation
`hpdc : φ̂ ∘ φ = [#ker φ]` at `P₀` (`φ P₀ = T`): `φ̂ T = φ̂(φ P₀) = #ker(φ) · P₀`. -/
theorem sigma_pullbackDivisor_kappaDivisor_eq_picDual
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hpdc : (φ.picDual ch hinj hfin).comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    {T P₀ : W.toAffine.Point} (hP₀ : φ.toAddMonoidHom P₀ = T) :
    Curves.projectiveDivisorSum W.toAffine
        (pullbackDivisor (W := W.toAffine) φ.toAddMonoidHom inferInstance
          (Curves.kappaDivisor W.toAffine T)) =
      (φ.picDual ch hinj hfin) T := by
  rw [sigma_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance hP₀]
  -- `φ̂ T = φ̂ (φ P₀) = [#ker φ] P₀ = #ker(φ) • P₀`.
  have hval := DFunLike.congr_fun hpdc P₀
  rw [AddMonoidHom.comp_apply, hP₀, mulByInt_apply] at hval
  rw [hval, natCast_zsmul]

/-! ### Step 3 — `PicDualDivisorClass φ` from the dual relation (the main discharge)

With the degree-0 fact and the σ-point-identity in hand, Abel
(`projIsPrincipal_of_degZero_of_sigma_eq_zero`, char-free) finishes: `Δ_T` is principal. The only
hypotheses are the dual relation `φ̂ ∘ φ = [#ker φ]` and the surjectivity of `φ` on points (to
furnish the preimage `P₀`). -/

/-- **`PicDualDivisorClass φ` from the dual relation `φ̂ ∘ φ = [#ker φ]` (Silverman III.6.1b).**

For an isogeny `φ` with `picDual` data `ch`/`hinj`/`hfin`, the dual relation
`hpdc : φ̂ ∘ φ = [#ker φ]` (Silverman III.6.2(a)), and surjectivity of `φ` on points
`hsurj` (automatic over `K̄`, Silverman III.4.10a), the projective divisor-class identity
`PicDualDivisorClass φ` holds: `pullbackDivisor φ ((T) − (O)) ∼ (φ̂ T) − (O)` for every `T`.

Proof: for each `T`, pick a preimage `P₀` (`hsurj`); the difference
`Δ_T = pullbackDivisor φ ((T) − (O)) − ((φ̂ T) − (O))` has degree `0`
(`degree_pullbackDivisor_kappaDivisor` + `kappaDivisor_degree`) and `σ Δ_T = O`
(σ-point-identity `sigma_pullbackDivisor_kappaDivisor_eq_picDual` + `projectiveDivisorSum_kappaDivisor`),
so it is principal by Abel (`projIsPrincipal_of_degZero_of_sigma_eq_zero`). **Char-free** (the Abel
half needs only `[IsIntegrallyClosed CoordinateRing]`). -/
theorem picDualDivisorClass_of_picDualComp
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hpdc : (φ.picDual ch hinj hfin).comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hsurj : Function.Surjective φ.toAddMonoidHom) :
    PicDualDivisorClass W φ ch hinj hfin := by
  intro T
  obtain ⟨P₀, hP₀⟩ := hsurj T
  refine projIsPrincipal_of_degZero_of_sigma_eq_zero (W := W.toAffine) _ ?_ ?_
  · -- degree 0: `(#ker − #ker) − 0`.
    rw [← Curves.ProjectiveDivisor.degreeHom_apply, map_sub,
      Curves.ProjectiveDivisor.degreeHom_apply, Curves.ProjectiveDivisor.degreeHom_apply,
      degree_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance hP₀,
      Curves.kappaDivisor_degree, sub_self]
  · -- `σ = φ̂ T − φ̂ T = 0`.
    rw [Curves.projectiveDivisorSum_sub,
      sigma_pullbackDivisor_kappaDivisor_eq_picDual W φ ch hinj hfin hpdc hP₀,
      Curves.projectiveDivisorSum_kappaDivisor, sub_self]

/-! ### Step 4 — `PicDualDivisorClass φ` from the standard III.3.4/III.6.2(a) witnesses

The dual relation `φ̂ ∘ φ = [#ker φ]` is exactly the shipped
`Isogeny.picDual_comp_toAddMonoidHom_of_surjective` (giving `[finrank R R]`) once the kernel
cardinality is matched to the coordinate-ring rank, `#ker φ = finrank R R`. We package the discharge
of `PicDualDivisorClass` directly from the project's standard carried data: the III.3.4 naturality
`hnat`, surjectivity of `φ̂` and of `φ`, and the kernel-rank match `hcard`. -/

/-- **`PicDualDivisorClass φ` from the standard per-isogeny witnesses (Silverman III.6.1b).**

Given the III.3.4 naturality `hnat : φ.Naturality …`, surjectivity of the Pic⁰ dual `hsurjDual`
and of the point map `hsurj`, and the separable kernel-rank match
`hcard : #ker φ = finrank R R`, the projective divisor-class identity `PicDualDivisorClass φ` holds.

This is the form assembled purely from the project's *standard* carried isogeny data (identical to
`ProjOrdTransport`/`Naturality` usage elsewhere): the dual relation `φ̂ ∘ φ = [finrank R R]` is the
shipped `picDual_comp_toAddMonoidHom_of_surjective`, rewritten via `hcard` to `[#ker φ]` and fed to
`picDualDivisorClass_of_picDualComp`. -/
theorem picDualDivisorClass_of_naturality
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : φ.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (φ.picDual ch hinj hfin))
    (hsurj : Function.Surjective φ.toAddMonoidHom)
    (hcard : (Nat.card φ.toAddMonoidHom.ker : ℤ) =
      (letI := ch.toAlgebra;
        ((@Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
          ch.toAlgebra.toModule : ℕ) : ℤ))) :
    PicDualDivisorClass W φ ch hinj hfin := by
  refine picDualDivisorClass_of_picDualComp W φ ch hinj hfin ?_ hsurj
  rw [Isogeny.picDual_comp_toAddMonoidHom_of_surjective ch hinj hfin hnat hsurjDual]
  congr 2
  exact_mod_cast hcard.symm

/-! ### Step 5 — the `[ℓ]` instance: `PicDualDivisorClass [ℓ]` (Silverman III.6.1b for `[ℓ]`)

For `φ = [ℓ]` the kernel cardinality is the shipped `#ker[ℓ] = ℓ²` (`nat_card_mulByInt_ker`), so the
kernel-rank match in `picDualDivisorClass_of_naturality` reduces to `ℓ² = finrank R R`. Combined with
the standard per-`[ℓ]` `picDual` witnesses (III.3.4 naturality `hnat`, surjectivity of `[ℓ]̂` and of
the point map `[ℓ]`), `PicDualDivisorClass [ℓ]` is discharged outright.

Point-surjectivity of `[ℓ]` over `K̄` is the shipped `mulByInt_point_surjective`
(`WeilPairing/PairingNondeg.lean`, Silverman III.4.10a/b); it is taken here as the explicit
hypothesis `hsurj` to avoid importing that file (a sibling that re-declares
`pullbackDivisor_kappaDivisor`), so the caller supplies `mulByInt_point_surjective W ℓ hℓ`. -/

/-- **`PicDualDivisorClass [ℓ]` (Silverman III.6.1b for multiplication-by-`ℓ`).** For the separable
isogeny `φ = [ℓ]` (`(ℓ : F) ≠ 0`) and the carried `picDual` witnesses (`ch`/`hinj`/`hfin`, III.3.4
naturality `hnat`, surjectivity of `[ℓ]̂` `hsurjDual`, point-surjectivity of `[ℓ]` `hsurj`
(`= mulByInt_point_surjective W ℓ hℓ`, Silverman III.4.10a/b over `K̄`), and the separable
kernel-rank match `hcard : ℓ² = finrank R R`), the projective divisor-class identity
`PicDualDivisorClass [ℓ]` holds.

`#ker[ℓ] = ℓ²` is `nat_card_mulByInt_ker`; the rest is `picDualDivisorClass_of_naturality` with the
kernel cardinality rewritten through it. -/
theorem picDualDivisorClass_mulByInt [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    [Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker]
    (ch : (mulByInt W.toAffine ℓ).CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : (mulByInt W.toAffine ℓ).Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective ((mulByInt W.toAffine ℓ).picDual ch hinj hfin))
    (hsurj : Function.Surjective (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (hcard : (ℓ : ℤ) ^ 2 =
      (letI := ch.toAlgebra;
        ((@Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
          ch.toAlgebra.toModule : ℕ) : ℤ))) :
    PicDualDivisorClass W (mulByInt W.toAffine ℓ) ch hinj hfin := by
  refine picDualDivisorClass_of_naturality W (mulByInt W.toAffine ℓ) ch hinj hfin hnat hsurjDual
    hsurj ?_
  rw [nat_card_mulByInt_ker W ℓ hℓ]
  exact hcard

/-! ### The unconditional separable adjoint (III.6.1b residual eliminated)

`weilPairing_adjoint_of_picDualDivisorClass` (`HfactLemma`) needed the *bare* divisor-class
hypothesis `hpd : PicDualDivisorClass φ`. With `picDualDivisorClass_of_naturality` discharging it
from the project's standard III.3.4/III.6.2(a) witnesses, the separable adjoint
`e_ℓ(φS, T) = e_ℓ(S, φ̂T)` now holds with **no** divisor-class hypothesis — only the geometric
data already carried per isogeny. This is the brief's target: III.6.1b eliminated, the adjoint
unconditional modulo the standard isogeny witnesses. -/

variable [IsAlgClosed F]

/-- **The separable Weil-pairing adjoint, `PicDualDivisorClass` discharged (Silverman III.8.2).**

For a separable isogeny `φ` of `E`, the adjoint `e_ℓ(φS, T) = e_ℓ(S, φ̂T)` (`φ̂ = picDual φ`) holds
from the geometric witnesses `hφ : ProjOrdTransport φ`, the commutation `hcommφ : [ℓ] ∘ φ = φ ∘ [ℓ]`,
the translation covariance `hcomm'`, **and the standard III.3.4/III.6.2(a) dual data** (the III.3.4
naturality `hnat`, surjectivity of `φ̂` and of `φ`, and the separable kernel-rank match `hcard`).

This is `weilPairing_adjoint_of_picDualDivisorClass` with its bare `hpd : PicDualDivisorClass φ`
hypothesis *discharged* by `picDualDivisorClass_of_naturality` — so the adjoint no longer carries the
III.6.1b divisor-class identity as an axiom, only the standard per-isogeny witnesses. -/
theorem weilPairing_adjoint_of_naturality (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hφ : ProjOrdTransport φ)
    (hcommφ : (mulByInt W.toAffine ℓ).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ℓ).toAddMonoidHom)
    (hnat : φ.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (φ.picDual ch hinj hfin))
    (hsurj : Function.Surjective φ.toAddMonoidHom)
    (hcard : (Nat.card φ.toAddMonoidHom.ker : ℤ) =
      (letI := ch.toAlgebra;
        ((@Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
          ch.toAlgebra.toModule : ℕ) : ℤ)))
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0)
    (hcomm' : translateAlgEquivOfPoint W S (φ.pullback (weilFunction W ℓ hℓ T hT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) (weilFunction W ℓ hℓ T hT))) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT =
      weilPairing W ℓ hℓ S ((φ.picDual ch hinj hfin) T) hS
        (by rw [← map_zsmul, hT, map_zero]) :=
  weilPairing_adjoint_of_picDualDivisorClass W ℓ hℓ φ ch hinj hfin hφ hcommφ
    (picDualDivisorClass_of_naturality W φ ch hinj hfin hnat hsurjDual hsurj hcard)
    S T hS hT hφS hcomm'

end HasseWeil.WeilPairing
