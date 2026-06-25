/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PairingProps
import HasseWeil.Pic0.PicDual

/-!
# The separable adjoint and the symplectic scaling of the Weil pairing (Silverman III.8.2/8.6.1)

This file proves, for the finite-level Weil pairing `e_ℓ : E[ℓ] × E[ℓ] → F` over an
algebraically closed field `F`, two structural identities that the determinant endgame
(Prop 8.6) consumes:

* `weilPairing_adjoint_picDual` — **the separable adjoint** (Silverman III.8.2,
  Prop 8.2): `e_ℓ(φS, T) = e_ℓ(S, φ̂T)` with `φ̂ = picDual φ` (the Pic⁰ dual
  proved in `HasseWeil/Pic0/PicDual.lean`), for a **separable** isogeny `φ : E → E`.
* `weilPairing_scaling` — **the symplectic scaling** (Silverman III.8.6.1):
  `e_ℓ(φS, φT) = e_ℓ(S, T) ^ (deg φ)`, the per-isogeny identity that, combined
  with the universal `φᵀ J φ = (det φ)·J`
  (`PairingDet.det_eq_of_alternating_scaling`), forces `det(φ|E[ℓ]) = deg φ`.

## The adjoint (Silverman III.8.2)

For SEPARABLE `φ`, the divisor pullback `φ^*((T)−(O)) = Σ_{φP=T}(P) − Σ_{φP=O}(P)`
is **multiplicity-free**, so the Pic⁰ dual `φ̂ = picDual φ` automatically realises
the σ-bridge `(φ̂T) − (O) ∼ φ^*((T)−(O))` (the divisor-class identity defining
`picDual`). Concretely, write `g_T = weilFunction W ℓ T`
(`div g_T = [ℓ]^*(T) − [ℓ]^*(O)`). Two geometric facts about a separable isogeny
produce the adjoint:

* **(divisor factorisation)** `φ^* g_T = c · g_{φ̂T} · ([ℓ]^* k)` for a constant
  `c ∈ F^×` and some `k ∈ K(E)`. Indeed
  `div(φ^* g_T) = φ^*(div g_T) = φ^*([ℓ]^*((T)−(O))) =
  [ℓ]^*(φ^*((T)−(O)))` (using `[ℓ] ∘ φ = φ ∘ [ℓ]`), and
  `φ^*((T)−(O)) = (φ̂T) − (O) + div k` (the `picDual` divisor-class identity,
  automatic for separable `φ`), so `div(φ^* g_T) = div(g_{φ̂T}) + div([ℓ]^* k)`.
  The divisor of the ratio vanishes, giving the constant `c`.
* **(translation covariance)** `τ_S^*(φ^* z) = φ^*(τ_{φS}^* z)`, the function-field
  shadow of the group-hom commutation `φ ∘ (·+S) = (·+φS) ∘ φ`.

Applying `τ_S` (`S ∈ E[ℓ]`) to the factorisation — `τ_S` fixes `c` and the covariant
factor `[ℓ]^* k` (`PairingProps.translate_pullback_fixed`, the `S ∈ E[ℓ]` invariance)
— and using the pairing relations `τ_{φS}^* g_T = e_ℓ(φS,T)·g_T` and
`τ_S^* g_{φ̂T} = e_ℓ(S,φ̂T)·g_{φ̂T}` collapses to
`e_ℓ(φS,T)·(φ^* g_T) = e_ℓ(S,φ̂T)·(φ^* g_T)`. Cancelling `φ^* g_T ≠ 0` gives the
adjoint.

The two geometric facts are carried as per-isogeny hypotheses, exactly as the divisor-pullback
functoriality (`DivisorPullback.ProjOrdTransport`) and the `κ`-naturality (`PicDual.Naturality`)
are throughout the project: an abstract `Isogeny` stores its `pullback` and `toAddMonoidHom` as
independent data, so the geometric link is supplied per isogeny (it is the separability content of
Silverman III.8.2 / the multiplicity-free pullback).

## The scaling (Silverman III.8.6.1)

`e_ℓ(φS, φT) = e_ℓ(S, φ̂(φT)) = e_ℓ(S, [deg φ]T) = e_ℓ(S, T) ^ (deg φ)`:
the adjoint, then `picDual φ ∘ φ = [deg φ]` (`PicDual.picDual_comp_toAddMonoidHom`),
then bilinearity in the second slot (`weilPairing_nsmul_right`, the `nsmul`→power law).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.2 (Prop 8.2, the adjoint), III.8.6
  (Prop 8.6, `det φ_ℓ = deg φ` via the symplectic scaling).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

section SecondSlot

variable [IsAlgClosed F]

/-- Equal second arguments give equal Weil-pairing values. -/
theorem weilPairing_congr_right (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    {S T T' : W.toAffine.Point} (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hT' : ℓ • T' = 0) (h : T = T') :
    weilPairing W ℓ hℓ S T hS hT = weilPairing W ℓ hℓ S T' hS hT' := by
  subst h
  rfl

/-- The Weil pairing is trivial on `O` in the second slot. -/
theorem weilPairing_refl_right (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S : W.toAffine.Point) (hS : ℓ • S = 0) (h0 : ℓ • (0 : W.toAffine.Point) = 0) :
    weilPairing W ℓ hℓ S 0 hS h0 = 1 := by
  have hsum : ℓ • ((0 : W.toAffine.Point) + 0) = 0 := by
    simp
  have hbil := weilPairing_mul_right W ℓ hℓ S 0 0 hS h0 h0 hsum
  rw [weilPairing_congr_right W ℓ hℓ hS hsum h0 (add_zero _)] at hbil
  have hne := weilPairing_ne_zero W ℓ hℓ S 0 hS h0
  exact (mul_right_cancel₀ hne (by simpa using hbil)).symm

/-- `ℓ • (n • T) = 0` whenever `ℓ • T = 0` (the scalars commute). -/
theorem smul_nsmul_eq_zero_right (ℓ : ℤ) (T : W.toAffine.Point) (hT : ℓ • T = 0)
    (n : ℕ) : ℓ • (n • T) = 0 := by
  rw [smul_comm, hT, smul_zero]

/-- Power form of bilinearity in the second slot. -/
theorem weilPairing_nsmul_right (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (n : ℕ) (h_ns : ℓ • (n • T) = 0) :
    weilPairing W ℓ hℓ S (n • T) hS h_ns = (weilPairing W ℓ hℓ S T hS hT) ^ n := by
  induction n with
  | zero =>
    rw [weilPairing_congr_right W ℓ hℓ hS h_ns
      (by simp : ℓ • (0 : W.toAffine.Point) = 0) (zero_smul ℕ T), pow_zero]
    exact weilPairing_refl_right W ℓ hℓ S hS _
  | succ k ih =>
    have hk : ℓ • (k • T) = 0 := smul_nsmul_eq_zero_right W ℓ T hT k
    have hsum : ℓ • (k • T + T) = 0 := by rw [smul_add, hk, hT, add_zero]
    rw [weilPairing_congr_right W ℓ hℓ hS h_ns hsum (succ_nsmul T k),
      weilPairing_mul_right W ℓ hℓ S (k • T) T hS hk hT hsum, ih hk, pow_succ]

end SecondSlot

section Adjoint

variable [IsAlgClosed F]

/-- Core separable-adjoint identity from translation covariance and divisor factorisation. -/
theorem weilPairing_adjoint_core (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine)
    (S T U : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) (hU : ℓ • U = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0)
    (hcomm : translateAlgEquivOfPoint W S (φ.pullback (weilFunction W ℓ hℓ T hT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) (weilFunction W ℓ hℓ T hT)))
    {c : F} {k : KE}
    (hfact : φ.pullback (weilFunction W ℓ hℓ T hT) =
      algebraMap F KE c *
        (weilFunction W ℓ hℓ U hU * (mulByInt W.toAffine ℓ).pullback k)) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT = weilPairing W ℓ hℓ S U hS hU := by
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at hℓ
  set gT := weilFunction W ℓ hℓ T hT with hgT
  set gU := weilFunction W ℓ hℓ U hU with hgU
  set u : KE := (mulByInt W.toAffine ℓ).pullback k with hu
  have hgT_ne : gT ≠ 0 := weilFunction_ne_zero W ℓ hℓ T hT
  have hpb_ne : φ.pullback gT ≠ 0 :=
    fun h0 ↦ hgT_ne (φ.pullback_injective (h0.trans (map_zero _).symm))
  have heval1 : translateAlgEquivOfPoint W S (φ.pullback gT) =
      algebraMap F KE
        (weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT) * φ.pullback gT := by
    rw [hcomm, weilPairing_translate W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT, map_mul,
      φ.pullback.commutes]
  have hu_fixed : translateAlgEquivOfPoint W S u = u := translate_pullback_fixed W ℓ hℓ0 S hS k
  have heval2 : translateAlgEquivOfPoint W S (φ.pullback gT) =
      algebraMap F KE (weilPairing W ℓ hℓ S U hS hU) * φ.pullback gT := by
    rw [hfact, map_mul, map_mul, (translateAlgEquivOfPoint W S).commutes,
      weilPairing_translate W ℓ hℓ S U hS hU, hu_fixed]
    ring
  have hkey :
      algebraMap F KE
        (weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT) * φ.pullback gT =
      algebraMap F KE (weilPairing W ℓ hℓ S U hS hU) * φ.pullback gT := by
    rw [← heval1, heval2]
  exact (algebraMap F KE).injective (mul_right_cancel₀ hpb_ne hkey)

/-- Separable adjoint identity via `picDual`. -/
theorem weilPairing_adjoint_picDual (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine)
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin :
      @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0)
    (hcomm : translateAlgEquivOfPoint W S (φ.pullback (weilFunction W ℓ hℓ T hT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) (weilFunction W ℓ hℓ T hT)))
    {c : F} {k : KE}
    (hfact : φ.pullback (weilFunction W ℓ hℓ T hT) =
      algebraMap F KE c *
        (weilFunction W ℓ hℓ ((φ.picDual ch hinj hfin) T)
            (by rw [← map_zsmul, hT, map_zero]) *
          (mulByInt W.toAffine ℓ).pullback k)) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT =
      weilPairing W ℓ hℓ S ((φ.picDual ch hinj hfin) T) hS
        (by rw [← map_zsmul, hT, map_zero]) :=
  weilPairing_adjoint_core W ℓ hℓ φ S T ((φ.picDual ch hinj hfin) T) hS hT
    (by rw [← map_zsmul, hT, map_zero]) hφS hcomm hfact

end Adjoint

section Scaling

variable [IsAlgClosed F]

/-- Symplectic scaling of the Weil pairing under a separable isogeny. -/
theorem weilPairing_scaling (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine)
    (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin :
      @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hφT : ℓ • φ.toAddMonoidHom T = 0)
    (hcomm : translateAlgEquivOfPoint W S
        (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
        (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT)))
    {c : F} {k : KE}
    (hfact : φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT) =
      algebraMap F KE c *
        (weilFunction W ℓ hℓ ((φ.picDual ch hinj hfin) (φ.toAddMonoidHom T))
            (by rw [← map_zsmul, hφT, map_zero]) *
          (mulByInt W.toAffine ℓ).pullback k))
    (hdual : ∀ P : W.toAffine.Point,
      (φ.picDual ch hinj hfin) (φ.toAddMonoidHom P) = (φ.degree : ℤ) • P) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom T) hφS hφT =
      weilPairing W ℓ hℓ S T hS hT ^ φ.degree := by
  have hφφT_tor : ℓ • (φ.picDual ch hinj hfin) (φ.toAddMonoidHom T) = 0 := by
    rw [← map_zsmul, hφT, map_zero]
  rw [weilPairing_adjoint_picDual W ℓ hℓ φ ch hinj hfin S (φ.toAddMonoidHom T) hS hφT hφS
    hcomm hfact]
  have hdegN_tor : ℓ • ((φ.degree : ℕ) • T) = 0 :=
    smul_nsmul_eq_zero_right W ℓ T hT φ.degree
  rw [weilPairing_congr_right W ℓ hℓ hS hφφT_tor hdegN_tor
    ((hdual T).trans (natCast_zsmul T φ.degree))]
  exact weilPairing_nsmul_right W ℓ hℓ S T hS hT φ.degree hdegN_tor

end Scaling

end HasseWeil.WeilPairing
