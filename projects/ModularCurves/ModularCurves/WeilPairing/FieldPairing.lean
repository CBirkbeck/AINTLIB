/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.WeilPairing.PairingNondeg
import HasseWeil.HasseBound.WeilPairing.PairingProps
import ModularCurves.WeilPairing.Basic

/-!
# The Weil pairing at a geometric fibre (DS4 milestone M1a)

The DS4 register (`WeilPairing/Basic.lean`) posits the pairing
`e_N : E[N] ×_S E[N] ⟶ μ_{N,S}` over an arbitrary base together with its specification
list. Over an **algebraically closed field** the pairing is not a register at all: AINTLIB
already contains a sorry-free construction — `HasseWeil.WeilPairing.weilPairing`
(`projects/HasseWeil/…/HasseBound/WeilPairing/Pairing.lean`, Silverman AEC III.8) — with
bilinearity, alternation, `μ_N`-valuedness and nondegeneracy proved.

This file repackages that construction in exactly the shape of the DS4 specification list,
i.e. as a `{u : F // u ^ N = 1}`-valued pairing of `N`-torsion points indexed by a
**natural** `N`, so that it can be compared against `weilPairingEval` fibre by fibre (the
`T-C4` normalisation pin) and used as the input of the field-level DS4 construction (M1).

Everything here is a thin, sorry-free wrapper: no new mathematical content beyond the
`ℤ`-indexed → `ℕ`-indexed translation and the `μ_N`-bundling.
-/

universe u

open WeierstrassCurve HasseWeil.WeilPairing

namespace ModularCurves

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

section

variable (N : ℕ) (hN : (N : F) ≠ 0)

include hN in
private theorem fieldWeil_intCast_ne_zero : ((N : ℤ) : F) ≠ 0 := by
  simpa using hN

/-- **(M1a)** The Weil pairing of two `N`-torsion points of `W(F)`, `F` algebraically
closed, bundled as an `N`-th root of unity. This is `HasseWeil.WeilPairing.weilPairing`
with the index cast to `ℕ` and the `μ_N`-membership attached. -/
noncomputable def fieldWeilPairing (P Q : W.toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) : { u : F // u ^ N = 1 } :=
  ⟨weilPairing W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) P Q hP hQ, by
    have h := weilPairing_pow_eq_one W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) P Q hP hQ
    rwa [Int.natAbs_natCast] at h⟩

@[simp] theorem fieldWeilPairing_val (P Q : W.toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (fieldWeilPairing W N hN P Q hP hQ : F) =
      weilPairing W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) P Q hP hQ := rfl

/-- The pairing depends only on the points (the torsion proofs are propositional). -/
theorem fieldWeilPairing_congr {P P' Q Q' : W.toAffine.Point}
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (hP' : (N : ℤ) • P' = 0) (hQ' : (N : ℤ) • Q' = 0)
    (h₁ : P = P') (h₂ : Q = Q') :
    (fieldWeilPairing W N hN P Q hP hQ : F) =
      (fieldWeilPairing W N hN P' Q' hP' hQ' : F) := by
  subst h₁
  subst h₂
  rfl

/-- **(M1a, the DS4 `T-C2` shape)** Bilinearity in the first slot. -/
theorem fieldWeilPairing_mul_left (P P' Q : W.toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hP' : (N : ℤ) • P' = 0) (hQ : (N : ℤ) • Q = 0)
    (hPP' : (N : ℤ) • (P + P') = 0) :
    (fieldWeilPairing W N hN (P + P') Q hPP' hQ : F) =
      (fieldWeilPairing W N hN P Q hP hQ : F) *
        (fieldWeilPairing W N hN P' Q hP' hQ : F) :=
  weilPairing_mul_left W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) P P' Q hP hP' hQ hPP'

/-- **(M1a, the DS4 `T-C2` shape)** Bilinearity in the second slot. -/
theorem fieldWeilPairing_mul_right (P Q Q' : W.toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) (hQ' : (N : ℤ) • Q' = 0)
    (hQQ' : (N : ℤ) • (Q + Q') = 0) :
    (fieldWeilPairing W N hN P (Q + Q') hP hQQ' : F) =
      (fieldWeilPairing W N hN P Q hP hQ : F) *
        (fieldWeilPairing W N hN P Q' hP hQ' : F) :=
  weilPairing_mul_right W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) P Q Q' hP hQ hQ' hQQ'

/-- **(M1a, the DS4 `T-C3` shape)** The pairing is alternating. -/
theorem fieldWeilPairing_self (P : W.toAffine.Point) (hP : (N : ℤ) • P = 0) :
    (fieldWeilPairing W N hN P P hP hP : F) = 1 :=
  weilPairing_alternating W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) P hP

/-- **(M1a, the DS4 `T-C3` shape)** Antisymmetry. -/
theorem fieldWeilPairing_antisymm (P Q : W.toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (fieldWeilPairing W N hN P Q hP hQ : F) *
        (fieldWeilPairing W N hN Q P hQ hP : F) = 1 :=
  weilPairing_antisymm W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) P Q hP hQ

/-- **(M1a, the DS4 nondegeneracy spec)** A point pairing trivially with everything is
zero. -/
theorem fieldWeilPairing_eq_zero_of_forall (Q : W.toAffine.Point) (hQ : (N : ℤ) • Q = 0)
    (h : ∀ (P : W.toAffine.Point) (hP : (N : ℤ) • P = 0),
      (fieldWeilPairing W N hN P Q hP hQ : F) = 1) :
    Q = 0 :=
  weilPairing_nondegenerate W (N : ℤ) (fieldWeil_intCast_ne_zero N hN) Q hQ
    (fun P hP => h P hP)

end

end ModularCurves
