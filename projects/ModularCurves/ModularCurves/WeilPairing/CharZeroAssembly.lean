/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.CharZeroDescent

/-!
# The DS4 Weil pairing from local descent data (T-C0e assembly)

`WeilPairing/CharZeroDescent.lean` proves the **descent half** of the Weil-pairing
construction gate-free: `weilPairingCharZero` turns a local pairing on a trivialising fppf
cover into the `S`-morphism `e_N : E[N] ×_S E[N] ⟶ μ_{N,S}`, and comes with restriction,
over-`S` and uniqueness specs.

This file bundles the three inputs it consumes into a single record
`WeilPairingLocalData`, so that the DS4 data-sorry (`EllipticCurve.weilPairing`,
`WeilPairing/Basic.lean`) reduces to **one** named existence statement: an elliptic curve
admits a Weil pairing as soon as it admits local pairing data. Everything downstream — the
`Y(ρ̄)` moduli functor's `PairingCompatAt`, hence `RhoLevelStructure`, hence
`rho_rigidNoeth` and `yRho_representable` — bottoms out here.

The remaining input is the *local* pairing on a cover trivialising `E[N]`: the point-level
`E[N] ≅ (ℤ/N)²` identification, which is the T-W7 (group-law-from-Weierstrass-charts)
convergence point. The determinant model it is fed is already in `CharZeroDescent`
(`detFun`, `detConstMor`, `detConstMor_gl2Both`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(T-C0e input)** Local descent data for the Weil pairing: a trivialising fppf cover
of the base, a pairing defined on the base change of `E[N] ×_S E[N]` along it, the cocycle
condition that makes it descend, and the over-`S` compatibility.

Bundling these makes the DS4 obligation a single existence statement — see
`nonempty_weilPairing_of_localData`. -/
structure WeilPairingLocalData (N : ℕ) [NeZero N] where
  /-- The trivialising cover's source. -/
  cover : Scheme.{u}
  /-- The trivialising fppf cover. -/
  p : cover ⟶ S
  /-- The cover is flat. -/
  flat : Flat p
  /-- The cover is locally of finite presentation. -/
  lfp : LocallyOfFinitePresentation p
  /-- The cover is surjective. -/
  surj : Surjective p
  /-- The local pairing on the base change of the Weil-pairing source. -/
  pairing : pullback (E.torsionSqπ N) p ⟶ muN S N
  /-- The cocycle condition: the two pullbacks to the kernel pair agree. -/
  cocycle :
    pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫
        pairing =
      pullback.snd (pullback.fst (E.torsionSqπ N) p)
        (pullback.fst (E.torsionSqπ N) p) ≫ pairing
  /-- The local pairing is a morphism over `S`. -/
  overBase : pairing ≫ muNπ S N = pullback.fst (E.torsionSqπ N) p ≫ E.torsionSqπ N

variable {E}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-C0e)** The Weil pairing determined by local descent data. -/
noncomputable def WeilPairingLocalData.toPairing {N : ℕ} [NeZero N]
    (d : E.WeilPairingLocalData N) :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N :=
  haveI := d.flat
  haveI := d.lfp
  haveI := d.surj
  E.weilPairingCharZero N d.p d.pairing d.cocycle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-C0e spec)** The descended pairing is a morphism over `S` — the DS4 specification
`weilPairing_over`. -/
theorem WeilPairingLocalData.toPairing_over {N : ℕ} [NeZero N]
    (d : E.WeilPairingLocalData N) :
    d.toPairing ≫ muNπ S N = E.torsionSqπ N :=
  haveI := d.flat
  haveI := d.lfp
  haveI := d.surj
  E.weilPairingCharZero_over N d.p d.pairing d.cocycle d.overBase

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-C0e spec)** The descended pairing restricts to the local one. -/
theorem WeilPairingLocalData.toPairing_restrict {N : ℕ} [NeZero N]
    (d : E.WeilPairingLocalData N) :
    haveI := d.flat
    haveI := d.lfp
    haveI := d.surj
    pullback.fst (E.torsionSqπ N) d.p ≫ d.toPairing = d.pairing :=
  haveI := d.flat
  haveI := d.lfp
  haveI := d.surj
  E.weilPairingCharZero_restrict N d.p d.pairing d.cocycle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-C0e, THE DS4 REDUCTION)** An elliptic curve admits a Weil pairing — a morphism
`E[N] ×_S E[N] ⟶ μ_{N,S}` over `S` — as soon as it admits local descent data. This is the
single named input the whole `Y(ρ̄)` line rests on: the DS4 register entry
`EllipticCurve.weilPairing` can be *defined* by it, and every `sorryAx` in
`rho_rigidNoeth` / `rhoProblem_affineOverEll` / `yRho_representable` traces to this one
obligation through `PairingCompatAt`. -/
theorem nonempty_weilPairing_of_localData {N : ℕ} [NeZero N]
    (d : E.WeilPairingLocalData N) :
    ∃ e : pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N,
      e ≫ muNπ S N = E.torsionSqπ N :=
  ⟨d.toPairing, d.toPairing_over⟩

end EllipticCurve

end ModularCurves
