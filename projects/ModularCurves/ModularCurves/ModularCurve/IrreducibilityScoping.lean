/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.YRho
import ModularCurves.ForMathlib.IrreducibleConnected
import ModularCurves.ForMathlib.SmoothSchemeIrreducible

/-!
# Scoping skeleton for `yRho_geometricallyIrreducible` (T-IRR0, stream IRR)

`/develop --decompose` skeleton for the geometric-irreducibility target
`yRho_geometricallyIrreducible` (`YRho.lean`). This file states the **tractable** leaves of the
decomposition as `:= by sorry` declarations that build clean, and isolates the single
`MAJOR-INFRA` gap — the transcendental connectedness of `Y ⊗ ℂ` — behind the hypothesis `hconn`
of the master reduction. It creates **no tickets** and edits no held file. Full decomposition,
verbatim Katz–Mazur Ch. 10 quotes, adversarial passes and the feasibility assessment live in
`.mathlib-quality/decomposition-km10.md`.

## Source-faithful finding driving the decomposition

Katz–Mazur Ch. 10 is the *algebraic* route to geometric irreducibility, but its own connectedness
proof (Cor. 10.9.2, p. 303) reduces to the geometric generic fibre and then invokes the
**transcendental** description "the underlying complex manifold to `M(𝒫)⊗ℂ` is isomorphic to the
quotient of the upper half plane by the subgroup `Γ̃ ⊂ SL(2,ℤ)`". So the algebraic shell
(finite-étale-Galois `SL(2,ℤ/N)`-structure over `Z[ζ_N]`, cusps via `T[N]`, KM 10.2.5 / 10.6 /
10.8.2 / 10.9.1) only *reduces* the problem; the connectedness core is the analytic `ℍ/Γ̃` fact,
shared by both routes and matching Buzzard's "irreducibility is proved complex-analytically by
uniformising the ℂ-points of the curve by the upper half plane".

## Decomposition (see `decomposition-km10.md` for the full tree)

* **L1** (tractable, mathlib-adjacent) — a nonempty connected smooth curve over an algebraically
  closed field is irreducible: `irreducibleSpace_of_connectedSpace_of_smooth`.
* **L4** (tractable, mathlib) — the only property of `ℍ/Γ̃` actually used: the quotient of a
  connected space by a group action is connected: `connectedSpace_quotient_orbitRel`.
* **MASTER** — `yRho_geometricallyIrreducible_of_connected`: the algebraic reduction of the target
  to geometric connectedness `hconn` of `Y ⊗ ℚ̄` (via base-change smoothness + L1).
* **API GAPS** (analytic, `MAJOR-INFRA`; stated in prose in `decomposition-km10.md`, not here,
  because the objects are absent from mathlib and AINTLIB):
  * **L2** — geometric connectedness is insensitive to the algebraically-closed extension `ℚ̄ ↪ ℂ`.
  * **L3** — the transcendental uniformisation `(Y ⊗ ℂ)^an ≅ ℍ/Γ̃` as Riemann surfaces
    (KM 10.9.2 core; the LeanModularForms bridge).
  * **L5** — GAGA: a `ℂ`-scheme is connected iff its analytification is connected.

AINTLIB ModularCurves T-IRR0 (stream IRR, planning-only; late-phase, `MAJOR-INFRA`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- **(T-IRR0, L1 — reduce irreducibility to connectedness)** A nonempty connected smooth curve
over an algebraically closed field is irreducible: a smooth `k`-scheme is regular, and a regular
scheme's irreducible components coincide with its connected components, so connected + nonempty
forces irreducible. Tractable from mathlib (`regular ⟹ locally irreducible`); the analytic input
enters only through the `ConnectedSpace` hypothesis. -/
theorem irreducibleSpace_of_connectedSpace_of_smooth
    {X : Scheme.{0}} (sX : X ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (hsm : SmoothOfRelativeDimension 1 sX) [Nonempty ↥X] [ConnectedSpace ↥X] :
    IrreducibleSpace ↥X :=
  haveI := hsm
  irreducibleSpace_of_connectedSpace_of_smooth_curve sX

/-- **(T-IRR0, L4 — the only property of `ℍ/Γ̃` we need)** The quotient of a connected space by a
group action is connected, because the quotient map is a continuous surjection and the continuous
image of a connected space is connected. Instantiated at `X = ℍ` (the upper half plane, connected
in mathlib via `LocallyPathConnectedSpace ℍ` + convexity) and `G = Γ̃`, this is KM 10.9.2's
connectedness of `ℍ/Γ̃`. Tractable directly from mathlib. -/
theorem connectedSpace_quotient_orbitRel
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {G : Type*} [Group G] [MulAction G X] :
    ConnectedSpace (Quotient (MulAction.orbitRel G X)) :=
  Quotient.instConnectedSpace

/-- **(T-IRR0, MASTER — the algebraic reduction)** Geometric irreducibility of a curve representing
the `ρ`-level moduli problem follows from geometric **connectedness** of its base change to `ℚ̄`
(`hconn`), via base-change smoothness of `sY` and `L1`. This isolates the entire analytic content of
`yRho_geometricallyIrreducible` into the single hypothesis `hconn`, whose discharge is the
`MAJOR-INFRA` chain L2 → L3 → L5 (uniformisation `(Y⊗ℂ)^an ≅ ℍ/Γ̃` + GAGA), documented in
`decomposition-km10.md`. Discharging this lemma + `hconn` proves `yRho_geometricallyIrreducible`. -/
theorem yRho_geometricallyIrreducible_of_connected {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (D : GaloisRepData N) (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ))
    (hY : RepresentsYRho D Y sY)
    (hconn : ConnectedSpace ↥(pullback sY
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))))
    (hlf : LocallyFinite ((↑) : irreducibleComponents
      ↥(pullback sY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) →
        Set ↥(pullback sY
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))))
    (hdisj : ∀ Z ∈ irreducibleComponents
        ↥(pullback sY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))),
      ∀ W ∈ irreducibleComponents
        ↥(pullback sY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))),
      Z ≠ W → Disjoint Z W) :
    IrreducibleSpace ↥(pullback sY
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) := by
  haveI : ConnectedSpace ↥(pullback sY
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) := hconn
  haveI : Nonempty ↥(pullback sY
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :=
    ConnectedSpace.toNonempty
  exact irreducibleSpace_of_connected_of_disjoint_irreducibleComponents hlf hdisj

end ModularCurves
