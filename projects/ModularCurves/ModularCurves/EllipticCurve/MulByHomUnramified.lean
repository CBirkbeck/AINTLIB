/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Torsion
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Unramifiedness of `[N]` via the `E[N]`-torsor (T-B5D / BB-DIFF, scoping skeleton)

`/develop --decompose` skeleton for **BB-DIFF** = `mulByHom_formallyUnramified` (`Torsion.lean:228`,
held): `[N] : E ⟶ E` is formally unramified when `N` is invertible on `S`. It states the leaves of
the **non-circular, HasseWeil-anchored** route (beastmode-B's `tb5z_architecture.md` route (c),
grounded in KM §2.3) as `:= by sorry`, and assembles the target from them. NEW bridge file; the held
`Torsion.lean` / `GroupLawConstruction.lean` are not edited. Full tree, verbatim KM 2.3 / Loeffler
3.4.2(2) quotes, adversarial passes and feasibility live in `.mathlib-quality/decomposition-km2.3-b5d.md`.

## Why not the "obvious" routes (mapped dead ends — do NOT re-litigate)
- **Invariant-differential / scheme `Ω¹`** (KM's own "tangent map at the origin is multiplication by
  `N`"): mathlib has NO invariant differential for `WeierstrassCurve` and NO relative-`Ω¹` sheaf API.
- **Chart route** (categorical `mulByHom = (mulBy N).left` on `GrpObj` ↔ Weierstrass-chart `[N]`):
  that comparison is **T-W7 scope** (A-lane, in progress) — collides.
- The `torsionπ_etale ⟸ mulBy_etale ⟸ mulByHom_formallyUnramified` chain (`Torsion.lean:233-250`)
  and the T-B6 fibre count are currently **circular** in `BB-DIFF`.

## The route (KM §2.3, non-circular)
KM Thm 2.3.1: `[N]` is finite locally free of rank `N²`, and its kernel `E[N]` is finite étale over
`S` when `N` is invertible. KM's proof reduces geometric-fibre-by-fibre and uses KM Cor 2.3.2:
**`[N]` is an f.p.p.f `E[N]`-torsor**, so `[N]` is unramified iff `E[N] → S` is. The fibre-level
`[N]`-separability that mathlib lacks is **already in AINTLIB's HasseWeil** (`InvariantDifferential`,
`OmegaPullbackCoeff`, `EC/KernelCountGeneral.card_kernel_eq_degree_of_separable`, `mulByInt_degree`,
`NTorsion/TorsionGeneralN`) — verified present. So the leaves:

* **L-A** (self-contained core, "build first", route-independent) — `formallyUnramified_mulByHom_of_torsionπ`:
  `FormallyUnramified (torsionπ N) → FormallyUnramified (mulByHom N)`, via the `E[N]`-torsor structure
  (KM 2.3.2) / group infinitesimal-lifting. Cannot collide with any lane.
* **L-BC** (API-gap sub-tree) — `formallyUnramified_torsionπ`: `E[N] → S` is formally unramified when
  `N` is invertible, from (L-B) HasseWeil geometric fibres `E[N]_{k̄}` étale (the crux **T-B6**
  scheme-fibre ↔ HasseWeil-`WeierstrassCurve` comparison) + (L-C = **T-DISC**) the "finite + geometric
  fibres unramified ⟹ unramified" criterion.
* **MASTER** — `mulByHom_formallyUnramified'` = L-A ∘ L-BC (assembled, term-mode; discharges
  `Torsion.lean:228` once L-A and L-BC land).

AINTLIB ModularCurves T-B5D + T-DISC (stream v10.10; planning-only, BB-DIFF discharge route).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(T-B5D, L-A — the self-contained core, build first)** If the `N`-torsion `E[N] → S` is formally
unramified, then so is `[N] : E ⟶ E`. Route-independent: `[N]` is an f.p.p.f `E[N]`-torsor (KM Cor.
2.3.2), so two infinitesimal lifts `g₁, g₂` of `[N]` agreeing on a square-zero closed subscheme differ
by a map into `E[N]` vanishing there, which is `0` once `E[N] → S` is formally unramified — hence
`g₁ = g₂`. Uses only the `GrpObj` group structure of `E` and mathlib's `FormallyUnramified` morphism
property; collides with no lane. This is the piece to land first. -/
theorem formallyUnramified_mulByHom_of_torsionπ (N : ℕ)
    (htors : FormallyUnramified (E.torsionπ N)) :
    FormallyUnramified (E.mulByHom N) := by sorry

/-- **(T-B5D, L-BC — the arithmetic input, API-gap sub-tree)** If `N` is invertible on `S`, then the
`N`-torsion `E[N] → S` is formally unramified. Route: `E[N] → S` is finite (`torsionπ_isFinite`,
proven) and its geometric fibres `E[N]_{k̄}` are étale — the latter from AINTLIB's **HasseWeil**
field-level theory (`[N]` separable when `char k̄ ∤ N` via the invariant differential
`OmegaPullbackCoeff`/`card_kernel_eq_degree_of_separable`; `TorsionGeneralN` gives `E[N]_{k̄} ≅
(ℤ/N)²`), transported across the crux **T-B6** scheme-fibre ↔ `WeierstrassCurve k̄` comparison — plus
the **T-DISC** "finite + geometric fibres unramified ⟹ unramified" criterion. Source: KM Thm 2.3.1. -/
theorem formallyUnramified_torsionπ (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) := by sorry

/-- **(T-B5D, MASTER — assembly)** BB-DIFF: `[N]` is formally unramified when `N` is invertible,
assembled from L-A ∘ L-BC. Term-mode (no `sorry` of its own): discharging `formallyUnramified_torsionπ`
(L-BC) and `formallyUnramified_mulByHom_of_torsionπ` (L-A) proves this, which is defeq to the held
`Torsion.lean:228` `mulByHom_formallyUnramified`. -/
theorem mulByHom_formallyUnramified' (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) :=
  E.formallyUnramified_mulByHom_of_torsionπ N (E.formallyUnramified_torsionπ N h)

end EllipticCurve

end ModularCurves
