/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.GroupLaw

/-!
# Flatness of `[N]` — the kernel-divisibility funnel (BB-FLAT, route (G))

The board v10.147 route: `[N]` is affine on the invertible-`N` trail (finite, proven), so
`Smooth`/`Flat` are affine-local ring questions. The infinitesimal lifting for `[N]`
reduces, by smoothness of `E/S` and the abelian point groups, to **`N`-divisibility of the
square-zero kernels** `ker(E(A') → E(A'/I))` — `KernelNDivisible` below, the single
funneled hypothesis. Its discharge is the `TorsionUnramifiedFibre` co-multiplication
layer (`pointSharp_add`) generalized off the field base — the L3 campaign's remaining
mathematical content.

Once `MulByHom.flat_of_nIsInvertible` (`MulByHomSmooth.lean`, via the route-(G) smoothness)
and the discharge land, `MulByHom.etale'` (`MulByHomEtale.lean`) swaps its flat input and the
`Y₁(N)` MASTER closes at `{propext, Classical.choice, Quot.sound}`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(BB-FLAT funnel)** The square-zero kernels of the point functor are `N`-divisible:
for every affine square-zero thickening `Spec (A'/I) ⊆ Spec A'` over `S` and every point
`ε ∈ E(A')` restricting to zero on the thickening, `ε` is `N` times such a point. This is
the Lie-theoretic content of `[N]`-smoothness (`d[N] = N·`, invertible when `N` is);
discharge route: the `TorsionUnramifiedFibre` co-multiplication layer off the field base
(board v10.147). -/
def KernelNDivisible (N : ℕ) : Prop :=
  ∀ (A' : CommRingCat.{u}) (I : Ideal A'), I ^ 2 = ⊥ → ∀ (b' : Spec A' ⟶ S)
    (ε : E.Point b'),
    Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ε = 0 →
    ∃ δ : E.Point b',
      Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) δ = 0 ∧
      (N : ℤ) • δ = ε

end EllipticCurve

end ModularCurves
