/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.GroupScheme.MuN

/-!
# The Weil pairing over a base scheme (KM 2.8)

The pairing `e_N : E[N] ×_S E[N] ⟶ μ_N` for an elliptic curve `E/S`, needed (a) as the
determinant constraint in full-level moduli (`Y(N)`, `Y(ρ,p)`), and (b) as the source of
the `μ_N`-valued "representations-with-pairing" in the FLT application.

Because the pairing is *canonical data*, not a property — and the literature pins it down
only up to the standard inverse ambiguity ("there are two standard normalizations for the
Weil pairing — pick one", Buzzard, Lecture 8 p. 33) — it is registered as construction DS4
(ticket chain `T-C*`; construction of record KM 2.8). The normalisation is fixed by
comparison with the fibrewise field-level Weil pairing already proved in this repository
(`projects/HasseWeil/…/HasseBound/WeilPairing/Pairing.lean`, Silverman III.8); that
comparison is `T-C4` in `WeilPairing/FibreComparison.lean` (kept out of the definitional
spine to isolate the cross-project import). Normalisation choice: review questions
Q-WP1/Q-WP2.

Everything downstream must consume the pairing through `weilPairing` and the specification
statements below; no other properties may be assumed of it.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(DS4, ticket chain T-C1)** The Weil pairing of `E[N]`, as an `S`-morphism
`E[N] ×_S E[N] ⟶ μ_{N,S}`. DATA-SORRY (register entry DS4). Construction of record:
KM 2.8 (the norm/divisor construction; equivalently Cartier autoduality of `E`). -/
noncomputable def weilPairing (N : ℕ) [NeZero N] :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N := sorry

/-- **(T-C1a, specification of DS4)** The Weil pairing is a morphism over `S`. -/
theorem weilPairing_over (N : ℕ) [NeZero N] :
    E.weilPairing N ≫ muNπ S N = pullback.fst _ _ ≫ E.torsionπ N := by sorry

/-- Pair two `T`-points of `E[N]` into a `T`-point of `E[N] ×_S E[N]`, and evaluate the
Weil pairing, landing in the `N`-th roots of unity of `Γ(T, O_T)` via the points
description of `μ_N` (DS3-spec `muNPointsEquiv`). Real construction modulo the registered
data it consumes. -/
noncomputable def weilPairingEval {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) :
    { a : Γ(T, ⊤) // a ^ N = 1 } :=
  muNPointsEquiv S N g
    ⟨pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
        (by simp) ≫ E.weilPairing N, by
      rw [Category.assoc, E.weilPairing_over N, ← Category.assoc,
        pullback.lift_fst, E.pointToTorsion_torsionπ]⟩

/-- **(T-C2 = KM 2.8, bilinearity)** `e_N(x + x', y) = e_N(x, y) · e_N(x', y)` on
`T`-points, where the addition is the registered group structure (DS2) and the raw
kill-by-`N` hypotheses transport by `point_add_killedBy` (T-A6d).
Source: KM 2.8.2; Silverman III.8.1(a). -/
theorem weilPairingEval_add_left {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x x' y : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : x'.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hxx' : (x + x').1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (x + x') y hxx' hy : Γ(T, ⊤)) =
      E.weilPairingEval x y hx hy * E.weilPairingEval x' y hx' hy := by sorry

/-- **(T-C2′ = KM 2.8, alternating)** `e_N(x, x) = 1`.
Source: KM 2.8; Silverman III.8.1(b). -/
theorem weilPairingEval_self {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by sorry

/-- **(T-C3 = KM 2.8, fibrewise nondegeneracy)** On every geometric point of `S`, the
pairing is nondegenerate: a torsion point pairing trivially with everything is zero.
(The full perfectness — `E[N] ≅` Cartier dual of `E[N]` — needs the Cartier-duality
vocabulary, API gap AG-CD; this fibrewise form is its faithful surrogate, sufficient for
the `Y(ρ,p)` application, and is where the comparison with the HasseWeil field-level
pairing enters — `T-C4`.) Source: KM 2.8; Silverman III.8.1(c). -/
theorem weilPairingEval_nondegenerate {N : ℕ} [NeZero N]
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (h : ∀ (y : E.Point t) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
      (E.weilPairingEval x y hx hy : Γ(Spec (.of k), ⊤)) = 1) :
    x = E.zeroPoint t := by sorry

/-- **(T-C2a, base-change naturality — required pinning spec per expert review Q4:
"compatible with arbitrary base change", since fibrewise agreement does not pin
morphisms over non-reduced bases)** Restriction along `k : T' ⟶ T` commutes with the
pairing: `e_N(x|_{T'}, y|_{T'}) = (e_N(x,y))|_{T'}` in `Γ(T', O)`. -/
theorem weilPairingEval_restrict {N : ℕ} [NeZero N] {T T' : Scheme.{u}} {g : T ⟶ S}
    (k : T' ⟶ T) (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : (Point.restrict E k x).1 ≫ E.mulByHom N = (k ≫ g) ≫ E.zero)
    (hy' : (Point.restrict E k y).1 ≫ E.mulByHom N = (k ≫ g) ≫ E.zero) :
    (E.weilPairingEval (Point.restrict E k x) (Point.restrict E k y) hx' hy' : Γ(T', ⊤))
      = (Scheme.Γ.map k.op).hom (E.weilPairingEval x y hx hy : Γ(T, ⊤)) := by sorry

/-- **(T-C2b, divisibility — expert review Q5: "compatibility with N ∣ M")** For
points killed by `N`, the `N·M`-pairing is the `M`-th power of the `N`-pairing:
`e_{NM}(x, y) = e_N(x, y)^M`. (Lattice check: for `x = a/N`, `y = b/N`,
`e_N = exp(2πi(ad−bc)/N)` and as `NM`-torsion points `e_{NM} = e_N^M`.)
Source: Silverman III.8.4-type compatibility; ⧗KM 2.8 for the KM form. -/
theorem weilPairingEval_mul {N M : ℕ} [NeZero N] [NeZero M] {T : Scheme.{u}}
    {g : T ⟶ S} (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : x.1 ≫ E.mulByHom (N * M) = g ≫ E.zero)
    (hy' : y.1 ≫ E.mulByHom (N * M) = g ≫ E.zero) :
    (haveI : NeZero (N * M) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩;
      (E.weilPairingEval (N := N * M) x y hx' hy' : Γ(T, ⊤))) =
      (E.weilPairingEval (N := N) x y hx hy : Γ(T, ⊤)) ^ M := by sorry

/-- **(T-C2c, the symplectic-formula pin — expert review Q6, Silverman convention)**
On a pair of torsion points, `e_N(aP + bQ, cP + dQ) = e_N(P,Q)^{ad − bc}` (exponent
taken mod `N`). Together with Galois equivariance over fields (recorded in ticket
`T-C4`) and `det ∘ ρ_E = χ_N`, this fixes the project's normalisation once and for
all. -/
theorem weilPairingEval_symplectic {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (P Q : E.Point g) (a b c d : ℤ)
    (hP : P.1 ≫ E.mulByHom N = g ≫ E.zero) (hQ : Q.1 ≫ E.mulByHom N = g ≫ E.zero)
    (h₁ : (a • P + b • Q).1 ≫ E.mulByHom N = g ≫ E.zero)
    (h₂ : (c • P + d • Q).1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (a • P + b • Q) (c • P + d • Q) h₁ h₂ : Γ(T, ⊤)) =
      (E.weilPairingEval P Q hP hQ : Γ(T, ⊤)) ^ (((a * d - b * c) % (N : ℤ)).toNat) :=
  by sorry

end EllipticCurve

end ModularCurves
