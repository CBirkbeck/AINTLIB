/-
Copyright (c) 2026 the AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ModularCurves.LevelStructure.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# KM-INTEGRAL stream skeleton: the Drinfeld upgrade of Y₁(N) (Katz–Mazur Ch. 5)

Skeleton for the KM-INTEGRAL stream (see `decomposition-km-integral.md`): the regularity
theory of the moduli problem of Drinfeld `[Γ₁(N)]`-structures over all of `ℤ`, following
Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 5 (print pages 129–141;
pdf = print + 11). This file carries the leaves of KM's own proof tree that are
STATABLE with today's vocabulary — waves W0–W3 of the stream. The deep-vocabulary
waves (W4 universal formal deformations, W5 Serre–Tate / p-divisible groups, W6 the
axiomatic homogeneity engine) are API-gap charters on the board; their statements
enter this file as their vocabulary lands.

The headline (KM First Main Theorem 5.1.1, `[Γ₁(N)]` clause, verbatim print p. 129):
"Each of the four moduli problems [Γ(N)], [Γ₁(N)], [bal.Γ₁(N)], and [Γ₀(N)] is
relatively representable over (Ell). Each is finite and flat over (Ell) of constant
rank ≥ 1, and regular (necessarily of dimension two). Each tensored with ℤ[1/N] is
finite etale over (Ell/ℤ[1/N])."
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-! ## W0 — the Drinfeld transport leaf (KM 3.6 substrate)

The integral relative-representability wave. The problem object `gammaOneProblem`
(the Drinfeld analogue of `gammaOneNaiveProblem`, with `IsGammaOne` in place of
`IsNaiveGammaOne`) is DEFERRED to ticket [KM-W0]: per the v10.8 no-sorried-data rule
the functor cannot be defined before its transport lemma is proven. The transport
lemma itself is the first skeleton leaf. -/

section Transport

variable {S T : Scheme.{u}} (E : EllipticCurve S)

/-- **[KM-W0-1] Drinfeld structures pull back.** Source: KM 1.4 / 3.6 — exact order in
the Cartier-divisor sense is stable under arbitrary base change (KM 1.4, "the formation
of the divisor commutes with base change"; the `[Γ₁(N)]`-problem's functoriality clause,
KM 3.2). Elliptic-curve form over a morphism of base schemes. -/
theorem isGammaOne_pullAlong (N : ℕ) [NeZero N] (f : T ⟶ S) (P : E.Section)
    (h : E.IsGammaOne N P) :
    (E.baseChange f).IsGammaOne N (EllipticCurve.Point.asSection E f (EllipticCurve.Point.pull E f P)) := by sorry

end Transport

/-! ## W1 — the combinatorial core (KM 5.3.4)

KM Prop 5.3.4 (verbatim, print p. 140): "Let R be an arbitrary ring, and
G(X,Y) = X + Y + ⋯ a one-parameter commutative formal group law over R. Suppose that
for some prime power pⁿ, the equation X^{pⁿ} = 0 defines a subgroup-scheme of G. Then
p = 0 in R, and this subgroup-scheme is equal to Ker(Fⁿ)."

Stated here in the raw universal form KM's own proof uses (print p. 140–141): the
subgroup condition at the universal quotient `B = R⟦X,Y⟧/(X^{pⁿ}, Y^{pⁿ})` says
exactly `G^{pⁿ} ∈ (X₀^{pⁿ}, X₁^{pⁿ})`. Only the constant and linear coefficients of
`G` enter the argument. The `Ker(Fⁿ)` clause (5.3.4b) is stated in wave W2 with the
Frobenius vocabulary. -/

section CombinatorialCore

variable {R : Type u} [CommRing R]

/-- **[KM-W1-1] (KM 5.3.4, first conclusion).** If a two-variable power series `G` with
`G ≡ X₀ + X₁ (mod degree ≥ 2)` satisfies `G^{pⁿ} ∈ (X₀^{pⁿ}, X₁^{pⁿ})`, then `p = 0`
in `R`. KM's proof (print p. 141): compare total-degree-`pⁿ` terms in
`G^{pⁿ} = X^{pⁿ}·A + Y^{pⁿ}·B` to get `(X+Y)^{pⁿ} = X^{pⁿ}A(0,0) + Y^{pⁿ}B(0,0)`;
coefficients of `X^{pⁿ}`, `Y^{pⁿ}` force `A(0,0) = B(0,0) = 1`; hence all intermediate
binomial coefficients `(pⁿ choose i)` vanish in `R`; `i = 1` gives `pⁿ = 0`,
`i = p^{n-1}` gives `p × (unit prime to p) = 0`, so `p = 0`. -/
theorem CharP.p_eq_zero_of_pow_mem_span (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (G : MvPowerSeries (Fin 2) R)
    (h0 : MvPowerSeries.constantCoeff G = 0)
    (hlin : ∀ i : Fin 2, MvPowerSeries.coeff (Finsupp.single i 1) G = 1)
    (hsub : G ^ p ^ n ∈ Ideal.span
      {(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ p ^ n, (MvPowerSeries.X (1 : Fin 2)) ^ p ^ n}) :
    (p : R) = 0 := by sorry

end CombinatorialCore

/-! ## W2 — the zero-section proposition (KM 5.3.3, elliptic case)

KM Prop 5.3.3 (verbatim, print p. 140): "Let R be an arbitrary ring, C/R a smooth
commutative one-dimensional group-scheme over R (cf. 1.4.1), p a prime number, n ≥ 1
an integer. Suppose that the zero section 0 ∈ C(R) is a point of 'exact order pⁿ' in
C/R, i.e., that the effective Cartier divisor pⁿ[0] in C/R is a subgroup-scheme. Then
p = 0 in R, and the subgroup-scheme pⁿ[0] is none other than Ker(Fⁿ)."

Stated here for our elliptic curves over an affine base (the shape the Rigid-II
application consumes; KM's proof is Zariski-local anyway: "Zariski locally on R, we
may choose a parameter X for the formal group. Once this is done, our proposition
results from [5.3.4]."). The chart parameter comes from the repo's Weierstrass chart
machinery; the divisor-to-power-series bridge is the `sectionsDivisor`/killed-locus
layer. -/

section ZeroSection

/-- **[KM-W2-1] (KM 5.3.3, first conclusion, elliptic affine case).** If the zero
section of an elliptic curve over `Spec A` has Drinfeld exact order `pⁿ`, then
`p = 0` in `A`. -/
theorem CharP.p_eq_zero_of_isGammaOne_zero (p n : ℕ) [NeZero (p ^ n)] (hp : p.Prime) (hn : 1 ≤ n)
    (A : Type u) [CommRing A]
    (E : EllipticCurve (Spec (CommRingCat.of A)))
    (h : E.IsGammaOne (p ^ n) 0) :
    (p : A) = 0 := by sorry

end ZeroSection

/-! ## W3 — Rigidity II, first half (KM 5.3.2.2 via 5.3.5)

KM (5.3.2.2) Rigid II (verbatim, print p. 138–139): "Let k be an algebraically closed
field of characteristic p. If R is an artin local W(k)-algebra [with residue field k],
and if E/R admits 0 as a point of 'exact order pⁿ', then R is a k-algebra, i.e.,
p = 0 in R."  KM 5.3.5 (print p. 141): "Assertion II is just the proposition itself,
applied to E/R."  The second half of Case II (the `T`-invariant clause forcing `E/R`
constant) enters with wave W4's deformation vocabulary. -/

section RigidII

/-- **[KM-W3-1] (Rigid II, first conclusion).** An artin local ring whose elliptic curve
admits the zero section as a point of Drinfeld exact order `pⁿ` has `p = 0` — the
one-line corollary of [KM-W2-1] per KM 5.3.5. Stated without the Witt-vector algebra
structure (not needed for this half; W4 re-states the full deformation form). -/
theorem CharP.p_eq_zero_of_isGammaOne_zero_artinLocal (p n : ℕ) [NeZero (p ^ n)] (hp : p.Prime)
    (hn : 1 ≤ n) (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (E : EllipticCurve (Spec (CommRingCat.of A)))
    (h : E.IsGammaOne (p ^ n) 0) :
    (p : A) = 0 := by sorry

end RigidII

end ModularCurves
