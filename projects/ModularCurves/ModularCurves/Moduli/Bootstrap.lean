/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.NaiveProblems
import ModularCurves.Moduli.Representability

/-!
# The KM 4.7 bootstrap objects (T-E12–T-E15)

The ⇐ direction of `representable_iff` (T-E5 = KM SCHOLIE 4.7.0 = Loeffler 3.7.4) is proved
by KM's axiomatized engine (KM p. 112, verbatim in `.mathlib-quality/km47-source-quotes.md`):

> "Let `N ≥ 1` be an integer, `G` a finite group, and `δ` a relatively representable and
> affine moduli problem on (Ell) which satisfies the following axioms: 1) `δ` is
> representable, by an affine `ℤ[1/N]`-scheme. 2) `G` operates upon `δ`, in such a way that
> for every elliptic curve `E/S` with `S` a `ℤ[1/N]`-scheme, the `S`-scheme `δ_{E/S}` is a
> finite etale `G`-torsor. We claim that over `ℤ[1/N]`, `𝒫` is represented by the affine
> `ℤ[1/N]`-scheme `𝕸(𝒫, δ)/G`."

applied twice — `(N, δ, G) = (2, Legendre, GL₂(ℤ/2) × {±1})` and `(3, naive level 3,
GL₂(𝔽₃))` — and then glued over `ℤ[1/6]` by "recollement". The engine itself is
`representable_of_rigid_of_torsor` (`Moduli/QuotientProblem.lean`, ticket T-Q6e). This file
holds the two **bootstrap objects** it consumes, i.e. the `δ`'s and their axioms.

## Status of the four bootstrap tickets (cut 2026-07-08, T-E5-KM47 part (2))

* **T-E15 (naive level 3, `ℰ₃`)** — statable *now*: the problem is
  `gammaFullNaiveProblem R 3`, already defined. Its two engine-axioms are the `sorry`d
  theorems below. Explicit model (KM Ex. 2.2.2, GME 2.2.10):
  `Spec ℤ[1/3][β, γ][((a₁³ − 27a₃)a₃)⁻¹]/(β³ − (β+γ)³)` with `a₁ = 3γ − 1`,
  `a₃ = −3γ² − β − 3βγ`, `P = (0,0)`, `Q = (γ, β+γ)`.
* **T-E12 (`M₁ = Spec ℤ[1/6, g₂, g₃, Δ⁻¹]`)**, **T-E13 (`Aut_S(E, ω) = {1}`)** and
  **T-E14 (Legendre, `M'₂ = Spec ℤ[1/2, λ, (λ(λ−1))⁻¹]`)** — **NOT statable yet.** All three
  quantify over an `S`-basis `ω` of the invariant differentials `ω_{E/S}` (KM 4.6.2
  verbatim: *"pairs `(φ₂, ω)` consisting of an `S`-group-scheme isomorphism
  `φ₂ : (ℤ/2ℤ)² ≅ E[2]` together with an `S`-basis `ω` of `ω_{E/S}`…"*), and **`ω_{E/S}`
  exists neither in mathlib (no relative differentials for schemes: no `Ω¹`, no cotangent
  complex in `Mathlib/AlgebraicGeometry`) nor in this repo** (verified 2026-07-08). Rather
  than register a def-level data-sorry, the datum is cut as its own gap ticket
  **[T-E-OMEGA]** with a plan that terminates in a proof (board); the intended signatures
  are recorded there. No decl is emitted here for them.

Consequently the `ℤ[1/2]`-half of the bootstrap is **blocked on [T-E-OMEGA]**, while the
`ℤ[1/3]`-half (this file) is unblocked. See the board for the level-4 alternative that
would dodge `ω` entirely (`δ = ` naive level 4, `G = GL₂(ℤ/4)`, `2` invertible).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable (R : CommRingCat.{u})

/-! ### T-E15 — the naive level 3 bootstrap object `ℰ₃` over `ℤ[1/3]` -/

/-- **(T-E15a, KM engine axiom 1 for `δ = ` naive level 3; KM Ex. 2.2.2 / GME 2.2.10)**
Over a base in which `3` is invertible, the naive level-3 problem is representable by an
object whose base is **affine** — explicitly `Y(3) = Spec ℤ[1/3][β, γ][((a₁³−27a₃)a₃)⁻¹] /
(β³ − (β+γ)³)` with `a₁ = 3γ − 1`, `a₃ = −3γ² − β − 3βγ`, carrying `P = (0,0)`,
`Q = (γ, β+γ)`.

This is the `N = 3` instance of KM COROLLARY 4.7.2 *proved by hand* (not via 4.7.1 — that
would be circular: 4.7.1 is what this object bootstraps). Route: the AME 2.2.10 computation
— normalise a Weierstrass model so that `P` is a flex at the origin (`[3]P = 0`), read off
`a₁, a₃`, and check the universal property against `EllipticCurve.Point`; the repo's
`VariableChange` machinery (`EllipticCurve/ModelVariableChange.lean`, `WeierstrassModel`)
plus `ForMathlib/TateNormalForm.lean` are the intended engines. -/
theorem naiveLevelThree_representable_by_affine (hR : IsUnit (3 : R)) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((gammaFullNaiveProblem R 3).RepresentableBy X) := by
  sorry

/-- **(T-E15b, KM engine axiom 2 for `δ = ` naive level 3)** For every elliptic curve `E/S`
over a base in which `3` is invertible, the `S`-scheme `δ_{E/S}` relatively representing the
naive level-3 problem is **finite étale over `S`** — the underlying scheme of the
`GL₂(𝔽₃)`-torsor of KM's axiom 2 (KM p. 112).

Stated here in the torsor-free shape (finite + étale + the relative representability
bijection), matching `gammaHNaive_relativelyRepresentable`'s packaging; the
simply-transitive `GL₂(𝔽₃)`-action is supplied separately by `EllipticCurve.glSmul`
(`Moduli/GammaH.lean`) and the torsor property is `T-Q2`'s `InvariantTorsor` datum. Route:
`E[3]` is finite étale of rank 9 when `3` is invertible (T-B5), and a naive full level-3
structure is exactly a basis of it, so `δ_{E/S}` is the `Isom`-scheme
`Isom_S((ℤ/3)², E[3])`, an open-and-closed subscheme of `E[3] ×_S E[3]` cut out by the
non-vanishing of the Weil pairing (Loe 3.8.2 — consumes stream C). -/
theorem naiveLevelThree_relativelyRepresentable_finiteEtale (hR : IsUnit (3 : R))
    (X : EllObj R) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
        ({ h : T ⟶ Z // h ≫ f = g } ≃
          (gammaFullNaiveProblem R 3).obj (Opposite.op (X.pullbackAlong g))) := by
  sorry

end ModularCurves
