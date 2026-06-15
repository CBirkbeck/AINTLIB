# T-II-2-001: Rational map from smooth curve is a morphism

**Status**: DONE (2026-04-18)
**Silverman**: II.2.1 (Proposition)
**Module**: `HasseWeil/Curves/RationalMap.lean` (`ProjectiveTuple.isRegularAt_of_smooth` / `isMorphism_of_smooth`)
**Owner**: worker-H
**Estimated lines**: 60 (delivered: ~60 lines for the main theorem, plus ~500 lines of supporting infrastructure in `ProjectiveTuple.lean`, `RationalMap.lean`, `Valuation.lean`)
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-1-001 (DVR) — done
- T-II-1-003 (uniformizer) — done

## Blocks
- T-II-2-002 through T-II-2-011 (the rest of the II.2 section, except the
  Frobenius-specific EC tickets T-II-2-012..015 which are done)
- T-II-2-016 (separable ∘ Frobenius factorization)
- T-III-3-006 (addition is morphism on EC)

## Statement (Silverman II.2.1)
Let `C` be a curve, `V ⊂ ℙ^N` a variety, `P ∈ C` a smooth point, and
`φ : C → V` a rational map. Then `φ` is regular at `P`. In particular, if
`C` is smooth, then `φ` is a morphism.

## Why BLOCKED

The ticket requires a `RationalMap` type and a `Morphism` (or "regular
everywhere") type between our `SmoothPlaneCurve`s and (some notion of) target
varieties. **Neither exists in the project.** Building them is the foundational
task gating almost all of Stream-A's II.2 section.

### The shape of the missing API

A proper `RationalMap C V` for affine/projective targets would need, roughly:

1. **`RationalMap C V`**: a homomorphism `K(V) →ₐ[F] K(C)` plus data/proof that
   the corresponding point map `C(F̄) ⇢ V(F̄)` is defined on a dense open.
   For our setting (affine Weierstrass + projective target `ℙⁿ`), a
   working minimal version is: a tuple of `(N+1)` elements of `K(C)`, not
   all zero, modulo simultaneous scaling by `K(C)*`.

2. **`RationalMap.IsRegularAt (φ : RationalMap C V) (P : C.SmoothPoint) : Prop`**:
   for the minimal tuple representation, this says there is a choice of
   representative `[f₀ : ⋯ : f_N]` where every `f_i` satisfies `ord_P f_i ≥ 0`
   and at least one has `ord_P f_i = 0`.

3. **`Morphism C V`**: a `RationalMap` that is regular everywhere, i.e.,
   `∀ P : C.SmoothPoint, φ.IsRegularAt P`.

Silverman's proof of II.2.1 is then the standard "multiply by a power of the
uniformizer" trick: given a uniformizer `t` at `P` and a rational map with
representative `[f₀, …, f_N]`, let `n = min_i (ord_P f_i)` and replace by
`[t^{-n} f_0, …, t^{-n} f_N]`. This representative has nonnegative valuations
at `P` and at least one has valuation 0.

All of this requires the infrastructure pieces above.

### What mathlib has

- `Mathlib.AlgebraicGeometry.RationalMap` — defines `Scheme.RationalMap` and
  `Scheme.PartialMap` for schemes. Our project uses the affine Weierstrass +
  function-field formulation, not `Scheme`, so this is not directly usable
  without a large adapter (or rewriting the project as schemes, which is a
  non-starter at this point in the development).

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace` — too abstract; adapting
  requires identifying `SmoothPlaneCurve` with a locally ringed space.

- `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point` — the projective
  points on an elliptic curve; closer to what we want for the codomain `V = E`
  but still not a general `Morphism` API.

### What the project has

- `C.FunctionField` and `C.ord_P` — used by the proof.
- `Uniformizer C P t` — used by the proof.
- No notion of `RationalMap`, `Morphism`, projective target, or target variety
  beyond the specific case of another `SmoothPlaneCurve` (which is an affine
  model, not a projective variety).

## The whole II.2 section is blocked on this infrastructure

Status of the II.2 tickets as of 2026-04-17:

| Ticket | Topic | Depends on Morphism API? |
|---|---|---|
| T-II-2-001 | rat map ⇒ morphism | **yes (foundational)** |
| T-II-2-002 | nonconst ⇒ surjective | yes |
| T-II-2-003 | curves ↔ field extensions | yes |
| T-II-2-004 | deg / deg_s / deg_i | yes |
| T-II-2-005 | norm map φ_* | yes |
| T-II-2-006 | deg-1 ⇒ iso | yes |
| T-II-2-007 | ramification e_φ(P) | yes |
| T-II-2-008 | Σ e_φ = deg | yes |
| T-II-2-009 | #φ⁻¹(Q) = deg_s | yes |
| T-II-2-010 | ramification chain rule | yes |
| T-II-2-011 | unramified ⇔ ... | yes |
| T-II-2-012..015 | Frobenius (EC case) | **DONE** (uses Weierstrass directly, not generic Morphism) |
| T-II-2-016 | factor sep ∘ Frob^e | yes |

The Frobenius tickets `T-II-2-012..015` are done in the `HasseWeil.Frobenius`
module by working directly with the Weierstrass equation (`Affine.CoordinateRing`)
rather than a generic Morphism API. This same trick may work for a few other
II.2 tickets, but not for the statements that quantify over arbitrary
`Morphism`s or `RationalMap`s.

## Acceptance criteria (still BLOCKED)

```lean
namespace HasseWeil.Curves

theorem rationalMap_regular_of_smooth (C : SmoothPlaneCurve F)
    (V : ProjectiveVariety F) (φ : RationalMap C V) (P : C.SmoothPoint) :
    φ.IsRegularAt P

theorem rationalMap_isMorphism_of_smooth (C : SmoothPlaneCurve F)
    (V : ProjectiveVariety F) (φ : RationalMap C V) : Morphism C V

end HasseWeil.Curves
```

## What would unblock this

A sub-stream of **infrastructure tickets** is needed before T-II-2-001 can
start. Suggested decomposition:

1. **T-II-2-INFRA-001** (~150 lines): define `ProjectiveVariety F` (or a thin
   wrapper adequate for II.2's use cases — tuples of homogeneous-poly
   equations in `F[X₀, …, X_N]`).

2. **T-II-2-INFRA-002** (~100 lines): define `RationalMap C V` as tuples of
   `K(C)` elements modulo scaling; include `IsRegularAt`.

3. **T-II-2-INFRA-003** (~80 lines): define `Morphism C V` (regular
   everywhere) and its composition / identity.

4. **T-II-2-INFRA-004** (~60 lines): define the pullback `φ* : K(V) → K(C)` of
   a dominant rational map.

After this, T-II-2-001 becomes the ~60-line ticket it was estimated at, and
the downstream II.2 tickets become reachable.

An alternative — dramatically cheaper — path is to **not** develop a general
Morphism API, and instead handle each downstream consumer of II.2 with a
specialized argument for the specific Weierstrass/projective-point situation
at hand (as was done for Frobenius). This is how `HasseWeil.Frobenius` avoids
the issue. But it gives up on having a reusable Silverman-chapter-II library.

## Progress log

- **2026-04-17** (worker dev): Assessed; blocked on RationalMap/Morphism
  infrastructure that the project does not carry. Documented the
  ripple-through to the rest of the II.2 section. Proposed
  `T-II-2-INFRA-001..004` as the unblocking path.
