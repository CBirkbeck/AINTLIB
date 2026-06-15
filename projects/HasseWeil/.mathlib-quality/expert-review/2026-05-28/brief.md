# Review brief (round 5) — Hasse bound formalization: V.1.3 Step-3 wall (the base-change of `1−π` is not a CoordHom)

*Prepared 2026-05-28 for the same arithmetic-geometry reviewer as rounds 1–4.
Self-contained; no repository access required. Round 4 (2026-05-27)
recommended **Route B** (base-change to `K̄`, then descend) for V.1.3, with
a four-step implementation plan. We pursued Step 3 (the concrete
base-change of `1 − π` and its identification with `1 − Frob_q` on
`E_{K̄}`) across ~24 deep-pass dispatches and have now established that
the specific sub-residual the project reduced Step 3 to is **mathematically
false**. This brief reports the obstruction, gives a concrete counterexample,
and asks the reviewer to confirm and recommend a Step-3 reformulation.*

## 1. Where we got after round 4

Following round 4's recommendation, Route B Steps 1, 2, 4 are
**axiom-clean** in our development:

- **Step 1** (field fixed-subfield) — `a^q = a ⟺ a ∈ image(K → K̄)` in
  `K̄`, by the polynomial-root counting on `X^q − X` you suggested.
- **Step 2** (point fixed-locus descent) — the `q`-Frobenius fixed locus
  on `E(K̄)` equals (the image of) `E(F_q)`, by case-split on `P = O` /
  `P` affine.
- **Step 4** (alg-closed fibre count) — `#ker((1−π)_{K̄}) = sep-deg((1−π)_{K̄})`
  was already proved (the inertia-degree-one + height-one-prime analysis
  on `E_{K̄}`).

Combining: if Step 3 lands — i.e. if we can identify
`(1−π)_{K̄} = 1 − Frob_{q,K̄}` *as an isogeny of `E_{K̄}`* (point map +
function-field pullback together) — then Route B closes V.1.3 by the
chain `deg(1−π) = deg((1−π)_{K̄}) = sep-deg = #ker = #E(F_q)`.

## 2. What Step 3 reduces to in our formalization (the issue)

Our `Isogeny` data structure on a Weierstrass curve `E/K` records, as
*independent* data, a function-field pullback `φ* : K(E) → K(E)` and a
point map `φ : E → E` (no compatibility recorded by construction).
"Identifying" `(1−π)_{K̄} = 1 − Frob_{q,K̄}` as an isogeny means
identifying their `toPointMap`s — which requires a **`CurveMap.CoordHom`
for `(1−π)_{K̄}`**, i.e. a `K̄`-algebra map

> `ρ : R_{K̄} → R_{K̄}` such that `ρ(𝔵) = addPullback_x`, `ρ(𝔶) = addPullback_y`,

where `R_{K̄} = K̄[X,Y]/(W) = E_{K̄}`'s affine coordinate ring,
`𝔵 = class of X`, `𝔶 = class of Y`, and `addPullback_x`, `addPullback_y` are
the chord-formula outputs computing the `x`- and `y`-coordinates of
`P + (−π(P))` for the generic point. From the `CoordHom`, mathlib-style
machinery (`maximalIdealAt_toPointMap`, the smooth-point-equiv etc.)
delivers the point-map identification.

The chord-formula for our isogeny `(1−π_q)` writes

> `addPullback_x = ρ² + a₁ ρ − a₂ − 𝔵 − 𝔵^q`,
>
> `ρ = (𝔶 − (−𝔶^q − a₁𝔵^q − a₃)) / (𝔵 − 𝔵^q) = (𝔶 + 𝔶^q + a₁𝔵^q + a₃) / (𝔵 − 𝔵^q)`,

both *a priori* elements of `K̄(E) = Frac(R_{K̄})`. To get `ρ` as a
`CoordHom`, we need `addPullback_x ∈ image(R_{K̄} → K̄(E))`. Clearing
the chord denominator gives an explicit polynomial `𝒩 ∈ R_{K̄}` (the
"chord numerator") with

> `(𝔵 − 𝔵^q)² · addPullback_x = 𝒩`  in  `K̄(E)`.

Hence the precise polynomial residual the project reduced Step 3 to:

> **(Sharp residual.)** `(𝔵 − 𝔵^q)² ∣ 𝒩` in `R_{K̄}` (and the parallel
> y-side residual).

The explicit form of `𝒩`, after Weierstrass reduction:

> `𝒩 = a₄(𝔵 + 𝔵^q) + 2a₆ − a₃(𝔶 + 𝔶_π⁻) − 2 𝔶 𝔶_π⁻ − a₁(𝔵 𝔶_π⁻ + 𝔵^q 𝔶) + 𝔵² 𝔵^q + 𝔵 (𝔵^q)² + 2a₂ 𝔵 𝔵^q`,
>
> `𝔶_π⁻ := −𝔶^q − a₁𝔵^q − a₃` (`= π·𝔶` under the negative-Frobenius pullback).

(Equivalent form via reduction modulo two Weierstrass relations:
`𝒩 = 𝒟² + a₁ (𝔵 − 𝔵^q) 𝒟 − (𝔵 − 𝔵^q)² (a₂ + 𝔵 + 𝔵^q)`,
`𝒟 := 𝔶 + 𝔶^q + a₁𝔵^q + a₃`.)

After 24 deep-pass dispatches we have three correct, axiom-clean
identities in `R`:

> **(A)** `(𝔶^q − 𝔶) · 𝒟 = (𝔵 − 𝔵^q) · (a₁ 𝔶 − C)`,
>
> **(B)** `(𝔶^q − 𝔶) · (𝒟 + a₁(𝔵 − 𝔵^q)) = (𝔵 − 𝔵^q) · (a₁ 𝔶^q − C)`,
>
> **(C)** `(𝔶^q − 𝔶)² · 𝒩 = (𝔵 − 𝔵^q)² · M`,
>
> where `C := 𝔵² + 𝔵 𝔵^q + (𝔵^q)² + a₂(𝔵 + 𝔵^q) + a₄`
> and `M := (a₁ 𝔶 − C)(a₁ 𝔶^q − C) − (𝔶^q − 𝔶)²(a₂ + 𝔵 + 𝔵^q)`.

Each is provable by `linear_combination` of the curve equation at
`(𝔵, 𝔶)` and at `(𝔵^q, 𝔶_π⁻)` (= `pullback_equation_R`). They are real
algebra, not formalisation artefacts. (A), (B), (C) collectively give
`(𝔵 − 𝔵^q)² ∣ (𝔶^q − 𝔶)² · 𝒩`, but the `(𝔶^q − 𝔶)²` cannot be
cancelled — it shares its zeros with `(𝔵 − 𝔵^q)²` on the `F_q`-rational
locus.

## 3. The sharp residual is mathematically false

**Counterexample.** Take `K = F_5`, `E : y² = x³ − x`
(`a₁=a₂=a₃=a₆=0`, `a₄=−1`; `Δ = −16(4·a₄³ + 27·a₆²) = 64 ≡ 4 ≠ 0`,
so `E` elliptic). The point `P = (2, 1) ∈ E(F_5)`
(check: `2³ − 2 = 6 ≡ 1 = 1² (mod 5)`). It is **non-2-torsion** —
since `a₁ = a₃ = 0` the 2-torsion locus is `{y = 0}`, and `1 ≠ 0`.

Evaluating at `P`:

- `𝔵 ↦ 2`, `𝔵^q = 𝔵^5 ↦ 2^5 = 32 ≡ 2 (mod 5)`, so
  `(𝔵 − 𝔵^q)(P) = 0` and `(𝔵 − 𝔵^q)²(P) = 0`.
- `𝔶 ↦ 1`, `𝔶^q ↦ 1^5 = 1`, `𝔶_π⁻ ↦ −1 ≡ 4 (mod 5)`.
- `𝒩(P) = −1·(2+2) + 0 − 0·(1+4) − 2·1·4 − 0·(...) + 4·2 + 2·4 + 0
        = −4 − 8 + 8 + 8 = 14 ≡ 4 (mod 5)`. **`≠ 0`.**

If `𝒩 = (𝔵 − 𝔵^q)² · p` held in `R` for any `p ∈ R`, evaluating at `P`
would give `4 = 0 · p(P) = 0`. Contradiction.

Equivalently, by the reduced-form identity
`𝒩 = 𝒟² + a₁(𝔵 − 𝔵^q)𝒟 − (𝔵 − 𝔵^q)²(a₂ + 𝔵 + 𝔵^q)`, every
`F_q`-rational point `P` evaluates to `𝒩(P) = 𝒟(P)²
= (2y₀ + a₁x₀ + a₃)²`, which is `≠ 0` precisely when `P` is
non-2-torsion. So at **every non-2-torsion `F_q`-rational point of any
elliptic curve**, the residual fails.

The geometric content: `1 − π_q` sends every `F_q`-rational point of
`E` to `O` (since `π_q` fixes `E(F_q)` pointwise). So the rational
function `addPullback_x` on `E` has a pole of order `2` at every
`F_q`-rational affine point, and does *not* belong to `R = O_E(E ∖ {O})`.
Silverman III.2 says `1 − π_q` is a morphism of *projective* elliptic
curves; it does not say the affine `x`-coordinate function lies in `R`.

The project had implicitly conflated "morphism of projective varieties"
with "morphism of affine coordinate rings". The codebase actually
contains an explicit obstruction note flagging this — but a later
deep-pass plan re-introduced the impossibility and chased it for the
24 dispatches.

## 4. What this means for Step 3 (and our reformulation candidates)

Step 3 as we formulated it requires a `CoordHom : R_{K̄} → R_{K̄}` for
`(1−π)_{K̄}`. **No such map exists**, because `addPullback_x` is
genuinely meromorphic on `E_{K̄}` with poles at the `F_q`-rational
points. Any working Step 3 must avoid `R → R` at the level of the full
curve.

We see three candidate reformulations, listed in order of perceived
ease (and we may be missing a fourth):

> **(I) Function-field-level only.** Identify `(1−π)_{K̄}` with
> `1 − Frob_{q,K̄}` at the level of the *function-field pullback*
> `K̄(E) → K̄(E)` and the *point map*, separately, without ever
> constructing a `CoordHom`. The function-field pullback is the chord
> formula at the `K̄(E)`-level (well-defined as a meromorphic function);
> the point-map identification is direct from
> `(P + (−π(P))) = P − π(P) = (1 − π)(P)` in the group law. Mathlib's
> `Isogeny.sepDegree` already operates at the function-field level, and
> we may be able to feed it the field map directly. The consumer lemma
> `card_primesOver_eq_card_ker_oneSubGeomFrob` would need to be reworked
> to accept a *function-field map* in place of a `CoordHom`.

> **(II) Localised CoordHom `R_{K̄}[1/D] → R_{K̄}[1/D]`** where
> `D = 𝔵 − 𝔵^q`. In `R_{K̄}[1/D]`, the chord function `addPullback_x`
> *is* regular (its poles have been inverted away), so the `CoordHom`
> exists on the localisation. The `F_q`-rational kernel points
> contribute via the existing axiom-clean Step-2 / fixed-locus
> infrastructure (Section 1) at the projective level. The challenge is
> stitching the localised affine map back to the projective curve at
> the kernel locus.

> **(III) Projective coordinates throughout.** Use Mathlib's projective
> Weierstrass formula API (`EllipticCurve.Projective.*`), where
> `1 − π_q` is a global morphism of the projective curve with no
> affine-coordinate poles. This is the morally clean approach but the
> heaviest restructuring; the project so far has used affine-coordinate
> machinery throughout (the function field via affine `R`, the
> divisor / valuation analysis at `O` via affine `ord_∞`, etc.).

Our inclination is Option I — it stays closest to the existing
infrastructure and uses the cleanest abstraction (function fields,
exactly the layer at which round-4 Step 4 already operates). But this
involves redesigning the consumer lemma's signature
(`card_primesOver_eq_card_ker_oneSubGeomFrob` currently takes a
`CoordHom`), and we want to make sure we are not missing a
simpler route.

## 5. What of the round-4 chain survives?

Steps 1, 2, 4 (Section 1) are *unaffected* by this finding — they do
not touch the false residual. The casualties are exactly the Step-3
sub-residuals: the `CoordHom` for `(1−π)_{K̄}` itself, the two
divisibility-witness lemmas (x- and y-side), the polynomial residuals
`addPullback_x_in_coordRing_range` and its y-companion. Identities A,
B, C above remain true polynomial identities in `R`; they just cannot
bridge to a false divisibility.

We **want** to keep Identities A, B, C — they are correct, they may be
useful in the function-field reformulation (Option I) as components of
the meromorphic-function analysis, and they took substantial work.

## 6. Questions for the reviewer

The four numbered questions below are the user's explicit asks (no
agent paraphrasing).

**Q1 — Counterexample sanity check.** Is the §3 counterexample
mathematically correct? `E : y² = x³ − x` over `F_5`, `P = (2, 1)`,
`𝒩(P) = 4 ≠ 0`, `(𝔵 − 𝔵^q)²(P) = 0`. We have triple-checked the
arithmetic and the algebraic obstruction (`addPullback_x` has poles
at every `F_q`-rational point of any elliptic curve over `F_q` with
such points). Is there any reading under which the sharp residual
remains true that we have missed?

**Q2 — Best Step-3 reformulation.** Of Option I (function-field map
only), Option II (`R[1/D]` localisation), Option III (projective
coordinates), or a fourth route we have not seen, what is the
*cleanest* way to identify `(1−π)_{K̄} = 1 − Frob_{q,K̄}` as isogenies
of `E_{K̄}` — at the level needed for round-4 Step 4 to compose —
without building a `CoordHom : R_{K̄} → R_{K̄}` for `1 − π_q`?

**Q3 — Existing Lean / Mathlib analogue.** Does Mathlib (or any
adjacent formalisation) already have *anywhere* a
"`sep-deg(isogeny) = #kernel`"-type identity for elliptic-curve
isogenies that operates at the function-field level (i.e. takes
`φ* : K̄(E) → K̄(E)` rather than a coordinate-ring map as input)? If
yes, what is the right `Isogeny.…` / `WeierstrassCurve.…` lemma to
look for and feed our round-4 Step-4 fibre count into? We suspect there
must be one — the standard `[K(E) : φ*K(E)]_sep` story should be
expressible without going through `R → R`.

**Q4 — Salvage assessment.** Of the round-4-era axiom-clean
infrastructure (Steps 1, 2, 4; the smooth-point / height-one-prime
correspondence on `E_{K̄}`; the inertia-degree-one analysis at affine
primes; the alg-closed fibre count; the degree base-change identity;
identities A/B/C above; the structural identities at the L6 ramification
layer), is there anything that is implicitly predicated on the false
residual that we have not yet recognised needs retraction? Or
equivalently: anything that we expect to "just compose" with the
reformulated Step 3 that the reviewer can already spot as a hidden
trap?

## 7. Document metadata

- Project: Hasse bound for `E/F_q`, Lean 4 / Mathlib.
- Round: 5 (rounds 1–3 concerned `qf_nonneg`; round 4 chose Route B for
  V.1.3 and laid out Steps 1–4).
- Status: Steps 1, 2, 4 of round 4's Route B are axiom-clean. Step 3 —
  identifying `(1−π)_{K̄} = 1 − Frob_{q,K̄}` — reduced to a polynomial
  divisibility we now know to be false. The project builds; the false
  residual is retained as a `sorry` with an annotated doc-block
  pointing at the counterexample. The work in 24 deep-pass dispatches
  produced correct axiom-clean polynomial identities (A, B, C above)
  that we believe will still be useful in the reformulation.
- Counterexample audit-trail: recorded as a JSON record in the
  project's project-internal log of definition / scope errors.
