# Expert-review session state — Round 5

- Generated: 2026-05-28
- Audience: same senior arithmetic geometer as rounds 1–4
- Goal of brief: Reformulation strategy (confirm the obstruction + recommend the cleanest reformulation route for V.1.3 Step 3)
- Scope: Whole Hasse bound (context); deep focus on V.1.3 Step 3
- Reply received: true (date: 2026-05-28)
- Reply integrated: true (date: 2026-05-28)

## Questions in the brief

| # | Question (verbatim from §6 of the brief) |
|---|------------------------------------------|
| Q1 | Counterexample sanity check. Is the §3 counterexample mathematically correct? E : y² = x³ − x over F_5, P = (2, 1), 𝒩(P) = 4 ≠ 0, (𝔵 − 𝔵^q)²(P) = 0. Triple-checked the arithmetic and the algebraic obstruction (addPullback_x has poles at every F_q-rational point of any elliptic curve over F_q with such points). Is there any reading under which the sharp residual remains true that we have missed? |
| Q2 | Best Step-3 reformulation. Of Option I (function-field map only), Option II (R[1/D] localisation), Option III (projective coordinates), or a fourth route, what is the *cleanest* way to identify (1−π)_{K̄} = 1 − Frob_{q,K̄} as isogenies of E_{K̄} — at the level needed for round-4 Step 4 to compose — without building a CoordHom : R_{K̄} → R_{K̄} for 1 − π_q? |
| Q3 | Existing Lean / Mathlib analogue. Does Mathlib (or any adjacent formalisation) already have anywhere a "sep-deg(isogeny) = #kernel"-type identity for elliptic-curve isogenies that operates at the function-field level (i.e. takes φ* : K̄(E) → K̄(E) rather than a coordinate-ring map as input)? What is the right Isogeny.… / WeierstrassCurve.… lemma to look for and feed our round-4 Step-4 fibre count into? |
| Q4 | Salvage assessment. Of the round-4-era axiom-clean infrastructure (Steps 1, 2, 4; smooth-point / height-one-prime correspondence on E_{K̄}; inertia-degree-one analysis; alg-closed fibre count; degree base-change identity; Identities A/B/C; structural identities at the L6 ramification layer), is anything implicitly predicated on the false residual that we have not yet recognised needs retraction? Anything we expect to "just compose" with the reformulated Step 3 that already looks like a hidden trap? |

## Project-state snapshot at brief time

No `tickets.md` system (project uses direct codebase work; the closest
ticket-equivalent is the deep-pass handover document
`.mathlib-quality/V13-HANDOVER.md`). Status at brief time:

- **Hasse skeleton** (`hasse_bound_skeleton`): axiom-clean, sorry-free
  over the two leaves below.
- **ker_deg_skeleton** (V.1.1 / III.4.10c top leaf): axiom-clean over
  the V.1.3 sharp residual `isogOneSub_negFrobenius_degree_eq_pointCount`.
- **qf_nonneg_skeleton** (III.6.3 top leaf): parametric over an
  existence-of-realisation witness; rounds 1–3 territory; not the focus
  of this round.
- **V.1.3 sharp residual** `isogOneSub_negFrobenius_degree_eq_pointCount`:
  `sorry`-gated. RouteB attempted reduction to
  `oneSubFrob_baseChange_coordHom` → `addPullback_x_in_coordRing_range`
  → `divisibility_witness_x` → `nReduced_R_div_D_sq` is **mathematically
  false** as of 2026-05-28 (counterexample above).
- Round-4 Steps 1, 2, 4: axiom-clean and unaffected.

## Stuck points (from §3 / §4 of brief, one-line summary)

1. V.1.3 Step 3 sharp residual `(𝔵 − 𝔵^q)² ∣ 𝒩` in R is false (counter-
   example: y² = x³ − x over F_5 at P = (2,1)).
2. Need a Step-3 reformulation avoiding `CoordHom : R → R` for `1 − π_q`.
3. Options I (function-field), II (R[1/D]), III (projective) on the
   table; user inclines toward I.

## Reference list (from §1–§2 of brief, short cite tags)

- Round-4 reply (2026-05-27): reviewer's Route B recommendation, Steps 1–4
  laid out.
- Silverman, *Arithmetic of Elliptic Curves* (GTM 106): II.2.4 / II.2.6
  / III.2 / III.4.10 / III.5.5 / V.1.1.
- Mathlib: `AlgebraicGeometry.EllipticCurve.Affine.*` (coordinate ring,
  addX/addY formulae, addPolynomial_slope cubic factorisation);
  `AlgebraicGeometry.EllipticCurve.Projective.*` (Option III candidate);
  `Isogeny.sepDegree` (Option I candidate).
- Project-internal counterexample audit: `.mathlib-quality/b2_log.jsonl`
  (entry timestamped 2026-05-28).
