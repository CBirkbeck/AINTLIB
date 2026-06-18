# Expert-review session state — Round 6

- Generated: 2026-05-28 (second session of the day; first was the round-5
  reply integration at `2026-05-28/`)
- Audience: same senior arithmetic geometer as rounds 1–5
- Goal of brief: Strategic guidance on placeholder removal (the `isogOneSub α`
  pattern, where `pullback := AlgHom.id` lets false statements compile).
  Plus a V.1.3 status update under the live witness-parametric chain.
- Scope: structural placeholder issue is primary; V.1.3 is secondary
  status update; III.6.3 mentioned briefly.
- Reply received: partial (2026-05-28 — answers Q1–Q5 + Strategy-B verdict; predates Q6)
- Reply integrated: deferred (decision record written; code execution held — user re-sent the updated brief and is awaiting the reviewer's Q6 response before we run Strategy B)

## Questions in the brief

| # | Question (verbatim from §7 of the brief) |
|---|------------------------------------------|
| Q1 | Is the placeholder pattern pathological? In a formal-proof project where a data structure has multiple fields with no enforced compatibility, is "pair a correct field with a deliberately incorrect other field" categorically illegal, or acceptable scaffolding when downstream callers only use the correct field? Body of formal-proof literature on the right hygiene? |
| Q2 | Right pullback for general 1 − α? We have genuine pullbacks for α = π_q (via addition formula) and α = [n] (via division polynomials). For general α, what's the right Lean-formalisable construction — Pic⁰ + Picard scheme, general addition-pullback `(α, β)` then specialise, or accept that only specific α have genuine pullbacks and refactor to witness-parametric API? |
| Q3 | hq threading strategy. `isogOneSub_negFrobenius` requires `hq : 2 ≤ Fintype.card K` (derivable from Field K + Fintype K but not auto-elaborated). (a) Add hq parameter to oneSubFrobeniusIsog (~160 call sites); (b) derive inside the def; or (c) typeclass `[NontrivialFinite K]` packaging both? |
| Q4 | Structure-level enforcement. Change the `Isogeny` data structure itself to enforce pullback / point-map compatibility (e.g., add a `Prop`-valued field), so placeholders become impossible to define? Or is this over-engineering? |
| Q5 | (Agent-surfaced.) Compositional placeholders elsewhere? Are there other constructions in the project that propagate a placeholder's lie (e.g., `oneSubFrobeniusIsog.comp ψ` inheriting the identity-map placeholder)? Systematic audit beyond grepping for `.pullback` / `.degree`? |
| Q6 | (Agent-surfaced.) Salvage on the orphaned middle (~40–50% of project content built for the dead CoordHom strategy: KE-level chord-formula infrastructure + R-level polynomial-identity layer A/B/C). Can any of this feed the live L6_B3_tower path, V.1.3 closure, or III.6.3 Pic⁰ pivot — or do we accept it as sunk cost? Pointers to "you went the wrong way but here's how to recover" arguments in formal-proof literature? |

## Project-state snapshot at brief time

- Build status: clean (3019 jobs).
- Two parallel top-level Hasse-bound APIs:
  * `hasse_bound` (Frobenius/HasseBound chain, dead — built on the
    placeholder lies; sorry-bearing on universally-false statements).
  * `hasse_bound_skeleton` (witness-parametric chain, live — uses the
    genuine `isogOneSub_negFrobenius`, sorry-free body modulo the two
    GAP leaves V.1.3 and qf-nonneg).
- B2 entries in `b2_log.jsonl`: 3 (`V13-RESIDUAL` /
  `nReduced_R_div_D_sq`, `V13-PLACEHOLDER-PCEQ` / `pointCount_eq`,
  `V13-PLACEHOLDER-TRACE` / `traceOfFrobenius_sq_le`).
- V.1.3 status: round-5 retraction applied; single concrete residual is
  the K-level place ↔ closed-point bijection at the pole-locus of
  `f = (1 − π_q)*x`.
- Three placeholder definitions targeted for removal: `isogOneSub α`,
  `isogSmulSub α r s`, `oneSubFrobeniusIsog W`.
- **Honest content accounting** (per §2.5 of brief): ~30–40% live,
  ~10% dead placeholder chain, ~40–50% orphaned (KE chord-formula
  infrastructure + R-level Vieta identities A/B/C built for the dead
  CoordHom strategy), ~10% reusable scaffolding (base-change).

## Stuck points (from §2.3 / §4 / §6 of brief, one-line summary)

1. Three placeholder definitions pair a correct `toAddMonoidHom` with a
   wrong `pullback := AlgHom.id`, allowing three false-statement
   theorems to compile.
2. ~40 files reference the placeholder names; ~150 of ~160 textual uses
   only touch `toAddMonoidHom` (sound).
3. Three candidate removal strategies (A: replace body / keep signature;
   B: delete + bare-data refactor; C: structural enforcement).
4. V.1.3 — single residual is the K-level Silverman II.2.4 at pole-locus
   (deferred to a focused session).
5. III.6.3 — needs the Pic⁰-pivot witness `(rV − s)(rπ − s) = [Q(r, s)]`
   (deferred).

## Reference list (from §3 of brief, short cite tags)

- Silverman, *Arithmetic of Elliptic Curves* (GTM 106). III.2 (rational
  maps from smooth curves), III.4.6 (deg π = q), III.4.10(c)
  (#ker = sepDeg for separable), III.5.5 (deg(1 − π) = #E(F_q)),
  III.6.3 (degree quadratic form positive semidefinite), V.1.1 (Hasse
  bound), II.2.4 (curve ↔ function-field functorial faithfulness).
- Round-5 reply (`.mathlib-quality/expert-review/2026-05-28/reply.md`):
  Option I′ (function-field map + projective fibre compatibility), the
  reformulation the project applied for V.1.3.
- Mathlib: `Ideal.sum_ramification_inertia`,
  `Fintype.one_lt_card_iff_nontrivial`,
  `WeierstrassCurve.Affine.{addPolynomial_slope, addX, addY}`,
  `IsIntegrallyClosed`.

## Notes for Mode 2 (when reply arrives)

This is a *strategic* brief, not a closure-of-a-residual brief. The
reviewer's reply is expected to be design guidance (which of strategies
A/B/C to pick, hq threading, structure-level enforcement) rather than
new mathematical content. Apply-actions will involve project-wide
refactoring rather than ticket additions.
