# Expert-review session state — round 19

- Generated: 2026-05-15
- Audience: ChatGPT Pro (continuing series; round 19, follow-up to round 18)
- Goal of brief: Concrete-shape question after project audit. The reviewer prescribed (round 18) using a Wedhorn 2.13 reverse-direction theorem to build P3's `RatioNodeData`. We audited the ~250-file project and found Wedhorn 2.13 in three SPECIFIC shapes (iterated-minus, iterated-overlap, Laurent-normalized) but none fits the relative Laurent at `r = u_g · u_h⁻¹` needed by P3. Asking how to proceed.
- Scope: Lead question — which existing shape (if any) fits P3, or do we build something new? Plus parallel question for Wedhorn 7.49.
- Reply received: true (2026-05-15)
- Reply integrated: true (2026-05-15)

## Questions in the brief

| # | Question |
|---|----------|
| Q1 | Of the three project-existing Wedhorn 2.13 shapes (A=iterated-minus, B=iterated-overlap, C=Laurent-normalized), can we reformulate P3's relative datum to fit one of them — e.g., express the ratio piece as an iterated-minus or iterated-overlap at an absolute f ∈ A? |
| Q2 | If no existing shape fits: build a fourth specific shape for our relative Laurent at `r = u_g · u_h⁻¹`, OR build the truly general `exists_absolute_rationalLocData_of_relative`? |
| Q3 | Does Wedhorn's text actually produce an explicit absolute datum for the per-piece rational subset `R(L) ∩ {v(g) ≤ v(h)}`, with pair-of-definition and hopen, or does he rely on a non-explicit existence claim? |
| Q4 | Same question for Wedhorn 7.49 — is the reverse direction (rationalOpen → Spv on completion) written down explicitly, or non-explicit? |
| Q5 | Effort estimate: is building the missing reverse-direction theorems a focused effort within the project's existing apparatus, or does it need mathlib-level new infrastructure (e.g., continuous valuation extension to commutative-ring completions)? |

## Ticket-board snapshot at brief time

Same as round 17/18, plus the new sub-ticket renaming:
- `relative_RationalLocData_to_absolute_transport` → renamed to `exists_absolute_rationalLocData_of_relative` (round 18).
- All other tickets unchanged.

## Project audit findings

**Wedhorn 2.13 in the project:**
1. Shape A: `presheafValue_iteratedMinus_equiv` — `O(laurentOverlapDatum D₀ f) ≃ O(iteratedMinusDatum_B P D₀ f)`. Sorry-free.
2. Shape B: `presheafValue_iteratedOverlap_equiv` — same LHS, different RHS (overlap-shape relative). Sorry-free.
3. Shape C: `presheafValue_relative_equiv` (Group III) — `O(D) ≃ O(D@E)` for Laurent-normalized D ⊆ E. Sorry-free.

**Wedhorn 2.13 NOT in the project:** the GENERAL reverse direction (build absolute datum from arbitrary relative datum). This is what P3 needs.

**Wedhorn 7.49 in the project:** forward direction (Spv on completion → rationalOpen valuation via comap). Reverse direction (rationalOpen → Spv on completion) is NOT in the project.

## Stuck points (from §8 of brief)

1. §8.1 — No existing shape directly fits P3's required relative Laurent at `r = u_g · u_h⁻¹`. None of A, B, C produces an absolute rational subset of the form `R(L) ∩ {v(g) ≤ v(h)}` (half-space, not overlap).
2. §8.2 — Same issue for the bridge lemma's Wedhorn 7.49 reverse direction. Not in project.

## Reference list

- [Wedhorn 2019] Adic Spaces — Lemma 2.13, 7.45, 7.49, 7.50, 8.2, 8.28(b), 8.34.
- [Huber 1993] Étale Cohomology of Rigid Analytic Varieties.

## Architecture status

Round 16/17/18 architecture confirmed sound (`RatioNodeData` with literal equalities; construction via relative-to-absolute transport). Round 19 reports the audit confirms the reverse-direction Wedhorn 2.13/7.49 theorems are NOT in the project, and asks the reviewer how to proceed: reformulate P3 to fit existing shapes, build a specific new shape, or build the general reverse direction.
