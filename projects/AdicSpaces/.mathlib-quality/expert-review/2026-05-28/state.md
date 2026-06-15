# Expert-review session state

- Generated: 2026-05-28T00:00:00Z
- Audience: ChatGPT / general LLM (senior algebraic geometer)
- Goal of brief: Specific blocker — two stuck points from the 2026-05-28 `/develop --continue` audit
- Scope: narrow (B2 restatement direction + 5-lemma diagram body); skip bucket prioritization / tactical questions
- Reply received: true (2026-05-28T00:00:00Z)
- Reply integrated: true (2026-05-28T00:00:00Z)
- Wedhorn cross-check performed (user-requested): see integration.md table

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Signature-defect resolution for the restriction-inherit chain. (a) Is the right move (i) adding the missing hypotheses to the intermediates and propagating to consumers, (ii) collapsing the intermediates and routing consumers directly through `propA3_part2_project_gluing` applied to the refinement, or (iii) refactoring the upstream predicates (`IsLaurentCover`, `IsGeneratedBy`, `IsUnitGenerated`) to track images in `𝒪_X(base)` rather than elements of `A`? Specific ask: has Wedhorn or another reference given a cleaner formulation that side-steps the same-`fs` issue for the restricted cover? (b) For the `restricted_cover_inherits_IsGeneratedBy` bijection: is the standard formulation in the literature using a sub-Finset T' ⊆ T, or do textbooks finesse this differently? |
| Q2 | 5-lemma diagram chase for Wedhorn 8.33. (a) Is the categorical 5-lemma in mathlib usable here, or hand chase on CommRingCat? (b) What's the cleanest formulation of the Laurent decomposition A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩ in Lean / Mathlib (LaurentPolynomial-completion vs IsLocalization.Away vs MvPowerSeries with index set ℤ)? (c) The ker(λ) = A computation — coefficient-matching via MvPowerSeries.coeff_injective or abstract Pi.algebra decomposition? (d) Alternative routes (Tate acyclicity, Mittag-Leffler, Čech-derived-functor) that bypass the diagram chase? (e) Sub-decomposition granularity — per-row, per-equation, or inline? |

## Ticket-board snapshot at brief time

The active ticket board (`.mathlib-quality/tickets.md`) was 9457 lines as of
2026-05-28 audit. Key state for the questions in this brief:

**Tickets directly mentioned (all currently OPEN):**

- `T-WC-RESTR-INHERIT-GEN-RESTATED` (in_progress) — the
  `restricted_cover_inherits_IsUnitGenerated` body, sorry-bodied. Drives Q1.
- `T-WC-RESTR-INHERIT-GEN` (superseded by RESTATED) — original
  `restricted_cover_inherits_IsGeneratedBy`. Drives Q1.
- `T-WC-LAURENT-RESTR-IS-LAURENT` (OPEN) — `laurent_restriction_isLaurent`
  signature mismatch with Wedhorn's image-tracking phrasing. Drives Q1.
- `T-WC-RESTRICTED-INHERITS-UG-DEFECT` (NEW, 2026-05-28) — B2 log entry for
  the above, logged to `b2_log.jsonl`. Drives Q1.
- `T-WC-833-GLUING-FIELD` (OPEN) — `wedhorn_lemma_833_gluing_as_field` body,
  the 5-lemma diagram chase. Drives Q2.
- `T-WC-COMPATIBLE-PAIR-5LEMMA` (OPEN) — the 5-lemma sub-piece if we go
  per-equation decomposition. Drives Q2.

**Background context tickets (all DONE):**

- `T-WC-PROPA3-PART2-GLU-RESTATED` (done 2026-05-28, commit 4d0d3c1) — the
  Prop A.3(2) project bridge gluing direction
- `T-WC-PROPA3-PART1-GLU-RESTATED` (done 2026-05-28, commit d29fdee) — the
  Prop A.3(1) project bridge gluing direction
- `T-WC-EPRIME-RESTRICT-TO-D` (done) — `RationalCovering.restrictToPiece`
  construction
- `T-WC-CAT-C-CHANGE-BASE` (done) — `presheafValueCast` cast helper

## Stuck points (from §8 of brief)

1. §8.1 — Signature defects in the restriction-inherit lemmas:
   `restricted_cover_inherits_IsUnitGenerated`,
   `restricted_cover_inherits_IsGeneratedBy`, `laurent_restriction_isLaurent`.
   Missing hypotheses (`E.base ⊆ C'.base`, `E'.T` ↔ `T`) at the lemma
   signature; naturally available at consumers but not threaded.
2. §8.2 — Wedhorn 8.33 5-lemma diagram chase body. Need Laurent decomposition
   `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩`, ideal-level decomposition for
   `(f - ζ) A⟨ζ, ζ⁻¹⟩`, and the row-2 kernel computation. Mathlib has the
   categorical 5-lemma in abelian categories but presheafValues live in
   `CommRingCat`; need to choose between lifting to `ModuleCat A` or hand chase.

## Reference list (from §2.2 of brief)

- [Wedhorn19] Torsten Wedhorn. *Adic Spaces.* arXiv:1910.05934v1, 2019. 154 pp.
- [Huber94] Roland Huber. "A generalization of formal schemes and rigid analytic
  varieties." Math. Z. 217 (1994), 513–551.
- [BGR] Bosch–Güntzer–Remmert, *Non-Archimedean Analysis* (Grundlehren 261, Springer 1984).
- [Bourbaki-CA-III] N. Bourbaki, *Algèbre commutative*, ch. III.
