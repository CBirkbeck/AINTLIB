# Reply integration — 2026-06-03

Reply received from the adic-spaces/Huber-expert reviewer on 2026-06-03.
Brief: ./brief.md
Reply: ./reply.md

## Executive read

The reply **confirms the entire route to `IsSheafy` (Thm 8.28(b)) is sound** and **de-risks the single
deep blocker**: instead of formalizing Proposition 7.48 (= Huber [Hu2] 3.9) monolithically, the
genuinely-needed and *elementary* keystone is a density/strict-triangle lemma, which then unblocks the
relative ∃! Spa-lift the project already states. No tickets deleted/superseded; the structure is validated.

## Interpretation summary

| Reviewer point | Maps to | Type | Action taken |
|---|---|---|---|
| Don't formalize Prop 7.48 monolithically; target the relative ∃! lift; injectivity is elementary (density+continuity) | Q1/Q2 + framing | sharper target | ADD T-SUM-7 (density keystone), ADD/re-scope T-SUM-8, re-scope T-SUM-2-RESID |
| Q1: route right; maximal-ideal bridge (6 steps); weaker-than-7.48 suffices; no faithful bypass | Q1 | direct answer | recorded; T-SUM-2 maximal-bridge route confirmed |
| Q2: lemma "dense image R→S, continuous v,w agree on R ⟹ v=w" via NA strict triangle | Q2 | direct answer + proof | T-SUM-7 statement + sketch from the reply |
| Q3: no algebraic bypass; "immediate" = 8.30 + 7.51/7.52 + Spa comparison | Q3 | direct answer | recorded (decision, no code change) |
| Q4: a-posteriori inducing via OMT legitimate, not circular (6 steps) | Q4 | confirmation | re-scope T-SUM-4 with the 6-step sketch |
| Q5: Henkel route right; caution — state OMT for exact category (complete Hausdorff NA modules / first-countability, not σ-compact) | Q5 | confirmation + caution | reviewer-guidance note on the OMT category in T-SUM-4 + header block |
| Q6: [Hu2] = Continuous valuations, Math. Z. 212 (1993), 445–477, Prop 3.9 (Habilitationsschrift = [Hu1]) | Q6 | bibliographic | fixed page-number typo (455→445) in two docstrings; full citation recorded in board |
| A.3 abelian-group-level; AddCommGroup correct; q≥1 deferrable | §8.2 | scoping | reviewer-guidance note in header block |
| A.4: only degree-0 basis-sheaf criterion needed for IsSheafy; defer Cartan–Godement | §8.2 | scoping | reviewer-guidance note in header block |
| Lemma 8.33 chase additive, NO domain hyp; two Laurent decompositions are the inputs | Appendix | confirmation | reviewer-guidance note in header block |
| Lemma 8.34 relative at each rational base | Appendix | confirmation + caution | reviewer-guidance note in header block |

## Changes applied (tickets.md + docstrings)

- **ADD `T-SUM-7`** (`valuation_determined_by_dense_subring`) — the reviewer-recommended IMMEDIATE TARGET:
  continuous valuations on a Hausdorff completion are determined by a dense subring (NA strict triangle).
- **ADD/re-scope `T-SUM-8`** (`comap_coeRingHom_injOn_spa`) — now an instance of T-SUM-7; status 🔴→🔧.
- **MODIFY `T-SUM-2-RESID`** (`cor_8_32_spaExtendsAlongRestriction`) — re-scoped from "🔴 blocked
  deferred-to-Huber B3" to "🔧 the relative ∃! lift, tractable via T-SUM-8 ← T-SUM-7 + the done ⊇ extension".
- **MODIFY `T-SUM-4`** (`cor_8_32_productRestrictionSub_isInducing`) — reframed from "🔴 deep Pettis-lift"
  to "🔧 a-posteriori inducing via degree-0 acyclicity + the LANDED OMT `wedhorn_6_16_of_topNilpUnit`";
  added the reviewer's 6-step sketch; recorded the Q5 category caution.
- **MODIFY FLATNESS-SUMMIT header** — added a "Reviewer guidance (2026-06-03)" block with the Appendix-A
  scoping (degree-0 only; A.3 in AddCommGroup; 8.33 no-domain; 8.34 relative-at-base), the OMT category
  caution, and the [Hu2] citation; revised the Dep order to
  **T-SUM-7 → T-SUM-8 → T-SUM-2-RESID → T-SUM-2 → Cor 8.32 injective**.
- **CITATION** — fixed the page-number typo `455–477` → `445–477` for Huber *Continuous valuations*,
  Math. Z. 212 (1993), in `SpaCompact.lean` and `ValuationSpectrumCompact.lean`.

## Changes rejected by user

(none — user approved "apply all".)

## Open questions remaining

(none — the reviewer addressed all six questions.)

## Decisions recorded but not actioned (no code change)

- Q1/Q3: the maximal-ideal route via Nullstellensatz 7.51/7.52 + Spa comparison is the faithful route;
  no purely-algebraic bypass of the Spa↔maximal bridge exists.
- Q4: deriving the topological inducing a posteriori from acyclicity + OMT is legitimate (not circular).
- Q5: keep the Henkel zero-sequence-of-units OMT; downstream uses must carry no σ-compact/normed-field hyp.

## Net effect on the project

The single deep blocker (Prop 7.48 / [Hu2] 3.9) is converted into a small elementary keystone (T-SUM-7).
With T-SUM-7 → T-SUM-8 → T-SUM-2-RESID done, the `embedding` field's *injective* half closes; the
*inducing* half is then a wiring on the (deferred) Čech acyclicity + the landed OMT. The remaining
substantial-but-standard work is the Appendix-A/Lemma-8.33/8.34 Čech layer, now correctly scoped to
its degree-0 part for the `IsSheafy` deliverable.
