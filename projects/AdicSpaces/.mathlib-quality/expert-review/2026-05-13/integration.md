# Reply integration — 2026-05-13

Reply received from ChatGPT Pro on 2026-05-13.

- Brief: `.mathlib-quality/expert-review/2026-05-13/brief.md`
- Reply: `.mathlib-quality/expert-review/2026-05-13/reply.md`

## Interpretation summary

Reviewer addressed every sub-question Q1a-Q4c, often with substantive corrections of
the round-4 plan. The five priority directives in the "Manager message":

1. **Attack `bivariate-example-638` first** (T-OV-1) — TOP priority. Direct
   topological quotient/evaluation proof. Do not sidestep via limit/pushout.
2. **Pause `closedness-residual`** (T-IDEAL-2) — statement audit required. The
   original framing was mathematically false for arbitrary proper ideals in a
   non-complete `locSubring`.
3. **Do NOT build `stacks-00MA-full` as unconditional faithful flatness** —
   that's mathematically false. Split into noetherianness (unconditional, can
   be a mathlib PR) and faithfully flat under Jacobson (already in mathlib).
4. **For `lane-c-arbitrary-c`**, build a topological refinement induction
   mirroring Wedhorn 8.34, not a search for "single Laurent pair at base".
   Theorem 5.10 is a LOCAL induction step.
5. **Don't expect Cor 8.32 algebraic faithful flatness to imply topological
   inducing**. The embedding field needs strictness/refinement arguments
   independently.

## Changes applied

### Modified tickets

- **T-OV-1** (Bivariate Example 6.38): PROMOTED to TOP PRIORITY. Added
  round-5 reviewer note with direct-proof prescription and "do not switch to
  limit/pushout" annotation.
- **T-IDEAL-2** (Closedness of proper ideals): REFRAMED to PAUSED-NEEDS-STATEMENT-AUDIT.
  Documented the reviewer's counterexample (`1 + X` becomes unit after
  completion). Documented the two candidate replacements (Spec-cover
  surjectivity OR safe Bourbaki closedness).
- **T-MATHLIB-STACKS-00MA** (Adic completion Stacks 00MA): REFRAMED. The
  "unconditional faithful flatness" half was mathematically incorrect. Split
  into the three true components per Stacks. Only noetherianness remains as
  a genuine mathlib gap.
- **T-EMBED-TOPO** (IsSheafy embedding via topological Example 6.38): Added
  round-5 reviewer note clarifying that (a) Cor 8.32 does NOT imply topological
  inducing, (b) Theorem 5.10 is a LOCAL induction step not a global theorem,
  and (c) the correct approach is topological refinement induction mirroring
  Wedhorn 8.34.

### New tickets

- **T-SPA-COVER-SURJ**: `Spec(∏ 𝒪_X(D_i)) → Spec(𝒪_X(C.base))` surjective
  for rational Spa-cover. Replacement for the false framing of T-IDEAL-2.
  Reviewer-prescribed alternative #1.
- **T-BOURBAKI-FG-CLOSED**: `fg_submodule_closed_of_complete_noetherian_adic`.
  Reviewer-prescribed safe Bourbaki form. Alternative #2 to T-IDEAL-2.
- **T-LANE-C-REFINEMENT-INDUCTION**: topological refinement induction for
  Lane C arbitrary-C, mirroring Wedhorn 8.34. Replaces the round-4
  search for "single Laurent pair at base".
- **T-LAURENT-REFINEMENT-TREE**: finite Laurent refinement tree from
  standard cover. Blocks T-LANE-C-REFINEMENT-INDUCTION.
- **STACKS-00MA-NOETH**: AdicCompletion of Noetherian is Noetherian
  (unconditional). Future mathlib upstream. Reviewer-prescribed reframing
  of T-MATHLIB-STACKS-00MA's noetherianness component.

### Reannotated

- **T-EMBED-TOPO-LANE-C-BASE** / `lane-c-single-laurent` (Theorem 5.10):
  now annotated as LOCAL induction step for T-LANE-C-REFINEMENT-INDUCTION,
  not a global theorem.

## Changes rejected by user

None — user said "apply all".

## Open questions remaining

None — reviewer addressed every Q1-Q4 sub-question.

## Decisions recorded but not actioned

- Wedhorn framing stays (no switch to Zavyalov; no switch to Hübner non-domain
  as main route). Validates the current architecture.
- Full strongly noetherian Tate scope stays (no narrowing to DVR base).
- Aux 10.7 (`productRestrictionSub_isInducing_of_finer_rational_continuous`)
  and Aux 10.8 (`naturalRefinementMap` + continuity + commutativity) are the
  core refinement-transfer tools for T-LANE-C-REFINEMENT-INDUCTION.

## Next work order (per reviewer priority)

1. T-OV-1 (bivariate Example 6.38) — top priority, direct proof.
2. T-IDEAL-2 statement audit (then either T-SPA-COVER-SURJ or T-BOURBAKI-FG-CLOSED).
3. T-LANE-C-REFINEMENT-INDUCTION (depends on T-LAURENT-REFINEMENT-TREE).
4. STACKS-00MA-NOETH (only if iterated-completion noetherianness is needed downstream).
