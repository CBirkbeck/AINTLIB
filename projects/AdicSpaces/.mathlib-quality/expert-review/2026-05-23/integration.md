# Reply integration — 2026-05-23

Reply received from senior algebraic geometer / Huber–Wedhorn expert on 2026-05-23.
Brief: ../2026-05-23/brief.md
Reply: ../2026-05-23/reply.md

## Interpretation summary

| # | Reviewer point | Type | Confidence |
|---|---|---|---|
| 1 | L4 IS false; deeper than the `0` analysis — even nonzero f can vanish at v | direct answer, sharpens diagnosis | high |
| 2 | Replace L4, don't prove it. New artifact: extract from `R(insert f T/s) ∩ R({f}/f)` | direct prescription | high |
| 3 | Reject fix (b): v(s) ≠ 0 too weak for spanTop_iff_noCommonZero_spa | direct answer | high |
| 4 | Reject fix (c): post-filter unsafe — may destroy cover | direct answer | high |
| 5 | Cascade real; 4 wrappers "assembly closed but mathematically open" pending L4 fix; no body edits if interface preserved | direct answer + tracking guidance | high |
| 6 | L1 stays YELLOW; Wedhorn Prop 6.18 NOT enough; cite Hübner/Zavyalov | direct answer | high |
| 7 | L11 typeclass is structural but reflects real underlying theorem; adopt Approach 1 (prove the class) | direct answer + recommendation | high |
| 8 | Reorder: F12 → L1 strengthened → L4 replacement → Tate-aux → ... | direct answer | high |
| 9 | L1 statement should already incorporate `R({f}/f)` non-vanishing clause | sharpens L1 | high |

All 6 brief questions directly addressed. **Zero unanswered Qs.**

## Changes applied

### Code-level decisions (no Lean edits this pass — left for worker)
- C1: Replace L4 — do not prove
- C2: Strengthen C2 source (`exists_per_D_finite_cover_of_localBasisHyp`) via compactness on refined opens
- C3: Strengthen L1 (`LocalBasisHyp` predicate) to include non-vanishing clause
- C4: Edit `span_top_of_per_D_finite_cover` body to use strengthened C2 output, drop L4 call
- C5: Adopt Approach 1 for T-LOCLIFT-PRESERVATION

### Artifacts
- A1: B2 #21 logged in `.mathlib-quality/b2_log.jsonl` (line 21)
- A2: `.mathlib-quality/decomposition.md` updated:
  - Header note added with reviewer verdict summary
  - Tier 0 table: 4 wrappers marked **(†)** "assembly closed but mathematically open"; footnote added
  - L1 section: "STATEMENT STRENGTHENED" annotation + new statement spec
  - L4 section: "REPLACED / B2 #21" + replacement plan + rejected alternatives
  - L11 section: "Discharge decision: adopt Approach 1" added
  - Execution order revised: F12 → L1 strengthened → L4 replacement → Tate-aux → ...
  - Action items: L4 audit marked DONE
- A3: `docs/ACYCLICITY-CRITICAL-PATH-PLAN.md` not edited (already noted as stale at the
  top of decomposition.md; superseded by the decomposition.md frontier)

### Task board
- T1: Task #114 CREATED — "L4-replacement: nonvanishing cover extraction"
- T2: Task #67 (P7 / W1 `exists_standard_cover_refining`) UPDATED — notes L1 strengthening + L4 obviation
- T3: No separate L4 ticket existed — no removal needed
- T4: Execution order reflected in #114 + decomposition.md (no separate ticket reorder needed)
- T5: Task #38 (T-LOCLIFT-PRESERVATION) UPDATED — adopt Approach 1

## Changes rejected by user

(none)

## Open questions remaining

(none — reviewer answered all 6 directly)

## Decisions recorded but not actioned

- Approach 1 vs Approach 2 for L11: Approach 1 chosen and recorded in task #38 + decomposition.md, but the actual proof work is downstream (task #38 + #87 chain).
- The four tainted (†) wrappers are NOT re-flagged as "open" in the task board, because the L4 replacement preserves their downstream interface — they will remain "done at the assembly level" once #114 lands. The mathematically-open status is recorded in decomposition.md but does not require a status flip in the tracker.
