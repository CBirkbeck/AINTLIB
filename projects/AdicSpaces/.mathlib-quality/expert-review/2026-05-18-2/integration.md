# Reply integration — 2026-05-18-2 (Session 23)

Reply received: 2026-05-18.
Brief: ./brief.md
Reply: ./reply.md
Status: ALL 14 changes applied per user "apply all" directive.

## Interpretation summary

Reviewer's verdict was substantive and constructive — confirmed Session 22 audit findings, gave per-leaf cluster-by-cluster pass, raised 5 additional ⚠ concerns not in our explicit Qs (B1 route, C2 route, D9/D10 hypotheses, N2 circularity), and provided concrete decisions on the four SUSPECT leaves.

Most important guidance:
- A3 statement is correct (Wedhorn's theorem); only proof route is wrong → keep, retarget
- B5 is wrong-shaped → restate to cover-level form
- F5 should be the clean non-domain target → keep F4 as narrower domain variant
- I2 statement is true for all `f` (including units) → case-split or use row3_exact
- IsDomain is artifact; final theorem should not need it
- Cluster E should be moved out of main path
- Priority reorder: C1, C2, F4, I1, C3

## Changes applied (Session 23)

### Code changes (Statement-level)

| # | Change | File | Lines |
|---|--------|------|------:|
| 1 | RESTATED B5 to `hSpa_surj_cover_level` (cover-level form); kept legacy as WRONG-SHAPED | StructureSheaf.lean | ~30 added |
| 2 | RESTATED F2 to `exists_ideal_generators_refining_cover_relative` (over O(C.base)); kept legacy | TateAcyclicityResiduals.lean | ~25 added |
| 3 | F3 docstring marks SCOPE-ERROR inheritance | TateAcyclicityResiduals.lean | 3 |

### Code changes (Docstring/route-constraint)

| # | Change | File | Line ~|
|---|--------|------|------:|
| 4 | A1 docstring: NARROWER parametric variant, not consequence of strong noeth | StructureSheaf.lean | 1103 |
| 5 | A3 docstring: new clean route via C1/C2/Lemma 8.34; exclude deleted chain | StructureSheaf.lean | 1543 |
| 6 | B1 docstring: route MUST be via C3 + D8, NOT B5 | StructureSheaf.lean | 1302 |
| 7 | C2 docstring: Spec-surjectivity must be cover-level via hSpa_surj_cover_level | StructureSheaf.lean | 1496 |
| 8 | I2 docstring: case-split on IsUnit f or use row3_exact | LaurentCoverExact.lean | 1939 |
| 9 | N2 (hSpa_surj_from_spanTop body) CIRCULARITY warning: must NOT route via C2 | Cor832.lean | 521 |

### No-op (already done in prior stages)

| # | Note |
|---|------|
| 10 | D8 docstring already corrected in Stage 1 (Wedhorn 7.42 citation dropped). Full rename of the lemma name (drop wedhorn_7_42_ prefix) deferred to a later cleanup pass. |
| 11 | Cluster E is already orphaned in practice (not imported by IsSheafy main path after Session 21 deletions). No additional move needed. |

### Project/memory

| # | Change |
|---|--------|
| 12 | Saved `feedback_taint_graph.md` — for every false leaf X, run taint graph BEFORE deletion (4-category classification) |
| 13 | Updated decomposition.md Session 23 section with reviewer's verdict shifts + reordered priorities |
| 14 | Updated state.md for this session folder (next phase) |

## Sorry-count delta

**120 → 122** (+2 for the two restated theorems alongside legacy):
- `hSpa_surj_cover_level` (B5 restatement) +1
- `exists_ideal_generators_refining_cover_relative` (F2 restatement) +1
- All other changes are docstring-only / route-constraint notes

Both legacy forms (`exists_hSpa_points_global_*` and `exists_ideal_generators_refining_cover`) are marked WRONG-SHAPED but kept until downstream consumer migration; they'll be removed when:
- A2's `hSpa` hypothesis is updated to match the new B5 signature (legacy B5 removable)
- P3–P8 consumers are migrated to the relative F2 form (legacy F2 removable)

## Verdict shifts (full list)

(Same as in decomposition.md §Session 23 update — see there for the table.)

## Changes rejected by user

None — user said "apply all".

## Open questions remaining

Reviewer answered all 7 meta-questions + per-cluster pass. No questions remaining for this round.

The natural next round would be after the F2/F5/A3 statement restatements have downstream consumer migration in place — to confirm the new shapes are mathematically right and the cascade is complete.

## Decisions recorded

1. A3 stays as final theorem target; proof route is via C1+C2+Lemma 8.34
2. B5 restatement is `hSpa_surj_cover_level`; legacy form quarantined
3. F2 relative form added; legacy quarantined; downstream consumers TBD
4. IsDomain removal from A1/A2/F4: documented as "narrower variant" status; no signature change (keep IsDomain in narrower form)
5. F5 is the clean non-domain target; refactor F4/F5 architecture pending
6. I2 case-split or row3_exact route documented
7. Cluster E orphan status confirmed; no consumer to fix
8. Priority order: C1, C2, F4, I1, C3 (was C3, C1, C2, F4, I1)

## Recommendation for next session

Pick highest-leverage target: **C1 (`prop_8_30_flat_clean`)**. Reviewer's recommendation per Q-META.5. Discharge route:
- basic rational step flatness via Tate-algebra quotients (Wedhorn Lemma 8.31)
- + decomposition/transitivity of rational localizations (project has T-RATIONAL-FLAT-GENERAL chain)
- → arbitrary rational restriction flatness

Estimated work: ~100 LOC assembly. Closes C2 once done; closes B7 + B8 cascade.
