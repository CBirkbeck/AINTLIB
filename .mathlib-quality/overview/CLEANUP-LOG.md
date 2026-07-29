# Per-declaration /cleanup log — FarguesFontaine

Full 11-phase `/cleanup` procession, one audit per declaration.
Adaptation: Phase-4 audits run inline (no subagents per the session's tool policy);
`lake build <module>` substitutes for `lean_diagnostic_messages` (no lean MCP tools).

| File | Decls | Status | Commit |
|---|---|---|---|
| CurveIsAdicSpace.lean | 2 | DONE | (this commit) |

## CurveIsAdicSpace.lean — 2/2 declarations

**Phase 0** baseline green, 0 file diagnostics.
**Phase 2** punch-list: 3 items (A.2 no Main-results section; C.1 docstring decoration;
C.2 docstring depth). A.1 `Authors:` line absent → project-wide gap (11/46 files have
one); skill forbids inventing names → NO ACTION, coordinator sweep.
**Phase 3** added `## Main results` + `## References`. Bib key corrected to the project's
established `wedhorn2019adic` (my first draft invented `wedhorn2019` — 1 use vs 3).
A.6 `set_option linter.overlappingInstances false` TESTED load-bearing (removing it
yields 2 warnings, one per decl) → KEPT.

**Phase 4 — item 18 drop-test (the substantive find).**
The linter's own advice was only 1/3 right:

| Instance | Linter says | Drop-test | Result |
|---|---|---|---|
| `[TopologicalSpace F]` | "may be removed" | 22 errors | KEPT |
| `[NonarchimedeanRing F]` | "may be removed" | 22 errors | KEPT |
| `[IsTopologicalRing F]` | (not mentioned) | **0 errors** | **DROPPED** |

The two the linter proposed carry more than the continuity instances it reasons about;
the one it did not mention is the genuinely redundant one. Dropping it does NOT clear
the suppression (the other two complaints remain), but it removes a redundant hypothesis
from both headline theorems on its own merit.

**Phase 4 — other.** Both bodies 3→2 lines (rule 1.18: trailing `fun` needs no parens).
Both docstrings rewritten for item 10 (tips-when-applying + difference-from-neighbour);
the `★ ALL-CAPS ★` decoration normalised to mathlib bold sentence case (it was a one-off —
the only other `★` in the project, in CurveChartVIso, is a *referenced label* `(★)`).

**Phase 6.5 simplify — one finding, deliberately SKIPPED (out of diff scope).**
`isAdicSpace_xVObj` and `isAdicSpace_yVObj` pass the *same* 2-line lambda, and the two
`_of_windowVIso` helpers' `hviso` hypotheses are byte-identical. Extracting the lambda
here would require restating that 8-line type — trading a 2-line term duplication for an
8-line type duplication. **The deep fix belongs in `CurveAdicSpace.lean`: name the
hypothesis type once (e.g. `abbrev WindowVIso : Prop := …`), then all three sites
reference it.** DO THIS when cleaning CurveAdicSpace.lean, then revisit here.

**Phase 6.6 buzz — FAST-BOARD.** Whole file: elaboration 22.1ms, typeclass inference
31.8ms. Nothing near the 1000ms budget. maxHeartbeats raises removed: 0 · added: 0.

**Follow-ups raised**
- (altitude) The `[IsTopologicalRing F]` drop applies to the same variable block in
  ~26 sibling files — a project-wide sweep, not a per-file fix.
- (generalise, big change) Literature: the general form is the RELATIVE curve
  `X_S = 𝒴_(0,∞)(S)/φ^ℤ` for `S` any perfectoid space in char `p`. Ours is
  `S = Spa(F, 𝒪_F)`. Restating over a perfectoid base would touch every definition in
  the campaign — user approval required.
