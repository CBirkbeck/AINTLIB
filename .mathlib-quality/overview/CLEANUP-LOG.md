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

---

# /decompose-proof pass — biggest proofs first

107 bodies exceed 60 lines. Working down from the largest.

| # | Declaration | File | Before | After | Helpers extracted |
|---|---|---|---|---|---|
| 1 | `exists_window_subdatum_nbhd` | CurveAdicPresentation | 235 | **79** | 6 |
| 2 | `PhiHatK_teichCoeffAr` | ArCompletion | 200 | **167** | 3 |

## 1. `exists_window_subdatum_nbhd` 235 → 79 (−66%)

Six named `private` helpers, all placed above it; statement byte-unchanged.
The valuable one is `exists_rationalLocData_mem_subset` — **rational opens over a window
chart are a neighbourhood basis** — which was the mathematical content of the middle
third of the old proof, previously inlined and unnameable.

Also `exists_isOpen_mem_yTop_iff`, `exists_isOpen_chart_trace`,
`exists_finset_basicOpen_mem_subset` (basic opens are a basis of `Spv B`, in the exact
shape `exists_spanning_presentation_of_mem_basicOpens` consumes), `windowNbhd`,
`windowTraceHomeomorph`.

The extraction exposed dead code (`hIM'` became unused once the homeomorphism moved out)
and let the `V ≤ O` bullet shrink, because the new `hQmem` is a pointwise iff rather than
a set equality needing a two-step unfold.

## 2. `PhiHatK_teichCoeffAr` 200 → 167 (−17%)

A much harder target: unlike #1 it is a *linear chain* of `have`s, each feeding the next,
so there are few independent seams. Three genuinely generic lemmas came out:

* `exists_le_inv_pow` — every `NNReal` is dominated by a power of `c⁻¹` when `0 < c < 1`,
  and that power can be taken `≥ 1`. (21 lines of inline algebra → one call.)
* `eq_of_forall_valued_sub_le` — squeeze-to-zero in `hatK`. Reusable; this "value below
  every positive bound" step recurs across the file.
* `gaussValueF_p_pow_teichmuller_sub_le` — one Teichmüller piece is small, uniformly in
  the index (the `ρ ^ i ≤ 1` factor).

Gotcha worth remembering: `gaussValueF_p_pow_teichmuller_sub_le` needs `ϖ` in its *proof*
but not its *statement*, so Lean did not auto-include the section variable — it needs an
explicit `include ϖ in`.

The residual 167 lines are the `hkey` ε-argument: choose ε′, a base approximant and its
decay thresholds, a working index, a cap, a Hölder modulus, a late approximant, prefix
splitting, then a three-term ultrametric chain. Each step consumes the previous one's
witnesses; helpers here would carry 8–12 hypotheses apiece.
