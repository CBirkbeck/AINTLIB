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
| 1 | `exists_window_subdatum_nbhd` | CurveAdicPresentation | 235 | **~45** | 7 |
| 2 | `PhiHatK_teichCoeffAr` | ArCompletion | 200 | **5** | 11 |

**Bar: no proof over 50 lines.**  My first pass stopped at 79 and 167 on the reasoning
that "helpers would carry more hypotheses than content".  That is not a reason — it is
simply what decomposing a tightly-coupled proof costs.  Corrected below.

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


## 2 (redone). `PhiHatK_teichCoeffAr` 200 -> 5, twelve declarations, all under 50

| Declaration | Lines |
|---|---|
| `PhiHatK_teichCoeffAr` | 5 |
| `valued_PhiHatK_teichCoeffAr_sub_le` | 43 |
| `gaussValueF_sub_teich_prefix_le` | 40 |
| `exists_base_approx_and_index` | 26 |
| `tailValueF_alocToWittF_le` | 25 |
| `exists_le_inv_pow` / `exists_holder_modulus_on_range` | 21 |
| `eventually_teichCoeffF_sub_le` | 19 |
| `gaussValueF_p_pow_teichmuller_sub_le` | 16 |
| `eq_of_forall_valued_sub_le` | 9 |
| `valued_sub_le_of_chain` | 7 |
| `perfectoidValuation_toOF_pos` | 5 |

**The move I had skipped: 157 of the 200 lines were a single `have hkey`.**  Lifting that
one `have` to its own lemma made the theorem a 5-line consequence and gave the ε-argument
a name to split further.  Always look for a dominant `have` before anything else.

**The "too many hypotheses" objection never materialised.**  `exists_base_approx_and_index`
takes 3 hypotheses and returns 5 facts; `tailValueF_alocToWittF_le` takes 5.  Ordinary.

**The biggest single win came from MERGING, not splitting.**
`exists_holder_modulus_on_range` absorbs the value cap, the Hölder modulus and the
per-coordinate bound into one statement — *there is a δ that works uniformly across the
first N coordinates* — removing 21 lines at once, and making five setup lines (`ϖF`, `c`,
`hϖne`, `hc0`, `hclt`) dead as a side effect.  When several consecutive steps exist only to
feed one conclusion, state the conclusion and swallow all of them.

### Technique checklist for the remaining 105 targets
1. Is one `have` most of the body?  Lift it first.
2. Is the statement a conjunction?  Split it (audit item 12).
3. Does a block appear twice (e.g. `hrest`/`hdrop`)?  Extract once, use twice.
4. Do N consecutive steps exist only to feed one fact?  Merge them into one lemma stating
   that fact — this beats splitting them individually.
5. A chain with no seams still cuts: consecutive segments, each taking the previous
   segment's outputs as hypotheses.  Hypothesis count is the cost, not a blocker.

## 1 (redone). `exists_window_subdatum_nbhd` 235 -> 36

The last cut was the one I had refused: lift the ENTIRE tail — build the neighbourhood and
verify all three `refine` bullets — into `exists_windowNbhd_spec`. I had left the bullets
inline because they "share too much local context". They do; the lemma takes 8 hypotheses
and that is fine.

Residual over the bar in this file (body lines, excluding signature):
* `exists_windowNbhd_spec` 55 — the three bullets; splits again into y∈V / V≤O / homeo
* `windowTraceHomeomorph` 67 — see the mathlib finding below

### MATHLIB finding (audit item 13) — missed on the first pass
`windowTraceHomeomorph` hand-rolls a homeomorphism between two subtypes: forward map,
backward map, both inverse proofs, both continuity proofs — 67 lines.  Mathlib has
**`Homeomorph.subtype`** (`Mathlib/Topology/Homeomorph/Lemmas.lean:161`):

    def subtype {p : X → Prop} {q : Y → Prop} (h : X ≃ₜ Y) (h_iff : ∀ x, p x ↔ q (h x)) :
        {x // p x} ≃ₜ {y // q y}

which builds all six components from a single `iff`.  It does not collapse this def to one
line — our two subtypes sit over *different* ambient types (`Spa B_n` and the `𝒴`-carrier),
so only the chart leg is covered and the carrier-vs-window identification still needs
building — but the chart leg should go through `Homeomorph.subtype` rather than by hand.
**This is exactly what audit item 13 exists to catch, and I skipped it when first
extracting the def.**

## 3. `valued_degAr_PhiHatK_convF` 164 -> 7 declarations, all under 50

| Declaration | Total |
|---|---|
| `valued_sum_antidiagonal_lt` | 25 |
| `gaussTerm_mul_lt_of_ne_dominant` | 20 |
| `gaussTerm_convF_attain` | 43 |
| `gaussTerm_convF_lt_of_gt` | 17 |
| `valued_PhiHatK_convF` | 17 |
| `degAr_PhiHatK_convF` | 36 |
| `valued_degAr_PhiHatK_convF` | 11 |

Three techniques stacked:
1. **Duplication inside the proof.** `hrest` and `hdrop` ran the same 20-line antidiagonal
   argument — bound the sum by its sup, pick the maximiser, split `ρⁿ = ρ^k₀·ρ^(n−k₀)`,
   apply the strict bound.  `valued_sum_antidiagonal_lt` replaces both.
2. **The `∧`-split** (audit item 12), which I had talked myself out of: the conclusion is a
   genuine conjunction of two independently-usable facts, so `valued_PhiHatK_convF` and
   `degAr_PhiHatK_convF` are now separate public theorems and the bundled statement is a
   4-line `⟨_, _⟩`.  Its one consumer still destructures it unchanged.
3. Extracting the attainment and the drop as named facts about `convF`.

Two Lean gotchas from this one:
* `zero_le` in `NNReal` takes **no** explicit argument — `zero_le (ρ ^ n)` is a "function
  expected" error.
* **`set` only folds occurrences present when it runs.** `have hattain := …` obtained
  *after* `set a := …` keeps the unfolded spelling and then will not match the folded goal.
  Hoist such `have`s above the `set` block.

### Metric note
The bar is on **proof bodies**, not declarations.  `groebner_reduce` is 163 lines but ~72
are signature + a six-fold conclusion; its body is ~90.  Measuring by body also confirms
the statement of `groebner_reduce` must NOT be split — it is a shared-witness existential
`∃ g m J, P₁ ∧ … ∧ P₆`, which `references/statement-splitting.md` explicitly exempts.

### Remaining over-50 bodies (measured)
ArCompletion 6, Euclidean 14, CurveAdicPresentation 2 — plus the rest of the 107.
