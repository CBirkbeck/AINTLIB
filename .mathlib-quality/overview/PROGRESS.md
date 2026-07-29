# FarguesFontaine folder — /overview + full /cleanup campaign

**Goal (user, 2026-07-28):** run `/overview` on everything in
`projects/AdicSpaces/Adic spaces/FarguesFontaine/`, then act on its suggestions with the
full `/cleanup` procession and `/decompose-proof` where needed, until **every single result
in the folder has had a full `/cleanup`**. Slow and methodical is explicitly fine.

## Scale
- 46 files, 39,787 lines
- **1656 declarations** (1586 public, 70 private)
- 0 `sorry`, 5 non-linter `set_option`s
- Baseline at start: `lake build '«Adic spaces»'` GREEN, `isAdicSpace_xVObj` axiom-clean

## Scope decision
Running `/overview` Steps 1–8. **Step 9 (mathlibable) deliberately deferred**: the skill
estimates 2–4 h for 35 declarations; at 1586 public decls that is hundreds of hours, and its
purpose (mathlib-PR triage) is orthogonal to the stated goal (cleanup coverage). Offered to
the user as a separate later run.

## Phase 1 — per-file inventory (46 workers, output to `inventory/<File>.md`)

Workers write the full per-declaration inventory to a file and return only the File Summary
(1656 entries cannot be held in context).

### STATUS as of the RobbaPresentation split

COMPLETE (16): Euclidean, Groebner, ChartVObj, IntervalSplitting, CurveObject, Presentation,
WittF, YSpace, UniformizerEquivariance, YStalks, YPresheaf, ChartData, IntervalRing,
ArCompletion, + GaussNorm(part 1 of 2)

IN FLIGHT: GaussNorm pt2, FrobeniusGauss, ChartComparison, FrobeniusValuation

STILL TO DISPATCH (~28): RobbaPresentation (SPLIT INTO HALVES — stalled twice whole),
CurveVMorphism, Curve, CurveAdicPresentation, RestrictionInjective, AinfHuber, BigWindows,
CurveYSlice, CurveChartVIso, ChartBIQ, SheafyBI, RobbaCorrespondence, FrobeniusLimit,
ChartSpa, IntervalCoordinates, CurveQuotientLeg, PerfectoidFieldCharP, YCharts, GaussPoint,
FrobeniusAction, CurveAdicSpace, UniformizerTwist, FrobeniusSpa, YSheaf, RobbaLoc,
StronglyNoetherianB, CurveVChart, CurveIsAdicSpace

### (original batching plan)
### Batch 1 — DISPATCHED
| File | Lines | Status |
|---|---|---|
| RobbaPresentation.lean | 6578 | dispatched |
| Groebner.lean | 2424 | dispatched |
| Presentation.lean | 2398 | dispatched |
| Euclidean.lean | 2224 | dispatched |
| WittF.lean | 2058 | dispatched |
| IntervalRing.lean | 1844 | dispatched |

### Batch 2 — pending
ArCompletion (1787), CurveObject (1781), ChartData (1674), ChartVObj (1338),
IntervalSplitting (1029), YStalks (996)

### Batch 3 — pending
YSpace (963), GaussNorm (923), UniformizerEquivariance (801), YPresheaf (798),
FrobeniusGauss (782), ChartComparison (632)

### Batch 4 — pending
FrobeniusValuation (626), CurveVMorphism (611), Curve (580), CurveAdicPresentation (551),
RestrictionInjective (536), AinfHuber (451)

### Batch 5 — pending
BigWindows (425), CurveYSlice (397), CurveChartVIso (365), ChartBIQ (357), SheafyBI (356),
RobbaCorrespondence (345)

### Batch 6 — pending
FrobeniusLimit (340), ChartSpa (319), IntervalCoordinates (311), CurveQuotientLeg (308),
PerfectoidFieldCharP (274), YCharts (240)

### Batch 7 — pending
GaussPoint (190), FrobeniusAction (180), CurveAdicSpace (179), UniformizerTwist (166),
FrobeniusSpa (157), YSheaf (152)

### Batch 8 — pending
RobbaLoc (138), StronglyNoetherianB (86), CurveVChart (59), CurveIsAdicSpace (58)

## Structural scan — DONE (`scan-structural.md`), mechanical half of Steps 5-8

Scanned 1632 declarations across all 46 files:

| Finding | Count |
|---|---|
| Bodies > 60 lines (decompose-proof candidates) | **80** |
| Bodies 30-60 lines (STRUCTURE watch) | 154 |
| Declarations with no docstring | **206** |
| Lines > 100 codepoints | 115 (mostly FrobeniusGauss 12, ChartVObj 10) |
| Forbidden name patterns / abbreviations | **0** |
| `≥`/`>` in a signature (orientation) | **0** |
| Banned `set_option` (maxHeartbeats/maxRecDepth) | **0** |
| Cross-file name collisions | 2, both false positives |

The 5 non-linter `set_option`s are all benign: `warn.classDefReducibility false` (x2, a
warning suppression) and `maxSynthPendingDepth 1` (x3, a *reduction*, explicitly allowed).
The 2 name "collisions" (`isUniformAddGroup`, `presheaf`) are same-name declarations in
different namespaces, not duplication.

Biggest decompose-proof targets: `exists_window_subdatum_nbhd` (228 lines),
`PhiHatK_teichCoeffAr` (197), `valued_degAr_PhiHatK_convF` (156), `resIHom_injective` (150),
`digit_sub_le` (145).

**So the folder's hard gates already pass** — the work is documentation (206), structure
(80 + 154), line packing (115), and whatever semantic duplication / mathlib-dedup /
generalisation the inventory turns up.

## Worker reliability note — RESOLVED, three lessons

1. **"Agent failed" != "work lost."** Workers stall in the REPLY stream *after* the artifact
   is written.  ChartData reported failure with a complete 773-line artifact.  ALWAYS check
   `inventory/<File>.md` (entry count vs source decl count, and for a `### File Summary`)
   before relaunching; recover the summary with `sed -n '/### File Summary/,$p'`.
2. **Relaunch in RESUME mode**, not from scratch: tell the worker to read the partial
   artifact, find the last declaration covered, and continue from the next.  ArCompletion
   went 20/58 -> 58/58 this way.
3. **Split files that stall repeatedly** into explicit line ranges.  GaussNorm died three
   times whole; as two halves it went through immediately.  RobbaPresentation (6578 lines,
   stalled twice) must be split.

## (historical) Worker reliability note
Two large-file inventory workers (Presentation, ArCompletion) died on transient
"Response stalled mid-stream" API errors. Relaunched with an INCREMENTAL instruction
(read ~350-line chunk -> write immediately -> next chunk) rather than accumulating the
whole inventory before writing. Use that pattern for all remaining large files.

## DEDUP PASS — COMPLETE (2026-07-29). See `DEDUP.md`.

Ran ahead of the rest of Phase 2 because the user asked for it directly. Four systematic
scans over all 46 files / 1463 declaration bodies; **all deletable duplication is gone**.

| Commit | What |
|---|---|
| `f3eae1ab3` | `comap_comp_apply` hoisted to ValuationSpectrum (2 byte-identical private copies) |
| `8ef7c94bc` | the primed/unprimed twin sweep — 14 pairs classified, net −11 declarations |
| `c3f17193e` | last same-body duplication (`Nfst`/`Nsnd` via mathlib, U/V wandering lemma, `chartTate`) |
| `db9177ae8` | `valued_ball_mem_nhds`: one lemma instead of three copies across three files |
| `c4e4cfe6f` | the 73-line Euclidean copy → `valued_prefix_sub_sub_le` |

Every commit gated on a separate `lake build '«Adic spaces»'` (3365 jobs, 0 errors, 0
sorries) with `#print axioms` on all touched declarations; `isAdicSpace_xVObj` axiom-clean
throughout.

**Handed back to the user as decisions, not done silently:**
- the subscript-`₂` family in RobbaPresentation (~600 lines, largest and riskiest
  opportunity in the folder) — needs a statement change, `/generalise` lane
- the remaining `_fst`/`_snd`, U/V, `_left`/`_right` twins — same reason
- the 29 uncited dead declarations identified before the dedup pass — several are
  meaningful named results, so deletion is an owner call

## Phase 2 — deep analysis (Steps 4–8), sequential after inventory
- Step 4 Mathlib API audit (most important)
- Step 5 Moral duplications (pairwise table REQUIRED)
- Step 6 Generalisation opportunities (with literature search)
- Step 7 API design review
- Step 8 Junk identification

## Phase 3 — write `PROJECT_OVERVIEW.md`

## Phase 4 — act: full `/cleanup` per file + `/decompose-proof` where flagged
Tracked in a table appended here once the overview lands.

## Notes / invariants to preserve
- `lake build '«Adic spaces»'` must stay green; `isAdicSpace_xVObj` axiom-clean.
- NEVER add `set_option maxHeartbeats`; no `sorry`.
- Path contains a space — quote it; `lake` runs from the repo root.
- Already fully cleaned this session (Campaign 9 files): CurveVMorphism, CurveQuotientLeg,
  CurveVChart, CurveYSlice, CurveAdicSpace, CurveChartVIso, CurveIsAdicSpace — these still
  need the *full* per-declaration `/cleanup` procession, only the file-level pass was done.
