# GOAL: clean up all of the adic code

User directive (2026-07-29): remove **all** maxHeartbeat options; `/decompose-proof` every
proof over 50 LOC; run the **full** `/cleanup` on **every** lemma. Full budget, no stopping.

## Measured scope (baseline)

    files                      376
    lines                  231,153
    declarations             7,926   <- each needs full /cleanup
    proof bodies > 50 LOC      486   across 140 files
    heartbeat raises           104   across 13 files

## Order of work, and why

**1. Heartbeats first.** Removing a raise either just works, or exposes a proof that is
genuinely slow — and slow proofs are exactly the ones needing decomposition. So this pass
generates the priority list for task 2 instead of duplicating it.

**2. Decompose the 486**, largest first, batched per file to amortise the ~40 min full-build
gate. Budget ~1.5-2 extraction rounds per proof (measured, see CLEANUP-LOG.md).

**3. Full /cleanup per declaration**, file by file.

## Heartbeat inventory

| File | raises |
|---|---|
| WedhornCechAcyclicity.lean | 56 |
| FJP/FiniteJetFunctoriality.lean | 12 |
| RelativePieceKeystoneOpen / Gen / (base) | 6 each |
| Wedhorn828.lean | 4 |
| FJP/FiniteJetChart.lean | 3 |
| FarguesFontaine/RobbaCorrespondence.lean | 3 |
| Vendored/CoramRestrictedIso.lean | 2 |
| FJP/FiniteJetUniformDomain.lean | 2 |
| FJP/FiniteJetSheafTransfer.lean | 2 |
| LaurentOverlap.lean | 1 |
| ExampleUnitDisc.lean | 1 |

Values: `maxHeartbeats` 1000000 (x53), 1600000 (x26), 800000 (x9), 6400000, 4000000;
`synthInstance.maxHeartbeats` 800000 (x6), 400000 (x2); `maxSynthPendingDepth 8` (x3).
**KEEP `maxSynthPendingDepth 1` (x3) — that is a REDUCTION, not a raise.**

## Worst files for over-50 proofs
WedhornCechAcyclicity 55 · LaurentRefinementCore 28 · RobbaPresentation 17 ·
TateAcyclicityFinalAssembly 14 · Euclidean 12 · EmbeddingTopo 11

Largest single proofs: `wedhorn_lemma_834_propA3_part1_gluing` 450 ·
`isIntegral_of_forall_continuous_valuation_le_one` 405 ·
`exists_lift_norm_le_of_closed_range` 389 · `tateAlgebra_flat` 352

## Progress
Full detail per file appended below as work lands.

---

## Task 1 — heartbeat removal

### Scope corrections found while starting
* `FarguesFontaine/RobbaCorrespondence.lean`'s 3 hits are `maxSynthPendingDepth 1` —
  **reductions**, not raises. Not in scope. (104 -> 101)
* `Vendored/` is third-party: William Coram's code vendored 2026-07-04 pending its own
  mathlib PR. Modifying it would diverge from upstream and complicate that PR. Its 2 raises
  stay, documented. (101 -> 99)

### Done
| File | raises removed | how |
|---|---|---|
| ExampleUnitDisc.lean | 1 | removed; proof compiles as-is |
| LaurentOverlap.lean | 1 | required a real fix — see below |

### TECHNIQUE: typed `have` + forward rewriting beats goal rewriting
`LaurentOverlap.TA_B_bivariate_to_outerQuotient_evalHom₂_one_sub_algMap_b_Y_eq_zero`
timed out at `isDefEq` (200k) once the raise came off.  The cost was
`rw [show (1 : _) = Ideal.Quotient.mk I 1 from rfl]` on the GOAL: that makes the elaborator
search the goal for a `1` and check it defeq to `mk 1`, across a Tate algebra over a
quotient.  Swapping the `rfl` for `← map_one` moved the timeout but did not remove it.

The fix inverts the direction:

    have key : mk I (1 - algebraMap _ _ (mk J X) * X) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]; unfold outerLaurentOverlapIdeal
      exact Ideal.subset_span rfl
    rw [map_sub, map_one, map_mul] at key      -- forward, on a pinned type
    exact key

State the identity on a LIFTED element with its type pinned by the `have`, then push the
ring-hom maps forward through it.  Forward rewriting on a known expression has nothing to
search.  **Compiles at default heartbeats.**

Also removed: a `have h_eq : <expr> = <same expr> := rfl` followed by `rw [h_eq]` — a
literally reflexive no-op, and part of what the elaborator was paying for.

**Generalise this**: most `isDefEq` timeouts in this codebase are goal-directed rewriting
against quotient/algebraMap chains.  Try the typed-`have`-and-push-forward shape before
anything else.

### Task 1 COMPLETE (bar 5 deferrals): 94 of 99 raises removed

| File | removed | proof changes needed |
|---|---|---|
| WedhornCechAcyclicity | 53 of 56 | **none** |
| RelativePieceKeystone{,Gen,Open} | 18 | none |
| FJP/FiniteJetFunctoriality | 12 | none |
| Wedhorn828 | 4 | none |
| FJP/FiniteJetChart | 3 | none |
| FJP/FiniteJetUniformDomain | 2 | 1 real fix (gcongr -> explicit term) |
| LaurentOverlap + ExampleUnitDisc | 2 | 1 real fix (rewrite direction) |

**89 of 94 removals required NO proof change.**  These raises were litter — added during
proof development, never removed after the proof was golfed.  The file with 56 needed 3.

### The 5 remaining, all GOAL-DEFERRED in-source, all on the task-2 list
| Decl | raise | note |
|---|---|---|
| `gluing_JetA` | 6.4M | 279-line body; times out even at 1.6M |
| `productRestrictionSub_isEmbedding_JetA` | 1.6M | shares its subtype-instance whnf cost |
| `genPiece_relative_overlap_square₁`/`₂` | 1.6M | on the over-50 list |
| `imageCover` | 4M | on the over-50 list |

They come off as a by-product of decomposing those proofs.

### GOTCHA: finding a declaration's preamble start
I broke this twice.  To insert above a declaration you must scan back over: attributes
`@[...]`, `include`/`omit ... in`, `set_option ... in` — and **when you hit a line ending
`-/`, jump to its opening `/--`**.  A docstring BODY line beginning with `--` looks exactly
like an attribute line to a naive scanner, so I spliced raises *inside* docstrings; and
placing a `set_option` between an `include ... in` and its declaration breaks the binding.

## Task 2 — decompose the over-50 proofs

Re-measured: **486** bodies over 50 across 140 files (whole tree; the FarguesFontaine 103
is a subset).  Worst: WedhornCechAcyclicity 55 · LaurentRefinementCore 28 ·
RobbaPresentation 17 · TateAcyclicityFinalAssembly 14 · Euclidean 12 · EmbeddingTopo 11.

`wedhorn_lemma_834_propA3_part1_gluing` (454 lines) carries **48 comment seams with
numbered Steps 1-8** — the author's own decomposition.  Highly tractable: name the steps.

### Misplaced-lemma sweep (run before decomposition — cheap, and shrinks the work)

Script: `scratchpad/misplaced.py`.  Indexes every top-level lemma statement (3597 of them),
then scans every inline `have <n> : <stmt>` for a statement matching one.  Results: **89
matches**, of which **4 declared later in the SAME file** (the pure-win category).

Adjudicated:
| Case | Verdict |
|---|---|
| `WittF:1666/1677` vs `bddAbove_gaussTermF_of_coords_shift` (1991) | **REAL, fixed** — the 11-line argument was written out inline TWICE (`hBX`, `hBY`) while the lemma sat 325 lines later. 22 lines -> 4. |
| `Groebner:200` vs `gaussNormRPS_ne_zero` (235) | **REAL, fixed** — 31-line inline copy -> 2 lines. |
| `IntervalRing:1157` vs `wI_le_of_approx` | **FALSE POSITIVE** — the `have hb … := hz` is a one-liner; the matcher only matched the conclusion. |
| `PresheafTateStructure:127` vs `locSubring_induced_eq_adicTopology` (309) | **REAL but CIRCULAR** — the inline `have key` is a step *inside* `locSubring_subspace_eq_adic` (118), and the later lemma proves the same fact *from* that finished theorem. Moving it up fails (its own dependency is in between). Fix = extract the shared step above both, not relocate. Queued. |

The 85 cross-file matches need filtering: many are `have h : P := the_lemma …`, which is not
duplication.  Filter for `have … := by` with a multi-line body that does not mention the
lemma's name.

**Mover limitation to remember**: relocating a lemma upward requires checking the lemma's
OWN dependencies are still above it.  `move_lemma.py` does not check this — it broke
PresheafTateStructure exactly this way, caught by the module build.

### Misplaced-lemma sweep: FINAL YIELD — smaller than I projected

Filtered pass (`misplaced2.py`: `by` proof, >=4 lines, not already delegating) cut 89 raw
matches to **12 candidates / 141 lines**.  Adjudicating those 12 by hand:

* **2 REAL, fixed** (53 lines): WittF `bddAbove_gaussTermF_of_coords_shift` (three copies of
  one fact), Groebner `gaussNormRPS_ne_zero`.
* **1 REAL but circular**, queued: PresheafTateStructure — needs the shared step extracted
  above both, not a relocation.
* **The rest are FALSE POSITIVES**, and the failure mode is instructive:
  `productRestrictionSub_injective_of_flat_and_lifting` (Cor832:370) appeared to be inlined
  three times (26L + 14L + 4L).  It is not.  The conclusion matches
  (`Function.Injective (productRestrictionSub A C)`) but the proofs derive it from
  **different hypotheses** — the lemma needs flatness + Spa-lifting; SheafyPair proves it
  from `IsLimitSheaf`.  Independent proofs of one conclusion, not duplication.

**Lesson: conclusion-matching over-reports badly.**  A statement match is necessary but far
from sufficient — you must also check the lemma's HYPOTHESES are available at the use site.
That is not cheaply automatable, so this sweep is a ~2-fix tool, not the free win I
projected when I recommended running it first.  Import reachability *is* worth checking
mechanically (it correctly ruled TateAcyclicity's copy out of scope).

Corrected expectation: the 486 decompositions are the work; there is no shortcut around them.
