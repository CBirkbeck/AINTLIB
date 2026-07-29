# GOAL: clean up all of the adic code

User directive (2026-07-29): remove **all** maxHeartbeat options; `/decompose-proof` every
proof over 50 LOC; run the **full** `/cleanup` on **every** lemma. Full budget, no stopping.

## Measured scope (baseline)

    files                      376
    lines                  231,153
    declarations             7,926   <- each needs full /cleanup
    proof bodies > 50 LOC      383   across 124 files   <- CORRECTED, see below
    heartbeat raises           104   across 13 files

### MEASUREMENT BUG (found 2026-07-29) — the over-50 count was inflated by 103

My first script took the **first** `:=` at/after the declaration line as the signature/body
boundary. But signatures legitimately contain `:=`:

```lean
theorem tate_quotPresentation_canonicalMap
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;  -- <-- HERE
      CompleteSpace A]
```

That instance binder made a **19-line** body measure as **51**. Same for default arguments and
any `:= by` nested inside a binder type. Fix: track bracket depth over `( ) [ ] { } ⟨ ⟩` and
accept only a `:=` at depth 0 — `scratchpad/scope2.py`. Real count **383**, not 486; 103 of the
"over-50" proofs were never over 50. Corrected worst files:

    WedhornCechAcyclicity 40 · RobbaPresentation 17 · LaurentRefinementCore 13 ·
    Euclidean 12 · FiniteJetGraphKoszul 8 · TateAlgebra 8 · TateAlgebraTopology 8 · WittF 8

**Lesson for any future scan of Lean source: a declaration's signature can contain `:=`.**
Never split on the first one.

## Order of work, and why

**1. Heartbeats first.** Removing a raise either just works, or exposes a proof that is
genuinely slow — and slow proofs are exactly the ones needing decomposition. So this pass
generates the priority list for task 2 instead of duplicating it.

**2. Decompose the 383**, largest first, batched per file to amortise the ~40 min full-build
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
(corrected figures — see the measurement-bug note above)
WedhornCechAcyclicity 40 · RobbaPresentation 17 · LaurentRefinementCore 13 ·
Euclidean 12 · FiniteJetGraphKoszul 8 · TateAlgebra 8 · TateAlgebraTopology 8 · WittF 8

Largest single proofs: `isIntegral_of_forall_continuous_valuation_le_one` 405 ·
`exists_lift_norm_le_of_closed_range` 389 · `wedhorn_lemma_834_propA3_part1_gluing` 386 ·
`tateAlgebra_flat` 352 · `gluing_JetA` 279

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

Re-measured (corrected script): **383** bodies over 50 across 124 files (whole tree; the
FarguesFontaine set is a subset).  Worst: WedhornCechAcyclicity 40 · RobbaPresentation 17 ·
LaurentRefinementCore 13 · Euclidean 12.

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

## Task 2 — decomposition plan for `wedhorn_lemma_834_propA3_part1_gluing`
WedhornCechAcyclicity.lean:7666-8119 (454 lines).  Author's own numbered Steps:

| Step | lines | span | produces | note |
|---|---|---|---|---|
| 1-2 | 49 | 7736-7784 | `gVj` + compatibility | restricted family at each Vj |
| 3-4 | 8 | 7785-7792 | `yVj` | apply acyclic-gluing, then cast |
| **5** | **147** | 7793-7939 | `h_yV_compat` | **extract first** — compatibility of yV on V |
| 6-7 | 6 | 7940-7945 | `x` | apply V-gluing, cast to C.base |
| **8** | **174** | 7946-8119 | the goal | **extract second** — verify x|D = f D per D |

Steps 5 and 8 are 321 of the 454 lines.  Extract both and the residue is ~70 (still over 50,
so Steps 1-2 come out next).

**Apply the data-flow rule** (CLEANUP-LOG.md): Step 5 defines `h_yV_compat`, consumed by
Step 6; Step 8 is terminal.  So Step 5's lemma must RETURN the compatibility fact, and
Step 8's can take everything as hypotheses.  Do NOT lift a Step boundary without checking
what it defines for later Steps.

## Task 2 — the `invS` power-bounded family (2026-07-29): 8 duplications → 1 lemma

Started on the cheapest band (51-60 LOC) and the first target, `iteratedMinus_B_flat_of_canonical`
(RestrictionFlatness.lean:67), turned out to be the visible tip of a **whole-tree duplication**.

### What was actually there

The fact `invS D = D.coeRingHom (divByS 1 D.s)` (unit-cancellation: both are inverse to
`D.canonicalMap D.s`) plus its corollary "`invS D` is power-bounded when `1 ∈ D.T`" was written
out **8 separate times**:

| Site | form |
|---|---|
| `Example638.lean:1102` | the named general lemma `invS_eq_coeRingHom_divByS_one` (+13 users) |
| `TateAcyclicityFinalAssembly.lean:2487` | `..._of_one_mem_T_general` — **dead, 0 call sites** |
| `TateAcyclicityFinalAssembly.lean:2517` | `..._of_one_mem_T_minimal` — strictly weaker, 1 call site |
| `RestrictionFlatness.lean:133` | inline, 23 lines |
| `LaurentRefinementCore.lean:2962` | inline, 19 lines |
| `LaurentRefinementCore.lean:3280` | inline, 19 lines (byte-identical) |
| `LaurentRefinementCore.lean:3486` | inline, 19 lines (byte-identical) |
| `Wedhorn828.lean:3000` | inline, `coUnitDatum`-specialised |

Plus 8 more sites spelling the corollary as `rw [invS_eq_coeRingHom_divByS_one]` +
`exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T …` — 3-4 lines each.

### Why it happened (worth remembering)

Two independent causes, both invisible to a name-based duplicate scan:

1. **Wrong home.** `invS` lives in `PresheafIdentification.lean`; the boundedness engine
   (`CompletionLocalization.invS_isPowerBounded_of_one_mem_T`) lives in `CompletionLocalization.lean`
   — and **neither file imports the other**. So no single one of them could host a lemma about
   `IsPowerBounded (invS D)`. The general lemma ended up in `Example638.lean` (a file about one
   specific Wedhorn example) and the corollary in `TateAcyclicityFinalAssembly.lean` (the *last*
   file), i.e. as far downstream as possible from the 8 places that needed it.
2. **Typeclass anxiety.** The B-level (base = `presheafValue D₀`) has no
   `HasLocLiftPowerBounded` instance, so rather than weaken the hypotheses once, two more
   copies were made — `_general` and `_minimal` — differing only in typeclass set. `_minimal`
   strictly subsumes `_general` (`IsHuberRing extends IsTopologicalRing`), so `_general` was
   dead on arrival.

### The fix

`PresheafTateStructure.lean` is the **unique** file importing both `PresheafIdentification` and
`CompletionLocalization`, and all 9 duplicating sites reach it transitively (254 of 376 modules
depend on it). Both lemmas now live there, stated over a bare `[CommRing R] [TopologicalSpace R]
[IsTopologicalRing R]` — the weakest set, so they apply at the B-level too:

    invS_eq_coeRingHom_divByS_one      -- moved up from Example638
    isPowerBounded_invS_of_one_mem_T   -- new; replaces _general and _minimal

Removed: `_general` + `_minimal` (53 lines, one of them dead), 4 inline copies (80 lines),
8 `rw`+`exact` pairs collapsed to single term-mode calls. Net declaration count 7926 → 7925.

**Three over-50 proofs came under the bar as a side effect** — `iteratedMinus_B_flat_of_canonical`
(RestrictionFlatness), `laurentMinusBridge` and `laurentMinusBridge_restrictionMap`
(LaurentRefinementCore). Tree total **383 → 380**; LaurentRefinementCore 13 → 11.
`iteratedMinus_forwardHom_comp_backwardHom` (57) is untouched by this — a separate target.

### Method note

Grepping for the lemma *name* finds nothing when the copies are anonymous `have`s. What found
this was grepping for a **distinctive sub-expression of the statement** — `coeRingHom (divByS 1`
— which matches the inline copies and the named lemma alike. Do that for every helper extracted
from now on: search the tree for the statement's shape, not its name.

**And: a name collision on `lake build` is a dedup signal, not just an error.** The build failing
with "`invS_eq_coeRingHom_divByS_one` has already been declared" is what revealed copy #8.

## Task 2 — batch 2 (planned, ready to apply): the Keystone preamble

Scan: `scratchpad/repeated_haves.py` → **36 real groups, 910 duplicated lines** across the tree,
catalogued in `.mathlib-quality/goal/DEDUP-INLINE.md`. Batch 2 takes the top three groups, which
are one copy-pasted proof preamble (`hF_alg` / `hps` / `hA₀` / `hqt`, same `have` names,
consecutive lines) shared by `RelativePieceKeystone{,Gen,Open}` and WedhornCechAcyclicity.

**Home: `RelativePieceKeystone.lean`, after `algebraMap_s_mul_divByS` (line 47).** Verified: Gen,
Open and WCA all reach it. Its section vars are `[CommRing A] [TopologicalSpace A]
[IsTopologicalRing A] [PlusSubring A] [IsHuberRing A]` — deliberately **no `[IsTateRing A]`**,
which matters (see the `concretePair_A₀'` note below).

| group | copies | lines | new lemma |
|---|---|---|---|
| #2 + #5 | 6 + 3 | 90 | `canonicalMap_eq_canonicalMap_s_mul_coeRingHom_divByS` — `canonicalMap p = canonicalMap s * coe (p/s)`. **#5 (`hqt`) is the SAME identity one level up** (B-side, `p := D₀.canonicalMap q`), i.e. the same fact proved twice inside one proof. |
| #0 | 7 | 92 | `coeRingHom_divByS_mem_concretePair_A₀` — `p ∈ insert D.s D.T → coe (p/s) ∈ (presheafValue_concretePair D).A₀` |
| #17 | 4 | 21 | `hT_pb` companion: `T = {1}` ⟹ every `t ∈ T` power-bounded. Second half of the `hb` proofs already fixed in batch 1. |

Checked first, per the rule: **no existing named lemma** covers #2 or #17. For #0 there is
`presheafValue_concretePair_A₀` (PresheafTateStructure:887) but it carries `[IsTateRing A]`, which
Gen/Open do not have — so they each cloned it as **`concretePair_A₀'`, byte-identical in
`RelativePieceKeystoneGen.lean:42` and `RelativePieceKeystoneOpen.lean:157`**, docstring included
(the docstring itself says the `[IsTateRing A]` binder is "vestigial — the statement is `rfl`").
Both copies have exactly one user each: the `hA₀` block being collapsed. So state the new lemma
**without** `[IsTateRing A]`, proving the `A₀` rewrite by `show … from rfl`, and delete both twins.

Collapse shape (minimal blast radius): keep each `have hX : <same statement> :=` and replace only
its proof with `fun p hp => <new lemma> …`. 13L → 3L, 8L → 3L; the rest of every proof is untouched.

### Batch 2 RESULT — and the lesson that dedup ≠ the 50-LOC bar

Applied as planned. Net **−105 lines** (−138 duplication, +33 for the two new lemmas and their
docstrings). All three Keystone files and WCA build.

| what | before | after |
|---|---|---|
| `hA₀` (7 copies) | 13-14L each | 3L each |
| `hps` (7 copies) | 8L each | 3L each (one is 6L, see below) |
| `hqt` (3 copies) | 14L each | 4L each |
| `concretePair_A₀'` twins | 2 declarations | deleted (orphaned by the collapse) |
| `presheafValue_concretePair_A₀` | `[IsTateRing A]` | binder dropped (drop-test: body is `rfl`) |

**But the over-50 count did not move: 380 before, 380 after.** Every one of those blocks sits
inside a proof that is 100-250 lines long, so removing 10 lines from it changes nothing about
the bar. Batch 1 crossed three thresholds only by luck — the copies there happened to live in
51-56 line proofs.

**So the two objectives are separate.** Deduplication is worth doing on its own merits (single
source of truth, and it is most of what `/cleanup` means), but **it will not discharge task 2**.
To move the over-50 count I have to decompose the large proofs directly. Remaining dedup work
stays catalogued in `DEDUP-INLINE.md` and gets picked up per-file during task 3.

#### Two gotchas from batch 2

**1. Never key a bulk collapse on a `have`'s FIRST line.** My script matched
`have hps : ∀ p : A, D₀.canonicalMap p =` and replaced 7 blocks — but one of them
(`WedhornCechAcyclicity.lean:3027`) continues `D₀.canonicalMap DI.s * …`, not `D₀.s`. Different
statement, and the original proof had an extra `have hs : DI.s = D₀.s * 1 := rfl; rw [hs, mul_one]`
step to bridge it. Caught by auditing the second line of all 7 afterwards; recovered the original
from `git show HEAD:<path>`. **Match the whole statement, or verify every hit afterwards.**

**2. `Finset.insert` needs `[DecidableEq A]`.** The first draft of
`coeRingHom_divByS_mem_concretePair_A₀` took `p ∈ insert D.s D.T` and failed to synthesize
`Insert A (Finset A)` — the callers only have it because they run `classical`. Taking
`[DecidableEq A]` instead would risk a diamond (the caller's `Classical.decEq` instance vs the
one synthesised at the call, making the two `insert` terms non-syntactically-equal). Fixed by
stating the hypothesis as the disjunction `p = D.s ∨ p ∈ D.T` — which is what the proof's first
step (`Finset.mem_insert.mp`) produced anyway. **Prefer a disjunction to a `Finset.insert`
membership in a shared lemma's hypotheses.**

#### Assessed and deliberately skipped

Group #17 (`hT_pb`, 4 copies, 21L): each copy is `intro t ht; rw [Finset.mem_singleton.mp ht];
exact TopologicalRing.isPowerBounded_one` — 3 lines of clear tactic code. A shared lemma would
save 2 lines per site and add a declaration. Not worth it. (A `▸` one-liner would save the same
and is direction-fragile.) Recorded so it is not re-litigated.
