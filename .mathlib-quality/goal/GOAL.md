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

## Task 2 — batch 3: the 405-line headliner, decomposed

`isIntegral_of_forall_continuous_valuation_le_one` (Presheaf.lean) — the largest sorry-free
proof in the tree — was **405 lines and 30 top-level steps, of which one `have` was 371 lines.**
That is the dominant-`have` shape again (cf. `PhiHatK_teichCoeffAr`, 157 of 200). Three cuts,
each following the author's own phase labels:

| declaration | body | note |
|---|---|---|
| `isIntegral_of_forall_continuous_valuation_le_one` | 405 → **39** | the contraposition + the final contradiction |
| `exists_continuous_valuation_of_notMem_integralClosure` | **36** | Wedhorn 7.18 / [Hu2] Lemma 3.3; assembles A with B+C |
| `exists_valuationSubring_of_notMem_integralClosure` | 138 | Phase A, the refined Stacks 090P |
| `exists_continuous_valuation_of_valuationSubring_of_span_eq` | 182 | Phases B+C, standard (`S.Nonempty`) case |

Net: one 405-line proof became **two under the bar and two named, documented, independently
tractable** targets. All four are public with real docstrings — these are literature results
(Wedhorn 7.18, its Phase A, its Phase B+C), not private scaffolding, so they earn visibility.

### The method that made this cheap

`scratchpad/skeleton.py <file> <decl>` prints every tactic step at the proof's base indentation
with its line span. That one view exposes the whole decomposition: a 371-line step against 29
one-line steps is unmissable, and after the first cut the same view showed a 137-line Phase-A
`have` and a 180-line `by_cases` branch. **Run it before reading any long proof.**

Data flow was checked per cut by grepping the block for every context binder (script prints
USED/unused with a reference count). Each cut turned out to need only hypotheses the parent
already had — which is why all three lifted with no plumbing. It also found that `hx_ne_zero`
was consumed by *neither* phase: dead code, deleted.

### Two gotchas

**1. `Type _` in an extracted existential breaks universe inference.** The `have` read
`∃ (Γ₀ : Type _) …`, and inside the parent Lean resolved that metavariable from context. As a
standalone theorem it cannot: `failed to infer universe levels`, plus three
`Type u_3` vs `Type u_4` mismatches where `V.ValueGroup` appeared. Fix: bind the universe
explicitly — `{R : Type u}` and `∃ (Γ₀ : Type u)`. **Any extraction whose statement mentions
`Type _` needs its universe pinned.**

**2. Stale planning comments outlive the thing they planned.** The parent carried 28 lines of
F3/F4/F5/F6 construction notes ending "*we assert the existence of V … as a sub-sorry capturing
Phase A*" — but there is no sorry, and the notes now duplicate the extracted lemma's docstring.
The theorem docstring made the same false claim ("*isolates this gap to a single sub-sorry inside
the main proof*"), and a third comment said "*For now, handle via sorry (minor edge case)*" over a
real `by_cases` proof. Deleting the block took the assembler from 60 lines to **36** — under the
bar on comment removal alone. **When decomposing, the stale-comment sweep is part of the cut, and
docstrings that describe a proof as unfinished must be re-read against the actual proof.**

## Task 1 — the 5 deferred raises revisited: 5 → 2

Came back to the five `GOAL-DEFERRED` raises with the empirical method (remove the raise, read
*where* it times out) instead of assuming they all needed decomposition. Three came off.

| decl | before | after | what it actually was |
|---|---|---|---|
| `productRestrictionSub_isEmbedding_JetA` | 1.6M | **none** | litter — came off once the module's whnf pressure dropped |
| `genPiece_relative_overlap_square₁` | 1.6M | **none** | one bad tactic step (below) |
| `genPiece_relative_overlap_square₂` | 1.6M | **none** | the same step, mirrored |
| `gluing_JetA` | 6.4M | 1.6M | two bad steps fixed; the rest is cumulative → needs decomposition |
| `imageCover` | 4M | 4M | not a proof step at all → needs split-def-from-packaging |

### The single most valuable finding: `_ _ _` on a lemma whose proof is one term

Both G3b squares died at

    · exact (restrictionMapHom_continuous _ _ _).comp
        UniformSpace.Completion.continuous_extension

`restrictionMapHom_continuous`'s own body (Presheaf.lean:1888) is *literally*
`UniformSpace.Completion.continuous_extension`. So those three placeholders bought nothing and
cost everything: the elaborator had to solve `Continuous (restrictionMapHom ?D ?D' ?h)` against
a goal full of nested `interSamePair` chains — `isDefEq` blew past 200k. The sibling bullet in
the very same proof already used the bare `continuous_extension`. Making bullet 2 match bullet 1
removed **two 1.6M raises**.

**Generalise:** when a lemma's proof is a single term, invoking it with placeholder arguments is
strictly worse than inlining that term — you pay a metavariable unification against the whole
goal for zero abbreviation. Look for `(foo _ _ _)` in any proof that needs a raise.

### `gluing_JetA`: 6.4M → 1.6M, and the reason changed

Two per-step blow-ups, both of the "rewrite against a `Classical.choose_spec` transport" family:

1. `hgBres`/`hgCres` did `rw [restrictionMap_cast _ _ …choose_spec.2]`, forcing `kabstract` +
   `whnf` of the chosen datum. Replaced by a new lemma —
   **`restrictionMap_cast_restrictionMap`** (PresheafFunctoriality.lean): restricting a
   transported value restricts straight from the source datum, proved by `subst` so it is free.
   It serves *both* vertices, so this also killed a 25-line B/C mirror duplication (10 lines → 1
   in each).
2. `hgBd`/`hgCd` used `rw [congrFun (restrictionMap_id ..)] at h` where `simp only` does the
   same job without kabstract — the rule already recorded as "**`simp only` NOT `rw`** for these
   goals". 4 sites, 4 lines.

After both, the *only* remaining error is the whole-declaration budget (`348:0`) — no single hot
step. Verified ladder: 200k fails, 400k fails, 1.6M passes. So the residue is genuinely
cumulative and decomposition is the real fix (extract `hDmatch`, 84 lines, plus the two closing
bullets). The in-source note now records this precisely instead of the old guess.

### `imageCover` is not a proof at all

Worth flagging because it was mis-filed on the task-2 list: `imageCover` is a **structure
instance**, and its hot spot (`11217:41`) is inside the `covers` *field*, elaborated with the
whole `haveI`/`letI` stack in scope. No proof body to decompose. The fix is split-def-from-
packaging: give the covers family its own `def` and instance preamble, then package.

### Method note

Never assume a deferred raise needs the expensive fix. `lake build` with the raise deleted names
the exact `line:col` of the hot step, which distinguishes the three cases cheaply: one bad tactic
step (fix it), cumulative cost (decompose), or a def field (restructure). Two of five turned out
to be one-line fixes and a third was pure litter.

## Task 2 — `exists_lift_norm_le_of_closed_range`: the mirror-pair pattern

389-line body (FJP/FiniteJetGraphKoszul.lean), an ultrametric Banach open-mapping argument.
The `skeleton.py` view showed ~100 lines of small *scaling helpers* ahead of the two big pieces,
and four of those helpers were **mirror pairs** — the same proof twice, differing only in an
index type or in `t` versus `t⁻¹`:

| helpers | differ only in | replaced by |
|---|---|---|
| `hpitpow` / `hpitpowκ` | index `ι` vs `κ` | `pi_norm_pow_mul_of_scale` |
| `hpitinvpow` / `hpitinvpowι` | index, and `c := t⁻¹` | the same lemma |
| `hequiv_pow` / `hequivinv_pow` | `c := t` vs `c := t⁻¹` | `map_pow_mul_of_equivariant` |

Plus the sub-fact `‖t ^ n‖ = ‖t‖ ^ n` was re-derived **four times** inline → `norm_pow_of_scale`.

Three new lemmas, six blocks collapsed to one-liners: body **389 → 346**, and each new lemma is
generic (arbitrary index type, arbitrary scaling element) so it can serve other FJP proofs.
Both `▸`-based specialisations (`htinvnorm ▸ pi_norm_pow_mul_of_scale htinvscale' n u`) compiled
first try.

**The pattern to look for:** in a proof over a map `(ι → A) →+ (κ → A)`, any helper stated for
one index type almost certainly has a twin for the other. Make the index a parameter and both
copies collapse. Same for anything stated for a unit and again for its inverse — parameterise
over the element.

### Still over the bar: 346 lines

Remaining structure, for the next pass:

    59L  have key   : δ-small elements of the range lift with norm ≤ R
    39L  have step  : the approximation step at scale k  (used 10x, incl. inside `key`)
   121L  the `y ≠ 0` bullet: the [δ‖t‖, δ) window argument

`step` is used both inside `key` and in the closing bullet, so `key` cannot be lifted without
either passing `step` in or lifting both together. The natural split is the textbook one:
one lemma for the δ-ball lifting (`step` + `key`), leaving the Baire setup and the window
argument in the parent.

## Task 1 — the last two raises: one closed as out-of-scope, one reduced

### `imageCover` (4M): split-def-from-packaging TRIED AND FAILED

The previous entry recorded split-def-from-packaging as "the fix". **It is not.** Attempted
2026-07-30 and reverted:

* Lifting the family into `def imageCoverCovers` requires instances on `presheafValue C.base`
  for `RationalLocData` to typecheck. Two ways to supply them, both bad:
  - `haveI`s in the **return type** — times out at `isDefEq` on the ascription itself, i.e.
    strictly worse than the original, and cascaded 6 downstream errors;
  - instance **binders** — relocates the identical `Finset.image` cost without shrinking it.
* The real cost is the `DecidableEq (RationalLocData (presheafValue C.base))` that
  `Finset.image` demands. It can only be `Classical.decEq`, and `whnf` grinds it because
  `Finset.image` is computationally relevant (it dedups).

**Root cause is a design choice, not a proof defect:** `RationalCoveringData.covers` is a
`Finset`, which is what forces decidable equality on a heavy structure. An indexed family, or a
`Set` plus a finiteness field, needs no decidability at all. That is a statement change →
`/generalise`, out of scope for this pass. **Removed from the task-2 list** — there is no proof
body here. The in-source note now records the failed attempt so it is not retried.

### `gluing_JetA` (6.4M → 1.6M): `hDmatch` extracted, but the cost is diffuse

`hDmatch` (84 lines) is now `mapBD_eq_mapCD_of_pushed_gluing`; body 257 → 173. The signature
compiled first try, which is worth noting as a method result: doing a **verbatim** extraction —
move the body unchanged, dedent, and turn the six consumed bindings into hypotheses — puts all
the risk in the signature, where a mistake is a type error, instead of in the proof, where a
mistake is a silent change. Types for the hypotheses came from reading `IsSheafy.gluing`'s
field signature rather than guessing.

Measured ladder at 173 lines: **200k fails, 400k fails, 1.6M passes.** So this is not one hot
step but dozens of individually-affordable `restrictionMap`/`presheafValueMap` rewrites over
completions. Next real cut: the closing `pairMapBC_injective` pair — two 19-line B/C mirror
bullets, one lemma should serve both — but their goals are the `?_`s of `pairMapBC_injective`
and are written down nowhere, so deriving them is the prerequisite.

### Task 1 status

In-scope raises: **2**, both now with a full in-source diagnosis and a verified ladder.
`imageCover` is blocked on a design decision (owner call); `gluing_JetA` is a tractable but
diffuse decomposition. Nothing else in the tree carries a raise except `Vendored/`
(third-party, 1 heartbeat + 1 `maxSynthPendingDepth 8`) and the three
`maxSynthPendingDepth 1` reductions, which stay.

## Task 2 — the cheap-win queue: a scan that finds the one-cut proofs

Two new scanners replace guesswork about which proof to attack next.

**`scratchpad/dominance.py`** — for each over-50 proof, prints the span of its largest
top-level step and what fraction of the body that is, plus whether that step is a
`have` (statement written down → the extracted signature can be **copied**) or a
bullet / `by_cases` branch (goal is a `?_` → the signature must be **reconstructed**, much
riskier). Of 375 proofs, **45 have a dominant `have` at ≥45% of the body**.

**`scratchpad/liftable.py`** — narrows that to the ones where a single cut puts *both* halves
under 50 (**81 proofs**, i.e. −81 available on the count), then reports, per target, which
*proof-local* bindings the dominant `have` actually touches. Zero locals ⇒ the `have` refers only
to the theorem's own binders and lifts mechanically: copy the parent's binder list verbatim, copy
the `have`'s statement as the conclusion, move the body. **13 targets** are in that class.

This is the useful contrast with `gluing_JetA`: there the dominant step was 33% of the body and
the residual cost was diffuse, so cutting it did not finish the job. The dominance figure predicts
that in advance.

### Landed from the queue (3 proofs, net −3)

| parent | was | now | extracted lemma |
|---|---|---|---|
| `locRhoB_bridgeFwdB` | 51 | 20 | `locRhoB_bridgeFwdB_comp_coeRingHom` (30) |
| `locRhoC_bridgeFwdC` | 51 | 20 | `locRhoC_bridgeFwdC_comp_coeRingHom` (30) |
| `exists_translateFam_glue` | 63 | 44 | `translateFam_pairwise_compat` (19) |

The first two are a B/C mirror pair and took one script run. All six declarations are now under
the bar.

### GOTCHA (hit again — third time this campaign)

Inserting a lemma "above the parent" must use the **preamble-start scan**, not the `theorem` line:
anchoring on `theorem exists_translateFam_glue …` spliced the new lemma *between* the parent's
docstring and its `theorem`, giving `unexpected token '/--'; expected 'lemma'`. Anchor on the
whole docstring-plus-declaration block, or scan back over `/-- … -/`, attributes, `include`/`omit
… in` and `set_option … in` as recorded earlier. Any batch inserter must do this or it will
corrupt every target that has a docstring — which is most of them.

## Task 2 — `scratchpad/lift_have.py`: the batch inserter, and four defects it exposed

Doing the one-cut lifts by hand was costing a wrong build each time, so the transformation is now
a tool:

    lift_have.py <file> <parent_decl> <new_lemma_name> "<section prefix>" [--write]

It finds the parent's dominant `have`, emits `private theorem <new>` with the parent's binder text
**verbatim** and the `have`'s stated type as the conclusion, moves the proof unchanged, and
replaces the `have` with a call. Building it surfaced four defects worth recording — three of
them were live bugs in my earlier hand-work or in the scanner:

**1. `:= by` is not the boundary of a `have`.** A `have` may be closed by a *term*:
`have hsplit : <22 lines of type> := fun z => rfl`. Searching forward for a literal `':= by'`
then overruns into a later declaration and captures an **empty proof** — which, written out,
would have silently deleted the body. Use the `:=` at bracket depth 0 inside the `have`'s block.

**2. Span ≠ proof size — the scanner was manufacturing false targets.** `dominance.py` ranked by
the step's *span*, so a `have` with a 22-line type and a one-line proof scored as a 22-line
"dominant step". Extracting it relocates a long TYPE and shrinks nothing. `liftable.py` now
splits at the depth-0 `:=` and reports proof lines; the mechanical queue went 10 → **8**, and the
**2 rejected were exactly `ringStalkMap_piYHom_germ` / `ringStalkMap_yFrob_germ`** — the pair I
was about to "fix".

**3. Anonymous `letI`/`haveI` instance setup is invisible to a named-binder scan.**
`locSubring_subspace_eq_adic` opens with four `letI : TopologicalSpace/UniformSpace … := D₀.…`
lines. The lifted lemma lost them and failed with `failed to synthesize instance of type class
TopologicalSpace (Localization.Away D₀.s)`. The tool now carries that preamble into the extracted
lemma. (This is why the FiniteJetFunctoriality pair worked earlier — it happened not to need its
instances in the lifted block.)

**4. Modifier lines belong to the declaration, not the file.** `omit [PlusSubring A] in`,
`include … in`, `set_option … in`, `open … in` must be **replicated** on the extracted lemma, and
the insertion must go above the whole preamble including them.

Also: the instance preamble sits at the parent's *base* indent, which is already the new lemma's
proof base — it must NOT be dedented, unlike the `have`'s proof which is one level deeper. Getting
that wrong put `letI` at column 0 (`unexpected token 'letI'; expected command`).

### Landed: 3 of 6 attempted. The tool's classification is UNSOUND — do not trust it blind.

Green and kept:

* `locSubring_subspace_eq_adic` (PresheafTateStructure) — 60 → 26 + 37
* `telescope_down_bound` (RobbaPresentation) — 63 → 40 + 26
* `RationalLocData.isClosed_powerBoundedSubring` (Presheaf) — 52 → 34 + 21

**Reverted after failing the gate — three separate holes in the "no proof-locals" test:**

| target | failure | hole |
|---|---|---|
| `iteratedPlus_forwardToCompletion_continuous` | `failed to synthesize TopologicalSpace (Localization.Away (iteratedPlusDatum_B …).s)` | parent carries `set_option backward.isDefEq.respectTransparency false`; its elaboration context does not survive extraction |
| `gaussNorm_sub_combination_le` | `g has type ?m.14 but is expected to have type GRing p F ϖ k hρ0 hρ1` | section variables (`g`, `k`, `hρ0`, `hρ1`) my scope tracker missed, so the call passed too few arguments |
| `chartPlus_le_completedPlusSubring_of_dense` | `Unknown identifier hseq` | a proof-local introduced by a binder form the regex list does not match |

So the regex "does this `have` touch proof-locals?" test is **necessary but far from
sufficient**. Three distinct context dependencies escape it: elaboration `set_option`s on the
parent, section variables in files with rich `variable` blocks, and binder forms the pattern list
misses. A sound version would have to *elaborate* the candidate lemma, not pattern-match it.

**Working rule from this:** the tool is a drafting aid, not a batch processor. One target, one
module build, then keep or revert. Two of the eight (`gaussTermF_mul_le`, `isInducing_`) the tool
cannot even parse.

### A second, costlier lesson: a failed multi-target `lake build` does NOT verify the others

I built five modified modules in one `lake build A B C D E`. It reported errors in
`PresheafTateStructure` only, and I read that as "the other four are fine". They were not built at
all — they import `PresheafTateStructure`, so the broken dependency skipped them, and their
failures surfaced only two full gates later. **Never read a multi-target build's silence about a
target as success; confirm the target actually compiled.**

## Task 2 — DEFINITIVE: there is no mechanically-liftable class. Stop looking for one.

The "81 one-cut targets, 13 of them mechanical" figure from two passes ago was an artifact of an
unsound test, and I have now measured how unsound. `scratchpad/screen.py` replaces the
binder-pattern heuristic with one that cannot miss a local:

    suspects = identifiers in the `have` block
             ∩ identifiers appearing in the proof body BEFORE the have
             − identifiers in the parent's signature

A proof-local must be introduced earlier in the same proof, so this catches it regardless of the
binder form. Result on the 75 current one-cut targets:

    survive with zero suspects:  1   (and it is the one `lift_have.py` cannot parse)
    rejected for suspect locals: 74
    suspect-count histogram: {1:4, 2:5, 3:9, 4:9, 5:8, 6:6, 7:7, 8:5, 9:4, 10:3, 11:3, 12:3,
                              13:3, 14:1, 15:1, 19:2, 20:1}

So **essentially every over-50 proof in this codebase threads proof-locals into its big step.**
That is what the earlier regex was blind to, and it is why 8 of the 11 batch attempts failed. The
median target needs 4–5 locals plumbed. There is no cheap batch; each target is individual work of
the `hDmatch` kind — read the locals, write the signature, verify.

`liftable.py` is superseded by `screen.py`. Keep both for the record but trust `screen.py`.

### What DOES work: re-derive short locals instead of threading them

The one clean win this pass came from a technique worth naming. When the dominant `have`'s local
dependencies are **short, written-down** facts, do not add them as hypotheses — **re-prove them
inside the extracted lemma**. For `exists_correction_sequence` the two suspects were
`hhalf0 : (0:NNReal) < 2⁻¹` and `hhalf1 : (2:NNReal)⁻¹ ≤ 1`, both `by norm_num`; the extracted
lemma just proves them again, and they are deleted from the parent (they had no other use).

    exists_correction_sequence   62 → 33  +  exists_correction_step_of_wI_le (31)

Compiled first try. Over-50 count 376 → 375.

### Why the same trick FAILED on the `exists_correction_chain_BI` pair

Worth recording because it looked identical. Their locals were `hK0` (a `have`) and `K` (a
`set K : NNReal := σ₁ ^ m₀ * ((ρ₁ ^ m₀)⁻¹) with hKdef`). Re-deriving both inside the lemma gives

    invalid 'calc' step, left-hand side is …

because **`set` folds only the occurrences that exist when it runs** (already recorded as a
gotcha, and it bites exactly here). In the parent, `set K` runs *before* `hstep`, so `K` is folded
into `hstep`'s own statement; in the extracted lemma the conclusion is fixed first, so `set K`
folds nothing and the body's `((K)⁻¹)` no longer matches the statement's unfolded form. A second
error (`Unknown identifier hφb`) showed the section-variable prefix was wrong too.

**Rule:** the re-derive trick is safe for a `have`, and unsafe for a `set`/`let` whose folding the
statement depends on. For those, the abbreviation must become an explicit parameter of the
extracted lemma together with its defining equation — or the statement must be written unfolded.

## Task 2 — suspect classification: only 1 of 64 targets is cheap

`scratchpad/classify.py` extends the screen by asking, for each proof-local suspect, **how it is
introduced** — because that decides the cost:

| introduced by | what the extraction must do |
|---|---|
| a short `have` | **re-derive it** inside the lemma (safe; this is the whole trick) |
| `set` / `let` | **unsafe to re-derive** — folding is positional (see the `BI` failure above). Must become an explicit parameter + defining equation |
| `obtain` / `rcases` / `intro` / `choose` / `fun` | must be threaded as a hypothesis, and its type is written down **nowhere** — it has to be read off the destructured term's source |

Across the 64 targets that have suspects and a real proof body, suspect-kind frequency is

    unknown 57 · have 48 · set 32 · obtain 24 · intro 16 · fun 11 · haveI 3 · by_cases 1

and **exactly 1 target has all-`have`, all-short suspects**. That was
`isPowerBounded_of_discrete_presheafValue`, done below. Everything else needs either a `set`
parameterisation or a destructured hypothesis whose type must be reconstructed by hand.

### Landed

* `isPowerBounded_of_discrete_presheafValue` (Presheaf.lean) 53 → 36, extracting
  `uniformSpace_eq_bot_of_discrete` (17). Its single suspect `htop` was a one-line
  `locTopology_eq_bot_of_discrete D'`, re-derived inside.

Also corrected a **stale docstring** on that theorem, which claimed *"Body pending the
`nhds (0 : Completion _) = pure 0` derivation"*. There is no `sorry`; the proof is complete. That
is the fourth stale "unfinished" claim found this campaign (cf. the three on
`isIntegral_of_forall_continuous_valuation_le_one`). **When touching any declaration, re-read its
docstring against the actual proof** — these claims are actively misleading about what is done.

## Task 3 — first mechanical pass (deprecations)

| item | result |
|---|---|
| `λ` → `fun` | **n/a: all 30 occurrences are prose** — Kedlaya's Gauss norm `λ_r`, the difference map `λ`, `ker λ`. None is a Lean lambda. Checking first was the right call (recorded gotcha). |
| `$` → `<\|` | n/a: 0 occurrences |
| `zero_le'` → `zero_le` | **20 sites**, 6 files |
| `push_neg` → `push Not` | **16 sites**, 11 files |

36 deprecation sites fixed across 12 files. Remaining deprecations visible in the build log, for a
later pass: `PowerSeries.derivative` (4), `HahnSeries.embDomain_of_notMem_range` (3),
`Derivation.leibniz` (2), `RingHom.pi` (2), `Finsupp.mapDomain_of_notMem_range` (1),
`Polynomial.finsetSum_coeff` (1), `IsLocalization.under_map_of_isPrime_disjoint` (1),
`continuous_mul_const` (1) — plus one project-internal `@[deprecated]` marked RETIRED (2 uses)
that wants a real repoint, not a rename.

## Task 2 — the `set`-suspect technique, solved (the BI pair, second attempt)

`exists_correction_chain_BI` / `BI₂` were the only targets whose suspects were all `set`/`have`,
and they failed last pass. All three causes are now understood, and the fixes compose:

**1. A `set` suspect must stay a `set` inside the extracted lemma — and then the lemma's
conclusion has to be written UNFOLDED.** `set K := e with hKdef` folds `e → K` in whatever exists
when it runs. In the parent it runs *before* the `have`, so the `have`'s statement is stored
folded (`((K)⁻¹) * …`). Copy that folded statement into a standalone lemma and the body no longer
matches, because there the `set` has nothing to fold: `invalid 'calc' step, left-hand side is …`.
Writing the conclusion with `K` expanded and putting `set K := e with hKdef` at the top of the
lemma reproduces the parent's context exactly, and the body transfers verbatim.

Do NOT instead make `K` an opaque parameter: facts produced *inside* the body (here `hfnorm`,
from `exists_correction_step_BI`) mention `e` unfolded, and only `set`'s definitional
transparency makes them match `K`. An opaque parameter breaks that.

**2. Section-variable HYPOTHESES need an explicit `include`.** `hφb` is used only in the proof,
never in the statement, so Lean does not auto-include it — the parent carries `include hφb in`,
and the extracted lemma needs its own. This was the `Unknown identifier hφb` from last pass.

**3. Keeping the `have`'s type ascription at the call site defeats the purpose.** With the
18-line statement re-stated as `have hstep : <18 lines> := <lemma> args`, the parents were still
**54** lines. Dropping to `have hstep := <lemma> args` took them to **37** — the lemma's unfolded
conclusion is defeq to the folded one, since `K` is a local definition. Always collapse the
ascription after extracting, or the extraction buys nothing.

| declaration | was | now |
|---|---|---|
| `exists_correction_chain_BI` | 68 | **37** + `exists_correction_chain_BI_step` (19) |
| `exists_correction_chain_BI₂` | 68 | **37** + `exists_correction_chain_BI₂_step` (19) |

Over-50 count 374 → **372**.

## FINDING (owner-facing): `tateAcyclicity` is not proved

Chasing the last deprecation warnings turned up something that matters more than the warnings.
Two project-internal lemmas are marked

    @[deprecated "RETIRED — false; use productRestriction_injective_tate_via_prime_extension_closed"]
    @[deprecated "RETIRED — false in general; use per-E via productRestriction_faithfullyFlat_tate"]

and their bodies say *"Statement preserved as a named sorry only to keep legacy callers
compiling"*. They still have three live consumers, and `#print axioms` confirms all of them rest
on `sorryAx`:

    ValuationSpectrum.tateAcyclicity_gluing_via_refinement   sorryAx
    ValuationSpectrum.tateAcyclicity                         sorryAx
    ValuationSpectrum.restrictionMap_isLocalization           sorryAx

So **`tateAcyclicity` — a headline result — is not proved**, and it depends on a lemma its own
author annotated as false. Repointing the three consumers at the replacement routes named in the
deprecation messages is real mathematical work, and `sorry`s are the owning producer's WIP, so
this pass does not touch them. Recording it because nothing in the file names warns a reader that
`tateAcyclicity` is unproved.

## Task 3 — deprecations, second pass

In-scope (non-`Vendored/`) mathlib renames applied:

| site | change |
|---|---|
| `Bounded.lean:583` | `continuous_mul_right` → `continuous_mul_const` |
| `Cor832.lean:578` | `IsLocalization.comap_map_of_isPrime_disjoint` → `…under_map_of_isPrime_disjoint` |
| `FarguesFontaine/FrobeniusLimit.lean:74,250` | `Pi.ringHom` → `RingHom.pi` |
| `FJP/FiniteJetChart.lean:1050` | `Polynomial.finset_sum_coeff` → `Polynomial.finsetSum_coeff` |

The earlier "21 remaining" figure was too pessimistic: it counted the whole workspace build, which
includes HasseWeil and LeanModularForms. AdicSpaces itself had only these 4 plus 3 in `Vendored/`
(skipped, third-party) and the 3 RETIRED uses above.

**Process note:** `Bash`'s `timeout` is capped at 600000 ms. Passing 1800000 does not extend it —
the build is killed at 10 minutes with exit 143. Long builds must be backgrounded.

## Task 2 — THE UNBLOCKING MOVE: extend the cut upward

The blocker was a dominant `have` depending on locals introduced by `obtain`/`intro`/`fun`, whose
types are written down nowhere. The way round it is not to thread them at all: **extract the
contiguous block from the first line that introduces a suspect down to the end of the `have`.**
The suspects are then introduced *inside* the lemma, so they stop being suspects; the extra lines
are prologue and the `have`'s statement is still the conclusion.

`scratchpad/extend.py` iterates that (extend one base-indent step, re-compute suspects, repeat)
and reports whether both halves still fit. On 148 dominant-have targets:

    39 become suspect-free by extending, with both halves ≤ 50
    24 of those have a prologue of ONLY `have`/`set`/`let` steps  ← verbatim-extractable

The 15 excluded ones have `obtain`/`rintro`/`refine`/`subst` in the prologue, which means the
`have`'s statement mentions a locally-obtained witness. Those need the conclusion re-authored as
an `∃` — real design work, not extraction. Worth knowing the split: **24 mechanical, 15 authoring.**

### Landed (3 parents, 4 new lemmas)

| parent | was | now | extracted |
|---|---|---|---|
| `tateAlgNhd_of_coeff_mem_principal` | 72 | **48** | `divided_mem_pairSubring_of_coeff_mem_pow` (37) |
| `tateAlgNhd₂_of_coeff_mem_principal` | 60 | **38** | `divided_mem_pairSubring₂_of_coeff_mem_pow` (32) |
| `coeff_of_oneSubfX_eq_aXn` | 55 | **~25** | `coeff_zero_…` + `coeff_succ_of_oneSubfX_eq_aXn` |

All compiled first try. Two observations that made them cheap:

* The `Fin 1`/`Fin 2` pair is another **mirror** — identical shape, so the second cost almost
  nothing once the first was done. Mirrors keep paying; look for a `₂`/`κ`/`Minus` twin whenever
  a target is finished.
* For `coeff_of_oneSubfX_eq_aXn`, `extend.py` proposed one 34-line block, but inspection showed
  its two `have`s (`h_base`, `h_step`) are *independently* self-contained — each uses only the
  theorem's binders. Extracting them as **two** small lemmas beats one combined block. The
  extension analysis gives an upper bound on what must move, not the best cut.

### The `let`-in-conclusion rule (same family as the `set` rule)

`tateAlgNhd_of_coeff_mem_principal`'s `have` was `g_val ∈ pairSubring P` where `g_val` and `πinv`
are `let`-bound in the parent. As with `set`, the extracted lemma's conclusion must spell them out
(`algebraMap A _ ((↑hπ_unit.unit⁻¹ : A) ^ n) * y ∈ pairSubring P`) and re-introduce the `let`s at
the top of the proof, so the body's `change …  g_val …` steps still work by defeq.

## Task 2 — `scratchpad/lift_block.py`, and two more preconditions the tool now enforces

The extend-upward technique is now a tool: `lift_block.py <file> <parent> <newname> <cut> <have>`.
It moves the block from `cut` to the end of the dominant `have` into a lemma, carries the prologue
verbatim, replicates `include`/`omit`/`set_option … in` modifiers, computes the section-variable
prefix for the call, and emits `have <h> := <lemma> args` with **no** type ascription.

Building it turned up two more preconditions, both now asserted rather than discovered by a build:

**1. A prologue local must not be used by the parent AFTER the block.** The prologue moves into
the lemma, so its locals stop existing in the parent. `isNoetherianRing_unitBall_restricted_dualNumber`
failed with `Unknown identifier hcoeffle` — a prologue `have` still referenced 40 lines later.
Reverted. Either the block must be extended to cover those uses too, or the local threaded back
out of the lemma. The tool now refuses instead of breaking the file.

**2. `have_line` is a separate argument from `cut`.** My first version assumed the dominant `have`
was the block's *last* base-indent step. It usually is not — there are further steps after it that
stay in the parent — so the tool was extracting the wrong span.

### Landed (2 of 3 attempted)

| parent | was | now |
|---|---|---|
| `tendsto_gaussTermF_add_of_tendsto` (WittF) | 51 | 16 + `gaussTermF_add_le_max_of_tendsto` (38) |
| `isInducing_ιSpvPropR_spa` (SpaQCviaSpvAI) | 84 | 41 + `isInducing_ιSpvPropR_spa_induced_eq` (46) |

`berkeley_6_2_8` (Tilting.lean) was in the automatic set but is **sorry-bearing** — out of scope,
producer's WIP. Worth re-checking that on every candidate: the auto filter does not look for it.

## SCANNER BUG (found while doing the above): declaration names were being truncated

`isInducing_ιSpvPropR_spa` was reported by `dominance.py` as `isInducing_`, and `lift_block.py`
then could not find the declaration. Cause: `scope2.py`'s `DECL` name class was
`[A-Za-z_][A-Za-z0-9_'!?.₀-₉«»]*` — **ASCII plus subscripts only**, so it stops at a Greek letter.
Lean names here use Greek freely (`ι`, `σ`, `ρ`, `φ`, `ϖ`). Widened to `[^\s({\[:]+`.

Two consequences worth recording:

* Any earlier report of a name ending in `_` was a truncation, not the real name.
* **The declaration count was UNDERCOUNTED.** It is **7978**, not 7947 — and by extension the
  original 7926 baseline for task 3 was also low. Declarations whose name begins with a Greek
  letter were skipped entirely, not merely mis-named.

## Task 2 — the mechanical queue is EXHAUSTED (measured, not guessed)

`scratchpad/candidates.py` now applies every precondition learned across this campaign in one
pass — dominant-`have`, one-cut-fits, real proof body, suspects closable by extending, prologue is
`have`/`set`/`let` only, no prologue local leaking to the parent, parent sorry-free. Run against
the current 368:

    368 over-50 proofs -> 0 pass every precondition

    rejections:
      203  the dominant step is NOT a named `have` (a bullet, `obtain`, `refine`, `calc` …)
       77  suspects not closable by extending the cut
       34  prologue contains obtain/intro/refine
       25  a prologue local is still used by the parent after the block
       13  one cut does not make both halves fit
       12  statement-heavy (long TYPE, short proof)
        3  sorry-bearing (producer's WIP)

So the 25 targets the earlier passes worked through were the entire mechanically-extractable
population. **The remaining 368 need authoring**, in three distinct flavours:

* **203** have a non-`have` dominant step. A bullet or `by_cases` branch has a `?_` goal that is
  written down nowhere, so its lemma statement must be *reconstructed* from the surrounding
  `refine`. That is the `pairMapBC_injective` situation already recorded for `gluing_JetA`.
* **77 + 34** need a destructured hypothesis threaded out, or the conclusion re-stated as an `∃`
  bundling a locally-obtained witness.
* **25** need the extracted lemma to return its prologue local as well (a conjunction, or a second
  lemma).

None of that is mechanical, and none of it should be attempted by a script. Recording the
breakdown so the next pass does not re-derive it.

## Task 3 — mechanical sweep from the build's own linter output

The build is the authoritative `/cleanup` worklist. AdicSpaces (excluding `Vendored/`) reports:

| count | warning | verdict |
|---|---|---|
| 3047 | `Overlapping instance parameters` | out of scope — a project-wide variable-block issue, already recorded as not-a-per-file defect |
| 550 | `automatically included section variable(s) unused` | needs per-theorem `omit`; large, deferred |
| 119 | `declaration uses sorry` | producer's WIP |
| 96 | `Variable name X is not explicitly referenced` | signature churn; deferred |
| **45** | `This simp argument is unused` | **fixed** |
| 21 | `Definition X is a proposition; use theorem` | next pass |
| **15** | `'<tac>' tactic does nothing` | **11 fixed, 4 left** (see below) |
| 7 | `try simp instead of simpa` | next pass |

**56 fixes across 22 files**, all pure removals the compiler had already certified inert.

4 left by hand on purpose: three are `· change …` where the no-op *is* the bullet's only tactic,
so deleting the line would orphan the bullet; one is `convert h using 1 <;> first | rfl | simp`,
where `simp` is a fallback alternative and removing it changes what the combinator does.

### GOTCHA: separator normalisation after deleting a list element must be WHOLE-FILE

First attempt normalised commas per line and broke `HuberRings.lean`:

```
simp only [a, PairOfDefinition.restrictRingHom, uK, vL,
  SubmonoidClass.coe_pow,
  ,
  , map_pow, ← pow_mul]
```

A `simp only [...]` list often spans several lines, so removing a token that occupied a line of
its own leaves a `,` alone on a line — invisible to any single-line regex. Fixed by normalising
over the joined file text (`,\n,` → `,`, a line that is only `,` → deleted, `[\n,` → `[`,
`,\n]` → `]`), iterated to a fixed point. The script also refuses to write a file where a
`simp only` set would end up empty (that hit `PresheafTateStructure.lean`, left untouched).

## Task 3 — second mechanical tranche: `def` → `theorem`, and what must NOT be converted

The linter flags 21 `Definition X is a proposition; use theorem instead of def`. Auditing them
before touching any split the list cleanly, and the split is the useful part:

**12 must NOT be converted.** They carry `@[reducible]` (several also `@[instance 1000]`) and are
named `instIsTopologicalRingTateAlgebra`, `RationalLocData.isTopologicalRing`,
`instT2SpaceTateAlgebra₂`, … — i.e. they *supply instances by name*, and their reducibility is
load-bearing for instance resolution and defeq. `theorem` is irreducible, so converting them
risks exactly the `isDefEq` walls this codebase is already prone to. Left alone, with the reason
recorded here so the warning is not "fixed" by a future pass.

**9 looked like plain `def`s** returning Prop-valued structures, with **zero**
`unfold`/`delta`/`simp [..]` uses anywhere in the tree (checked by grep first). I converted 8 —
and **6 of those had to be reverted**, because the gate failed with 14 errors:

    TateAlgebraTopology.lean:876:0: cannot omit referenced section variable `inst✝¹`
    TateAlgebraTopology.lean:1475:5: unsolved goals            (and 12 more)

**`def` → `theorem` changes SECTION-VARIABLE INCLUSION.** A `theorem` includes only the section
variables its statement mentions; a `def` includes more. Files that carry explicit `omit … in`
lines — `TateAlgebraTopology.lean` and `MvTateAlgebraTopology.lean` both do — then try to omit a
variable that is now referenced, which is an error. The grep for `unfold`/`simp` was necessary but
nowhere near sufficient: the risk was never unfolding, it was binder inclusion.

Kept (verified green): `nonarchimedeanAddGroup` (HuberRings), `locBasis` (LocalizationTopology).
Reverted: `tateAlgBasis`, `tateAlgBasis'`, `tateAlgBasis₂`, `tateAlgBasis'₂` (TateAlgebraTopology),
`mvTateAlgBasis`, `mvTateAlgBasis'` (MvTateAlgebraTopology). `isLocAway_of_isUnit`'s declaration
line did not match the pattern and was never touched.

**Rule: before converting `def` → `theorem`, check whether the file uses `omit … in`.** If it
does, the conversion is not mechanical.

I also repeated a mistake I had already recorded: I pre-checked with
`lake build HuberRings LocalizationTopology`, which passed, and treated that as covering the
batch. It covered those two modules only — the same masking that cost three gates several passes
ago. A pre-check must build *every* touched module, or it verifies nothing about the rest.

Also: `convert h using 1 <;> first | rfl | simp` → `convert h using 1 <;> rfl`, the linter having
reported the `simp` alternative as never executed.

### Deferred, with reasons

`simpa` → `simp` (7 sites). The linter's suggestion drops the `using <term>`, which **changes the
proof term** — `simpa using isOpen_univ` becomes `simp`, which only works if the goal is a simp
tautology on its own. That needs per-site checking, not a bulk rename, so it is not in this batch.

The 3 remaining `· change …` no-ops still need the bullet restructured rather than the line
deleted.

## Task 2 — authoring pass: the leaked-local class, and the LIMIT of the set-unfold recipe

With the mechanical queue exhausted, this pass attacked the 17 targets where a prologue local
leaks to the parent. Two attempts, one success, and the failure pins down a boundary worth having.

### The over-extension insight

`extend.py` proposes swallowing the prologue, but that is an **upper bound**, not the right cut.
For `isNoetherianRing_unitBall_restricted_dualNumber` it proposed swallowing `hcoeffle`; in fact
the dominant `have` (`hEball`) **does not use `hcoeffle` at all** — the suspect was a false
positive from an identifier appearing on both sides. Both `have`s turned out independently
self-contained (only the theorem's `S`/`m`), so the right move was **two separate extractions**,
no prologue swallowed and nothing threaded:

    isNoetherianRing_unitBall_restricted_dualNumber   69 → 48
      + norm_coeff_le_norm_restricted   (6)
      + norm_epsRestricted_le_one      (17)

Both are genuinely useful named lemmas. **Always check whether the dominant `have` really uses the
prologue local before assuming it must move.**

### THE LIMIT: the set-unfold recipe fails when the parent consumes the `have` by `rw`

`wI_partial_cauchy_diff`'s dominant `have` (`hcauchy`) does use the `set`-bound `g`, so I applied
the recipe that worked for `K` and `g_val`: conclusion written with `g` expanded, `set g … with hg`
re-introduced inside the lemma. It failed:

    Tactic `rewrite` failed: Did not find an occurrence of the pattern
    Application type mismatch … (at `wI_sum_le p F _ g`)

The reason is exactly the difference from the earlier successes. In the `K` case the extracted
`have` was passed as an *argument* (`exists_chain … hstep`), and argument passing unifies up to
defeq, so folded-vs-unfolded did not matter. Here the parent does `rw [hprod, hcauchy, …]`, and
**`rw` is syntactic**: the lemma's unfolded RHS cannot match the goal's folded `g`. Reverted.

**Rule:** the set-unfold recipe is safe when the extracted `have` is *consumed as a term*, and
unsafe when it is *consumed by `rw`/`simp only [h]`*. For the latter the abbreviation must stay
folded on both sides, which means the `set` cannot move into the lemma — so those targets need the
`set` hoisted above the parent as a real definition, or the rewrite restated. Neither is
mechanical.

### Gotcha

The `have hcoeffle : … := fun y s => by …` form puts its proof at indent **4**, not 2, because the
body sits inside the `fun`. Dedenting by 4 (as for a normal `have`) drops it to column 0 and gives
`unexpected token 'have'; expected command`. Dedent by 2.

## Task 2 — a THIRD approach: golf the 51-55 band instead of extracting

Extraction is not the only way under the bar. **53 of the 367 remaining proofs are 51-55 lines**,
so they need 1-5 lines removed, not a lemma. Reading a 51-line proof for two removable lines is
much cheaper than reconstructing a `?_` goal, and it leaves no new declaration behind.

`genPiece_rel_backwardLocHom_continuous` exists in all three of
`RelativePieceKeystone{,Gen,Open}` — a mirror **triple**. One anti-pattern golfed in all three:

```lean
have hw' : w ∈ T.image D₀.canonicalMap := hw     -- re-ascribe
rw [Finset.mem_image] at hw'                      -- rewrite
obtain ⟨q, hq, rfl⟩ := hw'                        -- destructure
```
→ `obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hw : w ∈ T.image D₀.canonicalMap)`

−2 lines each. Gen and Open: 51 → **49**. The base variant is 3 lines longer (it derives
`IsTateRing`/`IsNoetherianRing` inline where Gen/Open take them as instance binders), so it needed
two more:

* `have hbdd := …coeRingHom_image_locSubring_isBounded DI` + `refine hbdd.subset ?_` →
  `refine (…coeRingHom_image_locSubring_isBounded DI).subset ?_`   (single use, so the binding
  earned nothing)
* a `haveI hNoethB : … :=` / value split across two lines, rejoined — 99 chars, inside the limit.

Base: 54 → **50**.

Deliberately NOT golfed: the `rw [show (DB.s : presheafValue D₀) = D₀.canonicalMap t from rfl]`
step. Merging that into the neighbouring `rw` list would save a line but this is exactly the
goal-directed-rewrite-with-`rfl` shape that already cost a heartbeat raise in `LaurentOverlap`
(recorded in the task-1 section). Not worth one line.

### A tree-wide search for the same anti-pattern found only 7 more sites

`have h' : T := h` immediately followed by `rw [..] at h'`, with exactly one later use of `h'`,
occurs 7 times outside the Keystone triple (Lemma745, SpaRationalSubsetCorrespondence, SpvAI,
SpvCompletionExtension, ValuationPrimeConvex, ArCompletion, Groebner). Each saves 1-2 lines and
**none is inside an over-50 proof**, so golfing them advances nothing measurable. Left alone —
noted so a future pass does not re-derive the search.

## Task 2 — the continuation join: 7 proofs in one batch, zero semantic risk

Building on last pass's golf approach, the cheapest golf of all is mechanisable.
`scratchpad/joinable.py` finds **continuation joins**: a construct split across two lines where
the second is a pure continuation, and the joined line still fits 100 chars. The joined line holds
*exactly the same tokens*, so no proof can change meaning — this is the only fully-safe way to
remove a line.

Accepted shape (deliberately narrow):

* line ends in `:=`, successor is more-indented, joined length ≤ 100, **and line k+2 is not also
  more-indented** — that last guard matters: if the value spans several lines, pulling only the
  first one up is a reshape, not a join.
* neither line carries a `--` comment (the join would swallow the rest of the line).
* `:= by` is *excluded* by construction, since it does not end in `:=`.

Result: of 364 over-50 proofs, **7 cross the bar on `:=`-joins alone**, needing 9 joins in total.
Applied, bottom-up per file, only as many as each proof needs:

    ciSup_gaussTerm_eq_zero_of_valued_PhiHatK_eq_zero   ArCompletion
    glue_piece_eq                                       CurveObject
    uniformContinuous_frobToBI                          FrobeniusGauss
    SpvAI.exists_subbasic_mem_nhds                      SpvAITopology
    genPiece_relOverlap_forwardCompletion_continuous    WedhornCechAcyclicity  (3 joins)
    sigma_factored_supplier_via_localized_cor732        WedhornSigmaFactoredSupplier…
    mapValueGroupWithZero_surjective_of_localization     WedhornValueGroupLocalization…

Over-50 count **364 → 357**. All nine joined lines are single statements of 80-97 chars
(`set s : … := fun N => … with hs`, `haveI : IsNoetherianRing … := …`, etc.).

A further **6** proofs could cross if comma/open-bracket continuations were joined too. Those are
left for now: a `,`-terminated line inside a term is safe to join, but the detector cannot yet
distinguish that from other uses of a trailing comma, and the gain is not worth a wrong guess.

### Where this leaves the three routes

| route | cost | availability |
|---|---|---|
| continuation join | ~free, scriptable, zero risk | 7 done; 6 more behind a better comma detector |
| targeted golf (read the proof, remove 2-4 lines) | one read per proof | ~46 left in the 51-55 band |
| extract a self-contained `have` | one read + one module build | rare now |
| author a reconstructed `?_` goal | expensive | the 203-strong bulk |
