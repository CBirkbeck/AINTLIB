# /develop improvements tracker — what we need to teach future workers

**Purpose**: Each defect found in the v3-v7 adversarial passes maps to a step or check
that `/develop` should have caught at planning time. Once we're confident the
project is ready to work in, this list becomes a `/teach` skill or amended
`/develop` rules.

## Map: defect → /develop step that should have caught it

### Step 1 (Read source's FULL proof) improvements

**D-31** (`prop_8_30_flat_clean` has 9+ instance hypotheses vs Wedhorn 8.30's 1):

> When reading a Wedhorn theorem statement, **also catalog the hypothesis bundle
> the project's translation will add**. Path α scaffolding (`(P, [IsNoetherianRing P.A₀])`,
> `[IsDomain]`, `[CompleteSpace]`, etc.) adds 5-10 instances. Each must be threadable
> through the discharge chain. Note signature mismatches with source.

### Step 2.5 (State lemmas in Lean with `sorry`) improvements

**D-22** (auto-* wrappers are NOT axiom-clean despite no direct sorry):

> After stating lemmas with `sorry`, **also run `lean_verify` (axiom check) on every
> "supposedly proved" lemma the plan cites**. A lemma can have an empty proof body
> AND a transitive sorryAx via its dependencies. The plan must distinguish
> "0 sorries in body" from "axiom-clean".

**D-32** (Cor832 had 2 sorries, one dead-code):

> Run `grep -c sorry` per critical file BEFORE planning. Don't trust task tracker
> "completed" labels for completeness of sorry-elimination.

### Step 3 (Tension against references) improvements

**D-17** (project's `laurentMinusNormalizedDatum` chain cannot replicate Wedhorn 7.55):

> When the plan says "the project's operation X corresponds to Wedhorn's
> construction Y", **work out an explicit example by hand on both sides**. If
> the rationalOpens differ (e.g., extra `1 ∈ T` constraint), the operations
> don't actually match — even if they're named for the same Wedhorn theorem.

**D-15** (LaurentNormalized class mismatches Wedhorn 7.55):

> When a project class definition has stricter constraints than the source
> requires, the class might not be applicable to all source constructions.
> Verify by counterexample: pick a generic source case, check it satisfies
> the class hypotheses.

**D-23** (Wedhorn 7.45 has hidden `hAplus_le_A₀`):

> When the plan cites "Wedhorn Lemma 7.45 is proved at Lemma745.lean", **read
> the actual Lean signature**, not just the file's docstring. Project theorems
> often carry side hypotheses not present in the Wedhorn statement.

### Step 4 (Provability check) improvements

**D-1, D-2** (T276 requires `hf_nonunit` and `[IsDomain (presheafValue D₀)]`):

> When citing "discharged by project lemma X", **fetch X's signature** and verify
> every typeclass + hypothesis is satisfied at the call site. Don't assume
> "infrastructure proved ✓" means "always applicable".

**D-14** (`[IsDomain (presheafValue D₀)]` not propagated from `[IsDomain A]`):

> For each `[Typeclass T (f X)]` requirement, **check if the project propagates
> T from X**. If not, it's an explicit hypothesis the chain must supply.

**D-3** (T-S6c claimed P3 done, but P3 is pending):

> Task tracker "completed" labels are **aspirational**. Cross-check against the
> actual code: does the named theorem exist as a sorry-free, axiom-clean
> declaration?

### Step 4.5 (Disproof attempt) improvements

**D-16** (T-DEF1: unit in completion ≠ unit in localization):

> Disproof attempt should include **edge cases distinguishing
> "completion-level" from "algebraic-level"** for ring homomorphism
> hypotheses. `IsUnit (φ x)` vs `IsUnit x` for ring iso φ — these are
> equivalent, but `IsUnit (canonicalMap x)` ≠ `IsUnit x` for completion maps.

**D-17** (T-S10: Wedhorn 7.55 chain produces strictly smaller rationalOpen):

> Disproof should check **rationalOpen equality under chain construction**: pick
> A = ℚ_p with non-trivial valuation; trace one step of the chain; verify the
> resulting rationalOpen matches what the source claims.

### Step 4.6 (Consult prior-B2 log) improvements

**D-25** (Stale `docs/ACYCLICITY-CRITICAL-PATH-PLAN.md` contradicts v3+):

> Step 4.6 already consults `.mathlib-quality/b2_log.jsonl`. **Extend to all
> `docs/*.md` planning files** — search for the leaf's name/claim across all
> planning docs to find contradictory previous claims.

### Step 5 (Confidence gate) improvements

**D-22** (Confidence gate didn't catch sorryAx):

> Add a binding gate: "every lemma cited as 'proved' has been `lean_verify`'d
> with axiom output `[propext, Classical.choice, Quot.sound]` ONLY — no
> `sorryAx`."

**D-26** (autoB hypothesis bundle has 9 items, plan only addressed some):

> Gate requires **enumerating EVERY hypothesis** of the closure-path's
> final wrapper theorem. Each hypothesis is either:
> - (a) Auto-supplied by typeclass — verify with `lean_multi_attempt` instance synthesis
> - (b) Discharged by an existing project lemma — verify exists
> - (c) NEW ticket required — add to ticket list

> No "trivially supplied" without one of (a)/(b) verified.

**D-29** (lane_A/lane_B suppliers are hidden recursive obligations):

> Gate: for every hypothesis that's a universally-quantified sub-proof
> (`∀ S', ... → ...`), check whether the discharge is recursive. If so,
> **require an explicit termination argument** (decreasing measure +
> base case) before passing the gate.

**D-33** (no termination argument for lane_A/lane_B recursion):

> Same as D-29 above.

### Step 6 (Write decomposition.md) improvements

**D-25** (contradictory plans coexist):

> When writing `decomposition.md`, **search for and link/redirect/delete every
> older planning doc** that touches the same target. No two docs should claim
> different statuses for the same leaf.

## Map: defect → /develop NEW SUB-STEP needed (not in current process)

These defects suggest /develop is missing a step entirely.

### NEW STEP: hypothesis-bundle expansion

After Step 4 (provability check) and before Step 5 (gate), require:

**Step 4.7: Hypothesis-bundle expansion.** For the closure-path wrapper (e.g.,
`_via_normalizedLaurent_autoCont`), enumerate every hypothesis and trace its
discharge:

1. Read the wrapper's signature.
2. For each hypothesis H, classify as:
   - Class typeclass (auto-derived)
   - Concrete value (e.g., `f₀ : A` — trivially supplied)
   - Equation/inclusion side-hypothesis (verify via grep)
   - Existence-claim ("∃ ..."): create or cite a discharge ticket
   - Universal-claim ("∀ ...") sub-proof: identify recursion if any
3. Each universal sub-proof needs a termination argument.

This catches D-26, D-27, D-28, D-29, D-30.

### NEW STEP: axiom-hygiene verification

After Step 5 (gate), require:

**Step 5.5: Axiom hygiene.** Run `lean_verify` on every project lemma the
plan cites as "discharged from project code". Verify output contains ONLY
`{propext, Classical.choice, Quot.sound}`. Any `sorryAx` invalidates the
"discharged from project code" claim — the lemma is a sorry through, not
discharged.

This catches D-22.

### NEW STEP: cross-doc consistency

After Step 6 (write decomposition.md), require:

**Step 6.5: Cross-doc consistency.** Grep all `docs/*.md` for the leaf's
name and the target theorem's name. Resolve any contradictory status claims
(e.g., older doc says "closed", new audit says "stuck"). Add redirect
headers to stale docs.

This catches D-25.

## Recommended /develop rule additions

1. **Rule: Verify axiom hygiene for every "proved ✓" citation.** Section 1e
   Step 4 should require `lean_verify` output check.

2. **Rule: Read project signatures, not just docstrings.** Section 1e Step 3
   needs the verbatim Lean signature alongside the verbatim Wedhorn quote.

3. **Rule: Enumerate the closure-path's final wrapper hypothesis bundle.**
   Add Step 4.7 (Hypothesis-bundle expansion).

4. **Rule: Termination argument for recursive sub-proofs.** If a hypothesis
   is universally quantified and discharge is recursive, require a decreasing
   measure.

5. **Rule: Cross-check task tracker completion claims against code reality.**
   `task #N completed ✓` ≠ "named theorem exists sorry-free".

6. **Rule: Disproof attempt must include completion-vs-localization edge case.**
   For ring-homomorphism hypotheses involving completions.

7. **Rule: For every project class hypothesis on a derived object** (e.g.,
   `[Foo (presheafValue D)]`), verify propagation from base.

## Source-vs-project mismatch checklist

When the plan says "Wedhorn X corresponds to project Y", verify:

- [ ] Y's signature lists every Wedhorn-stated hypothesis
- [ ] Y's signature doesn't claim more than Wedhorn proves
- [ ] Y's signature additions (Path α scaffolding) are all derivable at call sites
- [ ] An explicit example traces through both Wedhorn's construction and Y's
- [ ] The rationalOpen / value-set / cohomology output of both matches

## Current adversarial-pass summary (for /teach material)

5 passes, 35 defects, LOC scale-up 4-5x from initial estimate. Each pass
attacked a different layer:

1. **v3** (defects 1-15): infrastructure mismatch
2. **v4** (defects 16-21): Wedhorn vs project operations
3. **v5** (defects 22-25): axiom hygiene + side hypotheses
4. **v6** (defects 26-30): hypothesis bundle expansion
5. **v7** (defects 31-35): body soundness + recursion + cross-check

The /develop process didn't catch any of these at the original planning
time. Each represents a missing check that the improvements above would add.

## Round v8 additions

### Lesson L9: Enumerate sorries by chain participation

`grep -c sorry` counts everything including orphans. `/develop` should distinguish:

- **Critical-path sorries**: in the closure chain to the goal.
- **Orphan sorries**: 0 call sites, aspirational stubs.
- **Dead-code sorries**: relied on deleted false lemmas, replacement exists.

Run for each candidate sorry: `grep -rn '<name>'` to find call sites. Orphans + dead-code don't block closure — note as cleanup work, not progress blockers.

**Defect maps**: D-36 (`propA3` orphan), D-37 (`laurentCover_exact_general` orphan), D-38 (`flat_over_base_tate` dead-code), D-39 (orphan-sorry pattern).

### Lesson L10: Theorem name doesn't determine source-statement coverage

A theorem named `prop_8_30_flat_clean` or `isSheafy_ofStronglyNoetherianTate_flat` might prove a Path-α weaker version, not the literal Wedhorn statement.

**Rule**: when planning cites "discharges Wedhorn X", explicitly note any added Path-α scaffolding hypotheses (`[IsDomain]`, `(P, [IsNoetherianRing P.A₀])`, completeness, etc.) and call out that the result is Path-α-Wedhorn-X, not literal Wedhorn-X.

**Defect maps**: D-31 (Path α scaffolding hypotheses), D-40 (A1 ≠ Wedhorn 8.28(b)).

### NEW STEP: Path-α deviation cataloging

After Step 3 (tension against references), require:

**Step 3.5: Path-α deviation cataloging.** For each project theorem cited as
"discharges Wedhorn X":

1. List Wedhorn X's hypothesis bundle (from PDF).
2. List the project theorem's hypothesis bundle (from Lean signature).
3. Diff: every extra project hypothesis is a Path-α deviation. Record in `decomposition.md`:
   ```
   - Wedhorn X requires: [...]
   - Project Y requires: [...]
   - Path-α deviation: [extra hypotheses]
   - Justification: [why we don't lose Wedhorn-faithfulness for the project's goal]
   ```
4. If any deviation has no documented justification, surface as a planning defect.

This catches D-31 + D-40.

### NEW STEP: Orphan + dead-code sorry sweep

Before the confidence gate, require:

**Step 5.6: Orphan sweep.** For each sorry in the project (use `lake env lean` per file):
1. Run `grep -rn '<theorem_name>'` to find call sites.
2. Classify: critical-path / orphan (0 call sites) / dead-code (per docstring).
3. Critical-path sorries are tickets; orphan + dead-code are cleanup items.
4. Document the count of each in `decomposition.md`.

This catches D-36 + D-37 + D-38 + D-39.

## Now-comprehensive checklist for `/develop` at this scale

A project that follows the improvement rules from this document should have, BEFORE writing any tickets:

- [ ] Read the source's FULL proof of R + every sub-lemma it uses (Step 1).
- [ ] State every lemma in Lean with `:= by sorry`; `lake build` clean (Step 2.5).
- [ ] **Each leaf has a verbatim source quote** (Step 3).
- [ ] **Each cited project lemma has its Lean signature verified** against Wedhorn (Step 3 + NEW Step 3.5 = Path-α deviation cataloging).
- [ ] Disproof attempt + edge cases per leaf (Step 4.5).
- [ ] Prior-B2 log consulted (Step 4.6).
- [ ] **Hypothesis-bundle expansion for the closure-path's final wrapper** (NEW Step 4.7).
- [ ] Confidence gate (Step 5).
- [ ] **Axiom hygiene verified** for every "proved ✓" citation (NEW Step 5.5).
- [ ] **Orphan + dead-code sorry sweep** (NEW Step 5.6).
- [ ] decomposition.md written (Step 6).
- [ ] **Cross-doc consistency check** (NEW Step 6.5).

These additions transform `/develop` from "follow the source's structure" to "verify every infrastructure assumption holds against the actual codebase + signatures + axiom hygiene". The 40 defects found in 5 adversarial passes are evidence that without these checks, plans drift from reality.

## What to put in the `/teach`

Once the project is ready for actual implementation work:

1. **Module 1: Source-vs-project tension** (defects 1-21).
   - When project translations of source statements add scaffolding (Path α).
   - When project operations don't structurally match source constructions (Defect #17).
   - When project signatures hide side hypotheses (Defect #23).

2. **Module 2: Axiom hygiene** (defects 22-25).
   - "No direct sorry" ≠ "axiom-clean".
   - Use `#print axioms` / `lean_verify` for verification.
   - Sources of inherited `sorryAx`: deleted false lemmas, transitive dependencies, undischarged-at-call-site hypotheses.

3. **Module 3: Hypothesis bundle expansion** (defects 26-30).
   - The closure-path wrapper has N hypotheses; map each to discharge.
   - Universal-quantification hypotheses can be hidden recursive obligations.
   - Auto-discharge typeclass requires actual instances available at call site.

4. **Module 4: Body, recursion, cross-checking** (defects 31-35).
   - Project signatures vs Wedhorn signatures may differ in path-α-relevant ways.
   - Multi-file projects can have stale planning docs contradicting current findings.
   - Recursive sub-proofs need explicit termination arguments.
   - Structural obstructions (e.g., LaurentNormalized + arbitrary rationalOpen) can be the closure path itself, not just a step.

5. **Module 5: Orphan-sorry pattern + Path-α deviation** (defects 36-40).
   - Sorry count is meaningless without critical-path filtering.
   - Theorem names don't determine which source statement they prove.
   - Distinguish "(project) Path α version of Wedhorn X" from "literal Wedhorn X".

Each module ties to specific `/develop` checklist additions documented above.

## Round v9 additions

### Lesson L11: Verify each sorry isn't already documented as wrong-shaped

Before counting/planning around any project sorry, check:
- b2_log.jsonl for FALSE-AS-STATED entries.
- In-line docstrings for "⚠ WRONG-SHAPED" / "wrong-scoped" / "wrong-shaped" annotations.

Wrong-shaped sorries are CLEANUP work (delete the declaration), not CLOSURE work. They inflate the sorry count without representing actual obstacles.

**Defect maps**: D-41 (`exists_hSpa_points_global` annotated wrong-shaped), D-43 (`exists_ideal_generators_refining_cover` annotated wrong-scoped).

### Lesson L12: Enforce no-placeholder programmatically

Project's `feedback_no_placeholder_theorems.md` bans `theorem foo : True := sorry/trivial` and variants. Extend programmatic check:
- Theorems with conclusion ending in `True := sorry` or `True := trivial`.
- Theorems with `... ∧ True` as a conjunct.
- Theorems whose body is `trivial` masquerading as proof of non-trivial Prop.

Confidence gate (Step 5) should grep for these and surface them as defects.

**Defect maps**: D-42 (`exists_ideal_generators_refining_cover_relative` has `... ∧ True := sorry`).

### NEW STEP: Stub-and-rule audit

Add to Step 5.6 (Orphan sweep):

**Step 5.7: Stub-and-rule audit.** For every sorry in the project:

1. **Wrong-shaped check**: grep docstring for "WRONG-SHAPED" / "wrong-scoped" / "wrong-shape" / "FALSE-AS-STATED". If matched, the theorem is a cleanup item (delete/restate), not a closure target.

2. **Placeholder check**: grep conclusion text for ` ∧ True` / `: True :=` / `= True ∧`. If matched, the theorem violates no-placeholder rule.

3. **Fragmentation check**: for each documented "Wedhorn 8.30 / 8.31 / 8.32 / 8.34 / 7.45 / 7.54" cited as discharged, look for duplicate parallel theorems doing similar work in different files. Consolidate to one canonical version, deprecate aliases.

This catches D-41, D-42, D-43, D-44.

## Comprehensive `/develop` checklist (post-v9)

Required steps for `/develop` at this project's scale:

- [ ] Step 1: Read source's FULL proof + all sub-lemmas (existing)
- [ ] Step 2: Decompose mirroring source structure (existing)
- [ ] Step 2.5: State everything as `:= by sorry`; `lake build` clean (existing)
- [ ] Step 3: Verbatim source quotes + Lean ↔ source match per leaf (existing)
- [ ] **Step 3.5 (NEW): Path-α deviation cataloging** — list project's added hypothesis bundle vs Wedhorn's, document justification.
- [ ] Step 4: Provability check (existing)
- [ ] Step 4.5: Disproof attempt (existing)
- [ ] Step 4.6: Prior-B2 log consultation (existing)
- [ ] **Step 4.7 (NEW): Hypothesis-bundle expansion** — enumerate every hypothesis of closure-path wrapper, classify each into typeclass / existence / universal / trivial.
- [ ] Step 5: Confidence gate (existing, augmented):
  - [ ] **5.5 (NEW): Axiom hygiene** — `lean_verify` shows only `[propext, Classical.choice, Quot.sound]`.
  - [ ] **5.6 (NEW): Orphan sweep** — every sorry classified as critical-path / orphan / dead-code.
  - [ ] **5.7 (NEW): Stub-and-rule audit** — no wrong-shaped/placeholder/fragmented stubs.
- [ ] Step 6: Write decomposition.md (existing)
- [ ] **Step 6.5 (NEW): Cross-doc consistency** — no contradictory plans in `docs/*.md`.

8 NEW steps added (3.5, 4.7, 5.5, 5.6, 5.7, 6.5) compared to the original /develop process.

These additions transform `/develop` from "follow the source's structure" to "verify every infrastructure assumption holds against the actual codebase + signatures + axiom hygiene + project rules". The 45 defects found in 6 adversarial passes are evidence that without these checks, plans drift from reality by **4-5x in LOC** and the codebase accumulates rule-violation stubs.

## v9 module addition for `/teach`

**Module 6 (NEW): Stale stubs and rule violations** (defects 41-45)
- Wrong-shaped theorems annotated but kept as sorries.
- `... ∧ True := sorry` placeholder pattern (banned but present).
- Multiple parallel theorems doing identical work.
- Transitive dependency cascades through unfilled sub-theorems.

## v12 lesson + module addition

### Lesson L13: Per-file lean-diagnostic-messages sweep is mandatory

When planning at scale, don't anchor only on the top-level goal's dependencies (top-down). Also do a per-file `lean_diagnostic_messages` sweep to find FOUNDATIONAL sorries (upstream of typeclass instances, infrastructure lemmas) that the top-down view misses.

Examples found in v12: Wedhorn 7.40(6), 7.41, 8.2(2) — all foundational upstream sorries NOT in the T-DEF or T-S ticket list because they feed in via typeclass instances rather than direct chain calls.

**Required new step** to add to /develop:

**Step 4.8 (NEW): Per-file foundational sorry sweep.** For each file in the chain's transitive imports:

1. Run `lake env lean <file> 2>&1 | grep "warning.*sorry"` to get actual sorry line numbers.
2. For each sorry, check if it's referenced by the closure-path's hypotheses (including typeclass instances).
3. Any sorry that supplies a typeclass instance used by autoB is critical-path even if not directly in the ticket list.

This catches Defects #54-57 type findings.

## Module 7 (NEW): Foundational upstream sorries

(defects 51-57)
- Per-file `lean_diagnostic_messages` sweep, not just top-down.
- Typeclass-supplier sorries are critical-path even if upstream.
- Wedhorn 7.40(6), 7.41, 8.2(2) examples.

Each module ties to specific `/develop` checklist additions documented above.
