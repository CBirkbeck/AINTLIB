# Kickoff message for the incoming worker

*Paste the block below verbatim into a fresh session in the worktree
`/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` on branch `dev/modular-curves`.*

---

You are taking over as **PRODUCER** on the AINTLIB `ModularCurves` project, branch
`dev/modular-curves`, worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves`.

**Read `projects/ModularCurves/.mathlib-quality/HANDOVER-2026-08-09-ds4-weil-pairing.md` in full
before your first edit.** It is written to be the only document you need. Everything below is a
summary of it, not a replacement.

## The situation

The project formalises modular curves as representing objects of moduli problems of elliptic
curves, Katz–Mazur style. Your strand is **DS4: the relative Weil pairing over an arbitrary base**,
built via the KM 2.8 norm/divisor backend.

As of 2026-08-09 the Katz–Mazur construction is **complete except for one statement**:

```
exists_torsionPoint_of_mem_kerMulByN     projects/ModularCurves/ModularCurves/WeilPairing/KMPairing.lean:302
```

— the `⊇` direction of KM (2.8.1.7), `E[N](S) ⊇ Ker([N]^* : Pic⁰ → Pic⁰)`. Every other step —
`(★)`/`(★′)`, the relative theorem of the square, AP-D4 `⊆`, AP-D5 existence and uniqueness, AP-D6
patching, AP-D7 `μ_N`-landing and bilinearity in **both** variables — is proved and axiom-verified
standard-three. `lake build ModularCurves` is green at ~9770 jobs.

## Your task, in order

1. **Fix stale docstrings** (§8 of the handover). Highest priority is
   `torsionSplittingEval_add`'s in `KMBilinear.lean`, which still says "OPEN, `sorry`" and lists
   four missing bricks that all now exist. That comment will actively mislead you or the next
   reader.

2. **The real work: `injective_baseChange_of_residueField_fibre_sModule`** — the last sorry in
   `ForMathlib/LocalFlatnessCriterion.lean`. Its docstring lists the four concrete steps, none of
   which needs a new algebra or module instance; step 1 (`𝔪_{R⧸I} = 𝔪ᴿ.map q` for a surjective
   local hom) is a genuine ~8-line mathlib gap.

   The theorem it feeds, `injective_of_lTensor_residueField_injective_sModule` (Stacks 00MK with
   the source finite over the *upper* ring), was **proved on 2026-08-09** and is axiom-clean — and
   note that the boarded route's "Artin–Rees" was a red herring: the inductive step is the ordinary
   associated-graded step, and it needs no graded machinery because `N/𝔪N` is already a `k`-module.
   A deliberately split form, `injective_of_lTensor_residueField_injective_of_separated`, takes the
   filtration-separatedness as a bare hypothesis so the remaining plumbing never has to construct
   `S ⧸ IS`.

   **Before you commit to this route, verify §6.3 of the handover**: that closing it really does
   discharge `evalGenerator_mem_nonZeroDivisors` (`AbelEquivalence.lean:848`) and thence
   "Blocker 4" (`AbelEquivalence.lean:971`). The board records a *different* route for Blocker 4
   (étale transversality, Stacks §37.38/055S). I believe that route is a detour and the
   commutative-algebra leaf is the real one, but **I did not verify the chain end to end** — and a
   consumer grep shows nothing currently calls either, so wiring is owed on top of the tool.

3. Then `AbelEquivalence.lean:971 / :994 / :1013`, then the two Abel halves (rigidity + surjectivity)
   for AP-D4 `⊇`, which additionally need a **fibrewise degree function on `Pic`** that the tree
   does not yet have.

## Non-negotiable rules

- **Never** `set_option maxHeartbeats` or `synthInstance.maxHeartbeats` on a proof. Fix slowness
  structurally (local `haveI`/`letI`, helper extraction, dropping type ascriptions).
- **Never** put `2>/dev/null` next to a `lake`/`lean` command — a guardrail blocks the command.
  Use `2>&1`.
- Push with `LEAN4_GUARDRAILS_BYPASS=1 git push origin dev/modular-curves`.
- Guardrails block `git reset --hard`, `git restore`, `git checkout --`, and any git command
  containing the word "clean".
- **Never `git add -A` while a subagent is running.** Stage explicit paths.
- Probe/temp files in the session scratchpad only, never under `projects/`.
- `refs/` PDFs are local-only; never commit or push them.
- You are a producer: prove theorems, leave `sorry`s where unfinished, reuse aggressively. Do not
  golf, restyle, dedup, or bump mathlib — that is fleet work on `main`.

## Working standards that have actually paid off here

- **`#print axioms` at every milestone.** `grep sorry` lies: it misses a bare `sorry`, and zero
  file-sorries ≠ axiom-clean because `sorryAx` is inherited. Failed tactics inside structure fields
  and `ext`-blocks silently become `sorryAx` with only a warning.
- **Verify fit by elaboration, not assertion.** Before declaring a result usable, write a
  scratchpad probe that applies it as a black box from an independent file. This caught real
  mismatches seven passes running. De-guard any `fail_if_success` check — three of them here failed
  for the wrong reason and would have "proved" a gap that wasn't there.
- **Run a full `lake build ModularCurves` before adding any import.** It is this tree's name-clash
  detector; a conclusion-grep has twice missed a clash it caught. Two shadowing incidents have
  already cost real time.
- **Grep the conclusion, not the inputs.** Finding all the ingredient lemmas is not evidence the
  target is absent — this tree has repeatedly had the same fact proved by a route sharing no lemma
  names with the one you have in mind. Before choosing a *route*, grep for that route's
  characteristic intermediate conclusion in the route's own vocabulary.
- **Treat every recorded blocker as a dated observation.** Boarded routes in this project have been
  wrong fifteen times — thirteen over-engineered, twice the statement was actually false, once the
  "missing API" already existed. Trust the statement over the sketch, and say so when you deviate.

## Known-dead — do not revisit

`ProjIsPrincipal`/`kappaDivisor_add_linEquiv` (unsound over non-closed fields — see
`.mathlib-quality/b2_log.jsonl`, T10-asm); `WeilPairing/LineVertical.lean` as a source of the
chord-and-vertical function (its header lies); "cover, generators and ratio must be produced
together" (wrong diagnosis); recovering the chord/vertical shape from the ideal identity alone
(needs a Dedekind coordinate ring); the μ_N/level-cover route for the pairing (it would prove the
pairing trivial); Route β (built, axiom-verified, unsourced, retired — dedup debt, not producer
work); fibrewise-trivial ⟹ trivial over a non-reduced base (**false** over `k[ε]/(ε²)`).

## Where the durable context lives

`.mathlib-quality/` on this branch: `tickets.md` (the board — 40k lines, grep don't read),
`plan.md` (goal + design decisions D1–D8), `plan-ds4-abel-pairing.md`,
`plan-blockers-2026-08-08.md` (**includes an external ChatGPT 5.6 Sol review as §"External review"
A1–A6** — read before re-planning Blocker 4), `b2_log.jsonl` (statements found to be *false* —
check before boarding anything), `DEBT.md`, and `beastmode_active` (the live FOCUS breadcrumb;
must exist at both the repo root and under `projects/ModularCurves/`).
