# Kickoff message for the incoming worker

*Paste everything below the line into a fresh session in the worktree
`/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves`, branch `dev/modular-curves`.*

---

You are taking over as **PRODUCER** on the AINTLIB `ModularCurves` project, branch
`dev/modular-curves`, worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves`.

**Read `projects/ModularCurves/.mathlib-quality/HANDOVER-2026-08-09-ds4-weil-pairing.md` in full
before your first edit.** It is written to be the only document you need; everything here is a
summary of it, not a replacement.

## The situation

The project formalises modular curves as representing objects of moduli problems of elliptic curves,
Katz–Mazur style. Your strand is **DS4: the relative Weil pairing over an arbitrary base**, built via
the KM 2.8 norm/divisor backend (owner design decision D7).

As of 2026-08-09, HEAD `b036851cf`, `lake build ModularCurves` green at 9772 jobs:

- The **Katz–Mazur construction is complete except for AP-D4 `⊇`**
  (`exists_torsionPoint_of_mem_kerMulByN`, `WeilPairing/KMPairing.lean:302`). `(★)`/`(★′)`, the
  relative theorem of the square, AP-D4 `⊆`, AP-D5 existence *and* uniqueness, AP-D6 patching, and
  AP-D7 — `μ_N`-landing plus bilinearity in **both** variables — are all proved and axiom-verified
  standard-three.
- **Stacks 00ME is complete.** `ForMathlib/LocalFlatnessCriterion.lean` is entirely sorry-free, every
  declaration axiom-clean. That was the deep commutative-algebra gate under the Abel chain.

## 🛑 Start here: two statements on the critical path are FALSE AS STATED

`evalGenerator_mem_nonZeroDivisors` (`EllipticCurve/AbelEquivalence.lean:836`) and
`relEffCartierDiv_of_degreeOne_package` (`:960`) — **the latter is "Blocker 4", the ticket the whole
board has been pointing at.**

`HasDegreeOneFibreCohomology` (`EllipticCurve/AbelSkeleton.lean:53`) is purely cohomological:
positive-degree Čech exactness plus `finrank (ker d⁰¹) = 1` over every field over the base ring. It
constrains the geometry of `E` not at all, so the fibres may be disconnected and reducible. Both
proofs need integral fibres — `evalGenerator`'s own docstring quotes *"the fibre is integral"* as
though it were a hypothesis. It isn't.

**One counterexample kills both.** `R = k` a field, `E = ℙ¹_k ⊔ Spec k` (proper, flat, lfp,
Noetherian over `k`), `M = 𝒪(-1)` on the `ℙ¹` component and `𝒪` on the point. Then `h⁰(M) = 1` and
`H¹(M) = 0`, so `hpkg` holds; take `σ` the nonzero section supported on the point, so `hσ` holds —
and it vanishes **identically** on the whole `ℙ¹`. Then the evaluation ideal on any nonempty affine
`V ⊆ ℙ¹` is `span {0}`, so `hspan` holds with `f = 0`, which is never a nonzerodivisor; and the
vanishing subscheme is the whole `ℙ¹`, not finite over `Spec k`, so `D.finite` fails and
`IsIso (… .subschemeι ≫ π)` is false.

Detail in §6.5 of the handover, in `b2_log.jsonl` (`AP2-B2-evalgen`, `AP2-B2-blocker4`), and in both
docstrings. The fix is to add smooth geometrically integral fibres plus `deg M_s = 1` — but that is
a statement change, so **ask the project owner before touching them**. `:981` and `:999` are
unaudited and suspect for the same reason. AP-D4 `⊇` is downstream of all of this.

## What you can actually work on today

**AP-E1** — `weilPairing` as a scheme morphism, plus `weilPairing_over`
(`WeilPairing/Basic.lean:49`, `:53`). AP-D7 unblocked it, and it is the only substantial DS4 work not
sitting behind a false statement.

**Scope warning, and it is not on the board.** The KM output is
`torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP` — it depends on a choice of the
auxiliary point `Q`, the invertible `M`, the cover `W`, the trivialisation `e` and the normalisation
`hnorm`. Yoneda needs a **canonical** pairing, so AP-E1 has a prerequisite: *independence of all
those choices*, then naturality in `T`. `WeilPairing/KMUniqueness.lean` (`eq_of_normalized_splitting`)
has part of it, not all. **Spawn the independence sub-tickets before attempting the Yoneda step.**

After that, AP-E2…E6 (the register's spec theorems). Two carry research risk already recorded on the
board: `_self` needs KM's "Notes Added in Proof" (2.8.3 gives only alternation, which is weaker), and
`_nondegenerate` needs Cartier–Nishi duality, absent from mathlib.

## Non-negotiable rules

- **Never** `set_option maxHeartbeats` or `synthInstance.maxHeartbeats` on a proof. Fix slowness
  structurally: local `haveI`/`letI`, helper extraction, dropping type ascriptions. (`backward.*`
  transparency options *are* allowed — they're the v4.33 bump-repair idiom.)
- **Never** put `2>/dev/null` next to a `lake`/`lean` command — a guardrail blocks the whole command.
  Use `2>&1`.
- Push with `LEAN4_GUARDRAILS_BYPASS=1 git push origin dev/modular-curves`.
- Guardrails block `git reset --hard`, `git restore`, `git checkout --`, and any git command
  containing the word "clean".
- **Never `git add -A` while a subagent is running.** Stage explicit paths — it has swept scratch
  files into the repo twice.
- Probe/temp files in the session scratchpad only, never under `projects/`.
- `refs/` PDFs are local-only; never commit or push them.
- Producer role: prove theorems, leave `sorry`s where unfinished, reuse aggressively. Do **not**
  golf, restyle, dedup, or bump mathlib — that is fleet work on `main`.

## Working standards that have actually paid off here

- **`#print axioms` at every milestone.** `grep sorry` lies: it misses a bare `sorry`, and zero
  file-sorries ≠ axiom-clean because `sorryAx` is inherited. Failed tactics inside structure fields
  and `ext`-blocks silently become `sorryAx` with only a warning. Lake's warning replay is also
  partial across runs — a second `lake build` under-reports.
- **Spend ten minutes trying to break a statement before spending a session proving it.** Both of
  today's B2 findings came from asking "what do the hypotheses actually give me?", not from a failed
  proof attempt.
- **Verify fit by elaboration, not assertion.** Before declaring a result usable, write a scratchpad
  probe that applies it as a black box from an independent file. De-guard any `fail_if_success`
  check — three of them here failed for the *wrong* reason and would have "proved" a gap that wasn't
  there.
- **Run a full `lake build ModularCurves` before adding any import.** It is this tree's name-clash
  detector; a conclusion-grep has twice missed a clash it caught. Related live gotcha: inside
  `namespace Module.Flat`, the bare name `lTensor_exact` resolves to `Module.Flat.lTensor_exact`,
  which has a *different* signature — `_root_.` is load-bearing there.
- **Grep the conclusion, not the inputs.** Finding all the ingredient lemmas is not evidence the
  target is absent — this tree has repeatedly had the same fact proved by a route sharing no lemma
  names with the one you had in mind. Before choosing a *route*, grep for that route's characteristic
  intermediate conclusion in the route's own vocabulary.
- **When a proof needs an instance package only to supply one `Prop`, expose the `Prop`.** That one
  move turned a planned `S ↦ S ⧸ IS` instance transport into four steps transporting nothing.
- **Treat every recorded blocker as a dated observation, in both directions.** Boarded routes here
  have been wrong repeatedly: most often over-engineered (2026-08-09 alone — "Artin–Rees is needed",
  it is not; "the base change needs `S ⧸ IS`", it does not; two of four boarded AP-D7 blockers were
  much smaller than recorded), once the "missing API" already existed, and four times the statement
  itself was false. And when you *discharge* a blocker, go back and rewrite the note — stale
  "still open" comments have misdirected work here more than once.

## Known-dead — do not revisit

`ProjIsPrincipal`/`kappaDivisor_add_linEquiv` (unsound over non-closed fields — `b2_log.jsonl`,
T10-asm); `WeilPairing/LineVertical.lean` as a source of the chord-and-vertical function (its header
lies — 2350 lines with no Weierstrass polynomial in them); "cover, generators and ratio must be
produced together" (wrong diagnosis); recovering the chord/vertical shape from the ideal identity
alone (needs a Dedekind coordinate ring); the μ_N/level-cover route for the pairing (it would prove
the pairing trivial); Route β (built, axiom-verified, unsourced, retired — dedup debt, not producer
work); fibrewise-trivial ⟹ trivial over a non-reduced base (**false** over `k[ε]/(ε²)`).

## Where the durable context lives

`.mathlib-quality/` on this branch: `tickets.md` (the board — 40k lines, grep don't read),
`plan.md` (goal + design decisions D1–D8), `plan-ds4-abel-pairing.md`,
`plan-blockers-2026-08-08.md` (**includes an external ChatGPT 5.6 Sol review as §"External review"
A1–A6** — read before re-planning Blocker 4), `b2_log.jsonl` (19 entries; statements found to be
*false* — check before boarding anything), `DEBT.md`. The `beastmode_active` FOCUS breadcrumb is
currently absent — it was removed at the B2 stop, which is the protocol; `/beastmode` recreates it,
and it must exist at both the repo root and under `projects/ModularCurves/`.
