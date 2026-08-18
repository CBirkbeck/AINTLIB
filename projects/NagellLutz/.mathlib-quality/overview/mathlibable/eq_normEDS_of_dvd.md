# /mathlibable report — `IsEllSequence.eq_normEDS_of_dvd`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz / elliptic
> curves / division polynomials / elliptic divisibility sequences).
> File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1271`.
> Re-run 2026-06-21. **Supersedes the 2026-06-18 report** (which read an older
> source where `W 1 ∈ R⁰` was an explicit hypothesis and landed
> YES-but-generalise-first; see "Change since prior run" at the end).
> Local Lean build is stale; verdict reasoned from source + literature + grep
> over the pinned mathlib in `.lake`. ChatGPT MCP was down (Codex command error);
> WebSearch evidence (Wikipedia + arXiv) is conclusive for this classical result.

## Baseline (Phase 0)
- lake build:               not run (stale per task); decl reasoned from source
- decl `IsEllSequence.eq_normEDS_of_dvd`: ✓ resolved at line 1271
- qualified name VERIFIED:   `IsEllSequence.eq_normEDS_of_dvd`
    - `namespace IsEllSequence` (643) is **closed at 702**; line 1271 is inside
      plain `section` / `section Divisibility` with **no enclosing namespace**
      (`section NormEDS` at 881 is a *section*). The decl is written with the
      explicit dotted name `theorem IsEllSequence.eq_normEDS_of_dvd`.
    - The project defines `def _root_.IsEllSequence` (line 135) — same **root**
      namespace and (via `Rel₃`) the **identical body** as mathlib's
      `IsEllSequence`. This theorem lives in the *same* namespace mathlib uses.
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  forked + extended copy of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`, adding the full
  normalisation/characterisation API that mathlib only lists as TODOs.

## Statement (Phase 1)

Let `R` be a commutative ring, `W : ℤ → R` an **elliptic sequence**
(`ellW : IsEllSequence W`): `W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² −
W(n+r)·W(n−r)·W(m)²` for all `m,n,r`. Assume `W 2 ∈ R⁰` (non-zero-divisor) and
`W 1 ∣ W 2`, `W 1 ∣ W 3`, `W 2 ∣ W 4`. Then `∃ b c d, W = (n ↦ W 1 · normEDS b c d n)`.

In words: **every elliptic sequence with the natural EDS divisibility data (and
`W 2` regular) is the constant `W 1` times a canonical normalised EDS.** `W 1`'s
regularity is **derived** in-proof from `dvd₁₂ ▸ two` (it divides `W 2 ∈ R⁰`), not
assumed — the docstring states this explicitly.

- Variables/typeclasses: `{R} [CommRing R]`, `W : ℤ → R`, `open scoped nonZeroDivisors`.
- Hypotheses: `ellW`; `two : W 2 ∈ R⁰`; `dvd₁₂`, `dvd₁₃`, `dvd₂₄`.
- Conclusion (Lean): `∃ b c d, W = (W 1 * normEDS b c d ·)`.

Proof (3 lines): destructure the three `∣` witnesses → `b,c,d`; recover
`one : W 1 ∈ R⁰` via `mul_mem_nonZeroDivisors.mp (h₁₂ ▸ two)`; apply
`IsEllSequence.ext` to `W` vs `W 1 • normEDS b c d` (two elliptic sequences
agreeing on terms 1–4 with `W1,W2` regular are equal), discharging the four
term-matches by `simp` / `normEDS_four` / `ring`.

## Size classification (Phase 2a)

Verdict: **BIG** — one of the two `## Main statements` TODOs in mathlib's own EDS
file ("prove that a normalised sequence satisfying `IsEllDivSequence` can be
given by `normEDS`"); the structural classification theorem for EDS theory (Ward).

## One-line check (Phase 2b)

n/a — kind is `theorem`. Body is a 3-line term-mode proof, not a one-line def.

## Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form | Notes |
|----|---------|-------|------|---------------|-------|
| 1  | WebSearch (specific) | "EDS Ward normalized characterization multiple of normalized EDS" | yes | "a sequence is normalised by replacing Dₙ with Dₙ/D₁; Dₙ ∣ Wₙ" | arXiv math/0402415 (Silverman–Stephens); Wikipedia *EDS* |
| 2  | WebSearch (general / initial data) | "EDS normalisation b c d initial terms W1 W2 W3 W4 division polynomials" | yes | **"an EDS is determined by W2,W3,W4; a triple W2,W3,W4 with W2W3≠0 gives an EDS iff W2 ∣ W4; normalise to W1=1 by dividing by W1."** | Wikipedia / eprint 2008/444 / Stange 2025/521 — `W2 ∣ W4` = our `dvd₂₄` |
| 3  | WebSearch (named-after) | "Ward division polynomial ψₙ(P)" | yes | Ward: ∃ E/ℚ, P with Wₙ = ψₙ(P); normalised EDS = division-poly sequence | canonical ref **Ward, *Memoir on EDS*** (in file's `## References`) |
| 4  | ChatGPT MCP | std form + minimal generality + ring-vs-domain | n/a | — | **MCP down** (Codex `command failed`, gpt-5.4 + gpt-5.4-mini). WebSearch above is conclusive. |
| 5  | Local references | grep `.mathlib-quality/references/` | n/a | — | no refs dir for NagellLutz; PDFs are LOCAL-ONLY per CLAUDE.md. Ward's Memoir is the cited source. |
| 6  | nLab | "elliptic divisibility sequence" | n/a | — | no nLab entry; not categorical. |
| 7  | nCatLab | — | n/a | — | not a categorical concept. |
| 8  | Stacks Project | — | n/a | — | EDS/division-poly recursions not in Stacks. |
| 9  | MathOverflow / MSE | "EDS normalization W2 divides W4" | yes | matches #2: data `(W2,W3,W4)` with `W2∣W4` is the standard parametrisation | consistent |
| 10 | recent arXiv (≤5 yr) | Stange, *Division polynomials for arbitrary isogenies* (2025/521) | yes | reaffirms normalised-EDS = division-poly dictionary | framing is current |

### Literature summary (Phase 3)

Concept: **Ward normalisation / classification of elliptic (divisibility)
sequences by their normalised representative** (`normEDS b c d` = division-poly
sequence). Sources agree on the standard form: **yes** — Wikipedia states it
verbatim: *an EDS is determined by `(W₂,W₃,W₄)`; a triple with `W₂W₃≠0` is an EDS
**iff `W₂ ∣ W₄`**; normalise to `W₁=1` by dividing by `W₁`.* This theorem is the
"extract the normalised representative" direction, with `W₂∣W₄` appearing
verbatim as `dvd₂₄`. The classical statement is over ℤ/domains; the project's
form is **strictly more general** (any commutative ring, with "non-zero-divisor"
replacing "nonzero in a domain"). Disagreement with literature: **none.**

## Generality analysis — `IsEllSequence.eq_normEDS_of_dvd`

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]` | arbitrary commutative ring | ℤ / domain | NO (already weaker) | project generalises *past* the literature's domain setting; CommRing is the maximal base |
| 2 | `two : W 2 ∈ R⁰` | `W 2` non-zero-divisor | `W₂ ≠ 0` in a domain | NO | exact ring-level analogue of "nonzero in a domain"; the `ext` cancellations need it |
| 3 | `dvd₁₂, dvd₁₃, dvd₂₄` | `W1∣W2, W1∣W3, W2∣W4` | `W₂∣W₄` (with `W₁=1`) | NO | with `W₁≠1` allowed, all three are the honest generalisation; with `W₁=1` the first two are automatic |
| 4 | `W 1 ∈ R⁰` | **derived, not assumed** | implicit (`W₁=1`) | already minimal | recovered from `dvd₁₂ ▸ two`; this is the weakening the 2026-06-18 run proposed — **now applied in source** |
| 5 | `W : ℤ → R` | sequence on ℤ | ℕ-indexed in some sources | NO | ℤ-indexing is mathlib's EDS convention |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (more general than the classical
literature statement). Weakening opportunities found: **0** — the only one ever
proposed (don't assume `W 1 ∈ R⁰`) is already in the current source. Cost: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Note |
|----|----------|----------|------|
| 1 | bundled hyps → typeclasses? | no | `IsEllSequence`/`IsEllDivSequence` and `R⁰` are already mathlib's own idiom |
| 2 | sequences → filters/topology? | no | purely algebraic |
| 3 | construct → universal-property class? | no | `normEDS` is concrete; this *is* the characterisation/representability statement |
| 4 | set+closure → bundled substructure? | no | not a substructure question |
| 5 | field-specific → weaken typeclass? | no | already at `CommRing`, weaker than literature |
| 6 | 1-categorical → higher-categorical? | no | n/a |
| 7 | concrete index → general monoid? | no | `W : ℤ → R` is mathlib's fixed EDS convention |

Modern idiom available: **no**. Already mathlib-idiomatic (uses mathlib's own
`IsEllSequence`/`normEDS`/`nonZeroDivisors`), at `CommRing` generality. This *is*
the form that discharges the TODO, in its native vocabulary.

## Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `theorem`.

## Mathlib search-status: `IsEllSequence.eq_normEDS_of_dvd`

[A] Lean-Finder       — tool absent in this env                   (n/a; grep substitute)
[B] Loogle            — tool absent in this env                   (n/a; grep substitute)
[C] LeanSearch        — tool absent in this env                   (n/a; grep substitute)
[D] Grep mathlib src  `grep -rn "eq_normEDS|normEDS_of_dvd|eq_normEDS_of" .lake/.../Mathlib/`   **NO HITS** anywhere
[E] TODO/name pattern `grep "## Main statements" + TODO`   → result is an **explicit OPEN TODO** (mathlib EDS file lines 44–45)

Searched both the user's form (`∃ b c d, W = (W 1 * normEDS b c d ·)`) and the
general "EDS = multiple of normalised EDS" form — **both absent from mathlib**.

Decisive evidence from mathlib's own
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`:

```
## Main statements
* TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
* TODO: prove that a normalised sequence satisfying `IsEllDivSequence`
        can be given by `normEDS`.        ← THIS theorem (+ its corollary)
```

Mathlib's EDS file also lacks the prerequisite API: it has **no
`IsEllSequence.ext`** and **no `IsEllSequence (normEDS …)`** lemma (only
`IsEllSequence.smul`). The project built that scaffolding
(`IsEllSequence.ext` @1217, `IsEllSequence.normEDS` @1211,
`IsEllSequence.of_oddRec_evenRec`, `normEDSRec`) to discharge the TODO.

**De-fork is trivial, not divergent:** the project's `normEDS` is
**byte-identical** to mathlib's (`preNormEDS (b^4) c d n * if Even n then b else 1`),
its `preNormEDS`/`preNormEDS'`/`complEDS₂` share mathlib's signatures, and its
`IsEllSequence` (via `Rel₃`) unfolds to mathlib's exact body. So re-targeting the
statement onto mathlib's definitions is mechanical (the defs are definitionally
equal), not a re-proof.

Concluded: **not in mathlib** (grep returns zero hits for both forms; mathlib
lists it as an unproven TODO and lacks the prerequisite lemmas).

## Call sites — `IsEllSequence.eq_normEDS_of_dvd`

Internal use count: **2** (both external to the declaration line; whole-repo grep
across `projects/` finds no other users; none in mathlib, correctly).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `EllipticDivisibilitySequence.lean:1282` | `h.1.eq_normEDS_of_dvd two (h.2 _ _ ⟨2,_⟩) (h.2 _ _ ⟨3,_⟩) (h.2 _ _ ⟨2,_⟩)` — proves the corollary `IsEllDivSequence.eq_normEDS` (**the other** mathlib TODO) |
| `EllipticDivisibilitySequence.lean:1451` | `obtain ⟨b,c,d,h⟩ := ellW.eq_normEDS_of_dvd two dvd₁₂ dvd₁₃ dvd₂₄` — proves `IsEllSequence.isDivSequence_of_dvd` |

Inline-derivation grep: (none) — not re-derived elsewhere; both consumers route
through this lemma. Load-bearing API (K≥1, no inline re-derivation) → genuine
contribution. It is the hinge from "elliptic + EDS divisibility data" to the
`normEDS` normal form.

## Composition check (Phase 6)

Can it be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `⟨W2, W3, W4/W2, IsEllSequence.ext …⟩` — but `IsEllSequence.ext` **is
not in mathlib**. No extensionality principle for elliptic sequences, no
`normEDSRec`, no `normEDS`-is-elliptic. **Fails** — every block is project-local.

Attempt 2: any other angle — mathlib's EDS API stops at `normEDS` arithmetic
(neg/even/odd/map) + the bare predicates; none compose to *existence of (b,c,d)
recovering an arbitrary elliptic sequence* (that needs the ~15-line `ext`
induction). **Fails.**

Conclusion: **NOT-COMPOSABLE** — needs genuinely new mathlib content (the `ext`
recursor + `normEDS`-is-elliptic + this theorem), not a 1–3 call composition.

## Verdict: `IsEllSequence.eq_normEDS_of_dvd`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature (Phase 3): standard Ward result; Wikipedia states the
  `(W₂,W₃,W₄)`-with-`W₂∣W₄` parametrisation verbatim. Lean form matches and
  generalises it (any CommRing).
- Generality (Phase 4): **MAXIMALLY GENERAL** — strictly beyond the classical
  domain/ℤ statement; 0 weakenings (the one ever proposed is already applied);
  no cleaner modern idiom (4c = no).
- Mathlib search (Phase 5): **not in mathlib** — zero grep hits; mathlib lists
  this exact result as an open `## Main statements` TODO and lacks the
  prerequisite `IsEllSequence.ext`.
- Composition (Phase 6): **NOT-COMPOSABLE** — building blocks themselves missing
  from mathlib.

**Rationale:**

This proves one of the two results mathlib's own EDS file flags as a `## Main
statements` TODO (line 45: *"a normalised sequence satisfying `IsEllDivSequence`
can be given by `normEDS`"*); its one-line corollary `IsEllDivSequence.eq_normEDS`
(line 1280) is the literal restatement of that bullet. The mathematics is the
textbook Ward normalisation — Wikipedia and the standard references state exactly
the `W₂∣W₄` parametrisation appearing here as `dvd₂₄`. The form is faithful **and
more general than the literature**: it holds over any commutative ring, using
"non-zero-divisor" (`W 2 ∈ R⁰`, with `W 1 ∈ R⁰` *derived*, not assumed) where the
classical statement needs a domain. That is mathlib house style, so there is no
generalise-first gap — Phase 4b is MAXIMALLY GENERAL and Phase 4c finds no modern
idiom. (The single weakening a prior run proposed — not assuming `W 1 ∈ R⁰` — has
since been applied to the source, which is exactly why this re-run upgrades the
verdict to add-as-is; see "Change since prior run".)

The fork is a **superset extension, not a divergence**: the project re-declares
mathlib's `IsEllSequence`/`normEDS`/`preNormEDS` *identically* (byte-identical
`normEDS` body; `IsEllSequence` in the same root namespace with mathlib's exact
relation) so it can build API ahead of mathlib. Transplanting the statement onto
mathlib's definitions is therefore mechanical (definitionally equal), not a
restatement — which is why this is add-as-is and not generalise-first. The
*proof* leans on prerequisite lemmas absent from mathlib (`IsEllSequence.ext`,
`IsEllSequence.normEDS`, the `normEDSRec` recursor), so those must travel in the
same PR; that is ordinary dependency-bundling, the packaging note below, not a
change to the statement.

**WHY add it (refactor-actionable):**
- New content: closes the second `## Main statements` TODO in mathlib's EDS file
  (characterisation of normalised EDSs by `normEDS`). The *specific gap* is that
  literal TODO comment at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:45`.
- Prerequisite content to ship in the same PR (all currently missing from mathlib,
  present in this file; they are the blocks the composition check found absent):
  `IsEllSequence.of_oddRec_evenRec`, `normEDSRec'`/`normEDSRec`,
  `IsEllSequence.normEDS` (`normEDS` is elliptic), `IsEllSequence.ext` (4-term
  extensionality for elliptic sequences with `W₁,W₂` regular).
- Composes with mathlib: once added, mathlib's existing `normEDS` arithmetic
  (`normEDS_neg/even/odd`, `map_normEDS`, `normEDS_dvd_normEDS_two_mul`) becomes
  usable on *arbitrary* elliptic/EDS sequences via their normal form — exactly how
  `isDivSequence_of_dvd` (line 1450) transports divisibility.

Proposed mathlib location: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(the same file — directly resolves its TODO).
Proposed PR title:
`feat(NumberTheory/EllipticDivisibilitySequence): every EDS is a multiple of a normalised EDS`
PR grouping: **one PR** bundling the prerequisite scaffolding
(`of_oddRec_evenRec`, `normEDSRec`, `IsEllSequence.normEDS`, `IsEllSequence.ext`)
+ this theorem + its corollary `IsEllDivSequence.eq_normEDS` (the other TODO
bullet) + `IsEllDivSequence.normEDS` (closes line-44 TODO: `normEDS` is an EDS) —
the natural unit "prove the two EDS TODOs". Coordinate with the file's original
author, David Kurniadi Angdinata (copyright holder), since this extends his file.

Pre-PR checklist before opening:
- [ ] `/generalise IsEllSequence.eq_normEDS_of_dvd` — confirm no further weakening
      (expected none; already CommRing + minimal non-zero-divisor, `W1∈R⁰` derived).
- [ ] `/cleanup` the upstreamed slice + this decl — the project uses
      `Rel₃`/`net`/`addMulSub` helper abstractions that may need inlining or
      separate justification for mathlib.
- [ ] Re-check against the *current* mathlib EDS file at PR time (bumped daily;
      the TODO/API may have shifted).
- [ ] Pick a reviewer from recent
      `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` /
      `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` commits.

## Next step

Run `/generalise IsEllSequence.eq_normEDS_of_dvd` to confirm no further weakening,
then `/cleanup` the upstreamable slice, then open
`feat(NumberTheory/EllipticDivisibilitySequence): every EDS is a multiple of a
normalised EDS` — bundling the `ext`/recursor/`normEDS`-is-elliptic prerequisites,
the `IsEllDivSequence.eq_normEDS` corollary, and `IsEllDivSequence.normEDS`,
resolving both `## Main statements` TODOs in mathlib's EDS file.

---

## Change since prior run (2026-06-18 → 2026-06-21)

The earlier report read a source in which `one : W 1 ∈ R⁰` was an **explicit,
`include`d hypothesis** and the proof took it as given; it therefore landed
**YES-but-generalise-first**, with "generalise" meaning two things: (a) drop the
redundant `W 1 ∈ R⁰` assumption, and (b) "de-fork" — re-target the statement onto
mathlib's own `IsEllSequence`/`normEDS` and upstream the prerequisite `ext`/
`normEDS` lemmas.

In the current source both have effectively been resolved at the *statement*
level: line 1267 now reads `omit ellU one in`, and line 1273 **derives**
`one : W 1 ∈ R⁰` from `mul_mem_nonZeroDivisors.mp (h₁₂ ▸ two)` — so weakening (a)
is already applied, and the docstring documents it. Weakening (b) is not a
generalisation under the skill's bucket definitions (Phase 4b = MAXIMALLY
GENERAL, Phase 4c = no modern idiom): the fork's defs are *identical* to
mathlib's, so de-forking is mechanical, and bundling a decl's missing
prerequisites is ordinary upstreaming that every YES-add-as-is decl in a fork
needs — not a statement change. Hence the verdict upgrades to **YES-add-as-is**,
with the prerequisite-bundling recorded as a PR-packaging note rather than a
"generalise-first" blocker.
