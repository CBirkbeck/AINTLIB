# /mathlibable report — `EllSequence.redInvarDenom_two`

_Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS)_
_Target: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1418`
(declaration body at 1418–1419; the `:1413` handle in the task points at the sibling
`redInvarDenom_zero` line — verified true location is **1418**) · re-assessed 2026-06-21_
_Run: Step-9 /overview mathlibable assessment, single declaration, full 10-phase workflow.
Supersedes the 2026-06-18 run; same verdict, now incorporating the decisive
mathlib-PR-#25990 finding from the sibling `invarDenom` assessment._

**Verdict: BORDERLINE-needs-human**
(its fate is bound to a human decision about upstreaming the parent `redInvarDenom` /
the invariant layer — and that layer is *already being merged upstream by its author*
via open mathlib PR #25990, possibly under renamed identifiers; this is the most
load-bearing of `redInvarDenom`'s three `@[simp]` base cases.)

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale per task — reasoned from source +
  mathlib `.lake` source grep + mathlib4 docs page + literature search).
- decl `EllSequence.redInvarDenom_two`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1418`, inside
  `namespace EllSequence` (opened l.1356) → qualified name **`EllSequence.redInvarDenom_two`**
  confirmed.
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- proof:                     `by simp [redInvarDenom, complEDS, compl', compl]`
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS, builds
  `normEDS`, the complement sequences (`complEDS`/`complEDS'`/`complEDS₂`), and (project
  extension) the `invarNum`/`invarDenom`/`redInvarNum`/`redInvarDenom` invariant layer
  relating an EDS to the Weierstrass addition/doubling formula.

---

### Statement (Phase 1)

`EllSequence.redInvarDenom_two` states: for the project-defined reduced invariant
denominator `redInvarDenom b c d m` of the normalised EDS `normEDS b c d`, the value at
`m = 2` is `1`:

> `redInvarDenom b c d 2 = 1`.

Mathematically `redInvarDenom b c d m` is the (division-free) ratio
`W(m+1)·W(m)·W(m-1) / (W₃·W₂)` for `W = normEDS b c d` — the denominator appearing in the
expression for the ω/`Y`-coordinate of `[m]·P` on a Weierstrass curve (paired with the
numerator `redInvarNum`). The lemma is the **doubling base case** `m = 2`, where this
ratio collapses to `1`. It is the `simp` normal form for the `m % 6 = 2` branch of the
six-way case split in the `redInvarDenom` definition (lines 1377–1386), specialised to the
literal `2`.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` (ambient section variable).
- `(b c d : R)` — the three parameters of `normEDS b c d`.

Hypotheses: none (unconditional evaluation at a literal index).

Conclusion (math): the `m = 2` reduced invariant denominator of any normalised EDS is `1`.
Conclusion (Lean): `redInvarDenom b c d 2 = 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a single-index `simp` evaluation lemma for a project-local `def`; not
a named theorem, not a `## Main results` entry, introduces no structure. (Literature width
run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def` → one-line-**def** check is **n/a**. (The parent `redInvarDenom`
is itself MULTI-LINE: a 6-branch `if m % 6 = …` definition.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                             | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "elliptic divisibility sequence division polynomial doubling formula omega coordinate normalised" | partial | EDS recurrence, doubling formula, normalisation D₀=0,D₁=1 are standard; `redInvarDenom` is **not** a named object | Wikipedia EDS; Stange "Elliptic nets"; eprint 2008/444; arXiv 2102.07573 |
| 2  | WebSearch (general framework)    | "elliptic divisibility sequence" complement W(nm)/W(m) invariant numerator denominator Stange net | no   | the complement `W(nm)/W(m)` notion exists (Stange nets); no "invariant numerator/denominator" named object | confirms complement layer is in the literature; the *invariant/ω-coordinate* layer is bespoke |
| 3  | WebSearch (named-after / aliases)| leansearch/loogle "reduced invariant denominator elliptic divisibility sequence mathlib EllSequence" | no | none | no source names a "reduced invariant denominator"; it is a formalisation-internal definition |
| 4  | ChatGPT MCP                      | (MCP unavailable in env — n/a)                                                                     | n/a  | —                   | substituted by docs-page fetch (#11) which directly answers the "is it upstream" question |
| 5  | Local references                 | `refs/NagellLutz/` / `.mathlib-quality/references/` for "invarDenom"                              | n/a  | (refs are local-only / gitignored; absent in this checkout) | recorded n/a |
| 6  | nLab                             | "elliptic divisibility sequence"                                                                  | n/a  | no EDS/division-polynomial invariant-denominator page | not a categorical concept |
| 7  | nCatLab                          | —                                                                                                 | n/a  | —                   | not categorical |
| 8  | Stacks Project                   | —                                                                                                 | n/a  | —                   | EDS ω-coordinate scaffolding is not a Stacks topic |
| 9  | MathOverflow / Math.SE           | folded into #1/#2                                                                                  | n/a  | nothing on a named "redInvarDenom" | — |
| 10 | recent arXiv (≤5y)               | Stange 2025/521 "Division polynomials for arbitrary isogenies" (arXiv 2503.15428)                 | partial | active modern isogeny division-polynomial work; still no named "reduced invariant denominator" | confirms surrounding math is live; this exact quantity is unnamed |
| 11 | mathlib4 docs page (MCP substitute) | Fetched `…/EllipticDivisibilitySequence.html`; asked for redInvarDenom/invarDenom/invarNum/redInvarNum | no | docs confirm the file defines `complEDS`/`complEDS'`/`complEDS₂` but **no** invariant numerator/denominator and **no** `W(m+1)W(m)W(m-1)` products | decisive: the invariant layer is not (yet) in released mathlib |

Protocol pass: WebSearch ran ≥3 queries at distinct generality (specific doubling form;
general complement/net framework; named-alias). ChatGPT MCP unavailable → substituted by
the mathlib-docs-page fetch (#11). nLab/Stacks/nCatLab/MathOverflow/arXiv each checked or
`n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: a **formalisation-internal "reduced invariant denominator"** — the
ratio `W(m+1)·W(m)·W(m-1)/(W₃·W₂)` used to write the ω/`Y`-coordinate of `[m]·P`. The
surrounding mathematics (EDS, normalisation, complement `W(nm)/W(m)`, division-polynomial
doubling/addition formulas) is fully standard (Ward; Shipsey; Stange; Silverman). The
specific quantity `redInvarDenom` and its base value `redInvarDenom 2 = 1` are **not** a
named literature object — they are scaffolding chosen to keep the coordinate proofs
division-free.
Sources agree on a standard form: n/a (no named object to standardise).
Most general standard form: n/a — index-specific (`m = 2`); the only "generality" axis is
the index, and the whole family is `{redInvarDenom_zero = 0, redInvarDenom_one = 0,
redInvarDenom_two = 1}`.
Disagreement with the literature: none.

---

### Generality analysis — `EllSequence.redInvarDenom_two`

Literature-standard form (from Phase 3): n/a — no named literature object.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | (none — `redInvarDenom` is defined only over `CommRing`) | NO | `redInvarDenom`/`normEDS`/`complEDS` all live over `CommRing R`; already the natural/maximal base. |
| 2 | `(b c d : R)`          | three free EDS params | same | NO | intrinsic to `normEDS b c d`. |
| 3 | index `m = 2`          | literal `2`       | n/a               | NO (by design) | the lemma *is* the `m = 2` specialisation; generalising the index just re-derives `redInvarDenom` itself. |

### Generality verdict (Phase 4b)

Current form: **MAXIMALLY GENERAL** for what it states (arbitrary `CommRing`, free `b c d`;
the only "specialisation" is the index `2`, which is the point). Weakening opportunities: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | bundled-hyps → typeclasses? | no | already a free-parameter statement over `CommRing`; nothing to bundle. |
| 2 | sequences/metric → filters/topology? | no | finite ring computation; no limiting notion. |
| 3 | construction → universal property? | no | it is an *evaluation*, not a construction. |
| 4 | set+closure → bundled substructure? | no | not a substructure statement. |
| 5 | field/metric-specific → weaken typeclass? | no | already at `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | not categorical. |
| 7 | concrete index → general additive structure? | no | the concrete index `2` *is* the content (a base case). |

Modern idiom available: **no** — a `= 1`-at-index-2 base-case fact has no contemporary
reorganisation. (NB: the *parent* `redInvarDenom`/`redInvarNum` were judged
`YES-but-generalise-first` in their own reports — the generalisation lives at the
definition level, not at this leaf.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `EllSequence.redInvarDenom_two`

[A] Lean-Finder        (local index tool unavailable in env)                 n/a — substituted by [D]
[B] Loogle             (local index tool unavailable in env)                 n/a — substituted by [D]
[C] LeanSearch         leansearch.net API (404 / path changed) + web index query   no hits; web index returns only the mathlib EDS docs page (which lacks the invariant layer)
[D] Grep mathlib src   `redInvarDenom|invarDenom|invarNum|redInvarNum|InvarDenom|InvarNum` over `.lake/packages/mathlib/Mathlib/`  **zero hits** (entire released tree)
[E] Name pattern       `redInvarDenom_two` over `.lake/packages/mathlib/Mathlib/`  **zero hits**

Fork-overlap confirmation (so the absence is meaningful): mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` **does** define `complEDS₂`
(l.246), `complEDS'` (l.392), `complEDS` (l.427) — the same complement substrate this
project has — but **none** of the `invarNum`/`invarDenom`/`redInvarNum`/`redInvarDenom`
invariant layer. The docs-page fetch independently confirms "no invariant
numerator/denominator … no `W(m+1)W(m)W(m-1)` products."

**In-flight upstreaming (decisive, from the sibling `invarDenom.md` assessment):** the
invariant layer is the subject of an **open mathlib PR #25990 by the EDS file's author**
(David Angdinata), which is upstreaming `invarDenom`/`invarNum` (and is expected to carry a
**rename** — `invarDenom` "may land under a different final name"). So the `redInvarDenom`
family is *about to exist upstream*, but not yet, and not necessarily under these names.

Searched for both (a) the user's exact form (`redInvarDenom_two`) and (b) the underlying
objects (`redInvarDenom`, `invarDenom`, `invarNum`, `redInvarNum`). Both absent from
released mathlib.

Concluded: **not in mathlib (released)** — mathlib has the `complEDS` substrate but not the
invariant/ω-coordinate layer this lemma belongs to; that layer is mid-upstreaming via PR
#25990.

---

### Call sites — `EllSequence.redInvarDenom_two`

Internal use count (project-wide, excluding the declaring file): **3 real rewrite sites**
(plus several docstring mentions).
External-to-file callers: **3 distinct files**, across **2 projects** (NagellLutz +
HasseWeil) — a genuine cross-project consumer.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:279` | `rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, Affine.addY, …]` — `[2]P` `Y`-coordinate |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:352` | `rw [smulY, ω, redInvarDenom_two, one_mul, complEDSAux₂_two, sub_zero, Affine.addY, …]` — same role |
| `projects/HasseWeil/HasseWeil/Verschiebung/QthRoots.lean:964` | `rw [WeierstrassCurve.ω, redInvarDenom_two, complEDSAux₂_two, …]` — char-2 reduction of ω |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
- **Duplicate declaration** found: `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:926`
  defines its own `@[simp] lemma redInvarDenom_two : redInvarDenom b c d 2 = 1` — the
  HasseWeil "General/PID-track" copy of this very lemma (the duplicated-fork track the
  project context warned about). Signals an in-flight internal consolidation; a dedup
  matter, not a mathlib-novelty matter.

Composability signal: K = 3 internal uses across 2 projects, no inline re-derivation that
bypasses the lemma (the only "re-derivation" is the literal duplicate) → a real, used API
surface. Leans YES-* on usefulness, **but** usefulness is gated by the parent
`redInvarDenom`'s upstreaming (the lemma is meaningless without the parent).

---

### Composition check (Phase 6)

Can `redInvarDenom_two` be derived from mathlib in ≤3 chained calls?

Attempt 1: a mathlib lemma about `redInvarDenom` / `invarDenom`.
- decls used: none exist in released mathlib.
- Result: **fails** — no mathlib primitive about this object to compose with.

Attempt 2: unfold + mathlib `complEDS`/`normEDS` simp lemmas (the substrate that *is* in
mathlib).
- The project proof is `simp [redInvarDenom, complEDS, compl', compl]`; the `redInvarDenom`,
  `compl'`, `compl` being unfolded are the **project's** definitions. Even though `complEDS`
  exists upstream, `redInvarDenom` (the thing evaluated) does not — this is unfolding a
  *project* def, not composing mathlib primitives.
- Result: **fails as a mathlib composition.**

Conclusion: **NOT-COMPOSABLE** from mathlib (composable only from project-local defs).

---

## Verdict: `EllSequence.redInvarDenom_two`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature (Phase 3): surrounding EDS/division-polynomial theory is standard, but
  `redInvarDenom` is an unnamed formalisation-internal quantity; `= 1`-at-2 is a base-case
  computation, not a cited result.
- Generality (Phase 4): MAXIMALLY GENERAL for what it states; no modern-idiom move at this
  leaf (the generalisation lives at the parent-def level, where `redInvarDenom`/`redInvarNum`
  were judged YES-but-generalise-first).
- Mathlib search (Phase 5): NOT in released mathlib (grep zero hits + docs-page confirm);
  the invariant layer is **mid-upstreaming via author PR #25990**, likely with renames.
- Composition (Phase 6): NOT-COMPOSABLE from mathlib (evaluates a project def).

**Rationale:**

`redInvarDenom_two` is correct, `sorry`-free, and genuinely used — three rewrite sites
across two projects (NagellLutz `ZSMul`, HasseWeil `DivisionPolynomial` + `QthRoots`),
discharging the `[2]P` doubling base case of the EDS-based ω/`Y`-coordinate. In isolation
it is a textbook small `simp` characterization lemma. The decisive fact is that its
*subject* — the `redInvarDenom` definition and the whole `invarNum`/`invarDenom`/
`redInvarNum` ω-coordinate layer it lives in — is **entirely a project extension** of
mathlib's EDS file (mathlib carries the `complEDS` substrate, none of the invariant layer).
So the lemma cannot stand alone upstream; its mathlibability is strictly **inherited** from
whether that parent layer is upstreamed.

That parent question is being answered *by someone else, right now*: mathlib PR **#25990**
(the EDS file's own author) is upstreaming `invarDenom`/`invarNum`, expected with a rename.
That is exactly why this is BORDERLINE rather than a clean YES or NO: (i) AINTLIB must **not**
open a competing mathlib PR for this lemma — it would race the maintainer's own in-flight
PR, and the eventual upstream identifiers (`redInvarDenom`? a renamed equivalent? the
base-case `simp` set at all?) are not yet fixed; (ii) there is a **duplicate** of this exact
lemma on HasseWeil's track (`Auxiliary/EllipticDivisibilitySequence.lean:926`), so an
internal consolidation must land first; and (iii) a base-case lemma should never be assessed
for mathlib ahead of the definition it characterises — the parent `redInvarDenom`'s own
`YES-but-generalise-first` verdict (and #25990's outcome) governs this leaf. Bring it to a
human with the parent-layer / PR-#25990 decision spelled out.

**Numbered questions (≤5):**

1. Should AINTLIB **wait for / track mathlib PR #25990** (the author's upstreaming of the
   `invarDenom`/`invarNum` invariant layer) rather than touch `redInvarDenom_two` for
   mathlib? (Strongly recommended: do not race the maintainer's PR.) If yes → no AINTLIB
   mathlib PR; on merge, delete the fork and import from mathlib, heeding any rename.
2. Once #25990 (and any follow-up upstreaming `redInvarNum`/`redInvarDenom`) lands, do the
   small base-case family (`redInvarDenom_zero = 0`, `redInvarDenom_one = 0`,
   `redInvarDenom_two = 1`) belong upstream as **one `simp`-lemma group** beside the
   `redInvarDenom` definition (rather than as standalone lemmas / this leaf alone)?
3. Independently of mathlib: should the NagellLutz↔HasseWeil **duplicate**
   (`HasseWeil/.../EllipticDivisibilitySequence.lean:926`) be consolidated to a single
   `Common/` home now, as a cleanup ticket? (Required regardless of the upstreaming outcome.)
4. If, contrary to (1), AINTLIB does upstream the invariant layer itself, run
   `/mathlibable EllSequence.redInvarDenom` (the **definition**) first and let its verdict +
   chosen final name drive this leaf — confirm that ordering?

**Next action:** user answers the questions. Recommended path: treat `redInvarDenom_two` as
inheriting from the parent `redInvarDenom` / mathlib PR #25990 — **do not open an AINTLIB
mathlib PR for it** (it would race the author's in-flight PR, which is expected to rename the
identifiers); when #25990 lands, drop the fork and import from mathlib. Separately, resolve
the NagellLutz↔HasseWeil duplicate (question 3) as a cleanup ticket.

---

## Next step

User answers the four questions. The lemma's mathlibability is inherited from the
`redInvarDenom` definition and the invariant layer, which is **already being upstreamed by
its author via mathlib PR #25990** (likely with renames) — so the correct move is to track
that PR, not to PR this leaf from AINTLIB, and to resolve the cross-project duplicate first.
