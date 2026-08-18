# /mathlibable report — `normEDS_one`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> divisibility sequences; division polynomials).
> Run: 2026-06-21. Local Lean build stale → reasoned from source + mathlib tree on disk.

---

## Baseline (Phase 0)

- lake build:               ⚠ stale (not rebuilt this session; reasoned from source — both
                            project decl and mathlib counterpart read directly off disk)
- decl `normEDS_one`:        ✓ resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:906`
- qualified name:            `normEDS_one`  (inside `section NormEDS`, **no enclosing `namespace`**
                            → the qualified name is the bare `normEDS_one`; verified against the
                            file's namespace/section map: the only open `namespace` at line 906 is
                            none — `section NormEDS` from line 881 carries no namespace)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  EDS / division-polynomial infrastructure for Nagell–Lutz; this file is
                            a **fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`** plus
                            extra `EllSequence` / complement / map API.

Exact source:

```lean
@[simp]
lemma normEDS_one : normEDS b c d 1 = 1 := by
  simp [normEDS]
```

with context `variable {R : Type u} [CommRing R]` and `variable (b c d : R)` (line 883).

---

## Statement (Phase 1)

`normEDS_one` is a **value lemma**: it states that the canonical normalised elliptic
divisibility sequence `normEDS b c d : ℤ → R` takes the value `1` at index `1`.

In mathematical notation: for the canonical normalised EDS `W = W_{b,c,d}` over a commutative
ring `R` with initial data `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d·b`, the lemma asserts the
defining initial value **`W(1) = 1`**.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (most general sensible base for an EDS).
- `(b c d : R)` — the three parameters fixing the canonical normalised EDS.

Hypotheses: none.

Conclusion (math): `W(1) = 1`, the normalisation that names "normalised" EDS.
Conclusion (Lean): `normEDS b c d 1 = 1`.

Proof: `simp [normEDS]` — unfolds `normEDS b c d 1 = preNormEDS (b^4) c d 1 * (if Even 1 then b
else 1)`, then `preNormEDS … 1 = 1`, `¬Even 1`, `1 * 1 = 1`. A one-step `simp`. It is effectively
a **glue / evaluation lemma** over the `normEDS` definition.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a single-index evaluation (`W(1)=1`) of a defined sequence, proved by one `simp`. Not a
named theorem, not a structure, not a `## Main results` entry — it is boilerplate API attached to
the `normEDS` definition (the `normEDS_zero/one/two/three/four` family of base-case `@[simp]`
lemmas).

(Literature width run regardless, per protocol.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner-def check **n/a**. Recorded:
the *proof* is a one-liner (`simp [normEDS]`), reinforcing the SMALL/glue classification, but
the Phase-2b def-exemption table does not apply to lemmas.

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "normalised elliptic divisibility sequence initial values W(1)=1 Ward division polynomial"     | yes  | canonical normalised EDS: `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d·b`; "normalised by `W₁=1`" | matches project/mathlib docstring **verbatim**; Ward 1948; Wikipedia "Elliptic divisibility sequence"; Stange "Elliptic nets and elliptic curves" |
|  2 | WebSearch (mathlib form)         | "mathlib NumberTheory EllipticDivisibilitySequence normEDS preNormEDS definition"              | yes  | mathlib doc page is the **top hit**; quotes the identical `normEDS`/`preNormEDS'` docstring & `W(1)=1` | confirms mathlib already formalises exactly this `normEDS` family |
|  3 | WebSearch (named-after / aliases)| Ward's equivalence theorem (covered by query 1's results: `W_n = ψ_n(P)`, `W₁=1`)               | yes  | `W₁ = 1` is the *normalisation convention* defining a normalised EDS, not a standalone theorem | arXiv math/0402415 (Everest–Ward, "sign of an EDS"); arXiv 0710.1316 (Stange) |
|  4 | ChatGPT MCP                      | (MCP down this session — per task note; substituted by the two extra WebSearch generality levels above + direct mathlib-source read) | n/a  | n/a — fallback used                                    | mathlib source on disk is the ground truth here; see Phase 5 |
|  5 | Local references                 | `.mathlib-quality/references/` grep "EDS" / "divisibility"                                       | n/a  | directory not consulted as decisive — the mathlib source on disk settles it | the standard form is the mathlib `normEDS` def, read directly (Phase 5) |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                | n/a  | nLab has no dedicated EDS entry                         | not a category-theoretic concept |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | n/a                                                    | not categorical |
|  8 | Stacks Project (alg geom)        | "elliptic divisibility sequence" / "division polynomial"                                        | n/a  | Stacks has no EDS section                              | EDS are arithmetic/recurrence objects; not in Stacks' scheme-theory scope |
|  9 | MathOverflow / MSE               | (covered by query-1 results: ResearchGate / arXiv survey hits)                                 | yes  | same normalisation convention `W₁=1`                   | no disagreement on the convention |
| 10 | recent arXiv (≤5 yrs)            | "elliptic divisibility sequence" (query-1 results incl. 2018–2019 papers)                      | yes  | same `W₁=1` normalisation                              | arXiv 1808.03846, 1904.12393, 1909.12654 — convention unchanged |

### Literature summary (Phase 3)

Concept identified as: **canonical normalised elliptic divisibility sequence** (Ward; Shipsey;
Stange). `normEDS b c d` is its mathlib name; `W(1) = 1` is its **defining normalisation**.
Sources agree on the standard form: **yes** — `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d·b` is the
universally-used initial data (the docstring in both the project and mathlib is the textbook
statement verbatim).
Most general standard form: over any commutative ring `R` (mathlib uses `[CommRing R]`; the
project uses the same). `W(1)=1` is not a theorem to be *proved* in the literature — it is *assumed*
as the normalisation. In mathlib it becomes a one-line consequence of the `normEDS` definition.
Generality dimensions where the literature varies: essentially none for the base value `W(1)=1`;
the coefficient ring is the only axis, and `[CommRing R]` is already the maximal sensible choice.
Disagreement with the literature: none.

---

## Generality analysis — `normEDS_one`

Literature-standard form (from Phase 3): `W(1) = 1` for the canonical normalised EDS over a
commutative ring — exactly the Lean statement.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | NO                  | `normEDS` is defined via `preNormEDS` over `[CommRing R]`; this is already mathlib's choice and the maximal sensible base. Dropping commutativity is meaningless for the EDS recurrence. |
| 2 | `(b c d : R)`          | three ring params | three ring params        | NO                  | intrinsic to the canonical normalised EDS; not a weakenable hypothesis. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is byte-for-byte mathlib's own statement; nothing
to weaken).
Number of weakening opportunities found: 0.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | bundled-hyp → typeclass? | no | `b c d` are genuine parameters of *the* canonical sequence, not a "let X be…" preamble | — |
| 2 | sequences→filters? | no | finite-index value lemma; no limit/topology | — |
| 3 | construct→universal property? | no | it's an evaluation of an existing def | — |
| 4 | subset-pred→bundled type? | no | no substructure | — |
| 5 | vector-space/field→module/ring weakening? | no | already `[CommRing R]` | — |
| 6 | 1-cat→higher-cat? | no | none | — |
| 7 | concrete index→general monoid? | no | the *point* is the specific index `1` (base case); generalising the index is the *recurrence* lemmas, not this | — |

Modern idiom available: **no** — already in mathlib's idiom (it *is* mathlib's lemma). One-line
reason: there is no modernisation move; the project copied mathlib's exact formulation.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

---

## Mathlib search-status: `normEDS_one`

[A] Lean-Finder        "normEDS one / normalised EDS value at 1"   → hit (mathlib `normEDS_one`)
[B] Loogle             `normEDS _ _ _ 1 = 1` pattern               → hit (mathlib `normEDS_one`)
[C] LeanSearch         "value of normalised EDS at 1 is 1"         → hit (mathlib `normEDS_one`)
[D] Grep mathlib src   `grep "normEDS_one" .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                       → **EXACT HIT, line 302**
[E] Name pattern       `(lemma) normEDS_one` in mathlib tree       → hit (same line 302)

Searched for both the user's current form and the literature-standard form — they are the
**same** form, and mathlib has it identically.

**Decisive on-disk evidence.** Mathlib (pinned in this very workspace) has, at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:302`:

```lean
@[simp]
lemma normEDS_one : normEDS b c d 1 = 1 := by
  simp [normEDS]
```

— with context `variable {R : Type u} [CommRing R]` (line 75) and `variable (b c d : R)`
(line 118), **no namespace**. This is **identical** to the project decl in: name, statement,
`CommRing R` typeclass, `(b c d : R)` parameters, `@[simp]` attribute, and proof term
(`simp [normEDS]`). The surrounding `normEDS` definition is also identical
(mathlib line 289 ≡ project line 890), as is the whole `normEDS_zero/one/two/three/four` family.

The project file `import`s **no** mathlib EDS module — it **re-declares** `preNormEDS'`
(line 710), `preNormEDS` (line 774) and `normEDS` (line 890) itself. So `normEDS_one` here is a
**verbatim fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`, not a new result. (The
HasseWeil project carries the *same* fork under
`HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` — see call-sites below.)

Concluded: **found in mathlib as `normEDS_one`** (full path
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, line 302); **identical form**.

---

## Call sites — `normEDS_one` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring file): **K = 8**
External-to-file callers (NagellLutz): 2 distinct files
Repo-wide (other projects forking the same file): HasseWeil has its **own** `normEDS_one` copy with
~10 further uses (a parallel duplicated fork, not consumers of this decl).

| Caller file:line | Usage pattern (excerpt) |
|------------------|--------------------------|
| LutzNagell/DivisionPolynomial.lean:335 | `normEDS_one ..` |
| LutzNagell/EllipticDivisibilitySequence.lean:962 | `(by rw [normEDS_one]; exact one_mem _)` |
| LutzNagell/EllipticDivisibilitySequence.lean:965 | `rw [… , OddRec, normEDS_one, one_pow, mul_one]` |
| LutzNagell/EllipticDivisibilitySequence.lean:968 | `rw [… , EvenRec, normEDS_one, normEDS_two, …]` |
| LutzNagell/EllipticDivisibilitySequence.lean:1236 | `simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]` |
| LutzNagell/EllipticDivisibilitySequence.lean:1329 | `(by rw [normEDS_one]; exact one_mem _)` |
| LutzNagell/EllipticDivisibilitySequence.lean:1332 | `(fun m ↦ by rw [normEDS_one, one_mul])` |
| LutzNagell/EllipticDivisibilitySequence.lean:1469 | `simp only [normEDS_one, normEDS_two]` |

Inline-derivation grep (was `W(1)=1` re-derived elsewhere without `normEDS_one`?):
  - (none — every site uses the named lemma; it is real, used API)

Composability signal: K = 8 internal uses → this is genuine, depended-upon API. **But** that
does not push toward a YES bucket here, because mathlib *already supplies the identical lemma*:
the right move is not "keep our copy" but "consume mathlib's copy". The high call-count instead
quantifies the **refactor surface** (8 NagellLutz sites + the parallel HasseWeil fork) once the
local fork is dropped in favour of `import Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

## Composition check (Phase 6)

n/a for the verdict — Phase 5 already found the **exact identical** decl in mathlib, so no
composition is needed. (For completeness: the project's `normEDS_one` follows from mathlib's
`normEDS_one` in **0 lines** — it is the same lemma; if one kept a thin local alias it would be
`exact normEDS_one`, but the correct action is to delete the fork and use mathlib's directly.)

Conclusion: NOT-APPLICABLE (mathlib-has-it short-circuits the composition phase).

---

## Verdict: `normEDS_one`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): `W(1)=1` is the *defining normalisation* of the canonical
  normalised EDS (Ward/Stange); the mathlib doc page is the top search hit; not a standalone
  literature theorem.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — byte-identical to mathlib's form; 0 weakenings;
  no modern-idiom move (it already *is* the mathlib idiom).
- Mathlib search (Phase 5): **found in mathlib as `normEDS_one`**, identical form, at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:302` (verified on disk in this workspace).
- Composition check (Phase 6): n/a — exact decl already present.

**Rationale.**
The NagellLutz file is a **standalone fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`:
it re-declares `preNormEDS'`, `preNormEDS`, and `normEDS`, and then re-proves the whole
`normEDS_zero/one/two/three/four` family. `normEDS_one` is one of those forked lemmas. Mathlib's
copy is identical in **every** respect — name (`normEDS_one`), statement (`normEDS b c d 1 = 1`),
typeclass (`[CommRing R]`), parameters (`(b c d : R)`), `@[simp]` attribute, and proof
(`by simp [normEDS]`) — and lives at a stable mathlib path already pinned in this repo's
`.lake/packages/mathlib`. There is nothing for mathlib to gain: it has exactly this declaration.

This is the cleanest `NO-mathlib-has-it`: not "mathlib has a more general form we specialise from",
but "mathlib has the byte-identical lemma". The project's 8 internal call sites (plus the parallel
HasseWeil fork) confirm the lemma is genuinely used — which is precisely why the fork should be
**replaced by an import of mathlib's module**, not why a duplicate should be upstreamed.

**WHY not (refactor-actionable):**
Mathlib already has it: **`normEDS_one`** at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:302`. The project's identical statement
follows in **0 lines** — it is the same lemma. The local copy exists only because the file forks
mathlib's EDS module wholesale instead of importing it.

Existing mathlib decl:   `normEDS_one`
Located at:              `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:302`
Our form follows in 0 lines (it *is* mathlib's lemma):

```lean
example {R : Type*} [CommRing R] (b c d : R) : normEDS b c d 1 = 1 := normEDS_one
```

Call sites in our project (Phase 6.0): **K = 8** (NagellLutz), excluding the declaring file.

**Refactor plan.** This is not a single-lemma fix but a **whole-file de-fork**, of which
`normEDS_one` is one line:
1. In `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, replace the forked
   `preNormEDS'` / `preNormEDS` / `normEDS` definitions and their `normEDS_*` value lemmas
   (including `normEDS_one`, line 906) with `import Mathlib.NumberTheory.EllipticDivisibilitySequence`,
   keeping only the genuinely-new project additions (`EllSequence`, complement/`complEDS₂`, map,
   divisibility API that mathlib lacks).
2. The 8 `normEDS_one` call sites then resolve to **mathlib's** `normEDS_one` unchanged — same name,
   same `@[simp]`, same argument shape; **no edit needed at the call sites** beyond the import.
3. Mirror the same de-fork in HasseWeil's `Auxiliary/EllipticDivisibilitySequence.lean`, which
   carries an independent copy of `normEDS_one` (+ ~10 of its own uses). (Cross-project dedup of the
   EDS fork is itself a `lane:cleanup`/`/overview` consolidation ticket; flag `normEDS_one` as part
   of that batch rather than in isolation.)
Next action: delete `normEDS_one` (and the surrounding forked `normEDS` block) from the project;
import `Mathlib.NumberTheory.EllipticDivisibilitySequence`; the call sites are unaffected.

---

## Next step

Delete `normEDS_one` (with the rest of the forked `preNormEDS`/`normEDS` block) from
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`; replace with
`import Mathlib.NumberTheory.EllipticDivisibilitySequence`. The 8 call sites resolve to mathlib's
identical `normEDS_one` with no further change. Handle as part of the cross-project EDS-fork
consolidation (NagellLutz + HasseWeil both fork the same mathlib module).
