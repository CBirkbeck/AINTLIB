# /mathlibable report — `invarNum_normEDS`

> AINTLIB `/overview` Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz
> theorem; elliptic curves; division polynomials; elliptic divisibility sequences).
> Target: `invarNum_normEDS` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:972`.
> Repo root: `/Users/mcu22seu/Documents/GitHub/aintlib-main`.

---

### Baseline (Phase 0)

- lake build:               not re-run (local build stale per task brief; reasoned from source + vendored mathlib tree).
- decl `invarNum_normEDS`:  ✓ resolved at `EllipticDivisibilitySequence.lean:972` (statement lines 972–973, proof line 974).
- **qualified name:**       `invarNum_normEDS` (root namespace — VERIFIED below).
- kind:                     `lemma` (theorem-kind ⇒ Phase 4.5 diamond/defeq risk is **n/a**).
- has sorry:                no (body is `simp [invarNum]`).
- module docstring summary: "Elliptic divisibility sequences (EDS) and the construction of
  normalised EDSs from initial terms" (Apache header, author **David Kurniadi Angdinata**).

**Qualified-name verification.** The decl sits in `section NormEDS` (opened line 881, an
*anonymous* `section` — no `namespace`). Every named namespace in the file is closed before
line 972: `EllSequence` (90–597), `IsEllSequence` (643–702), `PreNormEDS` (704–879). Line 884
has `open EllSequence`, so `invarNum` — which is `EllSequence.invarNum`, defined at line 140
inside `namespace EllSequence` — is referenced unqualified. The lemma itself is therefore at
the **root namespace**: its true qualified name is **`invarNum_normEDS`** (no prefix). The
parsed name in the task brief is correct.

---

### Statement (Phase 1)

`invarNum_normEDS` is a **lemma** evaluating the "invariant numerator" of an elliptic
sequence, specialised to shift `s = 1`, for the canonical normalised EDS `W = normEDS b c d`:

> For all `n ∈ ℤ`, with `W := normEDS b c d`,
> `invarNum W 1 n = W(n+2)·W(n−1)² + W(n+1)²·W(n−2) + W(n)³·b²`.

The general definition `EllSequence.invarNum` (line 140) is
`invarNum W s n = (W(n+2s)·W(n−s)² + W(n+s)²·W(n−2s))·W(s)² + W(n)³·W(2s)²`,
paired with `EllSequence.invarDenom W s n = W(n+s)·W(n)·W(n−s)` (line 145). Design intent
(docstring lines 138–139): for each fixed `s`, the quotient `invarNum s n / invarDenom s n` is
constant in `n` — an *invariant* of the elliptic sequence (proved via `invar_of_net`, line 149).

The lemma is the `s = 1` evaluation. Setting `s = 1` collapses `2s ⇝ 2`, `n±2s ⇝ n±2`, and the
factors `W(s)² = W(1)² = 1` and `W(2s)² = W(2)² = b²` are read off the normalised initial
values `normEDS_one : W 1 = 1` (line 906) and `normEDS_two : W 2 = b` (line 910). The whole
proof is `simp [invarNum]`: unfold `invarNum`, then `simp` discharges the `s = 1` arithmetic and
the two initial-value rewrites.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (file-level `variable`, line 85).
- `(b c d : R)` — the data of the normalised EDS (`section NormEDS` `variable`, line 883).
- `(n : ℤ)` — the index.

Hypotheses: none (unconditional algebraic identity).

Conclusion (math): the displayed closed form for `invarNum (normEDS b c d) 1 n`.
Conclusion (Lean): `invarNum (normEDS b c d) 1 n = normEDS b c d (n+2) * normEDS b c d (n−1)^2 +
normEDS b c d (n+1)^2 * normEDS b c d (n−2) + normEDS b c d n ^ 3 * b ^ 2`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper *evaluation* lemma — it unfolds one project-local definition (`invarNum`) at a
fixed argument (`s = 1`) and substitutes two known initial values. Not a new structure; not a
`## Main statements` entry (the file's only listed main statement is `isEllDivSequence_normEDS`);
not named after a person/place.

(Literature width was EXHAUSTIVE regardless, per protocol.)

### One-line check (Phase 2b)

Body: `simp [invarNum]` — a single `simp` line.
One-liner verdict: **n/a** — kind is `lemma`, not `def`/`abbrev`/`structure`; the Phase-2b def
one-liner gate does not apply. (Noted for context: the proof is trivial — unfold + specialise —
itself a glue-lemma signal, handled in Phases 6–7.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                       | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------|-------|
|  1 | WebSearch (specific form)        | `EDS invariant numerator denominator psi division polynomial Nagell-Lutz`                              | partial | EDS = denominators of `[n]P`; num/denom of `[n]P` involve `ψ`-division-polynomials | Alpoge "Nagell–Lutz, quickly"; MIT 18.783 PS3; Wikipedia EDS. Confirms the *theory*; no named "`invarNum` at `s=1`" identity. |
|  2 | WebSearch (general form / theory)| `"elliptic divisibility sequence" normalized recurrence psi_{n+2} psi_{n-1}^2 closed form`             | yes  | the two EDS recurrences `W_{2n+1}=W_{n+2}W_n³−W_{n−1}W_{n+1}³`, `W_{2n}W_2=W_n(W_{n+2}W_{n−1}²−W_{n−2}W_{n+1}²)` | arXiv:2102.07573 (recurrence relation for EDS); Wikipedia. These are mathlib's `normEDS_odd`/`normEDS_even` — *related but distinct* from `invarNum`. |
|  3 | WebSearch (named-after / aliases)| "elliptic net", "Ward sequence", "elliptic divisibility sequence" (folded into #1–#2)                  | no   | no *named* "invariant of an EDS at `s=1`"  | The invariant-quotient idea (Ward/Stange) is standard theory; the **specific `s=1` evaluation for `normEDS`** is not a named/quotable theorem — it is an intermediate algebraic step. |
|  4 | ChatGPT MCP                      | self-contained Q: is the `s=1` evaluation named, and can the glue lemma stand alone w/o the parent def? | n/a (DOWN) | —                                  | Codex/ChatGPT MCP errored twice (`Codex failed`), as the task brief warned. Fell back to WebSearch + source reasoning. |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`; `ls refs/`                                       | n/a  | (directories absent)                       | No `references/` dir under NagellLutz `.mathlib-quality/`, and no `refs/` store symlinked. Recorded n/a. |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                       | n/a  | —                                          | nLab has no dedicated EDS / elliptic-net page carrying this invariant; not a category-theoretic concept. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                          | Not a categorical concept (concrete arithmetic recurrence). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                          | Not in Stacks' scope (scheme-theoretic AG, not EDS recurrences). |
|  9 | MathOverflow / Math.StackExchange| (folded into WebSearch #1–#2 result sets)                                                               | no   | —                                          | No MO/MSE thread isolates this exact `s=1`-evaluation identity. |
| 10 | recent arXiv (last 5 years)      | arXiv:2102.07573 (EDS recurrence); arXiv:2503.15428 (division polys for arbitrary isogenies); Stange elliptic nets (arXiv:0710.1316) | partial | general EDS / elliptic-net recurrences | Confirm the surrounding theory the project formalises; none names this specific evaluation. |

### Literature summary (Phase 3)

Concept identified as: the **"invariant" of an elliptic divisibility sequence / elliptic net** —
a quotient `invarNum/invarDenom` constant in `n` (the project's Lean encoding of Ward 1948 EDS
theory and Stange's elliptic-net recurrences; the file's `net`/`rel₄` defs are the Lean
formalisation of that theory).

Sources agree on the standard form: **yes** for the *underlying theory* (the EDS recurrences are
textbook; mathlib already has them as `normEDS_odd`/`normEDS_even`). **No** for the specific
decl: the `s = 1` *evaluation* of `invarNum` for `normEDS` is **not a named standalone result**
anywhere — it is a routine intermediate substitution feeding the `invarNum → redInvarNum`
reduction.

Most general standard form: the EDS / elliptic-net *theory* is the general object; the
`invarNum`/`invarDenom`/`net`/`rel₄`/`invar_of_net` machinery is the project's formalisation of
it. The target lemma is a *leaf evaluation* inside that machinery.

Generality dimensions where the literature varies:
  - base structure: Ward (ℤ / fields) → modern (arbitrary `CommRing R`). The project already uses
    the **most general** `[CommRing R]`.
  - dimensionality: EDS (Ward, 1-D, `ℤ`-indexed) → elliptic nets (Stange, `ℤⁿ`). The project
    formalises the 1-D / `ℤ`-indexed strand — the relevant one for division polynomials.

Disagreement with the literature: **none**.

---

### Generality analysis — `invarNum_normEDS`

Literature-standard form (Phase 3): there is no *named* literature statement to match; the
governing object is the EDS invariant over a commutative ring, and the decl's parameters are
already at maximal generality for that object.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | **NO** | already maximal; `normEDS`/`invarNum` and the `ring`/`simp`-closed identity need exactly `CommRing`. |
| 2 | `(b c d : R)`          | the normEDS data  | same                     | NO                  | intrinsic to `normEDS`. |
| 3 | `(n : ℤ)`              | `ℤ`-indexed       | `ℤ`-indexed (EDS strand) | NO                  | `invarNum`/`normEDS` are `ℤ → R` by definition; not an "arbitrary additive group" candidate. |
| 4 | `s = 1` (specialised)  | fixed `s = 1`     | general `s`              | — (this *is* the specialisation; the general-`s` `invarNum` def already exists) | the lemma is *deliberately* the `s=1` slice; generality-in-`s` lives in the def `invarNum`, not this lemma. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** in its typeclasses (`CommRing` is the weakest sensible
base; `ℤ`-index and `R`-coefficients are intrinsic). The `s = 1` specialisation is **not** an
under-generalisation to fix here — generality-in-`s` lives in the *definition* `invarNum` (which
carries the free `s`), and dedicated `s = 1` / `s = 2` evaluation lemmas (`invarNum_normEDS`,
`invarNum_normEDS_two`) are the intended API shape.

Number of weakening opportunities: **0**.
Cost of restatement: n/a (nothing to restate).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
|  1 | bundled hypotheses → typeclasses? | no | no "let X be a foo" preamble; just ring data. |
|  2 | sequences/metric → filters/topology? | no | finite algebraic identity; no limit/topology. |
|  3 | construction → universal-property class? | no | it's an evaluation, not a construction. |
|  4 | set+closure-predicate → bundled substructure? | no | n/a. |
|  5 | vector-space/field-specific → weaken typeclass? | no | already `CommRing` (weakest). |
|  6 | 1-categorical → higher-categorical? | no | not categorical. |
|  7 | concrete index `ℤ` → arbitrary group/monoid? | no | `invarNum`/`normEDS` are `ℤ → R` by construction; the elliptic-net generalisation (`ℤⁿ`, Stange) is a *different decl*, not a re-indexing of this lemma. |

Modern idiom available: **no**. One-line reason: a concrete `simp`-true evaluation of a `ℤ → R`
sequence at a fixed shift; no contemporary mathlib idiom reorganises it without re-architecting
the whole `invarNum` construction (the parent's question, not this leaf's).

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (no definitional equality or typeclass-search path introduced).

---

### Mathlib search-status: `invarNum_normEDS`

Search method note: `lean_loogle` / `lean_leansearch` (mathlib index) and the ChatGPT MCP were
**not usable** in this environment (MCP down; loogle/leansearch deferred tools not surfaced). The
authoritative substitute is a direct grep of the **vendored mathlib tree this project actually
builds against** (`.lake/packages/mathlib/Mathlib/`, rev `09b373db6e24`, toolchain v4.32.0-rc1)
plus WebSearch against the public mathlib4 docs.

[A] Lean-Finder       n/a — tool unavailable in this env.
[B] Loogle            n/a — `lean_loogle` deferred tool not surfaced here.
[C] LeanSearch        n/a — `lean_leansearch` deferred tool not surfaced here.
[D] Grep mathlib src  `grep -rE 'invarNum|invarDenom|invar_of_net|\bnet\b|rel₄|Rel₃|addMulSub' .lake/packages/mathlib/Mathlib/` → **NO HITS** anywhere in mathlib. Separately grepped `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` for `invarNum|invarDenom|net|Invariant` → **NO HITS**.
[E] Name pattern      `grep 'def invarNum\|lemma invarNum_normEDS\|def normEDS' .lake/.../mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → `normEDS`/`preNormEDS`/`normEDS_even`/`normEDS_odd`/`normEDS_two`/`normEDSRec` **present**; `invarNum`/`invarNum_normEDS` **absent**. The only project-tree hits for `invarNum_normEDS` are NagellLutz (line 972) and the HasseWeil fork (line 607) — none in mathlib.

Searched for both:
  - the user's current form (`invarNum (normEDS …) 1 n = …`): **not in mathlib**.
  - the literature-adjacent parent (`invarNum`/`invarDenom`/`net` construction): **not in mathlib**.

**Critical finding.** Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(~547 lines) defines `preNormEDS`, `normEDS`, `normEDS_even`, `normEDS_odd`, `normEDS_two`,
`normEDSRec`, etc. — but has **no `invarNum`, `invarDenom`, `net`, `rel₃`, `rel₄`, or
`invar_of_net`**. The project's fork (1667 lines, ~3× larger) **adds** the entire "invariant of
an elliptic sequence / elliptic net" layer (`net`, `rel₄`, `invarNum`, `invarDenom`,
`invar_of_net`, `redInvarNum`, `redInvarDenom`, the `compl…EDS` family). So the target lemma is
about a **definition that does not exist in mathlib**.

Concluded: **not in mathlib** (both the lemma's form and its parent definition `invarNum` are
absent from the vendored mathlib). ⇒ `NO-mathlib-has-it` is **ruled out** (mathlib has neither
the lemma nor `invarNum`).

---

### Call sites — `invarNum_normEDS`

```
PROJ=/Users/mcu22seu/Documents/GitHub/aintlib-main
grep -rn "\binvarNum_normEDS\b" "$PROJ/projects" --include="*.lean"
```

Internal use count (within NagellLutz, excluding the declaring lines 972–974): **1**.
External-to-file callers in NagellLutz: **0**; but the same lemma is independently re-declared
and used in the **HasseWeil** fork.

| Caller file:line                                                            | Usage pattern (one-line excerpt) |
|-----------------------------------------------------------------------------|----------------------------------|
| `NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1374`              | `simp_rw [redInvarNum, …, compl₂EDSAux_mul_b, invarNum_normEDS]; ring` (proving `invarNum_eq_redInvarNum_mul`, line 1372) |
| `HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:863`       | `…, complEDSAux₂_mul_b, invarNum_normEDS]; ring` (a *separate re-declaration* of the same lemma at line 607 of that file, with its own local `invarNum`) |

Inline-derivation grep (was the identity re-derived inline without the lemma?): **(none)** —
every consumer uses the named lemma `invarNum_normEDS`; the cross-project duplication is
whole-lemma copying across the author's parallel forks, not inline re-derivation.

**Signal read.** The lemma has exactly **one** purpose across the codebase: feeding the single
rewrite that proves `invarNum_eq_redInvarNum_mul` (cancelling the `W₃·W₂ = b·c` factor to define
`redInvarNum`). It is a tightly-scoped internal step of the `invarNum → redInvarNum` reduction,
not a broadly-reused public result. The HasseWeil "copy" is the same EDS-invariant machinery
duplicated into another AINTLIB project — a **cross-project dedup** signal for the cleanup lane,
not a mathlib-public-API signal.

---

### Composition check (Phase 6)

#### Call-sites feedback (Phase 6.0 → 6.0.2)
`K = 1` internal use, no inline re-derivation. By the call-sites heuristic table this leans
toward NO-composable / "wrong abstraction" — *but only if mathlib supplies the building blocks*,
which is exactly what fails below.

#### Can `invarNum_normEDS` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: unfold `invarNum`, specialise `s = 1`, rewrite `normEDS_one` / `normEDS_two`.
  - Mathlib decls available: `normEDS_one`, `normEDS_two` (mathlib **does** have these). But the
    head symbol being unfolded, `EllSequence.invarNum`, is **not** in mathlib.
  - Result: **fails as a *mathlib* composition** — the subject `invarNum` is project-local, so
    there is no mathlib primitive to compose against. `simp [invarNum]` is a composition over a
    **project-local definition**, not over mathlib.
  - Notes: *within the project* (once `invarNum` exists) the lemma is a one-line `simp`. That is
    a "trivial composition over a local def" — the glue-lemma pattern — which does **not** satisfy
    "composable from mathlib's primitives".

Conclusion: **NOT-COMPOSABLE from mathlib.** Mathlib lacks the building block (`invarNum`)
entirely, so the bucket `NO-composable-from-mathlib` (which requires inlining a ≤3-call *mathlib*
composition at call sites and deleting the lemma) does **not** apply: there is nothing in mathlib
to inline. The composability is purely intra-project, over a def that itself isn't upstream.

> Ledger-consistency note: the `mathlibable_ledger.tsv` row for this decl currently reads
> `NO-composable-from-mathlib`. That bucket is **incorrect** by its own Phase-6 gate — it fires
> only when Phase 6 = COMPOSABLE, and here Phase 6 = NOT-COMPOSABLE (mathlib has no `invarNum` to
> inline). This report supersedes that row with the gated verdict below.

---

## Verdict: `invarNum_normEDS`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the `invarNum`/`net`/`rel₄` machinery is the project's faithful
  Lean formalisation of Ward/Stange elliptic-net theory; but the *specific* `s=1` evaluation
  `invarNum_normEDS` is **not a named standalone result** — it is a routine intermediate
  substitution feeding the `invarNum → redInvarNum` reduction.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (`CommRing`, `ℤ`-index — nothing to weaken;
  the `s=1` slice is the intended API shape). No modern-idiom restatement available (Phase 4c
  all-no).
- Mathlib search (Phase 5): **not in mathlib** — and, decisively, the **parent definition
  `EllSequence.invarNum` is itself not in mathlib** (mathlib's EDS file has `normEDS` but none of
  the `invarNum`/`net`/`invar_of_net` invariant layer).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — mathlib has no `invarNum` to
  compose against; the one-line `simp [invarNum]` is a composition over a *project-local* def.

**Rationale.**
`invarNum_normEDS` is a **glue / evaluation lemma whose mathlib-fate is entirely bound to a
definition that is not in mathlib** — `EllSequence.invarNum`. The lemma says nothing more than
"unfold `invarNum` at `s = 1` and read off `W(1)=1`, `W(2)=b`". It cannot stand alone in mathlib:
shipping it requires first (or simultaneously) upstreaming the whole
`invarNum`/`invarDenom`/`net`/`rel₄`/`invar_of_net` elliptic-net-invariant API. Per the skill's
glue-lemma / verdict-inheritance rule, such a lemma **inherits the verdict of its parent
definition** — and that parent's mathlib-worthiness is itself triaged `BORDERLINE-needs-human`
(see `invarNum.md` and the ledger), i.e. a genuine human judgment call the search does not
resolve.

This is not obviously NO. The file's author is **David Kurniadi Angdinata — the same author of
mathlib's `EllipticDivisibilitySequence.lean` and the entire mathlib
`AlgebraicGeometry/EllipticCurve/DivisionPolynomial` tree.** The file is written in full mathlib
house style (`module`, Apache header, `## Main definitions` / `## Main statements` / Ward
reference), and the `invarNum`/`net` layer is exactly the kind of next-increment-on-top-of-
`normEDS` that a continuation mathlib PR would carry: its purpose — proving the invariant-quotient
is constant via `invar_of_net`, then reducing to `redInvarNum`/`redInvarDenom` — is real, reusable
EDS theory directly tied to division polynomials and to Nagell–Lutz. So the parent `invarNum`
construction is **plausibly upstream-bound**, in which case `invarNum_normEDS` rides along as a
natural `s=1` API lemma. But it may equally be staying project-local as Nagell–Lutz / Hasse–Weil
scaffolding. That call — *does the elliptic-net-invariant layer go to mathlib?* — is the human's,
and this leaf lemma's verdict follows it. Hence **BORDERLINE**, not a forced NO.

Why not the other buckets:
- **Not `NO-mathlib-has-it`** — Phase 5 found mathlib has neither the lemma nor `invarNum`
  (so there is nothing to specialise from and no `≤1-line` follows-from sketch to write).
- **Not `NO-composable-from-mathlib`** — Phase 6 is NOT-COMPOSABLE: there is no mathlib building
  block to inline (`invarNum` is absent upstream), so the bucket's gate ("Phase 6 = COMPOSABLE")
  is not met. (This is the correction to the stale ledger row.)
- **Not `YES-*`** — a one-line unfolding of a non-upstream def is never a standalone mathlib
  contribution; if it goes up, it goes up *bundled with the `invarNum` definition*, never alone.

**Numbered questions (≤5):**
  1. Is the `invarNum` / `invarDenom` / `net` / `rel₄` / `invar_of_net` elliptic-net-invariant
     layer (the additions this fork makes on top of mathlib's `normEDS`) **intended for
     upstreaming to mathlib** (e.g. a continuation PR by the same author), or is it staying
     project-local as Nagell–Lutz / Hasse–Weil scaffolding?
  2. If **yes (upstream-bound)**: ship `invarNum_normEDS` (with its sibling `invarNum_normEDS_two`
     and `invarDenom_normEDS_two`) **in the same PR as the `invarNum` definition**, as the standard
     `s=1` / `s=2` evaluation lemmas — agreed? (They are the natural API of the def; the verdict
     then becomes effectively YES-add-as-is *bundled with the parent*, never standalone.)
  3. If **no (project-local)**: the lemma is correctly a private helper and should **not** be
     assessed for mathlib at all — confirm it should be dropped from the mathlibable candidate list
     (verdict collapses to NO, "not a mathlib concern").
  4. Independently of mathlib: this exact lemma (and its `invarNum` def) is **duplicated** across
     `NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` and
     `HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`. Should this be filed as an
     **AINTLIB cross-project dedup ticket** (`lane:cleanup`) to consolidate the shared
     `invarNum`/EDS-invariant API into `Common/`?

**Next action:** user answers Q1 (the load-bearing one). If upstream-bound → bundle this lemma
with the `invarNum` definition in one mathlib PR; re-run `/mathlibable invarNum` to assess the
*parent* def (the real decision). If project-local → drop from the mathlibable list and file the
dedup ticket from Q4. Either way, `invarNum_normEDS` is **never** a standalone mathlib addition —
it inherits the parent `invarNum`'s fate.

---

## Next step

User answers the numbered questions above — chiefly **Q1: is the `invarNum`/`net`
elliptic-net-invariant layer headed for mathlib?** The verdict on this leaf lemma resolves the
moment the parent definition's fate is decided. Re-run `/mathlibable invarNum` to put the real
question (should the *definition* go upstream?) through the full workflow.
