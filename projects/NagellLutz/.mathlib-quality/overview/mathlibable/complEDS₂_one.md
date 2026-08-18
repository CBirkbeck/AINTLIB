# /mathlibable report — `complEDS₂_one`

> Step-9 mathlibable assessment, NagellLutz project. One declaration.
> Generated against mathlib pin in `.lake/packages/mathlib`.

## TL;DR

**Verdict: `NO-mathlib-has-it`.** The declaration is a **byte-for-byte duplicate**
of `complEDS₂_one` already in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:255`. The whole project
file `LutzNagell/EllipticDivisibilitySequence.lean` is a **fork** of that mathlib
module (identical copyright header, identical `def complEDS₂`, identical
`@[simp] lemma complEDS₂_one`). Nothing to upstream — the action is to retire the
fork and `import Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief; reasoned from source — does not affect a verbatim-duplicate verdict)
- decl `complEDS₂_one`:      ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:853`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs from initial terms (a fork of the mathlib file of the same name).

---

### Statement (Phase 1)

`complEDS₂_one` states the value at `k = 1` of the **2-complement sequence** `complEDS₂`
of a (pre-)normalised elliptic divisibility sequence:

> For the 2-complement sequence `Wᶜ₂(k)` attached to the auxiliary EDS data `(b, c, d)`
> over a commutative ring `R`, one has `Wᶜ₂(1) = b`.

Here `complEDS₂ b c d k` is defined (verbatim, in both mathlib and the fork) as
```
(preNormEDS (b^4) c d (k-1)^2 * preNormEDS (b^4) c d (k+2)
   - preNormEDS (b^4) c d (k-2) * preNormEDS (b^4) c d (k+1)^2) * (if Even k then 1 else b)
```
the witness that `W(k) ∣ W(2*k)` for a normalised EDS, i.e. `W(k) * Wᶜ₂(k) = W(2*k)`.
At `k = 1` the bracket collapses (`preNormEDS` at `0, 3, -1, 2` give `0, c, 0, 1`,
so the bracket is `0·c − 0·1 = … ` evaluating to `1`) and the odd factor is `b`,
giving `Wᶜ₂(1) = b`. It is a base-case `simp` lemma feeding the EDS recursion API.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three free parameters of the auxiliary EDS.

Hypotheses: none.

Conclusion (math): `Wᶜ₂(1) = b`.
Conclusion (Lean): `complEDS₂ b c d 1 = b`.

Proof (both copies, identical): `by simp [complEDS₂]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a base-case evaluation lemma (`Wᶜ₂(1) = b`) in the EDS recursion API — a
one-`simp` helper, not a named theorem, not a structure, not a `## Main results` entry.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-liner def heuristic does not
apply. (Note for completeness: the *proof* is a one-liner `simp [complEDS₂]`, which is
exactly what a base-case API lemma should be.) n/a.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

The concept is the mathlib-specific **2-complement sequence** `complEDS₂` of a
normalised EDS — the divisibility witness for `W(k) ∣ W(2k)`. This is *not* a named
object in the classical EDS literature (Ward 1948; Shipsey thesis; Stange; Silverman);
those works study EDS divisibility but do not isolate this particular
`preNormEDS`-built complement term under any standard name. It is an implementation
device introduced by D.K. Angdinata for the mathlib formalisation of division
polynomials / EDS. Its value at `k=1` is a triviality (`Wᶜ₂(1) = b`), not a quotable
theorem in any source.

| #  | Channel                          | Query                                                                  | Hit? | Standard form found                              | Notes |
|----|----------------------------------|------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "2-complement sequence" elliptic divisibility `complEDS₂` value at 1   | no   | —                                                | no external source; term is mathlib-internal |
|  2 | WebSearch (general form)         | elliptic divisibility sequence "W(k) divides W(2k)" complement witness | no   | classical EDS divisibility known; this specific complement term not named | divisibility itself is in Ward/Shipsey, but not this `preNormEDS`-built witness |
|  3 | WebSearch (named-after/aliases)  | Ward / Shipsey / Stange elliptic divisibility sequence normalisation `preNormEDS` | no | — | "preNormEDS"/"complEDS₂" are mathlib coinages |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to manual literature reasoning)    | n/a  | —                                                | covered by channels 1–3 + domain knowledge: this is a formalisation-internal helper, no historical standard form |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "complement" / "complEDS"      | n/a  | —                                                | the existing sibling reports (`preNormEDS'.md`, `preNormEDS.md`, …) already establish this file is a verbatim mathlib fork; no separate paper defines `complEDS₂` |
|  6 | nLab                             | elliptic divisibility sequence                                          | no   | nLab has no EDS / `complEDS₂` page               | not a categorical concept |
|  7 | nCatLab                          | —                                                                       | n/a  | —                                                | not categorical |
|  8 | Stacks Project                   | —                                                                       | n/a  | —                                                | not an algebraic-geometry stack concept (EDS recursion, not schemes) |
|  9 | MathOverflow / MSE               | elliptic divisibility sequence value W(2k)/W(k)                          | no   | general divisibility discussed; this exact base lemma absent | trivial base case, nobody states it |
| 10 | recent arXiv (last 5 years)      | elliptic divisibility sequence division polynomial formalisation        | no   | — (Angdinata's mathlib work is the relevant artefact, not a paper defining this lemma) | — |

### Literature summary (Phase 3)

Concept identified as: the **2-complement sequence `complEDS₂`** of a normalised EDS
(a mathlib-internal construction; *no* classical literature name).
Sources agree on the standard form: n/a — there is no external standard form; this is a
formalisation device. Its `k=1` value is a base-case triviality.
Disagreement with the literature: none (nothing to disagree with).

**Decisive observation (supersedes the literature question):** the declaration is an
*exact copy of an existing mathlib declaration* (see Phase 5). When the project decl is
verbatim-identical to a mathlib decl, the literature-standard-form question is moot — the
verdict is mechanically `NO-mathlib-has-it`.

---

### Generality analysis (Phase 4)

Literature-standard form: n/a (no external standard). The decl is already stated over an
arbitrary `[CommRing R]` with free parameters `b c d : R`, which is the maximal natural
generality for this construction (the EDS recursion needs only a commutative ring).

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | n/a                 | NO                  | `complEDS₂`'s defining expression uses `-` and `^`; comm-ring is the right base. Identical to mathlib's. |
| 2 | `(b c d : R)`          | free ring elements| n/a                 | NO                  | the three EDS parameters; no further weakening meaningful |

#### Generality verdict (Phase 4b)
The current form is: **MAXIMALLY GENERAL** (and identical to mathlib's own statement).
Weakening opportunities: 0.

#### Modern-idiom check (Phase 4c)
Modern idiom available: **no**. This is a concrete base-case evaluation
(`Wᶜ₂(1) = b`) of a recursively-defined sequence; there is no filter/typeclass/
universal-property restatement to make. Mathlib already ships exactly this form, so the
"contemporary mathlib idiom" *is* the current form. (Rows 1–7 of the 4c table all answer
`no`: no preamble→typeclass move, no sequence→filter move, no construction→universal-
property move, no set→bundled-substructure move, no vector-space→module weakening, no
1-categorical→higher-categorical move, and the concrete index `1` is the literal point
being evaluated, not a generalisable parameter.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equality or typeclass-search
path). Skipped.

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       "complEDS₂ value 1", "2-complement EDS one"   → hit (mathlib EDS file)
[B] Loogle            `complEDS₂ _ _ _ 1 = _`                        → hit
[C] LeanSearch        "2-complement sequence of normalised EDS at 1"→ hit (mathlib EDS file)
[D] Grep mathlib src  `complEDS₂_one`, `def complEDS₂`              → **HIT — exact decl**
[E] Name pattern      `complEDS₂_one`                               → **HIT — exact name, root namespace**

Direct grep result (`grep -nE "complEDS₂_one|def complEDS₂"` over
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`):

```
246:def complEDS₂ (k : ℤ) : R :=
247:  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
248:    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
...
255:lemma complEDS₂_one : complEDS₂ b c d 1 = b := by
256:  simp [complEDS₂]
```

This is **identical** to the project's lines 844–854 (def) and 853–854 (lemma): same
`@[simp]` attribute, same statement, same proof, same root-namespace placement (both sit in
`section PreNormEDS` with no enclosing `namespace`; the fork's `namespace EllSequence`
closes at line 597, far above line 853, and the `@[expose] public section` at line 81 adds
no namespace prefix). The fork's file header (copyright, author "David Kurniadi Angdinata")
is byte-identical to mathlib's.

Concluded: **found in mathlib as `complEDS₂_one` (root namespace), identical form** — at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:255`.

---

### Call sites (Phase 6.0)

Internal use count (within NagellLutz, excluding the declaring fork file): effectively the
fork's own downstream copies. `complEDS₂` and its `_one`/`_two`/… accessors are used heavily
in the sibling **HasseWeil** project, where the comments explicitly call
`preNormEDS_mul_complEDS₂` / `normEDS_mul_complEDS₂` **"mathlib's"** (e.g.
`HasseWeil/OmegaPullbackCoeff.lean:431`, `HasseWeil/Auxiliary/DivisionPolynomial.lean:114`) —
i.e. consumers already treat this API as coming from mathlib, not from the NagellLutz fork.

| Caller (illustrative)                                   | Usage pattern |
|---------------------------------------------------------|----------------|
| `HasseWeil/Auxiliary/DivisionPolynomial.lean:114`       | `normEDS_mul_complEDS₂ _ _ _ _` (the `complEDS₂` API, attributed to mathlib) |
| `HasseWeil/OmegaPullbackCoeff.lean:431`                 | comment: "`p(4m) = complEDS₂(2m)·p(2m)` (mathlib's `preNormEDS_mul_complEDS₂`)" |

Inline-derivation grep: the base values (`complEDS₂_zero/one/two/…`) are *not* re-derived
inline anywhere — consumers rely on the named `@[simp]` lemmas. This confirms the API is
real and used; it simply should resolve to **mathlib's** copy, not a fork.

Composability signal: the decl is genuine API with real consumers — but since mathlib
already provides the identical lemma, the consumers should depend on mathlib directly.
This is the classic "K ≥ 1 use, but mathlib has it" → `NO-mathlib-has-it` pattern.

### Composition check (Phase 6)

Can `complEDS₂_one` be derived from mathlib in ≤3 calls? It need not be *derived* — it **is**
a mathlib lemma. The trivial "composition" is identity:
```lean
example : complEDS₂ b c d 1 = b := complEDS₂_one      -- after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
```
Conclusion: **the form is already in mathlib** (composition is the 0-step identity). Routed to
the `NO-mathlib-has-it` evidence, not `NO-composable`.

---

## Verdict: `complEDS₂_one`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): no external standard form (mathlib-internal construction); moot given the verbatim duplicate.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — and identical to mathlib's own statement; no modern-idiom move (4c all `no`).
- Mathlib search (Phase 5): **found in mathlib as `complEDS₂_one`, identical form**, at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:255`.
- Composition check (Phase 6): already in mathlib (identity).

**Rationale:**

The project's `complEDS₂_one` is a **byte-for-byte duplicate** of the mathlib lemma of the
same qualified name. The entire file `LutzNagell/EllipticDivisibilitySequence.lean` is a
fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence` — the copyright header, the
`def complEDS₂` (with its docstring), and the `@[simp] lemma complEDS₂_one : complEDS₂ b c d 1 = b := by simp [complEDS₂]`
are all identical between the two files. The HasseWeil consumers already refer to this
exact API as *"mathlib's"*, confirming the canonical home is mathlib, not the fork. This is
the same situation already documented for the sibling forked decls in this directory
(`preNormEDS'.md`, `preNormEDS.md`, `preNormEDS'_one.md`, …), every one of which concluded
`NO-mathlib-has-it` with a "retire the fork" recommendation.

There is nothing to upstream and no generalisation to make: mathlib's copy is the same
statement at the same (maximal) generality. The only correct action is to stop maintaining
the local copy and depend on mathlib.

**WHY not (refactor-actionable):**
Mathlib already has it, verbatim. Our form *is* the mathlib lemma — it follows in 0 lines
(`complEDS₂_one` resolves directly once the mathlib module is imported).

Existing mathlib decl:        `complEDS₂_one` (root namespace)
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:255`
Our form follows in ≤1 line:
```lean
-- after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`:
example {R : Type*} [CommRing R] (b c d : R) : complEDS₂ b c d 1 = b := complEDS₂_one
```
Call sites in our project: the `complEDS₂` API (incl. `_one`) is consumed mainly in
HasseWeil (which already attributes it to mathlib) and within the NagellLutz fork itself.

Refactor plan (file-level, not just this one lemma — `complEDS₂_one` is one line of a
whole forked module):
1. Replace the forked block in `LutzNagell/EllipticDivisibilitySequence.lean` that
   re-declares `preNormEDS'`, `preNormEDS`, `complEDS₂` (and the `complEDS₂_zero/one/two/…`,
   `preNormEDS_*`, `map_complEDS₂`, etc.) with
   `public import Mathlib.NumberTheory.EllipticDivisibilitySequence`.
2. After the import, every reference to `complEDS₂_one` (and siblings) resolves to mathlib's
   copy unchanged — same name, same root namespace, same `@[simp]` behaviour, so no call-site
   edits are needed for the names that overlap.
3. Keep in the project **only** the genuinely-new declarations the fork adds on top of the
   mathlib module (if any survive after the import); delete the duplicated ones.
4. This must be done as the single fork-retirement refactor coordinated with the other
   `NO-mathlib-has-it` decls in this directory — do **not** delete `complEDS₂_one` in
   isolation, since it shares the file with the rest of the duplicated EDS API.

Next action: retire the EDS fork in favour of
`import Mathlib.NumberTheory.EllipticDivisibilitySequence`; drop the duplicated
`complEDS₂_one` (and the rest of the duplicated EDS API) and let the names resolve to
mathlib. (Coordinate with the sibling fork-retirement reports in
`projects/NagellLutz/.mathlib-quality/overview/mathlibable/`.)

---

## Next step

Retire the forked `EllipticDivisibilitySequence` module: replace the duplicated block with
`public import Mathlib.NumberTheory.EllipticDivisibilitySequence` and delete the local
`complEDS₂_one` (it resolves to the identical mathlib lemma). Do it as one coordinated
refactor with the other `NO-mathlib-has-it` fork decls, not lemma-by-lemma.
