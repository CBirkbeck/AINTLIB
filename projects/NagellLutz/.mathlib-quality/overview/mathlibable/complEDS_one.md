# /mathlibable report — `complEDS_one`

**Verdict: `NO-mathlib-has-it`** — verbatim duplicate already in
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (PR #24826, merged 2025-06-04).

---

### Baseline (Phase 0)

- lake build:               not run (local build stale per task brief; reasoned from source + a
                            local mathlib checkout that contains the upstreamed API)
- decl `complEDS_one`:       resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1581-1583`
                            (the `@[simp]` attribute is line 1581; the `lemma` head is line 1582)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- enclosing namespace:       none — inside `section ComplEDS` (line 1524) with no `namespace`, so the
                            **qualified name is `complEDS_one`** (base name = qualified name)
- module docstring summary:  Forked development copy of mathlib's normalised-EDS / division-polynomial
                            theory for the Nagell–Lutz project. File header reads
                            `Copyright (c) 2024 David Kurniadi Angdinata` — i.e. the *same author* as
                            the mathlib upstream; this file is a fork of
                            `Mathlib.NumberTheory.EllipticDivisibilitySequence` (+ DivisionPolynomial),
                            not an import of it.

Exact source statement:

```lean
@[simp]
lemma complEDS_one : complEDS b c d k 1 = 1 := by
  simp only [complEDS, Int.sign_one, Int.cast_one, one_mul, Int.natAbs_one, complEDS'_one]
```

with section context `variable {R : Type u} [CommRing R] (b c d : R) (k : ℤ)`.

---

### Statement (Phase 1)

`complEDS_one` states that the **complement sequence of a normalised elliptic divisibility sequence,
evaluated at index `1`, equals `1`**. The complement sequence `Wᶜ : ℤ → R` (here `complEDS b c d k`)
is the witness to the divisibility `W(k) ∣ W(n·k)`: by design `W(k) · Wᶜ(k, n) = W(n·k)`. At `n = 1`
this forces `W(k) · Wᶜ(k, 1) = W(k)`, so `Wᶜ(k, 1) = 1`. It is a boundary/initial-value `@[simp]`
normalisation lemma, the `n = 1` companion to `complEDS_zero` (`= 0`).

Variables / typeclasses (Lean side):
- `R : Type u`, `[CommRing R]` — the coefficient ring of the EDS.
- `b c d : R` — the normalising parameters defining `normEDS b c d` (W₂‑factor `b`, W₃ `= c`, W₄ `= d`).
- `k : ℤ` — the base index whose multiples the complement sequence divides into.

Hypotheses: none.

Conclusion (math): `Wᶜ(k, 1) = 1`.
Conclusion (Lean): `complEDS b c d k 1 = 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line boundary `@[simp]` lemma (an initial value of a recursively-defined sequence), not
a named theorem, not a new structure, not a `## Main results` entry. (Literature width run anyway.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner *definition* heuristic does not
apply. n/a. (As a lemma it is, of course, a trivial one-line proof; that only reinforces SMALL.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence complement sequence W(k) divides W(nk) normalised EDS"          | yes  | EDS / normalised EDS `W₀=0, W₁=1`; divisibility `W(m)∣W(n)` when `m∣n` | **Top hit is the mathlib doc page** for `Mathlib.NumberTheory.EllipticDivisibilitySequence` — independent confirmation the API is upstream |
|  2 | WebSearch (general form / theory)| (same results) Stange, Ward, Silverman EDS theory                                                | yes  | EDS as elliptic divisibility sequences (Ward 1948; Stange) | "complement sequence `Wᶜ`" is the Lean-API name for the quotient witness `W(nk)/W(k)`; the underlying object (the divisibility quotient) is classical |
|  3 | WebSearch (named-after / aliases)| EDS = "elliptic divisibility sequence" (Ward), division polynomials                              | yes  | normEDS via division polynomials of an elliptic curve | matches the file's `normEDS`/`preNormEDS` machinery |
|  4 | ChatGPT MCP                      | —                                                                                                | n/a  | MCP down per task brief; fallbacks (WebSearch + direct mathlib source inspection) used instead | the mathlib exact-match makes the standard-form question moot |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for EDS/complement                       | n/a  | references dir not consulted; superseded by exact mathlib-source match | the decisive evidence is the verbatim mathlib decl, not the literature form |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                 | n/a  | not an nLab topic (number-theoretic sequence, not a categorical concept) | — |
|  7 | nCatLab                          | —                                                                                                | n/a  | not categorical | — |
|  8 | Stacks Project                   | —                                                                                                | n/a  | EDS are not a Stacks (scheme-theoretic foundations) topic | — |
|  9 | MathOverflow / MSE               | EDS divisibility quotient                                                                        | n/a  | not needed — exact mathlib match settles it | divisibility property `W(k)∣W(nk)` is standard (confirmed by #1) |
| 10 | recent arXiv                     | arXiv math/0402415 (Stange, sign of an EDS), 1001.5303, 1101.3839                                | yes  | EDS arithmetic; divisibility properties | corroborates that EDS + their divisibility structure are a well-studied published area |

### Literature summary (Phase 3)

Concept identified as: **the complement (cofactor) sequence of a normalised elliptic divisibility
sequence** — the witness `Wᶜ(k,n)` to `W(k) ∣ W(n·k)`, i.e. the quotient `W(n·k)/W(k)`.
Sources agree on the standard form: yes — normalised EDS (`W₀=0, W₁=1`) and the divisibility property
`W(m)∣W(n)` for `m∣n` are classical (Ward 1948; Stange; Silverman). The specific Lean packaging as a
named `complEDS` sequence is David Angdinata's mathlib formalisation.
Most general standard form: divisibility holds over any commutative ring `R` for the normalised EDS;
the `n=1` boundary value `Wᶜ(k,1)=1` is immediate.
Disagreement with the literature: none. The Lean form is at full `CommRing` generality.

**Decisive literature note:** WebSearch result #1 is the mathlib documentation page for
`Mathlib.NumberTheory.EllipticDivisibilitySequence` — the upstreamed home of this exact API.

---

### Generality analysis — `complEDS_one`

Literature-standard form: divisibility quotient of a normalised EDS over a commutative ring; boundary
value at index 1.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | NO                  | EDS theory is set up over `CommRing`; mathlib's `complEDS` uses exactly this. Already maximal for this API. |
| 2 | `b c d : R`            | three ring params | three normalising params | NO                  | intrinsic to `normEDS`. |
| 3 | `k : ℤ`               | integer base index| integer index            | NO                  | the index type for `complEDS`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** — it is *identical* to the mathlib form (same typeclasses,
same signature). There is nothing to weaken.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1–7 | typeclassify / filterise / universal-property / bundled-substructure / weaken-scalars / higher-cat / index-generalise | **no** | This is a one-line boundary value of a fixed `CommRing`-valued integer-indexed sequence. No preamble to typeclassify, no topology to filterise, no construction to characterise. The mathlib form is already the contemporary idiom (it *is* the mathlib idiom — same author). |

Modern idiom verdict: **no** — already in the canonical mathlib formulation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `complEDS_one`

[A] Lean-Finder        n/a (mathlib index unavailable for this exact decl name); covered by [D]
[B] Loogle             pattern `complEDS _ _ _ _ 1 = 1` / name `complEDS_one`  →  not separately queried; superseded by exact source match in [D]
[C] LeanSearch         "complement EDS at one equals one"                       →  superseded by [D]
[D] **Grep mathlib src**  `complEDS_one` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`  →  **HIT, identical form**
[E] Name pattern        `complEDS_one`, plus the whole sibling family            →  **HIT** — full family present

**Direct source evidence** (local mathlib checkout
`/Users/mcu22seu/Documents/GitHub/mathlib4`, master `4d8fc7e8`, file dated 2026-06-19):

```lean
-- Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:440-442
@[simp]
lemma complEDS_one : complEDS b c d k 1 = 1 := by
  simp [complEDS]
```

The entire surrounding family is present and matches the project file 1:1:
`complEDS₂` (246), `complEDS' ` (392), `complEDS'_zero/one/even/odd` (403/407/410/415),
`complEDS` (427), `complEDS_ofNat` (431), `complEDS_zero` (437), **`complEDS_one` (441)**,
`complEDS_neg` (445), `complEDS_even` (448), `complEDS_odd` (458), `map_complEDS'` (534).

**Provenance:** `git log -S "lemma complEDS_one"` ⇒ first introduced by commit `71aa47755e4`,
**PR #24826 "feat(NumberTheory/EllipticDivisibilitySequence): add complement sequences"**,
author **David Kurniadi Angdinata**, merged into mathlib master **2025-06-04** (> 1 year before
today, 2026-06-21). AINTLIB tracks latest mathlib daily (CLAUDE.md + project memory), so the
project's pinned mathlib contains this decl.

Concluded: **found in mathlib as `complEDS_one` (top-level namespace,
`Mathlib.NumberTheory.EllipticDivisibilitySequence`); identical form** — same name, same namespace,
same signature, same `@[simp]` attribute. Only the proof tactic differs cosmetically
(`simp [complEDS]` upstream vs. an explicit `simp only [...]` here).

---

### Call sites — `complEDS_one`

Internal use count (within NagellLutz, excluding the declaring file): **0**.
- The only in-project uses are *inside the declaring file*: lines 1607 and 1612 (`simp [..., complEDS_one]`
  within the `complEDS_odd` proof). As a `@[simp]` lemma it is also in the default simp set.

External-to-file callers (raw grep across all projects):

| Caller file:line | Usage pattern | Note |
|------------------|---------------|------|
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:756` | `simp [complEDS_one]` | **different project's OWN fork** — HasseWeil has its own `Auxiliary/EllipticDivisibilitySequence.lean` copy; this resolves against *that* file's `complEDS_one`, not NagellLutz's |
| `projects/HasseWeil/HasseWeil/Verschiebung/QthRoots.lean:2465` | `simp [redInvarDenom, complEDS_one]` | same — resolves against HasseWeil's own copy |

So there are **no genuine cross-project consumers** of *this* NagellLutz declaration; the HasseWeil
hits are that project's parallel fork (the duplicated `General*/PID*`-style tracks noted in the project
context). This reinforces that the decl is fork-duplicated code, not a unique API surface.

Inline-derivation grep: the equivalent boundary value `complEDS … 1 = 1` is not re-derived inline
anywhere — because the named `@[simp]` lemma (in mathlib, and in each fork) already provides it.

---

### Composition check (Phase 6)

Not needed for the verdict — mathlib has the **exact** lemma, so composition is irrelevant. (For
completeness: it is trivially `by simp [complEDS]`, i.e. a 1-call derivation from the `complEDS`
definition unfolding to `Int.sign 1 * complEDS' … 1 = 1·1 = 1`.) Conclusion: the bucket is decided by
Phase 5's exact match, not by composability.

---

## Verdict: `complEDS_one`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): EDS + complement/divisibility-quotient is a classical, published concept
  (Ward 1948; Stange; Silverman); the *top* WebSearch hit is mathlib's own EDS doc page.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — byte-for-byte the same typeclasses/signature
  as mathlib; nothing to weaken, no modern-idiom improvement available.
- Mathlib search (Phase 5): **found in mathlib as `complEDS_one`** in
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:441`; identical form. Came from PR #24826
  (David Angdinata), merged 2025-06-04.
- Composition check (Phase 6): n/a — exact match supersedes it.

**Rationale:**

This declaration is not a candidate for mathlib because **mathlib already contains it, verbatim**.
The NagellLutz file is a *fork* of `Mathlib.NumberTheory.EllipticDivisibilitySequence` — its header
carries `Copyright (c) 2024 David Kurniadi Angdinata`, the same author who upstreamed the complement-
sequence API to mathlib in **PR #24826** (merged 2025-06-04). The upstreamed `complEDS_one` has the
identical name (top-level, same `Mathlib.NumberTheory.EllipticDivisibilitySequence` namespace),
identical `(b c d : R) (k : ℤ)` signature over `[CommRing R]`, identical statement
`complEDS b c d k 1 = 1`, and the identical `@[simp]` attribute; only the proof tactic differs
cosmetically. The project context flagged exactly this scenario ("this project FORKS parts of mathlib …
so this decl may ALREADY be in mathlib"), and it is realised here. Since AINTLIB bumps mathlib to
latest daily, the project's pinned mathlib has had this lemma for over a year.

**WHY not (refactor-actionable):**

Mathlib already has it — `complEDS_one` at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:441`, in the top-level
`Mathlib.NumberTheory.EllipticDivisibilitySequence` namespace. The user's form *is* the mathlib form
(no specialisation even needed):

```lean
example {R : Type*} [CommRing R] (b c d : R) (k : ℤ) : complEDS b c d k 1 = 1 :=
  complEDS_one        -- mathlib's lemma, same name, same statement
```

- Existing mathlib decl:  `complEDS_one`  (`Mathlib.NumberTheory.EllipticDivisibilitySequence`)
- Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:441`
- Call sites in the NagellLutz project (Phase 6.0): **0** outside the declaring file (only the two
  in-file `simp` uses at lines 1607/1612, which are within the fork's own `complEDS_odd` proof). The
  two HasseWeil hits resolve against HasseWeil's *own* fork, not this declaration.

Refactor plan — this is **not** a per-call-site swap; it is a **whole-fork-retirement** task, because
`complEDS_one` is one lemma inside the `section ComplEDS` block (and the broader file) that mathlib has
fully absorbed:

1. **Do not delete `complEDS_one` in isolation** — it is consumed inside the file by `complEDS_odd`
   (lines 1607, 1612) and is part of an indivisible upstreamed family
   (`complEDS₂ / complEDS' / complEDS / complEDS_{zero,one,ofNat,neg,even,odd} / map_complEDS'`).
2. The correct cleanup is to **drop the project's fork of this API and `import
   Mathlib.NumberTheory.EllipticDivisibilitySequence`** (and the matching DivisionPolynomial modules),
   then delete the duplicated `section ComplEDS` / `NormEDS` blocks, letting the names resolve to
   upstream. All in-file `simp [complEDS_one]` calls keep working unchanged (same name, same `@[simp]`).
3. This is a coordination-level dedup against mathlib, best filed as a single cleanup ticket covering
   the whole forked EDS file (and likely the parallel HasseWeil fork too), not a one-lemma edit. Until
   then, the fork is a deliberate WIP development copy and may stay.

Next action: file/scope a cleanup ticket to **retire the EDS fork in favour of upstream
`Mathlib.NumberTheory.EllipticDivisibilitySequence`** (whole-file dedup); `complEDS_one` is removed as
part of that retirement, not on its own.

---

## Next step

File a cleanup ticket to delete the project's forked copy of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and import the upstreamed module instead;
`complEDS_one` (identical to mathlib's, from PR #24826) disappears with the fork. No new mathlib
contribution is warranted — mathlib already has this lemma verbatim.
