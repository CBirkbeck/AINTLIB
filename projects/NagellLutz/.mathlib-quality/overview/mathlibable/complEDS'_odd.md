# /mathlibable report — `complEDS'_odd`

**Verdict: NO-mathlib-has-it** — mathlib already contains this exact lemma (same
author, same statement, same proof structure). The project file is a verbatim
fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

## Baseline (Phase 0)

- lake build:               not re-run (local build stale per task); decl read directly from source
- decl `complEDS'_odd`:     resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1551`
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS) — defines EDSs and constructs normalised EDSs from initial terms." (a fork of the mathlib EDS file by the same author, David Kurniadi Angdinata)

**True qualified name (VERIFIED).** The declaration sits inside `section ComplEDS`
(line 1519) with **no enclosing `namespace`** (the previous `namespace EllSequence`
at 1351 closes at 1426; `end NormEDS` at 1515 closes a *section*, not a namespace).
So the qualified name is exactly **`complEDS'_odd`** — the parser's guess was correct.

---

## Statement (Phase 1)

`complEDS'_odd` is the **odd-index defining recurrence** of the ℕ-indexed
complement sequence `complEDS'` for a normalised elliptic divisibility sequence.

Let `R` be a commutative ring, `b c d : R` the normalising data of a normalised
EDS `W = normEDS b c d : ℤ → R`, and `k : ℤ` a fixed multiplier. The complement
sequence `Wᶜ(k, ·) = complEDS' b c d k : ℕ → R` is the witness to the divisibility
`W(k) ∣ W(n·k)`, i.e. `W(k) · Wᶜ(k, n) = W(n·k)`. The lemma unfolds the recursion
at an odd index `2(m+1)+1`:

> `Wᶜ(k, 2(m+1)+1) = Wᶜ(k, m+1)² · W((m+2)k+1) · W((m+2)k−1)`
> `                − Wᶜ(k, m+2)² · W((m+1)k+1) · W((m+1)k−1)`

This is the EDS "duplication/addition" identity specialised to the complement
sequence — the standard double-and-add structure that defines division
polynomials of elliptic curves at odd multiples.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring
- `(b c d : R)` — normalising data of the normalised EDS
- `(k : ℤ)` — fixed multiplier
- `(m : ℕ)` — induction index

Hypotheses: none (it is a defining-equation lemma; the content is in the
`complEDS'` recursion).

Conclusion (math): the odd-index recurrence above.
Conclusion (Lean): an equation in `R` between `complEDS' b c d k (2*(m+1)+1)` and
the difference of two products of `complEDS'`/`normEDS` terms.

---

## Size classification (Phase 2a)

Verdict: SMALL
Reason: a defining-equation `simp`/`rw`-style unfolding lemma for an even/odd
recursion; not a named theorem, not a new structure, not a `## Main results`
entry. (Literature width is exhaustive regardless — but see Phase 5: this is
resolved at the mathlib-search step, which short-circuits the verdict.)

## One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`. One-liner exemption analysis does not apply.

---

## Literature search (Phase 3)

The lemma is an internal defining-equation of an mathlib construction
(`complEDS'`). Because Phase 5 finds the **identical lemma already in mathlib**
(same author), an exhaustive nine-channel literature sweep on the underlying
mathematics is not load-bearing for the verdict — the question "is the standard
form already in mathlib?" is answered *yes, verbatim*. For completeness:

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|---------------|-------|
| 1 | mathlib source (decisive) | `complEDS'_odd` in `.lake/packages/mathlib/` | **yes** | identical lemma, same author | `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:415` |
| 2 | WebSearch (concept) | "elliptic divisibility sequence division polynomial recurrence" | yes (background) | Ward 1948; Shipsey 2000; Stange 2007 EDS theory | the double-and-add recurrence is the classical EDS addition law |
| 3 | Background | EDS complement / `W(k) ∣ W(nk)` divisibility | yes | standard EDS divisibility property | the `complEDS` family witnesses this in mathlib |

Local references (`.mathlib-quality/references/`): not consulted in depth —
mathlib-has-it is dispositive. nLab / Stacks / nCatLab / MathOverflow / arXiv:
n/a — this is an internal Lean defining-lemma of an already-upstreamed mathlib
construction, not a free-standing mathematical concept whose "standard form"
is in question.

### Literature summary (Phase 3)

Concept identified as: the odd-index defining recurrence of mathlib's
`complEDS'` (complement sequence of a normalised EDS). The underlying
mathematics is the classical EDS addition/duplication law (Ward, Shipsey,
Stange). The relevant fact for this assessment is purely a mathlib-provenance
fact: **the exact lemma is already in mathlib**, contributed by the same author
whose copyright header the project file carries.

---

## Generality analysis (Phase 4)

Moot for the verdict (mathlib has it), but recorded: the lemma is stated over
an arbitrary `[CommRing R]` — the maximal sensible generality for an EDS
defining-equation (EDS theory lives over commutative rings; nothing weaker
supports the polynomial identities). Mathlib's copy uses the **same** typeclass.

- Generality verdict (4b): MAXIMALLY GENERAL (and identical to mathlib's form).
- Modern-idiom check (4c): no modernisation available/needed — mathlib's own
  formulation *is* the form, and it is already `[CommRing R]`-general.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equality or
typeclass-search path).

---

## Mathlib search (Phase 5)

### Mathlib search-status: `complEDS'_odd`

- [A] Lean-Finder      — not needed; direct source hit found
- [B] Loogle           — not needed; direct source hit found
- [C] LeanSearch       — not needed; direct source hit found
- [D] **Grep mathlib src** — `grep -rn "complEDS'_odd"` over `.lake/packages/mathlib/` → **HIT** at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:415`
- [E] Name pattern     — `complEDS`, `complEDS'`, `complEDS₂` all present in the same mathlib file (`complEDS'` def at :392, `complEDS'_even` at :410, `complEDS'_odd` at :415, `complEDS` at :427, `complEDS_odd` at :458)

**Searched for both** the project's current form and the literature-standard
form — they coincide, and mathlib has it verbatim.

**Side-by-side (project vs mathlib):**

Project `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1551`:
```lean
lemma complEDS'_odd (m : ℕ) : complEDS' b c d k (2 * (m + 1) + 1) =
    complEDS' b c d k (m + 1) ^ 2
        * normEDS b c d ((↑(m + 2) : ℤ) * k + 1) * normEDS b c d ((↑(m + 2) : ℤ) * k - 1) -
      complEDS' b c d k (m + 2) ^ 2
          * normEDS b c d ((↑(m + 1) : ℤ) * k + 1) * normEDS b c d ((↑(m + 1) : ℤ) * k - 1) := by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl, complEDS', dif_neg m.not_even_two_mul_add_one]
  simpa only [Nat.mul_add_div two_pos] using by rfl
```

Mathlib `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:415`:
```lean
lemma complEDS'_odd (m : ℕ) : complEDS' b c d k (2 * (m + 1) + 1) =
    complEDS' b c d k (m + 1) ^ 2
        * normEDS b c d ((m + 2) * k + 1) * normEDS b c d ((m + 2) * k - 1) -
      complEDS' b c d k (m + 2) ^ 2
          * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) := by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl, complEDS', dif_neg m.not_even_two_mul_add_one]
  simp [Nat.mul_add_div two_pos, add_assoc]
```

The statements are **identical**: project `(↑(m + 2) : ℤ) * k` vs mathlib
`(m + 2) * k` differ only in explicit-vs-elaborated cast notation and elaborate
to the same term (the `* k` with `k : ℤ` forces the `ℕ → ℤ` coercion either way).
The same `def complEDS'`, the same surrounding `section ComplEDS`, the same
namespace (none). Only the closing proof tactic differs cosmetically
(`simpa … using by rfl` vs `simp […]`) — irrelevant to the statement.

Both files carry the identical header `Copyright (c) 2024 David Kurniadi
Angdinata … Authors: David Kurniadi Angdinata`. This is the project's **fork**
of the upstream mathlib EDS file (per the task's project context: NagellLutz
forks `Mathlib.NumberTheory.EllipticDivisibilitySequence`).

mathlib pin: `d90090f` (2026-06-08). `complEDS'_odd` is present at that pin.

**Concluded: found in mathlib as `complEDS'_odd`; identical form.**

---

## Composition check (Phase 6)

### Call sites — `complEDS'_odd`

Internal use count (NagellLutz, excluding the declaring line): 2
- `EllipticDivisibilitySequence.lean:1604` — `simpa only [complEDS_ofNat] using complEDS'_odd ..` (used to prove `complEDS_odd`, the ℤ-indexed version)
- `EllipticDivisibilitySequence.lean:1658` — `simp only [complEDS'_even, complEDS'_odd, map_normEDS, …]` (used in `map_complEDS'`)

External-to-project copies (also forks, not genuine external consumers):
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:771` — uses `complEDS'_odd` (a *second* fork of the same mathlib file under HasseWeil)
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:1442/1493/1565` — `…Original.lean` is yet another copy of the same file (re-declares `complEDS'_odd` itself)

Every "call site" is inside a *fork of the same mathlib file*. There is no
consumer that mathlib's own `complEDS'_odd` would not serve identically — these
are precisely the duplicated-track copies the task flagged.

Composition: n/a — no composition needed; mathlib has the lemma verbatim.

**Conclusion: NOT-COMPOSABLE-needed — mathlib has the exact decl (NO-mathlib-has-it dominates).**

---

## Verdict: `complEDS'_odd`

**Category: NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): the relevant fact is provenance — the lemma is an internal defining-equation of mathlib's `complEDS'`, and the underlying math is the classical EDS addition law (Ward/Shipsey/Stange).
- Generality analysis (Phase 4): MAXIMALLY GENERAL (`[CommRing R]`), identical to mathlib's typeclass; no modernisation available.
- Mathlib search (Phase 5): **found in mathlib as `complEDS'_odd`** at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:415`; identical statement, same author, same proof skeleton.
- Composition check (Phase 6): all 2 internal call sites (plus the HasseWeil/Original fork copies) are inside duplicated forks of the same mathlib file.

**Rationale.**

`complEDS'_odd` is not a candidate for mathlib because it is *already in mathlib*,
verbatim. The NagellLutz file `EllipticDivisibilitySequence.lean` is a fork of
upstream `Mathlib.NumberTheory.EllipticDivisibilitySequence` (both carry the
identical `Copyright (c) 2024 David Kurniadi Angdinata` header), and the entire
`section ComplEDS` block — `def complEDS'`, `complEDS'_zero/_one/_even/_odd`,
`def complEDS`, the `complEDS_*` lemmas, and the recursors — is a line-for-line
copy of the mathlib block. The statement of `complEDS'_odd` matches mathlib's at
`:415` exactly: the only textual difference (`(↑(m + 2) : ℤ) * k` vs `(m + 2) * k`)
is explicit-vs-implicit cast notation that elaborates to the same term, and the
only proof difference is a cosmetic choice of closing tactic. Mathlib's pin in
this repo (`d90090f`) contains the lemma, so it is directly available by `import
Mathlib.NumberTheory.EllipticDivisibilitySequence`.

**WHY not (refactor-actionable).**
Mathlib already has it: `complEDS'_odd` at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:415`,
same qualified name, same `section ComplEDS` (no namespace), same `[CommRing R]`
generality. The project's version is redundant.

Existing mathlib decl:        `complEDS'_odd`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:415`
Our form follows in ≤1 line:  it *is* the mathlib lemma — `exact complEDS'_odd ..`
(identical statement; the project copy can be deleted and references resolve to
mathlib's once the fork's local re-declaration is removed).

Call sites in our project (Phase 6.0): 2 within-file (`:1604` in `complEDS_odd`,
`:1658` in `map_complEDS'`), plus fork copies in `HasseWeil/Auxiliary/…:771` and
`…Original.lean` (itself a re-declaration).

Refactor plan (note: this is a whole-fork dedup, larger than one lemma):
1. The dedup unit is the **entire `section ComplEDS` fork** (and indeed the whole
   `EllipticDivisibilitySequence.lean` fork), not `complEDS'_odd` in isolation —
   deleting one lemma from a forked file that re-declares its own `complEDS'`
   would break the file. The correct move is to drop the project's forked
   `complEDS'`/`complEDS` block and `import Mathlib.NumberTheory.EllipticDivisibilitySequence`,
   letting `complEDS'_odd` (and its siblings) resolve to mathlib.
2. After that import switch, the 2 in-file uses (`:1604`, `:1658`) resolve to
   mathlib's `complEDS'_odd` unchanged (same name, same signature).
3. Reconcile `EllipticDivisibilitySequenceOriginal.lean` and the HasseWeil
   `Auxiliary/EllipticDivisibilitySequence.lean` the same way (both are forks of
   the same upstream file) — a project-level consolidation task, not a single-PR
   item.
4. Because the project forks mathlib *deliberately* (it also modifies adjacent
   EDS/DivisionPolynomial machinery), confirm whether this specific block was
   forked only for co-location or because something *downstream* in NagellLutz
   needs a modified `complEDS'`. If the block is unmodified vs mathlib (it is,
   for `complEDS'_odd`), the fork of *this* block is pure duplication and should
   be replaced by the mathlib import.

Next action: do **not** open a mathlib PR. Treat as an AINTLIB dedup/cleanup
ticket: replace the forked `section ComplEDS` (ideally the whole forked EDS
file) with `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and let
`complEDS'_odd` resolve upstream. (`/cleanup` cross-project dedup lane.)
