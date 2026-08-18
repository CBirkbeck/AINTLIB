# /mathlibable report — `preNormEDS_two`

> **Verdict: `NO-mathlib-has-it`** — this declaration is a byte-for-byte fork of
> an existing mathlib lemma. Name, statement, proof, `@[simp]` attribute,
> surrounding section, and original author are all identical to
> `preNormEDS_two` at
> `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:194`.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task note); verdict reasoned from source — does not depend on elaboration.
- decl `preNormEDS_two`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:792`
- qualified name:           `preNormEDS_two` (TOP-LEVEL — no namespace prefix; the nearest namespace `IsEllSequence` closes at line 702, and `section PreNormEDS` (704–879) opens **no** namespace, only `variable (b c d : R)`)
- kind:                     `lemma` (carrying `@[simp]`)
- has sorry:                no
- module docstring summary: Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms; a near-verbatim **fork of mathlib's** `Mathlib.NumberTheory.EllipticDivisibilitySequence` extended with a `complEDS₂` 2-complement track.

**Exact source (project, lines 791–793):**
```lean
@[simp]
lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]
```

---

### Statement (Phase 1)

`preNormEDS_two` states that the auxiliary pre-normalised elliptic divisibility
sequence `preNormEDS b c d : ℤ → R` takes the value **1 at index 2**, i.e.
`W(2) = 1`. This is one of the five defining initial-value lemmas of the
sequence (`W(0)=0`, `W(1)=1`, `W(2)=1`, `W(3)=c`, `W(4)=d`); it is the
unfolding of `preNormEDS b c d 2 = Int.sign 2 * preNormEDS' b c d (Int.natAbs 2) = 1 · 1 = 1`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three EDS parameters (section `variable`s).

Hypotheses: none.

Conclusion (math): `W(2) = 1` for the pre-normalised EDS with parameters `b, c, d`.
Conclusion (Lean): `preNormEDS b c d 2 = 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A zero-hypothesis initial-value (`@[simp]`-normal-form) lemma about a
specific index of a defined sequence — a helper, not a named theorem or a new
structure.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (Body is a single `simp`
call, but the one-liner heuristic targets definitions, not lemmas.)

---

### Decisive finding (short-circuit justification)

The `/mathlibable` workflow's full literature → generality → composition
machinery exists to decide *whether mathlib should have a declaration it does
not yet have*. That question is **already answered here**: mathlib has this
exact declaration. A `diff` of the two three-line declarations reports them
**IDENTICAL**:

```
$ diff <mathlib:193-195> <project:791-793>   →   IDENTICAL
```

Both files carry the same header `Authors: David Kurniadi Angdinata` and the
same `section PreNormEDS` / `variable (b c d : R)` scaffolding; the project file
is a direct fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(this is exactly the "this project FORKS parts of mathlib" case the ticket
flagged). When the upstream and local declarations agree in name, statement,
proof, attribute, namespace, and author, no search can move the verdict off
`NO-mathlib-has-it`; the literature/generality/modern-idiom/composition phases
below are recorded for completeness but cannot change the outcome.

---

### Literature search (Phase 3) — recorded, non-dispositive

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|---------------|-------|
| 1 | mathlib source (primary) | `grep preNormEDS_two .lake/.../mathlib/` | **yes** | `preNormEDS b c d 2 = 1` | `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:194` — identical |
| 2 | Literature (concept) | Ward, "Memoir on elliptic divisibility sequences" (Amer. J. Math. 70 (1948)) | yes | EDS normalisation `h_1 = h_2 = 1` | The `W(2)=1` normalisation is part of the classical definition of a *normalised* EDS; not a standalone named result. |
| 3 | WebSearch (general) | "elliptic divisibility sequence" normalisation initial values | yes | `h_0=0, h_1=1, h_2=1` | Standard; a definitional unfolding, never stated as an independent theorem in the literature. |
| 4–10 | nLab / Stacks / nCatLab / MathOverflow / arXiv / ChatGPT MCP | — | n/a | — | Not run / moot: a verbatim mathlib duplicate cannot be re-routed by literature evidence. EDS is a number-theory topic with no categorical/algebraic-geometry-scheme content for nLab/Stacks; the mathlib hit at #1 is dispositive. |

### Literature summary (Phase 3)

Concept identified as: the `W(2) = 1` initial value of a **normalised elliptic
divisibility sequence** (Ward 1948; mathlib's `preNormEDS'`/`preNormEDS`
construction). It is a *definitional unfolding*, not an independently named
literature theorem. The classical literature bundles it into the definition of a
normalised EDS; mathlib factors it out as a `@[simp]` lemma — and the project
copied mathlib verbatim.

---

### Generality analysis (Phase 4) — recorded, non-dispositive

#### 4a/4b — Generality verdict
The current form is **MAXIMALLY GENERAL** for what it states: `[CommRing R]` with
free parameters `b c d : R` is exactly mathlib's own generality (identical
signature). There is nothing to weaken — it already matches the upstream form
character-for-character. Weakening opportunities: **0**.

#### 4c — Modern-idiom check
Modern idiom available: **no**. This is a finite definitional unfolding
(`Int.sign 2 * preNormEDS' … 2`); there is no topology to filter-ise, no
universal property to introduce, no index to generalise (the index `2` is
intrinsic to the statement). The mathlib form *is* the modern idiom — the
project is downstream of it.

---

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma` (introduces no definitional equality or
typeclass-search path).

---

### Mathlib search (Phase 5)

```
[A] Lean-Finder       n/a (mathlib index): not needed — direct source hit is authoritative
[B] Loogle            preNormEDS _ _ _ 2 = 1  → would resolve to the mathlib lemma
[C] LeanSearch        "preNormEDS at 2 equals one" → mathlib EDS file
[D] Grep mathlib src  `grep -rn preNormEDS_two .lake/.../mathlib/`  → HIT (2 occurrences)
[E] Name pattern      `lemma preNormEDS_two`  → HIT
```

Both the user's current form and the literature-standard form were searched
(they coincide).

**Concluded:** found in mathlib as **`preNormEDS_two`**
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:194`); **identical
form** — same name, same statement, same proof, same `@[simp]` attribute, same
section, same author. Cross-referenced: mathlib itself consumes it at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:211`.

---

### Composition check (Phase 6)

#### 6.0 — Call sites of the project's `preNormEDS_two`

Internal use count (NagellLutz, excluding the declaring file): **1** external
file + 1 same-file use.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1077` | `rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, …]` (same file) |
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:134` | `preNormEDS_two ..` (used as a proof term) |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:746,1026` | the lemma is **also forked verbatim** here, and used; `…Original.lean` is a second copy of the same fork |

These call sites consume the project's **forked** `preNormEDS`, so they resolve
against the local copy today. They are **not** evidence of a needed contribution —
they are evidence the whole `preNormEDS` track is duplicated. Once the fork is
dropped in favour of mathlib's file, every one of these call sites resolves to
mathlib's `preNormEDS_two` unchanged (same name, same arity).

Inline re-derivation grep: the lemma is re-derived in `…Original.lean` (an
additional verbatim fork), reinforcing NO-mathlib-has-it.

#### 6a — Composition
Conclusion: **COMPOSABLE** trivially (the proof *is* one `simp` call) — but
composition is moot: the verdict is NO-mathlib-has-it (exact duplicate), which
strictly dominates NO-composable-from-mathlib.

---

## Verdict: `preNormEDS_two`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): primary mathlib-source hit; the `W(2)=1`
  normalisation is a definitional unfolding (Ward 1948), never an independent
  named theorem.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical signature to the
  mathlib lemma; 0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_two`**
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:194`), identical form
  (`diff` = IDENTICAL).
- Composition check (Phase 6): the 3 project call sites consume the forked copy;
  re-forked again in `…Original.lean`.

**Rationale:**

This declaration is not a candidate for mathlib — mathlib already contains it,
verbatim. The project's `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
is a fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same
Apache header, same author David Kurniadi Angdinata, same `section PreNormEDS`
and `variable (b c d : R)` scaffolding). A direct `diff` of the two
declarations reports them IDENTICAL: same name `preNormEDS_two`, same statement
`preNormEDS b c d 2 = 1`, same proof `by simp [preNormEDS, Int.sign_eq_one_of_pos]`,
same `@[simp]` attribute, same top-level (no-namespace) placement. There is no
weakening to make and no modernisation to apply, because the upstream form *is*
the form. The remaining `/mathlibable` phases were recorded for completeness but
cannot move a verbatim-duplicate verdict.

**WHY not (refactor-actionable):**
Mathlib already has it as `preNormEDS_two` at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:194`. The user's form is
not "follows in ≤1 line" — it is the *same line*. The project carries an entire
duplicated `preNormEDS'`/`preNormEDS` track (in this file **and** again in
`EllipticDivisibilitySequenceOriginal.lean`) that already exists upstream.

Existing mathlib decl: `preNormEDS_two`
Located at:            `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:194`
Our form follows in 0 lines (it is literally the same declaration):
```lean
-- mathlib already provides, identically:
@[simp] lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]
```

Call sites in NagellLutz (from Phase 6.0): 3 live uses
(`EllipticDivisibilitySequence.lean:1077`, `DivisionPolynomial.lean:134`, and the
parallel copies in `EllipticDivisibilitySequenceOriginal.lean:746,1026`).

**Refactor plan (do NOT cleanup-fix this lemma in isolation — it is one symptom
of a whole forked file):**
1. This single lemma is a verbatim duplicate; deleting only it would break the
   local `preNormEDS` it depends on. The correct unit of work is the **entire
   `preNormEDS'`/`preNormEDS` block** in
   `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` (the
   contiguous run including `preNormEDS'`, `preNormEDS`, and all
   `preNormEDS_zero/one/two/three/four/neg/even/odd`, lines ≈706–838) — every
   one of which is forked from mathlib's `EllipticDivisibilitySequence.lean`.
2. Replace that block by `public import Mathlib.NumberTheory.EllipticDivisibilitySequence`
   and `open`ing the relevant scope, **keeping only** the genuinely-new
   `complEDS₂` complement-sequence track (lines 840+) that mathlib lacks.
3. The 3 call sites then resolve to mathlib's `preNormEDS_two` automatically (no
   per-site edit — identical name and arity).
4. Apply the identical removal to the second fork in
   `EllipticDivisibilitySequenceOriginal.lean` (or delete that file if it is a
   stale snapshot).
5. **Before** any of this, diff the *whole* forked file against mathlib's to
   confirm the only project-original content is the `complEDS₂`/`complEDS`
   material (and any altered proofs, e.g. `preNormEDS'_even/odd` use
   `simpa only [...] using by rfl` here vs mathlib's `simp [...]`); preserve
   exactly that delta.

**Next action:** do not contribute `preNormEDS_two`. Treat the duplicated
`preNormEDS` track as a fork-dedup cleanup ticket against mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; keep only the project's
novel `complEDS₂` additions.

---

## Next step

Delete the forked `preNormEDS`/`preNormEDS'` block (and the parallel fork in
`EllipticDivisibilitySequenceOriginal.lean`) from NagellLutz, import
`Mathlib.NumberTheory.EllipticDivisibilitySequence` instead, and keep only the
project-original `complEDS₂` complement-sequence track. No mathlib PR — mathlib
already has `preNormEDS_two` identically.
