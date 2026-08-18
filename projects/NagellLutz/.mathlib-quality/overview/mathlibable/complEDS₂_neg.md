# /mathlibable report — `complEDS₂_neg`

**Verdict: `NO-mathlib-has-it`** — this lemma is a byte-for-byte fork of an existing mathlib lemma.

---

## Baseline (Phase 0)

- lake build:               not re-run (local build stale per task brief); decl read directly from source
- decl `complEDS₂_neg`:      ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:870`
- qualified name:           `complEDS₂_neg` (top-level — inside `section PreNormEDS` with `open EllSequence`; **no enclosing `namespace`**, so the base name *is* the qualified name)
- kind:                     `lemma` (carries `@[simp]`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines EDS (`IsEllSequence`/`IsDivSequence`/`IsEllDivSequence`), the auxiliary `preNormEDS'`/`preNormEDS`, the 2-complement `complEDS₂`, `normEDS`, and the general complement `complEDS'`/`complEDS`. The file header copyright is "Copyright (c) 2024 David Kurniadi Angdinata" — the **same author and header as the mathlib file**, confirming it is a fork.

---

## Statement (Phase 1)

`complEDS₂_neg` states that the **2-complement sequence `complEDS₂` of a normalised EDS is an even function of its integer index**:

> For a commutative ring `R`, parameters `b c d : R`, and any `k : ℤ`,
> `complEDS₂ b c d (-k) = complEDS₂ b c d k`.

Here `complEDS₂ b c d k = (preNormEDS (b⁴) c d (k-1)² · preNormEDS (b⁴) c d (k+2) − preNormEDS (b⁴) c d (k-2) · preNormEDS (b⁴) c d (k+1)²) · (if Even k then 1 else b)` is the factor `Wᶜ₂(k)` witnessing `W(k) ∣ W(2k)` for the normalised EDS `W = normEDS b c d`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (commutative ring; the file's standing assumption).
- `(b c d : R)` — the three defining parameters of the normalised EDS.

Hypotheses: none (universally quantified over `k : ℤ`).

Conclusion (math): the 2-complement sequence is even, `Wᶜ₂(−k) = Wᶜ₂(k)`.
Conclusion (Lean): `complEDS₂ b c d (-k) = complEDS₂ b c d k`.

Proof body (identical in both copies):
```lean
simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
ring1
```

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line structural symmetry lemma about an auxiliary sequence (`complEDS₂`); not a named theorem, not a new structure, not a `## Main results` entry. (Width is moot here — see Phase 5: the decl already exists verbatim in mathlib, which short-circuits the literature sweep.)

## One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`.

---

## Literature search (Phase 3)

**Short-circuited — and legitimately so.** Phase 5 establishes that this declaration is a **byte-for-byte copy of an existing mathlib lemma** (`Mathlib.NumberTheory.EllipticDivisibilitySequence`, line 272), same author, same header, same proof. The `/mathlibable` question — *"should mathlib have this?"* — is therefore already answered by mathlib itself: **it does.** A literature sweep to establish the "standard form" of `Wᶜ₂(−k) = Wᶜ₂(k)` adds nothing to a verdict that is settled by an exact identity match in the mathlib tree. For completeness:

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | mathlib source (decisive)        | grep `complEDS₂_neg` in `.lake/packages/mathlib/`                       | YES  | identical lemma at `…/EllipticDivisibilitySequence.lean:272` | exact statement + exact proof + `@[simp]` |
|  2 | Local references                 | task brief states project forks `Mathlib.NumberTheory.EllipticDivisibilitySequence` | YES | fork confirmed | CLAUDE.md + module header (Angdinata, 2024) match mathlib |
|  3 | Literature (Ward, EDS memoir)    | n/a                                                                    | n/a  | —                                                     | not needed: the decl is already in mathlib, so the "is it standard / what generality" question is settled upstream |

The defining concept (elliptic divisibility sequence, Ward's *Memoir on Elliptic Divisibility Sequences*) is already mathlib's cited reference for this very file; `complEDS₂` is mathlib's own auxiliary construction. There is no upstream-able novelty to investigate.

### Literature summary (Phase 3)

Concept identified as: the 2-complement (the cofactor `Wᶜ₂` in `W(k)·Wᶜ₂(k) = W(2k)`) of mathlib's normalised EDS — a mathlib-internal construction, not a named classical object.
Most general standard form: identical to the mathlib form; `R` an arbitrary `CommRing`. The mathlib lemma is already at full generality.
Disagreement with the literature / mathlib: **none** — the fork copy and the mathlib lemma are character-for-character equal.

---

## Generality analysis (Phase 4)

Moot — the declaration is literally the mathlib declaration. There is nothing to weaken: the existing mathlib `complEDS₂_neg` is already stated over an arbitrary `CommRing R` with bare parameters `b c d : R` and an unrestricted `k : ℤ`. No typeclass is stronger than necessary; the index is already `ℤ`.

### Generality verdict (Phase 4b)
The current form is: **MAXIMALLY GENERAL** (it equals mathlib's form, which is itself maximal here).
Weakening opportunities: 0.

### Modern-idiom check (Phase 4c)
Not applicable — this is not a candidate for upstreaming (mathlib already has the identical lemma). No modern-idiom reformulation question arises; were one to, it would be a `/generalise` task against the *mathlib* decl, not this fork copy.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

## Mathlib search (Phase 5)

### Mathlib search-status: `complEDS₂_neg`

[A] Lean-Finder       not needed       n/a — direct source match already decisive (below)
[B] Loogle            not needed       n/a — direct source match already decisive
[C] LeanSearch        not needed       n/a — direct source match already decisive
[D] Grep mathlib src  `complEDS₂_neg`  **HIT** — `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:272`
[E] Name pattern      `complEDS₂`      HIT — the entire `complEDS₂` API block (`complEDS₂`, `_zero`/`_one`/`_two`/`_three`/`_four`, `_neg`, `preNormEDS_mul_complEDS₂`) is present in mathlib at lines 246–279, matching the fork's lines 844–877

**Decisive evidence.** A direct `diff` of the fork lemma (lines 870–872) against the mathlib lemma (lines 272–274) produces **no output — they are byte-for-byte identical**, including the `@[simp]` attribute, the signature, and the two-line proof (`simp_rw […]; ring1`). The supporting `def complEDS₂` (fork 844–846 vs mathlib 246–248) is likewise identical. The mathlib lemma sits in the same `section PreNormEDS` with the same surrounding lemmas, so even the qualified name agrees (top-level `complEDS₂_neg`).

Concluded: **found in mathlib as `complEDS₂_neg`; identical form** (same name, same statement, same proof, same generality — a verbatim fork).

---

## Composition check (Phase 6)

### Call sites — `complEDS₂_neg`

Internal use count (this NagellLutz project, excluding the declaring file): **0** direct references to `complEDS₂_neg` were found. (The `complEDS₂` *definition* and sibling lemmas such as `normEDS_mul_complEDS₂` are used across the repo — e.g. `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean` uses `complEDS₂`, `normEDS_mul_complEDS₂`, `map_complEDS₂` — but those resolve to **mathlib's** copies in HasseWeil; the NagellLutz fork file is a self-contained re-derivation track. The HasseWeil docstrings even cite "mathlib's `preNormEDS_mul_complEDS₂`".)

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none in NagellLutz outside the declaring file) | `complEDS₂_neg` itself is not invoked elsewhere in the project; it exists as part of the copied API surface |

Inline-derivation grep: the whole `complEDS₂` block (including `_neg`) is re-derived inline in `EllipticDivisibilitySequenceOriginal.lean` (the project keeps an "Original" copy at lines 798+) — another fork artifact, not an independent need.

### Composition check (Phase 6)
Not applicable in the usual sense — there is nothing to compose *toward mathlib*, because mathlib already contains the exact lemma. (For the record, a one-line proof does exist — it is mathlib's own `simp_rw […]; ring1` — but the point is irrelevant: we would not add a composition, we would simply use the lemma that is already upstream.)

Conclusion: **N/A — mathlib has the identical declaration; no composition or new lemma is in question.**

---

## Verdict: `complEDS₂_neg`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the concept is mathlib's own internal 2-complement construction (Ward's EDS memoir is already mathlib's cited reference for this file); no upstream novelty.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it *is* the mathlib form (arbitrary `CommRing`, bare `b c d`, unrestricted `k : ℤ`); 0 weakenings.
- Mathlib search (Phase 5): **found in mathlib as `complEDS₂_neg`; identical form** — a byte-for-byte `diff` against `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:272` is empty.
- Composition check (Phase 6): N/A — nothing to compose; mathlib already has the exact lemma. 0 internal NagellLutz call sites of the fork copy.

**Rationale:**

This project (`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`) is an explicit **fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence` — same author (David Kurniadi Angdinata), same copyright header, same section layout. The lemma `complEDS₂_neg` at line 870, together with its parent `def complEDS₂` and all sibling lemmas, was copied **verbatim** from mathlib. A direct line-diff of the lemma against mathlib's line 272 yields no differences whatsoever: identical `@[simp]` attribute, identical signature `(k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k`, identical two-line proof `simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]; ring1`. The `/mathlibable` question "should mathlib have this?" is answered by mathlib itself: it already does. There is no statement to upstream, no generalisation to propose, and no composition to inline — the only correct action is to **stop maintaining the local copy and depend on the mathlib lemma**.

**WHY not (refactor-actionable):**

Mathlib already has the identical lemma; the fork copy is pure duplication of upstream code. Per AINTLIB's CLAUDE.md the cardinal rule is "reuse, don't duplicate" — re-proving something already in mathlib is the one cardinal sin. This entire forked `complEDS₂` API block exists only because the surrounding NagellLutz file forks mathlib's EDS module.

- Existing mathlib decl:        `complEDS₂_neg`
- Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:272`
- Our form follows in 0 lines — it is the same declaration:
  ```lean
  -- mathlib already provides, verbatim:
  @[simp] lemma complEDS₂_neg (k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k := by
    simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
    ring1
  ```
- Call sites of the **fork copy** in NagellLutz (Phase 6.0): **0** (the lemma is part of a copied API surface, not independently consumed).

**Refactor plan.** This single lemma should not be migrated in isolation — it is one line of a wholesale fork. The correct remediation is the file-level one the project context already anticipates: delete the forked `complEDS₂` block (`def complEDS₂` + `complEDS₂_{zero,one,two,three,four,neg}` + `preNormEDS_mul_complEDS₂`, fork lines 844–877) and have `EllipticDivisibilitySequence.lean` `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and reuse the upstream declarations, exactly as the `HasseWeil` project already does (it consumes mathlib's `complEDS₂` / `normEDS_mul_complEDS₂` / `map_complEDS₂` directly). Because the fork tracks a *specific* mathlib pin and may carry General*/PID* divergences elsewhere in the file, the deletion is a coordinator-level dedup decision over the whole forked module, not a per-lemma edit — but the verdict for *this declaration* is unambiguous: it is redundant with mathlib and contributes nothing new.

**Next action:** delete the forked `complEDS₂_neg` (and its sibling `complEDS₂` block) from `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`; depend on `complEDS₂_neg` from `Mathlib.NumberTheory.EllipticDivisibilitySequence` instead. File this as part of the project-wide "de-fork the EDS module" cleanup rather than a standalone change.

---

## Next step

Delete `complEDS₂_neg` (and the surrounding verbatim-forked `complEDS₂` API block) from the NagellLutz fork file and reuse the identical mathlib declaration in `Mathlib.NumberTheory.EllipticDivisibilitySequence`; track it under the module-level de-fork cleanup.
