# /mathlibable report — `normEDS_two`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences).

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task; reasoned from source)
- decl `normEDS_two`:       ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:910`
- qualified name:           **`normEDS_two`** (top-level — no enclosing `namespace`; line 881 is a bare `section NormEDS`; the prior `EllSequence` / `IsEllSequence` / `PreNormEDS` namespaces are all closed by line 879)
- kind:                     `lemma` (`@[simp]`)
- has sorry:                no
- module docstring summary: Forked copy of mathlib's elliptic-divisibility-sequence development (`EllSequence`, `preNormEDS`, `normEDS`, …) for the Nagell–Lutz project, with extra `General*`/`PID*`/complement tracks.

### Statement (Phase 1)

`normEDS_two` states that the canonical normalised elliptic divisibility sequence
`W = normEDS b c d : ℤ → R` takes the value `W(2) = b`. Here `normEDS b c d n :=
preNormEDS (b^4) c d n * (if Even n then b else 1)`, the standard normalised EDS of
Ward with initial data `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d·b`. The lemma is the
`n = 2` evaluation, used everywhere as a `simp`/`rw` rewrite.

- Variables (Lean): `{R} [CommRing R]`, `(b c d : R)`.
- Hypotheses: none.
- Conclusion (math): `W(2) = b`.
- Conclusion (Lean): `normEDS b c d 2 = b`.

Proof body (project): `by simp [normEDS]` — identical to mathlib's.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A one-step evaluation lemma of a defined sequence at `n = 2`; a `@[simp]`
helper, not a named theorem or main result.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check is n/a.
(Note for completeness: the underlying `def normEDS` is a one-liner, but it is **not**
the declaration under assessment, and it too already lives in mathlib.)

### Literature search (Phase 3)

This is a duplicate-detection case: the declaration is a near-byte-for-byte fork of
an existing mathlib lemma (confirmed in Phase 5). Per the verdict gate, when Phase 5
returns "found in mathlib … identical form", the bucket is fixed at NO-mathlib-has-it
and the literature/generality/composition phases are informational only. A brief
literature anchor is recorded; the exhaustive nine-channel sweep is not the
load-bearing artifact here (the mathlib hit is).

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|---------------|-------|
| 1 | Knowledge (Ward EDS) | "normalised elliptic divisibility sequence initial values" | yes | EDS `W` with `W(1)=1`, `W(2),W(3),W(4)` free, satisfying `W(m+n)W(m−n) = W(m+1)W(m−1)W(n)² − W(n+1)W(n−1)W(m)²` | Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948). `normEDS b c d` is exactly this with `(b,c,d) = (W(2),W(3),W(4)/W(2))`. |
| 2 | Mathlib source (def + docstring) | `def normEDS` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` | yes | same | Mathlib's own docstring: "The canonical example of a normalised EDS `W : ℤ → R`, with `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d*b`." Word-for-word the project's docstring. |
| 3 | nLab / Stacks / nCatLab / MathOverflow / arXiv | — | n/a | — | Not load-bearing: the object and the lemma are already in mathlib verbatim, so the standard-form question is settled by the mathlib hit. EDS are number-theoretic recurrences (not categorical / not algebraic-geometry-scheme content), so these channels add nothing beyond Ward's definition. |

### Literature summary (Phase 3)

Concept identified as: the **normalised elliptic divisibility sequence** (Ward 1948),
mathlib's `normEDS`. `normEDS_two` is its value at 2.
Sources agree on the standard form: yes — and mathlib already encodes precisely this
form (it is the source the project forked).
Most general standard form: `normEDS_two` over any `CommRing R` — which is exactly the
mathlib statement. No more-general ambient structure applies (the index is fixed at the
literal `2`; `R` is already a bare commutative ring).
Disagreement with the literature: none.

### Generality analysis (Phase 4)

| # | Parameter / hyp | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|-----------------|-------------------|---------------------|--------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | `normEDS` is defined over `CommRing`; mathlib uses the same. Already maximal. |
| 2 | `(b c d : R)` | ring elements | ring elements | NO | The defining data of the sequence; cannot be weakened. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (and identical to mathlib's).
Weakening opportunities: 0.
Note: generality is moot — the lemma already exists in mathlib in this exact form, so
there is nothing to generalise *into* mathlib.

### Modern-idiom check (Phase 4c)

Modern idiom available: no. The mathlib-idiomatic form *is* the current form (the
project copied it). No filter/typeclass/universal-property/bundled-substructure
reformulation applies to a literal evaluation `W(2) = b`.

### Mathlib search-status: `normEDS_two` (Phase 5)

[A] Lean-Finder       n/a (index not queried — direct grep hit is decisive)
[B] Loogle            n/a (direct grep hit is decisive)
[C] LeanSearch        n/a (direct grep hit is decisive)
[D] Grep mathlib src  `grep -rn "normEDS_two" .lake/packages/mathlib/` → **HIT**
[E] Name pattern      `lemma normEDS_two` → **HIT**

Found in mathlib as **`normEDS_two`** at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:306`:

```lean
@[simp]
lemma normEDS_two : normEDS b c d 2 = b := by
  simp [normEDS]
```

Identity confirmed at three levels:
- **Statement** identical: `normEDS b c d 2 = b`, both top-level (mathlib line 306 is
  also outside any `namespace` — `end PreNormEDS` at line 281 precedes it).
- **Attribute** identical: `@[simp]` on both.
- **Proof** identical: `by simp [normEDS]` on both.
- **Underlying `def normEDS` identical**: `diff` of the two definition bodies
  (project lines 890–891 vs mathlib lines 289–290) reports **no differences** — same
  `preNormEDS (b ^ 4) c d n * if Even n then b else 1`. So the lemma is the *same*
  statement about the *same* object, not a homonym about a different `normEDS`.

Concluded: **found in mathlib as `normEDS_two`; identical form.** (Same name, same
signature, same proof, same parent def. The NagellLutz file is a fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`.)

### Call sites — `normEDS_two` (Phase 6.0)

Internal use count (NagellLutz + sibling HasseWeil fork, excluding the declaring
line): ~14 substantive `rw`/`simp`/`rwa [normEDS_two]` uses; ~20 textual matches incl.
the unrelated `normEDS_two_three_two` / `invarNum_normEDS_two` names.

| Caller (representative) | Usage |
|--------------------------|-------|
| `LutzNagell/EllipticDivisibilitySequence.lean:962, 968, 1330, 1410, 1469` | `rw [normEDS_two]` / `rwa [normEDS_two]` / inside `simp only` |
| `LutzNagell/DivisionPolynomial.lean:339` | `normEDS_two ..` (term-mode application) |
| `LutzNagell/EllipticDivisibilitySequence.lean:1236` | `simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]` |
| `HasseWeil/.../EllipticDivisibilitySequence.lean:590, 597, 711, 749, 918, 952` | analogous (sibling fork of the same file) |

Inline re-derivation grep: not applicable — every consumer already calls
`normEDS_two` by name (it is the canonical rewrite). The "re-derivation" is the
*entire fork*: the project re-declares mathlib's lemma rather than importing it.

Signal: high internal usage → real API. But the API it duplicates is mathlib's own.
The high call count does **not** push toward YES; it just sizes the refactor (the
fork is load-bearing, so dropping it must be done by importing the mathlib module, not
by deletion-in-place).

### Composition check (Phase 6)

Can `normEDS_two` be derived from mathlib in ≤3 calls? Trivially — it **is** a mathlib
lemma. `exact normEDS_two` (the mathlib one) closes the goal in one token. But the
operative conclusion is stronger than "composable": mathlib *has the lemma itself*, so
this is NO-mathlib-has-it, not NO-composable-from-mathlib.

Conclusion: N/A — superseded by the exact mathlib hit (NO-mathlib-has-it dominates).

---

## Verdict: `normEDS_two`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature (Phase 3): Ward's normalised EDS; mathlib's `normEDS` docstring is
  word-for-word the project's.
- Generality (Phase 4): MAXIMALLY GENERAL, identical to mathlib; nothing to generalise.
- Mathlib search (Phase 5): **found in mathlib as `normEDS_two`** at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:306`; identical statement,
  attribute, proof, and parent `def normEDS`.
- Composition (Phase 6): n/a — exact lemma already in mathlib.

**Rationale:**

`normEDS_two` is not a candidate addition to mathlib — it is a **verbatim fork** of an
existing mathlib lemma. The NagellLutz file
`LutzNagell/EllipticDivisibilitySequence.lean` is a copy of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (the project forks this module plus
the `DivisionPolynomial.*` tree, as flagged in the project context). The `def normEDS`
bodies are byte-for-byte equal (`diff` clean), and the lemma matches mathlib's at the
statement, `@[simp]` attribute, and proof. It is heavily used (~14 call sites across
NagellLutz and the sibling HasseWeil fork), which makes it genuine API — but the API it
provides is exactly mathlib's, under the same name and signature.

**WHY not (refactor-actionable):** Mathlib already has this lemma, identically.
- Existing mathlib decl: `normEDS_two`
- Located at: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:306`
- Our form follows in 0 lines — it is the same declaration:
  ```lean
  example {R : Type*} [CommRing R] (b c d : R) : normEDS b c d 2 = b := normEDS_two
  ```
- Call sites in our project (Phase 6.0): ~14 substantive (`rw`/`simp`/term-mode).

**Refactor plan.** This lemma must not be deleted in isolation — it is part of a forked
module that downstream NagellLutz code depends on. The correct action is the **fork
retirement** handled at the file level, not the lemma level:
1. Replace the project's hand-rolled
   `LutzNagell/EllipticDivisibilitySequence.lean` `NormEDS`/`PreNormEDS` content with
   `import Mathlib.NumberTheory.EllipticDivisibilitySequence` (and the matching
   `DivisionPolynomial.*` imports), keeping only the project's genuinely-new
   `General*`/`PID*`/complement additions that are not yet upstream.
2. Once imported, every `normEDS_two` reference (lines 962, 968, 1330, 1410, 1469,
   DivisionPolynomial.lean:339, plus the HasseWeil sibling) resolves to the mathlib
   lemma **with zero edits** — identical name and signature. No argument-order or
   dot-notation changes are needed.
3. The same retirement subsumes the neighbouring forked decls (`normEDS_zero/one/
   three/four`, `normEDS_neg`, `normEDS_dvd_normEDS_two_mul`, etc.), so this entry
   should be actioned as one "drop the EDS fork, import mathlib" cleanup ticket rather
   than per-lemma.

**Next action:** Do not add to mathlib. File a NagellLutz cleanup ticket to retire the
forked `EllipticDivisibilitySequence` (and `DivisionPolynomial.*`) module in favour of
the mathlib originals; the ~14 `normEDS_two` call sites then bind to
`Mathlib.NumberTheory.EllipticDivisibilitySequence.normEDS_two` unchanged.

---

## Next step

File a fork-retirement cleanup ticket (drop the duplicated EDS module, import
`Mathlib.NumberTheory.EllipticDivisibilitySequence`); confirm the ~14 in-project
`normEDS_two` references resolve to the mathlib lemma with no call-site edits.
