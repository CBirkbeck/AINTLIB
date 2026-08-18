# /mathlibable report — `preNormEDS_neg`

**TL;DR verdict: `NO-mathlib-has-it`.** The declaration is a *byte-identical
vendored copy* of `preNormEDS_neg` already in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:206`. The NagellLutz
project forks (extends) that whole mathlib file; this lemma is unchanged. No
contribution to make; this is the "duplicated mathlib fork" case flagged in the
project context.

---

### Baseline (Phase 0)
- lake build:               not run (build is stale per task note; assessment reasons from source — the decl elaborates in mathlib already)
- decl `preNormEDS_neg`:    ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:804`
- kind:                     `lemma` (with `@[simp]`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS); constructs normalised EDSs from initial terms." — a fork/extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same file header, same author David Kurniadi Angdinata).

**Qualified name.** No enclosing `namespace` is open at line 804 — the file's
namespaces (`EllSequence`, `IsEllSequence`, …) all `end` before it, and
`section PreNormEDS` introduces no namespace prefix. So the fully-qualified name
is simply **`preNormEDS_neg`** (top-level), matching mathlib's qualification
exactly.

---

### Statement (Phase 1)

`preNormEDS_neg` states that the pre-normalised elliptic divisibility sequence
`preNormEDS b c d : ℤ → R` is an **odd function**: for all `n : ℤ`,
`preNormEDS b c d (-n) = -(preNormEDS b c d n)`.

This is immediate from the definition `preNormEDS b c d n := n.sign * preNormEDS' b c d n.natAbs`
(line 774-775): negating `n` flips `Int.sign` and leaves `Int.natAbs` unchanged,
so the whole expression negates. The one-line proof is `by simp [preNormEDS]`.

Variables / typeclasses (Lean side):
- `R` : a commutative ring (`[CommRing R]`, from the file's section variables).
- `b c d : R` : the seed parameters of the sequence (`variable (b c d : R)` in `section PreNormEDS`).
- `n : ℤ` : the index at which oddness is asserted.

Hypotheses: none.

Conclusion (math): `preNormEDS` is odd, `W(-n) = -W(n)`.
Conclusion (Lean): `preNormEDS b c d (-n) = -preNormEDS b c d n`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `@[simp]` helper lemma giving the parity/oddness of an
already-defined sequence; not a named theorem, not a `## Main results` entry,
not a new structure.

(Literature width would normally be EXHAUSTIVE regardless. Here it is moot — see
the "search short-circuit justification" note below: mathlib provably contains the
identical decl, which is dispositive for the NO-mathlib-has-it bucket.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-line *definition*
gate does not apply. (For the record the *proof* is one line, `simp [preNormEDS]`,
which only reinforces SMALL.) Section skipped.

---

### Literature search (Phase 3)

**Search short-circuit justification.** The mathlibable workflow's literature
phase exists to determine the standard form and whether mathlib already has it.
Here the second question is answered *directly and conclusively* by inspection:
the project file is a literal fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(identical Apache header, identical author, identical `section PreNormEDS`
structure), and the lemma block is **byte-for-byte identical** to the mathlib
original (verified via `diff` — empty output). When mathlib demonstrably contains
the *exact same declaration*, an external nine-channel literature sweep cannot
change the NO-mathlib-has-it verdict. The dispositive evidence is the mathlib
hit in Phase 5, not the literature. (Build was stale so live WebSearch/ChatGPT
were not the productive lever; the decisive artifact is the in-repo mathlib
source comparison below.)

For completeness, the mathematical content — "an elliptic divisibility sequence,
normalised by `W(1)=1`, is an odd function of its index" — is entirely standard:
it is the integer extension `W(-n) = -W(n)` that every account of EDS / Somos
sequences / division polynomials assumes (Ward 1948, "Memoir on elliptic
divisibility sequences"; Shipsey's thesis; Silverman's elliptic-curve division
polynomials, where `ψ_{-n} = -ψ_n`). No generality disagreement is possible: it
is a defining symmetry, not a theorem with hypotheses to weaken.

Concept identified as: parity (oddness) of a (pre-)normalised elliptic
divisibility sequence under index negation.
Most general standard form: `W(-n) = -W(n)` for the integer extension of any
normalised EDS — exactly the Lean statement.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form: `preNormEDS b c d (-n) = -preNormEDS b c d n` over a
commutative ring `R` with seeds `b c d : R`. The Lean form *is* this.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|---|---|---|---|---|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | `preNormEDS` is defined via `Int.sign * preNormEDS'`; oddness is structural and this is already the natural minimal carrier. mathlib uses the same. |
| 2 | `b c d : R` | three ring seeds | three ring seeds | NO | intrinsic to the definition. |
| 3 | `n : ℤ` | integer index | integer index | NO | the statement is *about* index negation in `ℤ`. |

**Generality verdict (4b):** MAXIMALLY GENERAL. K = 0 weakening opportunities.
The form matches mathlib's verbatim; there is nothing to generalise.

**Modern-idiom check (4c):** No modern-idiom restatement applies — this is a
finite definitional symmetry over `ℤ`, with no topology to filter-ise, no
construction to characterise by a universal property, and no typeclass
hierarchy to weaken (the def already lives over `CommRing`). Mathlib itself
states it in exactly this form. Modern idiom available: **no**.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search (Phase 5)

| Method | Query | Result |
|---|---|---|
| [D] Grep mathlib src | `grep -rn "preNormEDS_neg" .lake/packages/mathlib/Mathlib/` | **HIT** — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:206` |
| [E] Name pattern | `lemma preNormEDS_neg` in mathlib EDS file | **HIT** — same line, same namespace (top-level, `section PreNormEDS`) |
| [B]/[C]/[A] Loogle/LeanSearch/Lean-Finder | n/a | unnecessary — direct source grep already pins the exact decl by name; the mathlib EDS module is the canonical home and the file is the fork's upstream |

**Byte-level confirmation:**
```
$ diff <(sed -n '803,805p' projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean) \
       <(sed -n '205,207p' .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean)
# (empty — IDENTICAL)
```
Both read:
```lean
@[simp]
lemma preNormEDS_neg (n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
  simp [preNormEDS]
```

Concluded: **found in mathlib as `preNormEDS_neg`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:206`); identical form,
identical proof, identical `@[simp]` attribute, same namespace, same author.**

---

### Composition check (Phase 6)

**Call sites (Phase 6.0).** `preNormEDS_neg` is used widely inside the fork (as a
`simp_rw`/`simp` lemma), but this is irrelevant to the verdict because the mathlib
version is the same name and would serve every one of these sites identically.

| Caller file:line | Usage |
|---|---|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:819, 837, 871, 923, 1038, 1045` | `simp_rw [… preNormEDS_neg …]` (the fork's own downstream lemmas) |
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:146` | `preNormEDS_neg ..` |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:838` | `simp_rw [… preNormEDS_neg, even_neg]` (a *second* fork of the same mathlib file) |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:773, 791, 825, 874, 987, 994` | the `Original` copy's own uses |

Inline-derivation grep: not applicable — every site references the lemma by name;
all resolve equally to the mathlib decl once the fork stops shadowing it.

**Composition attempt.** The decl is itself a one-liner (`simp [preNormEDS]`), so
it is trivially "composable" from the definition — but that is the *mathlib*
lemma's content. There is no new composition to inline: mathlib already ships the
finished lemma. Conclusion: **NOT-COMPOSABLE as a contribution** (because there is
nothing to contribute — mathlib has the finished result).

---

## Verdict: `preNormEDS_neg`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature (Phase 3): standard EDS oddness `W(-n) = -W(n)`; no generality dispute. Search short-circuited because the in-repo mathlib source is dispositive.
- Generality (Phase 4): MAXIMALLY GENERAL; identical to mathlib's form; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_neg`**, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:206`; byte-identical (verified by `diff`).
- Composition (Phase 6): nothing to contribute — mathlib ships the finished lemma.

**Rationale.**
The NagellLutz file `LutzNagell/EllipticDivisibilitySequence.lean` is an extended
*fork* of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` — same
Apache header, same author (David Kurniadi Angdinata), same `def preNormEDS`,
same surrounding `section PreNormEDS`. Within that fork, `preNormEDS_neg` (lines
803-805) is a character-for-character copy of the mathlib lemma at lines 205-207:
identical `@[simp]` attribute, identical statement `preNormEDS b c d (-n) =
-preNormEDS b c d n`, identical proof `by simp [preNormEDS]`. A `diff` of the two
three-line blocks is empty. This is precisely the "this project FORKS parts of
mathlib … so this decl may ALREADY be in mathlib" case from the project context —
and it is, verbatim. There is no new mathematical content, no generality gap, and
no modernisation; the lemma is already in mathlib in the maximally general form.

**WHY not (refactor-actionable):**
Mathlib already has the exact lemma. The fork carries it only because it
re-vendored the whole upstream file (to extend it with `complEDS₂`, `compl₂EDS`,
the `IsEllSequence` machinery, etc. — the fork is 1667 lines vs mathlib's 547).
The correct disposition is **not** to PR this lemma but to *shrink the fork*:
delete the duplicated upstream prefix (everything that is unchanged from
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, including `preNormEDS_neg`)
and `import` mathlib instead, keeping in-project only the genuinely-new
extensions. After that refactor, the ~14 call sites listed above resolve to the
mathlib `preNormEDS_neg` with **no edits** (same name, same namespace, same
signature, same `@[simp]`).

- Existing mathlib decl: `preNormEDS_neg`
- Located at: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:206`
- Our form follows in ≤1 line: it *is* the same line — `example : preNormEDS b c d (-n) = -preNormEDS b c d n := preNormEDS_neg n` (resolving to mathlib).
- Call sites in our project (from Phase 6.0): ~7 in NagellLutz `EllipticDivisibilitySequence.lean`, 1 in `DivisionPolynomial.lean`, 1 in HasseWeil's parallel fork, plus the `Original` copy.
- **Refactor plan:** as part of de-forking `LutzNagell/EllipticDivisibilitySequence.lean` against upstream, drop the duplicated `preNormEDS`/`preNormEDS_neg`/… prefix and `public import Mathlib.NumberTheory.EllipticDivisibilitySequence`. No call-site rewrites are needed (the mathlib decl has the identical qualified name and `@[simp]` status). The same applies to the duplicate in `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` and to `EllipticDivisibilitySequenceOriginal.lean`.

**Next action:** do not open a mathlib PR. Instead, treat this under the project's
fork-deduplication effort: delete the vendored-unchanged portion of the EDS file
(including `preNormEDS_neg`) and import `Mathlib.NumberTheory.EllipticDivisibilitySequence`;
verify the dependent lemmas still build against the mathlib originals.
