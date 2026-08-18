# Mathlibable assessment — `EllSequence.compl_neg`

**Project:** NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic divisibility sequences)
**File:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1107`
**Date:** 2026-06-18
**Verdict:** **NO-mathlib-has-it**

---

## 1. The declaration (verbatim)

Qualified name (verified from source): **`EllSequence.compl_neg`**
(inside `namespace EllSequence`, opened at line 1079, closed at line 1112).

```lean
lemma compl_neg (n : ℤ) : compl W₁ compl₂ m (-n) = -compl W₁ compl₂ m n := by
  simp [compl, Int.sign_neg, Int.natAbs_neg, neg_mul]
```

with the supporting definitions (same namespace, `variable (W₁ compl₂ : ℤ → R) (m : ℤ)`):

```lean
/-- Given two sequences representing `W(m)/W(1)` and `W(2m)/W(m)` respectively,
we construct the sequence representing `W(n*m)/W(m)` in a division-free way. -/
def compl' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => letI k := n / 2 + 1
    if hn : Even n then compl₂ (k * m) * compl' k
      else W₁ ((k + 1) * m + 1) * W₁ ((k + 1) * m - 1) * compl' k ^ 2
      - W₁ (k * m + 1) * W₁ (k * m - 1) * compl' (k + 1) ^ 2

/-- `W(n*m)/W(m)` with `n : ℤ`. -/
def compl (n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs
```

So `compl` is the canonical sign-extension of a `ℕ → R` sequence to `ℤ`, and `compl_neg` is the
odd-symmetry of that extension: `compl(-n) = -compl(n)`. The proof is pure bookkeeping —
`Int.sign (-n) = -Int.sign n` and `(-n).natAbs = n.natAbs`.

Note the parameters `W₁ compl₂ : ℤ → R` are **abstract** sequences; this is the project's
generalised "complement" API, parameterised on `W(m)/W(1)` and `W(2m)/W(m)`. The `normEDS`
specialisation is `complEDS b c d m := compl (normEDS b c d) (compl₂EDS b c d) m` (line 1111).

---

## 2. Mathlib search (five methods)

Pinned mathlib: `rev = d90090f647ca` (`leanprover/lean4:v4.31.0-rc2`), at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

This project **forks** that exact mathlib file (same header/author David Kurniadi Angdinata, same
module docstring). The mathlib file already contains the entire complement-sequence development —
but **specialised to `normEDS`**, not abstracted over `W₁ compl₂`:

| Project (abstract)        | Mathlib `d90090f` (specialised to `normEDS`) |
|---------------------------|-----------------------------------------------|
| `EllSequence.compl'`      | `complEDS'`  (line 392)                        |
| `EllSequence.compl`       | `complEDS`   (line 427)                        |
| `EllSequence.complEDS`    | `complEDS`   (the project's `complEDS` = `compl (normEDS …)`) |
| **`EllSequence.compl_neg`** | **`complEDS_neg`** (line 445, `@[simp]`)     |

Mathlib's direct analogue (verbatim, `@[simp]`):

```lean
@[simp] lemma complEDS_neg (n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n := by
  simp [complEDS]
```

with `complEDS b c d k (n : ℤ) := n.sign * complEDS' b c d k n.natAbs` — i.e. **identical**
statement and **identical** proof idea (`n.sign · f n.natAbs` is odd), differing only in that
mathlib's underlying sequence is the concrete `complEDS'`/`normEDS` rather than the abstract
`compl'`/`W₁`.

Searches run:
- `grep` for `compl_neg`, `compl'`, `complEDS`, `EllSequence` across **all** of
  `.lake/packages/mathlib/Mathlib/` → only hit is this EDS file (`complEDS_neg` etc.); the only
  other `compl_neg` in mathlib is the unrelated `spectrum`/`Algebra.Spectrum.Basic` one.
- Mathlib **master** (fetched `raw.githubusercontent.com/.../EllipticDivisibilitySequence.lean`):
  confirmed **no** `namespace EllSequence`, **no** abstract `compl`/`compl'`/`compl_neg`; master
  still has only the `normEDS`-specialised `complEDS'` / `complEDS` / `complEDS_neg`. So the
  abstract-sequence refactor in this project has **not** been upstreamed.
- leansearch/loogle index agrees with the doc page
  (`leanprover-community.github.io/mathlib4_docs/.../EllipticDivisibilitySequence.html`): public
  API is `complEDS₂` / `complEDS'` / `complEDS` + `complEDS_neg`.

**Conclusion of search:** mathlib already has this lemma, as `complEDS_neg`, with the same
statement, same proof, and an `@[simp]` attribute (which the project copy lacks).

---

## 3. Generality analysis

`compl_neg` is the odd-symmetry of the standard sign-extension `n ↦ n.sign * f n.natAbs` of a
`ℕ → R` sequence. It is not a mathematical theorem about EDS — it is an implementation lemma about
the `ℤ`-indexing convention, true for **any** `f : ℕ → R`. The project's version is strictly more
general than mathlib's `complEDS_neg` only in that the underlying sequence is abstract
(`W₁ compl₂`) rather than `normEDS b c d`; the lemma content is the same one-line `Int.sign`/
`Int.natAbs` fact in both.

There is no "literature-standard maximally-general form" to weaken toward: the maximally general
statement is just `(fun n : ℤ => n.sign * f n.natAbs)` is odd, which is below the threshold of a
standalone mathlib lemma — it is discharged inline by `simp [Int.sign_neg, Int.natAbs_neg]`
wherever needed (exactly as the proof does).

The literature (Ward 1948; Shipsey; Stange; the arXiv EDS corpus) treats `W(-n) = -W(n)` as a
defining/elementary property of (normalised) elliptic sequences; it is never isolated as a named
result, and certainly not the sign-extension bookkeeping lemma seen here.

---

## 4. Composition check (≤ 3 mathlib calls)

Trivially yes — the proof **is** the composition:

```lean
simp [compl, Int.sign_neg, Int.natAbs_neg, neg_mul]
```

unfolds `compl` and applies the existing mathlib simp lemmas `Int.sign_neg`
(`(-n).sign = -n.sign`) and `Int.natAbs_neg` (`(-n).natAbs = n.natAbs`), then `neg_mul`. Any
consumer of the abstract `compl` API can inline this in one `simp` call; no new lemma is needed for
the result to be reachable.

---

## 5. Five-bucket verdict

**NO-mathlib-has-it.**

Mathlib (at the pinned `d90090f`, and still on master) carries the exact analogue
**`complEDS_neg`** — same statement, same proof, additionally tagged `@[simp]` — for its concrete
`complEDS`. The project's `EllSequence.compl_neg` is merely the abstract-sequence (`W₁ compl₂`)
restatement of that already-present lemma, and the lemma itself is trivial sign/`natAbs`
bookkeeping that is also fully composable from existing mathlib simp lemmas (its own one-line
proof).

Disposition: this belongs to the project's local `EllSequence.compl`/`compl'` **refactor track**
that abstracts mathlib's `normEDS`-specialised `complEDS` family over arbitrary sequences. That
*refactor* (the abstract `compl`/`compl'`/`complEDS` API) could be a worthwhile generalisation PR
to mathlib as a whole — but **`compl_neg` in isolation is not a new contribution**: if the abstract
API were upstreamed, mathlib's existing `complEDS_neg` would simply be re-derived from it. As an
individual declaration, mathlib already has it. No action for this decl beyond the usual fork-merge
bookkeeping (and, if upstreaming the abstract API, copy the `@[simp]` attribute mathlib's
`complEDS_neg` already has).

---

### Sources
- Mathlib docs — `Mathlib.NumberTheory.EllipticDivisibilitySequence`:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- Local pinned mathlib source (`d90090f`):
  `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (lines 388–446)
- Mathlib master source (fetched): `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
- Wikipedia — Elliptic divisibility sequence: https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- Stange, "Elliptic nets" / EDS background (arXiv:1909.12654, arXiv:1505.00194)
