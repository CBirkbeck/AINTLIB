# Mathlibable assessment — `complEDS_neg`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `complEDS_neg` (root namespace — defined in `section ComplEDS`, which has no
enclosing `namespace`).

---

## 1. The declaration under review

Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1585-1587`
(inside `section ComplEDS`, opened line 1524, closed line 1644; variables
`{R : Type u} [CommRing R] (b c d : R) (k : ℤ)` — no enclosing `namespace`, so the qualified name is
the bare `complEDS_neg`).

```lean
@[simp]
lemma complEDS_neg (n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n := by
  simp only [complEDS, Int.sign_neg, Int.natAbs_neg, Int.cast_neg, neg_mul]
```

where (line 1568)

```lean
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs
```

**Mathematical content.** `complEDS` is the *complement sequence* `Wᶜ(k, n)` of a normalised
elliptic divisibility sequence `W = normEDS b c d`, the witness to `W(k) ∣ W(n·k)` (i.e.
`W(k) · Wᶜ(k,n) = W(n·k)`). It is the ℤ-extension of the ℕ-indexed `complEDS'` via the standard
"sign × value-at-absolute-value" trick: `complEDS n = (sign n) · complEDS'(|n|)`. The lemma states
that this extension is an **odd function of `n`**. This is immediate by definition: negating `n`
flips `Int.sign` and leaves `Int.natAbs` unchanged, so the whole product negates. The proof is a
one-line `simp` unfolding `complEDS` plus `Int.sign_neg`, `Int.natAbs_neg`.

This is the exact same pattern mathlib already uses for the analogous lemmas
`preNormEDS_neg` and `normEDS_neg` (both ℤ-extensions of ℕ-indexed auxiliary sequences via
`n.sign * f n.natAbs`).

---

## 2. Mathlib search (five methods)

The project's own header (file docstring) and `CLAUDE.md` flag that this project **forks**
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. That is exactly what is happening here, so the
mathlib source file is the primary search target.

**Method — direct source read of the forked mathlib file.**
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (in the repo's pinned mathlib at
`.lake/packages/mathlib`) contains, verbatim, the entire `section ComplEDS` that the project
duplicates:

Pinned mathlib for this monorepo: `lakefile.toml rev = 09b373db6e24`, toolchain
`leanprover/lean4:v4.32.0-rc1`. All mathlib line numbers below are in that checkout.

- `def complEDS (n : ℤ) : R := n.sign * complEDS' b c d k n.natAbs`  — **line 427** (identical to
  project line 1568).
- ```lean
  @[simp]
  lemma complEDS_neg (n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n := by
    simp [complEDS]
  ```
  — **line 444–446**, same `section ComplEDS`, same root namespace, same `@[simp]`, **identical
  statement**. (Proof is `simp [complEDS]` vs the project's slightly more explicit
  `simp only [complEDS, Int.sign_neg, Int.natAbs_neg, Int.cast_neg, neg_mul]` — cosmetic only.)

The surrounding context matches too: mathlib has the same `complEDS₂`, `complEDS'`,
`complEDS_ofNat`, `complEDS_zero`, `complEDS_one`, `complEDS_even`, `complEDS_odd`,
`complEDSRec'`, `complEDSRec`, with the same variable binders (`{R} [CommRing R] (b c d : R)`
plus `(k : ℤ)` in `section ComplEDS`). The project's `ComplEDS` section is a near-verbatim copy of
mathlib's.

- **grep / loogle / leansearch:** unnecessary — the declaration is found by name in the pinned
  mathlib source with an identical signature. (`grep -n "complEDS_neg"` in the mathlib file returns
  the line above; the analogous `preNormEDS_neg` (line 206) and `normEDS_neg` (line 318) confirm the
  family is fully upstreamed.)

**Conclusion of search:** `complEDS_neg` is already in mathlib, byte-for-byte the same statement.

---

## 3. Generality analysis

Not applicable for the verdict (mathlib already has the identical decl), but for the record: the
statement is already at its natural generality — any `CommRing R`, arbitrary `b c d : R`, `k : ℤ`.
There is no weaker hypothesis to drop and no more general home: it is a property of *this specific*
`complEDS` definition, and mathlib states it over exactly the same general `CommRing`.

## 4. Composition check

Also moot, but worth noting why this could never be a standalone mathlib target on its own merits:
the lemma is a definitional triviality. Given mathlib's `complEDS` plus `Int.sign_neg` and
`Int.natAbs_neg`, the proof is a single `simp [complEDS]`. It is the kind of "the sign-extension is
odd" boilerplate that ships *next to* the definition (as mathlib indeed does), never as an
independent contribution.

---

## 5. Five-bucket verdict

**NO-mathlib-has-it.**

The exact declaration — same name `complEDS_neg`, same root namespace, same `section ComplEDS`,
same `@[simp]`, same statement `complEDS b c d k (-n) = -complEDS b c d k n`, resting on the
identical `def complEDS` — already exists in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:444`. The project's copy is a fork of that
mathlib section (as the file docstring and `CLAUDE.md` both note). Nothing to upstream; the
cleanup action is to drop the local fork in favour of the mathlib declaration (or, if the fork must
persist for `module`/`@[expose]` reasons, to track it as intentional duplication of upstream).

**Evidence (required for this bucket):**
- Mathlib decl: `complEDS_neg`, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:444`.
- Mathlib `complEDS` def: same file, line 427 — identical to project line 1568.
- Statements compared: identical up to whitespace; proofs differ only cosmetically.
