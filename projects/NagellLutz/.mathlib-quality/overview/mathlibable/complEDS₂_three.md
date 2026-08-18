# Mathlibable assessment — `complEDS₂_three`

**Verdict: NO-mathlib-has-it**

> This exact lemma — same qualified name, statement, `@[simp]` attribute, and proof — is already in
> upstream mathlib. The whole `complEDS₂` family in this project is a verbatim fork.

---

## 1. Declaration under review

- **Qualified name:** `complEDS₂_three` (top-level / root namespace — VERIFIED).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:861`.
- **Statement & proof (project copy, lines 860–862):**

  ```lean
  @[simp]
  lemma complEDS₂_three : complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b := by
    simp [complEDS₂, if_neg (by decide : ¬Even (3 : ℤ)), sub_mul]
  ```

- **Context:** inside `@[expose] public section` (line 81) and `section PreNormEDS` (line 704), with
  `variable (b c d : R)` and `[CommRing R]`. No `namespace` is open at line 861 (the `EllSequence`
  namespace opened at line 90 was closed at line 597), so the fully-qualified name carries **no
  prefix**: it is just `complEDS₂_three`.

### Mathematical content

`complEDS₂` is the *2-complement* of a normalised EDS: the sequence `Wᶜ₂ : ℤ → R` defined from
`preNormEDS` that witnesses the divisibility `W(k) ∣ W(2k)`, i.e. `W(k) · Wᶜ₂(k) = W(2k)`. Concretely

```
complEDS₂ b c d k =
  (preNormEDS (b^4) c d (k-1)^2 · preNormEDS (b^4) c d (k+2)
   − preNormEDS (b^4) c d (k-2) · preNormEDS (b^4) c d (k+1)^2) · (if Even k then 1 else b).
```

`complEDS₂_three` is simply the **evaluation of this definition at the index `k = 3`** — one of the
small-index base cases (`_zero = 2`, `_one = b`, `_two = d`, `_three = …`, `_four = …`) that pin down
the sequence's first terms. It is a `@[simp]` normal-form lemma, obtained by unfolding the definition
and discharging `¬ Even 3` by `decide`. It is API plumbing, not a theorem of independent
mathematical interest.

## 2. Literature search

Not required to settle the bucket (the decl is a trivial index-3 unfolding of a definition that is
itself already in mathlib), but for the record: `complEDS₂` and its complement-sequence API
(`complEDS`, `complEDS'`, `normEDS_mul_complEDS₂`, …) originate from David Kurniadi Angdinata's
mathlib development of elliptic divisibility sequences, following M. Ward, *Memoir on Elliptic
Divisibility Sequences* (Amer. J. Math. 70 (1948), 31–74) — the reference cited in the file header
(line 74). The base-case evaluation lemmas are an artifact of the Lean formalisation, not named
results in the literature.

## 3. Mathlib search — IT IS ALREADY THERE

The AINTLIB monorepo pins mathlib at rev **`d90090f647ca`** (`lakefile.toml`), vendored at
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib`.

`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:263` in that pinned mathlib contains:

```lean
@[simp]
lemma complEDS₂_three : complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b := by
  simp [complEDS₂, if_neg (by decide : ¬Even (3 : ℤ)), sub_mul]
```

This is **byte-identical** to the project's lemma — same name, same signature, same `@[simp]`
attribute, same one-line proof. The underlying `def complEDS₂` (mathlib lines 246–249 vs. project
lines 844–846) is likewise byte-identical, and both sit at the **root namespace** inside a
`section PreNormEDS` with `variable (b c d : R)`.

Provenance confirms this is genuine upstream mathlib, not a project-local addition to a fork: the
git history of the file in the pinned package shows ordinary mathlib PRs —
`48f66c0814 refactor(NumberTheory): golf .../EllipticDivisibilitySequence (#38833)`,
`8eda17ddee doc(NumberTheory): … (#37571)`, `057422b6bc (#36085)`, etc.

**Conclusion:** the project's `EllipticDivisibilitySequence.lean` is a verbatim **fork** of the
mathlib file (consistent with the documented NagellLutz strategy of forking
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and the division-polynomial files). The
declaration `complEDS₂_three` already exists in mathlib, unchanged.

Search methods applied:
- **Direct grep of the pinned mathlib source** — found at `…/EllipticDivisibilitySequence.lean:263`
  (exact name + statement + proof). Decisive.
- **Definition comparison** — `complEDS₂` itself is identical, so the lemma is about the *same*
  object, not a coincidental name clash.
- `lean_loogle` / `leansearch` over the mathlib index would return the same upstream lemma; no
  divergence is possible since the statement is verbatim.

## 4. Generality analysis

Not applicable for the verdict — the maximally-general form *is* the mathlib form, and they are
identical (`[CommRing R]`, `b c d : R`, evaluated at the literal index `3`). There is no weaker
hypothesis to reach for: it is a closed evaluation of a definition.

## 5. Composition check

Trivially composable from mathlib in `≤ 3` calls (it is literally `simp [complEDS₂, …]`), but this
is moot: the *named lemma itself* is already present upstream, so there is nothing to add or
reconstruct.

## 6. Five-bucket verdict

**NO-mathlib-has-it.**

Evidence: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:263` (pinned rev `d90090f647ca`)
defines `complEDS₂_three` with an identical name, statement, `@[simp]` attribute, and proof, over the
identical `def complEDS₂`. The project file is a verbatim fork of the mathlib module. Nothing to
contribute; the project should `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and delete
the duplicated `complEDS₂` block rather than re-state these lemmas (a cleanup/dedup task, not a
mathlib-contribution task).
