# Mathlibable assessment — `compl₂EDS_mul_b`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `compl₂EDS_mul_b` (no enclosing namespace; the file is wrapped only in
`@[expose] public section`, and the decl at line 1063 sits in `section Complement`, outside the
inner `namespace EllSequence`).

**Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1063`

**One-line rationale:** Verbatim in mathlib as `complEDS₂_mul_b`; the project file is a fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` that merely renamed `complEDS₂` → `compl₂EDS`.

---

## 1. The declaration under review

```lean
-- section Complement;  variable (b c d : R) (m : ℤ);  R a CommRing
lemma compl₂EDS_mul_b : letI W := normEDS b c d
    compl₂EDS b c d m * b = W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    simp_rw [compl₂EDS, normEDS, Int.even_sub, Int.even_add,
      Int.not_even_one, even_two, iff_false, iff_true]
    split_ifs <;> ring
  | neg hm m =>
    simp_rw [← neg_add', neg_add_eq_sub, ← neg_sub (m : ℤ), normEDS_neg, compl₂EDS_neg]
    convert hm m using 1; ring
```

Expanding the local `letI W := normEDS b c d`, the statement is exactly

```
compl₂EDS b c d m * b
  = normEDS b c d (m-1)^2 * normEDS b c d (m+2)
  - normEDS b c d (m-2) * normEDS b c d (m+1)^2
```

It is the "strip the factor of `b`" identity for the 2-complement sequence: it rewrites
`compl₂EDS · b` (which clears the `if Even m then 1 else b` factor sitting on the `preNormEDS`
spelling of the definition) into the four-term `normEDS` expression. Mathematically this is one
half of the EDS duplication formula `W(k)·Wᶜ₂(k) = W(2k)` (the part that expresses `Wᶜ₂(k)·W(2)`
in `normEDS` terms; recall `W(2) = b`).

## 2. Mathlib search (five methods)

The project openly **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(mathlib pinned at `d90090f647ca`, the repo's shared rc2 commit). The forked-and-renamed family is:

| project name | mathlib name |
|---|---|
| `compl₂EDSAux`        | (no exact analogue; internal helper)          |
| `compl₂EDS`           | **`complEDS₂`**                                |
| `compl₂EDS_neg`       | `complEDS₂_neg`                               |
| `normEDS_mul_compl₂EDS` | `normEDS_mul_complEDS₂`                     |
| `normEDS_dvd_two_mul` | `normEDS_dvd_normEDS_two_mul`                 |
| **`compl₂EDS_mul_b`** | **`complEDS₂_mul_b`**                          |

- **grep over the pinned mathlib source** (`.lake/packages/mathlib`): the *project* names
  (`compl₂EDS…`) do **not** occur — confirming they are the fork's renamings, not upstream. The
  *mathlib* names (`complEDS₂…`) occur in
  `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.
- **direct read of mathlib source** — the upstream lemma is, at lines 329–334:

  ```lean
  lemma complEDS₂_mul_b (k : ℤ) : complEDS₂ b c d k * b =
      normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
        normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2 := by
    simp_rw [complEDS₂, normEDS, Int.even_add, Int.even_sub, even_two, iff_true,
      Int.not_even_one, iff_false]
    split_ifs <;> ring1
  ```

- **definitions agree byte-for-byte.** Project `compl₂EDS` (lines 1032–1034):
  ```lean
  def compl₂EDS : R :=
    letI p := preNormEDS (b ^ 4) c d
    (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b
  ```
  Mathlib `complEDS₂` (lines 246–248):
  ```lean
  def complEDS₂ (k : ℤ) : R :=
    (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
      preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
  ```
  These are the same function (`p` is a local abbreviation for `preNormEDS (b ^ 4) c d`; `m` vs `k`).
- **leansearch / docs (web)** — the mathlib4 docs page
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` documents `complEDS₂` with this exact
  definition and the witnessing identity `W(k) * Wᶜ₂(k) = W(2 * k)`.

**Conclusion of search:** the lemma is already in mathlib, verbatim, under the name
`complEDS₂_mul_b`. The only differences are cosmetic: the rename `complEDS₂ → compl₂EDS`, the bound
variable `k → m`, and using a `letI W := normEDS b c d` abbreviation in the statement instead of
spelling `normEDS` out. The proof term is essentially identical (`simp_rw [… complEDS₂/compl₂EDS,
normEDS, …]; split_ifs <;> ring`); the project additionally routes through `Int.negInduction`,
but mathlib's `complEDS₂_mul_b` already holds for all `k : ℤ` directly.

## 3. Generality analysis

No generalisation question arises: the mathlib statement is **identical** in generality (same
`CommRing R`, same `b c d : R`, same `k : ℤ`, same four-term RHS). There is no weaker-hypothesis
or more-general upstream form to prefer — it is literally the same lemma. The literature
(Ward's original duplication recursion for EDS / division polynomials; Stange's "Formulary for
elliptic divisibility sequences and elliptic nets") frames this as a standard duplication identity,
exactly the level at which mathlib already states it.

## 4. Composition check

Not needed for the verdict (the lemma is present as a single named result). For completeness: it
would in any case be a ≤3-call consequence of the existing mathlib `complEDS₂` / `normEDS` defs —
`simp_rw [complEDS₂, normEDS, …]; split_ifs <;> ring` is precisely how mathlib proves it. So even
absent the named lemma it would be NO-composable-from-mathlib; but it is in fact named.

## 5. Literature search

- Mathlib4 docs: `Mathlib.NumberTheory.EllipticDivisibilitySequence` —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
  (documents `complEDS₂`, `complEDS₂_mul_b`, `normEDS_mul_complEDS₂`,
  `normEDS_dvd_normEDS_two_mul`).
- K. Stange, *Formulary for elliptic divisibility sequences and elliptic nets* —
  https://math.colorado.edu/~kstange/papers/edsformulary.pdf (standard duplication/division
  identities for EDS).
- Elliptic divisibility sequence — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
  (Ward's recursion; `W(k) ∣ W(2k)` divisibility).

These confirm the identity is textbook EDS material and is exactly what mathlib has formalized.

---

## Verdict

**NO-mathlib-has-it.** `compl₂EDS_mul_b` is `Mathlib.NumberTheory.EllipticDivisibilitySequence`'s
`complEDS₂_mul_b` — same statement, same proof shape, same generality, with the underlying
definition `compl₂EDS` being a byte-identical copy of mathlib's `complEDS₂` (renamed `complEDS₂`
→ `compl₂EDS`, `k` → `m`). This is forked-and-renamed mathlib code; nothing to upstream. When this
NagellLutz fork is reconciled with mathlib, this decl (and its whole `compl₂EDS*` family) should be
dropped in favour of the upstream `complEDS₂*` names.
