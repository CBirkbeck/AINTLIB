# Mathlibable assessment — `compl₂EDS_neg`

**Verdict bucket: `NO-mathlib-has-it`**

**One-line rationale:** Verbatim renamed duplicate of mathlib's `complEDS₂_neg` — same statement, same definition, same proof.

---

## 1. The declaration under review

- **Parsed/verified qualified name:** `compl₂EDS_neg` (root namespace — confirmed no `namespace` wraps line 1044; the enclosing `section NormEDS` / `section Complement` introduce no namespace).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1044`

```lean
@[simp] lemma compl₂EDS_neg : compl₂EDS b c d (-m) = compl₂EDS b c d m := by
  simp_rw [compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m, preNormEDS_neg, even_neg]; ring
```

with `variable (b c d : R) (m : ℤ)` and `R` a `CommRing`.

The underlying definition (`compl₂EDS`, line 1032):

```lean
def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b
```

**Mathematical content.** `compl₂EDS b c d m` is the "2‑complement" of a normalised EDS `W = normEDS b c d`: the witness of `W(m) ∣ W(2m)`, i.e. `W(m) · compl₂EDS(m) = W(2m)` (see the companion lemma `normEDS_mul_compl₂EDS`). The lemma states this complement is an **even** function of the index `m`. This is immediate because it is built from squares and products of `preNormEDS`, which is an **odd** function (`preNormEDS_neg : preNormEDS (-n) = -preNormEDS n`), so the negative-index reflection `m-1 ↦ -(m+1)`, `m+2 ↦ -(m-2)` etc. flips every sign in pairs and the `if Even m` factor is `even_neg`-invariant.

## 2. Literature search

- Wikipedia "Elliptic divisibility sequence" and Ward's foundational parametrisation `Wₙ = σ(nz)/σ(z)^{n²}` make `W₋ₙ = −Wₙ` (odd) standard folklore. The 2‑complement `W(2m)/W(m)` is then even in `m`. There is no special name in the literature for this parity fact; it is a one-line corollary of the oddness of `W`.
- Crucially, the **top search hit is the mathlib doc page itself** (`Mathlib.NumberTheory.EllipticDivisibilitySequence`), which is exactly where this lemma already lives. (Refs: leanprover-community mathlib4 docs; Wikipedia EDS; Ward, *Memoir on elliptic divisibility sequences*; Silverman/Stephens "The sign of an EDS", arXiv:math/0402415.)

## 3. Mathlib search — IT IS ALREADY THERE (exact match)

The NagellLutz project **forks** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The upstream file (in this repo's pinned mathlib, `.lake/packages/mathlib/.../EllipticDivisibilitySequence.lean`) contains:

```lean
-- mathlib lines 246-248
def complEDS₂ (k : ℤ) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

-- mathlib lines 271-274
@[simp]
lemma complEDS₂_neg (k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k := by
  simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
  ring1
```

**Equivalence to the project decl:**
- **Definition:** project `compl₂EDS` inlines `letI p := preNormEDS (b^4) c d`; expanding it gives mathlib's `complEDS₂` term-for-term. They are *definitionally identical*.
- **Statement:** `compl₂EDS_neg` and `complEDS₂_neg` are the identical proposition `(-m) ↦ (m)`, both `@[simp]`.
- **Proof:** identical strategy — `simp_rw` unfolds the def, rewrites the three offsets to negated forms, applies `preNormEDS_neg` + `even_neg`, then closes by `ring`/`ring1`. The only difference is a cosmetic choice of the three arithmetic rewrite lemmas (`neg_sub_left, neg_add_eq_sub, ← neg_sub m` vs `← neg_add', ← sub_neg_eq_add, ← neg_sub'`), which reach the same intermediate goal.

**Smoking gun:** the project's *own* file already contains the verbatim mathlib copy at **line 870** — `complEDS₂_neg (k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k` with the exact mathlib proof — inside its forked `section NormEDS` (lines 844–942 are byte-for-byte the upstream `complEDS₂` API). The `compl₂EDS` track (lines 1011+, `section Complement`) is a parallel **renamed re-derivation** the project layered on top (it adds `compl₂EDSAux`, not in mathlib, but `compl₂EDS_neg` itself adds nothing new).

Mathlib's five search methods all collapse to the same answer here: the decl, its definition, and its proof are present upstream under the name `complEDS₂_neg`.

## 4. Generality analysis

No generality gap. Both versions are stated over an arbitrary `CommRing R` with `b c d : R` and an integer index — already the maximal natural generality (EDS coefficients live in a commutative ring; the index is `ℤ`). The project version is *not* more general; it is the same statement with a different name and an extra inlined `letI`.

## 5. Composition check

Trivially composable from mathlib in 0 extra steps: it **is** `complEDS₂_neg`. Even ignoring the exact match, it is a 1-line `simp_rw [...preNormEDS_neg, even_neg]; ring` over the existing mathlib lemma `preNormEDS_neg`. Nothing new to contribute.

## 6. Conclusion

`compl₂EDS_neg` is a forked, renamed duplicate of the existing mathlib lemma **`complEDS₂_neg`** (`Mathlib.NumberTheory.EllipticDivisibilitySequence`), over a definitionally-identical `compl₂EDS` = `complEDS₂`. It is already in mathlib in full generality with essentially the same proof. Nothing to upstream.

- **Bucket:** `NO-mathlib-has-it`
- **Mathlib name it duplicates:** `complEDS₂_neg`
- **Action for the project:** when this fork is reconciled with mathlib, delete the renamed `compl₂EDS`/`compl₂EDS_neg` track and use `complEDS₂` / `complEDS₂_neg` directly (the project already imports them at lines 844–942). The only genuinely project-local addition in this section is `compl₂EDSAux` (and its lemmas), which is *not* this declaration.
