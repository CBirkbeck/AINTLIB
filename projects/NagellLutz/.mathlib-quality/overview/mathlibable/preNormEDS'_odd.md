# Mathlibable assessment — `preNormEDS'_odd`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `preNormEDS'_odd` (root namespace — see below)

**Project:** NagellLutz
**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:764`
**Date:** 2026-06-18

---

## 1. The declaration

Inside `section PreNormEDS` (file line 704), with `variable (b c d : R)` over `[CommRing R]`, in
the **root namespace** (the preceding `namespace IsEllSequence` closed at line 702; `section
PreNormEDS` opens no namespace, and the file-wide `@[expose] public section` is visibility, not a
namespace). Hence the fully-qualified name is simply **`preNormEDS'_odd`**.

```lean
lemma preNormEDS'_odd (m : ℕ) : preNormEDS' b c d (2 * (m + 2) + 1) =
    preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, preNormEDS', dif_pos <| even_two_mul m]
  simp only [Nat.mul_div_cancel_left _ two_pos]
```

It is the defining recurrence (the "odd" branch) of the auxiliary normalised-EDS sequence
`preNormEDS' : ℕ → R` unfolded at an odd index `2*(m+2)+1`. It simply rewrites with the equation
lemma for `preNormEDS'` and discharges the `Even`/division side conditions.

## 2. Mathlib search (5 methods)

The NagellLutz EDS file is a **verbatim fork** of mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence` — same copyright header (David Kurniadi
Angdinata, 2024). The mathlib pin is `d90090f647ca` (`lakefile.toml`).

- **By-name grep of the pinned mathlib source**
  `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`:
  - `def preNormEDS'` — line 124
  - `lemma preNormEDS'_odd` — **line 166** ✅
  - `lemma preNormEDS'_even` — line 160
- **Statement comparison.** Mathlib lines 166–170:

  ```lean
  lemma preNormEDS'_odd (m : ℕ) : preNormEDS' b c d (2 * (m + 2) + 1) =
      preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
    rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, preNormEDS', dif_pos <| even_two_mul m,
      m.mul_div_cancel_left two_pos]
  ```

  This is **character-for-character identical in statement and signature** to the project's lemma
  (`(b c d : R) (m : ℕ)`, same RHS, same `section PreNormEDS` context, root namespace). The
  underlying `def preNormEDS'` is likewise identical (mathlib lines 124–138 vs project 710–736),
  including the extra `b` parameter — so this is **not** a generalisation of a less-general mathlib
  lemma; it is the same lemma over the same definition.
- **Proof differences are purely cosmetic.** Project closes with `simp only [Nat.mul_div_cancel_left
  _ two_pos]`; mathlib folds `m.mul_div_cancel_left two_pos` into the `rw`. The recursive `def`
  differs only in how the well-founded `decreasing_by` bounds are produced (`letI`/explicit `have`
  termination proofs vs `let`/`gcongr`). Statement and type are unchanged.
- **Doc / index confirmation.** The official mathlib4 docs page
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` lists `preNormEDS'` and its companion lemmas
  as public API (WebSearch, §4).

Conclusion of search: the declaration **already exists in mathlib**, verbatim, under the same name
and signature.

## 3. Generality analysis

No gap. Both mathlib's and the project's lemmas are stated over an arbitrary `CommRing R` with the
full `(b, c, d)` parameter set — already the maximally general form for this recurrence (the EDS
normalisation lives in any commutative ring). There is nothing to weaken or strengthen; the project
copy is not more general than mathlib's.

## 4. Composition check

Not applicable in the usual sense (a ≤3-call mathlib reconstruction): the result is literally the
same `lemma` that mathlib already provides. Anything downstream should `import
Mathlib.NumberTheory.EllipticDivisibilitySequence` and use `preNormEDS'_odd` directly rather than
re-prove or re-import the fork.

## 5. Literature

The mathematics is the standard normalised division-polynomial / EDS recurrence (Ward; Stange;
Shipsey), formalised by Angdinata. The recurrence's odd/even split is the content of mathlib's
`preNormEDS'`, with the underlying theory in the arXiv preprint *On Elliptic Sequences over
Commutative Rings* (2604.05280) and Angdinata's mathlib PR. No literature form is "more standard"
than the lemma already in mathlib; literature is moot for a verbatim source-identity match.

Sources:
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [On Elliptic Sequences over Commutative Rings (arXiv 2604.05280)](https://arxiv.org/pdf/2604.05280)
- [An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves in Any Characteristic (ITP 2023)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.6)
- Pinned mathlib source: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:166` (rev `d90090f647ca`)

## 6. Verdict

**NO-mathlib-has-it.** `preNormEDS'_odd` is present verbatim in
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (same name, signature, `CommRing` generality,
and author); the NagellLutz file is a fork of that mathlib module. Action for the project: drop the
fork and `import` the mathlib declaration (cleanup/dedup ticket), not a contribution candidate.
