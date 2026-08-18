# Mathlibable assessment — `normEDS_even`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `normEDS_even` (top-level, no enclosing namespace — confirmed from source)

---

## 1. The declaration under review

Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:945`

```lean
lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  rw [← normEDS_mul_complEDS₂, mul_assoc, complEDS₂_mul_b]
  ring1
```

Context (project file):
- `variable {R : Type u} [CommRing R]`
- `variable (b c d : R)`, in `section NormEDS`, no enclosing `namespace`.
- `normEDS b c d n := preNormEDS (b ^ 4) c d n * if Even n then b else 1` — the canonical
  normalised elliptic divisibility sequence (`W 0 = 0, W 1 = 1, W 2 = b, W 3 = c, W 4 = d*b`).

Mathematical content: the **even-index recursion / duplication identity** for the canonical
normalised EDS. It expresses the doubled term `W(2m)·b` (the factor `b` clears the normalisation
denominator) through the five neighbours `W(m-2), W(m-1), W(m), W(m+1), W(m+2)`. This is one half of
the standard pair of EDS recurrences (the other being `normEDS_odd`) — the recurrences that *define*
an elliptic divisibility sequence à la Ward.

## 2. Mathlib search (five methods)

The repo carries its own bundled mathlib at `.lake/packages/mathlib`. Direct grep over it:

- `grep "normEDS_even" .lake/packages/mathlib/...` →
  **`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:336`**

```lean
lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  rw [← normEDS_mul_complEDS₂, mul_assoc, complEDS₂_mul_b]
  ring1
```

This is **byte-for-byte identical** — same name, same signature, same `variable (b c d : R)` over
`[CommRing R]`, same top-level (un-namespaced) qualified name `normEDS_even`, and the **same
proof term**. Every dependency it uses is likewise present and identical in the bundled mathlib:
`normEDS` (def, line 289), `complEDS₂` (def, line 246), `normEDS_mul_complEDS₂` (line 321),
`complEDS₂_mul_b` (line 329), `preNormEDS`/`preNormEDS_even`/`preNormEDS_odd`.

Methods cross-checked:
1. **Exact-name grep** — hit (mathlib line 336). ✔
2. **Statement / signature match** — identical. ✔
3. **Dependency grep** (`preNormEDS_even`, `preNormEDS_odd`, `complEDS₂`, `normEDS_mul_complEDS₂`,
   `complEDS₂_mul_b`) — all present and identical in mathlib. ✔
4. **Consumers** — both `projects/NagellLutz/.../DivisionPolynomial.lean:355` and
   `Mathlib/.../DivisionPolynomial/Basic.lean:432` call `normEDS_even ..` the same way, confirming
   the duplicated API is consumed identically on both sides. ✔
5. **leansearch/loogle** unnecessary — the symbol is already located by exact name in the in-tree
   mathlib; an index lookup would only re-find the same upstream lemma.

This matches the PROJECT CONTEXT note exactly: NagellLutz **forks**
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`. `normEDS_even` is a verbatim copy of
the upstream lemma carried inside the fork.

## 3. Literature / generality analysis

The EDS recurrences are classical (Ward, *Memoir on elliptic divisibility sequences*, Amer. J.
Math. 70 (1948); see also Shipsey's thesis and Stange's *Elliptic nets*). The mathlib statement is
already in its **maximally general standard form**: an arbitrary commutative ring `R`, arbitrary ring
elements `b c d : R` (no domain / field / `IsDomain` / `nonZeroDivisors` hypotheses), index over all
of `ℤ`. There is nothing to weaken or generalise — and even if there were, it is moot because the
identical lemma is already upstream. (The project's nearby `IsEllSequence.normEDS_*` lemmas are where
a `nonZeroDivisors` hypothesis was *removed* relative to an earlier private version; `normEDS_even`
itself carries no such hypothesis in either copy.)

## 4. Composition check

Not applicable for an add decision: the lemma is not "composable from mathlib primitives we'd write
inline" — it **is** a named mathlib lemma already. (For the record, its own proof is a 2-step
`rw` + `ring1` on top of `normEDS_mul_complEDS₂` and `complEDS₂_mul_b`, both also upstream.)

## 5. Conclusion

`normEDS_even` is a duplicate of an existing mathlib lemma
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:336`), identical in name, statement, and
proof, living in a file the project forked from mathlib. It cannot be "added" — mathlib already has
it. The appropriate cleanup action is **dedup**: drop the fork and `import
Mathlib.NumberTheory.EllipticDivisibilitySequence`, or, if the fork must persist for unrelated local
edits elsewhere in the file, treat this lemma as upstream and do not propose it for contribution.

**Bucket: NO-mathlib-has-it** — exact upstream match at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:336`.
