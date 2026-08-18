# Mathlibable assessment: `complEDS_odd`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `complEDS_odd` (top-level — no enclosing `namespace`; lives in `section ComplEDS`)

**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1594`

---

## 0. The declaration (verified from source)

```lean
lemma complEDS_odd (m : ℤ) : complEDS b c d k (2 * m + 1) =
    complEDS b c d k m ^ 2 * normEDS b c d ((m + 1) * k + 1) *
        normEDS b c d ((m + 1) * k - 1) -
      complEDS b c d k (m + 1) ^ 2 * normEDS b c d (m * k + 1) *
          normEDS b c d (m * k - 1) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp [complEDS_zero, complEDS_one]
    norm_cast
    simpa only [complEDS_ofNat] using complEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp [complEDS_zero, complEDS_one]
    simp_rw [Nat.cast_succ, show 2 * -(↑m + 1 : ℤ) + 1 = -(2 * ↑m + 1) by ring,
      show (-(↑m + 1 : ℤ) + 1) = -↑m by ring, neg_mul, ← sub_neg_eq_add, ← neg_sub',
      sub_neg_eq_add, ← neg_add', complEDS_neg, normEDS_neg, ih]
    ring
```

Context (`section ComplEDS`, `variable {R} [CommRing R] (b c d : R) (k : ℤ)`):
`complEDS b c d k n := n.sign * complEDS' b c d k n.natAbs` is the integer-indexed
**complement sequence** of a normalised EDS, witnessing the divisibility `W(k) ∣ W(n·k)`.
`complEDS_odd` is the odd-index recurrence step expressing `complEDS … (2m+1)` in terms of
`complEDS … m`, `complEDS … (m+1)` and `normEDS` values — the integer-lift of `complEDS'_odd`.

**Mathematical statement.** For a commutative ring `R`, ring elements `b, c, d`, an integer `k`,
and the integer-indexed complement sequence `Wᶜ(k, ·) = complEDS b c d k` of the normalised EDS
`W = normEDS b c d`, the odd terms satisfy
`Wᶜ(k, 2m+1) = Wᶜ(k, m)²·W((m+1)k+1)·W((m+1)k−1) − Wᶜ(k, m+1)²·W(mk+1)·W(mk−1)`
for every `m ∈ ℤ`.

---

## 1. Literature search

The "complement sequence" `complEDS`/`complEDS'` is **not** classical literature terminology — it
is the bookkeeping device introduced by **David Kurniadi Angdinata** (the copyright author of this
very file) inside mathlib's own EDS development to witness the divisibility property of normalised
EDSs (it generalises `complEDS₂`, the 2-division-polynomial complement). The odd recurrence
mirrors Ward's three-term elliptic recurrence (M. Ward, *Memoir on Elliptic Divisibility
Sequences*, Amer. J. Math. 70 (1948), 31–74), cited in the file header. There is no external
"standard form" to weaken toward: the lemma is internal API of an already-upstreamed construction.
The web search surfaces only the mathlib4 docs page for this exact module plus survey papers on
EDS — no competing formalisation.

## 2. Mathlib search — DECISIVE

`complEDS_odd` is **already in mathlib**, verbatim, on the *exact commit this repo is pinned to*.

- File: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (mathlib `09b373db6e24`,
  `leanprover/lean4:v4.32.0-rc1` — verified: vendored package HEAD == lakefile pin).
- Vendored at: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:458`.
- Same `section ComplEDS`, same top-level name `complEDS_odd`, **character-for-character identical
  statement**:

```lean
lemma complEDS_odd (m : ℤ) : complEDS b c d k (2 * m + 1) =
    complEDS b c d k m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
      complEDS b c d k (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1) := by …
```

The only differences are cosmetic proof-script nits (`using!` vs `using`, `ring1` vs `ring`,
`by rfl` vs `by ring`, an inlined `simp` vs `simp [complEDS_zero, complEDS_one]`). Statement,
signature, namespace, and surrounding API (`complEDS`, `complEDS'`, `complEDS₂`, `complEDS_even`,
`complEDS_ofNat`, `complEDS_neg`, `complEDSRec`, `map_complEDS`) are all present upstream and match.

Confirmed live on current mathlib master via the docs index
(`mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html`) — same author, same module.

**Conclusion:** the project's `EllipticDivisibilitySequence.lean` is a fork/snapshot of the
upstream mathlib module (this project forks `Mathlib.NumberTheory.EllipticDivisibilitySequence`
and the `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` files). `complEDS_odd` is
one of the duplicated declarations.

Search methods used:
1. Direct grep of the pinned mathlib source — **HIT** (exact match, line 458).
2. Namespace structure check — both top-level, no namespace; identical section layout.
3. mathlib4 docs / web index — **HIT** (module + family live on master).
4. loogle/leansearch — not needed; a verbatim source hit already settles it.

## 3. Generality analysis

Maximally general already and identical to upstream: stated over an arbitrary `CommRing R` with
free parameters `b c d : R`, `k : ℤ`, `m : ℤ`. No assumption to weaken — upstream chose the same
signature. Nothing to generalise.

## 4. Composition check

Not applicable in the usual sense — it is not "composable from three mathlib primitives", it
**is** a mathlib primitive (the canonical odd-recurrence lemma for `complEDS`). Anyone needing it
should `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and use `complEDS_odd` directly.

## 5. Verdict

**NO-mathlib-has-it.** `complEDS_odd` exists in mathlib under the identical top-level name with a
character-for-character identical statement, on the exact pinned commit (`09b373db6e24`,
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:458`) and on current master. The project
copy is forked duplication; the cleanup action is to drop the fork and import upstream (whole-file
de-duplication, owner-driven), not to contribute anything.

### Sources
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- Vendored mathlib pin: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:458` (`09b373db6e24`)
- M. Ward, *Memoir on Elliptic Divisibility Sequences*, Amer. J. Math. 70 (1948) 31–74 (file's cited reference)
