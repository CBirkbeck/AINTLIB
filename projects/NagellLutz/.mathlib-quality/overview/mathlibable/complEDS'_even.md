# Mathlibable assessment: `complEDS'_even`

**Verdict: NO-mathlib-has-it**

- **Qualified name:** `complEDS'_even` (root namespace — declared inside `section ComplEDS`, not inside any `namespace`).
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1551`

---

## 0. Source (the declaration under assessment)

Context: `section ComplEDS` (opens line 1524), with
`universe u` / `variable {R : Type u} [CommRing R] (b c d : R) (k : ℤ)`.
This section is **not** inside a namespace (the enclosing `namespace EllSequence` /
`namespace NormEDS` are closed at lines 1516–1522, with the comment
"close `@[expose] public` section to avoid `EllSequence.complEDS` ambiguity"). Hence the
fully-qualified name is just `complEDS'_even`.

```lean
lemma complEDS'_even (m : ℕ) : complEDS' b c d k (2 * (m + 1)) =
    complEDS' b c d k (m + 1) * complEDS₂ b c d ((↑(m + 1) : ℤ) * k) := by
  rw [show 2 * (m + 1) = 2 * m + 2 by rfl, complEDS', dif_pos <| even_two_mul m,
    m.mul_div_cancel_left two_pos, Nat.cast_succ]
```

`complEDS' : ℕ → R` (def at line 1533 of the same file) is the complement sequence of the normalised
EDS `normEDS b c d`. The lemma is its **even-index recursion**: at an even argument `2*(m+1)` the
`if Even` branch of the recurrence fires, giving the factorisation
`complEDS'(2(m+1)) = complEDS'(m+1) · complEDS₂((m+1)·k)`. The proof just unfolds the equation-compiler
definition through that `dif_pos` branch and tidies the index arithmetic.

## 1. Mathematical content / literature

Elliptic divisibility sequences: Ward, *Memoir on Elliptic Divisibility Sequences*, Amer. J. Math. 70
(1948), 31–74. For a normalised EDS `W = normEDS b c d`, the *complement sequence* `Wᶜ(k, n)` witnesses
the divisibility `W(k) ∣ W(n·k)`, i.e. `W(k) · Wᶜ(k,n) = W(n·k)`. `complEDS'_even` is one of the two
defining recurrences (even/odd) computing this complement — pure definitional bookkeeping for the
`complEDS'` recurrence, not an independent theorem. No external literature search is needed: the
identity is settled by an exact mathlib match (below).

## 2. Mathlib search (five methods)

The project file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **fork of
mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (flagged by the project prompt and the
AINTLIB memory atlas). The decisive search is a direct read of the pinned mathlib in `.lake/packages/`:

`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, `section ComplEDS`
(lines 384–503, **no namespace** → root namespace), contains:

- `complEDS'` (def, line 392) — **byte-for-byte identical definition** to the project's line 1533.
- `complEDS'_zero` (403), `complEDS'_one` (407).
- **`complEDS'_even` (line 410)** — identical statement AND identical proof:
  ```lean
  lemma complEDS'_even (m : ℕ) : complEDS' b c d k (2 * (m + 1)) =
      complEDS' b c d k (m + 1) * complEDS₂ b c d ((m + 1) * k) := by
    rw [show 2 * (m + 1) = 2 * m + 2 by rfl, complEDS', dif_pos <| even_two_mul m,
      m.mul_div_cancel_left two_pos, Nat.cast_succ]
  ```
- `complEDS'_odd` (415), `complEDS` (427), `complEDS_even` (448), `complEDS_odd`, `complEDSRec'`,
  `complEDSRec`, `map_complEDS` … — the entire surrounding API is upstream too.

Namespace match: both copies are in an unnamespaced `section ComplEDS`, so both have the
fully-qualified name `complEDS'_even`. Same name, same namespace, same signature, same proof, and the
same supporting definitions (`complEDS'`, `complEDS₂`, `normEDS` — all in mathlib).

Loogle / leansearch / `exact?`-style methods are unnecessary: the file-level identity already
establishes an exact match. The only out-of-project users of this API in the monorepo are in
`projects/HasseWeil/`, which explicitly cite mathlib's `complEDS₂`, `normEDS_mul_complEDS₂`,
`preNormEDS_mul_complEDS₂` — confirming the API is upstream, not project-original.

## 3. Generality analysis

Stated over an arbitrary `CommRing R` (`b c d : R`, `k : ℤ`, `m : ℕ`) — already the maximally general
setting for this ring-level definitional identity. The mathlib version has the **same** generality.
Nothing to weaken.

## 4. Composition check

Not applicable as "composable from primitives": this lemma *is* a mathlib primitive — the even-branch
unfolding of mathlib's own `complEDS'`. Any reproof would just reproduce mathlib's three-line `rw`.

## 5. Conclusion

`complEDS'_even` is a **verbatim fork** of `complEDS'_even` already present in
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (root namespace) — identical definition, statement,
and proof. This is exactly the duplicated-mathlib-fork track the project prompt warned about. It must
**not** be re-added to mathlib; the project should depend on mathlib's copy (the fork exists for
packaging reasons — the `@[expose] public` section noted near line 1522 — not because the lemma is new).

**Bucket: NO-mathlib-has-it.**

### Evidence pointers
- Mathlib: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:410`
  (`complEDS'_even`); def at `:392` (`complEDS'`); section `ComplEDS` `:384`–`:503`.
- Project: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1551`
  (`complEDS'_even`); def at `:1533` (`complEDS'`); section `ComplEDS` opens `:1524`.
