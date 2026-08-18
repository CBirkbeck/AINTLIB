# Mathlibable assessment — `IsEllSequence.neg`

**Verdict bucket: `YES-add-as-is`**

> An elliptic sequence is an odd function (`W (-m) = -W m`) given its first two terms are
> non-zero-divisors. Standard result (Ward/Stange), absent from mathlib, not composable.

---

## 1. The declaration

- **Qualified name:** `IsEllSequence.neg` (base name `neg`, inside `namespace IsEllSequence`,
  opened at line 643, closed at line 702 — line 676 is inside it).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:676`.

```lean
/-- An elliptic sequence is an odd function, provided its first two terms are not zero divisors. -/
lemma neg (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  · refine two.2 _ ((pow_mem one 2).2 _ ?_)
    have := sub_add_neg_sub_mul_eq_zero ell (1 - ↑m) (↑m + 1) 1
    rw [show ((1 : ℤ) - ↑m - (↑m + 1)) = -(2 * ↑m) from by omega,
      show ((1 : ℤ) - ↑m + (↑m + 1)) = 2 from by omega] at this
    simpa [neg_neg] using this
  · refine one.2 _ ((pow_mem one 2).2 _ ?_)
    have := sub_add_neg_sub_mul_eq_zero ell (-↑m) (↑m + 1) 1
    rw [show ((-↑m : ℤ) - (↑m + 1)) = -(2 * ↑m + 1) from by omega,
      show ((-↑m : ℤ) + (↑m + 1)) = 1 from by omega] at this
    simpa [neg_neg] using this
```

**Context / hypotheses in scope** (section variables, lines 647–673):
- `ell : IsEllSequence W` — `W : ℤ → R`, `R` a `CommRing`, satisfies
  `Rel₃ W m n r` for all `m n r`, i.e.
  `W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`.
- `one : W 1 ∈ R⁰` and `two : W 2 ∈ R⁰` — the first two terms are non-zero-divisors
  (`R⁰` = `nonZeroDivisors R`).

**Statement (math):** every elliptic sequence over a commutative ring is an odd function,
`W(−m) = −W(m)`, provided `W(1)` and `W(2)` are non-zero-divisors.

**Proof shape:** rewrite to `W(-m) + W m = 0`; split on parity of `m` via `Int.even_or_odd'`;
in each branch instantiate the project-local auxiliary identity
`sub_add_neg_sub_mul_eq_zero` (line 665) at carefully chosen indices so the surviving
factor is `W 2 · (W 1)²` (even case) or `(W 1)² · (W 1)` (odd case), then cancel those
factors using the non-zero-divisor hypotheses (`two.2`, `one.2`, `pow_mem`).

The dependency `sub_add_neg_sub_mul_eq_zero` proves
`(W(m−n) + W(−(m−n)))·W(m+n)·W(r)² = 0` by adding the elliptic relation to its `(m,n)`-swap.

---

## 2. Literature search

The antisymmetry of elliptic sequences/nets is a foundational, textbook result.

- **Morgan Ward**, *Memoir on Elliptic Divisibility Sequences* (the file's own cited reference):
  the sequence extends to negative indices as an **antisymmetric** sequence, `τ_{−n} = −τ_n`.
- **K. Stange**, *Elliptic nets and elliptic curves* (arXiv:0710.1316) and the
  *Formulary for elliptic divisibility sequences and elliptic nets*: an elliptic net is an
  **odd function**, `W(−v) = −W(v)` for every `v`. Stange's proof derives
  `W(v)³·(W(v) + W(−v)) = 0` and cancels because the base ring is an **integral domain**.

So the *fact* is completely standard. The project's contribution is the **formulation**:
instead of "`R` is an integral domain", it requires only the two specific terms `W(1), W(2)`
to be non-zero-divisors. This is a genuine, strictly-more-general hypothesis (an integral
domain makes *every* nonzero element a non-zero-divisor; here only two are needed, and `R`
may have zero-divisors elsewhere). The generalization matters for the project's intended
application — elliptic sequences arising from division polynomials over general base rings,
where one cannot assume `R` is a domain but can control these leading terms.

**Sources:**
- [Stange, Elliptic nets and elliptic curves (arXiv:0710.1316)](https://arxiv.org/abs/0710.1316)
- [Stange, Formulary for EDS and elliptic nets](https://math.colorado.edu/~kstange/papers/edsformulary.pdf)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [The sign of an elliptic divisibility sequence (arXiv:math/0402415)](https://arxiv.org/pdf/math/0402415)

---

## 3. Mathlib search (exhaustive)

The project **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence`. I compared directly
against the pinned mathlib source at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

| | mathlib (547 lines) | project fork (1667 lines) |
|---|---|---|
| `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence` | ✅ defs | ✅ (same) |
| `IsEllSequence.smul`, `.map` | ✅ `.smul` (`.map` only in fork) | ✅ |
| `preNormEDS`/`normEDS`/`complEDS` machinery + their `_neg` lemmas | ✅ | ✅ |
| `EllSequence` namespace (`Rel₃`, `rel₄`, `net`, `OddRec`, `EvenRec`, `addMulSub`, parity transf) | ❌ **absent** | ✅ **new** |
| `IsEllSequence.{zero, sub_add_neg_sub_mul_eq_zero, neg, rel₄, net, invar}` | ❌ **absent** | ✅ **new** |

Search methods applied:
1. **grep over the whole mathlib tree** for `IsEllSequence` — appears in exactly one file
   (the EDS file); the only lemma in its namespace there is `IsEllSequence.smul`. **No
   `.neg`, `.odd`, `.symm`** anywhere.
2. **grep for the helper** `sub_add_neg_sub_mul_eq_zero` across all of mathlib — **not present**.
3. **grep for** `Rel₃`, the `EllSequence` namespace, and a generic "elliptic-sequence oddness"
   lemma — **not present**.
4. Mathlib's `*_neg` lemmas (`normEDS_neg`, `preNormEDS_neg`, `complEDS_neg`) prove oddness only
   for the **specific constructed** normalised sequences, by unfolding their explicit recursive
   definitions (`even_neg`, `neg_mul`, …). That proof is **not transferable** to an arbitrary
   `IsEllSequence W`; it is a different statement (a property of one construction, not of the
   class).
   (Dedicated index tools `lean_loogle`/`lean_leansearch` were unavailable in this environment;
   direct source grep over the pinned mathlib is strictly more authoritative and was used instead.)

**Conclusion:** the general result "an arbitrary elliptic sequence is odd" is **not in mathlib**
in any form.

---

## 4. Generality analysis

- **Object:** maximally general — `W : ℤ → R` for an arbitrary `CommRing R`, with the elliptic
  recurrence as the sole structural hypothesis. Matches the literature's `IsEllSequence`.
- **Hypothesis:** `W 1 ∈ R⁰`, `W 2 ∈ R⁰` is **strictly weaker** than the classical "`R` is an
  integral domain" used by Ward/Stange, and is the right minimal condition (the proof cancels
  exactly factors `(W 1)²` and `W 2`). This is the better-than-literature formulation and is
  already in its most general useful form.
- No further mechanical weakening is available: dropping either hypothesis breaks the
  cancellation (over a ring with zero-divisors, an elliptic sequence need not be odd if its
  leading terms are zero-divisors). So no `YES-but-generalise-first` action is warranted.

---

## 5. Composition check (can ≤3 mathlib calls give it?)

**No.**

- The mathematical core is the auxiliary identity
  `(W(m−n) + W(−(m−n)))·W(m+n)·W(r)² = 0`, obtained from the **elliptic recurrence and its
  index-swap** — this is `sub_add_neg_sub_mul_eq_zero`, which is **project-local and not in
  mathlib**. It is irreducibly tied to the `Rel₃` definition.
- On top of that, the proof needs a **parity split** (`Int.even_or_odd'`) with **two distinct
  index specializations** chosen so the leftover coefficient is a product of (powers of) `W 1`
  and `W 2`.
- The generic mathlib API that *is* used (`pow_mem`, the non-zero-divisor cancellation
  `mem_nonZeroDivisors`/`x * r = 0 ↔ x = 0`) is only the final cancellation step — it does not
  produce the identity being cancelled.

So while the *last* step is generic, the lemma as a whole is a multi-step argument resting on a
new elliptic-sequence-specific identity. It is **not** a ≤3-lemma composition of existing
mathlib primitives. → not `NO-composable-from-mathlib`.

---

## 6. Verdict

**`YES-add-as-is`.**

- The result is a standard, named property of elliptic sequences/nets (Ward antisymmetry;
  Stange "an elliptic net is an odd function").
- It is **not in mathlib** — mathlib has oddness only for the specific constructed normalised
  EDS, not for the general class `IsEllSequence`.
- It is already in (better than) its literature-standard generality: the non-zero-divisor
  hypothesis is strictly weaker than the usual integral-domain assumption, so no
  generalise-first step is needed.
- It is not composable from a handful of generic lemmas; the proof rests on a genuinely new
  elliptic-relation identity plus a parity argument.

This lemma — together with the surrounding `EllSequence`/`IsEllSequence` symmetry API the fork
adds (`zero`, `sub_add_neg_sub_mul_eq_zero`, `neg`, `rel₄`, `net`, `invar`) — is exactly the kind
of foundational EDS material that belongs upstream in
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. Recommend contributing the block as-is
(after the usual mathlib-PR polish), with `IsEllSequence.neg` as a headline lemma.
