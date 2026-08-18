# Mathlibable assessment: `complEDS_zero`

**Verdict: `NO-mathlib-has-it`**

> An identical declaration `complEDS_zero` already exists in the mathlib version pinned by this
> repo, in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The project's copy is a stale
> fork of that exact file.

---

## 1. The declaration under assessment

**Qualified name:** `complEDS_zero` (top-level — *not* namespaced).

File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1577-1579`

> **Line-number note:** the prompt pointed at line 1573, which is actually inside the *proof
> body* of the neighbouring `complEDS_ofNat`. The lemma literally named `complEDS_zero` is the
> `@[simp] lemma` at **line 1578** (with its `@[simp]` attribute on 1577). Verified target = that
> lemma.

```lean
@[simp]
lemma complEDS_zero : complEDS b c d k 0 = 0 := by
  simp only [complEDS, Int.sign_zero, Int.cast_zero, zero_mul]
```

Context (`projects/.../EllipticDivisibilitySequence.lean:1519-1564`):

```lean
section ComplEDS
universe u
variable {R : Type u} [CommRing R] (b c d : R) (k : ℤ)
...
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs
```

This is the boundary/`simp` lemma stating that the **complement sequence** `Wᶜ(k, n)` for a
normalised EDS vanishes at `n = 0`. It is a trivial unfolding: `Int.sign 0 = 0`, the cast of `0` is
`0`, and `0 * _ = 0`.

> **Qualified-name note (the prompt asked to verify):** the prompt's guessed base name
> `complEDS_zero` is correct, but note the file contains a *second, different* `complEDS` —
> `EllSequence.complEDS` (line 1111, the abstract sequence-parametrised version). The target at
> line 1573 is the **concrete** top-level `complEDS` (defined via `normEDS`), and its full name is
> simply `complEDS_zero`. The file's `@[expose] public section` is deliberately closed at line 1517
> ("to avoid `EllSequence.complEDS` ambiguity") precisely so this top-level `complEDS` lives outside
> any namespace.

---

## 2. Mathlib search (five methods) — DECISIVE

The pinned mathlib in this repo is:
`/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`

That file contains the **entire complement-sequence theory** — `complEDS₂`, `complEDS'`,
`complEDS`, their `_zero`/`_one`/`_neg`/`_even`/`_odd` lemmas, the recursors, and the `map_*`
lemmas — in a `section ComplEDS` (line 384). In particular:

**`def complEDS`** (mathlib lines 427-428):
```lean
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs
```
— **byte-for-byte identical** to the project's definition (project line 1563-1564).

**`lemma complEDS_zero`** (mathlib lines 436-438):
```lean
@[simp]
lemma complEDS_zero : complEDS b c d k 0 = 0 := by
  simp [complEDS]
```
— **same statement, same `@[simp]` attribute, same top-level (unnamespaced) `section ComplEDS`
context** (`variable {R} [CommRing R] (b c d : R) (k : ℤ)`). The only difference is a cosmetic one
in the *proof script* (`simp [complEDS]` vs. the project's spelled-out
`simp only [complEDS, Int.sign_zero, Int.cast_zero, zero_mul]`) — the statement and name are
the same.

So the project's `EllipticDivisibilitySequence.lean` is a **stale fork** of the upstream mathlib
file: it re-derives `preNormEDS`/`normEDS`/`complEDS₂`/`complEDS'`/`complEDS` verbatim, then layers
*additional* unupstreamed machinery on top (the `EllSequence.compl`/`complEDS`,
`redInvarNum`/`redInvarDenom`, divisibility, and `Param`/`MvPolynomial` apparatus). The concrete
`complEDS`/`complEDS_zero` it carries is **exactly mathlib's** and should be deleted in favour of
the upstream copy when this fork is reconciled.

- Method 1 (exact name `complEDS_zero`): **HIT** in pinned mathlib (line 437).
- Method 2 (definition `complEDS`): **HIT** in pinned mathlib (line 427), identical signature.
- Methods 3-5 (loogle / leansearch / more-general form): moot — an identical declaration is
  already present in the build's mathlib.

(The repo's MEMORY atlas already records this: the project "FORKS parts of mathlib
... `Mathlib.NumberTheory.EllipticDivisibilitySequence`", which this confirms exactly.)

---

## 3. Literature search

Not load-bearing given the verbatim mathlib hit, but for the record: the complement /
"co-sequence" `Wᶜ` witnessing the divisibility `W(k) ∣ W(nk)` of an elliptic divisibility sequence
is standard EDS theory (M. Ward, *Memoir on Elliptic Divisibility Sequences*, Amer. J. Math. 70
(1948); cf. the references block at the head of both files). `complEDS_zero` is merely the `n = 0`
base value `Wᶜ(k, 0) = 0`, not a named theorem in the literature — it is housekeeping for the
recursive definition.

---

## 4. Generality analysis

There is no meaningful generalisation to seek. The lemma is the definitional value of a bespoke
recursive sequence at its zero index, stated over an arbitrary `CommRing R` (already the maximal
natural setting — `complEDS` is defined for any `CommRing`). The matching mathlib declaration is
stated at exactly the same generality.

---

## 5. Composition check

Trivially composable from mathlib primitives (`≤ 2` steps): unfold `complEDS`, then
`Int.sign_zero : Int.sign 0 = 0` (mathlib `Mathlib/Data/Int/Sign` / core) gives `(0 : ℤ)`, whose
cast is `0` (`Int.cast_zero`), and `zero_mul` closes it. But composition is irrelevant here: the
fully-assembled lemma **already exists in mathlib under the same name**, so the correct action is to
*use it*, not re-derive it.

---

## 6. Verdict and recommended action

**`NO-mathlib-has-it`.**

`complEDS_zero` is present verbatim (same name, same statement, same `@[simp]`, same namespace) in
the mathlib pinned by this repo:
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:436-438`, alongside the identical
`def complEDS`. The NagellLutz file is a stale local fork of that mathlib module. No new
contribution is possible from this declaration; the cleanup action is to **drop the forked
`complEDS`/`complEDS_zero` (and the rest of the duplicated `preNormEDS`…`complEDS` block) and import
the upstream mathlib versions instead.**
