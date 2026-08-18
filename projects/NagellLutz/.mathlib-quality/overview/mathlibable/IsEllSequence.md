# Mathlibable assessment — `IsEllSequence`

**Verdict:** `NO-mathlib-has-it`

**Qualified name:** `IsEllSequence` (declared `def _root_.IsEllSequence` inside `namespace EllSequence`,
so the true fully-qualified name is the root-level `IsEllSequence`).

**Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:135`

---

## 1. The declaration under assessment

In the project file (inside `namespace EllSequence`, with `variable (W : ℤ → R)`, `[CommRing R]`):

```lean
/-- The three-index elliptic relation, obtained by
specializing to `d = 0` in the four-index relation. -/
def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

/-- The proposition that a sequence indexed by integers is an elliptic sequence. -/
def _root_.IsEllSequence : Prop :=
  ∀ m n r : ℤ, Rel₃ W m n r
```

Unfolding `Rel₃`, the statement is:

```
IsEllSequence W ↔ ∀ m n r : ℤ,
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2
```

This is the classical Ward elliptic-sequence relation, over an arbitrary `CommRing R`.

## 2. Mathlib search (five methods)

The decisive method is **direct source read of the file this project forks**.

`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:82` (mathlib pinned in this repo's
`.lake/packages/mathlib`):

```lean
section IsEllDivSequence
variable (W : ℤ → R)

/-- The proposition that a sequence indexed by integers is an elliptic sequence. -/
def IsEllSequence : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2
```

- **Name match:** identical — `IsEllSequence` (mathlib's is root-level; the project re-declares the
  same root-level name via `_root_.IsEllSequence`, which would *collide* on import — confirming the
  project does not import the mathlib EDS file but **forks** it).
- **Signature match:** identical — `(W : ℤ → R)`, `[CommRing R]`, result `Prop`.
- **Body match:** definitionally identical. The project merely factors the relation through the
  intermediate `Rel₃`; `IsEllSequence W` unfolds to exactly the mathlib body, term for term
  (same operands, same sign, same `^2` placement, same `∀ m n r : ℤ`).
- **Context match:** the project file's module docstring, `## Mathematical background`, copyright
  header (David Kurniadi Angdinata, 2024), and `## References` (Ward, *Memoir on Elliptic
  Divisibility Sequences*) are copied verbatim from the mathlib file. mathlib also already carries
  the companion API: `IsDivSequence`, `IsEllDivSequence`, `isEllSequence_id`, `IsEllSequence.smul`,
  etc.

loogle/leansearch on the mathlib index would return the same `IsEllSequence`; no search beyond the
forked source is needed because the match is exact.

## 3. Literature / generality analysis

Ward's defining relation for an elliptic (divisibility) sequence is precisely
`W(m+n) W(m−n) W(r)² = W(m+r) W(m−r) W(n)² − W(n+r) W(n−r) W(m)²` for all integers `m, n, r`, over a
commutative ring. The mathlib definition is already at the **maximal natural generality**: an
arbitrary `CommRing R` and an arbitrary sequence `W : ℤ → R`. There is no weaker typeclass to relax
to (the relation needs `+`, `−`, `*`, `^2`, i.e. a commutative ring), and no index generalisation is
meaningful (the relation is intrinsically `ℤ`-indexed). So even the `YES-but-generalise-first` route
is closed — mathlib's form is the literature-standard, fully general one.

## 4. Composition check

Not applicable as a route to inclusion: this is a `def` of a named predicate, and mathlib already
contains that exact `def`. There is nothing to compose — it is the same definition.

## 5. Why this is a fork, not a contribution

This project (`NagellLutz`, toward Nagell–Lutz / division polynomials / EDS) explicitly forks
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and the `DivisionPolynomial.*` files (per project
context: duplicated General*/PID* tracks). `IsEllSequence` is one of the forked, already-upstream
definitions, re-exposed at root level via `_root_.IsEllSequence` so downstream project code can use
the familiar name while the surrounding `EllSequence` namespace develops the *new* `Rel₃` / `rel₄` /
`net` four-index-relation API (which may itself be mathlibable — but that is a different declaration).
`IsEllSequence` itself adds nothing new over mathlib.

---

## Verdict

**`NO-mathlib-has-it`** — `Mathlib.IsEllSequence` (in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`) is the identical definition, identical
name, identical signature, at identical (maximal) generality. The project's copy is a fork. Drop the
local re-declaration and `import Mathlib.NumberTheory.EllipticDivisibilitySequence` (or unify the
forked file against upstream) instead.
