# Mathlibable assessment: `normEDS`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `normEDS` (top-level; no enclosing namespace — defined inside `section NormEDS`)

**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:890`

---

## 1. The declaration

```lean
section NormEDS
variable {R : Type u} [CommRing R]
variable (b c d : R)

/-- The canonical example of a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.

This is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`. -/
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1
```

The canonical construction of a normalised elliptic divisibility sequence `W : ℤ → R`
over a commutative ring `R`, from initial data `b c d : R`, built on the auxiliary
sequence `preNormEDS (b^4) c d` (even terms carry an extra factor of `b`). Initial
values `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d*b`.

## 2. Literature search

`normEDS` / `preNormEDS` are the standard Lean encoding of the classical normalised EDS
of Ward / Shipsey / Stange (see the Wikipedia "Elliptic divisibility sequence" article and
Stange's work, plus the recent arXiv "On Elliptic Sequences over Commutative Rings"
2604.05280). The recurrence is the textbook EDS recursion; the `preNormEDS`/`normEDS`
split (pulling the even-term factor of `b` into a separate auxiliary so the recursion
stays polynomial over a general `CommRing`) is precisely how mathlib formalises it. This
is not a project-original construction — it is the established literature object, already
formalised upstream.

## 3. Mathlib search — IT IS ALREADY IN MATHLIB (verbatim)

This project **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence`, and `normEDS`
is a direct, unmodified copy of the mathlib definition.

mathlib source: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:289`

```lean
section NormEDS

/-- The canonical example of a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.

This is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`. -/
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1
```

The match is **character-for-character identical**:
- Same body: `preNormEDS (b ^ 4) c d n * if Even n then b else 1`.
- Same signature: `(n : ℤ) : R` under `variable {R : Type u} [CommRing R]` and
  `variable (b c d : R)`.
- Same section name (`NormEDS`), same docstring, same qualified name (top-level `normEDS`,
  no namespace).
- Same surrounding API in both files: `normEDS_ofNat`, `normEDS_zero`, `normEDS_one`,
  `normEDS_two`, `normEDS_three`, `normEDS_four`, `normEDS_neg`, `normEDS_odd`,
  `normEDS_even`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`.
- Same upstream author (David Kurniadi Angdinata, per the Apache copyright header carried
  in both files).

The mathlib module docstring lists `normEDS` as one of its Main definitions, and the
mathlib docs page (leanprover-community.github.io/mathlib4_docs) documents it.

## 4. Generality analysis

No gap. The mathlib definition is already at the maximal natural generality: an arbitrary
`CommRing R` with `n : ℤ`. The project copy uses the identical typeclass assumption
(`[CommRing R]`) and identical signature — there is nothing to weaken or generalise. They
are the same definition.

## 5. Composition check

Not applicable in the "compose from primitives" sense — this is a `def` that *is* the
mathlib primitive, not a derived lemma. It already exists upstream verbatim, so the correct
action is to delete the fork and `import`/use `Mathlib.NumberTheory.EllipticDivisibilitySequence.normEDS`
directly.

## 6. Why this exists in the project

The header of the project file notes it forks parts of mathlib's EDS / division-polynomial
machinery. The fork carries extra downstream API the Nagell–Lutz development needs (e.g.
`complEDS₂`, `complEDS`, `normEDS_mul_complEDS₂`, the `Map`/`Param` sections, plus
`IsEllSequence.normEDS_of_mem_nonZeroDivisors`). `normEDS` itself is just dragged along by
the fork; it is the unchanged upstream definition.

> Note: mathlib still has TODOs (lines 44–45 of the mathlib file) to prove `normEDS`
> satisfies `IsEllDivSequence` and the converse. Those *theorems* (e.g. the project's
> `isEllDivSequence_normEDS`) may be genuinely mathlib-worthy and are assessed separately —
> but the **definition** `normEDS` is already upstream.

## Verdict

**NO-mathlib-has-it** — `normEDS` is a verbatim copy of
`Mathlib.NumberTheory.EllipticDivisibilitySequence.normEDS`. Drop the fork and use the
mathlib definition directly.
