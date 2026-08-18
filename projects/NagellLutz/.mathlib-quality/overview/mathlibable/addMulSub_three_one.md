# Mathlibable assessment: `EllSequence.addMulSub_three_one`

- **Project:** NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic divisibility sequences)
- **File:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:171`
- **Date:** 2026-06-18
- **Verdict:** **BORDERLINE-needs-human**

## 1. Exact declaration (verified from source)

Qualified name (verified): **`EllSequence.addMulSub_three_one`** (inside `namespace EllSequence`, opened at line 90, closed at line 597).

```lean
lemma addMulSub_three_one : addMulSub W 3 1 = W 2 * W 1 := rfl
```

Context / dependencies:

```lean
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)

namespace EllSequence

/-- The expression `W((m+n)/2) * W((m-n)/2)` is the basic building block of elliptic relations,
where integers `m` and `n` should have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)
```

So `addMulSub W 3 1 = W ((3+1).tdiv 2) * W ((3-1).tdiv 2) = W (4.tdiv 2) * W (2.tdiv 2) = W 2 * W 1`,
which holds by `rfl` (numeral `tdiv` reduces definitionally).

It sits immediately after its sibling `addMulSub_two_zero : addMulSub W 2 0 = W 1 ^ 2 := (sq _).symm`
(line 170), and before the genuinely-used computation lemmas `addMulSub_even` / `addMulSub_odd`
(lines 173, 176).

## 2. Literature search

- Mathlib's upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (Angdinata) defines
  `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'`, `preNormEDS`, `normEDS` and
  carries an explicit **`TODO: prove that normEDS satisfies IsEllDivSequence`**.
  [docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- This project's `EllSequence` namespace is exactly the work-in-progress that discharges that TODO.
  It introduces a *different*, non-recursive formulation built on Stange's **elliptic nets**: the
  building block `addMulSub`, the four-index relation `rel₄`, the net relation `net`, and the
  transfer/permutation machinery. The relevant background is the EDS recursion
  `h_{m+n} h_{m-n} = h_{m+1} h_{m-1} h_n^2 − h_{n+1} h_{n-1} h_m^2`
  (Wikipedia / Ward), realised here through `addMulSub` and `rel₄`.
  [Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- `addMulSub` is a bespoke notational helper of this development; it is **not** a named object in the
  literature. `addMulSub_three_one` is just its value at the index pair `(3, 1)` — a base-case
  arithmetic fact, not a theorem with independent mathematical content.

## 3. Mathlib search (is it there, or a more general form?)

Direct grep over the *pinned* mathlib source tree
(`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib/`):

```
grep -rn "addMulSub" .lake/packages/mathlib/Mathlib/    →  (no matches)
```

- **`addMulSub` does not exist in mathlib at all.** Mathlib's EDS file uses the recursive
  `preNormEDS'` formulation and has none of the `addMulSub` / `rel₄` / `net` / elliptic-nets API.
- Therefore neither this exact lemma nor any "more general form of it" is in mathlib — there is no
  mathlib statement of the shape `addMulSub _ a b = …` to generalise, because the underlying
  definition is absent upstream.
- Repo-wide grep shows `addMulSub` is duplicated only *inside AINTLIB*
  (`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`, def at line 38) and in
  this project's own `EllipticDivisibilitySequenceOriginal.lean` baseline — i.e. it is a within-repo
  fork, not a mathlib decl.

Index tools (`lean_loogle`/`lean_leansearch`) were unavailable in this environment, but a grep over
the actual pinned mathlib source is strictly stronger evidence than the index for an
absent-symbol question.

## 4. Generality analysis

The statement is already at full generality for what it is: `W : ℤ → R`, `R` an arbitrary
`CommRing`. There is nothing to weaken. The lemma is a *specialisation* (fixed numerals `3`, `1`),
the opposite of a generality opportunity — its general parents are `addMulSub_even` /
`addMulSub_odd`, which compute `addMulSub` on all even/odd argument pairs and which this lemma is a
trivial instance of (`addMulSub_odd` with `m = 1, n = 0` gives `addMulSub W 3 1 = W 2 * W 1`).

## 5. Composition check (≤ 3 mathlib calls)

Not applicable in the usual sense, because the symbol `addMulSub` is not in mathlib, so mathlib
primitives cannot even state it. *Within the development*, the lemma is `rfl`, and is also an
immediate instance of the existing `addMulSub_odd`. As a piece of mathlib-bound API it carries no
standalone content: it is a definitional unfolding of a private auxiliary definition at one numeral
pair.

## 6. Usage

`grep -rn "addMulSub_three_one"` over the whole repo: **zero call sites** (likewise
`addMulSub_two_zero`). The lemma is currently unused dead convenience API. The actually-used
computation lemmas are `addMulSub_even` and `addMulSub_odd`.

## 7. Verdict and rationale

**BORDERLINE-needs-human.**

This is not a "mathlib already has it" case (mathlib has no `addMulSub`), nor a clean
"composable-from-mathlib" case (mathlib cannot even express the statement). It is a **trivial `rfl`
unfolding of a project-private auxiliary definition** that is, on top of that, **unused**.

Its mathlib fate is entirely parasitic on a larger, human-level packaging decision: whether the
whole `EllSequence` elliptic-nets development (the machinery proving `normEDS` is an EDS — the
upstream `EllipticDivisibilitySequence` TODO) is upstreamed, and in what shape. If that development
goes to mathlib, a base-case fact like `addMulSub W 3 1 = W 2 * W 1` would at most travel as a small
(likely `private` / `rfl`) helper alongside `addMulSub`, and only if a proof actually needs it —
which, given zero current uses, it does not. As a standalone declaration it is below the mathlib
bar. That "depends on a bigger upstreaming/packaging call + currently unused" character is exactly
what BORDERLINE-needs-human is for.

Recommendation for the human: do **not** PR this lemma on its own. Treat it as part of the
`EllSequence`/elliptic-nets contribution; if that contribution is prepared for mathlib, drop unused
base-case unfoldings like `addMulSub_three_one` (and `addMulSub_two_zero`) unless a proof requires
them, in which case inline them as `rfl` or derive them from `addMulSub_odd`/`addMulSub_even`.

## Sources

- [Mathlib.NumberTheory.EllipticDivisibilitySequence (docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic (docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Stange, "The sign of an elliptic divisibility sequence" (arXiv:math/0402415)](https://arxiv.org/pdf/math/0402415)
