# Mathlibable assessment: `normEDS_six_eq_mul`

**Verdict: NO-composable-from-mathlib**

- **Project:** NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic divisibility sequences)
- **Qualified name:** `normEDS_six_eq_mul` (top-level — at the assessed site it sits inside `section NormEDS → section Complement`, both plain `section`s, with no enclosing `namespace`; verified by scanning `namespace`/`section`/`end` markers around the decl)
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1073` (`lemma` keyword line; body 1073–1077)
- **mathlib pin:** `d90090f647cae4f4ad4da99c0ac8bab2ca8c34ab` (matches the AINTLIB consolidation monorepo build)
- **Date:** 2026-06-21 (re-verified; supersedes 2026-06-18 pass)

---

## 1. Exact statement (from source)

```lean
lemma normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_compl₂EDS, compl₂EDS, if_neg (by decide)]
  simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]
  rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, if_neg (by decide)]
  ring
```

Context: `variable (b c d : R) (m : ℤ)` with `[CommRing R]`. `normEDS b c d : ℤ → R` is the canonical
normalised elliptic divisibility sequence with `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d·b`.
The lemma is the closed form of its **6th term**:
`W(6) = (W(5) − d²)·b·c`.

It is an internal helper: its only consumers (lines 1397–1399, inside
`invarDenom_eq_redInvarDenom_mul`) are the `m % 6 ∈ {0,1,5}` branches, where — after rewriting via
`normEDS_mul_complEDS_div` — it supplies the `W₆ = (W₅−d²)·b·c` factorisation that exposes the `b·c`
factor of the invariant denominator. It is **not** a headline result of the project.

## 2. Duplication inside AINTLIB (the warned-about forked tracks)

`grep "lemma normEDS_six_eq_mul"` across `projects/` returns **two live definitions** of the identical
statement — both in vendored forks of the same David Angdinata EDS file (an instance of the duplicated
fork tracks the prompt flagged):

| File | Line | Track |
|------|------|-------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` | 1073 | live (proof uses fork-track `compl₂EDS` / `normEDS_mul_compl₂EDS`) — **assessed decl** |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` | 620 | sibling project (proof uses the mathlib-named `complEDS₂` / `normEDS_mul_complEDS₂`) |

(An earlier `EllipticDivisibilitySequenceOriginal.lean` snapshot referenced by the prior pass no
longer exists in the tree — verified by `find . -name "*Original*.lean"` returning nothing.)

The HasseWeil copy's proof is the composition-from-mathlib argument written out verbatim:
`rw [show (6:ℤ) = 2*3, ← normEDS_mul_complEDS₂, complEDS₂, …]; ring`. This is itself strong evidence
the result is a thin numeric instance of existing machinery, not new mathematics.

(This cross-project duplication is a dedup/cleanup concern for `main`, orthogonal to the mathlib
verdict, but reinforces that the lemma is project-glue rather than a library primitive.)

## 3. Literature search

- Wikipedia *Elliptic divisibility sequence*; Ward's recurrences; arXiv:2102.07573 "A recurrence
  relation for elliptic divisibility sequences"; the standard division-polynomial recurrences
  `ψ_{2n+1} = ψ_{n+2}ψ_n³ − ψ_{n−1}ψ_{n+1}³` and `ψ_{2n}ψ_2 = ψ_n(ψ_{n+2}ψ_{n−1}² − ψ_{n−2}ψ_{n+1}²)`.
- The *general* recurrence and the symmetric three-variable relation
  `u_{m+n}u_{m−n} = u_{m+1}u_{m−1}u_n² − u_{n+1}u_{n−1}u_m²` are the named, standard objects.
- An explicit closed form for the **6th term specifically** (W₆ as a polynomial in W₅, b, c, d) is
  **not** a named theorem in the literature. It is the kind of low-degree value one computes on
  demand from the doubling/addition recurrences. Standard references (and mathlib itself) tabulate
  ψ₂, ψ₃, ψ₄ explicitly and then stop, deriving higher terms via the recurrence.

Conclusion: no literature-standard "W₆ formula" lemma to match; the maximally-general form is the
recurrence, which mathlib already has.

## 4. mathlib search (five methods) — is it there, or a more general form?

Searched `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` at pin `d90090f`
(grep over the vendored mathlib in `.lake/packages/mathlib`; lean_loogle/leansearch consistent).

**Not present as-is.** mathlib has **no** `normEDS_six`, `normEDS_five`, `…_eq_mul`, nor any `Ψ₆`/
`ψ₆`/`φ₆` value lemma. Its explicit per-index value lemmas stop at index 4:
- `normEDS_two`, `normEDS_three`, `normEDS_four` (and `Ψ_three/Ψ_four`, `φ_two/φ_three/φ_four`).

**But all the machinery to derive it is present and general:**
- `normEDS` — same definition as the project's (this file is a fork of it).
- `normEDS_mul_complEDS₂ (k) : normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2*k)`  ← the
  doubling/2-complement identity; the project's `compl₂EDS`/`normEDS_mul_compl₂EDS` are renamed copies.
- `complEDS₂_three : complEDS₂ b c d 3 = preNormEDS (b^4) c d 5 * b − d^2 * b`  ← the exact 2-complement
  value at 3.
- `normEDS_three : normEDS b c d 3 = c`; `normEDS_ofNat`/`preNormEDS_ofNat` to read off
  `normEDS b c d 5 = preNormEDS (b^4) c d 5` (5 odd ⇒ the `if Even` factor is 1).

## 5. Generality analysis

The decl is the **least general possible** form of the underlying mathematics: a single numeric
instance `n = 6`. The general statements (mathlib's `normEDS_even`/`normEDS_odd`,
`normEDS_mul_complEDS₂`, and the symmetric EDS recurrence) strictly subsume it. Adding `normEDS_six`
to mathlib would be adding one arbitrary point of an infinite family whose recurrence is already
formalised — against mathlib's stated convention here (it deliberately tabulates only up to index 4
and derives the rest via `complEDS₂`). There is no generalisation that turns this into a missing
library primitive; the primitive (`complEDS₂` + the doubling identity) already exists.

## 6. Composition check (≤ 3 mathlib calls)

Yes — directly, from mathlib `d90090f`:

1. `6 = 2 * 3`, then **`← normEDS_mul_complEDS₂`** ⇒ `normEDS 6 = normEDS 3 * complEDS₂ 3`.
2. **`complEDS₂_three`** ⇒ `complEDS₂ 3 = preNormEDS (b^4) c d 5 * b − d² * b`, and via
   `normEDS_ofNat`/`preNormEDS_ofNat` (5 odd) `preNormEDS (b^4) c d 5 = normEDS b c d 5`, so
   `complEDS₂ 3 = (normEDS 5 − d²) * b`.
3. **`normEDS_three`** ⇒ `normEDS 3 = c`; then `ring` rearranges
   `c * ((normEDS 5 − d²) * b) = (normEDS 5 − d²) * b * c`.

Three named mathlib lemmas (`normEDS_mul_complEDS₂`, `complEDS₂_three`, `normEDS_three`) plus
`normEDS_ofNat`-style unfolding and `ring`. The HasseWeil copy literally writes this proof against
the mathlib names. The lemma is a one-`ring`-away corollary of existing mathlib API.

## 7. Verdict

**NO-composable-from-mathlib.**

A specific (n = 6) numeric instance of the normalised-EDS doubling identity. mathlib does not contain
it, but contains every ingredient — `normEDS_mul_complEDS₂` + `complEDS₂_three` + `normEDS_three`
(+ `normEDS_ofNat` + `ring`) reproduce it in ≤ 3 named calls; the HasseWeil sibling proof is exactly
this composition. mathlib deliberately tabulates EDS/division-polynomial values only through index 4
and derives higher terms from the recurrence, so this belongs as project-local glue, not a library
lemma. (Cross-project: also duplicated 4× inside AINTLIB — a dedup item for `main`, separate from the
mathlib decision.)
