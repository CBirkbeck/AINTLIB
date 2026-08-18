# Mathlibable assessment — `WeierstrassCurve.natDegree_preΨ'_pos`

- **Verdict:** `NO-mathlib-has-it`
- **Qualified name:** `WeierstrassCurve.natDegree_preΨ'_pos`
- **One-line rationale:** Byte-for-byte copy of an existing mathlib lemma; the project forked the entire module it lives in.

---

## 0. The declaration

`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:251`

```lean
lemma natDegree_preΨ'_pos {n : ℕ} (hn : 2 < n) (h : (n : R) ≠ 0) : 0 < (W.preΨ' n).natDegree := by
  simp_rw [W.natDegree_preΨ' h, Nat.div_pos_iff, zero_lt_two, true_and]
  split_ifs <;> exact Nat.AtLeastTwo.prop.trans <| Nat.sub_le_sub_right (Nat.pow_le_pow_left hn 2) _
```

Context: inside `namespace WeierstrassCurve` (opened at line 55), with
`variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)` (line 57). So the
fully-qualified name is **`WeierstrassCurve.natDegree_preΨ'_pos`** (parsed name VERIFIED
against source — the prompt's tentative name is exactly right).

**Mathematical content.** For a Weierstrass curve `W` over a commutative ring `R`, the
`n`-indexed (ℕ) pre-`Ψ` division polynomial `preΨ' n` has *strictly positive* `natDegree`
whenever `n > 2` and `n` is not a zero-divisor witness (`(n : R) ≠ 0`). It is an immediate
corollary of the exact degree formula `natDegree_preΨ' : (W.preΨ' n).natDegree =
(n² − (if Even n then 4 else 1)) / 2`: for `n ≥ 3` that quantity is `≥ (9−4)/2 = 2 > 0`.
The proof is pure bookkeeping — unfold the degree formula, reduce `0 < _/2` via
`Nat.div_pos_iff`, then bound `n² − 4 ≥ 5 ≥ 2` (resp. `n² − 1`) by monotonicity of squaring.

This is a feeder lemma: its sole purpose is to power `preΨ'_ne_zero`
(`ne_zero_of_natDegree_gt <| W.natDegree_preΨ'_pos hn h`, line 262) and the ℤ-indexed
`natDegree_preΨ_pos` (line 303). It is not a named "Main statement" of the file (the
module docstring's Main-statements list, lines 27–40, does not include it).

---

## 1. Literature search

The object is internal Lean division-polynomial-degree API, not a named theorem in the
mathematical literature. The mathematical fact behind it — that the `n`-th division
polynomial of an elliptic curve has degree `(n²−1)/2` (n odd) / `(n²−4)/2` (n even), and
hence positive degree for `n ≥ 3` — is classical, e.g. Silverman, *The Arithmetic of
Elliptic Curves* (2009), Exercise 3.7 / §III.4 (the module itself cites `[silverman2009]`,
line 44). There is no "positivity of the degree" named result to weigh against; positivity
is a trivial downstream consequence of the degree computation.

- WebSearch (`mathlib WeierstrassCurve natDegree_preΨ' division polynomial degree`) → top
  hit is the official mathlib4 docs page
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`, i.e. the very module
  this project forked. No external/literature source defines a separate "positive-degree"
  lemma; it is library-internal plumbing.

Conclusion of step 1: nothing in the literature suggests a more-general "standard form" of
this micro-lemma. It is glue.

---

## 2. Mathlib search — IT IS ALREADY THERE (verbatim)

The decisive finding. This project **forks** mathlib's division-polynomial tower: it
redefines `preΨ'` (`DivisionPolynomial.lean:76`) and imports its own
`LutzNagell.EllipticDivisibilitySequence` instead of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(stated explicitly in that file's docstring, line 13). The degree file is a copy of
mathlib's `…/DivisionPolynomial/Degree.lean` — **same author and copyright header** (`David
Kurniadi Angdinata`, 2024) in both.

The lemma exists upstream, in the pinned mathlib checkout, at:

`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:254`

```lean
lemma natDegree_preΨ'_pos {n : ℕ} (hn : 2 < n) (h : (n : R) ≠ 0) : 0 < (W.preΨ' n).natDegree := by
  simp_rw [W.natDegree_preΨ' h, Nat.div_pos_iff, zero_lt_two, true_and]
  split_ifs <;> exact Nat.AtLeastTwo.prop.trans <| Nat.sub_le_sub_right (Nat.pow_le_pow_left hn 2) _
```

`diff` of the project lemma (lines 251–253) against the mathlib lemma (lines 254–256):
**IDENTICAL** — same signature, same namespace, same two-line proof, character-for-character.

This was reached by mathlib's exhaustive-search methods:

| Method | Result |
|---|---|
| 1. Exact-name grep in pinned mathlib source | **Hit** — `Degree.lean:254`, identical statement + proof. |
| 2. Name family (`natDegree_preΨ_pos`, `natDegree_ΨSq_pos`, `natDegree_Φ_pos`, `natDegree_Ψ₂Sq_pos`, `natDegree_Ψ₃_pos`, `natDegree_preΨ₄_pos`) | All present upstream (`Degree.lean:81,111,141,302,365,438`) — the **whole `_pos` family** is in mathlib. |
| 3. More-general form | `natDegree_preΨ_pos {n : ℤ}` (`Degree.lean:302`) is the ℤ-indexed generalisation and is **also already upstream** — it is *proved by calling this very lemma* (`using! W.natDegree_preΨ'_pos hn …`, line 305). |
| 4. WebSearch / mathlib4 docs | Confirms the module `…DivisionPolynomial.Degree` is live in mathlib. |
| 5. Consumer match | The downstream `preΨ'_ne_zero` (project 263 / mathlib 263) is also identical, confirming the whole block is a verbatim fork, not an independent reproof. |

There is nothing to add and nothing to generalise: mathlib has both this lemma **and** its
more-general ℤ sibling.

---

## 3. Generality analysis

Moot, because the lemma already exists upstream with this exact signature. For completeness:
the statement is already at the right generality for the ℕ layer — `CommRing R` (no
domain/field assumption), the hypothesis `(n : R) ≠ 0` is exactly what `natDegree_preΨ'`
needs, and `2 < n` is the sharp threshold (`preΨ' 0, preΨ' 1, preΨ' 2` are constants, degree
0). The ℤ-indexed strengthening `natDegree_preΨ_pos` already lives one section down in the
same upstream file. No weakening is available or warranted.

---

## 4. Composition check

Not needed for the verdict (the lemma is present verbatim), but worth recording: even absent
the copy, it is a ≤2-call composition over upstream API —
`Nat.div_pos_iff` + a `Nat.pow`/`Nat.sub` monotonicity bound, on top of the already-upstream
`natDegree_preΨ'` degree formula. That only reinforces "mathlib already has this", since the
formula it rewrites with (`natDegree_preΨ'`) is itself upstream (`Degree.lean:250`).

---

## 5. Verdict — `NO-mathlib-has-it`

`WeierstrassCurve.natDegree_preΨ'_pos` is a **byte-for-byte duplicate** of
`WeierstrassCurve.natDegree_preΨ'_pos` already in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:254` — same name,
same namespace, same statement, same proof, same author. The NagellLutz project forked the
entire `DivisionPolynomial` / `EllipticDivisibilitySequence` subtree (to swap in its own EDS
file), and this lemma rode along inside the copied `Degree` file. Mathlib additionally
already carries the more-general ℤ-indexed `natDegree_preΨ_pos` (`Degree.lean:302`), which is
literally proved *by invoking this lemma*.

**Action for consolidation:** nothing to upstream. When the project's forked
`DivisionPolynomial*` tower is retired in favour of mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` (the standing recommendation
across the sibling reports — see `preΨ₄.md`, `natDegree_preΨ'_le.md`,
`coeff_preΨ'_ne_zero.md`), this declaration and its `_pos` siblings disappear automatically,
re-pointing every call site at the identical upstream names (`WeierstrassCurve.natDegree_preΨ'_pos`,
`…_preΨ_pos`, etc.). No statement, namespace, or dot-notation change at any call site.

### Sources
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html)
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- Pinned local source: `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:254` (mathlib rev `69aaaa313f44`)
- J. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer GTM 106 (division-polynomial degree, §III.4 / Exercise 3.7)
