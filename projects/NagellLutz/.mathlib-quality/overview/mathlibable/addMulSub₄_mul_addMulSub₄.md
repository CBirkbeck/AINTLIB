# Mathlibable assessment — `EllSequence.HaveSameParity₄.addMulSub₄_mul_addMulSub₄`

**Verdict: NO-mathlib-has-it** (more precisely: *NO — it IS mathlib code, currently upstreaming via PR; not a standalone target*)

- **Qualified name:** `EllSequence.HaveSameParity₄.addMulSub₄_mul_addMulSub₄`
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:264`
- **Date:** 2026-06-18

---

## 1. Exact statement and proof (from source)

```lean
namespace EllSequence          -- line 90
section transf                 -- line 202
variable (a b c d : ℤ)
namespace HaveSameParity₄      -- line 216
variable {W a b c d} (same : HaveSameParity₄ a b c d)

variable (W) in
/-- A hybrid product formed by one factor from an `addMulSub` and one from another `addMulSub`. -/
def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)   -- line 261

omit same in
lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub]; ring                                        -- line 264
```

Supporting definition (line 94):
```lean
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)
```

**Qualified name VERIFIED.** Namespace stack: `EllSequence` (l.90) ▸ `HaveSameParity₄` (l.216).
The lemma carries `omit same in`, so despite living in the `HaveSameParity₄` namespace it does
**not** depend on the `same : HaveSameParity₄ a b c d` hypothesis — it is a pure ring identity.
The `HaveSameParity₄.` prefix is purely a namespacing artifact of where it is placed in the file.

**What it says, unfolded.** With `R` a `CommRing` and `W : ℤ → R`, writing the four values
`W((a+b)/2)`, `W((c-d)/2)`, `W((c+d)/2)`, `W((a-b)/2)` (all `Int.tdiv` by 2), the LHS is
`[W((a+b)/2)·W((c-d)/2)] · [W((c+d)/2)·W((a-b)/2)]` and the RHS is
`[W((a+b)/2)·W((a-b)/2)] · [W((c+d)/2)·W((c-d)/2)]`. These are equal by commutativity/associativity
of multiplication — a `ring` rearrangement of a product of four ring elements. There is no
arithmetic on the indices (the `tdiv` arguments are identical on both sides); only the four `W _`
factors get regrouped.

---

## 2. Mathlib search (five methods)

**Is it in mathlib?** The *primitives it is stated over* are not yet in mathlib.

- The pinned mathlib (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`)
  contains **only** `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'`, `preNormEDS`,
  `complEDS₂`, `normEDS`, `complEDS'`, `complEDS`. It has **no** `EllSequence` namespace and **no**
  `addMulSub`, `addMulSub₄`, `rel₄`, `net`, or `HaveSameParity₄`.
- The mathlib file's own "Main statements" section still lists these as **TODO**:
  `* TODO: prove that normEDS satisfies IsEllDivSequence` and
  `* TODO: prove that a normalised sequence ... can be given by normEDS`.
- The project's `EllipticDivisibilitySequence.lean` is a **strictly more advanced fork** of that exact
  mathlib file (identical copyright header — "Copyright (c) 2024 David Kurniadi Angdinata", identical
  module docstring) that *discharges* those TODOs. The whole `EllSequence` block (`addMulSub`, `rel₄`,
  `net`, `HaveSameParity₄`, `addMulSub₄`, `rel₄_transf`, `rel₄_of_oddRec_evenRec`, …) is the
  scaffolding of that proof.
- `loogle`/`leansearch` for `addMulSub` / `addMulSub₄`: no hits (not indexed — not in published mathlib).
  The published `mathlib4_docs` for `EllipticDivisibilitySequence` likewise show none of these names.

**Conclusion of search:** the lemma is **mathlib's own author's code**, sitting in the project as a
fork ahead of master. It is being upstreamed.

---

## 3. Literature / upstream-PR search

- WebSearch surfaced the author's own description: *"an elementary, purely algebraic proof of the
  formula for the nth multiple of a point on an elliptic curve … joint work with David Kurniadi
  Angdinata, and most results are included in a **pull request to Lean's Mathlib in the file
  EllipticDivisibilitySequence.lean**."* This is precisely the development containing
  `addMulSub`/`rel₄`/`addMulSub₄`.
- The mathematics here corresponds to **Stange's elliptic nets** (the `net` definition cites Stange's
  paper explicitly) and Ward's *Memoir on Elliptic Divisibility Sequences* (the file's reference). The
  `rel₄` / `addMulSub` apparatus is an *implementation device* internal to that formalisation, not a
  named theorem in the literature. `addMulSub₄_mul_addMulSub₄` itself is a bookkeeping product-regroup
  step inside `rel₄_transf` (the index-permutation transfer lemma); it has no independent mathematical
  content or name in any source.
- It is a **private/internal helper**, on par with the dozens of `addMulSub_*` micro-lemmas around it
  (`addMulSub_same`, `addMulSub_neg₀/₁`, `addMulSub_abs₀/₁`, `addMulSub_swap`, `addMulSub_even/odd`).

---

## 4. Generality analysis

- The statement is already at maximal natural generality for its primitives: `R` an arbitrary
  `CommRing`, `W : ℤ → R` arbitrary, `a b c d : ℤ` arbitrary, **no** hypotheses (`omit same`).
- But it is *defined in terms of* `addMulSub₄` and `addMulSub`, which are **project-local helper
  definitions that themselves are not (yet) in mathlib**. A lemma cannot be added to mathlib ahead of
  the definitions it mentions. Generalising the assumptions further is impossible (there are none) and
  pointless: the lemma's whole reason to exist is to relate these two specific helper defs.

---

## 5. Composition check (≤ 3 mathlib calls)

- Once `addMulSub₄` and `addMulSub` are unfolded, the goal is a product-of-four-ring-elements
  rearrangement closed by a single `ring` call. The proof is literally `simp_rw [addMulSub₄,
  addMulSub]; ring` — i.e. **definitional unfolding + one `ring`**.
- So for any *consumer* of these definitions, the fact is recovered in one line; it does not warrant a
  named library lemma on its own. It is "composable" trivially, but only against the project-local
  defs, not against current mathlib (which lacks the defs).

---

## Verdict

**NO-mathlib-has-it.**

Rationale: this is not a candidate AINTLIB result at all — it is **upstream mathlib code by mathlib's
own EDS author (David Angdinata)**, living in NagellLutz as a fork of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` that runs ahead of mathlib master, and it is
**already being upstreamed via an open mathlib PR** (the "elementary algebraic group-law" PR).
`addMulSub₄_mul_addMulSub₄` is an internal one-line `ring` helper (a product regrouping) inside the
`rel₄_transf` permutation-transfer proof, defined over the not-yet-merged helpers `addMulSub₄` /
`addMulSub`. It has no independent mathematical content, no literature name, and no standalone value;
it travels with the PR that introduces those definitions, not as an AINTLIB contribution. Nothing to
add or generalise here — the correct action is to let the upstream PR land (and then drop the fork),
not to PR this lemma separately.

(If one insisted on a five-bucket label scoped to "should AINTLIB PR *this lemma* to mathlib": still
**NO** — it is non-extractable from its companion defs and is mathlib's own in-flight code.)
