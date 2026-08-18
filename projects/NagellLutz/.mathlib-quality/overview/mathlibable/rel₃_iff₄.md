# Mathlibable assessment — `EllSequence.rel₃_iff₄`

**Verdict: `YES-add-as-is`** (ships as part of the `rel₄`-API bundle, not as an isolated cherry-pick)

- **Qualified name:** `EllSequence.rel₃_iff₄`
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:307`
- **Date:** 2026-06-18

---

## 1. The declaration

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  rw [rel₄, ← mul_zero 2, Rel₃]
  simp_rw [addMulSub_even, add_zero, sub_zero]
  convert sub_eq_zero.symm using 2; ring
```

Qualified name **verified**: line 307 sits inside `namespace EllSequence` (lines 90–597) and is
*not* inside the `transf` section (202–299) nor any sub-namespace, so the full name is
`EllSequence.rel₃_iff₄` (the prompt's guess was correct).

Supporting project-local definitions:

- `Rel₃ W m n r` (line 130) — the three-index elliptic relation
  `W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`. This is **exactly the body of
  mathlib's `IsEllSequence`** (`IsEllSequence W = ∀ m n r, Rel₃ W m n r`).
- `rel₄ W a b c d` (line 103) — a new, fully permutation-symmetric four-index relation
  `addMulSub a b · addMulSub c d − addMulSub a c · addMulSub b d + addMulSub a d · addMulSub b c`.
- `addMulSub W m n = W((m+n).tdiv 2) · W((m−n).tdiv 2)` (line 94) — the basic building block;
  `addMulSub_even` (line 173) gives `addMulSub (2m) (2n) = W(m+n)·W(m−n)`.

**Mathematical content:** the three-index elliptic relation at `(m,n,r)` is equivalent to the
four-index relation vanishing at the doubled, zero-padded tuple `(2m, 2n, 2r, 0)`. It is the bridge
that lets the symmetric `rel₄` machinery (permutation lemmas, `transf`, `rel₆_eq₃`/`rel₆_eq₁₀`
recurrences) be applied to ordinary EDS recurrences. Proof is a pure unfold-of-two-custom-defs plus
`ring`.

**Role in the development:** load-bearing internal step. Used at line 499 inside the main inductive
proof `rel₄_of_anti_oddRec_evenRec` (converting `OddRec`/`Rel₃` facts into `rel₄ = 0` facts), and
again at `EllipticDivisibilitySequenceOriginal.lean:476`. Duplicated verbatim in the HasseWeil copy
(`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:151`) — i.e. it is shared
infrastructure, not a one-off.

## 2. Literature search

- **PRIMARY SOURCE — Junyan Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280v1
  (8 Apr 2026).** This is the paper behind this exact fork. It explicitly proves: *"a three-index
  relation for elliptic sequences holds if and only if a corresponding four-index relation vanishes
  at doubled indices with one index set to zero"* — verbatim `rel₃_iff₄`. The paper generalises EDS
  from fields/ℤ to **arbitrary commutative rings** and states the work is **formalised in Lean 4 /
  mathlib, extending the existing `EllipticDivisibilitySequence`**. (The file's copyright author is
  David Kurniadi Angdinata, who wrote mathlib's original EDS file; Junyan Xu is a mathlib
  maintainer.) The `tdiv`-based `addMulSub` and unconditional sign lemmas are exactly the
  commutative-ring-generality devices the paper describes.
- Ward (*Memoir on EDS*, 1948) — original three-index EDS recurrence (the `Rel₃` form).
- Stange (*Elliptic nets and elliptic curves*, arXiv:0710.1316) — elliptic nets are the higher-rank
  generalisation governed by a **four-index** recurrence; the file's `net` / `rel₄` follow Stange's
  four-index relation (the docstring on `net` cites Stange). The three-index ⇔ four-index passage is
  the standard rank-one specialisation, here made an explicit Lean lemma.

So the statement is a **named, published result** in the source paper, at the same (commutative-ring)
generality as the formalisation.

## 3. Mathlib search (five methods)

mathlib pin: `.lake/packages/mathlib` (d90090f). Searched the on-disk source *and* the published
docs.

- **Local source grep** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines):
  defines only `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'/preNormEDS`,
  `complEDS₂`, `normEDS`, `complEDS'/complEDS`, the `*Rec` recursors and the `map_*` lemmas. **No**
  `addMulSub`, `rel₄`, `Rel₃`, `net`, `rel₆`, `rel₃_iff₄`, or `HaveSameParity₄`.
- **Published docs fetch** (mathlib4_docs, same file): confirmed — none of `rel₄`, `Rel₃`,
  `addMulSub`, `net`, `rel₆`, `rel₃_iff₄`, `HaveSameParity₄`, and **no** three-index⇔four-index
  equivalence lemma present.
- **Repo-wide grep**: every `rel₄`/`rel₃_iff₄` hit is inside the two project forks (NagellLutz +
  HasseWeil); none in `.lake/packages/mathlib`.
- `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` builds *on top of* `normEDS`; it
  does not introduce a `rel₄`/`Rel₃` bridge either.
- WebSearch for the names surfaced only the mathlib docs page (the un-forked file) and the source
  arXiv papers.

**Conclusion:** mathlib does **not** currently contain this lemma, nor the `rel₄`/`Rel₃` objects it
relates. It is unupstreamed (but mathlib-destined) API.

## 4. Generality analysis

Already at **maximal generality**:

- Base ring is an arbitrary `CommRing R` (with a `RingHomClass` map only used elsewhere in the file)
  — the broadest setting in the source paper. No field, domain, or characteristic hypothesis is
  imposed, and none is needed: the proof is `simp_rw [addMulSub_even, …]; ring`.
- The indices are arbitrary integers `m n r` with no parity/sign side-conditions (the `2*·`/`0`
  padding makes the same-parity requirement automatic), so the iff is unconditional.

There is no weaker hypothesis set or more general carrier to move to. The statement matches the
paper's form exactly.

## 5. Composition check (≤3 mathlib calls?)

**No** — and not because it is hard, but because the *objects do not exist in mathlib*. `rel₄`,
`Rel₃`, and `addMulSub` are project-local definitions absent from mathlib, so there is nothing in
mathlib to compose: you cannot even *state* `rel₃_iff₄` against the current mathlib API without first
adding those three definitions. Once they are added, this lemma is a 4-line unfold + `ring`; but that
is the normal shape of an API gluing lemma, not evidence that mathlib already subsumes it.

## 6. Verdict

**`YES-add-as-is`.**

- It is a published result (Xu, arXiv:2604.05280) explicitly slated for mathlib, formalising an
  extension of mathlib's own `EllipticDivisibilitySequence` file.
- It is absent from mathlib today (verified against both the on-disk pin and the live docs).
- It is already at the maximal (arbitrary commutative ring, unconditional) generality of its source,
  so **no generalisation is required** — hence `YES-add-as-is` rather than `YES-but-generalise-first`.
- It is genuinely necessary infrastructure (the `Rel₃`↔`rel₄` bridge powering the whole symmetric
  four-index proof of `isEllDivSequence_normEDS`), not redundant or trivially eliminable.

**Caveat for the human integrator (the only nuance, not a downgrade):** `rel₃_iff₄` must travel with
its definitions — `Rel₃`, `rel₄`, `addMulSub` (+ `addMulSub_even`) — and ideally the surrounding
`rel₄` API. It is meaningless cherry-picked in isolation. This is the standard "lemma ships with its
API" situation, expected for any component of a coherent contribution, and does not move it off
`YES-add-as-is`. Practically, the cleanest path is to let the upstream Xu/Angdinata PR series land
this whole layer rather than to PR this single lemma standalone.

### Sources
- Junyan Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280v1 (2026).
- M. Ward, *Memoir on Elliptic Divisibility Sequences* (1948).
- K. Stange, *Elliptic nets and elliptic curves*, arXiv:0710.1316.
- mathlib docs: `Mathlib.NumberTheory.EllipticDivisibilitySequence` (no `rel₄`/`Rel₃`/`rel₃_iff₄`).
