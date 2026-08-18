# Mathlibable assessment: `EllSequence.rel₃_iff_oddRec`

**Verdict: BORDERLINE-needs-human**

> One-line rationale: Not in mathlib; trivial `ring` glue between two project-only defs (`Rel₃`/`OddRec`) — belongs in mathlib only *with* the whole new `EllSequence` framework, which a human should adopt.

---

## 1. The declaration

- **Qualified name:** `EllSequence.rel₃_iff_oddRec`
  (base `rel₃_iff_oddRec`, inside `namespace EllSequence` opened at line 90, closed at line 597 — verified).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:363`
- **Signature & proof:**
  ```lean
  lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
    rw [Rel₃, OddRec]; ring
  ```
- **Context:** `variable {R : Type u} [CommRing R] (W : ℤ → R)`.

The two sides are **both project-local definitions**:
- `Rel₃ W m n r : Prop` (line 130):
  `W (m+n) * W (m-n) * W r ^ 2 = W (m+r) * W (m-r) * W n ^ 2 - W (n+r) * W (n-r) * W m ^ 2`
  — the three-index elliptic relation, i.e. `d = 0` case of the four-index `rel₄`.
- `OddRec W m : Prop` (line 355):
  `W (2*m+1) * W 1 ^ 3 = W (m+2) * W m ^ 3 - W (m-1) * W (m+1) ^ 3`
  — the recurrence defining the **odd** terms of an elliptic sequence.

So the lemma says: the general 3-index elliptic relation at indices `(m+1, m, 1)` is, up to a `ring` normalisation, exactly the odd-term recurrence. It is one of a family of glue lemmas:
`rel₃_iff_oddRec`, `rel₃_iff_evenRec`, `rel₄_iff_evenRec` (lines 363–379).

**Downstream uses (load-bearing, not dead glue):**
- line 500 — inside a `normEDSRec'`-style construction (`(rel₃_iff_oddRec W m).mpr <| oddRec _ …`),
- line 650 — `lemma oddRec (m) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)`.

---

## 2. Literature search

- **Standard EDS recurrence (Ward):**
  `W(n+m) W(n-m) = W(n+1) W(n-1) W(m)^2 - W(m+1) W(m-1) W(n)^2`.
  Division polynomials of an elliptic curve, evaluated at a point, satisfy it
  (Ward, *Memoir on Elliptic Divisibility Sequences*; Wikipedia "Elliptic divisibility sequence").
- **The "odd recurrence"** `W(2m+1) W(1)^3 = W(m+2) W(m)^3 - W(m-1) W(m+1)^3` is the classical
  specialisation used to compute **odd-index** division polynomials/EDS terms — entirely standard.
  So `OddRec` is a *literature-standard object*, and the lemma is the (algebraically trivial)
  statement that the project's symmetric relation specialises to it.
- **Framework provenance:** the broader `EllSequence` machinery here (`addMulSub`, `rel₄`, `net`
  = Stange's elliptic nets, `rel₆`, `rel₆_eq₁₀`, `Rel₄OfValid`, …) matches the very recent
  arXiv:2604.05280 *"On Elliptic Sequences over Commutative Rings"* (June 2026), which explicitly
  acknowledges D. K. Angdinata (the file's author) for the division-polynomial motivation. This is
  **new research, freshly formalised** — not yet in mathlib.

Sources:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- https://arxiv.org/pdf/2102.07573 (a recurrence relation for EDS)
- https://arxiv.org/abs/2604.05280 (On Elliptic Sequences over Commutative Rings)
- https://arxiv.org/pdf/0710.1316 (Stange, Elliptic nets and elliptic curves)

---

## 3. Mathlib search (5 methods)

Searched the **pinned mathlib** (`.lake/packages/mathlib`, the same build this project forks) and the
published docs:

1. **Exact name** `rel₃_iff_oddRec` — 0 hits anywhere in mathlib.
2. **Both sides' definitions** — `Rel₃`, `OddRec`, `rel₄`, `addMulSub`, `net`, `EvenRec`,
   `namespace EllSequence`: **0 hits** in mathlib (`grep -r` over `.lake/packages/mathlib/`).
3. **The whole EDS file** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines):
   defines only the **older** API — `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`,
   `preNormEDS(')`, `complEDS₂`, `normEDS`, `complEDS(')`, `normEDSRec`, `map_*`. No `Rel₃`/`OddRec`
   predicates, no `iff` bridging lemma, no recurrence-as-Prop at all.
4. **Published mathlib4 docs** (web): confirmed the live module contains **none** of the framework
   names. (WebFetch of the doc page returned "None of the following appear".)
5. **The forks in this monorepo** both reproduce it verbatim — `HasseWeil/.../EllipticDivisibilitySequence.lean:288`
   and `NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:349` — confirming this is a
   **project-track lemma duplicated across forks**, *not* something pulled from upstream mathlib.

**Conclusion of search:** mathlib does **not** have this lemma, and *cannot* state it today —
both sides of the iff are project-private definitions absent from upstream. So this is firmly
**NOT** `NO-mathlib-has-it`.

---

## 4. Generality analysis

- Hypotheses are already maximal in the obvious axis: `W : ℤ → R` over an arbitrary `CommRing R`,
  no nonzero-divisor / domain / characteristic assumptions. Nothing to weaken.
- The statement is intrinsically tied to two bespoke definitions; there is no "more general form"
  to target — it is the canonical bridge for *these* two predicates.
- It is the right, named, reusable lemma **within** the `EllSequence` framework (used twice
  downstream). It is not over-specialised relative to that framework.

---

## 5. Composition check (≤ 3 mathlib calls?)

- The proof is literally `rw [Rel₃, OddRec]; ring` — two definitional unfoldings plus `ring`.
- **In isolation, given the two definitions, it is reproducible in one `ring` call** — i.e. it *is*
  "composable from primitives". This is the hallmark of `NO-composable-from-mathlib`.
- **BUT** it is *not* composable from **current** mathlib: the primitives it bridges (`Rel₃`,
  `OddRec`) do not exist upstream. Composability only holds *inside the new framework*, which is the
  thing that would have to land first.

---

## 6. Five-bucket verdict

| Bucket | Fit |
|---|---|
| YES-add-as-is | ✗ — meaningless without the `EllSequence` framework; not a self-contained result. |
| YES-but-generalise-first | ✗ — already maximally general; generalisation is not the issue. |
| NO-mathlib-has-it | ✗ — verified absent from pinned mathlib **and** published docs. |
| NO-composable-from-mathlib | ✗ *as stated* — the `ring` reproof needs `Rel₃`/`OddRec`, which **aren't in mathlib**. Composability holds only once the framework is upstream. |
| **BORDERLINE-needs-human** | **✓** |

**Why BORDERLINE.** The correct *unit of contribution* is not this lemma but the entire new
`EllSequence` algebraic framework (`addMulSub`/`rel₄`/`Rel₃`/`net`/`OddRec`/`EvenRec`/`normEDSRec'`),
which is active, recently-published research (arXiv:2604.05280, Angdinata) that plausibly supersedes
mathlib's current EDS file. Within that framework `rel₃_iff_oddRec` is a small, load-bearing, well-
named bridging lemma that absolutely should travel **with** the framework. In isolation it is
trivial `ring` glue and would never be added alone. The genuine decision — *adopt this framework
into mathlib (likely replacing/extending the existing EDS API), and if so carry this lemma along* —
is a human/maintainer call about API direction, not a mechanical one. Hence **BORDERLINE-needs-human**.

**Recommended action:** do not PR this lemma standalone. Track it as part of an "upstream the
`EllSequence`/elliptic-net framework to `Mathlib.NumberTheory.EllipticDivisibilitySequence`" effort
(coordinate with the file's author D. K. Angdinata, since this is his code and his paper). If/when
the framework lands, this lemma goes in as-is.
