# Mathlibable assessment — `IsEllDivSequence.eq_normEDS`

**Project:** NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic divisibility sequences)
**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1280`
**Assessed:** 2026-06-21

## Verdict

> **YES-add-as-is** — this is precisely mathlib's own open TODO (the EDS normalisation
> characterization); it is correctly and generally stated.

One caveat, recorded below: it must land together with its workhorse `IsEllSequence.eq_normEDS_of_dvd`
and the `IsEllSequence.ext` engine (also absent from mathlib, also forked-from-mathlib infrastructure
living in this same file). That is a packaging note, not a "generalise first" blocker.

---

## 1. The declaration

Verified qualified name (line 1280): **`IsEllDivSequence.eq_normEDS`** (the prompt's parsed name is correct).

```lean
omit ellW ellU one dvd₁₂ dvd₁₃ dvd₂₄ in
/-- An EDS whose second term is not a zero divisor
is a constant multiple of a normalised EDS. -/
theorem IsEllDivSequence.eq_normEDS (h : IsEllDivSequence W) :
    ∃ b c d, W = (W 1 * normEDS b c d ·) :=
  h.1.eq_normEDS_of_dvd two (h.2 _ _ ⟨2, by ring⟩) (h.2 _ _ ⟨3, by ring⟩) (h.2 _ _ ⟨2, by ring⟩)
```

Ambient context (section variables): `W : ℤ → R`, `[CommRing R]`, and a section hypothesis
`two : W 2 ∈ R⁰` (the second term is a non-zero-divisor). The `IsDivSequence` factor of `h`
supplies the divisibilities `W 1 ∣ W 2`, `W 1 ∣ W 3`, `W 2 ∣ W 4` (instantiated via `⟨2,…⟩`,
`⟨3,…⟩`, `⟨2,…⟩`), and the theorem delegates to the real workhorse:

```lean
theorem IsEllSequence.eq_normEDS_of_dvd : ∃ b c d, W = (W 1 * normEDS b c d ·)   -- line 1271
```

which builds the `b,c,d` from the three divisibilities, derives `W 1 ∈ R⁰` from
`W 1 ∣ W 2 ∈ R⁰`, and closes the goal with `IsEllSequence.ext` — a ~15-line induction
(line 1217) via `normEDSRec` over the even/odd recursive structure of normalised EDS, using
non-zero-divisor cancellation (`mul_cancel_right_mem_nonZeroDivisors`).

**Mathematical content.** Every elliptic divisibility sequence `W` (with `W 2` a non-zero-divisor)
is `W(1)` times a *normalised* EDS `normEDS b c d`. Equivalently: an EDS is determined up to the
constant `W(1)` by the three parameters `(b,c,d) = (normalised W2, W3, W4/W2)`, and `W/W(1)` is the
canonical normalised sequence. This is the converse/characterization direction of the EDS theory.

This file is the forked copy of `Mathlib.NumberTheory.EllipticDivisibilitySequence`; the project file
is 1672 lines vs mathlib's 547, and has **strengthened** the surrounding API (see §4).

## 2. Literature search

- **Wikipedia, "Elliptic divisibility sequence":** "A divisibility sequence `(Dₙ)` is *normalized*
  if `D₀ = 0` and `D₁ = 1`. A divisibility sequence may be normalized by replacing `Dₙ` with
  `Dₙ/D₁`." — This is *exactly* `eq_normEDS`: `W = W(1) · (W / W(1)) = W(1) · normEDS`.
- **M. Ward, *Memoir on Elliptic Divisibility Sequences*** (the reference cited in both the project
  and the mathlib file header) is the classical source: an EDS is determined by its initial terms,
  and the normalised representative is canonical.
- **Silverman–Stephens, "The sign of an elliptic divisibility sequence" (arXiv:math/0402415)** and
  the general EDS literature treat the normalisation `Wₙ ↦ Wₙ/W₁` as standard bookkeeping.

Conclusion: the statement is a **standard, attributed, literature-grade** result — the canonical
normalisation lemma of EDS theory, not an ad-hoc project artifact.

## 3. Mathlib search (five-method, decisive subset)

The mathlib index tools (`lean_loogle` / `lean_leansearch`) were unavailable this session, so the
search was done directly against the pinned mathlib *source* in `.lake/packages/mathlib`, which is
authoritative (full-text), plus the live mathlib docs via WebSearch.

| Method | Result |
|---|---|
| Full-package grep `eq_normEDS` / `eq_normEDS_of_dvd` over all of `.lake/packages/mathlib` | **no matches** |
| Enumerate every `normEDS` / `IsEllDivSequence` / `IsDivSequence` lemma in mathlib's EDS file | only the *forward* facts and recursors; **no characterization / converse lemma** |
| `EllipticCurve/DivisionPolynomial/*` (Basic, Degree) for `eq_normEDS` / `IsEllDivSequence` | **no matches** |
| Live mathlib4 docs (WebSearch) | docs page lists exactly the two open TODOs (below); the summary states the characterization "may not yet be fully formalized in Mathlib4" |
| nLab / Stacks | n/a — elementary, not categorical |

**Decisive finding.** Mathlib's own `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
records this as an explicit open TODO in its module docstring:

```
## Main statements
* TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
* TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.   ← line 45
```

`IsEllDivSequence.eq_normEDS` **is** that second TODO. Mathlib has the *definitions*
(`IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `normEDS`, the recursors) but **not** this
theorem. It is a genuine gap mathlib has flagged for itself.

## 4. Generality analysis

Stated at the literature-maximal generality, and in places **more general than current mathlib**:

- **Ring:** arbitrary `CommRing R` (no domain/field/integrality assumption). ✓ matches the general
  "EDS over a commutative ring" treatment (cf. arXiv:2604.05280, "On Elliptic Sequences over
  Commutative Rings").
- **Hypothesis:** only `W 2 ∈ R⁰` (a non-zero-divisor). `W 1 ∈ R⁰` is *derived*, not assumed
  (it divides `W 2 ∈ R⁰`). This is the minimal hypothesis — over a domain it reduces to `W 2 ≠ 0`.
- **Project strengthened the surrounding API vs mathlib:** the project's `IsDivSequence` is over **ℤ**
  (`∀ m n : ℤ, m ∣ n → W m ∣ W n`, line 602) whereas mathlib's is over **ℕ**
  (`∀ m n : ℕ, …`). So this development is, if anything, ahead of mathlib on generality.

Minor cosmetic nit (does not change the bucket): the conclusion uses the eta/anonymous-function form
`W = (W 1 * normEDS b c d ·)`. Mathlib reviewers sometimes prefer the pointwise
`∀ n, W n = W 1 * normEDS b c d n`, or factoring through `W 1 • normEDS b c d` (the section already
uses `IsEllSequence.smul`). Trivial to adjust at PR time; not a generality deficiency.

## 5. Composition check (can ≤3 existing mathlib calls give it?)

**No.** The one-line proof body is misleading: it composes two results that *do not exist in mathlib*:

1. `IsEllSequence.eq_normEDS_of_dvd` (line 1271) — itself nontrivial: extracts `(b,c,d)` from the
   three divisibilities, derives `W 1 ∈ R⁰`, applies `IsEllSequence.ext`.
2. `IsEllSequence.ext` (line 1217) — a ~15-line induction via `normEDSRec` over the even/odd EDS
   recursion with repeated non-zero-divisor cancellation. This "two elliptic sequences agreeing on
   their first four terms are equal (given `W 1, W 2 ∈ R⁰`)" uniqueness lemma is **also absent**
   from mathlib.

So `eq_normEDS` is not assemblable from ≤3 mathlib primitives; it sits on top of a forked-from-mathlib
infrastructure stack (`IsEllSequence.ext` → `eq_normEDS_of_dvd` → `eq_normEDS`) that mathlib lacks.

## 6. Decision

- Standard, attributed result (Ward; the EDS normalisation lemma). ✓
- **Mathlib's own declared TODO** (file line 45) — confirmed by source grep and the live docs. ✓
- Stated at literature-general level; project's ambient API is *more* general than mathlib's. ✓
- Not composable from ≤3 mathlib lemmas; rests on infrastructure mathlib doesn't have. ✓

**Bucket: YES-add-as-is.**

Packaging note for whoever PRs it: it cannot land alone — submit it together with its support
(`IsEllSequence.ext`, `IsEllSequence.eq_normEDS_of_dvd`, and likely the matching forward TODO
`isEllDivSequence_normEDS`), which are the same forked-mathlib EDS machinery from this file. Consider
the pointwise / `smul` form of the conclusion at PR time. None of this downgrades the verdict: the
headline theorem is correct, general, and a gap mathlib has explicitly asked to be filled.
