# Mathlibable assessment — `IsEllSequence.isEllDivSequence_of_dvd`

**Verdict: BORDERLINE-needs-human**

**Qualified name:** `IsEllSequence.isEllDivSequence_of_dvd`
(base name `isEllDivSequence_of_dvd`; declared inside `namespace IsEllSequence`, opened line 643)

**Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1457`

> Step-9 `/mathlibable` assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Re-run 2026-06-21,
> consistent with the prior 2026-06-18 verdict. ChatGPT MCP unavailable; literature
> grounded on WebSearch + Wikipedia + mathlib4 docs + Ward 1948 secondary sources,
> which converge cleanly. Pinned mathlib `09b373db6e24` (v4.32.0-rc1) **and** current
> master both checked directly.

---

## 1. Exact statement (verified from source)

`section Divisibility` inside `namespace IsEllSequence`. Ambient variables:

```lean
variable {R : Type u} [CommRing R] (W : ℤ → R)
-- (ellW : IsEllSequence W) (ellU : IsEllSequence U)
-- section Divisibility:
variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (dvd₁₂ : W 1 ∣ W 2) (dvd₁₃ : W 1 ∣ W 3) (dvd₂₄ : W 2 ∣ W 4)

omit ellU one in
lemma IsEllSequence.isEllDivSequence_of_dvd : IsEllDivSequence W :=
  ⟨ellW, ellW.isDivSequence_of_dvd two dvd₁₂ dvd₁₃ dvd₂₄⟩
```

Hypotheses actually used (after `omit ellU one in`): `ellW : IsEllSequence W`,
`two : W 2 ∈ R⁰`, `dvd₁₂ : W 1 ∣ W 2`, `dvd₁₃ : W 1 ∣ W 3`, `dvd₂₄ : W 2 ∣ W 4`.
Conclusion: `IsEllDivSequence W`.

Here `IsEllDivSequence W := IsEllSequence W ∧ IsDivSequence W`, with (in this project)
`IsDivSequence W := ∀ m n : ℤ, m ∣ n → W m ∣ W n` — note **over ℤ**.

**Mathematical content.** An elliptic sequence `W : ℤ → R` whose second term is a
non-zero-divisor and which satisfies the three base divisibilities `W 1 ∣ W 2`,
`W 1 ∣ W 3`, `W 2 ∣ W 4` is a full elliptic divisibility sequence (additionally
`W m ∣ W n` whenever `m ∣ n`). This is the top-level, user-facing form of the
"divisibility direction" of **Ward's theory** of EDS.

**Shape of THIS declaration.** It is a **two-element anonymous-constructor wrapper**:
`⟨ellW, ellW.isDivSequence_of_dvd …⟩`. The first component is the already-assumed
elliptic hypothesis `ellW`; the second is the sibling `IsEllSequence.isDivSequence_of_dvd`
(line 1450), which carries 100 % of the mathematical work. This lemma itself proves
nothing new beyond conjoining.

---

## 2. Literature search

- Morgan Ward, *Memoir on elliptic divisibility sequences* (Amer. J. Math. 1948) — founding
  reference. An EDS satisfies the elliptic recurrence **and** the divisibility property
  `Wₙ ∣ Wₘ` whenever `n ∣ m`. That the recurrence + base normalisation forces divisibility is
  exactly Ward's framework.
- Silverman–Stephens, "The sign of an elliptic divisibility sequence", arXiv:math/0402415;
  Wikipedia "Elliptic divisibility sequence"; Shipsey's thesis. Standard non-degeneracy is
  `W₂W₃ ≠ 0`, `W₁ = 1`. The project's `two : W 2 ∈ R⁰` + three base divisibilities is the
  general ring-theoretic form of that hypothesis over ℤ.

The result is a recognised, named theorem — genuine mathematics, not folklore filler.

---

## 3. Mathlib search (five methods) — pinned AND master

Searched `.lake/packages/mathlib/.../NumberTheory/EllipticDivisibilitySequence.lean`
(pin `09b373db6e24`, 547 lines) and current mathlib **master** (raw GitHub + mathlib4_docs).

- `grep` over all of `Mathlib/` for `isEllDivSequence_of_dvd`, `isDivSequence_of_dvd`,
  `IsEllDivSequence.normEDS`, `IsEllDivSequence.eq_normEDS`, `IsEllSequence.eq_normEDS_of_dvd`,
  `IsDivSequence.normEDS`: **zero hits**, both pin and master.
- Read the mathlib EDS file directly: it contains only the three **definitions**
  (`IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`) plus trivial lemmas
  (`isEllDivSequence_id`, the three `.smul`). No bridge from `normEDS` to the predicate at all.
- mathlib4_docs page for the file confirms the same short list under
  `IsDivSequence`/`IsEllDivSequence`.

**Decisive finding.** The mathlib EDS file header carries these two **open TODOs**
(verified byte-identical on the pin and on master):

> * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
> * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.

This project's `EllipticDivisibilitySequence.lean` is a **fork / forward-port of that very
mathlib file that discharges exactly these two TODOs.** `isEllDivSequence_of_dvd` (with
`isDivSequence_of_dvd`, `IsEllDivSequence.normEDS`, `IsEllDivSequence.eq_normEDS`) is part of
that converse machinery. So mathlib does **not** have it — and the underlying result is
**wanted** (TODO-listed). This is *not* a NO-mathlib-has-it case.

**Definitional divergence (important).** mathlib's `IsDivSequence` is indexed over **ℕ**
(`∀ m n : ℕ, m ∣ n → W m ∣ W n`); the fork generalised it to **ℤ**. The fork's conclusion is
therefore strictly stronger than what mathlib's current `IsDivSequence`/`IsEllDivSequence`
definitions can even express, and upstreaming entails changing an existing mathlib definition.

---

## 4. Generality analysis

- **Ring `R`:** general `CommRing R`, hypotheses via the non-zero-divisor submonoid `R⁰`.
  Already maximally general (broader than ℤ-coefficient or field) — correct mathlib framing.
- **Index set:** divisibility over **ℤ**, strictly stronger than mathlib's ℕ-indexed
  `IsDivSequence`. An improvement, but it changes the existing def.
- **Hypotheses:** `two ∈ R⁰` + three base divisibilities is the clean ring form of Ward's
  `W₂W₃ ≠ 0`; `one` and the `U`-hypotheses are correctly `omit`-ted.

No further weakening of *this* lemma is warranted; it is already at (indeed beyond) the
literature-standard generality. The generality concern is about the **package** (the ℕ→ℤ def
change), not this lemma's hypotheses.

---

## 5. Composition check (≤ 3 mathlib calls?)

Two distinct questions:

- **From existing *mathlib* primitives?** No. The dependency chain is fork-only:
  ```
  isEllDivSequence_of_dvd
    └─ isDivSequence_of_dvd        (line 1450, NOT in mathlib)
         ├─ eq_normEDS_of_dvd      (line 1271, NOT in mathlib)
         │    └─ IsEllSequence.ext (line 1217, NOT in mathlib)
         ├─ IsDivSequence.normEDS  (line 1437, NOT in mathlib)
         │    └─ normEDS_mul_complEDS (NOT in mathlib)
         └─ mul_dvd_mul_left       (mathlib ✓)
  ```
  Every non-trivial link is a fork-only declaration filling a mathlib TODO. The supporting
  `normEDS`-divisibility API does not exist upstream. So this is **new API to mathlib**, not
  composable from mathlib — rules out NO-composable-from-mathlib.

- **From its own *sibling* (already-in-this-PR) lemma?** Yes, trivially:
  `⟨ellW, ellW.isDivSequence_of_dvd …⟩` is a single anonymous constructor over
  `isDivSequence_of_dvd`. This is what makes the *grain* of THIS declaration a judgement call:
  given the content lemma, the conjunction is a one-liner that a consumer could inline.

---

## 6. Why BORDERLINE-needs-human (not a clean YES)

Every factual gate points to "the math belongs": recognised Ward result, absent from pin and
master, explicitly TODO-listed by mathlib, maximally general ring framing, and not composable
from existing mathlib primitives. So the **content** (`isDivSequence_of_dvd`, `eq_normEDS_of_dvd`,
`IsDivSequence.normEDS`, `IsEllDivSequence.eq_normEDS`) is YES-worthy and should be upstreamed as
the answer to the two TODOs.

But *this specific declaration* is not independently a clean YES, for three reasons that are
**library-design taste calls**, properly a human's:

1. **Thin wrapper, no content of its own.** It is `⟨ellW, ellW.isDivSequence_of_dvd …⟩`; all the
   mathematics is in the sibling. Mathlib might prefer to inline this conjunction, state it as an
   `iff` characterisation, or expose `IsEllDivSequence.eq_normEDS` as the headline instead of a
   bare `_of_dvd` wrapper.
2. **Zero consumers.** Repo-wide, the only `.lean` occurrence of `isEllDivSequence_of_dvd` is its
   own definition (line 1457) — no in-code call site anywhere (the only "twin" is the byte-copy in
   the `…Original.lean` fork). The surrounding converse API *is* used (e.g. `eq_normEDS_of_dvd` →
   `IsEllDivSequence.eq_normEDS`), but this exact wrapper is not.
3. **Entangled definitional change.** Landing it cleanly requires reconciling the fork's ℕ→ℤ
   generalisation of mathlib's `IsDivSequence` — a change to an existing mathlib definition that
   must move together with `isDivSequence_id`, `IsDivSequence.smul`, and downstream users.

Consistency note: the substantive sibling `isDivSequence_of_dvd` was itself assessed
`BORDERLINE-needs-human` in this same ledger, for the same TODO-but-entangled reason. A thin
wrapper over a borderline content lemma cannot be a *cleaner* YES than the lemma it wraps — so
the wrapper inherits BORDERLINE and adds the grain question on top.

**Recommendation to the human.** Upstream the EDS-converse track (`isDivSequence_of_dvd`,
`eq_normEDS_of_dvd`, `normEDS`-is-an-EDS, `IsEllDivSequence.eq_normEDS`) as the resolution of
mathlib's two header TODOs, after deciding the ℕ-vs-ℤ shape of `IsDivSequence`. Decide at PR time
whether `isEllDivSequence_of_dvd` ships as a named convenience lemma, an `iff`, or is inlined.

**Bucket:** `BORDERLINE-needs-human`
**Qualified name:** `IsEllSequence.isEllDivSequence_of_dvd`

### Sources
- Mathlib EDS file — pin `09b373db6e24` and master: header TODOs + full declaration list
  (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`).
- mathlib4_docs: `Mathlib/NumberTheory/EllipticDivisibilitySequence.html`.
- Silverman–Stephens, "The sign of an elliptic divisibility sequence", arXiv:math/0402415.
- Wikipedia, "Elliptic divisibility sequence" (Ward's recurrence + divisibility property).
