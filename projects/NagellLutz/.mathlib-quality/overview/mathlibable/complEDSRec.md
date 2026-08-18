# Mathlibable assessment — `complEDSRec`

**Verdict: NO-mathlib-has-it**

**One-line rationale:** Already present verbatim in the pinned mathlib
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:497`); this project file is a fork of that
exact upstream file.

---

## 0. Baseline

- Target: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1637-1642`.
- Kind: `@[elab_as_elim] noncomputable def`. No `sorry`.
- Local `lake build` not run (build stale per brief); reasoned from source + pinned mathlib source.
- Pinned mathlib commit in this repo: `09b373db6e247a35cfa5e44578c09a20e7c97271` (2026-06-21).

### Qualified name (VERIFIED)

The declaration sits in `section ComplEDS` (project line 1524) with **no enclosing `namespace`** —
every file-level namespace (`EllSequence`, `IsEllSequence`, `NormEDS`, …) is closed before that
section, and the `@[expose] public section` at line 81 is a *section*, not a namespace. So the
fully-qualified name is exactly the base name:

> **`complEDSRec`** (root namespace — qualified name == base name).

The task's tentative parse "`complEDSRec`" is correct.

---

## 1. The declaration

```lean
/-- Recursion principle for the complement sequence for a normalised EDS: if we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  and `P (m + 4)`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def complEDSRec {P : ℕ → Sort u} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, P (m + 1) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
  complEDSRec' zero one (fun _ ih ↦ even _ <| ih _ <| by linarith only)
    (fun _ ih ↦ odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n
```

**What it is:** a convenience `@[elab_as_elim]` eliminator that repackages the even/odd
strong-recursion structure of the EDS complement sequence (`complEDS'`) into a "short-step"
recursion principle (each arm consumes only the few immediately-needed predecessors instead of
all `k < n`). It is a derived helper definition — it delegates entirely to the strong recursor
`complEDSRec'` (itself a thin wrapper over `Nat.evenOddStrongRec`). It is *not* a mathematical
theorem about elliptic curves / division polynomials; it is Lean-formalisation plumbing used to
write the `complEDS*` / `map_complEDS*` lemmas by induction.

---

## 2. Mathlib search (five methods)

This project's entire `EllipticDivisibilitySequence.lean` is an explicit fork of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — confirmed by the identical author header
("Copyright (c) 2024 David Kurniadi Angdinata"), identical `## Mathematical background` prose, and
the identical `complEDS₂ / complEDS' / complEDS / normEDSRec / complEDSRec` API surface.

1. **Name grep in pinned mathlib:** HIT. `complEDSRec` at
   `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:497`, with its
   strong-recursion sibling `complEDSRec'` at line 482. Same root namespace, same `section ComplEDS`.
2. **Statement / proof comparison:** the upstream `complEDSRec` (mathlib lines 497-501) is
   **byte-identical** to the project's (lines 1637-1642): same attribute `@[elab_as_elim]`, same
   `noncomputable def`, same binder list `{P : ℕ → Sort u} (zero one) (even) (odd) (n) : P n`, same
   body `complEDSRec' zero one (fun _ ih => even _ <| ih _ <| by linarith only) (fun _ ih => odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n`.
   (Cosmetic-only drift: the project's `complEDSRec'` *docstring* lacks the blank line before "then
   we have `P n`" that mathlib's has — i.e. the project is a slightly older copy. The `complEDSRec`
   def itself is unchanged.)
3. **loogle / leansearch (mathlib index):** `complEDSRec` is library API (an eliminator), not a
   stated proposition, so type-/semantic-search is not the right instrument; the direct source hit
   in (1)-(2) is conclusive. Its analogue `normEDSRec` (mathlib line 374) is the well-known indexed
   recursor for `normEDS`, confirming `…Rec` is a mathlib naming convention here, not a literature name.
4. **doc-gen:** the WebSearch top result is the mathlib doc page
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.html`, which lists `complEDSRec`.
5. **Companion API also upstream:** `complEDSRec'`, `complEDS'`, `complEDS₂`, `complEDS`,
   `complEDS'_even/odd`, `complEDS_ofNat/neg/even/odd`, and `map_complEDS*` all likewise already
   exist in the same upstream file. The fork duplicates them.

Conclusion: this is not "a more general form upstream" — it is **the same declaration**, already in
the repo's pinned mathlib.

---

## 3. Generality analysis

`complEDSRec` is already at the natural generality for what it is: motive `P : ℕ → Sort u` (so it
serves `Prop`, `Type`, and data alike), and the ring `R` does not even appear (it is a pure-`ℕ`
recursion shape). There is nothing to weaken or strengthen, and no generalisation question arises,
because the declaration is identical to the upstream one. (`YES-but-generalise-first` is therefore
inapplicable.)

---

## 4. Composition check

Moot as a verdict route: mathlib already *contains* the declaration, so it trivially "composes" in
one call — itself. For the record, `complEDSRec` is itself a one-line composition over
`complEDSRec'` (which is `Nat.evenOddStrongRec`); even absent the fork it would be a thin derived
helper rather than a `YES-add-as-is` candidate. But this is irrelevant given (2).

---

## 5. Literature

- mathlib doc:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html>
- "On Elliptic Sequences over Commutative Rings" (D. K. Angdinata), arXiv:2604.05280 — the paper
  behind mathlib's EDS formalisation; the complement-sequence recursion is the device used there to
  define `normEDS` without dividing by `b`.
- The `…Rec` principle is a Lean-formalisation convenience (an `@[elab_as_elim]` eliminator), **not**
  a named theorem in the EDS literature (Ward, Shipsey, Stange, Silverman). There is no external
  "standard form" to match — the only operative fact is that mathlib already ships it.

---

## 6. Verdict — NO-mathlib-has-it

`complEDSRec` is already in this repo's pinned mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:497` (root namespace), with byte-identical
signature and proof. The project file is a fork of that very mathlib file (matching author header,
prose, and the full surrounding `complEDS*` / `normEDSRec` API). The correct cleanup action is
**deduplication against upstream** — delete the forked copy and rely on
`import Mathlib.NumberTheory.EllipticDivisibilitySequence` — **not** a mathlib contribution.

**Consolidation note:** essentially the whole `section ComplEDS` of this project file
(`complEDS'`, `complEDS₂`, `complEDS`, `complEDSRec'`, `complEDSRec`, and the `map_complEDS*`
lemmas) is a verbatim / near-verbatim fork of pinned mathlib and is a candidate for wholesale
removal in favour of the upstream import. (This independent assessment agrees with the prior
`complEDSRec.md` run, and additionally pins the upstream commit, confirms the byte-level match, and
verifies the literature provenance.)
