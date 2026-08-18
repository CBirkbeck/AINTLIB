# /mathlibable report — `complEDS_ofNat`

> NagellLutz / `LutzNagell/EllipticDivisibilitySequence.lean:1572` (root namespace).
> Step-9 mathlibable assessment. **Verdict: NO-mathlib-has-it.**

**Project:** NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic
divisibility sequences)
**Declaration:** `complEDS_ofNat` (root namespace)
**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1572` (`@[simp]` lemma;
the surrounding `def complEDS` sits at 1568)
**Date:** 2026-06-21
**Verdict:** **NO-mathlib-has-it**

---

## Phase 0 — Resolve the declaration & its true qualified name

- decl `complEDS_ofNat`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1571-1575` (the `@[simp]`
  attribute on 1571, the `lemma` on 1572).

**Qualified name verified.** The enclosing block is `section ComplEDS` (opened at line 1524 with
`variable {R : Type u} [CommRing R] (b c d : R) (k : ℤ)`, closed by `end ComplEDS` at 1644). A scan
of lines 1524–1575 finds **no `namespace`** between the section opener and the lemma — the only
`namespace`/`section`/`end` token in range is `section ComplEDS` itself. So the qualified name is
the bare, root-level **`complEDS_ofNat`**. (The earlier `EllSequence` / `IsEllSequence` / `NormEDS`
namespaces all close — `end NormEDS` at 1520 — before this section opens.) The project's own
inventory agrees: "lemma complEDS_ofNat (@[simp], root-level)".

---

## Phase 1 — Exact statement & proof

```lean
@[simp]
lemma complEDS_ofNat (n : ℕ) : complEDS b c d k n = complEDS' b c d k n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp only [Nat.cast_zero, complEDS, Int.sign_zero, Int.cast_zero, zero_mul, complEDS'_zero]
  · simp only [complEDS, Int.sign_natCast_of_ne_zero hn, Int.cast_one, one_mul, Int.natAbs_natCast]
```

with the ambient context

```lean
def complEDS (n : ℤ) : R := n.sign * complEDS' b c d k n.natAbs
def complEDS' : ℕ → R | 0 => 0 | 1 => 1 | (n + 2) => …   -- ℕ-indexed complement sequence
```

**What it says.** For a normalised elliptic divisibility sequence `W = normEDS b c d`, the
ℤ-indexed *complement sequence* `complEDS` (the odd extension `n ↦ sign(n)·complEDS'(|n|)`) agrees
with its ℕ-indexed core `complEDS'` on natural-number arguments:
`complEDS b c d k ↑n = complEDS' b c d k n`. It is a `@[simp]` **indexing-bridge lemma** — a
degenerate special case of `sign(↑n)·g(|↑n|) = g(n)` with `g = complEDS' b c d k`.

The complement (quotient) sequence `Wᶜ` witnesses the divisibility `W(k) ∣ W(n·k)` via
`W(k)·Wᶜ(k,n) = W(n·k)`. The *concept* is classical (Ward 1948); this particular lemma is the ℕ→ℤ
cast compatibility — a Lean-implementation artefact of building the ℤ-indexed sequence as the odd
extension of a ℕ-indexed one.

---

## Phase 2–4 — Literature search (abbreviated, justified)

The exhaustive nine-channel external sweep is **not applicable** here and forcing it would be
theatre. `complEDS_ofNat` is **not a named mathematical theorem** with a literature-standard form:
it is a Lean cast/bridge lemma whose "standard form" is fixed entirely by mathlib's own definition
`complEDS n := n.sign * complEDS' … n.natAbs`. There is no external-mathematics statement of "the
ℕ→ℤ cast of the complement sequence agrees with itself"; the relevant authority **is mathlib**, and
Phase 5 settles it conclusively. A focused literature pass was still run:

| # | Channel | Query | Result |
|---|---------|-------|--------|
| 1 | WebSearch | "elliptic divisibility sequence" complement/quotient sequence `W(k) ∣ W(nk)` Ward | The *concept* — complement/quotient sequence, divisibility `W(m) ∣ W(n)` for `m ∣ n` — is classical (Ward 1948; Wikipedia "Elliptic divisibility sequence" / "Divisibility sequence"). No source states `complEDS_ofNat` as a theorem; it is a Lean cast lemma. The search's own top *library* hit is mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` doc page — the upstream home of this lemma. |

Concept identified: the **complement / quotient sequence of a normalised EDS**, witnessing
`W(k) ∣ W(n·k)` — classical (Ward). `complEDS_ofNat` specifically is the **ℕ→ℤ indexing bridge** for
that sequence — not a literature theorem.

---

## Phase 5 — Mathlib search (five methods)

| Method | What was done | Result |
|--------|---------------|--------|
| [A] Concept / file | Locate mathlib's EDS file | `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` present in the pinned mathlib (`.lake/packages/mathlib/…`) |
| [B] Name search | `grep -n "complEDS_ofNat"` in mathlib file | **HIT — line 431** |
| [C] Grep whole package | `grep -rn "complEDS_ofNat" .lake/packages/mathlib/` | HIT — declared at `…/EllipticDivisibilitySequence.lean:431`; used at 455, 466. Only this one file mentions `complEDS` in all of mathlib. |
| [D] Read mathlib source | Read lines 418–462 + namespace context | Exact lemma present, **identical signature** |
| [E] Generic core | The underlying `sign(↑n)·f(|↑n|) = f(n)` | available as `Int.sign_natCast_of_ne_zero` (+ `Int.natAbs_natCast`) — mathlib's proof uses exactly this |

**Mathlib's declaration** (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:430-434`):

```lean
@[simp]
lemma complEDS_ofNat (n : ℕ) : complEDS b c d k n = complEDS' b c d k n := by
  by_cases hn : n = 0
  · simp [hn, complEDS]
  · simp [complEDS, Int.sign_natCast_of_ne_zero hn]
```

In mathlib this lemma is in **`section ComplEDS`** (line 384) with `variable {R : Type u}
[CommRing R]` (75), `variable (b c d : R)` (118), `variable (k : ℤ)` (386), and **no `namespace`** —
so its qualified name is also the bare root-level **`complEDS_ofNat`**. Same name, same arity, same
type ⇒ exact collision.

**Statement comparison.** Character-for-character identical:
`@[simp] lemma complEDS_ofNat (n : ℕ) : complEDS b c d k n = complEDS' b c d k n`. Same attribute,
same binders, same root namespace. The only difference is cosmetic proof spelling — the project
spells out the `simp only` lemma list (`Nat.cast_zero, complEDS, Int.sign_zero, …`) while mathlib
uses bare `simp`; both pivot on the same `Int.sign_natCast_of_ne_zero` core and the same
`n = 0 / n ≠ 0` split.

**The file is a fork.** The project file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` carries the **identical copyright
header** (`Copyright (c) 2024 David Kurniadi Angdinata`, same single author) and the **identical
module docstring** for `complEDS` as the upstream mathlib file. The entire `complEDS` API —
`complEDS₂`, `complEDS'`, `complEDS'_zero/_one/_even/_odd`, `complEDS`,
`complEDS_ofNat/_zero/_one/_neg/_even/_odd`, `map_complEDS'`, `complEDSRec`, … — is present upstream
and matches. This is a stale **vendored fork of an already-upstreamed mathlib file**.

**Conclusion:** found in mathlib as `complEDS_ofNat`
(`Mathlib.NumberTheory.EllipticDivisibilitySequence`, root namespace,
`…/EllipticDivisibilitySequence.lean:431`), **identical statement**. Generic core additionally
available as `Int.sign_natCast_of_ne_zero` (+ `Int.natAbs_natCast`).

---

## Phase 6 — Generality analysis

No generalisation question arises: mathlib already states this lemma in exactly the form needed,
over `{R : Type u} [CommRing R]` with `(b c d : R) (k : ℤ)` — the same generality as the project's
copy (the project file also carries an extra `{S}` / ring-hom `f` variable block higher up, but this
lemma uses only `R, b, c, d, k`). There is nothing weaker to ask for. The fully generic content
`sign(↑n)·g(|↑n|) = g(n)` is itself a one-liner from `Int.sign_natCast_of_ne_zero`.

### Call sites (informational)

| Call site | Use |
|-----------|-----|
| project `EllipticDivisibilitySequence.lean:1596` | `simpa only [complEDS_ofNat] using complEDS'_even ..` (inside `complEDS_even`) — same declaring file |
| project `EllipticDivisibilitySequence.lean:1609` | `simpa only [complEDS_ofNat] using complEDS'_odd ..` (inside `complEDS_odd`) — same declaring file |
| HasseWeil `Auxiliary/EllipticDivisibilitySequence.lean:757,768,777,781` | uses in another project's own (likewise forked) EDS file |

Every live use is **inside a forked EDS file** (this project's, or HasseWeil's parallel fork). All
resolve `complEDS_ofNat` from `Mathlib.NumberTheory.EllipticDivisibilitySequence` for free once the
fork is replaced by the import — same root namespace, same name, so the call sites need no edits.

---

## Phase 7 — Composition check

**Moot — mathlib has the exact lemma** (Phase 5). For completeness, even absent the exact lemma it
is a ≤2-call composition: split on `n = 0` (`simp`), then `Int.sign_natCast_of_ne_zero hn` +
`Int.natAbs_natCast`. So it is simultaneously NO-mathlib-has-it *and* trivially
NO-composable-from-mathlib; the exact-name + exact-statement match makes **NO-mathlib-has-it** the
correct, sharper verdict.

---

## Verdict: `complEDS_ofNat` — NO-mathlib-has-it

Mathlib already contains `complEDS_ofNat`, verbatim, at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:431` — same root namespace, same `@[simp]`,
character-for-character identical statement
(`lemma complEDS_ofNat (n : ℕ) : complEDS b c d k n = complEDS' b c d k n`); only the proof body
differs cosmetically (spelled-out `simp only` vs. bare `simp`, same `Int.sign_natCast_of_ne_zero`
core). The project file `LutzNagell/EllipticDivisibilitySequence.lean` is a **stale vendored fork**
of the upstreamed `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical Angdinata 2024
copyright header and module docstring; the whole `complEDS` API matches). There is no mathlib gap.

**Action (not a PR).** Do **not** PR this lemma. The right move is to **delete the local fork and
`import Mathlib.NumberTheory.EllipticDivisibilitySequence`** (and have HasseWeil's parallel copy do
the same). The lemma's only live uses are inside the forked file(s) (`complEDS_even`/`complEDS_odd`,
lines 1596/1609, plus HasseWeil's auxiliary file); once the fork is replaced by the import, those
consumers resolve `complEDS_ofNat` from mathlib unchanged — same root namespace, same name.

For belt-and-suspenders: even the generic content `sign(↑n)·f(|↑n|) = f(n)` is mathlib's
`Int.sign_natCast_of_ne_zero` (with `Int.natAbs_natCast`).

### Evidence
- Mathlib hit: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:431`, root namespace,
  `@[simp]`, identical signature. Found via name grep + whole-package grep + source read.
- Fork evidence: identical copyright header + module docstring; full `complEDS` API match
  (`complEDS₂/'/_zero/_one/_even/_odd`, `complEDS_ofNat/_zero/_one/_neg/_even/_odd`, …).
- Generic core present independently: `Int.sign_natCast_of_ne_zero`, `Int.natAbs_natCast`.
- Literature (WebSearch): concept classical (Ward); lemma itself is a Lean cast bridge, not a named
  theorem — relevant authority is mathlib, which has it.

**Sources:**
- [Mathlib.NumberTheory.EllipticDivisibilitySequence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
  (and local `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:431`)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Divisibility_sequence)
