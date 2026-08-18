# Mathlibable assessment: `IsDivSequence`

**Verdict: NO-mathlib-has-it**

Qualified name: `IsDivSequence` (root namespace).
Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:602`.

---

## 1. The declaration

```lean
/-- The proposition that a sequence indexed by integers is a divisibility sequence. -/
def IsDivSequence : Prop :=
  ∀ m n : ℤ, m ∣ n → W m ∣ W n
```

Context at the definition site (`EllipticDivisibilitySequence.lean`):
- `variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)` (line 85).
- All namespaces are closed before line 602 (`end EllSequence` at 597); `open EllSequence` at 599
  opens a *scope*, not a namespace for new decls. So the parsed/true qualified name is the bare
  **`IsDivSequence`** in the root namespace. (Confirmed: prompt's guessed name is correct.)

So: for `W : ℤ → R` with `R` a commutative ring, `IsDivSequence W` says `W` is a divisibility
sequence — `W m ∣ W n` whenever `m ∣ n`, with `m, n` ranging over **ℤ**.

This file is a fork of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same
copyright header, same docstring, same `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence`
block), extended with the EDS recurrence-construction machinery (`EllSequence`, `rel₄`, `normEDS`
divisibility, etc.).

## 2. Literature search

Standard references (Ward 1948 *Memoir on Elliptic Divisibility Sequences*; Wikipedia "Elliptic
divisibility sequence"; Shipsey; Stange "Elliptic nets and elliptic curves", arXiv:0710.1316;
Silverman–Stephens "The sign of an elliptic divisibility sequence", arXiv:math/0402415) all define
the divisibility property of an EDS as:

> `W(m) ∣ W(n)` for any `m, n ∈ ℤ` such that `m ∣ n`.

This is precisely a *divisibility sequence* in the classical sense (the same notion under which the
Fibonacci/Lucas sequences and `Nat.fib` are "(strong) divisibility sequences"). It is a completely
standard, named, atomic concept — not a bespoke construction. There is nothing to "discover" here:
the predicate is exactly the textbook definition.

Note the literature states it over **all integers** `m, n ∈ ℤ` — matching this project's ℤ-indexed
`def` (see §4).

## 3. Mathlib search (five methods)

- **Exact-name / source read.** Mathlib's
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the file this project forks) contains,
  at lines 86–88:

  ```lean
  /-- The proposition that a sequence indexed by integers is a divisibility sequence. -/
  def IsDivSequence : Prop :=
    ∀ m n : ℕ, m ∣ n → W m ∣ W n
  ```

  Same root-namespace qualified name **`IsDivSequence`**, same `variable (W : ℤ → R)`
  `[CommRing R]`, **same docstring verbatim**. It sits in the identical
  `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence` / `isEllDivSequence_id` /
  `IsEllSequence.smul` / `IsDivSequence.smul` block that the project copied.

- **Grep across all of mathlib** for `DivSequence` / "divisibility sequence" /
  `IsDivisibilitySequence`: the only hits are this mathlib EDS file and an informal comment on
  `Nat.fib` ("`fib n` is a strong divisibility sequence", `Mathlib/Data/Nat/Fib/Basic.lean`). No
  competing or more-general predicate exists.

- **leansearch / loogle (mathlib index)** for the shape `(m ∣ n) → (W m ∣ W n)`: resolves to the
  same `IsDivSequence`; no other named predicate captures it.

Conclusion of the search: **mathlib already has this declaration**, under the *same qualified name*,
in the *same file* this project forked.

## 4. Generality analysis (the one real nuance: ℕ vs ℤ)

The project's `def` and mathlib's `def` are identical except for the **index type of the
divisibility quantifier**:

| | quantifier | meaning |
|---|---|---|
| **mathlib** | `∀ m n : ℕ, m ∣ n → W m ∣ W n` | `W (↑m) ∣ W (↑n)` for naturals |
| **project (this decl)** | `∀ m n : ℤ, m ∣ n → W m ∣ W n` | `W m ∣ W n` for all integers |

The project's ℤ-indexed form is the (mildly) **more general / literature-faithful** statement —
it is exactly what mathlib's *own module docstring* says ("`W(m) ∣ W(n)` for any `m, n ∈ ℤ` such
that `m ∣ n`"), even though mathlib's actual `def` quantifies over ℕ. For a sequence that is an odd
function (`W (-k) = -W k`, the EDS normalisation used throughout this file) the ℤ-form and the
ℕ-form are equivalent, since `W (-m) ∣ W (-n) ↔ W m ∣ W n` and every integer divisibility reduces
to its absolute values.

This ℕ↔ℤ discrepancy is a **reconciliation issue between the fork and mathlib**, *not* a reason to
add a new declaration:
- It is the *same named concept* (`IsDivSequence`), not a genuinely different predicate worth its
  own name.
- Adding the project's ℤ-version to mathlib would *clash* with the existing `IsDivSequence` (same
  name, same namespace) — it is a redefinition, not an addition.
- The correct upstream action, if any, is to **change mathlib's existing `def` to quantify over ℤ**
  (a `/generalise`-style edit aligning the def with its docstring and the literature), accompanied
  by the trivial repair of `isDivSequence_id` (mathlib currently uses `Int.ofNat_dvd.mpr`; the ℤ
  version is `fun _ _ => id`, exactly as this fork has it at line 612). That is a *modification of a
  mathlib decl*, which is out of scope for "should this new decl be added".

## 5. Composition check

Trivially yes — but moot. `IsDivSequence W` unfolds to a one-line `∀ … → … ∣ …` statement; it is a
plain abbreviation. The point of mathlibability is whether the *named predicate* should live in
mathlib, and it already does (§3). No ≤3-call composition discussion changes the verdict.

## 6. Verdict

**NO-mathlib-has-it.**

Mathlib already contains `def IsDivSequence : Prop` under the identical root-namespace qualified
name, in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (lines 86–88) — the very file
this project forked — with the same docstring and the same `W : ℤ → R`, `[CommRing R]` setup. This
declaration is a re-statement of an existing mathlib definition.

The sole difference is that the project quantifies the divisibility over `ℤ` whereas mathlib
quantifies over `ℕ`. That is a fork-vs-upstream reconciliation point (and the project's ℤ-form is
the more literature-faithful one, matching mathlib's own docstring), but it does **not** make this a
new contribution: re-adding `IsDivSequence` would collide with the existing name. If the ℤ-indexing
is desired upstream, the route is a `/generalise` PR that *edits mathlib's existing `IsDivSequence`*
(and the one-line `isDivSequence_id` proof), not adding this declaration.

### Pointers
- mathlib source: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:86-88`
  (and the surrounding `IsEllSequence`/`IsEllDivSequence`/`*.smul` block, lines 77–116).
- project decl: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:602`.
- duplicate forks in-repo: `…/EllipticDivisibilitySequenceOriginal.lean:577` (identical ℤ-form);
  `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` imports rather than
  redefines it.

### Sources (literature)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Stange, *Elliptic nets and elliptic curves* (arXiv:0710.1316)](https://arxiv.org/pdf/0710.1316)
- [Silverman–Stephens, *The sign of an elliptic divisibility sequence* (arXiv:math/0402415)](https://arxiv.org/pdf/math/0402415)
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
