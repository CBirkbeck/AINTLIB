# /mathlibable report — `normEDSRec'`

**Verdict: NO-mathlib-has-it** — mathlib already contains this declaration verbatim.

Qualified name: `normEDSRec'` (root namespace; the enclosing `section NormEDS` is a plain
`section`, not a `namespace`, so there is no prefix).

---

## 1. The declaration under assessment

Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:986-992`
(inside `section NormEDS`, opened at line 881 — a bare section, **no** enclosing `namespace`;
the only thing in scope is `open EllSequence`, which affects body name-resolution, not the
declaration's own name).

```lean
/-- Strong recursion principle for a normalised EDS indexed by `ℕ`: if we have
 * `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
 * for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
 * for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def normEDSRec' {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 3), P k) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 2) + 1, P k) → P (2 * (m + 2) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])
```

`normEDSRec'` is the **strong recursion / elimination principle for `ℕ`-indexed normalised
elliptic divisibility sequences**: to construct `P n` for every `n : ℕ` it suffices to give the
five base values `P 0 … P 4` and two strong inductive steps, one for even indices `2*(m+3)` and
one for odd indices `2*(m+2)+1`, each allowed the *full* strong hypothesis `∀ k < …, P k`. It is
plumbing over `Nat.evenOddStrongRec`, specialised to the 5-base-case shape forced by the
`normEDS` even/odd recurrence, and is itself the engine behind the weak recursor `normEDSRec`
(line 1002, which just feeds it finitely many predecessors).

- kind: `noncomputable def`, attribute `@[elab_as_elim]` — a recursion/elimination principle.
- has sorry: no.
- module header copyright: *David Kurniadi Angdinata* — the upstream mathlib EDS author; i.e.
  this file is a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

## 2. Mathlib search — IT IS ALREADY THERE (verbatim)

The CLAUDE/project context flagged exactly this: the NagellLutz project forks
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (and the DivisionPolynomial.* files) and
keeps duplicated tracks, so a declaration may already be upstream. The mathlibable check here
reduces to a direct source comparison, which is decisive.

Upstream declaration (this build's pinned mathlib):
`/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:349-363`

```lean
/--
Strong recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,

then we have `P n` for all `n : ℕ`.
-/
@[elab_as_elim]
noncomputable def normEDSRec' {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 3), P k) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 2) + 1, P k) → P (2 * (m + 2) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])
```

Upstream is *also* in a bare `section NormEDS` (`end NormEDS` at line 382) with no enclosing
namespace — so the upstream fully-qualified name is **also** `normEDSRec'`. The companion
`normEDSRec` follows immediately at line 373, exactly as in the project (project line 1002).

### Byte-for-byte comparison

| Aspect | Project (line 986) | Mathlib (line 357) | Match |
|---|---|---|---|
| Name / qualified name | `normEDSRec'` (root ns) | `normEDSRec'` (root ns) | ✅ identical |
| Attribute | `@[elab_as_elim]` | `@[elab_as_elim]` | ✅ |
| Modifiers | `noncomputable def` | `noncomputable def` | ✅ |
| Universe / motive | `{P : ℕ → Sort u}` | `{P : ℕ → Sort u}` | ✅ |
| Base cases | `zero one two three four` (`P 0`..`P 4`) | identical | ✅ |
| `even` hypothesis | `∀ m, (∀ k < 2*(m+3), P k) → P (2*(m+3))` | identical | ✅ |
| `odd` hypothesis | `∀ m, (∀ k < 2*(m+2)+1, P k) → P (2*(m+2)+1)` | identical | ✅ |
| Proof term | `n.evenOddStrongRec (by rintro (_\|_\|_\|_) h; exacts [zero, two, four, even _ h]) (by rintro (_\|_\|_) h; exacts [one, three, odd _ h])` | identical | ✅ |
| Docstring text | same wording | same wording | ✅ (only cosmetic: project keeps `/-- …` on the opening line, mathlib puts it on its own line) |

The single difference is docstring line-wrapping. The mathematical content, the elaborated
type, and the definitional value are identical.

### Supporting primitive is also in mathlib

The body delegates to `Nat.evenOddStrongRec`, already upstream at
`/.lake/packages/mathlib/Mathlib/Data/Nat/EvenOddRec.lean:51-56`
(strong recursion split on even/odd via `Nat.strongRecOn` + `Nat.even_or_odd'`). The project
file already imports it (`public import Mathlib.Data.Nat.EvenOddRec`, line 14) and the duplicated
`normEDSRec'` calls it directly. So even the dependency closure of this declaration is fully
present in mathlib.

---

## 3. Five-method mathlib search

```
[A] Lean-Finder       (not needed)          n/a — exact source hit found first
[B] Loogle            (not needed)          n/a — exact source hit found first
[C] LeanSearch        (not needed)          n/a — exact source hit found first
[D] Grep mathlib src  grep "normEDSRec"     HIT: Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:357
[E] Name pattern      normEDSRec'           HIT (same file); companion normEDSRec at :373
```

Both the current form and the "standard" form are searched at once: they are the *same string*.
Loogle/LeanSearch would index the upstream `normEDSRec'` under the identical name and namespace.

---

## 4. Literature search

`normEDSRec'` is a **Lean implementation eliminator** (`@[elab_as_elim]`), not a named
mathematical theorem; it has no independent literature object. Its mathematical content —
strong induction on `ℕ` with the even/odd `2*(m+k)` split matching the `normEDS` recurrence — is
entirely standard, and the literature on elliptic divisibility sequences (Ward's *Memoir on
Elliptic Divisibility Sequences*, which the file itself cites; Shipsey; Stange) concerns the
*sequences*, not this recursion combinator. The decisive first probe found the byte-for-byte
mathlib declaration (same author, same file), which short-circuits the remaining literature
channels by design: once mathlib is shown to contain the identical declaration, the
standard-form question is moot. (Run at exhaustive intent; channels A–C and the
nLab/Stacks/MathOverflow/arXiv sweeps all recorded `n/a — superseded by the exact mathlib hit`.)

---

## 5. Generality analysis

Literature/mathlib-standard form: identical to the project's. The motive `P : ℕ → Sort u` is
already maximally general (any universe; covers `Prop` and `Type`), the index is `ℕ`, and there
are no typeclass assumptions.

| # | Parameter / hypothesis | Current Lean form | Standard (= mathlib) form | Weaker form exists? | Reason |
|---|---|---|---|---|---|
| 1 | `{P : ℕ → Sort u}` | `Sort u` motive | `Sort u` motive | NO | `Sort u` is the most general motive universe |
| 2 | base data + steps | 5 bases, strong even/odd | 5 bases, strong even/odd | NO | shape dictated by the `normEDS` recurrence; matches mathlib exactly |

**Generality verdict:** MAXIMALLY GENERAL; definitionally identical to the mathlib declaration.
Weakening opportunities: 0. Modern idiom: this already *is* the modern mathlib idiom (it is the
Angdinata-authored upstream eliminator). Nothing to modernise.

Diamond/defeq risk: n/a for the verdict — it is a `def`, but it is already in mathlib unchanged,
so importing it adds no new infrastructure relative to the current library. It carries no
instance, no coercion, no `@[reducible]`; `@[elab_as_elim]` only affects elaboration of
`induction … using`.

---

## 6. Composition check

Verdict NO-mathlib-has-it (exact decl) dominates NO-composable, so composition is moot. For
completeness: `normEDSRec'` *is* a thin wrapper over `Nat.evenOddStrongRec`, but since the
wrapper itself is already in mathlib, the right move is to reuse the mathlib wrapper rather than
re-inline `evenOddStrongRec` at call sites.

Call sites in the project (excluding the declaring file): **0** external files. Within the
declaring file it is used twice, exactly mirroring mathlib's own two uses:

| Caller (project) | Usage pattern |
|---|---|
| `EllipticDivisibilitySequence.lean:1007` | `normEDSRec' zero one two three four (fun _ ih ↦ …) …` — defines `normEDSRec` |
| `EllipticDivisibilitySequence.lean:1121` | `induction n using normEDSRec' with …` |

Pointing the project at mathlib's `normEDSRec'` loses nothing — every consumer is one the
identical mathlib declaration already serves unchanged.

---

## Verdict: `normEDSRec'`

**Category: NO-mathlib-has-it**

**Evidence**
- Mathlib search (§2, §3): found in mathlib as `normEDSRec'`,
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:357` — **identical** name, signature,
  `@[elab_as_elim]` attribute, body, and docstring (same author, Angdinata). Companion
  `normEDSRec` (`:373`) and the underlying `Nat.evenOddStrongRec`
  (`Mathlib/Data/Nat/EvenOddRec.lean:51`) are also present upstream.
- Literature (§4): the decl is a Lean eliminator with no independent literature; its standard
  form *is* the mathlib declaration.
- Generality (§5): MAXIMALLY GENERAL; definitionally identical to mathlib's; 0 weakenings.
- Composition (§6): moot — exact decl exists; all project call sites are ones mathlib serves.

**Rationale.** The project's `EllipticDivisibilitySequence.lean` is a fork of mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (it even reproduces the upstream copyright
header). `normEDSRec'` is one of the copied declarations: the project version (line 986) and the
mathlib version (line 357) agree byte-for-byte — same name, `{P : ℕ → Sort u}` motive, five base
parameters, `even`/`odd` strong-step parameters, `@[elab_as_elim]` attribute, `n.evenOddStrongRec
(by rintro (_|_|_|_) h; exacts […]) (by rintro (_|_|_) h; exacts […])` body, and docstring. Both
live in the root namespace (the enclosing `section NormEDS` is a plain `section`). There is
nothing to add: mathlib already has exactly this declaration.

**Disposition (not a mathlib submission).** This is the duplicated-fork case. The correct action
is a project-side de-fork, not a PR: delete the forked `normEDSRec'` (project lines 986–992) and
`import Mathlib.NumberTheory.EllipticDivisibilitySequence`; the two in-file uses resolve to the
identical mathlib declaration with no change. Treat as part of the broader effort to drop the
forked re-declarations that are identical to mathlib and keep only the genuinely new
`EllSequence`/`HaveSameParity₄`/`Rel₄OfValid`/`universalNormEDS`-style material that mathlib
lacks. (Apply the same to the parallel copy carried in the sibling
`EllipticDivisibilitySequenceOriginal.lean`, if present, and keep mathlib's `normEDSRec` redirect
consistent — same fork situation.)
