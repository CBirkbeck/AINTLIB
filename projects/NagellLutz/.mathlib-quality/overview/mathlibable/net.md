# Mathlibable assessment — `EllSequence.net`

- **Verdict:** `NO-mathlib-has-it`
- **Qualified name:** `EllSequence.net`
- **One-line rationale:** Byte-identical to `IsEllipticNet.rel` in open mathlib PR #25989 (same author, same generality) — re-adding would duplicate in-flight upstream.
- **Date:** 2026-06-18
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:115`

---

## 1. The declaration

```lean
namespace EllSequence

/-- The defining property of Stange's elliptic nets,
equivalent to a suitable valid (same-parity indices) `rel₄` relation,
but here only the first three indices enjoy symmetry under permutation,
while in `rel₄` all four indices can be freely permuted.

The order of the last two terms are changed and two signs are swapped compared to Stange's
paper to make the equivalence with elliptic relations unconditional (indepedent of W
being an odd function). This should also avoid peculiarities in characterstic 3. -/
def net (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r
    - W (p + r + s) * W (p - r) * W (q + s) * W q
    + W (q + r + s) * W (q - r) * W (p + s) * W p
```

Context: `variable {R : Type u} [CommRing R] (W : ℤ → R)`. So `net W p q r s : R` is a **ring-valued
four-index expression** — the relator whose vanishing defines an *elliptic net*. It is NOT a `Prop`;
the proposition "`W` is an elliptic net" would be `∀ p q r s, net W p q r s = 0`.

Confirmed true qualified name is **`EllSequence.net`** (base name `net`, inside `namespace
EllSequence`), matching the prompt's parsed guess.

This file is a **fork/refactor of `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (same
copyright header: David Kurniadi Angdinata). Neighbouring decls in the same file — `addMulSub`,
`rel₄`, `net_eq_rel₄`, `Rel₃`, `IsEllSequence`, `invarNum`, `invarDenom`, `invar_of_net` — are the
matching API.

## 2. Literature search

- **Stange, *Elliptic Nets and Elliptic Curves*** (arXiv:0710.1316; Algebra & Number Theory).
  This is the origin of the four-index elliptic-net recurrence. Standard form (rank-1 / sequence
  case), as recovered from the literature:

  `W(p+q+s)W(p−q)W(r+s)W(r) + W(q+r+s)W(q−r)W(p+s)W(p) + W(r+p+s)W(r−p)W(q+s)W(q) = 0`.

  The project's `net` is **exactly this relator**, up to the documented normalisation: "the order of
  the last two terms is changed and two signs are swapped" (equivalently, Stange's final term is
  negated). The project docstring states this explicitly, and so does the mathlib PR (see below):
  *"The elliptic relator is identical to the elliptic net recurrence defined by Stange, except that
  the final term in the latter is negated."*

- **Junyan Xu, *On Elliptic Sequences over Commutative Rings*** (arXiv:2604.05280, Apr 2026).
  Develops EDS theory over a general commutative ring and **explicitly references the mathlib
  formalization** `Mathlib/NumberTheory/EllipticDivisibilitySequence`. This is the mathematical
  backdrop for the commutative-ring generality used here (and in the mathlib PR). Related thread:
  mathlib PR #13155 by `alreadydone` (Junyan Xu's handle).

- M. Ward, *Memoir on Elliptic Divisibility Sequences* — the classical rank-1 source cited by the
  file; gives the three-index relation `Rel₃` (= mathlib's current `IsEllSequence`), the `d = 0`
  specialisation of `net`.

Conclusion: `net` is the **literature-standard Stange four-index elliptic-net relator**, with a
sign convention chosen (by Angdinata) to make equivalence with the Ward three-index relation
unconditional and characteristic-3-safe. It is a well-known object, not a bespoke gadget.

## 3. mathlib search (five methods)

- **grep of the pinned mathlib (`d90090f`)** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`:
  no `net`, no `EllSequence` namespace, no `addMulSub`, no `rel₄`, no `Stange`, no `invarNum`. The
  pinned file only has `IsEllSequence` (the three-index Ward `Prop`), `IsDivSequence`,
  `IsEllDivSequence`, `preNormEDS`, `normEDS`, etc.
- **grep of current mathlib `master`** (fetched live via GitHub contents API, 2026-06-18): same — no
  four-index relator, no elliptic-net definition. So as of today **`net` is not in mathlib HEAD**.
- **`DivisionPolynomial/{Basic,Degree}.lean`**: no `net` / `EllSequence.net` references.
- **GitHub code search** `EllSequence.net` over `leanprover-community/mathlib4`: no hits (engine
  verified working — `IsEllSequence` returns the expected file).
- **GitHub PR search** — DECISIVE. Two **open** PRs by the same author add exactly this:

  | PR | State | Title | Branch |
  |----|-------|-------|--------|
  | **#25989** | OPEN (non-draft, `awaiting-author`, `t-number-theory`) | feat(NumberTheory/EllipticDivisibilitySequence): **add elliptic nets** | `EllipticNet` |
  | **#25990** | OPEN | chore(...): **rename definitions** | `EllipticDivisibilitySequence.Chore` |

  Author: **David Kurniadi Angdinata (`Multramate`)** — the very author of the project file. PR
  #25989 last updated 2026-02-20; author actively responding to review (Feb 2026); only blockers are
  a merge-conflict bot ping and a "motivation?" question — **active, not abandoned**.

  In PR #25989 the four-index relator is named **`IsEllipticNet.rel`**, with `def rel` body:

  ```lean
  def rel (p q r s : ℤ) : R :=
    W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q +
      W (q + r + s) * W (q - r) * W (p + s) * W p
  ```

  This is **character-for-character identical** to the project's `EllSequence.net` body. The PR also
  carries the supporting API (`atom`, `atomRel`, `rel_eq`, `map_rel`, `IsEllipticNet`,
  `IsEllipticNet.isEllSequence`, …) — i.e. the project's `addMulSub`/`rel₄`/`net_eq_rel₄`/`net` track
  is an **earlier-named copy of this exact PR**.

## 4. Generality analysis

- mathlib PR #25989 context: `variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (W : ℤ → R) (f : R →+* S)`.
- Project context: `variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)` plus a
  `RingHomClass` morphism `f`.

Identical generality — full commutative-ring base, integer-indexed `W`, with ring-hom transport
lemmas on both sides. There is **nothing to generalise**; the upstream form is already at the
literature-standard maximum (commutative ring, matching arXiv:2604.05280). No
`YES-but-generalise-first` angle.

## 5. Composition check (≤ 3 mathlib calls)

Not applicable in the usual sense: `net` is a **definition** (a named ring expression), not a lemma
to be discharged. mathlib HEAD has **no** four-index elliptic-net relator (only the three-index
`IsEllSequence` `Prop`), so there is no existing primitive to compose it from — it is itself the new
primitive. The decisive fact is not composability but that this exact primitive **already exists in
mathlib's pipeline** as open PR #25989. Hence `NO-composable-from-mathlib` does not fit; the correct
bucket is `NO-mathlib-has-it`.

## 6. Verdict

**`NO-mathlib-has-it`.**

`EllSequence.net` is the Stange four-index elliptic-net relator. The byte-identical definition
(`IsEllipticNet.rel`), same generality, same supporting API, **by the same author**, is the content
of **open, active mathlib PR #25989** ("add elliptic nets"), with companion rename PR #25990. The
project file is a development fork of that upstream work under earlier names. Re-contributing `net`
to mathlib would duplicate and conflict with #25989.

**Recommended action (for consolidation):** do not file this as a "to-mathlib" candidate. Track PR
#25989 / #25990 upstream; once merged, the project should drop its forked
`addMulSub`/`rel₄`/`net`/`Rel₃` track and import mathlib's `IsEllipticNet.rel` (`net` ↦
`IsEllipticNet.rel`, `rel₄` ↦ `IsEllipticNet.atomRel`, `addMulSub` ↦ `IsEllipticNet.atom`). This
is a fork-vs-upstream dedup, not new mathlib API.

### Caveat / nuance
The PR is **open, not yet merged**, so strictly the decl is "in the mathlib *pipeline*" rather than
in a released tag. The five-bucket rubric has no separate "mathlib-PR-in-flight" bucket; the closest
and operationally correct one is `NO-mathlib-has-it` (the canonical author already owns this in
mathlib, the action is align-with-PR not re-derive). A human consolidator may want to note the PR
number rather than treat mathlib as already shipping it. This does not change the recommendation: do
not re-add.

## Evidence
- Project source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:115` (`def net`).
- Pinned mathlib (`d90090f`): `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — no `net`/`EllSequence`/`rel₄`.
- mathlib `master` (live, 2026-06-18): same file, no four-index relator.
- mathlib PR #25989 `feat(...): add elliptic nets` (OPEN, Multramate) — `def rel` body identical to `net`.
- mathlib PR #25990 `chore(...): rename definitions` (OPEN, Multramate) — Stange-relator docstring + Stange citation.
- Stange, *Elliptic Nets and Elliptic Curves*, arXiv:0710.1316.
- Junyan Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280 (cites the mathlib EDS file).
