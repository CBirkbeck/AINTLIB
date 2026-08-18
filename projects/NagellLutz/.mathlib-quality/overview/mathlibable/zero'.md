# /mathlibable report — `IsEllSequence.zero'`

**Verdict: YES-add-as-is** — a basic, literature-standard structural fact about the mathlib predicate
`IsEllSequence` (the zeroth term of an elliptic sequence over a *reduced* ring vanishes) that mathlib
does **not** currently have, at a natural generality, ready to upstream as part of building out the
`IsEllSequence` API.

> Target declaration: `IsEllSequence.zero'` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:653`.
>
> QUALIFIED-NAME NOTE: the base name in the source is `zero'`; it sits inside `namespace IsEllSequence`
> (opened at line 643), so the true qualified name is **`IsEllSequence.zero'`**. (Confirmed: there is no
> intervening namespace between line 643 and line 653; the file's outer `namespace EllSequence` was
> closed earlier, and `namespace IsEllSequence` is the active one.)
>
> SIBLING NOTE: this file holds TWO `W 0 = 0` lemmas with adjacent names —
> `IsEllSequence.zero'` @653 (hypothesis: `[IsReduced R]`) and `IsEllSequence.zero` @660 (hypothesis:
> `W (2*m) ∈ R⁰`, i.e. some even term is a non-zero-divisor). This report assesses **`zero'`** (the
> reduced-ring version). The two have *incomparable* hypotheses — neither implies the other — so both
> are legitimate, distinct API entry points.

---

### Baseline (Phase 0)
- lake build:                 not run (local build stale per task note); assessment reasons from source.
- decl `IsEllSequence.zero'`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:653`.
- kind:                       lemma.
- has sorry:                  no.
- module docstring summary:   Forked + heavily *extended* copy of mathlib's elliptic-divisibility-sequence
  (EDS) theory — the division-polynomial relations (`Rel₃`/`rel₄`/`net`/`invar`), the odd/even
  recurrences, and the EDS predicates `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence`, en route to
  the Nagell–Lutz theorem. The extension adds an entire `namespace IsEllSequence` API (`oddRec`,
  `evenRec`, `zero'`, `zero`, `neg`, `rel₄`, `net`, `invar`) that is **absent from the project's pinned
  mathlib**.

---

### Statement (Phase 1)

`IsEllSequence.zero'` states:

> If `W : ℤ → R` is an *elliptic sequence* over a commutative ring `R` **with no nonzero nilpotents**
> (`[IsReduced R]`), then its zeroth term vanishes: `W 0 = 0`.

A sequence is *elliptic* (`IsEllSequence W`) when, for all `m n r : ℤ`, it satisfies the fundamental
EDS relation `Rel₃`:
`W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`.

Mathematical content of the proof. Instantiate the relation at `m = n = r = 0`:
`W(0)·W(0)·W(0)² = W(0)·W(0)·W(0)² − W(0)·W(0)·W(0)²`,
whose right-hand side is `X − X = 0`. Hence `W(0)·W(0)·W(0)² = (W 0)^4 = 0` (the source collapses this
with `mul_assoc, ← pow_succ'`). So `W 0` is **nilpotent**; in a reduced ring a nilpotent is zero, giving
`W 0 = 0`. The source closes with `IsReduced.eq_zero _ ⟨_, this⟩` (witnessing `(W 0)^4 = 0`).

Variables / typeclasses (Lean): `{R : Type u} [CommRing R]`, `{W : ℤ → R}`, ambient
`variable (ell : IsEllSequence W)` + `include ell`, plus the local `[IsReduced R]`.
Hypotheses (Lean): `ell : IsEllSequence W`, `[IsReduced R]`.
Conclusion (math/Lean): `W 0 = 0`.

Source (project, line 653):
```lean
lemma zero' [IsReduced R] : W 0 = 0 := by
  have := ell 0 0 0
  simp_rw [Rel₃, add_zero, sub_self, mul_assoc, ← pow_succ'] at this
  exact IsReduced.eq_zero _ ⟨_, this⟩
```

`Rel₃` (project line 130) is definitionally mathlib's `IsEllSequence` body:
```lean
def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2
def _root_.IsEllSequence : Prop := ∀ m n r : ℤ, Rel₃ W m n r
```
— identical to mathlib's `IsEllSequence` (mathlib EDS file lines 82–84). So the *hypothesis* `IsEllSequence W`
is the same object as upstream; only the *conclusion lemma* is new.

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a one-step structural property (vanishing of the initial term) of the `IsEllSequence`
predicate; a helper lemma, not a main result, not named after a person/place. (Literature width run
exhaustively regardless, since the predicate it is about *is* a named mathlib object and the fact is a
documented folklore property.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a definition. (The "one-liner def" negative signal applies to defs only.)

---

### Literature search table (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                              | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS "W(0)=0" initial term Ward memoir definition normalization                                  | yes  | "A normalized divisibility sequence has `D₀ = 0`"; canonical normalized EDS has `W(0)=0` | Ward (1948); Wikipedia "Elliptic divisibility sequence" |
|  2 | WebSearch (general form / rings) | elliptic sequence first term `W₀` zero **reduced ring / no nilpotents** commutative ring        | yes  | "For a non-degenerate elliptic sequence, `W₀ = 0`"; EDS over commutative rings satisfy `W(0)=0` | hit: arXiv:2604.05280 "On Elliptic Sequences over Commutative Rings" |
|  3 | WebSearch (named-after/aliases)  | "elliptic net" / Somos / division polynomial zeroth term vanish                                 | yes  | division-polynomial `Ψ₀ = 0`; `Wₙ = λ^{n²−1}Ψₙ`, so `W₀` is the `Ψ₀ = 0` term     | Stange elliptic nets; Ward's `Wₙ = λ^{n²−1}Ψₙ(P)` |
|  4 | ChatGPT MCP                      | (MCP down per task note — fell back to WebSearch + arXiv + mathlib source as the literature)    | n/a  | mathlib EDS file + Xu's commutative-rings paper are the modern reference          | MCP unavailable here |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` — directory does not exist                   | n/a  | (none on disk)                                                                    | not the bottleneck |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                | no   | no dedicated page                                                                | not a category-theoretic concept |
|  7 | nCatLab                          | —                                                                                              | n/a  | —                                                                                | n/a |
|  8 | Stacks Project                   | "elliptic divisibility sequence" / "elliptic sequence"                                           | no   | not in Stacks                                                                    | arithmetic of EDS, not scheme theory |
|  9 | MathOverflow / MSE               | EDS initial term `W₀ = 0`; why does the zeroth term vanish                                       | yes  | community: instantiate the elliptic relation at `(0,0,0)` ⇒ `W₀` term squared/quartic ⇒ `0` | folklore derivation matches the proof here |
| 10 | recent arXiv (last 5 yrs)        | "elliptic sequences over commutative rings" zeroth term / `IsEllSequence` Lean                  | yes  | **arXiv:2604.05280 (Junyan Xu)** — *On Elliptic Sequences over Commutative Rings*, explicitly references the mathlib `IsEllSequence` formalisation | this is the literature companion to *this very formalisation track* |

### Literature summary (Phase 3)

Concept: **vanishing of the zeroth term of an elliptic (divisibility) sequence**, `W(0) = 0`, under a
non-degeneracy hypothesis.
Sources agree on the standard form: **yes.** Across Ward, the Wikipedia/textbook normalisation, the
division-polynomial picture (`Ψ₀ = 0`), and the modern commutative-ring treatment (Xu, arXiv:2604.05280),
`W(0) = 0` is a basic, expected property of (non-degenerate) elliptic sequences.
Most general standard form: over a **commutative ring**, an elliptic sequence has `W(0) = 0` once a
non-degeneracy condition rules out the pathological all-the-same situation. Two natural such conditions:
(a) **the ring is reduced** (this lemma, `zero'`), or (b) **some even term `W(2m)` is a non-zero-divisor**
(the sibling `zero`). Over a field/domain both reduce to the textbook fact.
Generality variation: the *hypothesis packaging* varies (reduced ring vs. regular even term vs. integral
domain), but the conclusion `W(0)=0` and the "instantiate at `(0,0,0)`" derivation are uniform.
Disagreement with the literature: none. The reduced-ring hypothesis is a clean, idiomatic way to state the
non-degeneracy needed (a nilpotent zeroth term is exactly the degenerate possibility the relation leaves
open at `(0,0,0)`).

Notable: arXiv:2604.05280 ("On Elliptic Sequences over Commutative Rings", Junyan Xu) is the literature
counterpart to this formalisation track — it studies precisely `IsEllSequence` over commutative rings and
cites the mathlib implementation. That strongly signals this whole `namespace IsEllSequence` API (including
`zero'`) is *intended* mathlib content, not a project-local convenience.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): over a commutative ring, a non-degenerate elliptic sequence has
`W(0) = 0`. The `[IsReduced R]` form is one of the two standard ways to supply the non-degeneracy.

| # | Parameter / hypothesis     | Current Lean form              | Literature-standard form                       | Weaker form exists? | Reason |
|---|----------------------------|--------------------------------|------------------------------------------------|---------------------|--------|
| 1 | `[CommRing R]`             | commutative ring               | commutative ring                               | NO                  | the EDS relation uses `+ − ·` and commutativity; matches mathlib's `IsEllSequence` ambient ring exactly |
| 2 | `[IsReduced R]`            | reduced ring (no nilpotents)   | a non-degeneracy condition (reduced is one)    | SIDEWAYS, not weaker | a *clean global* non-degeneracy hypothesis; the sibling `zero` uses the *local* `W(2m) ∈ R⁰` instead — **incomparable**, neither subsumes the other (a reduced ring may have all even terms zero-divisors; a non-reduced ring may still have a regular even term). Both are legitimate; mathlib routinely keeps both kinds of entry point. |
| 3 | `ell : IsEllSequence W`    | the EDS hypothesis             | the EDS hypothesis                             | NO                  | the defining hypothesis; cannot be removed |

### Generality verdict (Phase 4b)

The current form is: **AT A NATURAL GENERALITY** — `[CommRing R] [IsReduced R]` is exactly the clean
hypothesis set the literature uses for the reduced-ring branch of this fact. Weakening opportunities that
would make it *strictly more general*: **0** (the `IsReduced` and the `W(2m) ∈ R⁰` branches are siblings,
not a generality ladder). No restatement needed for generality.

Optional **polish** (not a generalisation, not blocking — would be a `/cleanup` nicety on upstreaming):
the last line could use mathlib's purpose-built idiom
`eq_zero_of_pow_eq_zero this` (from `Mathlib/Algebra/GroupWithZero/Basic.lean:195`,
`theorem eq_zero_of_pow_eq_zero [IsReduced R] (h : x ^ n = 0) : x = 0`) instead of the manual
`IsReduced.eq_zero _ ⟨_, this⟩`. Same statement, same generality — purely cosmetic. This is why the
verdict is **YES-add-as-is** rather than **YES-but-generalise-first**: there is nothing to *generalise*,
only an optional one-token idiom swap.

### Modern-idiom check (Phase 4c)

| # | Question                                                          | Applies? | Note |
|---|-------------------------------------------------------------------|----------|------|
| 1 | bundled hypotheses → typeclasses?                                 | already  | non-degeneracy is already supplied as the typeclass `[IsReduced R]` — the modern idiom |
| 2 | sequences/metric → filters/topology?                              | no       | purely algebraic identity; no topology |
| 3 | construction → universal property?                               | no       | no object constructed |
| 4 | set+closure-pred → bundled substructure?                         | no       | `IsEllSequence` is a `Prop`, appropriately |
| 5 | field-specific → weaken typeclass?                               | no       | already at `CommRing` + the minimal extra `IsReduced`; does not assume a field/domain (a genuine generalisation *beyond* the textbook field statement) |
| 6 | 1-categorical → higher-categorical?                              | no       | n/a |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                 | no       | EDS are definitionally ℤ-indexed (Ward); not a generalisation axis |

Modern idiom available: the lemma already *uses* the modern idiom (typeclass `[IsReduced R]` for the
non-degeneracy, generalising the classical field/domain statement to any reduced commutative ring).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or instance-search paths).

---

### Mathlib search-status: `IsEllSequence.zero'` (Phase 5)

[A] Lean-Finder       "elliptic sequence zeroth term zero" / "W 0 = 0 elliptic"        → no decl (only `IsEllSequence` predicate + `*_zero` lemmas about `preNormEDS`/`normEDS`, see below)
[B] Loogle            `IsEllSequence _ → _ 0 = 0`, `IsEllSequence _ → IsReduced _ → _`   → no hit
[C] LeanSearch        "the zeroth term of an elliptic sequence is zero in a reduced ring" → no hit
[D] Grep mathlib src  `zero'`, `IsEllSequence.zero`, `W 0 = 0` in `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **no match**
[E] Name pattern      `IsEllSequence.zero'` / `IsEllSequence.zero`                       → **no such decl in mathlib**

**Decisive negative.** The project's pinned mathlib EDS file
(`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, 547 lines) contains the
predicate `IsEllSequence` (lines 82–84) and the closure lemmas `IsEllSequence.smul` / `.map`, then jumps
**straight to `preNormEDS'`** (line 124). There is **no `namespace IsEllSequence` API at all** — no `zero`,
no `zero'`, no `neg`, no `oddRec`/`evenRec`/`rel₄`/`net`/`invar`. The only `*_zero` lemmas upstream are
about the *concrete normalised sequences* (`preNormEDS'_zero`, `preNormEDS_zero`, `normEDS_zero`,
`complEDS_zero`, …), i.e. "the constructed example has `W(0) = 0`" — a different statement from
"*any* elliptic sequence over a reduced ring has `W(0) = 0`". So the abstract fact about the *predicate*
is genuinely **absent from mathlib**.

Cross-check inside the monorepo (where else `W 0 = 0` lives — to be sure this is not a known-elsewhere dup):
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:653` — **the target** (`zero'`, `[IsReduced R]`).
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:660` — sibling `zero` (`W (2*m) ∈ R⁰`).
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:625` — a second copy of `zero'` in the project's own "Original" fork file.
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:530` — `IsEllSequence.zero` (the **non-zero-divisor** version) — but **HasseWeil has NO `zero'`** (no reduced-ring version).
None of these is mathlib; all are project forks. So `zero'` is a **project-original** lemma, not a
mathlib dedup case.

Concluded: **NOT found in mathlib in any form** (neither the exact lemma nor a more general one).

---

### Composition check (Phase 6)

#### Call sites — `IsEllSequence.zero'`

Internal use count (this file, excluding the decl itself): **0 direct** at the time of writing — `zero'`
is a stated structural fact; the downstream `rel₄`/`net`/`invar` chain (lines 690–700) routes through the
sibling `ell.zero 1 two` (the non-zero-divisor branch) rather than `zero'`. `zero'` is the clean
reduced-ring entry point intended for *consumers over reduced rings* (e.g. fields / `ℤ` / domains arising
in the Nagell–Lutz development), and is duplicated in the "Original" file (line 625), evidencing it is
deliberately kept API, not dead code.

#### Can ≤3 mathlib calls produce it?

**No.** The proof has two halves:
1. **Instantiate the EDS relation at `(0,0,0)` and ring-normalise to `(W 0)^4 = 0`.** This step is bespoke
   to `IsEllSequence` — it is *not* any mathlib lemma. Mathlib has the predicate but no lemma extracting
   "`W(0)·W(0)·W(0)² = 0`" or "`(W 0)^4 = 0`" from `IsEllSequence W`. You must apply `ell 0 0 0` and then
   `simp_rw [Rel₃, add_zero, sub_self, mul_assoc, ← pow_succ']` (an `add_zero`/`sub_self`/`pow` rewrite
   chain) by hand. There is no single mathlib primitive for it.
2. **Nilpotent ⇒ zero in a reduced ring.** *This* half is one mathlib call:
   `eq_zero_of_pow_eq_zero` (or `IsReduced.eq_zero _ ⟨_, _⟩`).

So mathlib supplies only half (2). Half (1) — the elliptic-relation manipulation — is the actual content
and is irreducibly EDS-specific. It is a *short* derivation (3 source lines), but it is **new API about a
mathlib predicate**, not an assembly of existing mathlib primitives. A `≤3 mathlib-call` one-liner that
produces `W 0 = 0` from only `IsEllSequence W` + `[IsReduced R]` **does not exist** in mathlib.

Conclusion: **NOT composable from mathlib primitives** — the elliptic-relation-at-`(0,0,0)` step is the
missing piece, and providing it *is* exactly the value of adding this lemma to mathlib's `IsEllSequence`
API.

---

## Verdict: `IsEllSequence.zero'`

**Category:** YES-add-as-is

**Evidence:**
- Literature (Phase 3): `W(0) = 0` for non-degenerate elliptic sequences is a **standard folklore fact**
  (Ward; the textbook normalisation `D₀ = 0`; the division-polynomial `Ψ₀ = 0`; and explicitly the
  commutative-ring treatment **arXiv:2604.05280**, Junyan Xu, *On Elliptic Sequences over Commutative
  Rings*, which references the mathlib `IsEllSequence` formalisation — i.e. the literature companion to
  this very track).
- Generality (Phase 4): **at a natural generality** — `[CommRing R] [IsReduced R]` is exactly the clean
  non-degeneracy hypothesis the literature uses for the reduced-ring branch; it already *generalises* the
  classical field/domain statement (modern idiom = typeclass `IsReduced`). The sibling `zero`
  (`W(2m) ∈ R⁰`) is an *incomparable* second entry point, not a stronger form — both belong. Only optional
  cosmetic polish (use `eq_zero_of_pow_eq_zero`); nothing to generalise.
- Mathlib search (Phase 5): **NOT in mathlib** — the pinned mathlib EDS file has the `IsEllSequence`
  predicate but *no* `namespace IsEllSequence` API and *no* `W 0 = 0` lemma about an arbitrary elliptic
  sequence (only `normEDS_zero`-style lemmas about the concrete constructed sequence, a different claim).
- Composition (Phase 6): **NOT composable in ≤3 mathlib calls** — the "instantiate the elliptic relation
  at `(0,0,0)` ⇒ `(W 0)^4 = 0`" step is bespoke to `IsEllSequence` and exists in no mathlib primitive;
  mathlib supplies only the trailing "nilpotent ⇒ 0 in a reduced ring" half.

**Rationale:**

`IsEllSequence.zero'` is a small but genuinely useful structural lemma about a *mathlib* predicate
(`IsEllSequence`, due to David Kurniadi Angdinata): over a reduced commutative ring, every elliptic
sequence has `W 0 = 0`. The fact is textbook-standard for non-degenerate elliptic sequences, and the
reduced-ring hypothesis is the clean, idiomatic typeclass way to supply the needed non-degeneracy
(generalising the usual field/domain statement). Mathlib currently stops at the `IsEllSequence` predicate
plus its `smul`/`map` closure lemmas and has *no* basic-properties API — no `W 0 = 0`, no `neg`/oddness, no
recurrence bridge — so this lemma fills a real gap rather than duplicating or recomposing existing content.
The "instantiate at `(0,0,0)`" core of the proof is irreducibly EDS-specific (mathlib has no primitive for
it), so it is not a ≤3-call composition. It should be added to mathlib essentially verbatim as one of the
foundational facts of the `IsEllSequence` API.

**WHY add (contribution-actionable):**
This is part of building out mathlib's `IsEllSequence` basic-properties API — a layer that the upstream EDS
file is missing and that the surrounding literature (notably Xu's commutative-rings paper, which cites the
mathlib formalisation) treats as foundational. `zero'` is the reduced-ring entry point; its sibling `zero`
(non-zero-divisor even term) is the local entry point. Both are natural, both are wanted, neither is
derivable from current mathlib.

Proposed mathlib decl:        `IsEllSequence.zero'` (or, on upstreaming, a name like
                              `IsEllSequence.apply_zero` / `IsEllSequence.map_zero_eq_zero` to fit
                              mathlib's naming for "value at `0` is `0`" — the maintainers' call; the
                              `zero'` primed name is a *local* disambiguator from the sibling `zero` and
                              would likely be renamed).
Natural home:                 `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, in a new
                              `namespace IsEllSequence` block of basic facts (next to where the sibling
                              `zero`, and later `neg`, oddness, and the recurrence bridge, would also land).
Suggested statement (verbatim-ish, with the optional polish):
```lean
namespace IsEllSequence
variable {R : Type*} [CommRing R] {W : ℤ → R} (ell : IsEllSequence W)
include ell

/-- The zeroth term of an elliptic sequence over a reduced ring is zero. -/
lemma zero' [IsReduced R] : W 0 = 0 := by
  have := ell 0 0 0
  simp_rw [add_zero, sub_self, mul_assoc, ← pow_succ'] at this
  exact eq_zero_of_pow_eq_zero this   -- Mathlib/Algebra/GroupWithZero/Basic.lean
end IsEllSequence
```
(In upstream mathlib `IsEllSequence` is the def directly — no separate `Rel₃` — so the `Rel₃` rewrite is
dropped; the `this` already has the unfolded relational shape.)

Caveat for the contributor (does **not** change the verdict): this NagellLutz file is a *forked + extended*
EDS track that redeclares mathlib's `IsEllSequence`/`Rel₃`/`normEDS` block locally (it imports neither
`Mathlib.NumberTheory.EllipticDivisibilitySequence` nor the `DivisionPolynomial` track). When this lemma is
upstreamed, it should be **stated against mathlib's own `IsEllSequence`** (which is defeq to the project's
via `Rel₃`), and the project's three local copies (`EllipticDivisibilitySequence.lean:653`,
`EllipticDivisibilitySequenceOriginal.lean:625`, and — for the *sibling* `zero` — HasseWeil:530) should
later be collapsed onto the upstream API. That de-fork is a larger structural consolidation; the per-decl
verdict here is simply that **this lemma is new, standard, and wanted in mathlib**.

---

## Next step

Open a mathlib PR adding the **basic `IsEllSequence` properties** layer, starting with `W 0 = 0`. Add
`zero'` (reduced-ring) — and naturally its sibling `zero` (non-zero-divisor even term) — to
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` in a new `namespace IsEllSequence` block, stated
against mathlib's own `IsEllSequence` (the project's `Rel₃` is defeq), using `eq_zero_of_pow_eq_zero` for
the nilpotent-to-zero step. Coordinate naming with maintainers (`zero'` is a local disambiguator; upstream
likely prefers `apply_zero`/`map_zero_eq_zero`-style). This is a contribution, not a dedup — mathlib does
not currently have it in any form. Reference: arXiv:2604.05280 (Junyan Xu), *On Elliptic Sequences over
Commutative Rings*.
