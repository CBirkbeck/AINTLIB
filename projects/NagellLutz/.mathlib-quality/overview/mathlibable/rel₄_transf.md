# Mathlibable assessment — `EllSequence.HaveSameParity₄.rel₄_transf`

- **Verdict:** `NO-mathlib-has-it`
- **Qualified name:** `EllSequence.HaveSameParity₄.rel₄_transf`
- **One-line rationale:** Identical to `IsEllipticNet.atomRel_avg_sub` in open, active mathlib PR #25989 (same author, same defs, same parity-reflection statement) — re-adding would duplicate in-flight upstream.
- **Date:** 2026-06-18
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:280`

---

## 0. Baseline (Phase 0)

- lake build: ⚠ not run (local build stale, per task note) — reasoned from source + mathlib grep + PR-diff fetch.
- decl `EllSequence.HaveSameParity₄.rel₄_transf`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:280`.
  Namespaces: `namespace EllSequence` (line 90) → `section transf` (line 202) → `namespace HaveSameParity₄`
  (line 216). So the **true qualified name is `EllSequence.HaveSameParity₄.rel₄_transf`** — confirming the
  prompt's parsed guess (the `section transf` does not contribute to the name; the `HaveSameParity₄` namespace
  does).
- kind: **theorem** (NOT a `def`; Phase 4.5 diamond/defeq analysis is n/a).
- has sorry: **no**.
- module docstring summary: Elliptic divisibility sequences (EDS). Defines `IsEllSequence`, `normEDS`,
  `preNormEDS`, and the project's own four-index relational apparatus
  (`addMulSub`, `rel₄`, `net`, `HaveSameParity₄`, `avg₄`, `StrictAnti₄`, the `transf` suite) used to prove
  `normEDS` is an EDS. **Forks/extends `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (same copyright
  header: David Kurniadi Angdinata).

---

## 1. Statement (Phase 1)

`rel₄_transf` is the theorem (lines 280–284):

```lean
theorem rel₄_transf :
    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf (W := W)
  simp_rw [rel₄, h₁, h₂, h₃, h₄, h₅, h₆, addMulSub₄_mul_addMulSub₄]; ring
```

Mathematically: for a commutative ring `R`, a sequence `W : ℤ → R`, and four integers `a, b, c, d` of the
**same parity** (`same : HaveSameParity₄ a b c d`, i.e. `a.negOnePow = b.negOnePow = c.negOnePow =
d.negOnePow`), with `avg₄ a b c d = (a + b + c + d) / 2`, the four-index elliptic relation `rel₄` is
**invariant under the reflection of the four indices through their average**:

> `rel₄ W (μ − d) (μ − c) (μ − b) |μ − a| = rel₄ W a b c d`, where `μ = avg₄ a b c d`.

This is a genuine, non-obvious **symmetry of the elliptic relation**. The map `xᵢ ↦ μ − xᵢ` is the reflection
of the multiset `{a,b,c,d}` about its mean `μ` (note `Σ(μ − xᵢ) = 4μ − Σxᵢ = 2·Σxᵢ − Σxᵢ = Σxᵢ` by
`avg₄_add_avg₄`, so the reflected indices have the *same* average — the transformation is an involution on
the relevant index set). The absolute value `|μ − a|` on the last slot is cosmetic: `addMulSub`/`rel₄` is
invariant under the sign of any index (`addMulSub_abs₁`, `addMulSub_neg₁`), so `|μ − a|` and `μ − a` give the
same value; it is written with `| |` only so the reflected 4-tuple is non-negative and strictly decreasing
(this is what `transf` / `strictAnti₄_transf` at lines 286–295 are arranged to deliver, feeding the
strong-induction descent in `rel₄_of_min₂` etc.).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (fully general; no field/domain/characteristic hypothesis).
- `(W : ℤ → R)` — the sequence.
- `{a b c d : ℤ}` — four indices.

Hypotheses (Lean side):
- `same : HaveSameParity₄ a b c d` — the four indices share parity (`include`d via the section). **Essential**:
  it is what makes `avg₄ = (a+b+c+d)/2` exact (the sum is even, `even_sum`) and the reflected differences
  integer-meaningful.

Conclusion (math): the elliptic relator is invariant under reflection of its four indices through their mean.
Conclusion (Lean): `rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| = rel₄ W a b c d`.

The proof is a one-screen reduction: expand `rel₄` on both sides, rewrite the six `addMulSub` products of the
LHS into the `addMulSub₄` hybrids via the packaged `same.addMulSub_transf` (the immediately-preceding lemma,
lines 270–278), collapse pairs with `addMulSub₄_mul_addMulSub₄` (line 264), and finish with `ring`.

---

## 2. Preliminary checks (Phase 2)

### 2a. Size classification

Verdict: **SMALL** (in the `/overview` triage sense), but it is a **named, load-bearing API lemma**, not a
throwaway. It is one of the ~16 `HaveSameParity₄.*` lemmas — specifically the **reflection-symmetry** member
of the `transf` suite (`addMulSub_transf` → `rel₄_transf` → `transf`/`strictAnti₄_transf`). Its parents `rel₄`,
`addMulSub`, `avg₄`, `HaveSameParity₄` are the substantive objects; this is a symmetry statement about them.
(Literature width is EXHAUSTIVE regardless — the `net`/`rel₄` concepts are squarely Stange/Ward/Xu, and the
symmetries of the relation are themselves a studied object, so the search is well-grounded.)

### 2b. One-line check

Kind is `theorem`, not `def`/`abbrev`/`structure` — **one-line check n/a**. The decl carries a real
(multi-line) proof. Note recorded; check skipped. No diamond/defeq concern (Phase 4.5 n/a).

---

## 3. Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic net relation symmetry four indices reflection average Stange EDS S4 permutation invariance" | yes | symmetries of the elliptic/net relation are a studied object | surfaced **"On Symmetries of Elliptic Nets and Valuations of Net Polynomials"** (arXiv:1408.6623, J. Number Theory) + Stange formulary |
| 2 | WebSearch (general/origin) | "Stange elliptic nets definition four-index relation; Ward EDS three-index relation" (via sibling reports + #1) | yes | net relator `W(p+q+s)W(p−q)W(r+s)W(r) − … = 0`; Ward 3-index relation | the `rel₄`/`net` relation itself is textbook-standard (arXiv:0710.1316; Wikipedia EDS) |
| 3 | WebSearch (named-after/aliases) | "elliptic relation symmetric quartic addMulSub half-index; On Elliptic Sequences over Commutative Rings" | yes | Xu 2026 (arXiv:2604.05280) "4-parameter highly symmetric family of homogeneous quartic relations = elliptic relations" | the symmetric-quartic packaging `rel₄` lives in; symmetries are its raison d'être |
| 4 | ChatGPT MCP | standard-name + status of the reflection/averaging symmetry of the elliptic relator | n/a | — | MCP down per task note; compensated by 3 WebSearch generality levels + the **decisive PR-diff fetch** (Phase 5) |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` + `refs/NagellLutz/` | n/a | (no project refs dir; `references/` absent) | reused the sibling reports `rel₄.md`/`net.md`/`rel₄_eq_net.md`/`HaveSameParity₄.md` as internal references |
| 6 | nLab | "elliptic divisibility sequence" / "elliptic net" | no | — | nLab has no EDS/elliptic-net page (not a category-theory topic). n/a-by-absence. |
| 7 | nCatLab (categorical) | — | n/a | — | not a categorical concept (an integer-recurrence symmetry). |
| 8 | Stacks Project (alg geom) | — | n/a | — | Stacks has no EDS/elliptic-net material. |
| 9 | MathOverflow / MSE | "elliptic net relation symmetry / equivalence Ward Stange" | yes (corroborative) | confirms Ward↔Stange + symmetry discussions | no thread on this *specific* reflection lemma; corroborates the broader picture. |
| 10 | recent arXiv (last 5 yrs) | (via #1, #3) symmetries of elliptic nets; Xu 2026 commutative-ring EDS; Stange 2025 isogeny division polynomials | yes | symmetries of the relation are live, named, in active use | the project's `transf` suite is the Lean realisation of these symmetries. |
| 11 | mathlib GitHub **PR** search (DECISIVE — Phase 5) | `IsEllipticNet atomRel atom rel` over leanprover-community/mathlib4 PRs | **yes** | **`IsEllipticNet.atomRel_avg_sub`** in **open PR #25989** | byte-identical defs + identical parity-reflection statement, same author. See Phase 5. |

The protocol passed: WebSearch ran ≥3 distinct generality levels (specific reflection-symmetry, general
relation, named-after/aliases); local refs + sibling reports checked; nLab/nCatLab/Stacks each recorded
n/a-with-reason; MO/MSE + arXiv corroborate; ChatGPT MCP recorded n/a (down), more than compensated by the
verbatim PR-diff fetch in Phase 5.

### Literature summary

Concept identified as: a **symmetry of the elliptic (net) relation** — the invariance of the four-index
elliptic relator under reflecting its indices through their average. The underlying relation is the
Ward(1948)↔Stange(2007) elliptic-net relation, packaged in the modern fully-`S₄`-symmetric "elliptic
relation" form of Xu (2026, arXiv:2604.05280). Symmetries of net polynomials/relations are a named, studied
object (arXiv:1408.6623). Sources agree the relation and its symmetries are standard; this particular
reflection symmetry is exactly the content of mathlib PR #25989's `atomRel_avg_sub`.

Most general standard form: holds for any `W : ℤ → R` over a commutative ring `R`, four same-parity integer
indices — which is exactly the project's (and the PR's) generality. The same-parity hypothesis is the genuine
domain of validity (it makes `avg₄` exact), not a narrowing.

Disagreement with the literature: **none** — faithful, maximally-general (`CommRing`) formalisation of a real
symmetry of the elliptic relation.

---

## 4. Generality analysis (Phase 4)

Literature-standard form: the reflection symmetry of the elliptic relator over a commutative ring, with the
same-parity precondition. The mathlib PR form (`atomRel_avg_sub`) is identical generality.

| # | Parameter / hypothesis | Current Lean form | Literature / PR-standard form | Weaker form? | Reason |
|---|------------------------|-------------------|-------------------------------|--------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (PR #25989; Xu 2026) | **NO** (already maximal) | `rel₄`/`addMulSub` are polynomial expressions in `W`-values; `CommRing` is the floor, already more general than the classical field/ℤ. |
| 2 | `(W : ℤ → R)` | sequence ℤ → R | same | NO | the relation is *about* such sequences. |
| 3 | `same : HaveSameParity₄ a b c d` | four same-parity indices | same-parity precondition (PR: `s%2=p%2 ∧ …`) | NO | **essential** — makes `avg₄=(a+b+c+d)/2` exact (`even_sum`); without it the reflected differences and the equality break. The PR carries the identical hypothesis (in `% 2` form vs the project's `negOnePow` form — equivalent). |
| 4 | `{a b c d : ℤ}` | integer indices | integer indices | NO | indices of an integer-indexed sequence. |

### Generality verdict (4b)

The current form is: **MAXIMALLY GENERAL**. Weakening opportunities: **0**. (`CommRing` is the floor; the
parity hypothesis is the domain-of-validity, not a narrowing.) No restatement needed.

### Modern-idiom check (4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | "let X be a foo" preamble → typeclass? | no | `HaveSameParity₄` is already a clean `Prop` bundle with dot-notation; the PR uses a raw `% 2` conjunction — if anything the project's `negOnePow` bundle is the *more* idiomatic of the two, but both are fine. |
| 2 | sequences/metric → filters/topology? | no | purely algebraic identity (Stange's "net" is an elliptic net, **not** a topological net). |
| 3 | construction → universal property? | no | it is an equality of two relator-expressions. |
| 4 | set-with-predicate → bundled substructure? | no | none involved. |
| 5 | vector-space/field-specific → weaken typeclass? | no | already at `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | elementary commutative algebra. |
| 7 | concrete index ℤ → arbitrary group/monoid? | no | the parity (`negOnePow`) structure the lemma is *about* is intrinsic to ℤ; generalising the index group dissolves it. |

Modern-idiom verdict: **no** improving reformulation. The lemma is already at the contemporary `CommRing`
generality with idiomatic `negOnePow`-based parity. (The only delta vs. the mathlib PR is `negOnePow` bundle
vs. `% 2` conjunction for the hypothesis — a cosmetic convention difference, not a modernisation move, and
arguably the project's `negOnePow` form is the cleaner one. This does not change the bucket: the PR already
*has* the lemma.)

### 4.5 Diamond/defeq risk

n/a — declaration kind is **theorem** (introduces no definitional equalities or typeclass-search paths).

---

## 5. Mathlib search — five methods (Phase 5)

[A] Lean-Finder — index unavailable locally; substituted by grep [D] + the live PR-diff fetch. n/a: tool offline.
[B] Loogle — `rel₄ _ _ _ _ _ = _` / `?a = rel₄ _ _ _ _ _`: **no hits** — `rel₄`/`addMulSub`/`avg₄` are not
    symbols in the pinned mathlib, so no Loogle pattern can match.
[C] LeanSearch — "elliptic relation invariant under reflection of indices through average, same parity":
    **no hit in the pinned mathlib** (it has no elliptic-net/`rel₄` API at all).
[D] Grep pinned mathlib src (`d90090f`) — `grep -rn "IsEllipticNet\|atomRel\|atomRel_avg_sub\|def atom\b\|rel₄\|addMulSub\|HaveSameParity₄\|avg₄"`
    over `.lake/packages/mathlib/Mathlib/`: **no relevant hits**. The only `.atom` matches are
    string-diagram / tactic-widget internals (`Tactic/Widget/StringDiagram.lean`, `Tactic/Ring/Basic.lean`,
    linters) — entirely unrelated. The mathlib EDS file
    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) contains **only**
    `IsEllSequence`/`IsDivSequence`/`IsEllDivSequence`/`preNormEDS`/`normEDS`/`complEDS` — **no** four-index
    relator, **no** `atom`/`atomRel`/`rel₄`/`net`, **no** parity-reflection lemma.
    `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`: no Stange/`rel₄`/`net`.
[E] Name pattern — `rel₄_transf` / `atomRel_avg_sub` / `*_avg_sub` in the pinned mathlib tree: **no hits**.

**DECISIVE — mathlib PR search.** Open, active **PR #25989** ("feat(NumberTheory/EllipticDivisibilitySequence):
add elliptic nets", author **David Kurniadi Angdinata / `Multramate` — the very author of this project file**;
companion rename PR #25990) adds, in `namespace IsEllipticNet` with context
`variable {R : Type u} [CommRing R] (W : ℤ → R)`:

```lean
def atom (p q : ℤ) : R := W ((p + q).tdiv 2) * W ((p - q).tdiv 2)           -- ≡ project addMulSub (line 94, verbatim)

def atomRel (p q r s : ℤ) : R :=
  atom W p q * atom W r s - atom W p r * atom W q s + atom W p s * atom W q r -- ≡ project rel₄ (line 103, verbatim structure)

def rel (p q r s : ℤ) : R :=                                                 -- ≡ project net (line 115, verbatim)
  W (p + q + s) * W (p - q) * W (r + s) * W r - W (p + r + s) * W (p - r) * W (q + s) * W q
    + W (q + r + s) * W (q - r) * W (p + s) * W p
```

and the lemma (the match for `rel₄_transf`):

```lean
lemma atomRel_avg_sub {p q r s : ℤ}
    (parity : s % 2 = p % 2 ∧ s % 2 = q % 2 ∧ s % 2 = r % 2) :
    atomRel W ((p + q + r + s) / 2 - s) ((p + q + r + s) / 2 - r)
      ((p + q + r + s) / 2 - q) ((p + q + r + s) / 2 - p) =
    atomRel W p q r s
```

This is **exactly `rel₄_transf`** under the dictionary `addMulSub ↔ atom`, `rel₄ ↔ atomRel`, `net ↔ rel`,
`avg₄ a b c d = (a+b+c+d)/2 ↔ (p+q+r+s)/2`, and `HaveSameParity₄ (negOnePow) ↔ (% 2)` parity. The PR also
carries the matching siblings of the project's `transf`/symmetry suite: `atomRel_same₁₂…₃₄`,
`atomRel_neg₁…₄`, `atomRel_abs₁…₄`, `atom_abs_left/right`, `map_atomRel`, `rel_eq`, `isEllSequence`, etc.
(The project's `|avg₄ − a|` differs from the PR's plain `(p+q+r+s)/2 − p` only by an absolute value on the
last slot, which `atom`/`addMulSub` ignores — `atom_abs_right` / `addMulSub_abs₁` — so the two statements are
definitionally the same content.)

**Conclusion:** not in mathlib's released/pinned tree, **but the identical lemma exists in mathlib's pipeline
as `IsEllipticNet.atomRel_avg_sub` in open PR #25989** (by the project file's own author). The project track
`addMulSub`/`rel₄`/`net`/`HaveSameParity₄.*` is an earlier-named development copy of that PR.

---

## 6. Composition / call-sites (Phase 6)

### 6.0 Call sites of `rel₄_transf`

Internal use count (NagellLutz, excluding the declaring line 280): **1** — at
`EllipticDivisibilitySequence.lean:491` (`rw [← same.rel₄_transf]`), inside the descent machinery that turns a
general same-parity `rel₄` into one on a strictly-decreasing non-negative 4-tuple (paired with
`strictAnti₄_transf`, line 290, and `six_le_of_strictAnti₄`, used by `rel₄_of_min₂` / the strong-induction in
`rel₄_of_anti_oddRec_evenRec`).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/EllipticDivisibilitySequence.lean:491` | `rw [← same.rel₄_transf]` (the live internal consumer) |
| `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:236, 406` | **fork copy** of the same theorem + its use (independent project needs it) |
| `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:269, 468` | **dead duplicate track** (slated for deletion per `05-duplications.md`) |

Inline-derivation grep: none — the reflection symmetry is always invoked through `rel₄_transf`, never
re-derived inline. K = 1 live internal use **plus a cross-project fork copy in HasseWeil** → a genuine,
duplicated-across-projects API lemma (an upstreaming signal), not dead code and not a one-off to inline.

### 6a. Composition from mathlib

Can `rel₄_transf` be derived from **mathlib** in ≤3 chained calls? **No** — it cannot even be *stated* using
only the pinned mathlib: `rel₄`, `addMulSub`, `avg₄`, `HaveSameParity₄` are project decls absent from mathlib.
The proof composes from the project's own `addMulSub_transf` + `addMulSub₄_mul_addMulSub₄` + `ring`, none of
which are mathlib primitives. So `NO-composable-from-mathlib` does **not** fit: there is no mathlib building
block to inline. **NOT-COMPOSABLE from mathlib.** The decisive fact is not composability but that the identical
lemma already exists in mathlib's pipeline (PR #25989) — hence `NO-mathlib-has-it`.

---

## 7. Verdict

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the symmetries of the elliptic (net) relation are a named, studied object
  (arXiv:1408.6623; Stange formulary; Xu 2026 arXiv:2604.05280). `rel₄_transf` is the reflection-through-the-mean
  symmetry of the relator. Standard, maximally-general (`CommRing`).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (`CommRing`; parity hypothesis is the genuine domain of
  validity). Modern-idiom (4c): no improving reformulation (the only delta vs. the PR is `negOnePow` vs `% 2`
  for the hypothesis — cosmetic).
- Mathlib search (Phase 5): **not in the pinned/released mathlib**, but **identical to
  `IsEllipticNet.atomRel_avg_sub` in OPEN, ACTIVE mathlib PR #25989** — byte-identical `atom`/`atomRel` defs,
  identical parity-reflection statement, **same author** (Multramate / David Kurniadi Angdinata).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (cannot even be stated in pinned mathlib).
  K = 1 live internal use + a HasseWeil fork copy.

**Rationale.**

`EllSequence.HaveSameParity₄.rel₄_transf` states that the four-index elliptic relator `rel₄` is invariant
under reflecting its four (same-parity) indices through their average `avg₄ = (a+b+c+d)/2`. This is one
member of the project's `transf` symmetry suite (`addMulSub_transf` → `rel₄_transf` → `transf`/
`strictAnti₄_transf`), used to reduce an arbitrary same-parity relation to one on a strictly-decreasing
non-negative 4-tuple for the strong-induction descent. The pinned mathlib (`d90090f`) has none of this
vocabulary — its EDS file stops at the 3-index `IsEllSequence`/`normEDS`. **But mathlib PR #25989 ("add
elliptic nets", authored by this file's own author) adds exactly this lemma as `IsEllipticNet.atomRel_avg_sub`,
with character-for-character-identical `atom` (= `addMulSub`) and `atomRel` (= `rel₄`) definitions and the
identical same-parity reflection statement** `atomRel W ((p+q+r+s)/2 − s) … ((p+q+r+s)/2 − p) = atomRel W p q r s`.
The project's `|avg₄ − a|` vs the PR's `(p+q+r+s)/2 − p` differ only by an absolute value the `atom`/`addMulSub`
building block ignores (`atom_abs_right` / `addMulSub_abs₁`), so the content is definitionally the same. The
project's whole `addMulSub`/`rel₄`/`net`/`HaveSameParity₄.*` track is an earlier-named development copy of that
PR (this is precisely the finding the sibling `net.md` report reached, with the same dictionary `net ↔
IsEllipticNet.rel`, `addMulSub ↔ atom`, `rel₄ ↔ atomRel`). Re-contributing `rel₄_transf` to mathlib would
duplicate and conflict with #25989.

Because the identical primitive+lemma already live in mathlib's pipeline, `NO-composable-from-mathlib` is not
the right bucket (there is nothing in *released* mathlib to compose or inline from), and the YES buckets are
wrong (the canonical author already owns this in an active mathlib PR; shipping it again would be a duplicate).
The five-bucket rubric has no separate "mathlib-PR-in-flight" bucket; the closest and operationally-correct one
is `NO-mathlib-has-it` — consistent with the sibling `net.md` verdict for the same fork.

**WHY not (refactor-actionable).** Mathlib's pipeline already has it — `IsEllipticNet.atomRel_avg_sub` in open
PR #25989 (by `Multramate`, same author; companion rename PR #25990).

Existing decl (in-flight upstream): `IsEllipticNet.atomRel_avg_sub` (mathlib PR #25989, branch `EllipticNet`).
Our form follows directly (it *is* the same lemma) under the dictionary:
```text
EllSequence.addMulSub                      ↦ IsEllipticNet.atom
EllSequence.rel₄                           ↦ IsEllipticNet.atomRel
EllSequence.net                            ↦ IsEllipticNet.rel
EllSequence.avg₄ a b c d = (a+b+c+d)/2     ↦ (p+q+r+s)/2
HaveSameParity₄ (via negOnePow)            ↦ parity : s%2=p%2 ∧ s%2=q%2 ∧ s%2=r%2
EllSequence.HaveSameParity₄.rel₄_transf    ↦ IsEllipticNet.atomRel_avg_sub
```
(the `|avg₄ − a|` ↔ `(p+q+r+s)/2 − p` gap closes via `atom_abs_right` / `addMulSub_abs₁`).

Call sites in this project (from Phase 6.0): **K = 1** live internal use (`EllipticDivisibilitySequence.lean:491`),
plus a HasseWeil fork copy (`Auxiliary/EllipticDivisibilitySequence.lean:236/406`) and the dead
`…Original.lean` copy.

Refactor plan (consolidation): do **not** file this as a to-mathlib candidate. Track PR #25989/#25990 upstream.
Once they merge: drop the project's forked `addMulSub`/`rel₄`/`net`/`HaveSameParity₄.*` track and import
mathlib's `IsEllipticNet` API; rewrite the single live call site
`EllipticDivisibilitySequence.lean:491` (`rw [← same.rel₄_transf]`) as `rw [← IsEllipticNet.atomRel_avg_sub …]`
(supplying the `% 2` parity from the existing `same`/`negOnePow` hypothesis, e.g. via `Int.negOnePow_eq_iff` /
an `emod`-bridge), reconciling the `|·|`-on-last-index spelling with `atom_abs_right`. Deduplicate the two
other in-repo copies (HasseWeil fork; dead `…Original`) at the same time so there is one source of truth that
simply imports the upstream lemma. This is a **fork-vs-upstream dedup, not new mathlib API.**

### Caveat / nuance
PR #25989 is **open, not yet merged**, so strictly the lemma is "in the mathlib *pipeline*" rather than in a
released tag. The rubric has no "mathlib-PR-in-flight" bucket; `NO-mathlib-has-it` is the closest and
operationally-correct choice (the canonical author already owns this in mathlib; the action is align-with-PR,
not re-derive). A human consolidator may prefer to record the PR number rather than treat mathlib as already
shipping it. This does **not** change the recommendation: do not re-add.

---

## Next step

Do not upstream `rel₄_transf` independently. Track mathlib PR #25989 ("add elliptic nets") / #25990 (rename);
when merged, delete the project's forked `addMulSub`/`rel₄`/`net`/`HaveSameParity₄.transf` track (and the
HasseWeil + `…Original` duplicate copies) and import `IsEllipticNet.atomRel_avg_sub`, rewriting the lone live
consumer at line 491 accordingly. Consistent with the sibling `net.md` verdict for the same fork.

## Evidence
- Project source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:280` (`theorem rel₄_transf`);
  defs at lines 94 (`addMulSub`), 103 (`rel₄`), 115 (`net`), 214 (`avg₄`), 210 (`HaveSameParity₄`); helper
  `addMulSub_transf` at 270, `addMulSub₄_mul_addMulSub₄` at 264; live consumer at 491.
- Pinned mathlib (`d90090f`): `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  (547 lines) — no `IsEllipticNet`/`atom`/`atomRel`/`rel₄`/`net`/`atomRel_avg_sub` (grep-confirmed).
- mathlib **PR #25989** "feat(NumberTheory/EllipticDivisibilitySequence): add elliptic nets" (OPEN, author
  `Multramate`) — `IsEllipticNet.atom`/`atomRel`/`rel` defs + `atomRel_avg_sub` lemma (verbatim signature
  quoted in Phase 5; fetched from the PR `.diff`).
- mathlib **PR #25990** "chore(...): rename definitions" (OPEN, `Multramate`) — companion.
- Sibling reports (internal references): `net.md` (NO-mathlib-has-it, same fork, found PR #25989),
  `rel₄.md`, `rel₄_eq_net.md`, `HaveSameParity₄.md`.
- Literature: K. Stange, *Elliptic Nets and Elliptic Curves*, arXiv:0710.1316; *On Symmetries of Elliptic Nets
  and Valuations of Net Polynomials*, arXiv:1408.6623; J. Xu, *On Elliptic Sequences over Commutative Rings*,
  arXiv:2604.05280; M. Ward, *Memoir on Elliptic Divisibility Sequences*; Stange, *Formulary for EDS and
  elliptic nets*.
