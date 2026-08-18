# /mathlibable report — `EllSequence.rel₄_abs`

> Step-9 (overview) mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> divisibility sequences; division polynomials). Run with the local Lean build **stale** (Phase 0
> build artifacts empty); reasoning is from the source statement, the vendored mathlib source tree
> (`.lake/packages/mathlib`, rev `d90090f`), WebSearch, and grep. ChatGPT MCP (Codex) was **down**
> this session — its channel is recorded `n/a (tool down)` and compensated by extra WebSearch + grep.
> This report reuses the settled sibling verdicts in this same directory
> (`addMulSub_abs₀.md`, `addMulSub_abs₁.md` — both NO-composable; `rel₄.md` — the keystone `def`,
> YES-add-as-is only as part of upstreaming the whole fork), since `rel₄_abs` sits directly on top of
> those three.

---

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — fork-internal glue, a ≤3-call composition over a non-mathlib subject.

`rel₄_abs` is the four-index analogue of the sibling `addMulSub_abs₀`/`addMulSub_abs₁` lemmas: it
strips `|·|` off all four indices of the elliptic relation `rel₄`. Its subject `rel₄` (and the
building block `addMulSub`) **do not exist in mathlib**, so it can never be a standalone mathlib
lemma; granting the fork, its one-line proof is `simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]`
— exactly a 3-call composition (`rel₄` unfold + the two `addMulSub` abs lemmas). It rides along with
the `rel₄`/`addMulSub` API if that is ever upstreamed; it is never an independent contribution.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale (build/lib empty) — reasoned from source per task instructions
- decl `EllSequence.rel₄_abs`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:514`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences — defines `IsEllSequence`, `preNormEDS`,
  `normEDS`, and (unlike upstream mathlib) **proves** `isEllDivSequence_normEDS` via the
  `addMulSub`/`rel₄`/`net` Stange-net machinery. A forward-port / extension of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

**Namespace verification.** The lemma sits inside `namespace EllSequence` (opened line 90, closed
line 597), in `section Perm` (opened line 509) under `variable (neg : ∀ k, W (-k) = -W k)` +
`include neg` (lines 511–512). Parsed qualified name in the task prompt — `EllSequence.rel₄_abs` — is
**CORRECT** (confirmed against the project inventory at
`.mathlib-quality/overview/inventory/LutzNagell_EllipticDivisibilitySequence.md:689`,
`### lemma EllSequence.rel₄_abs`).

---

### Statement (Phase 1)

```lean
variable (neg : ∀ k, W (-k) = -W k)
include neg

lemma rel₄_abs {m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]
```

`rel₄_abs` states that the four-index elliptic relation `rel₄ W m n r s` is **invariant under taking
the absolute value of every one of its four integer indices**: `rel₄ W |m| |n| |r| |s| = rel₄ W m n r
s`, provided `W` is an **odd** sequence (`W (-k) = -W k`).

Here `rel₄` is a **project-local** definition (line 103):
`rel₄ W a b c d = addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d
+ addMulSub W a d * addMulSub W b c` — the signed sum over the three pairings of the four indices,
built from `addMulSub W m n := W ((m+n).tdiv 2) * W ((m−n).tdiv 2)` (line 94). The lemma is the
immediate four-fold lift of the sibling building-block lemmas `addMulSub_abs₀` (line 191:
`addMulSub W |m| n = addMulSub W m n`, needs `neg`) and `addMulSub_abs₁` (line 195:
`addMulSub W m |n| = addMulSub W m n`, unconditional): `rel₄` is a polynomial in `addMulSub` terms,
and each `addMulSub` factor is even in each argument, so the whole quartic is even in each index.

Variables / typeclasses (Lean side):
- `{R : Type u}` `[CommRing R]` — the codomain ring (file-level `variable`).
- `(W : ℤ → R)` — the sequence (file-level `variable`).
- `(neg : ∀ k, W (-k) = -W k)` — `W` is an **odd** sequence (the literature-standard odd property of
  EDS terms; `include`d for this whole `Perm` section).
- `{m n r s : ℤ}` — the four integer indices.

Hypotheses: `neg` (oddness of `W`).

Conclusion (math): the elliptic-relation quartic is unchanged by `|·|` applied to each of its four
indices, when `W` is odd.
Conclusion (Lean): `rel₄ W |m| |n| |r| |s| = rel₄ W m n r s`.

**Role in the development (why it exists).** The literature states the elliptic relation on
**non-negative, strictly descending** indices `a > b > c > d ≥ 0` (Xu 2026, see Phase 3). `rel₄_abs`
is exactly the bridge that reduces *arbitrary integer* indices to that non-negative case: its sole
consumer (line 579, inside `rel₄_of_oddRec_evenRec`) does `rw [← rel₄_abs neg]; change relFin4 W t =
0`, i.e. replace `rel₄ W a b c d` by `rel₄ W |a| |b| |c| |d| = relFin4 W ![|a|,|b|,|c|,|d|]`, which
the `relFin4_perm` machinery can then sort into descending order. It is formalization plumbing for the
"WLOG indices are non-negative" step.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: incidental congruence/normalisation helper for a Lean-local definition; not a named theorem,
not a `## Main statement`, introduces no structure. It is the four-index member of the
`addMulSub_*`/`rel₄_*` micro-API family (`rel₄_abs`, `rel₄_swap₀₁/₁₂/₂₃`, `rel₄_same₀₁/₁₂/₂₃`) that
normalise `rel₄` arguments so the big permutation proof (`relFin4_perm` → `rel₄_of_oddRec_evenRec`)
goes through.

(Note: literature width is EXHAUSTIVE regardless. The keystone `def` it rests on, `rel₄`, is BIG and
its own report is YES-add-as-is; this *lemma about it* is SMALL glue.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner *def* check is **n/a**. (For the record
the proof body is a single `simp_rw` line, reinforcing the SMALL classification.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence elliptic net relation invariant absolute value of indices even function W(-n)=-W(n) symmetric quartic" | partial | Ward symmetry; Stange net relation; "sign of an EDS" | confirms the *subject* (the elliptic/net relation, the odd property `W(-n)=-W(n)`) and that the literature studies `|W_n|` = abs of **values**; **no** named "abs of the four *indices*" invariance lemma |
|  2 | WebSearch (named-after / source) | "Junyan Xu 'On Elliptic Sequences over Commutative Rings' elliptic relation S4 symmetry permutation indices absolute value" | yes | **arXiv:2604.05280** — elliptic relation `E(a,b,c,d)`, "4-parameter, highly symmetric family of homogeneous quartic relations", stated for **`a>b>c>d≥0`** | the paper behind the `EllSequence`/`rel₄` API; states the relation on **non-negative descending** indices — precisely the regime `rel₄_abs` reduces to |
|  3 | WebSearch (general form)         | (covered by #1) "elliptic net 'net polynomial' Stange Ward three-term relation"                        | yes  | Ward 3-term + Stange net | both classical anchors; the abs-invariance is not stated separately in either — it is implicit (indices range over a free abelian group / are reduced WLOG) |
|  4 | ChatGPT MCP                      | (standard-form + generality + history prompt; then short retry)                                        | n/a  | —                   | **tool down** — Codex `exec` failed this session; compensated by extra WebSearch (#1–3) + grep (Phase 5 [D]) + the settled sibling reports |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/` ; `refs/NagellLutz/`                              | n/a  | —                   | no `references/` dir under this project's `.mathlib-quality/` (only `overview/`); `refs/` symlink absent. Recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                      | n/a  | —                   | nLab has no EDS / elliptic-net page; not a categorical concept (a recurrence on `ℤ → R`) |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                   | not categorical |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                   | not a scheme-theoretic statement (an integer-index parity/sign identity) |
|  9 | MathOverflow / Math.SE           | "elliptic relation symmetric four index absolute value indices" / "even function f(\|n\|)=f(n)"        | n/a  | —                   | the abs-invariance is folklore ("even ⟹ `f∘abs = f`" lifted to a polynomial); no canonical reference |
| 10 | recent arXiv (≤5 yrs)            | covered by #2 → arXiv:2604.05280 (Xu 2026)                                                              | yes  | the `EllSequence`/`addMulSub`/`net`/`rel₄` framework | the helper lemma is part of that paper's Lean infrastructure (the WLOG-nonnegative-indices reduction), not a stated result |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (specific
abs-of-indices form, the named source/general symmetric-quartic, the classical Ward/Stange anchors);
ChatGPT MCP attempted and recorded `n/a` with the failure mode; local refs, nLab, nCatLab, Stacks,
MO/MSE, arXiv each checked/recorded.

### Literature summary (Phase 3)

Concept identified as: an **index-parity normalisation lemma** for the elliptic relation `rel₄` — the
"WLOG the four indices are non-negative" reduction. The paper-level object is Junyan Xu's **"elliptic
relation"** `E(a,b,c,d)` (*On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280, 2026),
a 4-parameter symmetric homogeneous quartic, which the paper states **for `a > b > c > d ≥ 0`** and
which the Lean `rel₄` implements at full `S₄` symmetry over an arbitrary commutative ring; the *lemma
itself* is just "`rel₄` is even in each index when `W` is odd, hence `|·|`-invariant".
Sources agree on a standard form: **no named form exists** — neither the EDS/elliptic-net literature
nor mathlib gives this abs-of-indices congruence an independent name. It is the well-known triviality
"an even function is invariant under `|·|`", lifted from the odd sequence `W` (via the even building
block `addMulSub`) to the quartic `rel₄`. (Note the literature's "absolute value of an EDS" — `|W_n|`,
sign of `W_n`, arXiv:math/0402415 — concerns abs of sequence *values*, a different topic from abs of
*indices* here.)
Most general standard form: for an even/odd sequence, the elliptic relation is unchanged by `|·|` on
its indices — an implicit WLOG step, never an isolated lemma in the sources.
Generality dimensions where the literature varies: only "which relation packaging" (Ward 3-index →
Stange net → Xu's symmetric quartic) and "coefficient domain" (ℤ → field → arbitrary commutative
ring); the abs-invariance is not a varying dimension — it is the same trivial reduction in every form.
Disagreement with the literature: none.

---

### Generality analysis — `EllSequence.rel₄_abs`

Literature-standard form (Phase 3): the elliptic relation is `|·|`-invariant in each index for an odd
`W` (the implicit "WLOG non-negative descending indices" reduction of Xu 2026). Here instantiated at
the specific quartic `rel₄ W (·) (·) (·) (·)`, which is even in each argument because each `addMulSub`
factor is (`addMulSub_abs₀`/`addMulSub_abs₁`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `(neg : ∀ k, W (-k) = -W k)` | `W` is odd | the standard EDS odd property `W(-n) = -W(n)` | **NO** | this is already the literature-standard odd hypothesis; it is genuinely needed (the `m,n` abs strip via `addMulSub_abs₀` requires `neg`; the `r,s` strip via `addMulSub_abs₁` does not, but the lemma abstracts over all four uniformly) |
| 2 | `[CommRing R]` | comm ring | arbitrary comm ring (Xu) | yes (vacuously) | the abs-invariance has nothing to do with `R` being a ring beyond hosting `rel₄`; but `rel₄` lives over `CommRing`, so this is the floor |
| 3 | indices `m n r s : ℤ` | four integers | four indices in ℤ (the rank-1 EDS case) | no | nets generalise to ℤⁿ, but `rel₄` is the rank-1 object by design; not a weakening of *this* lemma |
| 4 | the function `rel₄ W ·` | the specific quartic | **any** function even in each argument | yes | maximal generality is the generic "even-in-each-arg ⟹ abs-invariant" fact, which mathlib already supports inline via `abs_choice` (this is how the two `addMulSub_abs` siblings are proved) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what it is** (the `neg` hypothesis is the
literature-standard odd property; `CommRing` is the floor `rel₄` lives over) — equivalently, **STRICTLY
NARROWER than the generic even-function statement**, but that is the *correct* narrowness: the lemma
exists to `rw`/`simp` the *specific* term `rel₄ W |m| |n| |r| |s|` inside the `relFin4_perm` reduction.
The "more general" form is not a better mathlib lemma; it is the *already existing* generic pattern
(`abs_choice` + evenness), which is exactly how its two ingredient lemmas are proved. So there is **no
generalisation worth shipping**.
Number of weakening opportunities found: **0** *that yield a mathlib-worthy lemma* (every "weakening"
lands on the generic even-abs triviality that mathlib inlines via `abs_choice`, or on a non-mathlib
subject).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | `neg` is the natural odd-sequence hypothesis; no "let X be a foo" preamble |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic identity, no limits |
| 3 | construction → universal property? | no | — | not a construction |
| 4 | set+closure → bundled substructure? | no | — | no substructure |
| 5 | vector-space/field-specific → weaker typeclass? | no | — | already over an arbitrary `CommRing`; `R` is otherwise irrelevant |
| 6 | 1-categorical → higher-categorical? | no | — | elementary commutative algebra |
| 7 | concrete index `ℤ` → general additive structure? | technically yes (`ℤ` → ordered group) | the generic even-abs lemma about an even-in-each-arg function | **but** that target is the folklore `abs_choice` triviality (already inlined in mathlib), not a contribution — see 4b |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the only "modernisation" is to replace this term-specific glue with the
already-existing generic `abs_choice` pattern — i.e. inline it, which is the NO-composable conclusion,
not a YES-but-generalise restatement). One-line reason: there is no organisational improvement to make;
the lemma is a 3-call composition of `rel₄` + the two existing `addMulSub_abs` lemmas over a Lean-local
definition.

---

### Diamond / defeq risk — `EllSequence.rel₄_abs`

**n/a — declaration kind is `lemma`** (no definitional equalities or typeclass-search paths
introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `EllSequence.rel₄_abs`

[A] Lean-Finder       — n/a: tool not exposed in this environment.
[B] Loogle            — n/a: tool not exposed in this environment (lean_loogle unavailable).
[C] LeanSearch        — n/a: tool not exposed in this environment (lean_leansearch unavailable).
[D] Grep mathlib src  `rel₄`, `addMulSub`, `EllSequence`, `relFin4` over `.lake/packages/mathlib/`
                      → **zero relevant hits**. (The 6 grep lines that matched the alternation are all
                      `IsEllSequence` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` —
                      the bare doc/`def`; `rel₄`, `addMulSub`, the `EllSequence` *namespace*, and
                      `relFin4` appear **nowhere** in mathlib rev `d90090f`.) The mathlib EDS file has
                      `IsEllSequence`/`preNormEDS`/`normEDS` but NO `addMulSub`, `net`, `rel₄`,
                      `HaveSameParity₄`, no permutation/abs machinery, and still carries the
                      `normEDS`-is-`IsEllDivSequence` **TODO** this project discharges → this file is
                      an in-development *extension* of that mathlib file. A grep of the upstream file
                      for `rel|abs|net|Perm|Symm` returns empty.
[E] Name pattern      grep `rel₄_abs` across the repo → appears **only** in the 3 forked EDS files
                      (NagellLutz live, NagellLutz `…Original` dead track, HasseWeil aux), identical
                      text. The sole `_abs` name-pattern hit in mathlib's NumberTheory tree is the
                      unrelated `AddSubgroup.relIndex_eq_abs_det` (Discriminant/Different.lean). No
                      mathlib occurrence of this lemma.

Searched for both the user's current form (`rel₄ W |m| |n| |r| |s| = rel₄ W m n r s`) and the
literature-standard idea ("the elliptic relation is `|·|`-invariant in its indices for odd `W`"). The
generic underlying fact ("a function even in each argument is unchanged by `|·|`") is also **not** a
named mathlib lemma; mathlib handles it inline via `abs_choice` (e.g. `Mathlib/RingTheory/Prime.lean`,
`Mathlib/NumberTheory/NumberField/ClassNumber.lean`, `Mathlib/Analysis/Convex/Gauge.lean` all do
`obtain h | h := abs_choice …`), which is precisely how the two `addMulSub_abs` ingredients are proved.

Concluded: **not in mathlib** — and *cannot* be, since its subject `rel₄` (and `addMulSub`) are not in
mathlib. The generic even-abs fact it lifts is also not a mathlib lemma; mathlib inlines it via
`abs_choice`.

---

### Call sites — `EllSequence.rel₄_abs` (Phase 6.0)

Internal use count (this NagellLutz live file, excluding the declaring line 514): **1**
External-to-file callers in the repo: 2 other files, but both are **copies of the same forked API**
(not independent consumers).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:579` | `rw [← rel₄_abs neg]; change relFin4 W t = 0` — inside `rel₄_of_oddRec_evenRec` (the "WLOG non-negative indices" step feeding `relFin4_perm`) |
| `…/EllipticDivisibilitySequenceOriginal.lean:493` (decl) + `:554` (same use) | identical — **dead** duplicate track (slated for deletion per `05-duplications.md`) |
| `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:428` (decl) + `:496` (same use) | identical — third copy of the same fork (sibling vendored copy, not an external consumer) |

Inline-derivation grep (was `rel₄ W |…| |…| |…| |…|` re-derived anywhere without `rel₄_abs`?):
**none** — the only `rel₄ W |…|` occurrence in the repo is the lemma statement itself; the single
consumer goes through `rel₄_abs`. No bypass.

**Call-sites signal:** K = 1 internal use, no external (non-fork) consumer, no inline bypass. Per the
Phase-6.0.1 table, "K = 1 internal use only → possibly inlineable; lean toward NO-composable". It is
not standalone API; it is part of the `rel₄`/`addMulSub` micro-API and serves one reduction step.

---

### Composition check (Phase 6)

Can `EllSequence.rel₄_abs` be derived from mathlib in ≤3 chained calls?

There are two layers here, and **both** point to NO-composable:

**Layer 1 — given the project's own `addMulSub_abs₀`/`addMulSub_abs₁`** (themselves 1-line
`abs_choice` + `addMulSub_neg₀/₁` compositions):
```
Attempt 1:  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]
  - Mathlib decls used: none directly (the `abs_choice` work is inside the two ingredient lemmas)
  - Project decls used: rel₄ (unfold), addMulSub_abs₀, addMulSub_abs₁ (the two siblings)
  - Result: SUCCEEDS — this is literally the existing proof; a single `simp_rw` with 3 rewrite lemmas.
```
This is exactly a ≤3-call composition: unfold `rel₄`, then rewrite each `addMulSub |·| ·` and
`addMulSub · |·|` by the two abs lemmas. No new lemma is warranted — it is the natural one-line lift.

**Layer 2 — the deeper reason:** the *statement* mentions `rel₄` (and through it `addMulSub`), which
**are not in mathlib at all**. A lemma about `rel₄` therefore cannot stand alone in mathlib; it can
only ever exist *bundled with* `rel₄` (i.e. as part of upstreaming the whole `EllSequence` API / arXiv
2604.05280). Within that bundle it is a trivial congruence helper composed from the two
`addMulSub_abs` lemmas — it is **glue**, not an independent target.

Conclusion: **COMPOSABLE** (one `simp_rw` line from `rel₄` + the two sibling `addMulSub_abs` lemmas;
and at the deeper level its subject is non-mathlib).

---

## Verdict: `EllSequence.rel₄_abs`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): no named result; the subject is the elliptic relation of Xu 2026
  (arXiv:2604.05280, stated for non-negative descending indices `a>b>c>d≥0`), and this lemma is the
  *implicit WLOG-nonnegative-indices reduction* made explicit — incidental index-parity bookkeeping
  ("odd `W` ⟹ `rel₄` is `|·|`-invariant in each index"), unnamed in the literature and in mathlib.
  ChatGPT MCP down → compensated with 3 WebSearch queries + grep + the settled sibling reports.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it is (`neg` = standard odd property,
  `CommRing` floor); the only "more general" form is the folklore even-abs triviality mathlib inlines
  via `abs_choice`; no mathlib-worthy generalisation. No modern idiom (4c).
- Mathlib search (Phase 5): **not in mathlib**, and *cannot* be — `rel₄`/`addMulSub`/`EllSequence` are
  absent from mathlib (this file extends mathlib's EDS file, which still carries the `normEDS`-is-EDS
  TODO and has no four-index/abs/permutation layer). The generic even-abs fact is also not a named
  mathlib lemma; it is inlined via `abs_choice`.
- Composition check (Phase 6): **COMPOSABLE** — one `simp_rw` line,
  `simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]` (≤3 rewrite calls).

**Rationale.**
`rel₄_abs` is the four-index member of the `addMulSub_*`/`rel₄_*` normalisation micro-API: it strips
`|·|` off all four indices of the elliptic relation `rel₄`, for an odd sequence `W`. It is not an
independently mathlib-able lemma for two compounding reasons, exactly mirroring its two settled
siblings `addMulSub_abs₀`/`addMulSub_abs₁`. First, its subject `rel₄` (and the building block
`addMulSub`) **do not exist in mathlib** — this file is a forward-port that *extends*
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (which still carries the very `normEDS`-is-an-EDS
TODO this project discharges, and which lacks the `addMulSub`/`net`/`rel₄` machinery from arXiv
2604.05280). A lemma whose statement names a non-mathlib definition can only travel *with* that
definition, as part of the larger `EllSequence` upstreaming bundle — never as a standalone PR. Second,
even granting that bundle, the lemma is a trivial ≤3-call composition: unfold `rel₄`, then rewrite by
the two `addMulSub_abs` lemmas (each of which is itself the `abs_choice`-then-close idiom mathlib uses
inline everywhere). There is no general "function-even-in-each-arg ⟹ `|·|`-invariant" lemma in mathlib
to cite and none is wanted; the pattern is short enough to express in one `simp_rw`.

So within the project this lemma is fine and should stay as local glue (K = 1 honest internal use — the
"WLOG non-negative indices" step in `rel₄_of_oddRec_evenRec` — no inline bypass; keeping it named
beside the `relFin4_perm` reduction reads better than inlining the unfold). It simply is **not** a
mathlib contribution in its own right: if/when the `EllSequence`/`rel₄` API is upstreamed (the
`rel₄.md` report's YES-add-as-is, as a *unit*, coordinated with the paper's author), this lemma and its
`rel₄_swap*`/`rel₄_same*` siblings ride along as part of that file's internal `S₄`-symmetry API; they
are not separate mathlib lemmas, and each is a ≤3-call composition.

**WHY not (refactor-actionable).**
Mathlib has neither the subject (`rel₄`, `addMulSub`) nor the exact form; the only mathlib primitive in
the vicinity is `abs_choice`, buried inside the two ingredient lemmas. The project already has those
two ingredients (`addMulSub_abs₀` line 191, `addMulSub_abs₁` line 195) one screen up, and the exact
form is the one-line `simp_rw` below. No standalone mathlib lemma is needed or possible (the subject is
non-mathlib).

Mathlib building blocks: `abs_choice` (`Mathlib/Algebra/Order/AbsoluteValue/…`, the
`|a| = a ∨ |a| = -a` disjunction) — only reachable *through* the two project siblings, which are the
real ingredients: `EllSequence.addMulSub_abs₀` + `EllSequence.addMulSub_abs₁` (same file).

Composition sketch (≤3 lines — it *is* the current proof):
```lean
example (neg : ∀ k, W (-k) = -W k) (m n r s : ℤ) :
    rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]
```

Call sites in this project (Phase 6.0): K = 1 (line 579, inside `rel₄_of_oddRec_evenRec`).

Refactor plan: **no mathlib action.** Keep `rel₄_abs` as local glue exactly where it is — it is
correctly factored (the single `rw [← rel₄_abs neg]` call site reads cleanly, and inlining the
`simp_rw [rel₄, addMulSub_abs₀ …, addMulSub_abs₁]` into that proof would be strictly worse). The only
"mathlib" consequence is negative: do **not** file a PR for this lemma in isolation. It is
upstream-relevant only as part of the whole `EllSequence` / `rel₄` / `addMulSub` API (arXiv
2604.05280) — and there it is internal `S₄`-symmetry-API glue, not a headline lemma. If that whole API
is ever upstreamed, this lemma travels with `rel₄` and stays a one-line proof; it never becomes an
independent mathlib declaration. The one genuinely actionable cleanup is the AINTLIB cross-fork
**dedup**: the three byte-identical copies (NagellLutz live line 514, NagellLutz `…Original` line 493,
HasseWeil aux line 428) should be collapsed to a single `Common/`-hosted module — a `lane:cleanup`
ticket, not a mathlib PR.

Next action: none toward mathlib. Leave the lemma in place as project-local infrastructure. (The
broader question "should the entire `EllSequence`/`rel₄` extension be upstreamed to
`Mathlib.NumberTheory.EllipticDivisibilitySequence`?" is the separate, BIG decision tracked in the
`rel₄.md` report — run `/mathlibable` on the headline results like `isEllDivSequence_normEDS` /
`rel₄_normEDS` for that, not on `rel₄_abs`.)

---

## Next step

No mathlib action for `rel₄_abs`. It is a ≤3-call composition (`rel₄` unfold + the two sibling
`addMulSub_abs₀`/`addMulSub_abs₁` lemmas) about Lean-local definitions (`rel₄`, `addMulSub`) that are
not in mathlib; it is correct, correctly-factored local glue and should stay in the project. Do not PR
it standalone. The only actionable cleanup is deduplicating the three identical fork copies into a
shared `Common/` module (AINTLIB `lane:cleanup` ticket). Reconsider mathlib inclusion only if the
entire `addMulSub`/`rel₄`/`net` apparatus is upstreamed as a unit (per `rel₄.md`), where this
abs-of-indices helper is a free accompanying corollary.
