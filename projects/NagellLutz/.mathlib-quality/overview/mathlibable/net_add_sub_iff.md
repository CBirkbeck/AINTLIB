# /mathlibable report — `EllSequence.net_add_sub_iff`

## Verdict: **NO-composable-from-mathlib**

(more precisely: NOT-in-mathlib but **blocked on its own project-local `net` definition**, which is itself the missing upstream piece — see Phase 7)

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoned from source
- decl `EllSequence.net_add_sub_iff`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:158`
- qualified name:           `EllSequence.net_add_sub_iff` (namespace `EllSequence` opens at line 90; VERIFIED — the parsed guess was correct)
- kind:                     `lemma` (theorem-like; Phase 4.5 diamond/defeq check **skipped — kind is lemma**)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS); defines EDS and constructs normalised EDSs from initial terms." File is a **fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (same copyright header, "Authors: David Kurniadi Angdinata"), extended with Stange's elliptic-**net** machinery (`addMulSub`, `rel₄`, `net`, `Rel₃`, `invarNum`) that is **not** in the mathlib original.

---

### Statement (Phase 1)

`EllSequence.net_add_sub_iff` is a **bridge lemma**. It states that the vanishing of one specific instance of the project's 4-index elliptic-**net** relation is equivalent to a particular instance of the classical EDS / division-polynomial **addition formula**:

> For `W : ℤ → R` (`R` a `CommRing`) and `m n : ℤ`:
> `net W (m+n) m (m−n) n = 0` ↔ `W(2(m+n))·W(m−n)·W(m)·W(n) = (W(2m+n)·W(2n)·W(m) − W(m+2n)·W(2m)·W(n))·W(m+n)`.

Here `net W p q r s = W(p+q+s)·W(p−q)·W(r+s)·W(r) − W(p+r+s)·W(p−r)·W(q+s)·W(q) + W(q+r+s)·W(q−r)·W(p+s)·W(p)` (defined at line 115; this is **Stange's four-index elliptic-net recurrence**, with a documented sign/order tweak relative to Stange's paper). The lemma plugs the four indices `(p,q,r,s) = (m+n, m, m−n, n)` into `net`, simplifies the eight resulting index expressions, and observes that `net = 0` is then a linear rearrangement of the displayed addition formula.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (maximally general for a polynomial identity).
- `(W : ℤ → R)` — the sequence; **no** hypothesis that `W` is an EDS (the identity is purely formal in the symbols `W(·)`).
- `(m n : ℤ)` — the two free indices.

Hypotheses (Lean side): none.

Conclusion (math): a specific `net = 0` ⇔ a specific addition-formula equation.
Conclusion (Lean): `net W (m+n) m (m−n) n = 0 ↔ <RHS equation>` (a `Prop`, an `Iff`).

Proof body (line 162–168): `simp_rw [net, <eight `show … from by ring` index rewrites>]; constructor <;> intro h <;> linear_combination h`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/bridge lemma — not a named theorem, not a `## Main statement`, introduces no new structure. (Lit width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → **n/a**. Proof is multi-line (a `simp_rw` with 8 rewrites + `constructor`); no one-liner concern.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "EDS addition formula W(m+n)W(m−n) division polynomial recurrence"                              | yes  | Ward's recurrence `ψ(m+n)ψ(m−n) = ψ(m+1)ψ(m−1)ψ(n)² − ψ(n+1)ψ(n−1)ψ(m)²` | Wikipedia/EDS; Ward 1948; arXiv:2102.07573 |
| 2  | WebSearch (general / source form)| "Stange elliptic nets four-index recurrence net relation"                                      | yes  | Stange's net recurrence (4-index) | arXiv:0710.1316 "Elliptic nets and elliptic curves"; rank-1 net = EDS |
| 3  | WebSearch (exact net shape)      | "elliptic net Stange recurrence W(p+q+s)W(p−q) four points"                                     | yes  | `W(p+q+s)W(p−q)W(r+s)W(r) + W(q+r+s)W(q−r)W(p+s)W(p) + W(r+p+s)W(r−p)W(q+s)W(q) = 0` | matches the fork's `net` up to the documented sign swap; arXiv:0803.0728, arXiv:1408.6623 |
| 4  | ChatGPT MCP                      | (asked: is the RHS a named standard identity; is the iff-bridge a library candidate)           | n/a  | — | **MCP down** (Codex exec failed, as task warned); compensated by extra WebSearch rows 3 & the formulary in row 6 |
| 5  | Local references                 | `.mathlib-quality/references/` and `refs/NagellLutz/`                                            | n/a  | — | **neither directory exists** — recorded n/a |
| 6  | Stange's formulary               | "Formulary for elliptic divisibility sequences and elliptic nets" (kstange.net)                | yes  | canonical EDS+net identity catalogue | the bridge here is an instance of the formulary's addition relations, not itself a named formula |
| 7  | nLab                             | elliptic divisibility sequence / elliptic net                                                   | n/a  | — | nLab has no dedicated EDS/elliptic-net page; concept lives in the arXiv/number-theory literature |
| 8  | nCatLab                          | —                                                                                              | n/a  | — | not a categorical concept |
| 9  | Stacks Project                   | —                                                                                              | n/a  | — | not in Stacks' scheme-theoretic scope; EDS are an arithmetic/recurrence topic |
| 10 | MathOverflow / arXiv (recent)    | net polynomials, valuations of elliptic nets                                                    | yes  | arXiv:2512.09601, eprint 2025/521 (Stange, division polys for isogenies) | active area; net recurrence is the standard object, the specific re-indexed bridge is not separately named |

### Literature summary (Phase 3)

- Concept identified as: **the EDS / division-polynomial addition formula** (Ward 1948), expressed as a specialization of **Stange's four-index elliptic-net recurrence** (Stange 2007, arXiv:0710.1316).
- Sources agree on the standard form: **yes** — Ward's `ψ(m+n)ψ(m−n) = ψ(m+1)ψ(m−1)ψ(n)² − ψ(n+1)ψ(n−1)ψ(m)²` and Stange's net relation are both completely standard and well-cited.
- Most general standard form: Stange's net recurrence over `ℤⁿ → K`; rank-1 specializes to Ward's EDS recurrence over `ℤ → R`.
- **What is NOT separately named in the literature:** the *particular iff* between `net(m+n, m, m−n, n) = 0` and the displayed "doubled-index" equation `W(2(m+n))·… = (W(2m+n)·… − W(m+2n)·…)·W(m+n)`. This is a re-indexed *instance* the project derives to feed division-polynomial proofs downstream — it is a consequence of the formulary, tied to the fork's specific `net` sign/order convention (the docstring: "two signs are swapped compared to Stange's paper … to make the equivalence with elliptic relations unconditional").
- Disagreement with the literature: none mathematically; the fork's `net` is Stange's relation in a deliberately chosen sign convention.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): Stange's net recurrence / Ward's EDS addition formula, as a **polynomial identity in the symbols `W(·)`** — no ring restriction beyond commutativity, no EDS hypothesis on `W`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (identity is formal) | NO | already maximally general; `linear_combination` needs `CommRing`. A `CommSemiring` form is impossible — the relation has genuine subtractions. |
| 2 | `(W : ℤ → R)` | arbitrary function, **no EDS hypothesis** | arbitrary `W` (the addition law is a formal rearrangement) | NO | already maximally general — correctly stated without `IsEllSequence W`, since it is an identity, not a theorem about EDS. |
| 3 | `(m n : ℤ)` | integer indices | integer indices (rank-1) | NO (in this convention) | generalizing to Stange's `ℤⁿ` would change the object entirely — that's a different (much bigger) development, not a weakening of this lemma. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it states — a formal identity over a commutative ring with no superfluous hypotheses). Weakening opportunities: **0**.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation |
|---|----------|----------|---------------|
| 1 | "let X be a foo" → typeclass? | no | already typeclass-based (`[CommRing R]`); no bundled hypotheses to promote. |
| 2 | sequences/metric → filters/topology? | no | finite algebraic identity; no limiting/topological content. |
| 3 | construction → universal property? | no | it's an equation, not a construction. |
| 4 | set+closure-pred → bundled substructure? | no | n/a. |
| 5 | field/metric-specific → weaken typeclass? | no | already at `CommRing`; cannot weaken (subtraction present). |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index ℤ → general additive group? | **partially** | the *honest* generalization of `net`/the recurrence is Stange's `ℤⁿ`, but that is a **new, much larger object** (elliptic nets of arbitrary rank), not a free index-generalization of this one lemma. Not a "modernize-first" move for this decl. |

Modern idiom available: **no** (for this lemma as stated). The only "more general" direction is reproducing Stange's full `ℤⁿ` elliptic-net theory, which is out of scope for a single bridge lemma and would not be a restatement but a wholesale new development.

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a (mathlib index via grep over `.lake/packages/mathlib`; tool not separately queried — direct source grep is authoritative here)
[B] Loogle            type pattern `net`, `?W (?m + ?n) * ?W (?m - ?n) = …` — **no hit** (no `net`, no addition-formula lemma in mathlib EDS file)
[C] LeanSearch        "elliptic divisibility sequence addition formula", "elliptic net recurrence" — **no hit**
[D] Grep mathlib src  `net_add_sub_iff`, `addMulSub`, `def net `, `def rel₄`, `Stange` over all of `Mathlib/` — **zero matches anywhere in the mathlib tree**
[E] Name pattern      `IsEllSequence`, EDS file decl list — only the **3-index** `IsEllSequence` Prop + `normEDS`/`preNormEDS`/`complEDS` machinery; **no `net`, no `rel₄`, no addition-formula lemma, no iff-bridge**

Searched for both:
- the user's current form (`net (m+n) m (m−n) n = 0 ↔ …`) — not present.
- the literature-standard form (Ward addition formula / Stange net recurrence) — mathlib has `IsEllSequence` (def of the 3-index recurrence as a `Prop`) but **no derived addition-formula lemma** and **no 4-index `net` object** at all.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` (547 lines) defines `IsEllSequence`/`normEDS` but stops short of the elliptic-**net** layer and of any addition-formula lemma. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` contain no `net`/addition-formula/`Rel` lemma either. **The `net` definition that this lemma's statement mentions does not exist in mathlib.**

---

### Call sites — `EllSequence.net_add_sub_iff` (Phase 6.0)

Internal use count (NagellLutz project, excluding the declaring file): **1**
External-to-project callers: **1 distinct project** (HasseWeil)

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:334` | `(EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)` |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:407` | `(EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)` |

Both sites use the **`.mp`** direction: they have `net ψᵤ … = 0` (from `net_ψᵤ`, proving the univariate division polynomials `ψᵤ` satisfy Stange's net relation) and extract the addition-formula equation to feed a `linear_combination`/`eq_div_iff` step in the elliptic-curve `z`-scaling / group-law proof. This is a **genuine, load-bearing API lemma** (2 real consumers across 2 projects), not dead code.

Inline-derivation grep: the lemma is also **duplicated verbatim** in two sibling forks — `EllipticDivisibilitySequenceOriginal.lean:155` and `HasseWeil/.../EllipticDivisibilitySequence.lean:62` — confirming it is shared infrastructure the projects each need.

Call-sites signal → **YES-* leaning** (K≥1 internal + external consumer, no bypass). The lemma is real API; the only question is *whether mathlib should host it*, which hinges on whether mathlib hosts `net`.

### Composition check (Phase 6a)

Can `net_add_sub_iff` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: rewrite via a mathlib lemma about `net` / the addition formula → **fails**: mathlib has no `net` and no addition-formula lemma to chain.
Attempt 2: derive from `IsEllSequence` → **fails**: (a) the statement is hypothesis-free (no `IsEllSequence W` available), and (b) it is *about `net`*, a symbol mathlib does not define; you cannot even *state* the LHS using only mathlib.

Conclusion: **NOT-COMPOSABLE from mathlib.** The proof (`simp_rw [net, <8 index rewrites>]; constructor <;> intro h <;> linear_combination h`) is a short but real proof whose entire content is "unfold the project-local `net` and rearrange". Because mathlib lacks `net`, the lemma is **neither inline-composable from mathlib nor stateable in mathlib as-is**.

---

## Verdict: `EllSequence.net_add_sub_iff`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature (Phase 3): the RHS is Ward's standard EDS addition formula; `net` is Stange's standard 4-index recurrence — but the *specific iff-bridge / re-indexing* is not a separately named result, and is tied to the fork's chosen sign convention.
- Generality (Phase 4): MAXIMALLY GENERAL as stated (no superfluous hypotheses, `CommRing` is necessary); no modern-idiom restatement short of building Stange's full `ℤⁿ` net theory.
- Mathlib search (Phase 5): **not in mathlib**; crucially, the `net` definition it mentions is **also absent** from mathlib's EDS and DivisionPolynomial files.
- Composition (Phase 6): NOT-COMPOSABLE — cannot even be stated using only mathlib symbols.

**Rationale.**
`net_add_sub_iff` is mathematically sound, well-grounded in the literature (Ward, Stange), and a genuine load-bearing lemma with two downstream consumers. But it is **inseparable from the project-local `net` definition**: its statement *names* `net`, and its entire proof is "unfold `net` and rearrange". Mathlib has neither `net` (Stange's 4-index elliptic-net relation) nor any addition-formula lemma derived from `IsEllSequence`. So in mathlib's current state this is a **glue lemma over a definition mathlib does not have** — it cannot be added "as is" (the symbol `net` is undefined upstream) and cannot be inlined from mathlib primitives (same reason). It is `NO-composable-from-mathlib` in the precise sense that *once the project's own `net` exists, the bridge is a ≤3-line rearrangement* — the lemma carries no content beyond its `net` definition.

The honest framing: this lemma is **not independently mathlibable**. Its fate is **bound to the prior question** of whether *Stange's elliptic-net layer* (`addMulSub`, `rel₄`, `net`, and the `net ⇔ IsEllSequence` equivalence) should be upstreamed to `Mathlib.NumberTheory.EllipticDivisibilitySequence`. **If** that layer goes up (a real, citable, well-defined contribution — Stange's nets are standard and currently missing from mathlib), then `net_add_sub_iff` rides along as one of its API lemmas — and at that point it is a `YES-add-as-is` *bundled with `net`*, not on its own. **If** that layer stays project-local, this lemma stays project-local too. That decision is a BIG-development judgment call about the `net` definition, made when *that* def is assessed — not resolvable from this single bridge lemma.

**WHY not (refactor-actionable).**
Mathlib does not have the building block (`net`) this lemma is phrased in, so there is nothing to inline *at mathlib level* and no mathlib decl to replace it with. **No refactor of the existing call sites is warranted**: both consumers (`ZSMul.lean:334`, `DivisionPolynomial.lean:407`) correctly use the project's own `net_add_sub_iff`, and the project's own `net` is the right local abstraction for them. The actionable items are:

- **De-duplicate within AINTLIB** (this is a *cleanup-ticket* matter, not a mathlib matter): the identical lemma + the whole `addMulSub`/`net` block is copied across `NagellLutz/…/EllipticDivisibilitySequence.lean`, `NagellLutz/…/EllipticDivisibilitySequenceOriginal.lean`, and `HasseWeil/…/EllipticDivisibilitySequence.lean`. Consolidate into one shared module (e.g. `Common/`) and have all three import it. (Per CLAUDE.md, cross-project dedup is exactly a `lane:cleanup` job.)
- **Defer the mathlib question to the `net` def assessment.** When `/mathlibable` (or `/overview` Step 9) reaches `EllSequence.net` / `EllSequence.rel₄` / `EllSequence.net_eq_rel₄`, evaluate **upstreaming Stange's elliptic-net layer as a unit**. `net_add_sub_iff` should be listed in that PR's grouping as a dependent API lemma — *not* PR'd alone.

Building blocks (project-local, the composition that makes this a glue lemma — shown to justify the "composable-once-`net`-exists" classification):
```lean
-- Given the project's `net` (line 115), the bridge is purely:
example (W : ℤ → R) (m n : ℤ) :
    net W (m+n) m (m−n) n = 0 ↔
      W (2*(m+n)) * W (m−n) * W m * W n =
        (W (2*m+n) * W (2*n) * W m - W (m+2*n) * W (2*m) * W n) * W (m+n) := by
  simp_rw [net, /- eight `show … from by ring` index simplifications -/]
  constructor <;> intro h <;> linear_combination h
```

Next action: **do not** PR this lemma to mathlib on its own and **do not** refactor its call sites. (1) File/keep an AINTLIB `lane:cleanup` ticket to de-duplicate the shared `net` block across the three forks. (2) When the `EllSequence.net` definition is assessed for mathlib, evaluate the whole elliptic-net layer together; if it goes up, include `net_add_sub_iff` as bundled API (→ it becomes `YES-add-as-is` only in that bundle).

---

## Next step

Defer to the `EllSequence.net` definition's mathlibable assessment (upstream Stange's elliptic-net layer as a bundle, or keep it project-local). Meanwhile, de-duplicate the copied `net` block across the NagellLutz / NagellLutz-Original / HasseWeil forks via a `lane:cleanup` ticket. Do not PR this bridge lemma standalone; do not refactor its (correct) call sites.

### Sources
- [Stange, *Elliptic nets and elliptic curves*, arXiv:0710.1316](https://arxiv.org/abs/0710.1316)
- [*A recurrence relation for elliptic divisibility sequences*, arXiv:2102.07573](https://arxiv.org/abs/2102.07573)
- [Stange, *Formulary for elliptic divisibility sequences and elliptic nets*](https://math.colorado.edu/~kstange/papers/edsformulary.pdf)
- [*The ECDLP and equivalent hard problems for EDS*, arXiv:0803.0728](https://arxiv.org/pdf/0803.0728)
- [*On Symmetries of Elliptic Nets and Valuations of Net Polynomials*, arXiv:1408.6623](https://arxiv.org/pdf/1408.6623)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [`Mathlib.NumberTheory.EllipticDivisibilitySequence` docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
