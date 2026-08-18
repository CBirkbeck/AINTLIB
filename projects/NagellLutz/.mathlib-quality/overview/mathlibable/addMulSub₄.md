# /mathlibable report — `EllSequence.HaveSameParity₄.addMulSub₄`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — `addMulSub₄ W a b c d := W ((a+b).tdiv 2) * W ((c−d).tdiv 2)`
is a one-line, project-internal proof abbreviation: a *hybrid* two-factor product splicing one
factor from `addMulSub W a b` and one from `addMulSub W c d`. It has no named-concept status in the
EDS / elliptic-net literature (Ward, Stange), no consumers outside its own declaring file, and no
Phase-2b exemption. It is literally `W (Int.tdiv (a+b) 2) * W (Int.tdiv (c−d) 2)` — a ≤2-call mathlib
composition — and its sole companion fact `addMulSub₄_mul_addMulSub₄` is a one-line `ring` identity.
Inline it, or keep it as a file-local helper that travels with the (un-upstreamed)
`addMulSub`/`rel₄`/`net` elliptic-net extension if that is ever PR'd.

This mirrors the already-recorded verdict for its sibling helper `avg₄` (`NO-composable-from-mathlib`)
and `StrictAnti₄` (`NO-composable-from-mathlib`); contrast the *central* relation `rel₄`
(`YES-add-as-is`). `addMulSub₄` is a building-block helper, not the central object.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `EllSequence.HaveSameParity₄.addMulSub₄`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:261`
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines `IsEllSequence`,
  `preNormEDS`, `normEDS`, `complEDS`, and (in the AINTLIB fork only) the `addMulSub`/`rel₄`/`net`
  four-index "elliptic net" machinery and its index-transformation argument. `addMulSub₄` lives in
  that fork-only extension, inside `namespace EllSequence` → `namespace HaveSameParity₄`.

**Qualified name verified.** `namespace EllSequence` opens at line 90; `namespace HaveSameParity₄`
opens at line 216 and closes (`end HaveSameParity₄`) at line 297; the `def` is at line 261 (under a
`variable (W) in`, so `W` is an explicit argument). Hence the true qualified name is
**`EllSequence.HaveSameParity₄.addMulSub₄`** — matching the task's parsed name.

---

### Statement (Phase 1)

`EllSequence.HaveSameParity₄.addMulSub₄` is **a definition**: a two-factor "hybrid" product of two
`W`-values at halved index-sums.

> Given `W : ℤ → R` (`R` a commutative ring) and `a, b, c, d : ℤ`,
> `addMulSub₄ W a b c d := W (Int.tdiv (a+b) 2) · W (Int.tdiv (c−d) 2)`.

Docstring: *"A hybrid product formed by one factor from an `addMulSub` and one from another
`addMulSub`."*

Variables / typeclasses involved (Lean side):
- `R : Type u`, `[CommRing R]` — the codomain ring (from the file-level `variable`).
- `W : ℤ → R` — the elliptic sequence (made explicit here via `variable (W) in`).
- `a b c d : ℤ` — four integer **indices** of an elliptic-net relation.

Hypotheses (Lean side): none on the definition itself. (The enclosing `HaveSameParity₄` section
carries a `same : HaveSameParity₄ a b c d` hypothesis, but the `def addMulSub₄` is marked with no
`include` and does not use it — it is parity-agnostic. The `omit same in` on the *next* lemma
confirms `same` is not a parameter of `addMulSub₄`.)

Conclusion (math): the ring element `W(⌊(a+b)/2⌋_trunc) · W(⌊(c−d)/2⌋_trunc)`, using truncated
(`Int.tdiv`) division by 2. Compare the basic block `addMulSub W m n = W((m+n).tdiv 2)·W((m−n).tdiv 2)`:
`addMulSub₄ W a b c d` is exactly **(first factor of `addMulSub W a b`) · (second factor of
`addMulSub W c d`)** — one factor spliced from each of two `addMulSub`s, mixing the two pairs.

Conclusion (Lean): n/a — definition. Type is `R`.

**Mathematical role.** Pure proof-engineering. The point of the hybrid is the factorization identity
`addMulSub₄ W a b c d · addMulSub₄ W c d a b = addMulSub W a b · addMulSub W c d`
(`addMulSub₄_mul_addMulSub₄`, line 264) — the cross-multiplication of two hybrids recovers the product
of the two original `addMulSub` blocks. This lets the index-translation step `addMulSub_transf`
(lines 270–278) rewrite each of the six translated `addMulSub` terms as a hybrid, and then
`rel₄_transf` (line 280) reassembles them — proving the four-index relation is invariant under the
centering translation `x ↦ avg₄ − x`. `addMulSub₄` exists only to make that 6-way bookkeeping line up.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line product `def`; not a named structure, not a `## Main` result, not a person/place
theorem. It is an intermediate notational device inside one proof argument (the `transf` invariance).

(Literature width was still run at full EXHAUSTIVE breadth below.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`W ((a + b).tdiv 2) * W ((c - d).tdiv 2)`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence                                                                                          |
|-----------------------------------|----------|---------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                 | **no**   | The def is actively *unfolded*, not sealed: every consumer uses `simp_rw [… addMulSub₄ …]` (lines 266, 277, 284) to expand it down to `addMulSub`/`W`. No `@[reducible]`/`@[irreducible]` discipline; the proofs rely on unfolding, so it is not a defeq barrier. |
| Avoid typeclass diamonds          | **no**   | The body is a bare ring-valued product `W _ * W _`. No instance is declared, no typeclass-search path is anchored; nothing can collide. |
| Mark semantic intent / API name   | **no**   | The only "consumers" are three lemmas in the *same file* (`addMulSub₄_mul_addMulSub₄`, `addMulSub_transf`, `rel₄_transf`). The name buys local readability of the 6-way `transf` identity, not a stable downstream API surface. No decl outside the declaring file (the sibling forks merely re-declare their own copy) depends on the name. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION**.
→ Carried into Phase 7: verdict biased toward `NO-composable-from-mathlib` / `NO-mathlib-has-it`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (surrounding concept)  | `elliptic divisibility sequence four-index relation Ward Stange division polynomial recurrence proof addMulSub` | yes (relation), no (this primitive) | Ward's 4-index recurrence `h_{m+n}h_{m−n}h_r² = h_{m+r}h_{m−r}h_n² − h_{n+r}h_{n−r}h_m²` (Ward 1948) | The *relation* is standard; **no source names the hybrid `W((a+b)/2)·W((c−d)/2)` factor**. Sources: Wikipedia "Elliptic divisibility sequence"; arXiv:2102.07573 "A recurrence relation for EDS"; Stange eprint 2025/521. |
|  2 | WebSearch (most-general / generic)| `"elliptic net" symmetric product W((m+n)/2) W((m-n)/2) factor pairing index translation centering proof` | yes (net recurrence), no (this primitive) | Stange's elliptic-net recurrence `W(p+q+s)W(p−q)W(r+s)W(r) + … = 0` (matches the file's `net`) | Confirms the surrounding `net` relation is standard (Stange arXiv:0710.1316); explicitly notes the search "don't contain explicit treatment of this particular symmetric product / factor-pairing identity". |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2 across Ward + Stange names) `Stange elliptic nets symmetric function four indices proof transformation` | partial | Net "transformation / symmetry" results exist (arXiv:1408.6623 "On Symmetries of Elliptic Nets") | The index-transformation *step* exists in the literature, but the hybrid half-sum factor is an unnamed implementation detail of *that* step, never a reusable named primitive. |
|  4 | ChatGPT MCP                      | "Is the hybrid product `W((a+b)/2)·W((c−d)/2)` a named/standard concept in EDS/elliptic-net/division-polynomial literature, or a proof-bookkeeping device? Most general setting `W : ℤ → CommRing` or more?" | **n/a** | —                                                      | **MCP genuinely unavailable** (Codex backend errored on invocation, exactly as the task warned). Compensated by the extra WebSearch generality levels (#1–#3) + direct mathlib-source grep + the algebraic composition reasoning in Phase 6. |
|  5 | Local references                 | `ls / grep projects/NagellLutz/.mathlib-quality/references/`                                            | n/a  | directory absent                                       | No project references dir for NagellLutz — recorded n/a per protocol. |
|  6 | nLab                             | "hybrid product / half-sum factor of elliptic sequence" relevance                                      | n/a  | —                                                      | Not a categorical concept; an elementary two-factor ring product. No nLab entry. Recorded n/a with reason. |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                                      | Not categorical. n/a. |
|  8 | Stacks Project                   | elliptic net / division-polynomial factor                                                              | n/a  | —                                                      | EDS / elliptic nets are out of scope of the Stacks Project (scheme-theoretic alg. geom.); this is a bare `ℤ → R` helper. n/a with reason. |
|  9 | MathOverflow / Math.SE           | (covered by the WebSearch #1–#2 sweeps over EDS/elliptic-net identities)                                | no   | —                                                      | No MO/MSE thread names this hybrid half-sum factor as a primitive. |
| 10 | recent arXiv (last 5 yr)         | surfaced: arXiv:2102.07573 (2021 recurrence), 1408.6623, 2109.07050 (Elliptic Net Algorithm Revisited), 2512.09601 | partial | Elliptic-net recurrence / algorithm / valuation results | Modern literature still treats any such factor splitting as an unnamed computational step inside net-recurrence manipulations, never a named reusable quantity. |

The protocol passed: WebSearch ran 3 distinct queries at three generality levels (surrounding
concept / most-general net form / named-after Ward+Stange); local refs, nLab, Stacks, nCatLab,
MO/arXiv each checked or recorded n/a with a reason. ChatGPT MCP genuinely unavailable and compensated.

### Literature summary (Phase 3)

Concept identified as: **a hybrid two-factor product** `W((a+b)/2) · W((c−d)/2)` formed by taking one
factor from each of two `addMulSub` blocks. This is **not** a named mathematical concept. The
*ambient* objects are standard and well-documented:
- Ward's four-index EDS recurrence (1948) — the file's `Rel₃`/`rel₄`;
- Stange's elliptic-net recurrence — the file's `net`;
- the existence of index-transformation/symmetry arguments for nets (Stange).

But the **hybrid half-sum factor itself is an implementation device** of this particular Lean proof
of translation-invariance, with no independent name or status in the literature.
Sources agree on the standard form: **n/a — there is no standard form to agree on for this primitive.**
Most general standard form: **none exists**; it is an inline ring product of two `W`-values.
Generality dimensions where the literature varies: n/a (no concept to generalize). The only relevant
generality remark: the natural setting for the surrounding `addMulSub`/`rel₄`/`net` machinery is
exactly `W : ℤ → R` with `R` a commutative ring — which is precisely what the file uses.
Disagreement with the literature: none — the literature has no opinion on this helper, which itself
signals it is too elementary/proof-specific to be a named library entity.

---

### Generality analysis — `EllSequence.HaveSameParity₄.addMulSub₄`

Literature-standard form (from Phase 3): **none** (not a named concept). The surrounding machinery is
already at its natural generality (`W : ℤ → CommRing`).

| # | Parameter / hypothesis | Current Lean form     | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|------------------------|---------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring       | commutative ring (Ward/Stange work over comm. rings / fields) | NO (not usefully) | The companion identity `addMulSub₄_mul_addMulSub₄` and the whole `rel₄` theory use commutativity essentially (`ring`). `CommRing` is already the standard, maximal sensible setting; the def's *body* (`W _ * W _`) would typecheck over a non-commutative `Ring`/`Mul`, but it would be useless in isolation (every consumer needs `CommRing`). No generality is gained by weakening the def alone. |
| 2 | `W : ℤ → R`            | integer-indexed sequence | integer-indexed (EDS are ℤ-indexed; nets are ℤⁿ-indexed but this slice is ℤ) | NO | EDS indices are intrinsically `ℤ`; the `(a+b).tdiv 2` halving is meaningful only for the same-parity integer indices of an EDS. |
| 3 | `a b c d : ℤ`          | four integer indices   | — (no literature concept)  | n/a                 | The four indices of a `rel₄` term; `ℤ` is the intrinsic and only relevant domain. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (vacuously for the helper — there is no more-general
literature target; the ambient `W : ℤ → CommRing` is already the standard maximal setting).
Number of weakening opportunities found: **0** (the `Mul`-only relaxation of `CommRing` is not a
*useful* weakening — the def is unusable without the `CommRing` consumers around it).
Proposed restatement: none.
Cost of restatement: n/a.

Note: "maximally general" here is *not* a point in favour of inclusion — the form is maximal only
because the concept is too trivial to admit a meaningful generalization. The decisive issue is
one-liner-ness + no external consumers + composability, addressed below.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                             | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                       | no       | —                      | No structure here; bare function value. |
|  2 | sequences/metric → filters/topology?                                                                  | no       | —                      | Finite algebraic identity; no limits/topology. |
|  3 | construction → universal-property class?                                                              | no       | —                      | A ring element, not an object with a UP. |
|  4 | set-with-closure-predicate → bundled substructure?                                                    | no       | —                      | No substructure. |
|  5 | vector-space/field-specific → weaken typeclass?                                                       | no       | —                      | Already at `CommRing`; further weakening (`Mul`) is useless (see Phase 4a row 1). |
|  6 | 1-categorical → higher-categorical?                                                                   | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                             | no       | —                      | The `(a+b).tdiv 2` halving is intrinsically about same-parity `ℤ` indices of an EDS; a general additive group has no `tdiv … 2`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: This is an elementary two-factor ring product used as a local proof device inside the
translation-invariance argument; there is no contemporary mathlib formulation that improves its
organisation, and there is no more-general natural setting than the `W : ℤ → CommRing` already in use.

---

### Diamond / defeq risk — `EllSequence.HaveSameParity₄.addMulSub₄` (Phase 4.5, kind = `def`)

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond             | none    | No instance; produces a plain `R`. Nothing enters typeclass search.                   |
| 2 | Reducibility leak             | low     | Not marked `@[reducible]`; semireducible. Body is two `W`-applications and one `*`; the project *deliberately* unfolds it via `simp_rw [addMulSub₄]`, so even eager unfolding is harmless and intended. |
| 3 | Non-canonical unfolding       | none    | `simp_rw [addMulSub₄]` exposes `W ((a+b).tdiv 2) * W ((c−d).tdiv 2)` exactly as written; no surprise. |
| 4 | Instance priority collision   | n/a     | Not an `instance`.                                                                    |
| 5 | Universe-polymorphism issues  | none    | `R : Type u`; the def is a value in `R`, no universe annotation forced beyond the ambient `W`. |
| 6 | Coercion ambiguity            | none    | No `CoeFun`/`CoeSort`; it is a bare ring element.                                     |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**. Top risks: none. (Risk is not the reason for the NO verdict; triviality +
composability is.)

---

### Mathlib search-status: `EllSequence.HaveSameParity₄.addMulSub₄`

[A] Lean-Finder       (mathlib-index tool unavailable in this env)        n/a — tool not loadable here
[B] Loogle            `(ℤ → R) → ℤ → ℤ → ℤ → ℤ → R` hybrid-product pattern  n/a — tool not loadable; covered by source grep below
[C] LeanSearch        "hybrid product of elliptic sequence half-sum factors" n/a — tool not loadable; covered by source grep below
[D] Grep mathlib src  `addMulSub`, `addMulSub₄`, `rel₄`, `net`, `HaveSameParity` over the whole `Mathlib/` tree | **no hits** — `addMulSub`/`addMulSub₄`/`rel₄`/`net`/`HaveSameParity₄` appear **nowhere** in mathlib; mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) stops at `preNormEDS`/`normEDS`/`complEDS`/`normEDSRec` and never introduces this `addMulSub`-based four-index machinery |
[E] Name pattern      grep `EllSequence` namespace in `Mathlib/`            **no hits** — there is no `namespace EllSequence` anywhere in mathlib; the entire host namespace is fork-only

Searched for both:
  - the user's current form (`W ((a+b).tdiv 2) * W ((c−d).tdiv 2)`, the hybrid product) → not in mathlib.
  - the literature-standard form → none exists to search for (Phase 3); and the *ambient* `rel₄`/`net`
    machinery that would host it is itself **not** in mathlib (its EDS file is `normEDS`-only).

Concluded: **not in mathlib** (all methods exhausted across the whole tree; the surrounding four-index
elliptic-net extension that would host it is itself un-upstreamed — mathlib's EDS file stops at the
`normEDS`/`complEDS` construction and has no `addMulSub`/`rel₄`/`net` API at all). There is also no
mathlib primitive for "hybrid product of two half-sum factors"; it is simply `W _ * W _` over `Int.tdiv`.

---

### Call sites — `EllSequence.HaveSameParity₄.addMulSub₄`

Internal use count (within the declaring file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, excluding the `def` at line 261):
**3 logical sites** (the `addMulSub₄` token appears on lines 265, 266, 271–276, 277, 284), all inside
the same `HaveSameParity₄` translation-invariance proof cluster.
External-to-file callers (a *different* project importing NagellLutz, or even a different file in
NagellLutz): **0**.

| Caller file:line                                                               | Usage pattern (one-line excerpt)                                                       |
|--------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------|
| …/EllipticDivisibilitySequence.lean:264–266 (`addMulSub₄_mul_addMulSub₄`)      | `addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d` (proof: `simp_rw [addMulSub₄, addMulSub]; ring`) |
| …/EllipticDivisibilitySequence.lean:270–278 (`addMulSub_transf`)               | `addMulSub W (avg₄ … - d) (avg₄ … - c) = addMulSub₄ W a b c d ∧ …` (6-way; proof `simp_rw […addMulSub₄…]; ring_nf`) |
| …/EllipticDivisibilitySequence.lean:280–284 (`rel₄_transf`)                    | `simp_rw [rel₄, h₁, …, h₆, addMulSub₄_mul_addMulSub₄]; ring`                            |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `addMulSub₄`?):
  - The hits in `…/LutzNagell/EllipticDivisibilitySequenceOriginal.lean` and
    `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` are **byte-identical sibling
    forks** of the same upstream source (each re-declares its *own* `addMulSub₄`). They are **not**
    consumers — so there are *three copies* of this def in the repo and **zero cross-file uses**.

**Signal:** matches the table row *"K = 0 external uses; purely internal to its own file; same def
copy-pasted in sibling forks rather than imported"* → strong `NO` signal (a local proof helper, not
shared API). The internal uses keep it from being dead code, but they are all in the one
translation-invariance proof it was written for.

---

### Composition check (Phase 6)

Can `EllSequence.HaveSameParity₄.addMulSub₄` be derived from mathlib in ≤3 chained calls?
**It *is* a 2-call mathlib expression.**

Attempt 1: `addMulSub₄ W a b c d` **is literally** `W (Int.tdiv (a + b) 2) * W (Int.tdiv (c − d) 2)`,
i.e. two applications of the given `W : ℤ → R`, two `Int.tdiv` calls (mathlib/core `Int.tdiv`), and one
`HMul.hMul` from `R`'s `CommRing`. No new definition is needed; the RHS *is* the composition.
  - Mathlib decls used: `Int.tdiv`, `HMul.hMul` (on `R`).
  - Result: **succeeds** — zero wrapper logic; the body is the composition verbatim.

Its one companion fact composes trivially too:
  `addMulSub₄_mul_addMulSub₄ : addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b *
  addMulSub W c d` is proved by `simp_rw [addMulSub₄, addMulSub]; ring` — i.e. after unfolding both to
  `W _ * W _` products it is a pure **`ring`** identity (the four `W`-factors commute into the same
  product on both sides). That is a borderline-trivial `ring` composition, not a substantive lemma.

Conclusion: **COMPOSABLE.** Wherever `addMulSub₄ W a b c d` appears, write
`W ((a + b).tdiv 2) * W ((c − d).tdiv 2)`; the `addMulSub₄_mul_addMulSub₄` rewrite is just `ring`
after unfolding `addMulSub`.

---

## Verdict: `EllSequence.HaveSameParity₄.addMulSub₄`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the four-index EDS recurrence (Ward) and the elliptic-net recurrence
  (Stange, = the file's `net`) are standard and well-documented, but **no source names the hybrid
  factor** `W((a+b)/2)·W((c−d)/2)`; it is an unnamed implementation device of the index-translation step.
- Generality analysis (Phase 4): MAXIMALLY GENERAL only vacuously; the ambient setting `W : ℤ →
  CommRing` is already standard/maximal; no modern idiom applies.
- Mathlib search (Phase 5): **not in mathlib** (name + pattern exhausted; the entire host
  `addMulSub`/`rel₄`/`net`/`EllSequence` extension is itself un-upstreamed — mathlib's EDS file is
  `normEDS`-only).
- Composition check (Phase 6): **COMPOSABLE** — the def body *is* `W (Int.tdiv (a+b) 2) * W (Int.tdiv
  (c−d) 2)`; its sole lemma is a `ring` identity after unfolding.

**Rationale.**
`addMulSub₄` is a one-line definitional abbreviation — a hybrid product `W((a+b).tdiv 2) ·
W((c−d).tdiv 2) : R` splicing one factor from `addMulSub W a b` and one from `addMulSub W c d` — with
no Phase-2b exemption: it is not a defeq barrier (every consumer unfolds it with `simp_rw
[addMulSub₄]`), it anchors no typeclass instance, and its name is local proof-readability of the 6-way
`addMulSub_transf` identity, not a stable downstream API. The literature treats this factor splitting
as an unnamed computational step inside net-recurrence manipulations, so there is no mathematical
*content* to upstream — only a name for a two-factor ring product mathlib already expresses directly.
The single fact anyone needs about it, the cross-multiplication identity `addMulSub₄ W a b c d ·
addMulSub₄ W c d a b = addMulSub W a b · addMulSub W c d`, is a one-line `ring` fact after unfolding.
With zero external consumers (the only other copies are byte-identical sibling forks, not importers),
there is no API-stability argument for a named mathlib definition either. This is the same verdict the
project already recorded for its sibling helpers `avg₄` and `StrictAnti₄`.

**WHY not (refactor-actionable).**
Mathlib already provides every building block: the sequence `W` is supplied by the caller, `Int.tdiv`
gives the truncated halving, and `R`'s `CommRing` multiplication gives the product — and the proofs
*already unfold to exactly these*. The named `def` adds a layer with no payoff at mathlib's bar, and
its companion lemma is `ring`. There is no mathlib hole to fill: the host `rel₄`/`net` four-index
machinery is what (if anything) might one day be upstreamed, and `addMulSub₄` should ride inside *that*
PR as a `private`/file-local helper, not as an independent public definition.

  Mathlib building blocks:
    - `W : ℤ → R`                 (the caller's sequence — not a mathlib decl, but supplied at every call site)
    - `Int.tdiv : ℤ → ℤ → ℤ`      (truncated integer division — core/`Mathlib`; chosen so `(−m).tdiv 2 = −(m.tdiv 2)`)
    - `HMul.hMul`                 (multiplication from `R`'s `CommRing` instance)
    - `ring`                      (discharges `addMulSub₄_mul_addMulSub₄` after `simp_rw [addMulSub₄, addMulSub]`)
  Composition sketch (≤3 lines):
  ```lean
  -- the definition, inlined:
  example (W : ℤ → R) (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)
  -- its only lemma, by ring after unfolding addMulSub:
  example (W : ℤ → R) (a b c d : ℤ) :
      (W ((a + b).tdiv 2) * W ((c - d).tdiv 2)) * (W ((c + d).tdiv 2) * W ((a - b).tdiv 2))
        = addMulSub W a b * addMulSub W c d := by
    simp_rw [addMulSub]; ring
  ```
  Call sites in our project (from Phase 6.0): **0 external**, 3 internal (all in the declaring file).
  Refactor plan: this decl should **not** be sent to mathlib as a standalone. Options, in order of
  preference:
    1. **Leave it as project-internal code** (a `private`/file-local helper) — it is fine where it is;
       it just does not belong *in mathlib* as a public definition. If/when the
       `addMulSub`/`rel₄`/`net` elliptic-net extension is upstreamed, `addMulSub₄` rides along as a
       `private`/file-local helper inside that PR, not as an independently named public API.
    2. **If trimming the fork for an upstream PR:** at each of the 3 internal sites, inline
       `W ((a + b).tdiv 2) * W ((c − d).tdiv 2)` for `addMulSub₄ W a b c d`, and discharge the
       `addMulSub₄_mul_addMulSub₄` rewrite with `simp_rw [addMulSub]; ring` directly (the proofs already
       call `ring` after `simp_rw`, so the inlining is mechanical — mind the *argument permutation* in
       the cross term `addMulSub₄ W c d a b`, whose inlined form is `W ((c+d).tdiv 2) * W ((a−b).tdiv 2)`).
  Next action: do **not** open a standalone mathlib PR for `addMulSub₄`. Keep it local, or inline the
  composition at its 3 in-file call sites when slimming the elliptic-net extension for upstreaming.

---

## Next step

Do not upstream `EllSequence.HaveSameParity₄.addMulSub₄` on its own. It is a one-line hybrid ring
product `W ((a+b).tdiv 2) * W ((c−d).tdiv 2)` with no external consumers and no named-concept status in
the EDS / elliptic-net literature; its sole lemma is a `ring` identity. Keep it as a
project-internal/file-local helper (it travels inside the larger `addMulSub`/`rel₄`/`net` extension if
that is ever upstreamed), or inline the composition at its 3 in-file call sites.
