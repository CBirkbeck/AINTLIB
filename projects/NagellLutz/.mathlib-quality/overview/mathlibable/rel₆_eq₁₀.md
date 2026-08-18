# /mathlibable report — `EllSequence.rel₆_eq₁₀`

_Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic
divisibility sequences). Source forks `Mathlib.NumberTheory.EllipticDivisibilitySequence`
and the `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` track._

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; decl elaborates in source — proof is `ring`, no `sorry`)
- decl `EllSequence.rel₆_eq₁₀`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:336`
- kind:                      theorem
- has sorry:                 no  (`simp_rw [rel₆, rel₄]; ring`)
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms; this is a fork of the upstream Angdinata `NumberTheory.EllipticDivisibilitySequence` extended with the `addMulSub`/`rel₄`/`rel₆`/`net` elliptic-relation algebra.

**Qualified name VERIFIED.** Declared as `theorem rel₆_eq₁₀` inside `namespace EllSequence`
(opened line 90, the block enclosing line 336 runs to `end EllSequence` at line 597). Full
name: `EllSequence.rel₆_eq₁₀`. Matches the prompt's parsed guess.

---

### Statement (Phase 1)

`EllSequence.rel₆_eq₁₀` is a **theorem**: an unconditional polynomial identity in the
values of an arbitrary sequence `W : ℤ → R` over a commutative ring `R`.

Building blocks (all project-local; none in mathlib):
- `addMulSub W m n := W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` — abbreviate `A(m,n)`. The
  basic "product of two sequence values" block; a 2×2-minor-like quantity.
- `rel₄ W a b c d := A(a,b)·A(c,d) − A(a,c)·A(b,d) + A(a,d)·A(b,c)` — the four-index
  elliptic relation (the three pairings of four indices). This is exactly a **three-term
  Plücker relation** among the `A`-minors.
- `rel₆ W k l a b c d := A(k,l) · rel₄ W a b c d` — a `rel₄` pre-multiplied by a
  coefficient `A(k,l)`. (`abbrev`, so `rel₆` reduces to its body definitionally.)

The statement: for all `c d m n r s : ℤ`,

  rel₆(c,d, m,n,r,s)
    = rel₆(n,d, m,r,s,c) − rel₆(r,d, m,n,s,c) + rel₆(s,d, m,n,r,c)
    + rel₆(n,c, m,r,s,d) − rel₆(r,c, m,n,s,d) + rel₆(s,c, m,n,r,d)
    + rel₆(n,r, m,s,c,d) − rel₆(n,s, m,r,c,d) + rel₆(r,s, m,n,c,d)
    − 2·rel₆(m,d, n,r,s,c).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — arbitrary commutative ring (the value ring).
- `(W : ℤ → R)` — arbitrary sequence; **no hypotheses on `W`** (not assumed odd, not
  assumed elliptic, `W 0` need not be `0`). The identity is a formal `ring` consequence.
- `(c d m n r s : ℤ)` — six free integer indices.

Hypotheses (Lean side): none.

Conclusion (math): a fixed `rel₄` with four "free" indices `(m,n,r,s)`, scaled by the
coefficient `A(c,d)` on two "fixed" indices `(c,d)`, equals a signed combination of ten
`rel₆`s, each of which uses at least one of the two fixed indices `c,d` in its `rel₄` slot
(so each child `rel₄` has at most three genuinely-free indices). Per the docstring: "A
`rel₄` with four free indices can be expressed in terms of ten `rel₄`s with at least one
index chosen from two possibilities (fixed indices)."

Conclusion (Lean): `rel₆ W c d m n r s = … (RHS above) … : R` — an equation in `R`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/auxiliary algebraic identity (single-`have` `ring` lemma) consumed inside
one proof; not a named theorem, not a new structure, not a `## Main statements` entry. It
is one rung of the ladder building toward the main result `isEllDivSequence_normEDS`, not
the result itself.

(Literature width was EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (For the
record, the *proof* is one line, `simp_rw [rel₆, rel₄]; ring`; that is relevant to the
composition discussion in Phase 6, not to the Phase-2b def one-liner gate.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS Ward "elliptic relation" four index identity division polynomial                           | yes  | Ward's 4-index identity `W(m+n)W(m−n)W(r)² + … = 0`  | Wikipedia EDS; Ward 1948. The `rel₄`/`Rel₃` are formalisations of this. No "ten-term recombination" named. |
|  2 | WebSearch (general / nets form)  | Stange elliptic nets net relation recurrence W(m+n)W(m−n) somos identity proof                  | yes  | Stange net relation (4-term, ranks ≥1)               | `net` in the file is exactly Stange's net relation. The recombination identity itself is not named. |
|  3 | WebSearch (named-after / aliases)| division polynomial ψ addition-formula recombination identity coefficient ψ₂ elliptic relation | no   | only the standard ψ recurrences `ψ_{2m+1}=…`, `ψ₂ψ_{2m}=…` | The standard division-polynomial recurrences are the *targets* (`OddRec`/`EvenRec`), not this intermediate. |
|  4 | ChatGPT MCP                      | "Is the ten-term rel₆ recombination named? Plücker/Dodgson connection? bookkeeping or citable?" | n/a  | —                                                    | **MCP unavailable** (Codex backend failed, as task brief warned). Substituted by analyst reasoning + Plücker WebSearch (#9). |
|  5 | Local references                 | (no `.mathlib-quality/references/` PDFs present for NagellLutz)                                 | n/a  | —                                                    | references dir absent → recorded n/a. |
|  6 | nLab                             | elliptic divisibility / Somos / elliptic net recurrence                                        | yes  | Somos/EDS recurrences; no minor-recombination lemma  | nLab has the recurrences, not this auxiliary syzygy. |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | —                                                    | Not a categorical concept (a ring-level polynomial identity). |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | —                                                    | Not in scope: Stacks has no EDS / division-polynomial-identity material at this grain. |
|  9 | MathOverflow / arXiv (Plücker)   | Plücker relation three-term 2×2 minors syzygy `A(a,b)A(c,d) − A(a,c)A(b,d) + A(a,d)A(b,c)`      | yes  | three-term Plücker / Grassmann–Plücker relation      | Confirms the `rel₄` shape *is* a 3-term Plücker relation among 2×2 minors; `rel₆_eq₁₀` is a syzygy among such, specialised to the `addMulSub` minors. Not stated for these minors anywhere. |
| 10 | recent arXiv (last 5 yrs)        | Stange "division polynomials for arbitrary isogenies" (2025); EDS recurrence relation (2021)    | yes  | restate Ward/Stange recurrences                      | Active area; none state this specific recombination as a result. |

### Literature summary (Phase 3)

Concept identified as: an **auxiliary recombination identity** in the algebra of the
four-index elliptic / Stange-net relation — equivalently a **Plücker-type syzygy** among
the `addMulSub` 2×2-minor blocks, specialised to reduce a four-free-index `rel₄` to
combinations involving two fixed indices.

Sources agree on the standard form: **n/a** — there is *no* standard/named form for this
identity. The literature names the *objects* it is built from (Ward's four-index identity;
Stange's net relation; the three-term Plücker relation among minors) and the *targets* it
helps prove (the division-polynomial `OddRec`/`EvenRec` recurrences, and that `normEDS` is
an EDS), but not this intermediate recombination.

Most general standard form: not applicable (unnamed). The closest *conceptual* parent is
the Grassmann–Plücker syzygy, but `rel₆_eq₁₀` is one specific integer-indexed instance
chosen for the `EllSequence` induction, not a general syzygy statement.

Generality dimensions where the literature varies: none relevant — the Lean statement is
already at maximal algebraic generality (arbitrary `CommRing`, arbitrary `W`, no
hypotheses).

Disagreement with the literature: none. The result is a true, fully-general `ring`
identity; it simply isn't a *named* result anyone cites.

**Signal:** that the exhaustive search returns the surrounding theory but no name for this
identity is itself informative — it is formalisation bookkeeping internal to building the
EDS theory, not a stand-alone mathematical theorem.

---

### Generality analysis — `EllSequence.rel₆_eq₁₀`

Literature-standard form (from Phase 3): n/a (unnamed). Target for the generality check is
therefore "maximal algebraic generality", i.e. the weakest typeclass under which the `ring`
identity makes sense.

| # | Parameter / hypothesis | Current Lean form        | Maximal sensible form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | commutative (semi)ring       | borderline          | RHS has genuine subtractions (`−`, `−2·`); a `CommSemiring` restatement would need to move terms across `=`, changing the statement's shape. `CommRing` is the natural home. Not worth weakening. |
| 2 | `(W : ℤ → R)`          | arbitrary, no hypotheses | arbitrary, no hypotheses     | NO                  | already hypothesis-free; nothing to weaken. |
| 3 | `(c d m n r s : ℤ)`    | six free `ℤ` indices     | six free `ℤ` indices         | NO                  | the `tdiv 2` inside `addMulSub` is `ℤ`-specific; indices cannot be generalised off `ℤ` without changing `addMulSub`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what the statement is — an unconditional
`ring` identity over `CommRing R` with an arbitrary `W`). Weakening opportunities found: 0
worth taking (the `CommSemiring` reshaping in row 1 is a different statement, not a
weakening of this one).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                      | no       | —                      | already typeclass-driven (`[CommRing R]`); nothing bundled. |
|  2 | sequences/metric → filters/topology?                                     | no       | —                      | a finite algebraic identity; no limiting/topological content. |
|  3 | construct an object → universal-property class?                          | no       | —                      | proves an equation, constructs nothing. |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | —                      | no substructure here. |
|  5 | vector-space/field-specific → weaken typeclasses?                        | no       | —                      | already at `CommRing` (see 4b row 1). |
|  6 | 1-categorical → higher-categorical?                                      | no       | —                      | not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                         | no       | —                      | indices are intrinsically `ℤ` via `addMulSub`'s `tdiv 2`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite commutative-ring polynomial identity
closed by `ring`; there is no contemporary-mathlib reformulation that reorganises it. (The
*parent* `EllSequence` API has design choices — `addMulSub` via `tdiv` vs `/`, `net` vs
`rel₄` — but those are the parent development's calls, not a restatement of this lemma.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities, no
typeclass-search paths, no coercions). Skipped.

---

### Mathlib search-status: `EllSequence.rel₆_eq₁₀`

Note on tooling: in this environment the Loogle / LeanSearch / Lean-Finder MCP index tools
are **not exposed** (only LSP + a down ChatGPT MCP). Methods [A][B][C] are therefore
recorded `n/a — index MCP not available here`, and substituted by exhaustive **grep over
the pinned mathlib source** ([D]) + name-pattern grep ([E]) — which is decisive for this
case because the entire vocabulary (`rel₄`/`rel₆`/`addMulSub`/`net`/`Rel₃`) is searchable
text and is wholly absent from mathlib.

[A] Lean-Finder       — (no NL→decl index MCP here)                          n/a — substituted by [D]
[B] Loogle            — (no type-pattern index MCP here)                     n/a — substituted by [D]
[C] LeanSearch        — (no NL index MCP here)                               n/a — substituted by [D]
[D] Grep mathlib src  `addMulSub|rel₄|rel₆|net|Rel₃` over `.lake/.../Mathlib/`  **no hits** (0 files)
[E] Name pattern      `_eq₁₀ | rel.*_eq[0-9]` over `.lake/.../Mathlib/`          **no hits** (0 files)

Searched for both:
  - the user's current form (`rel₆_eq₁₀` and its `rel₆`/`rel₄` building blocks) — absent.
  - the literature-standard form — n/a, no named form exists (Phase 3); but the *parent*
    objects were also checked: mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
    has `IsEllSequence`/`normEDS`/`preNormEDS` but **no** `rel₄`/`rel₆`/`addMulSub`/`net`
    layer, and `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
    works with `preΨ`/`Ψ`/`ΨSq` recurrences directly, with no `rel₄`/`rel₆` abstraction.

Cross-project note (AINTLIB-internal, NOT mathlib): the identical theorem `rel₆_eq₁₀` and
the whole `addMulSub`/`rel₄`/`rel₆` machinery is **duplicated** in a sibling AINTLIB
project, `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:272`,
and in this project's own `EllipticDivisibilitySequenceOriginal.lean:322` (a vendored
snapshot). This is an internal-consolidation dedup signal for the AINTLIB monorepo, not a
mathlib-presence signal.

Concluded: **not in mathlib** (grep [D]+[E] exhausted over the pinned mathlib source; the
result and even its entire vocabulary are absent; the literature-standard form does not
exist to search for).

Upstream-relevance finding: the pinned mathlib EDS file's `## Main statements` lists as a
literal **TODO**: "prove that `normEDS` satisfies `IsEllDivSequence`" and "prove that a
normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`." This fork (by
the same author, David Kurniadi Angdinata) *discharges* exactly that TODO, and the
`addMulSub`/`rel₄`/`rel₆` algebra — including `rel₆_eq₁₀` — is the new infrastructure built
to do so. So while `rel₆_eq₁₀` itself is bookkeeping, the *development it belongs to* is
squarely upstream-shaped and fills a stated mathlib gap.

---

### Call sites — `EllSequence.rel₆_eq₁₀`

Internal use count (within NagellLutz, excluding the declaring line): **1 genuine call**.
External-to-file callers: 0 (no project outside this file/its snapshot uses it).

| Caller file:line                                   | Usage pattern (one-line excerpt)                         |
|----------------------------------------------------|----------------------------------------------------------|
| `EllipticDivisibilitySequence.lean:444`            | `rw [mul_comm, ← rel₆_eq, rel₆_eq₁₀]; simp only [rel₆_eq]` — the algebraic step inside `rel₄_of_fix₂` |
| `EllipticDivisibilitySequence.lean:350` (comment)  | `-- the third row in RHS of rel₆_eq₁₀` (documentation reference in `addMulSub_sq_mul_rel₄_eq₉`, not a call) |
| `EllipticDivisibilitySequenceOriginal.lean:423`    | same `rw […, rel₆_eq₁₀]` step in the vendored snapshot (not a distinct consumer) |

Inline-derivation grep (was the identity re-derived elsewhere without `rel₆_eq₁₀`?): **none**
— it is *used*, not bypassed. The sole real consumer is `rel₄_of_fix₂` (line 442–452), the
inductive workhorse that expresses a four-free-index `rel₄` via ten relations with fixed
indices and discharges them with the inductive hypothesis. That feeds
`rel₄_of_min₂` → `rel₄_of_anti_oddRec_evenRec` (the main induction, line 477) →
`IsEllSequence.of_oddRec_evenRec` (591) → ultimately `isEllDivSequence_normEDS` (the
project's headline result and the mathlib TODO).

Call-sites reading: K = 1 internal use, no inline re-derivation, load-bearing (on the
critical path to the main theorem) but with a single consumer. Per the skill's table this
is the "K = 1 internal use only — possibly the wrong abstraction; could be inlined" row: it
leans toward NO-composable / inline, *tempered* by the fact that it is real
on-the-critical-path infrastructure (not dead code) whose ultimate parent is mathlib-worthy.

---

### Composition check (Phase 6)

Can `EllSequence.rel₆_eq₁₀` be derived from mathlib in ≤3 chained calls?

Attempt 1: `by simp_rw [rel₆, rel₄]; ring` — the actual proof.
  - Mathlib decls used: `ring` (and `simp_rw` to unfold the two *project-local* abbrevs
    `rel₆`, `rel₄`).
  - Result: **succeeds** — but note what it means. Once the project-local definitions
    `rel₆`/`rel₄`/`addMulSub` are unfolded, the goal is a pure commutative-ring polynomial
    identity that mathlib's `ring` closes outright. The "composition" is therefore
    `unfold-then-ring`, the canonical signature of an identity that does **not** need to be
    a named lemma in its own right.
  - Crucial caveat: this is **not** a mathlib composition in the skill's sense. The
    statement itself mentions `rel₆`, which is **not a mathlib entity**. There is no
    mathlib call site at which one could inline a `ring` proof of "rel₆ … = …", because
    `rel₆` does not exist in mathlib. The composability here is *internal to the project's
    own vocabulary*, not composability from mathlib primitives.

Conclusion: **COMPOSABLE-WITHIN-PROJECT, NOT-COMPOSABLE-FROM-MATHLIB.**
  - As a `ring` identity it is trivially inline-able *wherever the `rel₆`/`rel₄` defs are in
    scope* — i.e. inside the `EllSequence` development. At its single call site (line 444)
    the `rw [rel₆_eq₁₀]` could be replaced by an inline `simp_rw [rel₆, rel₄]; ring`-style
    rearrangement, but the named lemma is kept for readability (it carries a docstring
    explaining the "ten relations with fixed indices" reduction).
  - It is NOT composable from *mathlib* primitives, because mathlib lacks the vocabulary the
    statement is written in. So neither NO-composable-from-mathlib nor NO-mathlib-has-it can
    fire cleanly: both presuppose mathlib has the relevant objects, and it does not.

---

## Verdict: `EllSequence.rel₆_eq₁₀`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): no named identity; surrounding theory (Ward 4-index, Stange
  net, three-term Plücker among 2×2 minors) is named, this recombination is not → it is
  internal bookkeeping. ChatGPT channel unavailable; covered by analyst + Plücker search.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (arbitrary `CommRing R`, arbitrary `W`,
  hypothesis-free); no `YES-but-generalise-first` move; no modern-idiom restatement (4c =
  no).
- Mathlib search (Phase 5): NOT in mathlib — and the entire `rel₄`/`rel₆`/`addMulSub`/`net`
  vocabulary is absent from mathlib; the upstream mathlib EDS file lists the *downstream*
  goal this machinery serves as an explicit TODO.
- Composition check (Phase 6): COMPOSABLE-WITHIN-PROJECT (`unfold; ring`) but
  NOT-COMPOSABLE-FROM-MATHLIB (the statement names `rel₆`, a non-mathlib entity).

**Rationale.**
`rel₆_eq₁₀` is a true, maximally-general, hypothesis-free commutative-ring identity proved
by `ring`. But on its own it is *formalisation bookkeeping*: a single-`have` recombination
(a Plücker-type syzygy among the `addMulSub` minors) with exactly one consumer
(`rel₄_of_fix₂`), written entirely in project-local vocabulary (`rel₆`/`rel₄`/`addMulSub`)
that **does not exist in mathlib**. That vocabulary-mismatch is why none of the clean
buckets fit as a per-declaration verdict: `NO-mathlib-has-it` and
`NO-composable-from-mathlib` both presuppose mathlib has the relevant objects (it has
neither the result nor the building-block defs), and `YES-add-as-is` cannot apply to a
lone `unfold;ring` auxiliary lemma that mathlib would never accept divorced from the API it
serves.

The honest unit of mathlibability is the **whole `EllSequence` elliptic-relation
development** — the `addMulSub`/`rel₄`/`rel₆`/`net` API plus the theorem chain
`rel₄_of_anti_oddRec_evenRec → IsEllSequence.of_oddRec_evenRec → isEllDivSequence_normEDS`.
That development is genuinely upstream-shaped: it is by the *same author* as mathlib's EDS
file, it lives in the *same namespace shape*, and it discharges a **literal mathlib TODO**
("prove that `normEDS` satisfies `IsEllDivSequence`"). If and when that development is
upstreamed, `rel₆_eq₁₀` should travel **inside** that PR — most likely as a `private`
auxiliary lemma (or inlined into `rel₄_of_fix₂`), not as a headline `Mathlib/...` API
lemma. The decision that the skill cannot make alone is precisely the packaging/policy one:
(a) whether to upstream the parent `EllSequence` elliptic-relation API at all (a
project-roadmap call — and note AINTLIB has duplicate `General*`/`HasseWeil` copies to
consolidate first), and (b) if so, whether this `ring` identity ships as a named `private`
lemma or is inlined. Those are human judgment calls, so the verdict is BORDERLINE.

**Numbered questions (≤5):**
1. Is upstreaming the `EllSequence` elliptic-relation API (`addMulSub`/`rel₄`/`rel₆`/`net`
   + the `normEDS`-is-an-EDS theorem) to mathlib an actual roadmap goal — i.e. should this
   family be PR'd against mathlib's existing `NumberTheory.EllipticDivisibilitySequence`
   (whose `## Main statements` lists exactly this as a TODO)? (yes/no)
2. If yes: should `rel₆_eq₁₀` ship as a **named `private`/auxiliary lemma** inside that PR
   (keeping its docstring + readability at the `rel₄_of_fix₂` call site), or be **inlined**
   into `rel₄_of_fix₂` as a `simp_rw [rel₆, rel₄]; ring` step? (named-private / inline)
3. Before any mathlib PR, the identical machinery is duplicated in `HasseWeil/Auxiliary/`
   and in this project's `…SequenceOriginal.lean`. Should AINTLIB first **consolidate** the
   duplicates into one shared copy (the `Common/` route in the repo conventions) so the
   upstream candidate is single-sourced? (yes/no)
4. Do you want this treated purely **per-declaration** (then the answer is "not a
   standalone mathlib lemma — it's an internal `ring` step": effectively NO), or
   **as part of its development** (then it is in-scope for mathlib *via* the parent API:
   effectively YES-with-the-parent)? (per-decl / with-development)

**Next action:** user answers the questions; re-run `/mathlibable EllSequence.rel₆_eq₁₀`
(or, more usefully, run the assessment on the *parent* results
`EllSequence.rel₄_of_anti_oddRec_evenRec` / `isEllDivSequence_normEDS`, since those are the
real mathlib-candidate units and this lemma's fate follows theirs). If treated
per-declaration in isolation, the working answer is NO — keep it project-local as an
internal `ring` step.

---

## Next step

User answers questions 1–4. The genuinely mathlib-worthy unit is the parent `EllSequence`
elliptic-relation development (same author as mathlib's EDS file; fills a literal mathlib
TODO); `rel₆_eq₁₀` rides inside that as a `private`/inlined `ring` identity. Standalone and
per-declaration, it is not a mathlib lemma.
