# /mathlibable report — `universalNormEDS`

Project: `NagellLutz` (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
Assessed: 2026-06-21. Mode A (single declaration), full 10-phase workflow.
Re-run of the 2026-06-18 assessment, now with (a) the **real local mathlib checkout**
`/Users/mcu22seu/Documents/GitHub/mathlib4` searched directly, and (b) a **literature hit that
explicitly names the object** (arXiv 2604.05280). Both materially strengthen the evidence; the
bucket is unchanged.

> **Project context.** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
> is a **fork/extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`. It carries the
> upstream copyright header (David Kurniadi Angdinata) and re-derives + extends the EDS theory in
> order to **discharge the two TODOs the mathlib file still lists** — "prove that `normEDS` satisfies
> `IsEllDivSequence`" and its converse (both verified still-open in the live mathlib source today,
> Phase 5). `universalNormEDS` is the central scaffolding device of that development.

---

### Baseline (Phase 0)
- lake build:               not re-run (env: local build stale per task brief; reasoned from source).
- decl `universalNormEDS`:   ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1186`.
- kind:                      `noncomputable def`.
- has sorry:                 no.
- qualified name:            **`universalNormEDS`** (top-level — no enclosing namespace). Verified by
                             walking every `namespace`/`end`: the file opens `namespace EllSequence`
                             at :90 but closes it at :597 (`end EllSequence`), reopens/closes it again
                             :1079–:1112; the def at :1186 sits inside `section Map` (:1116) inside
                             `section NormEDS` (:881), all of which are in the **root** namespace
                             (after `end EllSequence` + `open EllSequence`). The prompt's parse is correct.
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised
                             EDSs from initial terms; an extended fork of mathlib's EDS file.

---

### Statement (Phase 1)

`universalNormEDS` is the **universal (a.k.a. generic / standard) normalised elliptic divisibility
sequence**: the normalised EDS whose three defining parameters `b, c, d` are taken to be the three
independent indeterminates of a polynomial ring. Concretely:

```lean
noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)
```

where `Param` is a **project-local** three-element inductive (`inductive Param | B | C | D`, defined
immediately above at :1178; not in mathlib) indexing the three formal variables, and
`X B, X C, X D : MvPolynomial Param ℤ` are the corresponding indeterminates. So the codomain
`MvPolynomial Param ℤ` is exactly `ℤ[B, C, D]`.

Its docstring states the purpose: *"The universal normalised EDS, from which every normalised EDS can
be obtained by composing with a ring homomorphism, which allows us to reduce equalities between
expressions involving terms of a normalised EDS to the universal case. It takes values in a domain,
and all nonzero terms are nonzero and therefore are not zero divisors, a condition required to apply
certain lemmas."*

Variables / typeclasses (Lean side):
- none on the def itself — it is a closed term over the fixed ring `MvPolynomial Param ℤ`.
- `Param : Type` — project-local 3-element indexing inductive (the three EDS parameters).

Hypotheses: none.

Conclusion (math): the generic normalised EDS over `ℤ[B,C,D]`; every concrete `normEDS b c d` over
any `CommRing R` factors through it via `aeval (Param.rec b c d)` — established by the immediately
following `normEDS_eq_aeval` (:1188).

Conclusion (Lean): `ℤ → MvPolynomial Param ℤ` — a definition.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (BIG-adjacent role).
Reason: not a named theorem, not itself a headline result — an infrastructure `def`. But not a
throwaway helper: it is the linchpin of an honest, recognised technique (universal-case
specialisation) and the engine behind several genuine results in the file (`IsEllSequence.normEDS`,
`net_normEDS`, `invar₂_normEDS`, ultimately the `IsEllDivSequence`-for-`normEDS` goal). Recorded SMALL
for framing; literature width run EXHAUSTIVELY regardless.

### One-line check (Phase 2b)

Body line count: **1** substantive line (`normEDS (X B) (X C) (X D)`).
One-liner verdict: **ONE-LINER**.

| Exemption                        | Applies? | Evidence |
|----------------------------------|----------|----------|
| Avoid defeq abuse               | **yes**  | Downstream proofs rewrite *through* `universalNormEDS` as a sealed anchor. The file has **9** occurrences over **6** declarations; `net_normEDS` (:1466–1468) does `rw [normEDS_eq_aeval, … ← map_net, universalNormEDS, IsEllSequence.normEDS.net, map_zero]` and `invar₂_normEDS` (:1495–1498) does `rw [← universalNormEDS] at this` and `show (aeval … ∘ universalNormEDS) = normEDS b c d`. The **name is the rewrite target**; eager unfolding would break the `map_net`/`aeval`-specialisation chain. |
| Avoid typeclass diamonds        | no       | No instances keyed on it; codomain `MvPolynomial Param ℤ` carries only standard mathlib instances. |
| Mark semantic intent / API name | **yes**  | The name + docstring **is** the API: `universalNormEDS_ne_zero` (:1250) and `universalNormEDS_mem_nonZeroDivisors` (:1257) are stated *about* it and consumed at :1345 by a `mul_cancel` step. It marks "the generic EDS over a domain", precisely the `X`-is-a-non-zero-divisor property the rest of the file relies on. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (defeq-anchor + semantic-API). The one-liner-toward-NO bias
is therefore **not** dispositive; the def earns its name.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | `"elliptic divisibility sequence" universal generic indeterminate parameters polynomial ring specialization ring homomorphism normEDS` | **yes** | **"Every EDS is a specialization of the universal (standard) EDS `h^U = EDS(X₂,X₃,X₄)` over `ℤ[X₂,X₃,X₄]`"** | **Direct, named hit.** Source: arXiv **2604.05280** *On Elliptic Sequences over Commutative Rings*. |
|  2 | WebSearch (general form / naming)| `"universal" "elliptic divisibility sequence" EDS(X_2,X_3,X_4) specialization "standard" elliptic sequence over commutative rings` | **yes** | confirms #1 verbatim: *"Since `h₂^U = X₂ ≠ 0` is not a zero-divisor in the domain `ℤ[X₂,X₃,X₄]`, `h^U` is elliptic, so its specialization `h` is also elliptic."* | The **exact non-zero-divisor reduction argument** that `universalNormEDS_ne_zero`/`_mem_nonZeroDivisors` encode. |
|  3 | WebSearch (named-after / technique)| (subsumed by #1/#2) "reduction to the universal case" + "even-odd recurrence requiring h₁,h₂ not zero-divisors" | **yes** | the universal-case-then-specialise **technique** is standard practice in this literature | Confirms the technique is mathematics, not a Lean invention. |
|  4 | ChatGPT MCP                      | (intended: standard form + generality + historical evolution of the universal/generic EDS)             | n/a  | — | **ChatGPT MCP down in this env** (Codex `exec` failed; matches task brief). Compensated by the strong web hits + direct mathlib-source verification. |
|  5 | Local references                 | `find … -path "*mathlib-quality/references*"`; no NagellLutz `references/`, no `refs/` store           | n/a  | — | No project source-paper PDFs present. Recorded n/a. |
|  6 | nLab                             | EDS / division polynomial as a categorical/universal object                                            | n/a  | — | nLab has no EDS / division-polynomial entry; not a category-theoretic concept. |
|  7 | nCatLab                          | —                                                                                                      | n/a  | — | Not a categorical concept (same as #6). |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | — | EDS / division polynomials of curves are out of Stacks' scheme-theoretic-foundations scope. |
|  9 | MathOverflow / Math.SE           | (universal/generic EDS specialisation)                                                                 | n/a  | — | Subsumed by the arXiv hits in #1–#2; no extra standard-form info needed. |
| 10 | recent arXiv (last 5 years)      | surfaced directly: arXiv **2604.05280** *On Elliptic Sequences over Commutative Rings*                 | **yes** | EDS over **general commutative rings**, with the universal `ℤ[X₂,X₃,X₄]` object as a tool — matches the Lean `[CommRing R]` framing exactly | **Almost certainly the source paper for this AINTLIB development**: same even-odd recurrence, same universal object, same notation. |
| 11 | Wikipedia (corroboration)        | EDS article — Ward's curve↔EDS correspondence, normalised-parameter setup                              | part | confirms Ward (1948) foundations; treats the universal object implicitly | Background only; the precise named object is in #1/#2/#10. |

Protocol pass check: WebSearch ran **3 distinct queries at different generality levels** (specific
form, naming/general form, technique) — ✓; ChatGPT MCP **down, recorded n/a with reason and
compensated**; local refs checked (n/a, absent); nLab checked (n/a, reason); Stacks/nCatLab/MO each
n/a-with-reason; arXiv produced the on-point source paper. **Protocol satisfied — and this time with a
positive, named literature hit, not just an implicit one.**

### Literature summary (Phase 3)

Concept identified as: **the universal / generic / "standard" (normalised) elliptic divisibility
sequence** — the EDS whose parameters are the indeterminates of a polynomial ring, written
`h^U = EDS(X₂,X₃,X₄)` over `ℤ[X₂,X₃,X₄]` in arXiv 2604.05280. The associated technique is
*"reduction to the universal case: prove the identity for `h^U` over the domain `ℤ[X₂,X₃,X₄]`, then
specialise to any concrete EDS via the evaluation ring homomorphism."*

Sources agree on the standard form: **yes, and explicitly**. arXiv 2604.05280 names the object, fixes
the coefficient ring as `ℤ[X₂,X₃,X₄]` (= the Lean `MvPolynomial Param ℤ`), and gives the very
non-zero-divisor argument the Lean lemmas encode. (The 2026-06-18 run wrote "no source names a
`ℤ[b,c,d]` universal object explicitly" — **that is now refuted**; the match is essentially
line-for-line.)

Most general standard form: the generic EDS over the **initial** ring `ℤ[X₂,X₃,X₄]`, specialising to
any concrete EDS over any commutative ring by a ring homomorphism.

Generality dimensions where the literature varies:
  - coefficient ring: the division-polynomial presentation uses `ℤ[a₁..a₆][X,Y]` (Weierstrass
    coefficients; this is also what **mathlib's own** `DivisionPolynomial/Basic.lean` uses — see
    Phase 5); the EDS-sequence presentation uses `ℤ[X₂,X₃,X₄]` (normalised parameters), which is what
    this file uses. The `ℤ[X₂,X₃,X₄]` form is the **initial/most-general base** for the abstract
    `normEDS` sequence (every normalised EDS over any `CommRing` is a specialisation; `ℤ` is initial),
    so the Lean choice is the universal one.
  - "EDS over a field" (Ward, classical) vs. "EDS over a commutative ring" (modern; arXiv 2604.05280).
    The Lean development is already in the commutative-ring idiom.

Disagreement with the literature: **none**. The Lean form is a faithful, in-fact-initial realisation
of the standard "universal EDS" object as named in arXiv 2604.05280.

---

### Generality analysis — `universalNormEDS`

Literature-standard form (from Phase 3): the generic EDS over the universal (initial) coefficient
ring `ℤ[X₂,X₃,X₄]`, from which all concrete EDS specialise by ring homomorphism.

| # | Parameter / hypothesis | Current Lean form                         | Literature-standard form                       | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------------------------------|-------------------------------------------------|---------------------|----------------------------------|
| 1 | coefficient ring       | `MvPolynomial Param ℤ` (i.e. `ℤ[B,C,D]`)  | `ℤ[X₂,X₃,X₄]` (initial) — arXiv 2604.05280      | **NO**              | `ℤ[B,C,D]` is the **initial** commutative ring with three chosen elements; it is *already* the universal object. Nothing is more general — every normalised EDS is a specialisation of this one. Weakening loses universality. The literature uses precisely this ring. |
| 2 | index type `Param`     | project-local 3-element inductive `{B,C,D}`| three formal parameters `X₂,X₃,X₄`              | n/a (cosmetic)      | `Fin 3` would also work; a named 3-constructor inductive is a clean, mathlib-idiomatic choice. Not a generality axis — a naming/style call (see Phase 7 Q3). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** — it is the initial/universal object by construction;
the literature uses the identical coefficient ring. Nothing to weaken.
Number of weakening opportunities found: **0**.
Proposed restatement: none needed. Cost: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                    | no       | — | def has no bundled hypotheses to typeclass-ify. |
|  2 | sequences/metric → filters/topology?                                              | no       | — | purely algebraic; no analysis. |
|  3 | construct an object where a universal-property *class* would characterise it?     | **partly** | One could phrase "universal normalised EDS" as a universal-property class (initial object in a category of "rings-with-a-normalised-EDS"). | But this is over-engineering: the def already **is** the universal object concretely, and `normEDS_eq_aeval` (:1188) is exactly its universal property as a *usable lemma*. A class adds machinery with **no downstream consumer** in sight — and mathlib's own analogous universal device (`DivisionPolynomial/Basic.lean`) is *also* a concrete construction + a `map`/specialisation lemma, not a class. Recorded "no real improvement". |
|  4 | set-with-closure-predicate → bundled substructure?                                | no       | — | not a substructure. |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                           | no       | — | already over `ℤ` (initial ring); maximally weak base. |
|  6 | 1-categorical → higher-categorical?                                               | no       | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive monoid?                                | no       | — | the `ℤ` index is intrinsic to EDS (sequences indexed by ℤ); not a generalisation axis. |
|  8 | concrete-via-abstract (does the proof betray a more general statement)?           | no       | — | this is a `def` with no proof body to invert; the abstraction *is* the def. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The universal-property-class reformulation (row 3) is abstraction for
its own sake — no downstream mathlib consumer, and `normEDS_eq_aeval` already delivers the universal
property in directly-usable form. The honesty bar (verdicts doc §"What this is NOT a license for") is
not met. One-line reason: the concrete `def` + its `aeval`-specialisation lemma **is** the idiomatic
mathlib realisation of "universal object" here, and it mirrors exactly how mathlib already does the
universal Weierstrass ring for division polynomials.

---

### Diamond / defeq risk — `universalNormEDS` (def → Phase 4.5 runs)

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | Not an instance; no typeclass keyed on the def. Codomain `MvPolynomial Param ℤ` uses standard instances only. |
| 2 | Reducibility leak            | low     | `noncomputable def` (not `@[reducible]`). Intentionally *semi-reducible / sealed*: downstream proofs unfold it only via explicit `rw [universalNormEDS]` / `rw [← universalNormEDS]`. That is the desired behaviour (Phase 2b defeq-anchor), not a leak. |
| 3 | Non-canonical unfolding      | none    | No `@[simp]`; `simp` won't unfold it spontaneously. Unfolding is always explicit in the file. |
| 4 | Instance priority collision  | n/a     | Not an instance. |
| 5 | Universe-polymorphism issues | none    | Monomorphic (`ℤ → MvPolynomial Param ℤ`); no universe variables. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort` attached. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE / LOW** (the only non-`none` row is the *intended* sealing of a defeq anchor).
Top risks: none. Mitigations: n/a.

---

### Mathlib search-status: `universalNormEDS`

This run searched the **real local mathlib checkout** at
`/Users/mcu22seu/Documents/GitHub/mathlib4/Mathlib/` (a substantial upgrade over the 2026-06-18 run,
which only had a stale `.lake` copy / doc page).

[A] Lean-Finder       — `n/a`: AI index tool not surfaced in this environment.
[B] Loogle            — `n/a`: `lean_loogle` not available as a tool here (not in the deferred-tool list).
[C] LeanSearch        — `n/a`: `lean_leansearch` not available here.
[D] Grep mathlib src  — **authoritative, conclusive negative.**
   - `grep -rln "universalNormEDS\|universalEDS\|genericEDS\|UniversalNormEDS"` over the whole
     `mathlib4/Mathlib/` tree → **zero files**.
   - `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`: **no** `MvPolynomial`, **no** `aeval`,
     **no** `inductive Param`, **no** universal device. Its only non-`Init`/`Tactic` import is
     `Mathlib.Algebra.Group.Int.Even`. `def normEDS` (:289) is identical to the fork's. **Both TODOs
     are still open**, verbatim: *"TODO: prove that `normEDS` satisfies `IsEllDivSequence`"* and
     *"TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`."*
   - `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`: these **do** use
     the universal-ring technique, but for *division polynomials of curves* over
     `𝓡[X,Y] := ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]` (Basic.lean:36–38, "the associated universal morphism
     `𝓡[X,Y] → R[X,Y]` mapping `Aᵢ` to `aᵢ`"). **No `universalNormEDS`, no `Param`, no universal
     reduction for the abstract `normEDS` *sequence*.** So mathlib has the *technique* but not *this
     object*.
[E] Name pattern      — `n/a`: `lean_local_search` not available; the grep in [D] covers name search
                        (searched `universalNormEDS`, `universal`, `generic`, `Param`, `aeval` over the tree).

Searched for **both** the user's form and the literature-standard form (generic/universal EDS over
`ℤ[X₂,X₃,X₄]`): mathlib has **neither**. The absence is **structural, not incidental** — mathlib's EDS
file explicitly lists, as open TODOs, the very results this universal device is built to prove.

Concluded: **not in mathlib** (grep-exhausted under both forms against the live mathlib source; A/B/C/E
recorded n/a-with-reason because the mathlib-index tooling is unavailable in this environment, with the
full-source grep [D] standing in and returning a clean, conclusive negative).

---

### Call sites — `universalNormEDS`

Internal use count (within NagellLutz, **outside the declaring file**): **0**.
External-to-file callers: **0** distinct files.

*The relevant signal is intra-file:* within the declaring file there are **9** references over **6**
declarations — the def is the engine of the universal-specialisation proofs. The "0 external" number
is **not** a dead-code signal; it reflects that this is an internal device of one self-contained
development.

| Caller (declaring file) line | Usage pattern (one-line excerpt) |
|------------------------------|----------------------------------|
| `EllipticDivisibilitySequence.lean:1186` | the `def` itself |
| `:1188–1189` | `normEDS_eq_aeval : normEDS b c d = (aeval (Param.rec b c d) ∘ universalNormEDS)` — its **universal property** (`simp_rw [universalNormEDS, map_normEDS, aeval_X]`) |
| `:1250, :1253` | `universalNormEDS_ne_zero` — every nonzero index gives a nonzero polynomial |
| `:1257–1259` | `universalNormEDS_mem_nonZeroDivisors` — hence a non-zero-divisor (the key enabling property) |
| `:1345` | `… (universalNormEDS_mem_nonZeroDivisors hm) n` — feeds a `mul_cancel` step |
| `:1466–1468` | `net_normEDS`: `rw [normEDS_eq_aeval, … ← map_net, universalNormEDS, IsEllSequence.normEDS.net, map_zero]` |
| `:1495–1498` | `invar₂_normEDS`: `rw [← universalNormEDS] at this`; `show (aeval … ∘ universalNormEDS) = normEDS b c d` |

Inline-derivation grep (re-derived elsewhere without using `universalNormEDS`?):
  - **(duplicated, not re-derived):** identical copies exist in
    `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:639` (with the analogous
    `universalNormEDS_ne_zero`/`_mem_nonZeroDivisors` at :725/:734) and in a NagellLutz `…Original`
    sibling. These are **separate forks of the same Angdinata code**, not independent re-derivations
    bypassing the device — an *intra-AINTLIB dedup* matter (multiple copies across projects),
    orthogonal to the mathlib question.

Call-sites reading: K=0 external + heavy intra-file use (9 refs / 6 decls) + sibling-fork duplication
⇒ a **genuine internal API of one self-contained development**. The right home is "wherever that
development lands" — and that development is a candidate for upstreaming the missing mathlib EDS theory.

---

### Composition check (Phase 6)

Can `universalNormEDS` be derived from mathlib in ≤3 chained calls?

Attempt 1: `normEDS (MvPolynomial.X B) (MvPolynomial.X C) (MvPolynomial.X D)`
  - Mathlib decls used: `normEDS` (mathlib), `MvPolynomial.X` (mathlib) — over the project-local index
    type `Param`.
  - Result: **succeeds as a term** — the *body* is literally a 1-call composition of two mathlib
    primitives.
  - Notes: BUT this "composition" **is the definition itself**, not a proof discharged at a call site.
    The value of `universalNormEDS` is **not** the term — it is (a) the *sealed name* that the 9
    intra-file rewrites target (`rw [universalNormEDS]` / `rw [← universalNormEDS]`), and (b) the
    docstring-level semantic contract "this is the universal EDS, valued in a domain, so its nonzero
    terms are non-zero-divisors", which `universalNormEDS_mem_nonZeroDivisors` then exploits. Inlining
    `normEDS (X B) (X C) (X D)` everywhere would (i) destroy the `← universalNormEDS` rewrite targets
    and (ii) scatter the `Param`/`X` boilerplate through every proof. Per the Phase-2b defeq-anchor +
    semantic-API exemptions, this is the legitimate "one-liner that should be a named def" case — the
    Phase-6 composition heuristics table classifies "named anchor whose unfolding is deliberately
    controlled" as **not** a throwaway composition.

Conclusion: **NOT-COMPOSABLE** *in the sense that matters*. The term is a 1-call composition, but the
declaration is a deliberate sealed anchor + semantic-API marker (Phase 2b exemptions apply), so
"inline it everywhere" is the wrong move. It is not a wrapper consumers bypass; it is the device they
route through.

---

## Verdict: `universalNormEDS`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the **universal / "standard" EDS** `h^U = EDS(X₂,X₃,X₄)` over
  `ℤ[X₂,X₃,X₄]` is an **explicitly named** object in arXiv 2604.05280, with the **identical**
  coefficient ring and the **identical** non-zero-divisor reduction argument this Lean code encodes.
  The "specialise the generic via a ring hom" technique is standard. This def is its faithful, initial
  realisation.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — it is the universal/initial object; nothing
  to weaken (the literature uses the same ring). Modern-idiom: no real improvement (a universal-property
  class would be redundant machinery with no consumer; mathlib's own division-polynomial universal ring
  is also a concrete construction).
- Mathlib search (Phase 5): **not in mathlib** under either form — verified by full grep of the live
  `mathlib4` source tree. Mathlib's EDS file still lists the results this device proves as **open
  TODOs**; mathlib has the universal-ring *technique* (for division polynomials) but not *this object*.
- Composition check (Phase 6): **NOT-COMPOSABLE** in the load-bearing sense (sealed defeq anchor +
  semantic-API; Phase 2b exemptions apply) — though the body is a 1-call term.
- Diamond/defeq risk (Phase 4.5): **NONE/LOW**.

**Rationale.**
On the pure technical merits this clears the YES bar: a sorry-free, maximally-general, risk-free,
well-named definition that mathlib lacks, realising a **literature-named** mathematical object (the
universal EDS, arXiv 2604.05280) and powering real theorems (`IsEllSequence.normEDS`, `net_normEDS`,
`invar₂_normEDS`) that mathlib **explicitly** leaves as TODOs. The one-liner-without-exemption trap
does **not** apply (Phase 2b: defeq-anchor + semantic-API exemptions both hold), and the "just inline
the composition" trap does **not** apply either (inlining would destroy the rewrite anchors). This run
actually *strengthens* the YES case versus 2026-06-18 — the literature now positively names the object
rather than treating it implicitly.

What blocks a clean `YES-add-as-is` is a **scope/packaging judgment only the maintainer can make**, not
a technical deficiency, and (per the verdicts doc) **not cost**. `universalNormEDS` has essentially
zero value *in isolation*: its entire worth is as the proof-engine of the surrounding
universal-specialisation block (`normEDS_eq_aeval`, the two `nonZeroDivisors` lemmas, `net_normEDS`,
`IsEllSequence.normEDS`, the `invar` relations, culminating in `IsEllDivSequence (normEDS …)`). It
should go to mathlib **only as part of upstreaming that whole block** — a substantial PR closing
mathlib's stated TODOs, against the *upstream author's own* file (D. K. Angdinata), needing the
project-local helper `Param` shipped with it. The block is in fact already being routed to mathlib
**piecemeal across buckets** by the sibling assessments in this very overview (`net_eq_rel₄` →
YES-add-as-is; `net_normEDS` → YES-but-generalise-first; `normEDS_eq_aeval`,
`universalNormEDS_ne_zero`, `universalNormEDS_mem_nonZeroDivisors` → NO-composable), which confirms the
"ships as part of a coordinated block, not alone" framing. There is also the intra-AINTLIB wrinkle that
multiple identical copies exist (NagellLutz, NagellLutz-Original, HasseWeil), which should be
de-duplicated **before** any upstreaming. Whether to upstream the block now, how to grain the PR, how to
coordinate with the upstream author, and `Param`-vs-`Fin 3` are all taste/policy/sequencing calls —
exactly what BORDERLINE is for.

**Numbered questions (for the human):**
  1. Do you intend to upstream the **whole** universal-specialisation EDS block (`universalNormEDS`
     + `normEDS_eq_aeval` + the two `nonZeroDivisors` lemmas + `net_normEDS` + `IsEllSequence.normEDS`
     + the `invar` relations, culminating in `IsEllDivSequence (normEDS …)`) to
     `Mathlib.NumberTheory.EllipticDivisibilitySequence` — i.e. close mathlib's two stated TODOs? If
     **yes**, `universalNormEDS` ships **with** that block as the engine, target
     `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (it would become `YES-add-as-is` *as part
     of the block*).
  2. If **no** (this stays an AINTLIB-internal device): then it is correctly project-local, no mathlib
     action — and the only follow-up is **intra-AINTLIB dedup**: collapse the identical copies
     (NagellLutz / NagellLutz-Original / HasseWeil) into one shared `Common/` module. Should that dedup
     ticket be filed?
  3. Index type: ship `Param` as-is (named 3-constructor inductive — mirrors arXiv's `X₂,X₃,X₄`), or
     would mathlib prefer `Fin 3` (mechanical change, no math impact)? (Naming/style call.)
  4. Coordination: since the file carries the upstream author's (D. K. Angdinata) copyright header and
     extends *his* mathlib file, and arXiv 2604.05280 looks like the source paper, should the
     upstreaming be raised with him directly rather than opened cold? (Process call.)

**Next action.** Answer Q1 (the pivot). If Q1 = **yes** → re-run `/mathlibable` treating the whole
block as one PR unit; this def becomes `YES-add-as-is` shipped with the block, then `/cleanup`, then a
coordinated PR to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. If Q1 = **no** → no mathlib
action for this def; file the dedup ticket from Q2 instead.

---

## Next step

Answer Q1: do you intend to upstream the universal-specialisation EDS block (closing mathlib's
`IsEllDivSequence`-for-`normEDS` TODOs, coordinated with the upstream author)? **Yes** →
`universalNormEDS` is `YES-add-as-is` as part of that block (re-run `/mathlibable` on the block, then
`/cleanup`, then the coordinated PR). **No** → keep it project-local and file the intra-AINTLIB dedup
ticket for the multiple copies.
