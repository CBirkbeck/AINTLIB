# `/mathlibable` report — `PadicMeasure.padicZeta_witness_neg`

Mode A (single declaration), full 10-phase workflow with the exhaustive
9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **not re-run; reasoned from source** (per task BUILD NOTE — `lake build` is stale/slow here; the declaration and its dependency closure were read directly from source)
- decl `PadicMeasure.padicZeta_witness_neg`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:93`
- kind:                      theorem
- has sorry:                 no (proof is complete; sorry-free)
- module docstring summary:  "ζ_p as a pseudo-measure on 𝒢⁺ and the ideal I(𝒢)ζ_p" — RJW (arXiv:2309.15692) §11.1 corollary + §11.2, on the identified Galois side (`𝒢⁺ = GPlus p`).

Dependency closure read from source:
- `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (`Measure/Basic.lean:52`) — the Iwasawa algebra Λ(X) as the space of ℤ_p-valued p-adic measures.
- `dirac p x` (`Measure/Basic.lean:64`) — the Dirac measure `φ ↦ φ x`; written `[x]` in the prose.
- `QuotientField p := FractionRing (PadicMeasure p ℤ_[p]ˣ)` (`Measure/PseudoMeasure.lean:804`) — the total ring of fractions Q(𝒢) = Q(ℤ_p^×).
- `padicZeta p hp2 : QuotientField p` (`KubotaLeopoldt/ZetaP.lean:252`) — the p-adic zeta function as a pseudo-measure.
- `units_dirac_mul_dirac` (`Measure/PseudoMeasure.lean:200`) — `[u]·[v] = [u·v]` for `u v : ℤ_[p]ˣ`.
- `dirac_neg_one_sub_one_mul_padicZeta` (`ZetaGalois.lean:69`) — **the c-invariance input** `([−1]−[1])·ζ_p = 0` in Q(𝒢). Load-bearing for this proof.
- `IsFractionRing.injective` (mathlib, `RingTheory/Localization/FractionRing.lean:137`) — the only mathlib decl in the proof.

---

### Statement (Phase 1)

`PadicMeasure.padicZeta_witness_neg` is a theorem stating the following:

Let `p` be an odd prime and `g ∈ ℤ_p^×`. The p-adic zeta function `ζ_p` is a
pseudo-measure in the total fraction ring `Q(𝒢)` of the Iwasawa algebra
`Λ(𝒢) = Λ(ℤ_p^×)`. For each unit `b`, the augmentation-twisted product
`([b]−[1])·ζ_p` lands back in `Λ(𝒢)` (the pseudo-measure property), so it
has a *witness*: a genuine measure `ν` with `algebraMap(([b]−[1]))·ζ_p =
algebraMap ν`. The theorem says the witness for `g` and the witness for `−g`
**coincide**: if `ν` witnesses `([g]−[1])·ζ_p` and `ν'` witnesses
`([−g]−[1])·ζ_p`, then `ν = ν'`.

The mathematical engine is the c-invariance of `ζ_p`
(`([−1]−[1])·ζ_p = 0`, i.e. `ζ_p` is fixed by complex conjugation): one
computes `([−g]−[1]) − ([g]−[1]) = [g]·([−1]−[1])`, multiplies by `ζ_p` to
get `0`, hence the two witness images in `Q(𝒢)` are equal, and injectivity
of `Λ(𝒢) → Q(𝒢)` (a fraction ring of a domain-like ring with the measure
ring as base) forces `ν = ν'`. Per the docstring, this is "the
well-definedness of pushing witnesses to `𝒢⁺`", where `𝒢⁺ = ℤ_p^× / ⟨−1⟩`
(`GPlus`).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the prime.
- `(hp2 : p ≠ 2)` — odd prime (needed so `−1` generates the relevant order-2 piece and the plus/minus splitting is clean).
- `(g : ℤ_[p]ˣ)` — a p-adic unit (group element of 𝒢).

Hypotheses (Lean side):
- `{ν ν' : PadicMeasure p ℤ_[p]ˣ}` — two measures (implicit).
- `hν : algebraMap _ (QuotientField p) ([g]−1)·ζ_p = algebraMap _ _ ν` — `ν` witnesses the g-twist.
- `hν' : algebraMap _ (QuotientField p) ([−g]−1)·ζ_p = algebraMap _ _ ν'` — `ν'` witnesses the (−g)-twist.

Conclusion (math): the two pseudo-measure witnesses at `g` and `−g` are the same measure.

Conclusion (Lean): `ν = ν'`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**

Reason: it is a helper/glue lemma — a well-definedness step ("witness symmetry")
in the construction that descends `ζ_p` to a pseudo-measure on `𝒢⁺`. It is not a
named theorem, not a new structure, and not listed as a primary `## Main
declarations` bullet of the file (the bullets name `padicZetaPlus`,
`isPlusPseudoMeasure_padicZetaPlus`, `zetaIdeal`/`zetaIdealPlus`; this lemma is
infrastructure underneath them).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for
framing only.)

### One-line check (Phase 2b)

Body line count: ~18 substantive lines (a real proof: `hfac`/`hkey`/`hsub`
chain culminating in `IsFractionRing.injective`).

One-liner verdict: n/a — kind is theorem, not def. Section skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic zeta function pseudo-measure complex conjugation invariance descent to plus part Iwasawa"      | partial | the *framework* (pseudo-measures, plus/minus decomposition under ι, descent to plus-part) is standard; the *witness-symmetry* lemma is not separately named | top hit is **arXiv:2309.15692** — the exact source paper (RJW). |
|  2 | WebSearch (general form)         | "Iwasawa main conjecture totally real field pseudomeasure G^+ quotient well-defined witness"           | partial | pseudomeasure def confirmed (`(g−1)φ ∈ Λ(G)` for all g); plus-part descent is a standard move (Mazur–Wiles, Wiles, Kakde, Burns) | no source isolates "witness symmetry under g ↦ −g" as a stated lemma. |
|  3 | WebSearch (named-after / aliases)| "Coates Wiles pseudomeasure Stickelberger c-invariant odd part vanishes p-adic L-function units group ring" | partial | c-invariance / odd-part-vanishing of the zeta pseudo-measure is classical (Coates; Serre's reading of Deligne–Ribet) | the vanishing `([−1]−[1])·ζ_p = 0` is the standard fact; the witness-equality *corollary* is folklore book-keeping, not a citable named result. |
|  4 | WebSearch (cancellation idiom)   | `"pseudomeasure" Iwasawa algebra fraction field two witnesses equal cancellation non-zero-divisor`     | partial | confirms pseudomeasure = element `λ` of `Frac(Λ(G))` with `(1−h)λ ∈ Λ(G)`; Λ = ℤ_p[[T]], L = Quot Λ | found arXiv:0711.0581, arXiv:1004.2578 — none state the witness-uniqueness lemma. |
|  5 | ChatGPT MCP                      | (attempted) "standard form + generality + historical evolution of the witness-symmetry/c-invariance descent lemma" | **n/a** | — | MCP server `chatgpt-math` is *configured* in settings but **not connected/available** in this session (ToolSearch returns no `ask_chatgpt` tool). Compensated by running **four** WebSearch queries at different generality levels (rows 1–4) instead of the required three. |
|  6 | nLab                             | "Iwasawa algebra" / pseudomeasure                                                                      | yes  | nLab *Iwasawa algebra* page: Λ(G) = lim ℤ_p[G/H]; pseudomeasures (Coates) are elements of `Frac(Λ(G))` defined by Mellin transform | nLab has the *framework* but no entry for this witness-symmetry lemma. |
|  7 | nCatLab (categorical)            | (same as nLab; concept is not 2-categorical)                                                           | n/a  | —                                | not a categorical concept — no universal-property reformulation; recorded n/a with reason. |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept (no schemes/sheaves/cohomology); Iwasawa-algebra pseudo-measures are outside Stacks scope. |
|  9 | MathOverflow / Math.StackExchange| folded into WebSearch rows 1–4 (results surfaced MO/MSE threads on pseudomeasures + plus/minus parts)   | partial | reaffirms the framework; no thread isolates "witness symmetry g ↦ −g". | |
| 10 | recent arXiv (last 5 years)      | rows 1–4 surfaced arXiv:2309.15692 (2023, the source), 2503.23320, 2407.09002, 0711.0581               | yes  | source paper RJW arXiv:2309.15692 §11.1 is the home of this exact construction | the lemma is an internal step of that paper's §11.1 corollary, not an independently-stated theorem. |
| 11 | Local references                 | `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                    | n/a  | (both directories absent)        | no references dir present — recorded n/a with reason. |

Protocol pass check:
- WebSearch ran **4** distinct queries at different generality levels (specific form, general framework, named-after/aliases, cancellation idiom) — exceeds the ≥3 bar.
- ChatGPT MCP: **not available** this session (configured but not connected). Recorded n/a with reason; over-covered WebSearch to compensate.
- Local references: checked — absent, n/a with reason.
- nLab: checked (Iwasawa-algebra framework present; this lemma absent).
- Stacks / nCatLab / MathOverflow / arXiv: each checked or n/a with reason.

### Literature summary (Phase 3)

Concept identified as: **the well-definedness ("witness symmetry") step in the
descent of the Kubota–Leopoldt p-adic zeta pseudo-measure from `𝒢 = ℤ_p^×` to
the plus-part quotient `𝒢⁺ = ℤ_p^× / ⟨−1⟩`**, powered by the c-invariance of
`ζ_p` (`([−1]−[1])·ζ_p = 0`). The ambient framework (pseudo-measures of Coates;
plus/minus decomposition under complex conjugation; descent to the plus part) is
entirely standard and classical.

Sources agree on the standard form: **yes** for the *framework*; the witness-
symmetry lemma itself is **not separately named** in any source — it is internal
book-keeping inside the construction (here, RJW arXiv:2309.15692 §11.1 corollary,
TeX 3033–3039, the named source).

Most general standard form: there is no "more general standard form" of *this
lemma* in the literature, because the literature does not state the lemma in
isolation — it states the c-invariance (`([−1]−[1])·ζ_p = 0`) and then *uses* it
to define the plus-part pseudo-measure directly. The witness-equality fact is an
inlined consequence.

Generality dimensions where the literature varies:
  - the group: ℤ_p^× here; the general theory works for any compact p-adic Lie group G with the plus/minus decomposition under an order-2 automorphism (complex conjugation). But that is the generality of the *whole pseudo-measure apparatus*, which mathlib does not have at all — not a weakening axis for this single lemma.
  - the L-function: ζ_p here; analogous statements hold for Dirichlet/Hecke p-adic L-functions, again only meaningful once the apparatus exists.

Disagreement with the literature: **none**. The Lean statement faithfully encodes
a true, standard consequence of c-invariance.

---

### Generality analysis — `PadicMeasure.padicZeta_witness_neg`

Literature-standard form (from Phase 3): there is no isolated literature form; the
fact is the c-invariance `([−1]−[1])·ζ_p = 0` together with injectivity of
`Λ(𝒢) → Q(𝒢)`. The Lean lemma is one faithful packaging of "witnesses at `g`
and `−g` agree".

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|------------------------------------|
| 1 | `(p : ℕ) [Fact p.Prime]`, `(hp2 : p ≠ 2)` | odd prime                  | odd prime (the whole §11 hypothesis) | NO                  | the plus/minus splitting and `⟨−1⟩` order-2 structure require `p` odd; this is intrinsic, not slack. |
| 2 | `(g : ℤ_[p]ˣ)`                        | element of 𝒢 = ℤ_p^×       | element of the ambient group G | NO (within this project) | generalising `ℤ_p^×` to an abstract G means generalising the *entire* `PadicMeasure`/`padicZeta`/`GPlus` apparatus — mathlib has none of it, so there is no target to weaken toward. |
| 3 | `ζ_p` (`padicZeta p hp2`)            | the specific KL p-adic zeta | any c-invariant pseudo-measure | yes, in principle    | the proof only uses `([−1]−[1])·ζ_p = 0`; it would hold verbatim for any `q : Q(𝒢)` with `([−1]−[1])·q = 0`. But that abstraction is a *project-internal* refactor (a lemma about c-invariant pseudo-measures), not a literature-standard generalisation, and still about project-local objects mathlib lacks. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *for what it is* — within the project's
own vocabulary it is as general as the c-invariance input allows; the only
"weakening" (axis 3: replace `ζ_p` by an abstract c-invariant pseudo-measure) is a
project-internal abstraction over objects (`PadicMeasure`, `QuotientField`,
`dirac`) that **do not exist in mathlib at all**, so it cannot be a
mathlib-targeted generalisation.

Number of weakening opportunities found: 1 (axis 3), but project-internal, not
literature-grounded, and not a route to mathlib.

Cost of restatement: n/a — no mathlib-targeted restatement is available.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | Bundled-hypothesis preambles → typeclasses/instances?                                             | no       | — | already typeclass-driven (`Fact p.Prime`); the witness hypotheses are genuine data, not preambles. |
|  2 | Sequences/metric → filters/topological?                                                           | no       | — | no limits/convergence in the statement; purely algebraic identity in a fraction ring. |
|  3 | Construction → universal-property class?                                                          | no       | — | this is an equality of two given witnesses, not a construction of an object. |
|  4 | Set-with-closure-predicate → bundled substructure?                                                | no       | — | no subset/closure predicate here. |
|  5 | Vector-space/metric/field-specific → weakened typeclass (module/(semi)ring)?                       | no       | — | the base ring `PadicMeasure p ℤ_[p]ˣ` is already a specific commutative ring; the relevant abstraction (a c-invariant element of a fraction ring) is the axis-3 project-internal one, not a typeclass weakening. |
|  6 | 1-categorical → higher/∞-categorical?                                                              | no       | — | not categorical. |
|  7 | Concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid/ordered structure?                        | no       | — | no numeric index; the "index" is the group element `g`, already abstract within 𝒢. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.

One-line reason: this is a concrete algebraic equality (two pseudo-measure
witnesses coincide) proved by cancellation in a fraction ring; there is no
sequence-to-filter, construction-to-universal-property, or typeclass-weakening
move that improves its *mathlib* organisation — and its objects are project-local
in the first place.

---

### Diamond / defeq risk — `PadicMeasure.padicZeta_witness_neg`

n/a — declaration kind is **theorem** (no definitional equalities or
typeclass-search paths introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `PadicMeasure.padicZeta_witness_neg`

[A] Lean-Finder       n/a — Lean-Finder MCP not available in this session (no deferred tool); compensated with [D]+[E] over the vendored mathlib tree.
[B] Loogle            n/a — Loogle MCP not available in this session; the statement's head symbols (`padicZeta`, `QuotientField`, `dirac`, `PadicMeasure`) are project-local and would return nothing in any case.
[C] LeanSearch        n/a — LeanSearch MCP not available; natural-language target ("p-adic zeta witness symmetry") has no mathlib analog (no pseudo-measure theory in mathlib — see [D]).
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib/` for `pseudomeasure`/`pseudo_measure`/`PseudoMeasure`/`Iwasawa` (algebra) and `padicZeta`. **no hits** for any pseudo-measure / Iwasawa-algebra / p-adic-zeta concept. The only `Iwasawa` files are `GroupTheory/GroupAction/Iwasawa.lean` (Iwasawa's *simplicity criterion* for group actions) — entirely unrelated. Confirmed `IsFractionRing.injective` exists (`RingTheory/Localization/FractionRing.lean:137`) — the lone mathlib decl the proof uses.
[E] Name pattern      Grepped the whole repo for `padicZeta_witness_neg`: the declaration line is the **only** occurrence. No mathlib decl, no project decl, of that or a near name.

Searched for both:
  - the user's current form (witness symmetry for `ζ_p`) — not in mathlib;
  - the literature-standard form (c-invariant pseudo-measure descent to plus part) — the *entire apparatus* (Iwasawa algebra of measures, pseudo-measures, p-adic zeta, plus-part quotient) is absent from mathlib.

Concluded: **not in mathlib** (all methods exhausted — grep over the full
vendored mathlib tree, plus the name pattern, plus the literature-standard form;
the supporting MCP search tools were unavailable this session but the grep
evidence is conclusive: mathlib has no pseudo-measure / Iwasawa-algebra-of-
measures / p-adic-zeta theory whatsoever).

---

### Call sites — `PadicMeasure.padicZeta_witness_neg`

Internal use count: **0** (within the project, excluding the declaring file — and in fact zero across the entire repo).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none) | the only occurrence of `padicZeta_witness_neg` in the whole repo is its own declaration at `ZetaGalois.lean:93` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `padicZeta_witness_neg`?):
  - **Yes, effectively.** The file's *actual* descent route is
    `projPlus_padicZeta_witness` (`ZetaGalois.lean:190`) →
    `isPlusPseudoMeasure_padicZetaPlus` (`:240`) and `zetaIdealPlus_eq_span`
    (`:356`). That route establishes "ζ_p descends to 𝒢⁺" by pushing a single
    witness forward through `projPlus`, and it does **not** invoke
    `padicZeta_witness_neg`. So the "well-definedness of pushing witnesses to
    𝒢⁺" that this lemma's docstring claims to provide is supplied by a different
    (used) lemma. `padicZeta_witness_neg` is a **dead / superseded** sibling.

What the pattern tells you: **K = 0 internal uses, and the same purpose is
served by a different lemma that the consumers actually use.** Per the Phase 6
signal table this is the "dead code? / wrong abstraction" row — a strong
NO/BORDERLINE lean: it is either junk to delete or a genuine-but-orphaned result.

---

### Composition check (Phase 6)

Can `PadicMeasure.padicZeta_witness_neg` be derived from mathlib in ≤3 chained calls?

Attempt 1: `(IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) hkey).symm`
  - Mathlib decls used: `IsFractionRing.injective`.
  - Result: **fails as a standalone composition** — the call needs `hkey`
    (the equality of the two `algebraMap` images), and producing `hkey`
    requires the project-local chain: `units_dirac_mul_dirac` (to factor
    `[−g]−[g] = [g]·([−1]−[1])`), `map_mul`/`map_sub`, `sub_mul`, **and crucially
    `dirac_neg_one_sub_one_mul_padicZeta`** (the c-invariance `([−1]−[1])·ζ_p = 0`),
    then `sub_eq_zero`. That is multiple `have`s with non-trivial algebra between
    them, gated on a project-specific lemma.
  - Notes: the only mathlib step is the final injectivity; everything that makes
    the hypotheses combine is project-local and is "a proof, not a composition"
    per the Phase 6 heuristics (`have h := …; have h' := …; …` with real
    reasoning between).

Attempt 2 (different angle): inline the whole thing at call sites.
  - There are **no call sites** to inline into. So even the "delete and inline"
    refactor has nothing to act on.

Conclusion: **NOT-COMPOSABLE** (the result genuinely depends on the project-local
c-invariance lemma `dirac_neg_one_sub_one_mul_padicZeta` and the project-local
`dirac` multiplication law; mathlib supplies only the final `IsFractionRing.injective`).

---

## Verdict: `PadicMeasure.padicZeta_witness_neg`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the *framework* (pseudo-measures, c-invariance, plus-part descent) is classical and standard (Coates; Deligne–Ribet via Serre; nLab Iwasawa-algebra page; the source paper RJW arXiv:2309.15692 §11.1). But this specific "witness symmetry" lemma is **not separately named** anywhere — it is internal book-keeping inside the construction.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it is; the one weakening axis (abstract c-invariant pseudo-measure) is a project-internal refactor over objects mathlib lacks. Modern-idiom check: no mathlib-improving reformulation.
- Mathlib search (Phase 5): **not in mathlib** — mathlib has *no* pseudo-measure theory, no Iwasawa algebra of measures, no p-adic zeta function, no plus-part quotient. Conclusive by grep; supporting MCP search tools were unavailable this session.
- Composition check (Phase 6): **NOT-COMPOSABLE** — depends essentially on the project-local c-invariance `dirac_neg_one_sub_one_mul_padicZeta`; mathlib supplies only the final `IsFractionRing.injective`. **Call sites: K = 0**, and the lemma is superseded by the (used) `projPlus_padicZeta_witness` route.

**Rationale (1–2 paragraphs):**

This lemma sits at an awkward intersection. On one hand it clears the three "is
this real, novel-for-mathlib, and not trivially composable" bars: it is a
genuine algebraic fact (witnesses at `g` and `−g` coincide), it is *not* in
mathlib (mathlib has none of the Iwasawa-algebra/pseudo-measure/p-adic-zeta
apparatus it is phrased in), and it is *not* a 1–3 line mathlib composition
(its engine is the project-local c-invariance `([−1]−[1])·ζ_p = 0`). On the
other hand, every signal that would push it toward a confident YES is missing:
the literature does not name it (it is an inlined step inside RJW §11.1, not a
citable theorem), it is stated entirely in project-local vocabulary that mathlib
would have to acquire *en masse* first, and — decisively — **it has zero call
sites and is superseded by a sibling lemma (`projPlus_padicZeta_witness`) that
the actual `𝒢⁺`-descent consumers use instead.** A dead, unnamed, deeply
project-specific glue lemma is exactly the case the skill refuses to self-resolve:
"should mathlib have this?" hinges on judgment calls the worker cannot make —
chiefly, does mathlib want the *whole* Kubota–Leopoldt p-adic-zeta / pseudo-
measure / Iwasawa-algebra apparatus (a very large upstreaming program, of which
this lemma would be a late, minor corollary), and is this orphaned lemma even
being kept in the project or is it slated for deletion?

The honest reading is that **the unit of mathlib-worthiness here is the
apparatus, not this lemma.** If the project's `PadicMeasure` / pseudo-measure /
`padicZeta` development is ever upstreamed, this fact would ride along as a small
corollary of c-invariance (likely inlined, or stated as a lemma about *any*
c-invariant pseudo-measure rather than `ζ_p` specifically). On its own, detached
from that program and currently unused, it is not a standalone mathlib PR
candidate — but it is also not "mathlib already has it" or "compose it away",
because mathlib has nothing in this area. Hence BORDERLINE.

**Refactor-actionable bar — BORDERLINE-needs-human:**

Numbered questions for the user (each yes/no or short answer):

  1. **Is `padicZeta_witness_neg` still wanted in the project at all?** It has
     **zero call sites** and its stated purpose ("well-definedness of pushing
     witnesses to 𝒢⁺") is already delivered by the *used* lemma
     `projPlus_padicZeta_witness` (ZetaGalois.lean:190). If it is dead, the
     right action is **delete it** (a `/cleanup` dedup task), and the
     mathlibable question is moot.

  2. If it is kept: **is the intended mathlib contribution the whole pseudo-
     measure / `padicZeta` / Iwasawa-algebra-of-measures apparatus** (`PadicMeasure`,
     `dirac`, `QuotientField`, `IsPseudoMeasure`, `padicZeta`, `GPlus`, …), with
     this lemma as one late corollary? If yes, this single decl should **not** be
     PR'd alone — it should be sequenced as part of that much larger upstreaming
     program, and re-assessed in that context.

  3. **Should the statement be generalised away from `ζ_p` to "any c-invariant
     pseudo-measure"** before any mathlib consideration? The proof only uses
     `([−1]−[1])·q = 0`; a lemma `witness_neg` about an arbitrary `q : Q(𝒢)`
     with that property is strictly more reusable and is the form mathlib would
     prefer. (This would make it YES-but-generalise-first *relative to the
     apparatus*, but only once the apparatus itself is in scope.)

  4. **Does mathlib's roadmap actually want Kubota–Leopoldt p-adic L-functions /
     Iwasawa main-conjecture infrastructure** at this granularity, or is this
     research-frontier material that should mature in AINTLIB first? This is a
     mathlib-community taste/scope call the skill cannot make.

Next action: user answers (especially Q1 — it likely resolves to "delete as dead
code" via `/cleanup`). If kept and the apparatus is in scope, re-run
`/mathlibable` after generalising per Q3, treating the pseudo-measure framework
as the real upstreaming unit.

---

## Next step

User answers the four questions above. The most likely resolution is **Q1 → "dead
code, delete it"** (it is unused and superseded by `projPlus_padicZeta_witness`),
which removes it from mathlib consideration entirely. If instead it is kept, it is
**not** a standalone mathlib PR candidate: it would ride along as a minor corollary
*if and when* the project's entire pseudo-measure / `padicZeta` apparatus is
upstreamed, ideally first generalised to "any c-invariant pseudo-measure" per Q3.
