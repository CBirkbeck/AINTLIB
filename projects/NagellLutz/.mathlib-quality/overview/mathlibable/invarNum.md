# /mathlibable report — `EllSequence.invarNum`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single-declaration (Mode A).
> Local Lean build is stale; verdict reasoned from source + direct grep over the
> pinned mathlib (`d90090f`, `v4.31.0-rc2`) + WebSearch literature. lean_loogle /
> lean_leansearch MCP and ChatGPT MCP were unavailable in this environment; the
> "is it in mathlib" question is settled authoritatively by grep over the actual
> vendored mathlib source, which is stronger evidence than the index for *absence*.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale locally (not rebuilt); reasoned from source — decl elaborates in the committed tree
- decl `EllSequence.invarNum`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:140`
- qualified name:           `EllSequence.invarNum` (inside `namespace EllSequence`, opened line 90, closed line 597) — VERIFIED
- kind:                     `def`
- has sorry:                no
- module docstring summary: Elliptic divisibility sequences (EDS); defines EDS and constructs normalised EDSs from initial terms — this fork *extends* mathlib's file with Stange's elliptic-net machinery (`addMulSub`/`net`/`rel₄`/`HaveSameParity₄`) and the invariant `invarNum`/`invarDenom`.

---

### Statement (Phase 1)

`EllSequence.invarNum` is **a definition**: the numerator of a projective invariant
attached to a sequence `W : ℤ → R` over a commutative ring `R`. For shift parameter
`s` and index `n`,

```
invarNum W s n = (W(n+2s)·W(n−s)² + W(n+s)²·W(n−2s))·W(s)² + W(n)³·W(2s)²
```

Paired with `invarDenom W s n = W(n+s)·W(n)·W(n−s)`, the design intent (stated in the
docstring) is that for a *genuine* elliptic sequence the ratio
`invarNum W s n / invarDenom W s n` is **independent of `n`** (a constant of the
sequence, for each fixed `s`). This is the EDS analogue of Ward's classical
"symmetry"/invariant `W_{n+1}W_{n−1}/W_n²`; the `s`-parameter generalises Ward's
unit-shift form to an arbitrary shift. The constancy is the content of the
neighbouring theorem `invar_of_net` (line 149): if `W` satisfies all four-index net
relations (`net W p q r s = 0`), then
`invarNum W s m · invarDenom W s n = invarNum W s n · invarDenom W s m`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring; maximal sensible generality already.
- `(W : ℤ → R)` — the sequence (section variable, made explicit in the def).

Hypotheses (Lean side): none — it is a bare polynomial `def` in the values of `W`.

Conclusion (math): n/a — definition (an element of `R`).
Conclusion (Lean): `R`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper `def` — the numerator half of an invariant, an algebraic
building-block for `invar_of_net`. Not a named theorem, not a new mathematical
*structure* (the structure is `IsEllSequence` / Stange's net, defined elsewhere in
the file), not listed under `## Main statements` (which names only
`isEllDivSequence_normEDS`). It is BIG-adjacent only in that it is part of an EDS
theory that is itself eminently mathlib-worthy — but the individual decl is small.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **2 substantive lines** (the `(… + …)·W s²` line plus the `+ W n³·W(2s)²` line).
One-liner verdict: **MULTI-LINE** → the one-line exemption table is not required.
Note: even were it folded to one line, it would clearly clear the bar — it is a
named, docstring'd API object with 65 in-repo references (Phase 6.0).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS invariant `W(n+2s)W(n−s)² … ` numerator/denominator constant                               | partial | The *exact* `invarNum`/`invarDenom` split is not a textbook-named object | Ward recurrence is standard; this specific 2-line numerator is a formalisation-internal repackaging |
|  2 | WebSearch (general / named-after)| Stange elliptic nets, four-term relation, division polynomials                                  | yes  | Stange's elliptic nets (the `net`/`rel₄` parent machinery) — arXiv `0710.1316`       | confirms the *parent* concept (nets) is standard & named; `invarNum` is a derived quantity |
|  3 | WebSearch (Ward invariant)       | EDS "projective invariant", constant ratio `W_{n+1}W_{n−1}/W_n²`, Ward symmetry formula        | yes  | Ward's invariant / symmetry formula: `W_{n+1}W_{n−1}/W_n²` (the `s=1` case)          | Wikipedia "Elliptic divisibility sequence"; Ward 1948 Memoir |
|  4 | WebSearch (recent recurrence)    | arXiv 2102.07573 Verzobio recurrence for EDS; arXiv `0710.1316` Stange                          | yes  | Verzobio: recurrence/denominator conditions; reaffirms `h_{m+n}h_{m−n}h_r² = …` form | the *family* (recurrences/invariants of EDS) is live research, but no decl named `invarNum` |
|  5 | ChatGPT MCP                      | "standard form of EDS invariant and its generality / historical evolution"                      | n/a  | MCP unavailable in this environment                                                  | recorded n/a — could not run; compensated by channels 1–4, 6–10 |
|  6 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/`                  | n/a  | neither directory exists                                                             | no project reference PDFs to consult |
|  7 | nLab                             | "elliptic divisibility sequence" / "elliptic net" invariant                                     | n/a  | nLab has no dedicated EDS/elliptic-net page with this invariant                      | concept is number-theoretic, not categorical — nLab thin here |
|  8 | nCatLab                          | (categorical angle)                                                                             | n/a  | not a categorical concept                                                            | n/a with reason |
|  9 | Stacks Project                   | division polynomials / EDS invariant                                                            | n/a  | Stacks does not cover EDS / division-polynomial recurrences                          | not an alg-geom-schemes concept in Stacks' scope |
| 10 | MathOverflow / arXiv (≤5y)       | EDS invariant constant ratio; Stange nets valuations (arXiv 2512.09601, eprint 2025/521)        | yes  | the *net*/invariant theory is actively used; `invarNum` itself unnamed              | confirms forward-research relevance of the surrounding theory |

### Literature summary (Phase 3)

Concept identified as: the **numerator of a projective invariant of an elliptic
(divisibility) sequence** — the EDS analogue of Ward's symmetry/invariant
`W_{n+1}W_{n−1}/W_n²`, here generalised to an arbitrary shift `s` and expressed in a
form adapted to Stange's four-index *net* relations.
Sources agree on the standard form: **no, for `invarNum` itself.** The literature
fixes (a) the *recurrence* (Ward), (b) the *net* generalisation (Stange), and (c)
Ward's invariant in the `s=1` shape. The specific `invarNum`/`invarDenom`
decomposition — and in particular the `s`-shift generalisation with the
`+ W(n)³·W(2s)²` correction term — is a **formalisation-internal repackaging** chosen
so the constancy proof reduces cleanly to net relations (`invar_of_net`), and so it
avoids odd-function/char-3 peculiarities (cf. the `net` docstring at line 112).
Most general standard form: Ward's invariant is the `s=1` specialisation; the fork's
`invarNum W s n` is already *more* general (any `s`).
Generality dimensions where the literature varies:
  - coefficient domain: classically `ℤ` / a field; the fork uses any `CommRing R` — already maximal.
  - shift: literature fixes `s=1`; the fork takes general `s` — already maximal.
Disagreement with the literature: none mathematically; it is a strict generalisation
of the classical object, stated in a non-canonical (proof-driven) algebraic shape.

---

### Generality analysis — `EllSequence.invarNum`

Literature-standard form (Phase 3): Ward's invariant `W_{n+1}W_{n−1}/W_n²` over `ℤ`
(or a field) — the `s=1` case, no explicit denominator split.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | arbitrary commutative ring | `ℤ` / a field                  | NO                  | already at the maximal sensible algebra; the def is a polynomial in `W`'s values, needs only `+`, `·`, `−` — `CommRing` is exactly right. Could *in principle* drop to `CommSemiring` but the surrounding `net`/`rel₄` use subtraction, so `CommRing` is the coherent choice for the file. |
| 2 | `(W : ℤ → R)`          | sequence over `ℤ`        | sequence over `ℤ`               | NO                  | EDS are intrinsically `ℤ`-indexed; no generalisation intended. |
| 3 | `(s : ℤ)` shift        | arbitrary integer shift  | fixed `s = 1` (Ward)            | n/a (already MORE general) | the fork already generalises beyond the literature standard. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (indeed strictly more general than the
classical `s=1` invariant).
Number of weakening opportunities found: 0 (the only candidate — `CommRing` →
`CommSemiring` — is rejected as incoherent with the subtraction-using `net`/`rel₄`
neighbours that this def exists to serve).
Proposed restatement: none on generality grounds.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | —                      | it is a bare `def` over `(W : ℤ → R)`; no bundled hypotheses to classify. |
|  2 | sequences/metric → filters/nets/topology?                                                  | no       | —                      | purely algebraic identity; no limiting/topological content. |
|  3 | construct an object where a universal-property class would characterise it?                | no       | —                      | `invarNum` is an explicit polynomial expression; there is no universal property to abstract. |
|  4 | set-with-closure-predicate → bundled substructure?                                          | no       | —                      | not a substructure. |
|  5 | vector-space/metric/field-specific → modules/(semi)ring weakening?                         | no       | —                      | already `CommRing`-general (Phase 4a row 1). |
|  6 | 1-categorical → higher-categorical?                                                         | no       | —                      | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive monoid/group?                                  | no       | —                      | the `ℤ`-indexing is intrinsic to EDS; generalising the index breaks the concept. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: it is an explicit algebraic expression in `W`'s values over an
already-maximal `CommRing`; there is no preamble to classify, no construction to
turn into a universal property, no index/structure to abstract. The only
"reformulation" question that is *real* is the proof-internal shape (see BORDERLINE
question 2 below), which is a mathlib-taste call, not a modernisation move.

---

### Diamond / defeq risk — `EllSequence.invarNum`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|-----------------------|
| 1 | Typeclass diamond            | none    | no new instance; a plain `def : R`. No typeclass-search path introduced. |
| 2 | Reducibility leak            | none    | no `@[reducible]`; sealed semireducible. Body is a non-trivial polynomial, so leaving it sealed is correct — consumers `simp_rw [invarNum]` explicitly (lines 151, 610). |
| 3 | Non-canonical unfolding      | low     | consumers must `simp [invarNum]` / `simp_rw [invarNum]` to unfold — intended; no surprise `rfl`-unfolding since there is no `@[simp]`. |
| 4 | Instance priority collision  | none    | not an `instance`. |
| 5 | Universe-polymorphism issues | none    | `R : Type u`, body lives in `R`; no forced annotation, no polymorphic call-site breakage. |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE** (one `low` row, fully intended).
Top risks: none.
Mitigations: n/a.

---

### Mathlib search-status: `EllSequence.invarNum`

[A] Lean-Finder       — (MCP unavailable in env)                   n/a: tool not reachable here
[B] Loogle            `EllSequence.invarNum` / `_ → ℤ → ℤ → R` shape n/a: MCP unavailable — substituted by [D] over real source
[C] LeanSearch        "EDS invariant numerator" / "Ward invariant"   n/a: MCP unavailable — substituted by [D]
[D] Grep mathlib src  `invarNum`, `invarDenom`, `addMulSub`, `def net`, `def rel₄`, `HaveSameParity`, `namespace EllSequence` over `.lake/packages/mathlib/Mathlib/`  → **no hits** (the only "EllSequence" matches are substrings of `IsEllSequence`)
[E] Name pattern      `\b(def|lemma|theorem)\s+invarNum\b` over mathlib  → no hits

Searched for both:
  - the user's current form (`invarNum W s n`) — absent.
  - the literature-standard form (Ward `W_{n+1}W_{n−1}/W_n²`, and Stange's `net`) — the
    *parent* net machinery is also absent from mathlib; mathlib's EDS file
    (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, 547 lines) contains only
    `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence` / `preNormEDS` / `normEDS` /
    `complEDS` / `Map` — **no `EllSequence` namespace, no nets, no invariant.**

Concluded: **not in mathlib** (grep over the actual pinned mathlib source exhausted;
the literature-standard parent forms are absent too). The entire `EllSequence`
namespace — `addMulSub`, `net`, `rel₄`, `Rel₃`, `HaveSameParity₄`, `invarNum`,
`invarDenom`, `invar_of_net` — is **net-new forward development in this fork**, authored
by the same person as mathlib's EDS file (David K. Angdinata; identical copyright
header), evidently en route to upstreaming. The pinned mathlib (`d90090f`) does not yet
have it.

---

### Call sites — `EllSequence.invarNum`

Internal use count: **65** references repo-wide (excluding the declaring lines 138–143).
External-to-file callers: 3 distinct `.lean` files.

| Caller file:line                                                                 | Usage pattern (one-line excerpt) |
|----------------------------------------------------------------------------------|-----------------------------------|
| NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:150                      | `invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m` (`invar_of_net`) |
| HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:91,578,607,613,860,961 | `invar_of_net`, `IsEllSequence.invar`, `invarNum_normEDS*`, `invarNum_eq_redInvarNum_mul`, `net_invar` |
| NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean                  | same machinery (an older copy of the file) |

Inline-derivation grep (re-derived elsewhere without using `invarNum`?): none — every
site goes through the named def.

Composability signal: **K = 65 internal uses, no inline re-derivation → real API; the
def is the backbone of the invariant theory (`invar_of_net` → `IsEllSequence.invar` →
`invarNum_normEDS` → `redInvarNum`).** Leans firmly toward a YES-* bucket.

Caveat noted: the code is **duplicated** across NagellLutz and HasseWeil (and an
`...Original.lean` copy). That is a *project-internal dedup concern* (one consolidation
target), orthogonal to the mathlib verdict — both copies are the same upstream-bound
object.

---

### Composition check (Phase 6)

Can `EllSequence.invarNum` be derived from mathlib in ≤3 chained calls?

Attempt 1: build it from any existing mathlib EDS API.
  - Mathlib decls available: `IsEllSequence`, `normEDS`, `preNormEDS`, … — none expose an
    invariant or net.
  - Result: **fails** — there is no mathlib primitive for the invariant; one would have
    to *write this very polynomial*, which is the definition itself, not a composition.

Attempt 2: as a `def`, "composition" would mean expressing it via existing named
mathlib objects. There are none (`addMulSub`/`net`/`rel₄` are also absent).
  - Result: fails.

Conclusion: **NOT-COMPOSABLE.** It is an irreducible new definition relative to mathlib;
no 1–3 call inlining exists.

---

## Verdict: `EllSequence.invarNum`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *parent* theory (Ward EDS recurrence, Stange elliptic
  nets) is standard and named and clearly mathlib-worthy; but `invarNum`/`invarDenom`
  *as split* is a formalisation-internal, proof-driven repackaging — not a literature-named object.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (`CommRing`, arbitrary shift `s` —
  strictly more general than Ward's `s=1`); no modern-idiom restatement applies.
- Mathlib search (Phase 5): **not in mathlib** — the whole `EllSequence` namespace is
  net-new forward development by mathlib's own EDS author.
- Composition check (Phase 6): **NOT-COMPOSABLE** — irreducible new def. Call sites: K=65, real API.

**Rationale:**

Every individual gate points "YES": the definition is not in mathlib, is not composable
from mathlib, is at maximal generality, carries zero diamond/defeq risk, is sorry-free,
has a docstring, and is load-bearing (65 uses driving the `invar_of_net` →
`IsEllSequence.invar` → `invarNum_normEDS` chain). The surrounding theory (elliptic
divisibility sequences and Stange's elliptic nets) is unquestionably in-scope for
mathlib — indeed mathlib already hosts the EDS file this fork extends, by the same author.
So this is **not** a NO bucket: mathlib does not have it, cannot cheaply compose it, and
should eventually have something like it.

It is **not** clean-cut YES-add-as-is either, for one reason that is a genuine
mathlib-taste judgment, not a mechanical defect: `invarNum`/`invarDenom` is an
*intermediate algebraic shape chosen to make the constancy proof go through via net
relations* (the docstring even flags that signs/term-order were tuned vs. Stange's paper
"to make the equivalence with elliptic relations unconditional" and "avoid peculiarities
in characteristic 3"). It is the numerator/denominator of an invariant whose *canonical*
public face in mathlib might instead be the **invariant itself** (a single `def` returning
the ratio, or a theorem `invarNum s m * invarDenom s n = invarNum s n * invarDenom s m`
stated as "the projective point `[invarNum : invarDenom]` is `n`-independent"), with
`invarNum`/`invarDenom` as `private`/auxiliary. Whether mathlib wants the two halves
exposed as public API, or only the assembled invariant, and whether the `s`-generalised
proof-tuned form is the one to upstream (vs. re-deriving from a cleaner net statement),
are decisions for a human/mathlib reviewer — they shape the public API, not just the
proof. This is also entangled with a project-internal dedup decision (NagellLutz vs.
HasseWeil vs. `…Original.lean`), which should be resolved before any upstream PR.

Because the per-gate signal is YES-shaped but the *form to upstream* hinges on an
API-taste call the skill should not make unilaterally, the honest verdict is BORDERLINE
with the questions below. (Default leaning, if forced: **YES-but-generalise-first** — ship
the *whole* `EllSequence` net + invariant block as a coherent mathlib contribution, with
`invarNum`/`invarDenom` possibly demoted to auxiliaries behind the assembled-invariant
API — never NO.)

**Numbered questions (for the human / mathlib reviewer):**

1. Should mathlib expose `invarNum` and `invarDenom` as **public** API, or only the
   *assembled* invariant (the constancy statement `invarNum s m · invarDenom s n =
   invarNum s n · invarDenom s m`, i.e. `IsEllSequence.invar`), with these two halves
   made `private`/auxiliary?
2. Is the proof-tuned algebraic shape (sign/term-order tweaks vs. Stange, the
   `+ W(n)³·W(2s)²` term, the `s`-shift generalisation) the form to upstream — or should
   the upstream object be re-derived from a cleaner net/`rel₄` statement and `invarNum`
   kept internal?
3. This decl is **duplicated** across `NagellLutz`, `HasseWeil`, and an `…Original.lean`
   copy. Consolidate to a single owner (likely `HasseWeil`, the larger/maintained copy, or
   a shared `Common/`) **before** any mathlib PR — agreed?
4. Upstreaming should ship the **whole `EllSequence` block** (`addMulSub` → `net`/`rel₄` →
   `HaveSameParity₄` → `invarNum`/`invarDenom` → `invar_of_net`) as one coherent PR
   extending `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, not `invarNum`
   alone — confirm the grain.

**Next action:** user/reviewer answers Q1–Q4; then re-run `/mathlibable EllSequence.invarNum`
(or proceed directly to a consolidation + `/generalise` pass over the whole `EllSequence`
namespace, since the natural mathlib contribution is the *block*, not this one def). The
target file for any eventual PR is `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(same file this fork already extends).

---

## Next step

Resolve Q1–Q4 (public API surface for the two halves vs. the assembled invariant; whether
to upstream the proof-tuned shape; project-internal dedup across the 3 copies; PR grain =
whole `EllSequence` block). Then upstream the `EllSequence` net+invariant machinery as one
PR extending `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. Do **not** delete
locally — this is net-new, not-composable, maximal-generality forward development; the only
open question is the public *form*, not whether mathlib should have the result.
