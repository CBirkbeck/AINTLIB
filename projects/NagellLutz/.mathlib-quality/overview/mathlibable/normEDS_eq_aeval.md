# /mathlibable report — `normEDS_eq_aeval`

> AINTLIB `/overview` Step-9 mathlibable assessment, single declaration.
> Project: `projects/NagellLutz` (Nagell–Lutz theorem; elliptic divisibility sequences).
> Build state: local Lean build stale; assessment reasons from the source statement +
> mathlib-index search (loogle/leansearch) + WebSearch. ChatGPT MCP was down (Codex error);
> WebSearch fallbacks used per skill protocol.

### Baseline (Phase 0)
- lake build:               (stale — not re-run; reasoned from source per task brief)
- decl `normEDS_eq_aeval`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1188`
- qualified name:           **`normEDS_eq_aeval`** — *bare, no namespace.* The file's only top-level
  `namespace EllSequence` (line 90) closes at line 597; the decl lives in `section NormEDS`
  (line 881–1520), a **section** not a namespace. So the fully-qualified name is `normEDS_eq_aeval`.
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: elliptic divisibility sequences — `EllSequence` / `normEDS` API,
  forked + extended from `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`normEDS_eq_aeval` states: for a commutative ring `R` and parameters `b c d : R`, the normalised
elliptic divisibility sequence `normEDS b c d : ℤ → R` is obtained from the **universal** normalised
EDS by specialising along an evaluation homomorphism. Concretely,

  `normEDS b c d  =  fun n ↦ aeval (Param.rec b c d) (universalNormEDS n)`

where:
- `Param` is the 3-element inductive type `{B, C, D}` (one generator per EDS parameter);
- `universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)` is the "generic" EDS
  over the 3-variable integer polynomial ring (a UFD/domain);
- `aeval (Param.rec b c d) : MvPolynomial Param ℤ →ₐ[ℤ] R` is the unique ℤ-algebra hom sending
  the generator `X p` to `Param.rec b c d p` (i.e. `X B ↦ b`, `X C ↦ c`, `X D ↦ d`).

In words: *every normalised EDS is the image of the one universal/generic normalised EDS under the
evaluation map that sends the formal parameters to the actual ones.* This is the standard
"universal object + specialisation morphism" device; here its purpose is to transfer
nonzero-divisor / non-vanishing arguments from the polynomial domain down to an arbitrary `R`
(see the immediate consumers `universalNormEDS_ne_zero`, `universalNormEDS_mem_nonZeroDivisors`,
and `IsEllSequence.normEDS`).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the target ring.
- `(b c d : R)` — the EDS parameters (section variables, line 883).

Hypotheses: none.

Conclusion (math): `normEDS b c d` factors as `aeval (Param.rec b c d) ∘ universalNormEDS`.
Conclusion (Lean): `normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·)`
(an equality of functions `ℤ → R`).

Proof body (1 line):
```lean
simp_rw [universalNormEDS, map_normEDS, aeval_X]
```
— unfold `universalNormEDS`, push the algebra hom through the construction via `map_normEDS`
(the ring-hom-compatibility lemma `f (normEDS b c d n) = normEDS (f b) (f c) (f d) n`), then collapse
`aeval (Param.rec b c d) (X p)` to `Param.rec b c d p` via `aeval_X`. That is the *entire* content.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a glue lemma — restates `normEDS` through its universal `MvPolynomial` instance; one-line
proof; pure composition of `map_normEDS` + `aeval_X`. Not a named theorem, not a `## Main result`
(the Nagell–Lutz main results are downstream). It is *infrastructure* for the nonzero-divisor
transfer trick, not a mathematical statement of independent interest.

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the formal one-liner gate does not apply. Noted
nonetheless: the *proof* is a single substantive line and is a textbook composition (see Phase 6).
The companion `def universalNormEDS` (line 1186) **is** a one-line `def`; it is the device that gives
this lemma its reason to exist (the `Param`/`universalNormEDS` scaffolding), and is assessed only
insofar as it bears on this lemma's verdict.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "universal elliptic divisibility sequence polynomial ring specialization ring homomorphism"            | yes  | division polynomials = generic EDS over `ℚ[x,y,A,B]/(y²−x³−Ax−B)`; specialise via ring hom | arXiv 1105.5633 (Silverman), Wikipedia "Elliptic divisibility sequence"/"Division polynomials" — the *idea* is standard and foundational |
|  2 | WebSearch (general/named form)   | "normalised elliptic divisibility sequence universal polynomial Mazur Tate generic"                    | yes  | Tate-normal-form one-parameter family; division polynomials as universal example | arXiv 1101.3839, 0710.1316 (Stange, elliptic nets); confirms genericity is classical, but no *named* "normEDS = aeval(universal)" lemma |
|  3 | WebSearch (mathlib idiom)        | "mathlib MvPolynomial aeval_X universal property specialization ring homomorphism lemma pattern"        | yes  | `aeval`: unique hom `A[Xᵢ] → B` extending ρ, `Xᵢ ↦ bᵢ` — exactly `MvPolynomial.aeval_X` | leanprover mathlib4 docs (`Algebra.MvPolynomial.Basic`, `RingTheory.Extension.Generators`) — this is the mathlib primitive the lemma is built from |
|  4 | ChatGPT MCP                      | "is `normEDS_eq_aeval` a citable statement or glue over `map_normEDS`+`aeval_X`; ≤3-call composition?"  | n/a  | —                                | MCP **down** (Codex `exec` error); substituted by channels 1–3 + direct reasoning per task brief |
|  5 | Local references                 | `.mathlib-quality/references/` for "EDS / universal / division polynomial"                              | n/a  | (no references dir present)      | `projects/NagellLutz/.mathlib-quality/references/` absent → recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "division polynomial" / "universal property polynomial ring"        | n/a  | nLab has the generic universal-property of polynomial rings, nothing EDS-specific | the universal-property content reduces to the free-commutative-algebra adjunction, which mathlib already encodes as `aeval` |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                | not a categorical concept beyond the free-algebra adjunction already covered in #6 |
|  8 | Stacks Project                   | division polynomials / elliptic divisibility sequence                                                   | n/a  | —                                | EDS are not a Stacks topic; the underlying "represent a functor by a polynomial ring" is generic AG folklore, not a citable Stacks tag for this lemma |
|  9 | MathOverflow / Math.StackExchange| "elliptic divisibility sequence universal / generic division polynomial specialization"                | yes  | confirms division polynomials are *the* universal EDS; specialisation by ring hom is standard | corroborates #1; no statement at the granularity of this Lean lemma |
| 10 | recent arXiv (last 5 yr)         | "division polynomials arbitrary isogenies" (Stange 2025, eprint 2025/521; arXiv 2503.15428)            | yes  | extends division-poly/universal framework | confirms the universal viewpoint is live + standard; still no atomic "construction = aeval(universal)" lemma — it is taken as obvious |

### Literature summary (Phase 3)

Concept identified as: the **universal / generic elliptic divisibility sequence** (the division
polynomials over `ℤ[a₁..a₆]` or `ℚ[x,y,A,B]/(…)`), together with **specialisation by a ring
homomorphism**. This is a foundational and standard idea (Silverman, Stange, Ward; Wikipedia).
Sources agree on the standard form: **yes** — the genericity of division polynomials / EDS and
recovery of any concrete EDS by a specialisation map is classical and uncontroversial.
Most general standard form: *the division polynomials form the universal EDS; any EDS is its
pullback along the specialisation morphism of the relevant coefficient ring.*
Generality dimensions where the literature varies: parameter ring (`ℤ[a₁..a₆]` Weierstrass vs.
the 3-parameter `b,c,d` normalised form vs. Tate normal form) — all the same idea.
Disagreement with the literature: **none.** Crucially, the literature treats "every EDS is a
specialisation of the universal one" as an *evident* structural remark, **not** as a separately
named/citable theorem. There is no "normEDS = aeval(universal)" lemma in the sources — it is the
trivial functoriality of the construction, which is exactly what `map_normEDS` already records.

---

### Generality analysis — `normEDS_eq_aeval`

Literature-standard form (from Phase 3): any normalised EDS over `R` is the image of the universal
normalised EDS under the ℤ-algebra specialisation `b,c,d`.

| # | Parameter / hypothesis  | Current Lean form                | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------|----------------------------------|------------------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`          | commutative ring                 | commutative ring (base for `normEDS`) | NO               | `normEDS`/`aeval`/`MvPolynomial` already require `CommRing`; this is the mathlib-base generality. Cannot weaken. |
| 2 | `(b c d : R)`           | three ring elements              | three parameters                   | NO                 | intrinsic to the normalised-EDS construction. |
| 3 | universal ring `MvPolynomial Param ℤ` | free comm-ℤ-algebra on 3 gens | free comm-algebra on the parameter set | structurally fixed | already the most general "universal" choice — initial object over ℤ for 3 parameters. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is already stated for an arbitrary `CommRing R`, which
is the base generality of `normEDS` itself). No weakening opportunities.
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | bundled-hypothesis preambles → typeclasses/instances?                                              | no       | —                      | already typeclass-driven (`CommRing`) |
|  2 | sequences/metric → filters/topological?                                                            | no       | —                      | purely algebraic; no topology |
|  3 | construct an object where a universal-property *class* would characterise it?                      | partial  | the universal property in play **is** `aeval` (`MvPolynomial.aeval_X` / `RingTheory.Extension.Generators`) — mathlib already provides the universal-property class | confirms the lemma is the *application* of an existing universal-property API, not a new one |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | —                      | n/a |
|  5 | vector-space/field-specific → weaken typeclass?                                                    | no       | —                      | already at `CommRing` |
|  6 | 1-categorical → higher-categorical?                                                                | no       | —                      | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure?                                            | no       | —                      | the `ℤ`-index of the sequence is intrinsic to EDS |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (as a contribution). The modern idiom this lemma *uses* —
`MvPolynomial.aeval` / `aeval_X` as the universal property of the free commutative algebra — is
**already in mathlib**, and the lemma is precisely the one-step application of it to `normEDS` via
`map_normEDS`. There is no cleaner reformulation that would be a contribution: the clean form *is* the
two existing primitives composed. This pushes the verdict toward NO-composable, not toward
YES-but-generalise.

---

### Mathlib search-status: `normEDS_eq_aeval`

[A] Lean-Finder       "normEDS specialization universal MvPolynomial"   no hits (construction is project-coined: `Param`, `universalNormEDS`)
[B] Loogle/Grep       grep `.lake/.../Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` + `DivisionPolynomial/` for `normEDS_eq_aeval` | `universalNormEDS` | `eq_aeval` | `Param` | `aeval`   → **zero hits** (mathlib's EDS file has NO universal/aeval factorisation, no `Param`, no `aeval` at all)
[C] LeanSearch        "every normalised elliptic divisibility sequence is a specialisation of a universal one"   no hits
[D] Grep mathlib src  pattern `_eq_aeval ` repo-wide → hits exist (`AdjoinRoot`, `PowerBasis`, `MvPolynomial.Ideal`, `PowerSeries.Substitution`, …) → confirms `_eq_aeval` is a *recognised mathlib naming idiom*, but **none** for EDS / `normEDS`
[E] Name pattern      `normEDS_eq_aeval`, `universalNormEDS` → only in-project (NagellLutz + HasseWeil), never in `.lake/packages/mathlib`

Searched for both:
  - the user's current form (`normEDS = aeval(Param.rec…) ∘ universalNormEDS`) — not in mathlib;
  - the literature-standard form (any EDS = specialisation of universal EDS) — not stated as a lemma
    in mathlib's EDS file; mathlib has only `normEDS` + the building blocks `map_normEDS`, `aeval_X`.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib *does*
have the **building blocks** — `map_normEDS` (in the same mathlib EDS file the project forks) and
`MvPolynomial.aeval_X` — but not the assembled lemma, and not the `universalNormEDS`/`Param` device it
is stated against.

---

### Call sites — `normEDS_eq_aeval`

Internal use count (NagellLutz, excluding the declaring lines 1188–1189): **2**
- `EllipticDivisibilitySequence.lean:1212` — `rw [normEDS_eq_aeval]` inside `IsEllSequence.normEDS`
  (to pull the EDS-is-elliptic property back from the polynomial domain).
- `EllipticDivisibilitySequence.lean:1466` — `rw [normEDS_eq_aeval, show …]` in the nonzero-divisor /
  divisibility track.

External-to-file callers (within NagellLutz): 0 (it is used only inside its own file; downstream
NagellLutz results consume the *theorems proved with it*, not the glue lemma directly).

Repo-wide (cross-project): an **independent identical copy** lives in
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:641` (same `universalNormEDS`,
same statement, proof `funext n; unfold universalNormEDS; simp [MvPolynomial.aeval]`), with **6**
internal uses there (lines 673, 731, 803, 807, 954, 979). So the *device* is duplicated across two
AINTLIB projects — a dedup target — but neither copy is consumed outside its project.

| Caller file:line                                   | Usage pattern (one-line excerpt)                          |
|----------------------------------------------------|-----------------------------------------------------------|
| NagellLutz/…/EllipticDivisibilitySequence.lean:1212 | `rw [normEDS_eq_aeval]` (in `IsEllSequence.normEDS`)     |
| NagellLutz/…/EllipticDivisibilitySequence.lean:1466 | `rw [normEDS_eq_aeval, show …]` (divisibility track)     |
| HasseWeil/…/EllipticDivisibilitySequence.lean:641   | *duplicate declaration* (+6 uses in that file)            |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `normEDS_eq_aeval`?):
  - (none beyond the HasseWeil duplicate — which is a full re-declaration, not an inline re-derivation).

Composability signal: K = 2 internal uses, no inline bypass → *real local API* within the
universal-EDS scaffolding, **but** the entire scaffolding (`Param`, `universalNormEDS`, this lemma,
and the `*_ne_zero` / `*_mem_nonZeroDivisors` helpers) is a project-local proof device, duplicated,
with no mathlib-side consumer.

---

### Composition check (Phase 6)

Can `normEDS_eq_aeval` be derived from mathlib in ≤3 chained calls? **Yes — and it already is.**

Attempt 1: the lemma's own proof.
```lean
example : normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) := by
  simp_rw [universalNormEDS, map_normEDS, aeval_X]
```
  - Mathlib decls used: `map_normEDS` (mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`,
    ring-hom compatibility of `normEDS`) and `MvPolynomial.aeval_X` (the `aeval` universal property).
    `universalNormEDS` is unfolded (it is `normEDS (X B) (X C) (X D)`, a project def).
  - Result: **succeeds** — this is the verbatim one-line proof. The HasseWeil copy closes it with a
    single `simp [MvPolynomial.aeval]`.
  - Notes: 2 mathlib lemmas + 1 unfold = exactly the "≤3 mathlib-call composition" pattern. No new
    mathematical idea; pure functoriality (`map_normEDS`) followed by generator-evaluation (`aeval_X`).

Conclusion: **COMPOSABLE** (≤3 calls; the lemma *is* the composition).

Caveat carried to Phase 7: the composition is stated *against a project-local universal object*
(`universalNormEDS : ℤ → MvPolynomial Param ℤ`) and a project-local `inductive Param`. Mathlib has
neither. So although the *proof* is a trivial mathlib composition, the *statement* is not phrasable in
pure mathlib vocabulary — it presupposes the `Param`/`universalNormEDS` scaffolding, which is a
deliberate proof-engineering device (transfer nonzero-divisor facts from the polynomial domain to
general `R`), not a mathlib-target concept.

---

## Verdict: `normEDS_eq_aeval`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the universal-EDS / specialise-by-ring-hom idea is standard and
  foundational, but is treated everywhere as an *evident structural remark*, never a named theorem —
  i.e. it is the trivial functoriality already captured by `map_normEDS`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL already (`CommRing R`); Phase 4c found the only
  "modern idiom" in play (`aeval` universal property) is **already in mathlib** — the lemma is its
  application, not a new contribution.
- Mathlib search (Phase 5): not in mathlib; but the **building blocks are** — `map_normEDS` (mathlib
  EDS file) + `MvPolynomial.aeval_X`.
- Composition check (Phase 6): COMPOSABLE — the verbatim one-line proof `simp_rw [universalNormEDS,
  map_normEDS, aeval_X]` is the ≤3-call composition.

**Rationale:**

`normEDS_eq_aeval` is a glue lemma whose entire mathematical content is "the `normEDS` construction
commutes with ring homomorphisms" (which mathlib already has as `map_normEDS`) followed by "`aeval`
sends each generator to its assigned value" (mathlib's `MvPolynomial.aeval_X`, the universal property
of the free commutative algebra). Composing those two is exactly the one-line proof. There is no new
mathematical idea, no named theorem in the literature at this granularity, and no weakening to make.
It is the Lean encoding of the classical "specialise the universal/generic EDS" move, used purely as
internal scaffolding to push nonzero-divisor and non-vanishing facts down from the polynomial domain
`MvPolynomial Param ℤ` to an arbitrary `CommRing R`.

It is *not* `NO-mathlib-has-it`, because mathlib has no `universalNormEDS`/`Param` object and no
assembled lemma — the statement is unphrasable in pure mathlib vocabulary. It is *not* a YES bucket,
because shipping it would mean shipping the whole project-local `Param`/`universalNormEDS` proof
device, which is an internal "transfer to the universal domain" trick (cf. the literature's
division-polynomials-over-`ℤ[a₁..a₆]`), not a concept mathlib targets — and even then the lemma itself
would still be a 2-lemma composition. The right home is the call site: where mathlib's EDS API needs a
"reduce to the integral case" argument, it should either (a) build the universal object inline and
close the goal with `map_normEDS` + `aeval_X`, or (b) — better, as a *separate, larger* design
question — have mathlib's own EDS file provide a `normEDS_of_mem_nonZeroDivisors`-style API so the
universal detour is unnecessary. Neither requires *this* lemma as a standalone mathlib declaration.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; `normEDS_eq_aeval` is a 2-mathlib-lemma + 1-unfold composition.

Mathlib building blocks:
- `map_normEDS` — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (ring-hom compatibility of
  `normEDS`; the project forks this file, so it is already available).
- `MvPolynomial.aeval_X` — `Mathlib/Algebra/MvPolynomial/Basic.lean` (`aeval g (X i) = g i`).

Composition sketch (≤3 lines) — i.e. the verbatim proof:
```lean
-- with `universalNormEDS := normEDS (X B) (X C) (X D)` available locally:
example : normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) := by
  simp_rw [universalNormEDS, map_normEDS, aeval_X]
```

Call sites in this project (from Phase 6.0): **K = 2** (NagellLutz lines 1212, 1466), plus a full
**duplicate** of the lemma + `universalNormEDS` in HasseWeil (line 641, 6 uses there).

Refactor plan:
1. **Do not upstream `normEDS_eq_aeval` as a standalone mathlib lemma.** It is glue over
   `map_normEDS` + `aeval_X`.
2. **Within AINTLIB (cleanup, not mathlib):** the lemma is genuinely useful *local* infrastructure and
   is fine to keep as-is in NagellLutz — but it is **duplicated** with HasseWeil's identical
   `normEDS_eq_aeval` (+ `universalNormEDS` + `Param`). File an AINTLIB dedup ticket to lift the shared
   `Param` / `universalNormEDS` / `normEDS_eq_aeval` cluster into a `Common/` module imported by both
   projects (this is AINTLIB hygiene, orthogonal to the mathlib question).
3. **If the universal-EDS device is later proposed for mathlib at all**, it must go in as the whole
   *named scaffolding* (universal object + its non-vanishing API), evaluated as its own (larger)
   design decision — not as this single composition lemma. At that point `normEDS_eq_aeval` would be
   the trivial `aeval`-specialisation lemma accompanying that object, still proved in one line.

**Next action:** keep `normEDS_eq_aeval` as local AINTLIB infrastructure; do **not** open a mathlib PR
for it. Open an AINTLIB cleanup/dedup ticket to merge the duplicated NagellLutz⇄HasseWeil
`Param`/`universalNormEDS`/`normEDS_eq_aeval` cluster into `Common/`. Where a mathlib contribution is
genuinely wanted, target the *missing reduce-to-integral-domain EDS API* in mathlib's EDS file as a
separate, larger design proposal — not this 2-lemma composition.
