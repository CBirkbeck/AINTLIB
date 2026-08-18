# `/mathlibable` report — `PadicLFunctions.Coleman.FglobalPlus_le_Fglobal`

**Final verdict: `NO-composable-from-mathlib`.**

This is a Mode A run (single declaration, full 10-phase workflow, exhaustive
9-channel literature search).

---

### Baseline (Phase 0)
- lake build:               not re-run; reasoned from source (per task BUILD NOTE — the file is sorry-free and the proof body elaborates against the mathlib API confirmed in Phase 5).
- decl `PadicLFunctions.Coleman.FglobalPlus_le_Fglobal`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:50`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Cyclotomic units: the global modules 𝒟_n and their local closures 𝒞 (RJW §11.3)" — sets up the global cyclotomic tower `F_n = ℚ(μ_{p^n})`, its maximal real subfield `F_n⁺`, the global units, and the cyclotomic units, all inside `ℂ_[p]`.

---

### Statement (Phase 1)

`PadicLFunctions.Coleman.FglobalPlus_le_Fglobal` is **a theorem** stating the following:

For a prime `p` and `n : ℕ`, the maximal real subfield of the `p^n`-cyclotomic
field is contained in the full cyclotomic field. Concretely, with `ξ = ξ_{p^n} =
zetaSys p n` a fixed primitive `p^n`-th root of unity in `ℂ_[p]`:

> `ℚ(ξ + ξ⁻¹) ⊆ ℚ(ξ)`   as intermediate fields of `ℂ_[p]/ℚ`.

This is the (trivial, "⊆") half of the classical identity `ℚ(ζ_n)⁺ = ℚ(ζ_n +
ζ_n⁻¹) ⊆ ℚ(ζ_n)`, where `ℚ(ζ_n)⁺` is the maximal totally real subfield. The
proof is the one-step observation that the generator `ξ + ξ⁻¹` of the smaller
field lies in the larger field `ℚ(ξ)` (because `ξ ∈ ℚ(ξ)` and `ℚ(ξ)` is a field,
so `ξ⁻¹ ∈ ℚ(ξ)` and `ξ + ξ⁻¹ ∈ ℚ(ξ)`).

Variables / typeclasses involved (Lean side):
- `(p : ℕ)`, `[hp : Fact p.Prime]` — a fixed prime (section variables).
- `(n : ℕ)` — the level of the cyclotomic tower.
- `zetaSys p n : ℂ_[p]` — a fixed primitive `p^n`-th root of unity (from
  `Coleman/Tower.lean:86`; `zetaSys_primitiveRoot` certifies
  `IsPrimitiveRoot (zetaSys p n) (p^n)`).

Hypotheses (Lean side):
- none beyond the section parameters.

Conclusion (math): `ℚ(ξ_{p^n} + ξ_{p^n}⁻¹) ⊆ ℚ(ξ_{p^n})` as subfields of `ℂ_[p]`.

Conclusion (Lean): `FglobalPlus p n ≤ Fglobal p n`, i.e.
`(ℚ⟮zetaSys p n + (zetaSys p n)⁻¹⟯ : IntermediateField ℚ ℂ_[p]) ≤ ℚ⟮zetaSys p n⟯`.

Proof body (4 lines):
```lean
rw [FglobalPlus, IntermediateField.adjoin_simple_le_iff]
exact add_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
  ((Fglobal p n).inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _))
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step containment helper between two `IntermediateField` defs of
the same file; not a `## Main results` item, not named after a person/place, not
a new structure. The file's milestone (`cyclo_mem_cycloTower1`) is elsewhere;
this is plumbing feeding the Galois-action lemmas in `IwasawaProof/Generators.lean`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the
report's framing only.)

### One-line check (Phase 2b)

Body line count: ~3 substantive lines (one `rw`, one `exact` over two lines).
One-liner verdict: **n/a — kind is `lemma`, not a `def`.**

The Phase-2b def-exemption machinery does not apply to theorems/lemmas. Recorded
and skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "maximal real subfield cyclotomic field Q(zeta + zeta inverse) contained in Q(zeta)"                    | yes  | `ℚ(ζ_n)⁺ = ℚ(ζ_n + ζ_n⁻¹) ⊆ ℚ(ζ_n)`, `[ℚ(ζ_n):ℚ(ζ_n)⁺]=2` | Erickson notes, yutsumura, LTCC ANT notes; textbook |
|  2 | WebSearch (general form)         | "maximal totally real subfield Q(zeta_n)^+ = Q(zeta_n + zeta_n^{-1}) Washington cyclotomic fields"      | yes  | same; `[ℚ(ζ_m)⁺:ℚ]=φ(m)/2`; `𝓞 = ℤ[ζ+ζ⁻¹]` | This is Washington, *Intro to Cyclotomic Fields*, §2 — the canonical reference RJW itself cites |
|  3 | WebSearch (named-after / aliases)| "Q(2cos(2pi/n)) real cyclotomic field subfield index 2 Galois complex conjugation fixed field"          | yes  | `ℚ(2cos(2π/n)) = ℝ ∩ ℚ(ζ_n)`; real subfield = fixed field of complex conjugation; index 2 | Keith Conrad, Stanford 210B, arXiv:1210.1018 — confirms the generator and the index-2 / conjugation description |
|  4 | ChatGPT MCP                      | (would ask: standard form, generality, historical evolution of "maximal real subfield of a cyclotomic field") | n/a  | —                                | **n/a — ChatGPT MCP not configured in this environment** (`~/.claude` has no chatgpt/openai server). Channels 1–3 + nLab + textbook refs already give an unambiguous, redundant answer, so the MCP cross-check is not load-bearing here. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "real subfield" / RJW                                           | n/a  | —                                | **n/a — no `references/` dir for this project and no `refs/` store on this machine.** The source paper is RJW arXiv:2309.15692 (cited inline at TeX 2471/2475); the lemma is RJW's `F_n⁺` definition, whose containment in `F_n` is implicit/standard. |
|  6 | nLab                             | "cyclotomic field" → maximal real subfield                                                              | no   | —                                | nLab's `cyclotomic field` page only gives the bare definition `𝔽(ζ_n)`; no totally-real-subfield discussion. (Recorded as a genuine miss, not n/a.) |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | n/a — not a categorical concept (an explicit subfield containment of number fields). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | n/a — not a scheme-theoretic / algebraic-geometry concept (elementary field theory of number fields). |
|  9 | MathOverflow / Math.StackExchange| (covered by #1/#3 hits, e.g. yutsumura "Extension Degree of Maximal Real Subfield of Cyclotomic Field") | yes  | `[ℚ(ζ_n):ℚ(ζ_n)⁺]=2`, containment textbook | The exact `⊆` direction is universally treated as immediate ("`ζ+ζ⁻¹` is real, hence in the real subfield, which sits inside `ℚ(ζ)`"). |
| 10 | recent arXiv (last 5 years)      | "maximal real subfield 2^r p^s cyclotomic field" (arXiv:2504.05159; arXiv:2311.16870)                   | yes  | `𝕂_m⁺ = ℚ(ζ_m + ζ_m⁻¹)`, the maximal real subfield, used freely | Current crypto/lattice literature uses `ℚ(ζ_m + ζ_m⁻¹) ⊂ ℚ(ζ_m)` as a known fact without proof — confirms it is folklore, not a citable theorem. |

### Literature summary (Phase 3)

Concept identified as: **the maximal (totally) real subfield of a cyclotomic
field**, `ℚ(ζ_n)⁺ := ℚ(ζ_n + ζ_n⁻¹) = ℚ(2cos(2π/n)) = ℝ ∩ ℚ(ζ_n)`. The lemma is
the containment `ℚ(ζ_n)⁺ ⊆ ℚ(ζ_n)` (here at `ζ = ζ_{p^n}`, inside `ℂ_[p]`).

Sources agree on the standard form: **yes** — unanimously. Every source
(Washington §2, Keith Conrad, Stanford 210B notes, LTCC notes, yutsumura,
multiple arXiv papers) treats `ℚ(ζ_n + ζ_n⁻¹) ⊆ ℚ(ζ_n)` as elementary, with the
deeper content being the *equality* with the real-/conjugation-fixed subfield and
the *index 2* (which this lemma does **not** assert — it asserts only `⊆`).

Most general standard form: for any field `K` containing a root of unity `ζ`,
`K(ζ + ζ⁻¹) ⊆ K(ζ)` — and more generally still, `F⟮g(α)⟯ ⊆ F⟮α⟯` for any rational
expression `g` in `α` over `F`. The lemma's content is *strictly weaker* than even
the cyclotomic standard form (it omits index 2, omits the real/conjugation
characterisation, omits the ring-of-integers statement).

Generality dimensions where the literature varies:
  - **The full statement**: literature standard = `ℚ(ζ_n)⁺ = ℚ(ζ_n+ζ_n⁻¹)` *with*
    `[ℚ(ζ_n):ℚ(ζ_n)⁺] = 2` and `ℚ(ζ_n)⁺ = ℝ∩ℚ(ζ_n)`. This lemma = only the `⊆`
    half of the (already trivial) generation-containment.
  - **Base field**: literature uses `ℚ`; the containment itself is purely
    formal and holds over any base field with the root of unity present.
  - **The generator**: literature uses `ζ + ζ⁻¹ = 2cos(2π/n)`; identical here.

Disagreement with the literature: **none.** The Lean statement is a (much weaker)
special case of a unanimously-standard fact.

---

### Generality analysis — `PadicLFunctions.Coleman.FglobalPlus_le_Fglobal`

Literature-standard form (from Phase 3): `ℚ(ζ_n)⁺ = ℚ(ζ_n + ζ_n⁻¹) ⊆ ℚ(ζ_n)`,
with the substantive content being the index-2 equality and the
real/conjugation characterisation. The pure containment is folklore.

| # | Parameter / hypothesis            | Current Lean form                 | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-----------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `(p : ℕ)`, `[Fact p.Prime]`       | a fixed prime                     | any `n` (general cyclotomic level)        | yes (irrelevant)    | the containment uses nothing about `p` being prime or about cyclotomy at all — see #4 |
| 2 | `(n : ℕ)`                          | tower level                       | any modulus                               | yes (irrelevant)    | only `zetaSys p n` matters, and only as "some element" |
| 3 | ambient field `ℂ_[p]`             | `ℂ_[p]`                           | `ℚ` (or any field with the root)          | yes                 | the proof never touches the `p`-adic structure; works over any field |
| 4 | the element `ξ = zetaSys p n`     | a primitive `p^n`-th root of unity | a root of unity                          | **yes — fully**     | the proof uses **only** that `ξ` lies in `ℚ⟮ξ⟯` (true by definition) and that fields are inverse-closed. It uses *nothing* about `ξ` being a root of unity, primitive, or cyclotomic. The true content is the field-theory generality `F⟮α + α⁻¹⟯ ≤ F⟮α⟯` for **any** `α` in **any** field extension. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in a way that is
*decisive for the NO verdict, not for YES-but-generalise*. The maximally general
true statement the proof supports is the bare field-theoretic fact

```lean
example {F E : Type*} [Field F] [Field E] [Algebra F E] (α : E) :
    F⟮α + α⁻¹⟯ ≤ F⟮α⟯ :=
  IntermediateField.adjoin_simple_le_iff.mpr
    (add_mem (IntermediateField.mem_adjoin_simple_self F α)
      ((F⟮α⟯).inv_mem (IntermediateField.mem_adjoin_simple_self F α)))
```

Number of weakening opportunities found: 4 (all four parameters are inert — the
result has nothing to do with primes, levels, `ℂ_[p]`, or roots of unity).

Proposed restatement: as above (`F⟮α + α⁻¹⟯ ≤ F⟮α⟯`). Cost of restatement:
**CHEAP** — the *same three mathlib calls* prove the fully general form verbatim.

Crucially, the fully general form is **itself a ≤3-call composition of mathlib
primitives** (see Phase 6), so the generalisation does not rescue this into a
"worth-adding" lemma — it confirms the opposite: the content is so thin that even
its most general form is one `mpr` + one `add_mem`/`inv_mem`. This is the textbook
NO-composable-from-mathlib situation, *not* YES-but-generalise-first (the
generalise-first bucket is for results that are novel-in-some-form; this is novel
in no form — it's an instance of basic `IntermediateField` API).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                                | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                                     | no       | —                      | already typeclass-based (`IntermediateField`); nothing to bundle |
|  2 | sequences/metric → filters/topology?                                                                                    | no       | —                      | no analytic content; pure field theory |
|  3 | construct an object where a universal-property class would characterise it?                                             | no       | —                      | `IntermediateField` adjoin already *is* the universal (Galois-connection) object; `adjoin_simple_le_iff` is exactly its UP |
|  4 | set-with-closure-predicate → bundled substructure?                                                                      | no       | —                      | already a bundled `IntermediateField` |
|  5 | vector-space/metric/field-specific → modules/pseudometric/(semi)ring?                                                   | no       | —                      | inherently a field statement (uses `inv_mem`) |
|  6 | 1-categorical → higher-categorical?                                                                                     | no       | —                      | not categorical |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive/ordered structures?                                                        | no       | —                      | the "index" `p^n` is already inert; the relevant generalisation (drop cyclotomy entirely, #4 of Phase 4) is the *field* generalisation, captured in 4b, not a modern-idiom move |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The decl is already stated in the contemporary
mathlib idiom (`IntermediateField`, `≤`, `adjoin_simple_le_iff`). There is no
filter-/categorification-/bundling-style improvement to make. The only
"reformulation" is the trivial *field-theoretic generalisation* of Phase 4b,
which is itself a mathlib one-liner — i.e. a composition, not a new lemma.

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `lemma`.** Lemmas introduce no definitional
equalities and no typeclass-search paths. Skipped.

---

### Mathlib search-status: `PadicLFunctions.Coleman.FglobalPlus_le_Fglobal`

[A] Lean-Finder       n/a — Lean-Finder MCP not configured here; substituted with the four local methods below (grep over the pinned mathlib tree at `.lake/packages/mathlib/`, which is authoritative for *this* build).
[B] Loogle            type pattern `IntermediateField.adjoin _ {_ + _⁻¹} ≤ IntermediateField.adjoin _ {_}` / `F⟮?a + ?a⁻¹⟯ ≤ F⟮?a⟯`   no hits (Loogle MCP not available; reasoned from the grep over the adjoin files — no lemma of this shape exists, see [D])
[C] LeanSearch        "maximal real subfield of cyclotomic field is contained in the cyclotomic field" / "Q(zeta + zeta inverse) subset Q(zeta)"   no hits (no MCP; the concept maps onto mathlib only via the abstract `maximalRealSubfield`/CMField machinery, see [D], which is a *different* formulation)
[D] Grep mathlib src  terms: `adjoin_simple_le_iff`, `mem_adjoin_simple_self`, `F⟮.*⟯ ≤ F⟮`, `zeta.*\+.*inv`, `maximalRealSubfield`, `totallyReal.*cyclotomic`   building blocks found; exact form **not** found (details below)
[E] Name pattern      `FglobalPlus_le_Fglobal`, `*_le_*` adjoin-containment names, `real*subfield*le*`   no hits in mathlib (this name is project-local; mathlib has no `_le_` lemma packaging `ℚ⟮ζ+ζ⁻¹⟯ ≤ ℚ⟮ζ⟯`)

Building blocks found in mathlib (the pinned tree):
- `IntermediateField.adjoin_simple_le_iff`
  — `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:583`:
  `F⟮α⟯ ≤ K ↔ α ∈ K` (proved `by simp`). This is the Galois-connection step.
- `IntermediateField.mem_adjoin_simple_self`
  — `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:554`: `α ∈ F⟮α⟯`.
- `IntermediateField.inv_mem` / `add_mem`
  — `Mathlib/FieldTheory/IntermediateField/Basic.lean` (SubfieldClass instance,
  lines ~52/77/85): an `IntermediateField` is closed under `+` and `⁻¹`.

What mathlib does **not** have:
- No lemma of the exact shape `F⟮α + α⁻¹⟯ ≤ F⟮α⟯` (the grep `F⟮.*⟯ ≤ F⟮` over
  all of `Mathlib/FieldTheory/` returns nothing).
- The *abstract* "maximal real subfield" lives at
  `Mathlib/NumberTheory/NumberField/CMField.lean` as `maximalRealSubfield K`
  (`Subfield K`, defined via the fixed field of complex conjugation in a CM
  field), with `IsTotallyReal.le_maximalRealSubfield` and
  `eq_maximalRealSubfield` (CMField.lean:458). That is a **different
  formulation** (fixed-field / CM-type, not the two-generator adjoin `ℚ⟮ξ+ξ⁻¹⟯`),
  it requires a `IsCMField`/`NumberField` setup over a number field, and it does
  **not** specialise to this `ℂ_[p]`-internal containment in ≤1 line. So this is
  *not* `NO-mathlib-has-it`.

Searched for both:
  - the user's current form (`ℚ⟮ξ+ξ⁻¹⟯ ≤ ℚ⟮ξ⟯` in `ℂ_[p]`) — not present;
  - the literature-standard / fully-general field form (`F⟮α+α⁻¹⟯ ≤ F⟮α⟯`) — not
    present as a named lemma, but its proof is the three building blocks above.

Concluded: **"found building blocks (`IntermediateField.adjoin_simple_le_iff`,
`IntermediateField.mem_adjoin_simple_self`, `IntermediateField.inv_mem`/`add_mem`);
composition would yield our form"** — all four local methods exhausted, plus the
fully-general field form.

---

### Call sites — `PadicLFunctions.Coleman.FglobalPlus_le_Fglobal`

Internal use count: **2** (within the same project, NOT counting the declaring file)
External-to-file callers: **1 distinct file** (`IwasawaProof/Generators.lean`)

| Caller file:line                              | Usage pattern (one-line excerpt)                                  |
|-----------------------------------------------|-------------------------------------------------------------------|
| `IwasawaProof/Generators.lean:373`            | `fun hy => Fglobal_le_K p (FglobalPlus_le_Fglobal p n hy)`         |
| `IwasawaProof/Generators.lean:444`            | `Fglobal_le_K p (FglobalPlus_le_Fglobal p n hmem)`                 |

Both uses are the *same idiom*: take `x ∈ FglobalPlus p n`, push it to
`x ∈ Fglobal p n` via this lemma, then chain `Fglobal_le_K` to land in `K p n`.
In both call sites the lemma is applied directly to a membership hypothesis (it is
used as the coercion `FglobalPlus p n ≤ Fglobal p n` applied to a point).

Inline-derivation grep (was the equivalent re-derived elsewhere without using the
lemma?): **(none)** — the only places that need `FglobalPlus ⊆ Fglobal` route
through this lemma; there is no competing inline `adjoin_simple_le_iff` derivation.

Call-sites signal: **K = 2 internal uses, identical idiom, no inline
re-derivation.** Per the Phase 6.0 table this is a "K=2/K=1-ish, possibly the
wrong abstraction — could be inlined" pattern: a thin wrapper with a small number
of homogeneous call sites and a one-liner body. It leans NO-composable. (It is
*not* a K≥3, broadly-depended-upon API; the two uses are adjacent reality
arguments in a single file.)

---

### Composition check (Phase 6)

Can `FglobalPlus_le_Fglobal` be derived from mathlib in ≤3 chained calls? **Yes —
and the project's own proof body already *is* that composition.**

Attempt 1 (the existing 3-call proof, verbatim):
```lean
example (n : ℕ) : FglobalPlus p n ≤ Fglobal p n :=
  IntermediateField.adjoin_simple_le_iff.mpr
    (add_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
      ((Fglobal p n).inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _)))
```
  - Mathlib decls used: `IntermediateField.adjoin_simple_le_iff`,
    `IntermediateField.mem_adjoin_simple_self` (×2), `IntermediateField.inv_mem`,
    `add_mem`.
  - Result: **succeeds** — this is exactly the source proof (the source uses
    `rw [FglobalPlus, adjoin_simple_le_iff]` then the same `add_mem`/`inv_mem`
    term; `FglobalPlus`/`Fglobal` are defeq to the `ℚ⟮…⟯` adjoins, so the term
    above type-checks directly).
  - Notes: one Galois-connection `mpr` + one field-membership `add_mem` whose two
    arguments are `mem_adjoin_simple_self` and `inv_mem (mem_adjoin_simple_self)`.
    Per the Phase-6 heuristics table this is the `Foo.bar (Bar.baz hx)` /
    `Foo.bar.mpr (closure facts)` shape — a genuine **composition**, not a proof
    in disguise: no `rw [...]; ring_nf; aesop`, no chain of `have`s with
    reasoning between them.

Conclusion: **COMPOSABLE** (≤3 mathlib calls; the sketch is the source proof
itself, modulo the two `rw`-unfoldings of the defeq `FglobalPlus`/`Fglobal`
names).

---

## Verdict: `PadicLFunctions.Coleman.FglobalPlus_le_Fglobal`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the maximal real subfield `ℚ(ζ_n)⁺ = ℚ(ζ_n+ζ_n⁻¹)`
  and its containment in `ℚ(ζ_n)` is unanimously textbook (Washington §2, Keith
  Conrad, Stanford 210B, LTCC, yutsumura, arXiv:2504.05159 / 2311.16870). The
  substantive content (index 2, real/conjugation characterisation) is *not* what
  this lemma states; the lemma is only the trivial `⊆` half.
- Generality analysis (Phase 4): STRICTLY NARROWER — all four parameters
  (`p` prime, level `n`, `ℂ_[p]`, root-of-unity-ness) are inert; the true content
  is the bare field fact `F⟮α+α⁻¹⟯ ≤ F⟮α⟯`, itself a mathlib one-liner. Modern-idiom
  check: no improvement (already idiomatic). This pushes toward NO, not toward
  YES-but-generalise (the general form is *also* a composition, not a novel lemma).
- Mathlib search (Phase 5): found building blocks
  (`IntermediateField.adjoin_simple_le_iff`, `mem_adjoin_simple_self`,
  `inv_mem`/`add_mem`); the exact form is absent; the abstract `maximalRealSubfield`
  (CMField.lean) is a different, heavier formulation that does **not** specialise
  here in ≤1 line — so NOT `NO-mathlib-has-it`.
- Composition check (Phase 6): **COMPOSABLE** — the source proof *is* a ≤3-call
  mathlib composition.

**Rationale (1–2 paragraphs):**

The mathematical fact (`ℚ(ζ_n)⁺ ⊆ ℚ(ζ_n)`) is genuinely classical, but the part
mathlib would actually want — the *equality* with the totally-real / complex-
conjugation-fixed subfield and the index-2 statement — is exactly what this lemma
does **not** prove. What it does prove is the one-step generation containment
"`ζ + ζ⁻¹` lies in `ℚ(ζ)`", which uses nothing cyclotomic, nothing `p`-adic, and
nothing about roots of unity: it is an instance of the universal property of
simple adjunction (`adjoin_simple_le_iff`) combined with a field being closed under
`+` and `⁻¹`. Mathlib already exposes precisely those primitives, and the project's
own four-line proof is itself the ≤3-call composition of them. There is no API gap:
the building blocks exist, compose trivially, and even the maximally-general true
statement `F⟮α+α⁻¹⟯ ≤ F⟮α⟯` is a one-liner of the same three calls — so generalising
would not turn this into a contribution (it would just be a one-line restatement of
basic `IntermediateField` API, which mathlib does not collect as standalone lemmas).

Note this is deliberately **not** `NO-mathlib-has-it`: mathlib's
`maximalRealSubfield`/`IsCMField` machinery (`Mathlib/NumberTheory/NumberField/
CMField.lean`) is a different formulation (fixed field of complex conjugation in a
CM number field, as a `Subfield K`), it requires a number-field/CM setup the
project does not have here over `ℂ_[p]`, and it does not specialise to this
two-generator adjoin containment in one line. The honest classification is
"mathlib has the *building blocks*, not the packaged form, and the form is a
1-3-call composition" — i.e. `NO-composable-from-mathlib`.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the lemma is a 1-3 mathlib-call composition that
should be inlined at its (two) call sites rather than shipped as a lemma.

Mathlib building blocks:
- `IntermediateField.adjoin_simple_le_iff`
  — `.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:583`
- `IntermediateField.mem_adjoin_simple_self`
  — `.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:554`
- `IntermediateField.inv_mem` / `add_mem` (SubfieldClass)
  — `.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Basic.lean` (~52/77/85)

Composition sketch (≤3 lines — the existing proof body):
```lean
-- proof of `FglobalPlus p n ≤ Fglobal p n`, inlined:
IntermediateField.adjoin_simple_le_iff.mpr
  (add_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
    ((Fglobal p n).inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _)))
```

Call sites in our project (from Phase 6.0): **K = 2**, both in
`projects/PadicLFunctions/PadicLFunctions/IwasawaProof/Generators.lean`
(lines 373 and 444), both of the form `Fglobal_le_K p (FglobalPlus_le_Fglobal p n hmem)`.

Refactor plan:
- **Mathlib-PR decision: do NOT propose this for mathlib.** It is not a standalone
  lemma mathlib collects; it is `adjoin_simple_le_iff.mpr (add_mem … (inv_mem …))`.
- **Project-local decision (optional, for the cleaner, not required):** this is a
  judgment call about *intra-project* hygiene, not a mathlib question. Two
  reasonable options:
  1. *Keep it as a project-local helper.* With K=2 homogeneous call sites and a
     readable name, a 4-line named lemma is a perfectly fine local convenience —
     deleting it would duplicate the three-call term at both sites and slightly
     hurt readability. If kept, no mathlib action; leave as-is.
  2. *Inline it.* At `Generators.lean:373` and `:444`, replace
     `FglobalPlus_le_Fglobal p n h` with the composition above applied to `h`
     (i.e. `(adjoin_simple_le_iff.mpr (add_mem (mem_adjoin_simple_self ℚ _)
     ((Fglobal p n).inv_mem (mem_adjoin_simple_self ℚ _)))) h`), then delete the
     lemma. Verify the two sites still elaborate (they will: the term has type
     `FglobalPlus p n ≤ Fglobal p n`, applied to the membership hypothesis).

Next action (for the mathlib question this skill answers): **do not upstream.**
The lemma is composable from existing mathlib `IntermediateField` primitives; if
desired, inline at the 2 call sites per option 2 above — but this is a local
style choice (cleanup-lane territory), not a mathlib contribution.

---

## Next step

Do **not** open a mathlib PR. `FglobalPlus_le_Fglobal` is a ≤3-call composition of
existing mathlib `IntermediateField` primitives
(`IntermediateField.adjoin_simple_le_iff` + `add_mem`/`inv_mem` +
`mem_adjoin_simple_self`); mathlib does not collect such one-line adjoin
containments as standalone lemmas, and the abstract `maximalRealSubfield`
(CMField.lean) is a different, heavier formulation that does not specialise here.
The lemma may stay as a project-local convenience (K=2 call sites,
`IwasawaProof/Generators.lean:373,444`) or be inlined with the composition sketch
above — a local cleanup-lane decision, not a mathlib one.
