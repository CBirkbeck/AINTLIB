# `/mathlibable` report — `PadicLFunctions._root_.IsPrimitiveRoot.norm_pow_sub_one_eq_one`

**Final verdict: `YES-but-generalise-first`** (reason: LITERATURE-WEAKENING — the
hypothesis cluster `[NormedAlgebra ℚ_[p] L]` is strictly narrower than the
literature-standard "non-archimedean field whose residue characteristic does not
divide the order of the root").

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task instruction — read decl + dependencies directly)
- decl `IsPrimitiveRoot.norm_pow_sub_one_eq_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:211` (declared with `_root_.` into the `IsPrimitiveRoot` namespace)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) of a nonarchimedean complete normed `ℚ_[p]`-algebra field `L`, and norm facts about roots of unity in it.

---

### Statement (Phase 1)

`IsPrimitiveRoot.norm_pow_sub_one_eq_one` is a **theorem** stating the following:

Let `L` be a field that is a complete, non-archimedean (ultrametric) normed
`ℚ_p`-algebra, and let `ζ ∈ L` be a primitive `D`-th root of unity. If the
residue characteristic `p` does not divide `D`, and the exponent `c` is not a
multiple of `D` (so that `ζ^c ≠ 1`), then the analytic absolute value of
`ζ^c − 1` equals `1`. Equivalently: in the tame regime `p ∤ D`, every non-trivial
power difference `ζ^c − 1` is a unit of the valuation ring `𝒪_L` (norm exactly 1,
neither `< 1` nor `> 1`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L : Type*`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]` — `L` is a non-archimedean normed field over `ℚ_p`. (`[CompleteSpace L]` is in the section `variable`s but **omitted** for this theorem via `omit [CompleteSpace L]`.)
- `ζ : L`, `D : ℕ`, `c : ℕ` — the root of unity, its order, and the exponent.

Hypotheses (Lean side):
- `hζ : IsPrimitiveRoot ζ D` — `ζ` is a primitive `D`-th root of unity.
- `hD : ¬ (p : ℕ) ∣ D` — tameness: `p` does not divide the order `D`.
- `hc : ¬ D ∣ c` — `c` is not a multiple of `D`, i.e. `ζ^c ≠ 1`.

Conclusion (math): `|ζ^c − 1|_p = 1`; equivalently `ζ^c − 1 ∈ 𝒪_L^×`.

Conclusion (Lean): `‖ζ ^ c - 1‖ = 1`.

**Critical disambiguation (carried throughout):** the `‖·‖` here is the **analytic
/ metric norm** of the normed field `L` (the `Norm L` instance, ultrametric), NOT
the algebraic field norm `Algebra.norm K : L → K`. This distinction is the whole
ballgame for the mathlib search — see Phase 5.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a helper lemma (labelled W3 in the project's decomposition) about a
specific element's norm, feeding the "Gauss sum / `ε_D^c − 1` is a unit" steps of
the L-value computation (TeX 1798). It is not a named theorem, not a project main
result, and introduces no new structure. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: ~35 substantive lines (a real proof: peel the cyclotomic product, ultrametric-bound each factor, force equality).
One-liner verdict: **n/a — kind is theorem**, not a `def`. Phase 4.5 is also skipped for the same reason.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic absolute value of zeta^c − 1 root of unity prime to p equals 1 unit" | yes | `|ζ|_p = 1` and prime-to-`p` roots of unity are units (`μ_F'`); `F^× ≅ π^ℤ × μ_F' × U_F^(1)` | confirms prime-to-`p` roots are units of the local field; standard structure theory |
| 2 | WebSearch (general form) | "cyclotomic unit norm 1 − zeta^k p-adic valuation prime to p local field" | yes | local field with primitive `p`-th root has `ν(ξ_p − 1) = e/(p−1)` (the **ramified** case); for prime-to-`p` order, valuation is `0` | distinguishes tame (`p ∤ D`, val 0) from wild (`p | D`, val `>0`) — our lemma is the tame case |
| 3 | WebSearch (named-after / aliases) | "roots of unity of order prime to residue characteristic are unramified Teichmüller units local field" | yes | Teichmüller character `ω : κ^× → U`; prime-to-`p` roots of unity reduce isomorphically onto `κ^×` (the canonical splitting) | this is the *name* for the phenomenon: tame/Teichmüller roots reduce injectively, so `ζ^c` and `1` have distinct nonzero residues whenever `D ∤ c` ⟹ `ζ^c − 1` is a unit |
| 4 | ChatGPT MCP | "standard form + generality + historical evolution of: prime-to-p root of unity has |ζ^c − 1| = 1" | **n/a** | — | ChatGPT MCP not configured in this environment (no tool surfaced; `~/.claude` has only `mcp-needs-auth-cache.json`). Skill explicitly allows WebSearch + nLab/Stacks fallback. Compensated with extra WebSearch + nLab channels. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | **n/a** | (no references dir) | both `refs/` and `.mathlib-quality/references/` absent — recorded as n/a |
| 6 | nLab | WebFetch `ncatlab.org/nlab/show/root+of+unity` | no | page is purely classical (μ_n scheme, Kummer sequence); **no** non-archimedean valuation content | nLab has no local-field norm statement for roots of unity |
| 7 | nCatLab (if categorical) | — | **n/a** | — | not a categorical concept (it is a metric/valuation fact about a specific element); nothing to category-ify |
| 8 | Stacks Project (if alg geom) | concept = norm of root of unity in a non-arch field | **n/a** | — | not an algebraic-geometry / scheme-theoretic statement; Stacks treats DVRs but not this analytic-norm identity per se |
| 9 | MathOverflow / Math.SE | "valuation of 1 − ζ for prime-to-p root of unity" (covered via channel 1–3 result pages, e.g. Snowden / Conrad / Crew LCFT notes, Cambridge Part III Local Fields) | yes | unit-group structure of a local field; `1 − ζ` is a unit iff `ζ`'s order is prime to `p` | lecture-note consensus (Snowden CFT-01, Conrad "tamecomp", Crew LCFT) is uniform |
| 10 | recent arXiv (last 5 years) | "cyclotomic unit norm p-adic valuation"; surfaced arXiv 1109.2860 "Calculation of norms of some special elements of cyclotomic fields", 1901.01957 | yes (background) | norms of `1 − ζ`-type elements computed via the same residue-reduction principle | confirms the result is textbook, not a research frontier; no novel "modern" formulation found |

The protocol passed: WebSearch ran 3 distinct queries at three generality levels
(specific `|ζ^c−1|=1`, general unit-group structure, named-after = Teichmüller);
ChatGPT MCP recorded `n/a` with reason (not configured) and compensated; local
refs `n/a` with reason; nLab checked (no hit); nCatLab/Stacks `n/a` with reasons;
MathOverflow/lecture-notes + arXiv checked (hits, background).

### Literature summary (Phase 3)

Concept identified as: **"prime-to-`p` (tame / Teichmüller) roots of unity are units of the valuation ring; `1 − ζ^k` is a unit when `p` does not divide the order"** — the multiplicative-group structure theory of a non-archimedean local/complete field.

Sources agree on the standard form: **yes.** Every source (Teichmüller-character
notes, Local Fields lecture notes, Coates–Sujatha, the arXiv norm-computation
papers) states the same dichotomy:
- **tame** (`p ∤ D`): `ζ` and all its powers reduce to *distinct nonzero* residue-field elements; hence `ζ^c − 1` reduces to a nonzero residue iff `D ∤ c`, so `|ζ^c − 1| = 1`.
- **wild** (`p | D`): `ζ − 1` is a non-unit, `ν(ζ − 1) > 0` (e.g. `e/(p−1)` for a primitive `p`-th root).

Most general standard form: For a field `K` complete (or just henselian) with
respect to a non-archimedean absolute value, residue characteristic `p`, and `ζ`
a root of unity of order `D` **prime to `p`**: `|ζ^c − 1| = 1` whenever `ζ^c ≠ 1`.
**The literature does not require a `ℚ_p`-algebra structure** — only that the
residue characteristic not divide `D` (and that the absolute value be
non-archimedean / the ring henselian so the residue reduction is faithful on the
prime-to-`p` torsion).

Generality dimensions where the literature varies:
- **base scalars**: the literature states it for *any* non-archimedean field /
  henselian valued field (residue char `p`), not specifically a normed
  `ℚ_p`-algebra. The user's `[NormedAlgebra ℚ_[p] L]` + `[CompleteSpace L]` is a
  proper specialisation of "non-archimedean field with residue char `p`".
- **completeness**: the structural argument needs only henselian-ness (faithful
  residue reduction on prime-to-`p` torsion); the user already `omit`s
  `[CompleteSpace L]`, matching this.

Disagreement with the literature: none in *content*. The user's form is correct
but **stated over a narrower base** (`ℚ_p`-algebra) than the literature standard
(any non-archimedean field of residue characteristic `p`).

---

### Generality analysis — `IsPrimitiveRoot.norm_pow_sub_one_eq_one`

Literature-standard form (from Phase 3): for a non-archimedean field `K` (residue
characteristic `p`), and `ζ` a primitive `D`-th root of unity with `p ∤ D` and
`D ∤ c`: `|ζ^c − 1| = 1`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` | `L` is a normed `ℚ_p`-algebra | any non-archimedean field with residue char `p` | **yes** | the proof uses the `ℚ_p`-algebra structure in only ONE place: `hprodD` rewrites `(D : L)` through `algebraMap ℚ_[p] L` and applies `Padic.norm_natCast_eq_one_iff` to get `|D| = 1` from `p ∤ D`. That step is really "`|D| = 1` because `p ∤ D` and the residue char is `p`" — true in any non-arch field of residue char `p`. The `ℚ_p`-algebra is a convenience for citing `Padic.norm_natCast_eq_one_iff`, not essential. |
| 2 | `[IsUltrametricDist L]` | norm is ultrametric | non-archimedean abs. value | NO (this IS the non-arch hypothesis) | essential — the strong triangle inequality `‖a+b‖ ≤ max‖a‖‖b‖` is used in `hfac` to bound each factor `‖1 − ζ^{k+1}‖ ≤ 1`. Cannot be dropped. |
| 3 | `[NormedField L]` | normed field | valued field (mult. abs value) | borderline | mathlib's `IsUltrametricDist` + `NormedField` is the right packaging; a `Valued`/`MulRingNorm` restatement is possible but is a *re-encoding*, not a weakening. Not pursued (see 4c). |
| 4 | `[CompleteSpace L]` | (already `omit`ted) | henselian | already minimal | the author already removed completeness via `omit [CompleteSpace L]`. Good — matches the literature (no completeness needed). |
| 5 | `(hD : ¬ p ∣ D)` | `p ∤ D` | residue char ∤ order | NO | this is exactly the tameness hypothesis; it is the content. |
| 6 | `(hc : ¬ D ∣ c)` | `D ∤ c` | `ζ^c ≠ 1` | equivalent | `D ∤ c ⟺ ζ^c ≠ 1` for a primitive `D`-th root; current form is the clean arithmetic version. Fine. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **1** (row 1 — the `ℚ_p`-algebra base).

Proposed restatement (literature-standard target): drop `[NormedAlgebra ℚ_[p] L]`
and state for a general non-archimedean normed field whose residue characteristic
does not divide `D`. The cleanest mathlib-idiomatic encoding of "`|n| = 1` because
the residue characteristic does not divide `n`" still needs a hypothesis that
pins the residue characteristic; the honest restatement is therefore one of:

```lean
-- Option A (closest weakening): keep a normed field, replace the ℚ_p-algebra by a
-- direct hypothesis on the norm of natural numbers (this is exactly what the
-- ℚ_p-algebra was buying):
theorem IsPrimitiveRoot.norm_pow_sub_one_eq_one'
    {L : Type*} [NormedField L] [IsUltrametricDist L] {p : ℕ}
    (hnorm : ‖(D : L)‖ = 1)   -- or: a residue-characteristic hypothesis giving this
    {ζ : L} {D : ℕ} (hζ : IsPrimitiveRoot ζ D) {c : ℕ} (hc : ¬ D ∣ c) :
    ‖ζ ^ c - 1‖ = 1 := …
```

Cost of restatement: **CHEAP-to-MODERATE** — the proof body is unchanged except
the single `hprodD` step, which currently produces `‖(D:L)‖ = 1` via the
`ℚ_p`-algebra map + `Padic.norm_natCast_eq_one_iff`; under Option A that becomes
the hypothesis directly. Mechanical.

(Per the skill: cost is **not** a verdict factor. Recorded for sequencing only.)

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let `L` be a foo" preambles → typeclasses? | no | already fully typeclass-driven (`NormedField` + `IsUltrametricDist` + `NormedAlgebra`) | — |
| 2 | sequences/metric → filters/topological? | no | this is a single-element norm identity; no limit/filter content | — |
| 3 | construct an object → universal-property class? | no | it's a statement about an element, not a construction | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | no substructure here (the integer-ring packaging lives elsewhere, `integerRing`) | — |
| 5 | field/metric-specific → weaken typeclass hierarchy (`Valued`/`MulRingNorm`)? | **partially** | could state over `[Valued L Γ]` / via `AbsoluteValue` instead of `NormedField`+`IsUltrametricDist` | minor — would compose with mathlib's `Valued`/`Valuation` API. But mathlib's analytic-norm (`NormedField` + `IsUltrametricDist`) packaging is the established idiom for non-arch *analysis*; this is a re-encoding, not a real organisational win. |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | `D`, `c : ℕ` are orders/exponents — `ℕ` is the natural and correct index for root-of-unity orders | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no *real* organisational improvement).
One-line reason: the only candidate (row 5, re-encode over `Valued`/`AbsoluteValue`
rather than `NormedField`+`IsUltrametricDist`) is a lateral re-encoding, not a
mathematical improvement — mathlib's non-archimedean *analysis* is built on
`NormedField`+`IsUltrametricDist`, so that packaging is already the idiomatic one.
The generalisation that matters (Phase 4b row 1) is a **literature weakening**
of the base scalars, not a modern-idiom reformulation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (introduces no definitional equality or
typeclass-search path). Skipped per the skill's scope rule.

---

### Mathlib search-status: `IsPrimitiveRoot.norm_pow_sub_one_eq_one`

[A] Lean-Finder       MCP not available in env                                  n/a: tool not configured (no Lean-Finder tool surfaced)
[B] Loogle            MCP not available in env                                  n/a: tool not configured — compensated by [D]/[E] grep over the actual pinned mathlib source tree (`.lake/packages/mathlib`)
[C] LeanSearch        MCP not available in env                                  n/a: tool not configured — compensated by [D]/[E]
[D] Grep mathlib src  `norm_pow_sub_one`, `norm_sub_one`, `IsPrimitiveRoot`+`IsUltrametricDist`, `prod_one_sub_pow_eq_order`, analytic `‖ζ‖=1` lemmas  see below
[E] Name pattern      `IsPrimitiveRoot.*norm`, `norm_eq_one_of_pow_eq_one`, `nnnorm_eq_one`  see below

Searched for both:
  - the user's current form (`‖ζ^c − 1‖ = 1`, analytic norm, `p ∤ D` tame regime)
  - the literature-standard form (any non-arch field, residue char ∤ order)

**Findings (grep over the pinned `.lake/packages/mathlib`):**

1. **Closest-by-name mathlib decls are a DIFFERENT object.**
   `IsPrimitiveRoot.norm_pow_sub_one_of_prime_ne_two`
   (`Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:445`) and
   `IsPrimitiveRoot.norm_pow_sub_one_eq_prime_pow_of_ne_zero` (ibid. :505) state
   `Algebra.norm K (ζ ^ p ^ s − 1) = (p : K) ^ p ^ s` — the **algebraic field
   norm** (`norm K`), in the **prime-power** regime (`ζ` a primitive
   `p^(k+1)`-th root), which is the *opposite* (wild) regime from ours (`p ∤ D`),
   and a completely different quantity from the analytic `‖·‖`. **Not a match.**

2. **Analytic `‖·‖`-norm root-of-unity lemmas in mathlib are ℂ-only and about
   `‖ζ‖`, not `‖ζ^c − 1‖`:** `Complex.norm_eq_one_of_pow_eq_one`
   (`Mathlib/Analysis/Complex/Basic.lean:101`),
   `IsPrimitiveRoot.nnnorm_eq_one` (`Mathlib/RingTheory/RootsOfUnity/Complex.lean:136`),
   `Complex.norm_eq_one_of_mem_rootsOfUnity`. All give `‖ζ‖ = 1` over ℂ; none give
   `‖ζ^c − 1‖` in a non-archimedean field. **Not a match.**

3. **No file in mathlib mentions both `IsUltrametricDist` and `IsPrimitiveRoot`**
   (grep `IsUltrametricDist`-files ∩ `IsPrimitiveRoot`-files = ∅). So mathlib has
   **zero** results about the *ultrametric* norm of roots of unity.

4. **Building blocks DO exist** (and the proof uses them):
   `IsPrimitiveRoot.prod_one_sub_pow_eq_order`
   (`Mathlib/RingTheory/RootsOfUnity/Lemmas.lean:33`, `∏_{k<n}(1 − μ^{k+1}) = n+1`),
   `Padic.norm_natCast_eq_one_iff` (`Mathlib/NumberTheory/Padics/PadicNumbers.lean:955`),
   `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`.

Concluded: **not in mathlib** (all available methods exhausted — grep over the
pinned mathlib source, plus the literature-standard form — and the LeanSearch /
Loogle / Lean-Finder MCP tools recorded `n/a` as unavailable in this environment,
compensated by source grep). The name-collision decls (`norm_pow_sub_one_*`) are
the **algebraic field norm in the prime-power regime** and are a different theorem;
the analytic-norm statement for prime-to-`p` roots is absent.

---

### Call sites — `IsPrimitiveRoot.norm_pow_sub_one_eq_one`

Internal use count: **4** (within the PadicLFunctions project, NOT counting the declaring file `Coefficients.lean`)
External-to-file callers: **2 distinct files**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `ValuesAtOne.lean:70` | `exact hε.norm_pow_sub_one_eq_one (p := p) hD hc` (dot notation) |
| `ValuesAtOne.lean:122` | `exact hεD.norm_pow_sub_one_eq_one (p := p) hD hDc` (inside the wrapper `norm_pow_sub_one_eq_one_of_unit`) |
| `Interpolation/NonTame.lean:50` | `simpa using hζK.norm_pow_sub_one_eq_one (p := p) hD hc` — proves a `PowerSeries` unit via `integerRing.isUnit_of_norm_eq_one` |
| `Interpolation/NonTame.lean:118` | `have h1 : ‖(ζ : K) ^ c − 1‖ = 1 := hζK.norm_pow_sub_one_eq_one (p := p) hD hc` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — every site that needs `‖ζ^c − 1‖ = 1` calls this lemma. No bypassing re-derivation found.

**Signal:** K = 4 internal uses across 2 files, dot-notation, no inline
re-derivation ⟹ this is a **real API surface**, consumers depend on it. Per the
call-sites table this leans firmly toward a **YES-** bucket (not NO-composable /
not dead code).

### Composition check (Phase 6)

Can `IsPrimitiveRoot.norm_pow_sub_one_eq_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: chain `prod_one_sub_pow_eq_order` with `Padic.norm_natCast_eq_one_iff`.
  - Mathlib decls used: `IsPrimitiveRoot.prod_one_sub_pow_eq_order`, `Padic.norm_natCast_eq_one_iff`, `IsUltrametricDist.norm_add_le_max`.
  - Result: **fails as a ≤3-call composition.** These give "`∏(1−ζ^{k+1})` has norm 1" and "each factor has norm `≤ 1`", but turning "product of factors-of-norm-≤1 has norm 1" into "*each* factor has norm exactly 1" requires the multiplicative `norm_prod` split plus an `le_antisymm` + `nlinarith` argument over the partial product (the `hone` block: `Finset.mul_prod_erase`, `Finset.prod_le_one`, `Finset.prod_nonneg`, then `nlinarith`). That is a genuine 10+ line sub-proof, not a `.trans`/`.symm`/one-call chain.
  - Notes: also requires the mod-`D` exponent reduction (`hred`/`hr`) to land on a factor index — another non-trivial step.

Attempt 2 (different angle): residue-field reduction (`ζ^c` and `1` have distinct nonzero residues ⟹ difference is a unit ⟹ norm 1).
  - Mathlib decls used: would need a faithful residue-reduction-on-prime-to-`p`-torsion lemma.
  - Result: **fails** — mathlib has no packaged "prime-to-`p` root of unity is a unit / has unit power-differences" lemma in the non-archimedean setting (Phase 5 finding #3: no `IsUltrametricDist` ∩ `IsPrimitiveRoot` result at all). There is no building block to compose.

Conclusion: **NOT-COMPOSABLE.** The result is a real ~35-line proof assembling
several mathlib primitives with genuine reasoning (multiplicative norm split +
ultrametric bound + antisymmetry + exponent reduction), well past the 3-call /
no-real-rewriting bar in the Phase 6 heuristics table.

---

## Verdict: `IsPrimitiveRoot.norm_pow_sub_one_eq_one`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the result is the **textbook** tame-roots-of-unity / Teichmüller fact ("prime-to-`p` root of unity ⟹ `ζ^c − 1` is a unit, `|ζ^c − 1| = 1`"); the literature states it for **any** non-archimedean field of residue characteristic `p`, not specifically a `ℚ_p`-algebra. ≥3 channels confirm a single agreed standard form.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — exactly one weakening (row 1: `[NormedAlgebra ℚ_[p] L]` → a general non-archimedean field with residue char `p` / a direct `‖(D:L)‖ = 1` hypothesis). Modern-idiom check (4c): no real modernisation move.
- Mathlib search (Phase 5): **not in mathlib.** Name-collisions (`IsPrimitiveRoot.norm_pow_sub_one_*`) are the *algebraic field norm* in the *prime-power* (wild) regime — a different theorem. Analytic-norm root-of-unity lemmas in mathlib are ℂ-only and about `‖ζ‖`. No mathlib file pairs `IsUltrametricDist` with `IsPrimitiveRoot`.
- Composition check (Phase 6): **NOT-COMPOSABLE** (genuine ~35-line proof; K = 4 real call sites across 2 files, no inline re-derivation).

**Rationale (1–2 paragraphs):**

The statement is genuinely missing from mathlib *in any form*: mathlib has no
result about the **ultrametric/analytic** norm of a root of unity beyond the
complex case `‖ζ‖ = 1`, and nothing at all about `‖ζ^c − 1‖` in a non-archimedean
field — the grep confirms `IsUltrametricDist` and `IsPrimitiveRoot` never co-occur
in the library. The deceptively-named `IsPrimitiveRoot.norm_pow_sub_one_of_prime_ne_two`
/ `…_eq_prime_pow_of_ne_zero` are about the *algebraic field norm* `Algebra.norm K`
in the *prime-power* (wild-ramification) regime `ζ ∈ μ_{p^{k+1}}`, which is both a
different quantity and the opposite arithmetic regime from this lemma's tame
`p ∤ D`. So this is not `NO-mathlib-has-it`. It is also not
`NO-composable-from-mathlib`: while the building blocks
(`prod_one_sub_pow_eq_order`, `Padic.norm_natCast_eq_one_iff`, the ultrametric
inequalities) all exist, turning them into the per-factor norm-one statement is a
real ~35-line argument (multiplicative `norm_prod` split + `le_antisymm` +
`nlinarith` over the partial product + mod-`D` exponent reduction), far past a
≤3-call composition, and the lemma has four genuine dot-notation call sites across
two downstream files with no bypassing re-derivation — a real API.

Why **generalise first** rather than `YES-add-as-is`: Phase 4b found the form
**strictly narrower than the literature standard**. The `[NormedAlgebra ℚ_[p] L]`
hypothesis is a proper specialisation — the literature (and the proof) need only
that the residue characteristic not divide `D`, which mathlib can express without
fixing the base to a `ℚ_p`-algebra. The `ℚ_p`-algebra is used in exactly one step
(`hprodD`, to get `‖(D:L)‖ = 1` from `p ∤ D` via the scalar embedding +
`Padic.norm_natCast_eq_one_iff`). The skill's gate is explicit: when Phase 4b is
STRICTLY NARROWER, `YES-add-as-is` is rejected and the verdict is
`YES-but-generalise-first`. (Cost of the weakening is CHEAP-to-MODERATE, but per
the skill cost is not a verdict factor.)

**Reason for the generalisation:** LITERATURE-WEAKENING — Phase 4b found the
user's `[NormedAlgebra ℚ_[p] L]` base strictly narrower than the literature-standard
"non-archimedean field whose residue characteristic does not divide the order".
(MODERN-IDIOM does *not* apply — Phase 4c found no real organisational improvement.)

**Proposed restatement:**

```lean
-- Drop the ℚ_p-algebra; require only what the proof actually uses — an ultrametric
-- normed field in which the order D is a norm-unit (i.e. the residue characteristic
-- does not divide D). This is the literature-standard generality.
theorem IsPrimitiveRoot.norm_pow_sub_one_eq_one
    {L : Type*} [NormedField L] [IsUltrametricDist L]
    {ζ : L} {D : ℕ} (hζ : IsPrimitiveRoot ζ D) (hDnorm : ‖(D : L)‖ = 1)
    {c : ℕ} (hc : ¬ D ∣ c) :
    ‖ζ ^ c - 1‖ = 1 := by
  sorry  -- the body is the current proof verbatim, with the single `hprodD` step
         -- replaced by `hDnorm` (no longer routed through `algebraMap ℚ_[p] L` +
         -- `Padic.norm_natCast_eq_one_iff`).
```

Estimated cost of regeneralisation: **CHEAP-to-MODERATE** (mechanical — one step
changes; the ultrametric/product machinery is untouched). Note: EXPENSIVE would
not have downgraded the verdict; this one is cheap.

Mathlib downstream this enables: the weakened form applies to **`ℂ_p`** and to any
non-archimedean field of residue char `p` (e.g. completions, `FiniteAdele`-type
local components) without re-deriving — not only to `ℚ_p`-algebras. The original
project use sites (over `L` and over `K` a `ℚ_p`-algebra) still discharge the new
`‖(D:L)‖ = 1` hypothesis in one line via the existing
`norm_natCast_self_lt_one`/`Padic.norm_natCast_eq_one_iff` route, so no consumer
regresses. A companion convenience wrapper specialised to `[NormedAlgebra ℚ_[p] L]`
(supplying `hDnorm` from `p ∤ D`) can ship alongside if desired.

**Concrete mathlib gap this fills:** mathlib's non-archimedean analysis
(`Mathlib/Analysis/Normed/.../Ultra*`, `IsUltrametricDist`) has **no** root-of-unity
norm API — the only `IsPrimitiveRoot` + norm lemmas are (a) complex-analytic
(`‖ζ‖ = 1` over ℂ) or (b) algebraic field-norm in the cyclotomic prime-power case.
There is a clean, recurring missing fact ("tame roots of unity and their power
differences are norm-1 units in a non-archimedean field") that downstream p-adic
work currently has to prove by hand; this lemma is exactly that canonical form.

Proposed mathlib location: `Mathlib/Analysis/Normed/Ring/Ultra.lean` (or a new
`Mathlib/RingTheory/RootsOfUnity/Ultra.lean`), as `IsUltrametricDist`-API about
roots of unity, *not* under `NumberTheory/Cyclotomic/` (that file is for the
algebraic field-norm). PR grouping: ship alongside `IsPrimitiveRoot.norm_sub_one_lt`
(`Coefficients.lean:151`, the `‖ζ−1‖ < 1` companion in the *wild* `p^n` regime) and
its corollary `IsPrimitiveRoot.tendsto_pow_sub_one` — together they form the
"non-archimedean norms of roots of unity" mini-API and should be assessed/PR'd as
one batch.

Next action: run `/generalise IsPrimitiveRoot.norm_pow_sub_one_eq_one` (it will
tension the weakened form against the literature-standard target from Phase 3),
confirm the body survives with `hprodD` → `hDnorm`, then `/cleanup` the file and
open the mathlib PR (after assessing `norm_sub_one_lt` as the batch companion).

Pre-PR checklist before opening:
- [ ] `/generalise IsPrimitiveRoot.norm_pow_sub_one_eq_one` — confirm the `[NormedAlgebra ℚ_[p] L]` → `‖(D:L)‖ = 1` weakening proves out, and check for any further weakening.
- [ ] Re-discharge the 4 project call sites against the new signature (each supplies `‖(D:L)‖ = 1` in one line).
- [ ] `/cleanup Coefficients.lean` — full audit + diff gates on the generalised statement.
- [ ] Pick a mathlib reviewer from recent `Mathlib/Analysis/Normed/Ring/Ultra.lean` + `Mathlib/RingTheory/RootsOfUnity/` commits.

---

## Next step

Run `/generalise IsPrimitiveRoot.norm_pow_sub_one_eq_one` to restate over a general
non-archimedean normed field (`[NormedField L] [IsUltrametricDist L]` with a
`‖(D:L)‖ = 1` hypothesis in place of `[NormedAlgebra ℚ_[p] L]`), tensioning against
the literature-standard form; assess `IsPrimitiveRoot.norm_sub_one_lt` as the PR
batch companion; then `/cleanup` and open the mathlib PR.
