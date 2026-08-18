# `/mathlibable` report — `PadicLFunctions.ExtLogDomain.mul`

- **Mode:** A (single declaration, full 10-phase workflow, exhaustive 9-channel literature search).
- **Refs:** `--refs=/Users/mcu22seu/.claude/plugins/cache/mathlib-quality-plugins/mathlib-quality/0.50.0/skills/mathlib-quality/references` (read in full: `mathlibable.md`, `mathlibable-verdicts.md`).
- **Final five-bucket verdict: `NO-composable-from-mathlib`.**

---

## Baseline (Phase 0)

- lake build:               build NOT re-run; reasoned from source (per task note — `lake build` is stale/slow in this checkout; the declaration and its full dependency chain were read directly from source: `ExtLog.lean`, `PadicExp.lean`).
- decl `PadicLFunctions.ExtLogDomain.mul`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:386`
- kind:                      theorem
- has sorry:                 no (proof body lines 387–396 contain zero `sorry`)
- module docstring summary:  "The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)" — extends `padicLog` to the rational-valuation domain via `extLog x := m⁻¹·padicLog y` for a witness `x^m = p^k·y`.

---

## Statement (Phase 1)

`PadicLFunctions.ExtLogDomain.mul` is a **theorem** stating the following:

> Let `L` be a complete ultrametric normed field that is a `ℚ_p`-algebra. The **domain of the extended (Iwasawa-branch) p-adic logarithm** — the set of `x ∈ L` of "rational valuation", i.e. those `x` for which there exist `m ∈ ℕ₊`, `k ∈ ℤ` and `y ∈ L` with `xᵐ = pᵏ·y` and `y` a principal unit in the open exponential ball (`‖y−1‖^{p−1} < p⁻¹`) — is **closed under multiplication**: if `x` and `y` both lie in this domain, so does `x·y`.

This is the **multiplicative-closure half** of the standard structural fact that the domain of the p-adic/Iwasawa logarithm is a *multiplicative group* (on which `log_p` is a homomorphism). The proof exhibits the explicit **product witness**: from `xᵐ = pᵏ·a` and `yᵐ' = pᵏ'·b` it builds
`(x·y)^{m·m'} = p^{k·m' + k'·m}·(aᵐ' · bᵐ)`,
with `aᵐ'·bᵐ − 1` again in the exponential ball (closure of the ball under powers and products).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete ultrametric normed `ℚ_p`-algebra field. (`[CompleteSpace L]` is `omit`-ted from this theorem: the closure statement is purely algebraic/normwise and needs no completeness.)
- `{x y : L}` — the two domain elements.

Hypotheses (Lean side):
- `(hx : ExtLogDomain p x)` — `x` is in the extended-log domain (carries a witness `⟨m, k, a, hm, hxy, ha⟩`).
- `(hy : ExtLogDomain p y)` — `y` is in the extended-log domain (carries a witness `⟨m', k', b, hm', hxy', hb⟩`).

Conclusion (math): the extended-log domain is closed under multiplication.

Conclusion (Lean): `ExtLogDomain p (x * y)`.

**Dependency context (project-local subjects of this statement):**
- `ExtLogDomain p x := ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y ∧ InExpBall p (y - 1)` (`ExtLog.lean:278`) — verdict on this parent def is **`NO-composable-from-mathlib`** (see `PadicLFunctions.ExtLogDomain.md`).
- `InExpBall p x := ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹` (`PadicExp.lean:65`) — project-local, verdict `NO-composable-from-mathlib`.
- `padicLog` (`PadicExp.lean:384`) — project-local; **mathlib has no p-adic logarithm at all**.

---

## Size classification (Phase 2a)

Verdict: **SMALL**

Reason: It is a closure/structure helper lemma about a project-local predicate (`ExtLogDomain`), not a named theorem, not a new structure, and not a `## Main results` headline. It is the `mul`-closure companion to `ExtLogDomain.prod` and the engine `extLogDomain_of_integral_norm_one`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

## One-line check (Phase 2b)

Body line count: 10 substantive lines (a genuine multi-step witness construction: destructure both witnesses, build the product witness, discharge the factorisation by `mul_pow`/`pow_mul`/`zpow_add₀`/`ring` and the ball-membership by `mul_mem_expBall (pow_mem_expBall …) (pow_mem_expBall …)`).
One-liner verdict: **n/a — kind is theorem, not def.** The one-liner / defeq / API-anchor exemptions concern `def`s; this is a proof. Skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

The concept under search: **"the domain of the p-adic (Iwasawa-branch) logarithm is closed under multiplication"** — i.e. the *group-structure* fact that the principal units `1+𝔪` (and the Iwasawa extension `p^ℤ·(1+𝔪)` / `C_p^×`) form a multiplicative group on which `log_p` is a homomorphism, transported here to the "rational-valuation" domain over a general field `L`.

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                   | Hit? | Standard form found                                                                                                   | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Iwasawa p-adic logarithm extended to multiplicative group homomorphism domain closed under multiplication"             | yes  | `log_p` extends to a homomorphism on `C_p^×` / `G := p^ℤ·(1+𝔪)`; `1+J` is *closed under multiplication* since `J²⊆J` | MIT 18.785 PS10; Harron AWS 2018; arXiv 1907.06437, 1608.00392. The closure is the structural prerequisite for the homomorphism. |
|  2 | WebSearch (general form)         | "p-adic logarithm domain divisible elements valuation closed under multiplication subgroup C_p"                         | yes  | `𝔾_m(K)_f = {x ∈ K^× : ν(x)=0} = 𝒪_K^×`; `log_{G}` is a `K`-analytic **homomorphism**; domain is an open **subgroup** | arXiv 0711.5028 (Tate-style `G(K)_f`). The domain is *by construction* a group ⇒ closed under `·`. |
|  3 | WebSearch (named-after / aliases)| `"p-adic logarithm" principal units "1 + m" closed under multiplication group homomorphism Washington cyclotomic`        | yes  | principal units `1+𝔪_K` form a group; `log_p : (1+𝔪) → 𝔪` is a group homomorphism                                   | researchgate "On the image of p-adic logarithm on principal units"; Illinois J. Math (irregular cyclotomic units); matches Washington §5.1, the project's cited source. |
|  4 | ChatGPT MCP                      | "standard form + generality + historical evolution of: the domain of the p-adic/Iwasawa log is a multiplicative group" | n/a  | (server not configured)                                                                                              | ChatGPT MCP not installed in this environment (only Asana/Atlassian/etc. proxies present). Substituted with an extra WebSearch channel (#9) at the homomorphism/group-structure level to keep ≥3 distinct generality levels + the structural query. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                                            | n/a  | (no references dir; no `refs/` symlink)                                                                              | `.mathlib-quality/references/` absent and `refs/PadicLFunctions` absent — recorded n/a. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/p-adic+logarithm`; WebSearch "nLab p-adic logarithm Iwasawa homomorphism units"        | n/a  | nLab has **no** dedicated `p-adic logarithm` page (404)                                                              | The Iwasawa log is an analytic/arithmetic object; nLab carries no entry. Recorded n/a with reason. |
|  7 | nCatLab (if categorical)         | (covered by #6)                                                                                                         | n/a  | not a categorical concept                                                                                            | "Closed under multiplication" of an analytic domain has no higher-categorical content. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                                      | n/a  | not an algebraic-geometry concept                                                                                    | The p-adic logarithm / its domain is analytic number theory, not the scheme-theoretic material Stacks covers. |
|  9 | MathOverflow / arXiv (group str.)| "p-adic logarithm" principal units group homomorphism + integral logarithm Iwasawa                                      | yes  | "the p-adic logarithm extends to a continuous **homomorphism from the multiplicative group** … log_p(p)=0"; domain is a group | jtnb "The integral logarithm in Iwasawa theory"; arXiv 0512015 ("A Note on a result of Iwasawa"); arXiv 2601.18187. Unanimous: domain is a multiplicative group ⇒ closed under `·`. |
| 10 | recent arXiv (last 5 years)      | image of p-adic logarithm on annuli of principal units (2026)                                                          | yes  | recent work still treats `1+𝔪_K` as the multiplicative group and `log_p` as the homomorphism on it                  | arXiv 2601.18187 (2026); formulation unchanged from the classical one — no modernisation pressure. |

**Protocol pass check:** WebSearch ran 4 distinct queries at three generality levels (specific Iwasawa form #1, general valuation/subgroup form #2, named-after/principal-units form #3, plus the structural homomorphism query #9). ChatGPT MCP unavailable → recorded `n/a` with reason and substituted an extra structural web channel. Local refs, nLab, nCatLab, Stacks, MathOverflow/arXiv, recent arXiv all checked or `n/a` with reasons. ✓

### Literature summary (Phase 3)

Concept identified as: **"the domain of the p-adic (Iwasawa-branch) logarithm is a multiplicative group"** — equivalently, "the principal units `1+𝔪` (resp. `p^ℤ·(1+𝔪)`, resp. `C_p^×`) are closed under multiplication, and `log_p` is a homomorphism on them". The project's `ExtLogDomain` is the *rational-valuation / divisible-hull* version of this domain over a **general** complete ultrametric `ℚ_p`-algebra field `L`.

Sources agree on the standard form: **yes.** Every source states the domain as a *group* and `log_p` as a *homomorphism*; closure under multiplication is the (weakest, structural) prerequisite and is **never** isolated as a standalone "closed-under-mul" lemma — it is subsumed in "the domain is a subgroup".

Most general standard form: over `C_p` the domain is *all* of `C_p^×` (every nonzero element decomposes as `p^r·ζ·z`), so the closure statement is trivial there. Over a general field `L` (as in this project) the domain is a genuine subset and closure is a real, if elementary, fact: `(x^m)(y^{m'})` patterns multiply, and `1+𝔪` is closed because `𝔪²⊆𝔪`.

Generality dimensions where the literature varies:
- **Underlying field**: `ℚ_p` ⊂ finite extension `K/ℚ_p` ⊂ `C_p`. The project's `L` (general complete ultrametric `ℚ_p`-algebra field) is at least as general as the classical `K`-level statements.
- **How the domain is packaged**: as the subgroup `p^ℤ·(1+𝔪)` (classical) vs. the rational-valuation `∃ m,k,y. xᵐ=pᵏy ∧ …` (this project). These coincide over `C_p`; the existential form is the natural one over a general `L`.

Disagreement with the literature: **none** mathematically. The only "gap" is presentational: the literature carries this as "the domain is a group", **bundled** with the homomorphism property — not as the isolated `mul`-closure lemma the project states.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): the domain of `log_p` is a **multiplicative group** (principal units `1+𝔪`, the Iwasawa group `p^ℤ·(1+𝔪)`, or `C_p^×`); closure under `·` is one of its group axioms.

### 4a. Generality status table — `ExtLogDomain.mul`

| # | Parameter / hypothesis              | Current Lean form                                 | Literature-standard form                          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|---------------------------------------------------|---------------------------------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` | complete ultrametric normed `ℚ_p`-algebra field | finite ext `K/ℚ_p`, or `C_p`                    | NO (already ≥ standard) | The project's `L` is **more general** than the classical `K`/`C_p`. No literature axis asks to weaken further; the ultrametric + `ℚ_p`-algebra structure is exactly what makes the witness factorisation/ball arguments go through. |
| 2 | `(hx hy : ExtLogDomain p ·)`        | the project's rational-valuation predicate        | "x lies in the multiplicative group `p^ℤ·(1+𝔪)`" | n/a — encoding       | This is an **encoding choice tied to the project's `padicLog`/`InExpBall` API**, not a literature generality axis. `ExtLogDomain` is project-local (verdict `NO-composable-from-mathlib`); there is no more-general mathlib form to re-aim at. |
| 3 | conclusion `ExtLogDomain p (x*y)`   | closure under `·`                                  | the domain is a *group* (closed under `·`, `⁻¹`, `1`) | the lit form is STRONGER (full group) | The project states only the `·`-closure leaf; mathlib's idiomatic packaging would be a bundled `Submonoid`/`Subgroup` carrying `mul_mem`. See Phase 4c. |

### 4b. Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (in its field hypotheses — strictly more general than the classical `K`/`C_p` literature; no literature-supported *weakening* of any hypothesis exists).
Number of weakening opportunities found: **0** (there is no hypothesis to weaken; if anything the conclusion is *narrower* than the literature's "is a group", which is a *strengthening/bundling* question handled in 4c, not a weakening).
Proposed restatement: none on weakening grounds.
Cost of restatement: n/a.

Because Phase 4b is MAXIMALLY-GENERAL (no weakening), this is **not** a `YES-but-generalise-first (LITERATURE-WEAKENING)` case. Phase 7 considers YES-add-as-is vs the NO buckets, after 4c.

### 4c. Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | Could "x is in the domain" become a **bundled substructure** (`Submonoid`/`Subgroup`) whose `mul_mem'` field *is* this lemma? | yes (in principle) | `def extLogDomain : Submonoid L := ⟨{x | ExtLogDomain p x}, ExtLogDomain.mul …, ⟨…, …, inExpBall_one_sub_one …⟩⟩` — then this theorem *is* `(extLogDomain p).mul_mem`. | **None in mathlib.** It would compose with mathlib's `Submonoid` lattice/API, but only to organise *project* code: the carrier predicate, the unit `padicLog`/`extLog`, and `InExpBall` are all project-local; mathlib has no p-adic log to consume the bundle. |
|  2 | Sequences → filters/nets/topological notions?                                                            | no       | —                      | Purely algebraic closure (`xᵐ·yᵐ'` factorisation + `𝔪²⊆𝔪`); no sequential/limit content to filter-ise. |
|  3 | Construct an object where a **universal property** would characterise it?                                 | no       | —                      | This is a closure *property* of a predicate, not the construction of an object. |
|  4 | Set-with-closure-predicate → **bundled-substructure** type composing with mathlib's lattices?            | yes      | same as row 1 (the `Submonoid`/`Subgroup` bundle) | The bundle is the *correct mathlib idiom* — but it bundles **project-local** content; the lattice/quotient API it unlocks is exercised only inside this project. Not a mathlib-downstream win. |
|  5 | vector-space/metric/field-specific result that mathlib's typeclass hierarchy would weaken?               | no       | —                      | Already at the general normed-`ℚ_p`-algebra-field level; nothing to weaken to modules/(semi)rings (the `ℚ_p`-algebra + ultrametric structure is essential). |
|  6 | 1-categorical statement with a higher-/∞-categorical generalisation?                                     | no       | —                      | No categorical content. |
|  7 | Concrete index `ℕ/ℤ/ℝ` that would generalise to arbitrary additive groups/monoids?                      | no       | —                      | The `m,k` in the witness are intrinsically `ℕ`/`ℤ` (powers and `p`-valuations); generalising the index is meaningless here. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it bundles project-local content only.** The idiomatic move is to make the extended-log domain a `Submonoid L` (indeed a `Subgroup` once `ExtLogDomain.inv` and `ExtLogDomain.one` are added), so that `ExtLogDomain.mul` *becomes* the `mul_mem'` field. That is genuinely the right mathlib idiom **for the project**.

But this is **not** a `YES-but-generalise-first (MODERN-IDIOM)` case, for the reason the honesty bar demands: the bundling unlocks **no mathlib downstream**. The carrier predicate `ExtLogDomain`, its conclusion clause `InExpBall`, and the function it is the domain *of* (`padicLog`/`extLog`) are **all project-local** (sibling/parent verdicts `NO-composable-from-mathlib`); exhaustive grep of `Mathlib/NumberTheory/Padics/` confirms mathlib carries **no** `padicLog`/`padicExp`. A `Submonoid` bundle whose every ingredient is project-local, and which no mathlib API consumes, is a *project* refactor — exactly the "looks cooler / better organised but no real mathlib downstream" pattern the Phase-7 gate rejects as a basis for a YES verdict. (It is, however, a reasonable *project-internal* cleanup; recorded as such, not as a mathlib upstreaming.)

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities, no typeclass-search paths, no instances/coercions. Skipped per the skill's scope rule.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.ExtLogDomain.mul`

```
[A] Lean-Finder       "p-adic log domain closed under multiplication" / "Iwasawa log domain group"   n/a — tool not wired in this offline env; substituted by exhaustive source grep [D]+[E]
[B] Loogle            (ExtLogDomain _ _) → (ExtLogDomain _ _) → (ExtLogDomain _ _);  principal units mul_mem   no hits — `ExtLogDomain` is not a mathlib name; no p-adic-log-domain predicate exists to pattern-match
[C] LeanSearch        "the domain of the p-adic logarithm is closed under multiplication / is a subgroup"      n/a — tool not wired; covered by Phase-3 literature + [D]+[E] mathlib grep
[D] Grep mathlib src  padicLog / padicExp / Iwasawa-log / ExtLogDomain / extended logarithm / principalUnit subgroup / 1+𝔪 mul_mem   no relevant hits — `Mathlib/NumberTheory/Padics/` has NO padicLog/padicExp; "Iwasawa" hits are group-action Iwasawa decomposition (unrelated); "extended logarithm" hit is `ENNRealLogExp` (extended-reals, unrelated); valuation/localization files are generic infrastructure, none modelling the p-adic-log domain
[E] Name pattern      grep repo+mathlib for ExtLogDomain, extLog, InExpBall under .lake/packages/mathlib  no hits in mathlib — these names exist ONLY under projects/PadicLFunctions/
```

Searched for both:
- the user's current form (`ExtLogDomain p (x*y)` closure) — **not in mathlib**;
- the literature-standard form ("the p-adic-log domain / principal units `1+𝔪` is a multiplicative group / closed under `·`") — mathlib has **no** p-adic logarithm and **no** principal-unit subgroup bundle of `1+𝔪` carrying this `mul_mem`; the generic valuation API (`ValuationSubring`, `RamificationGroup`, etc.) does not model the exponential-ball principal units this lemma is about.

**Concluded:** **not in mathlib** (all methods exhausted, plus the literature-standard form). The proof's *building blocks* — `mul_pow`, `pow_mul`, `zpow_add₀`, `zpow_natCast`, `zpow_mul`, `ring` — are mathlib core, but the two domain-closure ingredients `mul_mem_expBall` and `pow_mem_expBall` are **project-local** (siblings; `mul_mem_expBall` verdict `NO-composable-from-mathlib`), and the *subject* `ExtLogDomain` is project-local (`NO-composable-from-mathlib`). Nothing to cite as an existing mathlib decl ⇒ **NOT** `NO-mathlib-has-it`.

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.ExtLogDomain.mul`

Internal use count: **1** (within `ExtLog.lean`, NOT the declaring line): `ExtLogDomain.prod` (`ExtLog.lean:408`) uses it in the `Finset.induction` step.
External-to-file callers: **1** distinct file.

| Caller file:line                                   | Usage pattern (one-line excerpt)                                                              |
|----------------------------------------------------|----------------------------------------------------------------------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:408` | `exact ExtLogDomain.mul p (hf i (Finset.mem_insert_self i s)) (ih …)` — builds `∏`-closure |
| `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:1095` | `ExtLogDomain.mul p (extLogDomain_of_integral_norm_one p …) hx` — proves `(-1)^k·x` stays in the domain (drives `extLog_neg_one_pow_mul`) |

Inline-derivation grep (was the equivalent re-derived without using `ExtLogDomain.mul`?):
- **YES — once, in `extLog_mul`** (`ExtLog.lean:357`, the additivity theorem). Its proof re-derives the *identical* product witness inline:
  `have hprod : (x*y)^(m*m') = (p:L)^(k*m'+k'*m) * (a^m' * b^m) := by rw [mul_pow, pow_mul x m m', hxy, …, zpow_add₀ hpL]; ring`
  and the same `hball : InExpBall p (a^m' * b^m - 1) := mul_mem_expBall p (pow_mem_expBall …) (pow_mem_expBall …)`.
  This is exactly the body of `ExtLogDomain.mul`, duplicated. (A `/cleanup` dedup opportunity *inside the project* — `extLog_mul` could destructure `ExtLogDomain.mul`'s witness — but this is fleet cleanup, not a mathlib-worthiness signal.)

**Call-sites signal:** `K = 1` internal + `1` external + `1` inline re-derivation of the same witness. This is **load-bearing project glue** (it is the `mul_mem` building block for `ExtLogDomain.prod`, `extLog_prod`, and `extLog_neg`/`extLog_neg_one_pow_mul`), but it is **not** mathlib-facing API — every consumer is inside `projects/PadicLFunctions/`.

### Composition check (Phase 6)

Can `ExtLogDomain.mul` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: produce the witness `⟨m*m', k*m'+k'*m, a^m'*b^m, …⟩` directly.
- Mathlib decls used: `mul_pow`, `pow_mul`, `zpow_add₀`, `zpow_mul`, `zpow_natCast`, `ring` (all mathlib core) — **plus** `mul_mem_expBall` and `pow_mem_expBall` (project-local).
- Result: **fails as a *mathlib* composition.** The factorisation `(x·y)^{m·m'} = p^{k·m'+k'·m}·(aᵐ'·bᵐ)` needs a real multi-rewrite + `ring` (≈6 rewrite lemmas, not a 1–3-call chain), and the ball-membership leg `mul_mem_expBall p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m)` calls **two project-local lemmas** with no mathlib counterpart (mathlib has no p-adic exponential ball). So it is neither a ≤3-call mathlib composition nor expressible from mathlib primitives alone.
- Notes: this is a genuine (if elementary) proof, not a `.symm`/`.trans`/one-call composition.

Attempt 2: re-aim at a more general mathlib `D'` (per the re-aim rule).
- There is **no** more-general mathlib object to re-aim at: `ExtLogDomain` has no mathlib analogue (mathlib has no p-adic log domain), and its building blocks `InExpBall`/`mul_mem_expBall` have no mathlib `D'`. The re-aim rule therefore does **not** fire; the decl is assessed in its own right.

Conclusion: **NOT-COMPOSABLE from mathlib** (the witness construction is a real proof and two of its legs are project-local). It *is* composable from **project** primitives — which is precisely why it lives in the project, not mathlib.

---

## Verdict: `PadicLFunctions.ExtLogDomain.mul`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the p-adic/Iwasawa log domain is canonically a **multiplicative group** (principal units `1+𝔪`, `p^ℤ·(1+𝔪)`, `C_p^×`); closure under `·` is its weakest group axiom — universally true and universally *bundled* into "the domain is a group / `log_p` is a homomorphism", **never** stated as a standalone `mul`-closure lemma (MIT 18.785, Harron AWS 2018, jtnb integral-logarithm, arXiv 1907.06437 / 0711.5028 / 0512015 / 2601.18187, Washington §5.1).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (field hypotheses already exceed the classical `K`/`C_p` literature; 0 weakenings). Phase 4c: the `Submonoid`/`Subgroup` bundling is the right *idiom* but unlocks **no mathlib downstream** (all ingredients project-local) ⇒ **not** a Bourbaki-2.0 YES.
- Mathlib search (Phase 5): **not in mathlib** — no `padicLog`/`padicExp`, no extended-log-domain predicate, no `1+𝔪` principal-unit `mul_mem` bundle; nothing to cite ⇒ **not** `NO-mathlib-has-it`.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the proof is a genuine product-witness construction and two of its legs (`mul_mem_expBall`, `pow_mem_expBall`) are project-local. Composable only from **project** primitives. Call sites: `K=1` internal + `1` external + `1` inline re-derivation (in `extLog_mul`).

**Rationale.** `ExtLogDomain.mul` is the closure-under-multiplication lemma for the project-local predicate `ExtLogDomain`, the domain of the project's Iwasawa-branch extended logarithm `extLog`. The mathematics is impeccable and canonical: every reference confirms that the domain of `log_p` is a *multiplicative group* (over `C_p`, all of `C_p^×`; over a finite extension, `p^ℤ·(1+𝔪)`), so closure under multiplication is automatic — it is one of the group axioms, and the literature carries it *bundled* into "the domain is a subgroup and `log_p` is a homomorphism", not as an isolated lemma. Two facts then place this firmly in `NO-composable-from-mathlib`, in lockstep with its parent. **(1)** The lemma's *subject* `ExtLogDomain` is project-local (verdict `NO-composable-from-mathlib`): it is the membership predicate for the domain of a `p`-adic logarithm that **mathlib does not have**, and its conclusion clause `InExpBall` is itself a project-local predicate. A `mul_mem` lemma about a not-in-mathlib predicate cannot be `NO-mathlib-has-it` (there is no decl, in any form, in mathlib that states it) and cannot be a YES bucket (mathlib gains nothing — there is no p-adic log, no principal-unit bundle, and no other API for it to compose with; per the skill's re-aim rule the parent has no more-general mathlib `D'` to re-aim at). **(2)** It is `NOT-COMPOSABLE from mathlib` specifically: the explicit product witness `(x·y)^{m·m'} = p^{k·m'+k'·m}·(aᵐ'·bᵐ)` is a genuine multi-rewrite proof (≈6 mathlib rewrites + `ring`, not a 1–3-call chain), and its ball-membership leg invokes the **project-local** `mul_mem_expBall`/`pow_mem_expBall` (no mathlib analogue, since mathlib has no exponential ball). It is, however, perfectly composable from the *project's own* primitives — which is exactly why it belongs in the project and not in mathlib.

This is the same shape as the parent `ExtLogDomain` (`NO-composable-from-mathlib`) and the sibling closure lemma `mul_mem_expBall` (`NO-composable-from-mathlib`): the genuinely-contributable mathematics of this development is the underlying `p`-adic `exp`/`log` API itself (`padicExp`, `padicLog`, the isometry, the functional equation, RJW §6), assessed under those declarations — while the domain-closure lemmas are project-local connective tissue. The Phase-4c `Submonoid`/`Subgroup` bundling is a reasonable *project-internal* refactor (it would turn this very lemma into the `mul_mem'` field), but it bundles only project-local content and unlocks no mathlib downstream, so it does not lift the verdict to a YES.

**WHY not — refactor-actionable detail.** Mathlib has the building blocks to write the *algebraic skeleton* of the witness factorisation (`mul_pow`, `pow_mul`, `zpow_add₀`, `zpow_mul`, `zpow_natCast`, `ring`), but it does **not** have the form and cannot, because (a) the statement is about the project-local predicate `ExtLogDomain` (domain of a p-adic log mathlib lacks), and (b) the ball-closure leg is the project-local `mul_mem_expBall`/`pow_mem_expBall`. The lemma should remain **project-local API**; there is nothing to upstream as a standalone declaration. Concretely, the actionable items are *project-internal cleanup*, not mathlib refactor:

Mathlib building blocks (the only mathlib-citeable parts — the algebraic skeleton):
- `mul_pow`, `pow_mul`, `mul_comm`, `zpow_add₀`, `zpow_mul`, `zpow_natCast`, `ring` — Mathlib core (`Mathlib/Algebra/GroupPower/...`, `Mathlib/Algebra/Order/...`). These assemble `(x·y)^{m·m'} = p^{k·m'+k'·m}·(aᵐ'·bᵐ)`.
- **Not** mathlib-citeable (the load-bearing legs): `mul_mem_expBall`, `pow_mem_expBall` (`ExtLog.lean:47, 67`; project-local, `mul_mem_expBall` verdict `NO-composable-from-mathlib`), and the subject `ExtLogDomain` (`ExtLog.lean:278`; `NO-composable-from-mathlib`).

Composition / inline form (≤3 lines — for the record; it is *not* a mathlib composition because two legs are project-local):
```lean
-- closure of the (project-local) extended-log domain under `·`, witness-explicit:
example {x y : L} (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) : ExtLogDomain p (x * y) := by
  obtain ⟨m, k, a, hm, hxy, ha⟩ := hx; obtain ⟨m', k', b, hm', hxy', hb⟩ := hy
  exact ⟨m * m', k * m' + k' * m, a ^ m' * b ^ m, Nat.mul_pos hm hm',
    by rw [mul_pow, pow_mul x m m', hxy, mul_pow, mul_comm m m', pow_mul y m' m, hxy', mul_pow,
        ← zpow_natCast ((p : L) ^ k) m', ← zpow_mul, ← zpow_natCast ((p : L) ^ k') m, ← zpow_mul,
        zpow_add₀ (natCast_p_ne_zero p)]; ring,
    mul_mem_expBall p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m)⟩  -- ← project-local legs
```

Call sites in our project (from Phase 6.0): **K = 1 internal** (`ExtLog.lean:408`, in `ExtLogDomain.prod`) + **1 external** (`ValuesAtOne.lean:1095`, in `extLog_neg_one_pow_mul`) + **1 inline re-derivation** of the identical witness (`extLog_mul`, `ExtLog.lean:357`).

**Refactor plan (project-internal, NOT a mathlib refactor).** Do **not** delete this lemma: it is load-bearing project API (it is the `mul_mem` step of `ExtLogDomain.prod`/`extLog_prod`, and is used in `ValuesAtOne.lean`). The actionable conclusions are:
1. **Negative for mathlib:** do not open a mathlib PR for `ExtLogDomain.mul` — its subject and two proof legs are project-local; nothing to upstream.
2. **Project dedup (fleet `/cleanup`, optional):** `extLog_mul` (`ExtLog.lean:357`) re-derives the *exact* product witness and ball-membership inline. It could destructure `ExtLogDomain.mul p hx hy` to obtain the witness instead of rebuilding it, removing the duplication. This is on-`main` cleanup, not mathlib work.
3. **Optional project idiom (Phase 4c):** if the project later wants the `Submonoid`/`Subgroup` packaging of the domain, this lemma becomes the `mul_mem'` field. Still project-local.

**Next action:** keep `ExtLogDomain.mul` as project-local API (verdict `NO-composable-from-mathlib`: the form is not in mathlib, cannot be — its subject is the domain of a p-adic log mathlib lacks — and it is composable only from the project's own primitives, not from mathlib in ≤3 calls). Do not upstream. Optionally, file a fleet `/cleanup` note to dedup the inline product-witness in `extLog_mul`.

---

## Next step

Keep `ExtLogDomain.mul` as project-local API. Do **not** open a mathlib PR: the lemma is the closure-under-multiplication fact for the project-local predicate `ExtLogDomain` (the domain of the project's `extLog`), whose subject and two proof legs (`mul_mem_expBall`, `pow_mem_expBall`) have no mathlib counterpart because mathlib carries no p-adic logarithm/exponential. The genuinely-contributable mathematics of this development is the `p`-adic `exp`/`log` API itself, assessed under those declarations. Optionally, file a fleet `/cleanup` ticket to dedup the identical product-witness construction that `extLog_mul` (`ExtLog.lean:357`) re-derives inline.
