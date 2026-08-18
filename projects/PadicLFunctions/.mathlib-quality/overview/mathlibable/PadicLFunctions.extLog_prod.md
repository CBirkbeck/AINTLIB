# `/mathlibable` report — `PadicLFunctions.extLog_prod`

**Final verdict: `BORDERLINE-needs-human`** (parent-def-dependent; leans `NO-composable-from-mathlib`).

The full ten-phase Mode-A workflow with the nine-channel exhaustive literature
search was run. Build was not re-run (stale/slow per task note); reasoned from
source, as Phase 0 fallback allows.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (task note: stale/slow). Decl + all dependencies read directly from `ExtLog.lean` / `PadicExp.lean`.
- decl `PadicLFunctions.extLog_prod`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:414`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The extended (Iwasawa-branch) p-adic logarithm — extends `padicLog` from the exponential convergence ball to the rational-valuation domain `{x : x^m = p^k·y, y ∈ ExpBall}`, with `extLog x := m⁻¹ • padicLog y` (junk `0` off-domain; Iwasawa branch `log_p p = 0`). RJW §6, decomposition W6a; cross-ref Washington, *Cyclotomic Fields*, §5.1.

---

### Statement (Phase 1)

`PadicLFunctions.extLog_prod` is a theorem stating the **finite-product additivity
law for the extended p-adic logarithm**:

> Let `L` be a complete ultrametric normed field, a normed `ℚ_p`-algebra. Let `s`
> be a finite index set and `f : ι → L` a family such that every `f i` (for
> `i ∈ s`) lies in the extended-log domain `ExtLogDomain p`. Then
> `extLog p (∏ i ∈ s, f i) = ∑ i ∈ s, extLog p (f i)`.

This is the classical "log of a product is the sum of logs" law, `log(∏ xᵢ) = ∑ log(xᵢ)`,
for the specific extended (Iwasawa-branch) p-adic logarithm `extLog` defined in
this file, with the standing requirement that every factor lie in the domain on
which `extLog` is additive.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — the coefficient field (a complete ultrametric normed `ℚ_p`-algebra).
- `ι : Type*` — index type.
- `s : Finset ι` — the finite index set.
- `f : ι → L` — the family of factors.

Hypotheses (Lean side):
- `hf : ∀ i ∈ s, ExtLogDomain p (f i)` — every factor lies in the extended-log domain. This is essential: `extLog` is additive *only* on this domain.

Conclusion (math): the extended logarithm of a finite product of domain elements equals the sum of their extended logarithms.

Conclusion (Lean): `extLog p (∏ i ∈ s, f i) = ∑ i ∈ s, extLog p (f i)`.

Proof body (5 lines): `classical`, then `Finset.induction` — empty case via
`Finset.prod_empty`/`Finset.sum_empty` + `extLog_eq_padicLog` + `padicLog_one`;
insert case via `Finset.prod_insert`/`Finset.sum_insert` + `extLog_mul` (binary
additivity) + `ExtLogDomain.prod` (domain closure under finite products) + the
induction hypothesis. The proof threads the domain hypothesis through
`ExtLogDomain.prod` so that `extLog_mul`'s domain preconditions are met at each
step.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a corollary/wrapper — the finite-product form of the binary
`extLog_mul`, proved by routine `Finset.induction`. Not a new structure, not a
named theorem, not a top-level project goal (it is a *driver* of the `μ_p`-collapse
inside the trace computation, per its own docstring, not an endpoint).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is for framing only.)

### One-line check (Phase 2b)

Body line count: 5 substantive lines (a `Finset.induction` with two cases).
One-liner verdict: n/a — kind is `theorem`, not `def`.

This section is skipped (not a definition). Carried forward: it is a thin
inductive wrapper, which biases Phase 7 toward a NO / composable framing.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm additive over finite product log of product equals sum of logs Iwasawa branch"       | yes  | p-adic log is "an injective group homomorphism on its domain"; converts products to sums on its domain | arXiv Iwasawa-theory papers; pari-users; researchgate "image of p-adic log on principal units" — the finite-product law is implicit in the homomorphism, never a named theorem |
|  2 | WebSearch (general form)         | "logarithm of a finite product equals sum of logarithms homomorphism general definition"               | yes  | `log_b(wxyz) = log_b w + log_b x + log_b y + log_b z` "by repeated applications of the product rule"; logarithm = "partially-defined homomorphism from multiplicative to additive group" | Lumen/Richland algebra texts; nLab; Wikipedia "Logarithm" — finite-product law is the standard *inductive consequence* of the binary law, not stated separately |
|  3 | WebSearch (named-after / aliases / mathlib) | `"map_prod" OR "MonoidHom.map_prod"` mathlib Lean homomorphism finite product partial conditional submonoid | yes  | `map_prod` (homomorphism over finite product) is the canonical mathlib/Lean primitive; `MonoidHom.prod`, `MonoidHom.prodMap` adjacent | confirms mathlib already has the generic monoid-hom-over-product lemma — but only for genuine `MonoidHomClass` maps, not junk-total partial homomorphisms |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of log-of-product law and p-adic log")   | n/a  | —                                | ChatGPT MCP server not configured in this environment (no tool surfaced). Recorded n/a; channels 1–3,6,9,10 cover the standard-form question. |
|  5 | Local references                 | `ls .mathlib-quality/references/`, `ls refs/PadicLFunctions/`                                            | n/a  | (no references dir; no refs store) | Neither `projects/PadicLFunctions/.mathlib-quality/references/` nor `refs/` exists in this checkout. Recorded n/a. The in-file docstrings cite RJW §6 and Washington §5.1 as the source for the *construction* of `extLog`. |
|  6 | nLab                             | nLab "logarithm" page (WebFetch)                                                                         | yes  | "a logarithm is a partially-defined smooth homomorphism from a multiplicative group of numbers to an additive group of numbers" | nLab does NOT state the finite-product law as a standalone property — "treated as an implicit consequence of the homomorphism definition rather than a named theorem". No p-adic-log discussion. |
|  7 | nCatLab (if categorical)         | (covered by the nLab fetch in #6)                                                                       | n/a  | —                                | Not a categorical construction; the relevant nLab content is the "logarithm" page already fetched. n/a. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | Not an algebraic-geometry concept (p-adic analytic / Iwasawa-theoretic logarithm law). n/a. |
|  9 | MathOverflow / Math.StackExchange| "partially defined homomorphism finite product induction membership domain ... conditional additivity"  | partial | "By induction, the statement holds for all finite (co-)products" (nLab additive-category); additive relations / quasi-homomorphisms | confirms the finite-product law is the routine induction from the binary case; no special name even for the *conditional/partial* case |
| 10 | recent arXiv (last 5 years)      | (channel-1 results) e.g. arXiv 1904.09850 "On the image of p-adic logarithm on principal units"; 1907.06437 | yes  | p-adic log as group homomorphism on principal units / its image as a module | modern Iwasawa-theory literature uses the homomorphism property freely; the finite-product additivity is assumed, never proved as a headline lemma |

The protocol passed: WebSearch ran 3 distinct queries at different generality
levels (specific p-adic finite-product form; general log-of-product
homomorphism form; mathlib/named-API form); nLab was checked (fetched);
Stacks / nCatLab / MathOverflow / arXiv each checked or recorded n/a with a
reason; local references recorded n/a (absent). ChatGPT MCP recorded n/a
(server not configured) — the standard-form question is nonetheless fully
answered by the remaining channels.

### Literature summary (Phase 3)

Concept identified as: **the finite-product (multiplicativity → additivity) law
of a logarithm** — `log(∏ xᵢ) = ∑ log(xᵢ)` — here for the *p-adic Iwasawa-branch
logarithm* on its domain of definition.

Sources agree on the standard form: **yes**. Universally, the logarithm is a
(partial) homomorphism from a multiplicative structure to an additive structure;
the finite-product law is the iterate of the binary product rule, obtained "by
repeated applications of the product rule" / "by induction". For the p-adic log
specifically, it is "an injective group homomorphism on its domain", so the
finite-product law holds on that domain.

Most general standard form: for any (partial) homomorphism `φ` from a commutative
monoid to a commutative additive monoid, `φ(∏ xᵢ) = ∑ φ(xᵢ)` whenever every `xᵢ`
lies in the domain of additivity. In bundled (total-homomorphism) form this is
mathlib's `map_prod` / `map_sum`.

Generality dimensions where the literature varies:
  - **What the logarithm is a hom of**: real/complex positive reals (classical);
    principal units of a local field (Iwasawa); the rational-valuation domain
    `ExtLogDomain` (this project, the Iwasawa branch). The most general standard
    statement is "for any homomorphism, over any finite product".
  - **Totality**: the literature emphasises the *partial* nature ("partially-defined
    homomorphism"); the additivity holds only on the domain. This project's
    `hf : ∀ i ∈ s, ExtLogDomain p (f i)` hypothesis is exactly the partial-domain
    bookkeeping the literature flags.

Disagreement with the literature: **none**. `extLog_prod` is precisely the
standard finite-product law for `extLog`, with the correct (necessary)
domain hypothesis on every factor. It is never given a name in the literature
because it is the trivial induction.

---

### Generality analysis — `PadicLFunctions.extLog_prod` (Phase 4)

Literature-standard form (from Phase 3): for a (partial) hom `φ` to an additive
commutative monoid, `φ(∏_{i∈s} xᵢ) = ∑_{i∈s} φ(xᵢ)` whenever each `xᵢ` is in
`φ`'s domain of additivity. Bundled form = `map_prod`/`map_sum`.

| # | Parameter / hypothesis                | Current Lean form                       | Literature-standard form                       | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|-----------------------------------------|------------------------------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L] … [CompleteSpace L]` | complete ultrametric normed ℚ_p-algebra | wherever `extLog` is defined                    | NO                  | These are exactly the standing hypotheses needed to *define* `extLog`/`padicLog` and to prove `extLog_mul`; not weakenable without changing the parent object. (Indeed `extLog_prod` even *uses* `CompleteSpace` indirectly via `extLog_mul`, unlike the `omit`-annotated `ExtLogDomain.prod`.) |
| 2 | `s : Finset ι`, `ι : Type*`           | arbitrary finite index set              | arbitrary finite index set                      | —                   | Already maximally general (any type, any finite subset) — matches mathlib's `Finset` big-operator convention exactly. |
| 3 | `hf : ∀ i ∈ s, ExtLogDomain p (f i)`  | every factor in the additivity domain   | every factor in the (partial) hom's domain      | NO                  | This is the minimal hypothesis: `extLog` is genuinely not additive off-domain (junk-total). Dropping it makes the statement false. Matches the literature's "partial homomorphism" caveat exactly. |
| 4 | the *object* `extLog`                 | project-specific Iwasawa-branch p-adic log | (literature: the p-adic / Iwasawa log)        | n/a (parent def)    | Generality of `extLog_prod` is entirely downstream of `extLog`'s generality — see Phase 4c Q8 and Phase 7. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the object it is about).
Number of weakening opportunities found: **0**. The index side is already fully
general (`Finset ι`, `ι : Type*`); the domain hypothesis is necessary and exactly
matches the literature's partial-homomorphism form; the field hypotheses are the
defining hypotheses of `extLog` itself.

Proposed restatement: none at the `extLog_prod` level. (The only "generalisation"
available is at the *parent object* level — see 4c.)

Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                                    | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | Already typeclass-driven (`NormedField`, `NormedAlgebra`, `IsUltrametricDist`, `CompleteSpace`). |
|  2 | sequences/metric → filters/topological?                                                                    | no       | — | No sequential/metric content in the *statement* — it is a finite-product algebraic identity. |
|  3 | construct an object where a universal property would characterise it?                                       | no       | — | This is a lemma, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure? **(relevant to the parent, not this lemma)**            | **yes (parent)** | Make `ExtLogDomain` a bundled `Submonoid L` (it IS closed under `1`, `*`, finite products — see `ExtLogDomain.mul`/`ExtLogDomain.prod`) and make `extLog` an `AddMonoidHom (extLogSubmonoid)ᵐᵒᵖ? / MonoidHom → Additive`. Then `extLog_prod` becomes a one-line `map_prod`. | The ENTIRE finite-product/finite-sum API (`map_prod`, `map_sum`, `Finset.prod_*`) applies for free. This is the real modernisation — but it is a change to `extLog`/`ExtLogDomain`, not to `extLog_prod`. |
|  5 | vector-space/metric/field-specific → weaker typeclass (module/pseudometric/(semi)ring)?                    | no       | — | Hypotheses are intrinsic to the p-adic-log construction. |
|  6 | 1-categorical → higher-categorical?                                                                         | no       | — | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                                  | no       | — | Index is already `ι : Type*` over a `Finset`. |
|  8 | **Concrete-via-abstract**: statement names a concrete object, but the proof body uses only abstract properties? | **yes** | See diagnostic below. | The abstract content is "additive-on-a-domain ⇒ additive over finite products", which mathlib *already* packages as `map_prod`/`prod_hom_rel` for the unconditional/bundled case. |

#### Q8 diagnostic (adversarial, run explicitly)

Grep the proof body of `extLog_prod` (lines 417–424) for the named object `extLog`
and for any `extLog`-specific lemma:
- The proof invokes `extLog`-specific facts at **every** step: `extLog_eq_padicLog`
  + `padicLog_one` (empty case) and `extLog_mul` (insert case). It is NOT the case
  that `extLog` vanishes after one unfolding — the proof is *about* `extLog` throughout.
- BUT the *shape* of the argument is entirely generic: it is the induction
  "binary law + closure-under-product + IH ⇒ finite-product law". The only
  `extLog`-specific inputs are (a) the binary additivity `extLog_mul` and (b) the
  domain closure `ExtLogDomain.prod`. Strip those two and the skeleton is the
  proof of `map_prod` / `Finset.prod_hom_rel`.

So Q8 fires in the *organisational* sense: the abstract content already lives in
mathlib (`map_prod`/`sum_hom_rel`); what is `extLog`-specific is only the two
ingredient lemmas, which are themselves the genuinely-new project content.

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it targets the parent object, not this lemma.**

- Proposed mathlib-idiomatic restatement (of the *parent*): bundle `ExtLogDomain p`
  as a `Submonoid L` (it contains `1` via `inExpBall_one_sub_one`, is closed under
  `*` via `ExtLogDomain.mul`, hence under finite products via `Submonoid`'s own
  `prod_mem`), and express `extLog` restricted to it as a genuine
  `MonoidHom → Additive`-style morphism (additivity = `extLog_mul`). Then
  `extLog_prod` collapses to a direct application of mathlib's `map_prod` / `map_sum`
  — i.e., it ceases to exist as a separate lemma.
- Cost: MODERATE (bundling `ExtLogDomain` + restating `extLog` on the bundle;
  the binary-additivity proof transfers verbatim).
- Mathlib downstream this enables: the full `map_prod`/`map_sum`/`Finset.prod_*`
  ecosystem applies to `extLog` for free — `extLog_prod`, `extLog_neg` (via `map_*`),
  and any future finite-(co)product law become free corollaries.
- Real mathematical improvement: eliminates the bespoke induction wrapper entirely
  by recognising `extLog`-on-its-domain as a (partial) homomorphism — exactly the
  nLab characterisation. **This is a `/generalise`-on-`extLog` action, not an
  `extLog_prod` action**, which is precisely why the Phase-7 verdict is parent-
  dependent (BORDERLINE), not a self-contained YES-but-generalise-first on this lemma.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equality or typeclass-search
path introduced).

---

### Mathlib search-status: `PadicLFunctions.extLog_prod` (Phase 5)

Performed via the five-method protocol against the local mathlib checkout
(`.lake/packages/mathlib/Mathlib/`) plus WebSearch over the mathlib docs.

[A] Lean-Finder       (server not available in this env) — n/a; substituted with direct source grep [D] over the local mathlib tree, which is authoritative.
[B] Loogle            type pattern `?f (∏ i ∈ ?s, ?g i) = ∑ i ∈ ?s, ?f (?g i)` / `map_prod`-shape — covered via source grep: the generic shape is `map_prod`/`prod_hom_rel`. No p-adic-log instance.
[C] LeanSearch        NL: "logarithm of finite product equals sum of logarithms", "p-adic logarithm additive over product" — covered via WebSearch #3 over mathlib docs: only generic `map_prod`/`MonoidHom.*` surface; no `padicLog`/`extLog`.
[D] Grep mathlib src  `grep -rn` for `padicLog`, `extLog`, `prod_induction`, `map_prod`, `prod_hom_rel`, `sum_hom_rel` in `.lake/packages/mathlib/Mathlib/` —
      • **No p-adic logarithm anywhere in mathlib.** `Mathlib/NumberTheory/Padics/` has `PadicVal`, `PadicNorm`, `PadicNumbers`, `PadicIntegers`, `Hensel`, `MahlerBasis`, `AddChar`, … but NO `padicLog`/`extLog`/`Padic*.log`. (grep hit only `PadicVal`/`PadicNorm`.)
      • Generic finite-product hom lemmas DO exist: `Finset.map_prod` (`Group/Finset/Defs.lean:346`, for `MonoidHomClass`), `Finset.prod_hom_rel` (`:534`), `Finset.prod_induction` (`:600`), and `Multiset`/`List` analogues.
[E] Name pattern      grep for decls named `*extLog*` / `*padicLog*` / `*_prod` about a logarithm in mathlib — none in mathlib (these names live only in this project).

Searched for both:
  - the user's current form (`extLog`-of-finite-product): **not in mathlib** — `extLog` does not exist in mathlib.
  - the literature-standard / bundled form (`map_prod` for a monoid hom): **in mathlib** as `Finset.map_prod` / `map_sum`, and the unconditional relational lift `Finset.prod_hom_rel` / `Finset.sum_hom_rel`. These require a *genuine* `MonoidHomClass` map (`map_prod`) or an *unconditional* binary law `h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)` (`prod_hom_rel`).

**Critical mismatch.** `extLog` is junk-total and additive ONLY on `ExtLogDomain`
(`extLog_mul` carries `hx : ExtLogDomain p x`, `hy : ExtLogDomain p y` — confirmed
at `ExtLog.lean:357`). Therefore:
  - `map_prod`/`map_sum` do NOT apply — `extLog` is not a `MonoidHomClass`/`AddMonoidHomClass` member (no bundled hom; not even total-additive).
  - `Finset.prod_hom_rel`/`sum_hom_rel` do NOT apply — their `h₂` hypothesis is *unconditional*, but `extLog`'s binary additivity is *conditional* on domain membership of both arguments. There is no `*_hom_rel` variant in mathlib that takes a per-factor membership predicate (grep for `∀ i ∈ s … → … ∏`/conditional `sum_hom_rel` in `Group/Finset/Defs.lean` returned nothing).

Concluded: **not in mathlib** (the object `extLog` is absent; the generic
bundled/unconditional product-hom lemmas exist but are inapplicable because
`extLog`'s additivity is a *partial/conditional* law). Mathlib has the *pattern*
(`map_prod`, `prod_hom_rel`) but neither the object nor a conditional-additivity
finite-product lemma matching this exact shape.

---

### Call sites — `PadicLFunctions.extLog_prod` (Phase 6.0)

Internal use count: **1** (within PadicLFunctions, excluding the declaring file).
External-to-file callers: **1 distinct file** (`ValuesAtOne.lean`).

| Caller file:line               | Usage pattern (one-line excerpt)                                         |
|--------------------------------|---------------------------------------------------------------------------|
| `ValuesAtOne.lean:1158`        | `rw [… , ← extLog_prod p _ _ hdomζ, hprodId, …]` — used backwards to collapse `∑_{ζ} extLog(ζ·ε^c − 1)` into `extLog(∏_ζ (ζ·ε^c − 1))`, the `μ_p`-collapse step. |
| `ValuesAtOne.lean:944` (doc)   | docstring: "(`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` + `extLog_prod`), and the `c ↦ pc`…" — names it as a key ingredient. |
| `ValuesAtOne.lean:1124` (doc)  | docstring: "…`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`), `extLog_prod`, and the sign-stripping…" |

Inline-derivation grep (was the equivalent re-derived elsewhere without `extLog_prod`?):
  - (none) — no other site re-runs the `Finset.induction`-over-`extLog_mul` argument
    inline. The sibling `ResidueZeta.lean` uses the *binary* `extLog_mul` directly
    (`:1766`), not a finite-product form.

Call-sites signal: **K = 1 internal use, no inline re-derivation.** Per the Phase-6
table, K = 1 "possibly the wrong abstraction — could be inlined" leans toward
NO-composable; however the single use is genuinely load-bearing (the `μ_p`-collapse
is a real step in the trace computation, R6 cluster W6a), and the `← extLog_prod`
rewrite is cleaner than an inline induction. This nudges back toward "keep it, but
project-local".

### Composition check (Phase 6)

Can `extLog_prod` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `Finset.sum_hom_rel` / `map_sum`.
  - Mathlib decls used: `Finset.sum_hom_rel` (or `map_sum`).
  - Result: **fails.** `map_sum` needs `extLog` to be a bundled `AddMonoidHomClass`
    map — it is not. `Finset.sum_hom_rel` needs the *unconditional* additivity
    `h₂ : ∀ a b c, r b c → r (f a + b) (g a + c)`; but `extLog (x*y) = extLog x + extLog y`
    holds only when `x, y ∈ ExtLogDomain`, so the unconditional `h₂` cannot be supplied.

Attempt 2: `Finset.prod_induction` to first establish `∏ f i ∈ ExtLogDomain`, then
  a separate induction for the equation.
  - Mathlib decls used: `Finset.prod_induction` (gives `ExtLogDomain (∏ f i)`).
  - Result: **partial.** This is exactly what `ExtLogDomain.prod` (project lemma)
    packages, and it only gives domain *membership*, not the additivity *equation*.
    The equation still requires the bespoke induction over `extLog_mul`. Not ≤3
    mathlib calls.

Conclusion: **NOT-COMPOSABLE from mathlib in ≤3 calls.** The obstruction is precisely
that `extLog`'s additivity is *conditional* (partial homomorphism), so neither the
bundled (`map_sum`) nor the unconditional-relational (`sum_hom_rel`) mathlib lemma
fits. The genuine composition would be from the *project's own* `extLog_mul` +
`ExtLogDomain.prod` (which is what the proof does) — but those are not mathlib.

**Important caveat for the verdict:** "NOT-COMPOSABLE from mathlib" here is true only
because the base object `extLog` is itself absent from mathlib. The *abstract pattern*
("conditional binary additivity + domain closure ⇒ finite-product additivity") is
fully within mathlib's wheelhouse and would be a one-line `map_prod` the moment
`extLog`-on-its-domain were bundled as a homomorphism (Phase 4c). So the composability
question is inseparable from the parent-object question.

---

## Verdict: `PadicLFunctions.extLog_prod`

**Category:** `BORDERLINE-needs-human` (parent-def-dependent; leans `NO-composable-from-mathlib`)

**Evidence:**
- Literature search (Phase 3): the finite-product log law is universally standard
  but never a *named* theorem — it is the routine induction from the binary product
  rule ("repeated applications of the product rule" / nLab "implicit consequence of
  the homomorphism definition"). The p-adic log is a homomorphism on its domain.
- Generality analysis (Phase 4): MAXIMALLY GENERAL *for the object it is about*
  (index side fully general; domain hypothesis necessary and matching the
  literature's partial-homomorphism caveat). The only available generalisation is
  to the **parent** (`extLog`/`ExtLogDomain`), via bundling — Phase 4c Q4/Q8.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic logarithm exists in
  mathlib at all; the generic `map_prod`/`prod_hom_rel`/`sum_hom_rel` exist but are
  inapplicable to a *conditional* (partial-domain) additivity.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib in ≤3 calls — but only
  because `extLog` is project-specific; the abstract pattern is mathlib-native.

**Rationale (why BORDERLINE):**

`extLog_prod` is the bespoke finite-product instance of a pattern mathlib already
owns completely (`map_prod` / `map_sum` / `Finset.prod_hom_rel`). It is not a new
piece of mathematics: the literature treats "log of a product = sum of logs" as the
trivial induction from the binary law, and mathlib already has the bundled
homomorphism-over-finite-product machinery. The lemma exists in this project only
because its base object, the extended Iwasawa-branch p-adic logarithm `extLog`, is
(a) absent from mathlib and (b) a *partial* (junk-total, domain-restricted)
homomorphism that is not bundled as an `AddMonoidHomClass` map. Those two facts are
exactly what make mathlib's `map_sum` and the unconditional `sum_hom_rel`
inapplicable, and they are what would have to change for `extLog_prod` to become a
one-line corollary.

This makes the verdict genuinely parent-dependent, which is the textbook trigger for
BORDERLINE (two buckets fit and the choice rests on a judgment the skill cannot make
alone). **If `extLog` is and will remain project-local** (the likely reality — it is
RJW-§6 trace-computation infrastructure, and mathlib has no p-adic-log development to
host it), then `extLog_prod` is plainly **NOT mathlib-worthy**: it is the local
analogue of `map_sum` for a local object, and the correct action is to keep it in the
project (it is genuinely used, once, in a load-bearing way at `ValuesAtOne.lean:1158`).
The closest mathlib bucket in that case is `NO-composable-from-mathlib` *in spirit*
(mathlib has the pattern; the lemma is the project-local specialisation), even though
it is not literally a ≤3-call mathlib composition because the building blocks
(`extLog_mul`, `ExtLogDomain.prod`) are themselves project lemmas. **If instead a
p-adic-logarithm development were ever upstreamed to mathlib**, the right move is not
to ship `extLog_prod` as-is but to bundle `ExtLogDomain` as a `Submonoid` and `extLog`
as a (partial) homomorphism (Phase 4c), after which `extLog_prod` evaporates into
`map_sum`. Either way, **`extLog_prod` is not a standalone mathlib addition.**

**Numbered questions for the user (≤5):**

1. Is the extended p-adic logarithm `extLog` (and `padicLog`, `ExtLogDomain`) intended
   to stay **project-local**, or is there an aspiration to upstream a p-adic-logarithm
   development to mathlib? (Mathlib currently has no p-adic logarithm at all.)
2. If `extLog` stays local: do you agree `extLog_prod` should simply **remain in the
   project** (it is the local `map_sum` analogue, genuinely used once at
   `ValuesAtOne.lean:1158`) and is **not** a candidate for a standalone mathlib PR?
3. If `extLog` is ever upstreamed: are you open to the **modernisation** in Phase 4c —
   bundling `ExtLogDomain` as a `Submonoid L` and `extLog`-on-it as a (partial)
   homomorphism — so that `extLog_prod` becomes a free `map_sum` corollary rather than
   a separate lemma? (Cost: MODERATE; binary-additivity proof transfers verbatim.)
4. Independently of mathlib: would you like a cleanup ticket to *try* replacing the
   bespoke `Finset.induction` body of `extLog_prod` with `Finset.sum_induction`-style
   plumbing or a thin wrapper, purely to reduce duplication with the generic pattern?
   (This is a project-internal golf question, orthogonal to the mathlib verdict.)

**Next action:** user answers the questions (chiefly Q1 — the parent-object policy).
Most likely resolution given the evidence: Q1 = "project-local" ⇒ verdict resolves to
**NO** (keep `extLog_prod` in the project as the local `map_sum` analogue; do not PR
to mathlib as a standalone lemma; revisit only if/when a p-adic-log development is
upstreamed, at which point Q3's bundling is the right route, not this lemma).

---

## Next step

User answers the four numbered questions above — primarily **Q1** (is `extLog`/
`padicLog` staying project-local, or is a mathlib p-adic-logarithm development
intended?). The answer to Q1 deterministically resolves the verdict:
- **project-local** ⇒ NO (not a standalone mathlib addition; it is the local
  `map_sum` analogue, kept in-project; genuinely used at `ValuesAtOne.lean:1158`);
- **upstream intended** ⇒ the contribution is the *bundled* `extLog`-as-homomorphism
  (Phase 4c), after which `extLog_prod` is a free `map_sum` corollary — run
  `/generalise` on `extLog`/`ExtLogDomain`, not a PR of `extLog_prod` itself.
