# `/mathlibable` report — `PadicLFunctions.extLogDomain_of_integral_norm_one`

**Final verdict: `BORDERLINE-needs-human`**

The theorem is genuinely novel (mathlib has no p-adic logarithm at all), is not
in mathlib, and is not a ≤3-call composition of mathlib primitives. But its
conclusion type `ExtLogDomain p z` is a *project-local* predicate built on the
project's own `padicLog` / `InExpBall` / `ExtLogDomain` definitions — none of
which exist in mathlib. So the lemma cannot be upstreamed in isolation; the real
question is whether to upstream the **entire extended-p-adic-logarithm
development** (and at what generality), which is a mathematical-taste +
project-policy judgment the skill cannot resolve alone. Hence BORDERLINE, with
numbered questions in Phase 7.

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task instruction; AINTLIB build is stale/slow)
- decl `PadicLFunctions.extLogDomain_of_integral_norm_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:446`
- kind:                      theorem
- has sorry:                 no (verified — no `sorry`/`admit` in `ExtLog.lean`)
- module docstring summary:  "The extended (Iwasawa-branch) p-adic logarithm" — extends `padicLog` to rational-valuation elements `x` with `x^m = p^k·y`, `y` in the open exponential ball; `extLogDomain_of_integral_norm_one` is named in the docstring as "the domain-membership engine for the theorem's arguments" (RJW §6, decomposition cluster W6a; cross-ref Washington, *Introduction to Cyclotomic Fields*, §5.1).

Environment note: no Loogle/LeanSearch/Lean-Finder MCP and no ChatGPT MCP are
available in this session. Phase 3 used WebSearch + WebFetch (incl. the Loogle
JSON API and arXiv/nLab/Stacks/MathOverflow via search); Phase 5 used the Loogle
JSON API + direct grep over the vendored mathlib at `.lake/packages/mathlib`.
Channels needing an absent MCP are recorded `n/a` with the reason.

---

### Statement (Phase 1)

`extLogDomain_of_integral_norm_one` is a theorem stating the following:

> Let `L` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra.
> If `z ∈ L` is integral over `ℤ` and has norm `‖z‖ = 1`, then `z` lies in the
> domain of the extended p-adic logarithm — i.e. there exist `m > 0`, `k ∈ ℤ`
> and `y ∈ L` with `z^m = p^k · y` and `y − 1` inside the open convergence ball
> of the p-adic exponential (`‖y − 1‖^(p−1) < p⁻¹`).

In the proof, the witness taken is `m = m₀·p^j`, `k = 0`, `y = z^(m₀·p^j)`,
where `m₀` is a power for which `‖z^{m₀} − 1‖ ≤ p⁻¹` (pigeonhole in the finite
ring `ℤ[z]/p`, supplied by `exists_pow_sub_one_norm_le`) and `j` is a p-power
iteration count carrying `z^{m₀}` into the exponential ball
(`exists_pPow_pow_inExpBall`). The conclusion is the *unconditional* fact that
every norm-one integral element is in the log-domain — i.e. the extended log is
defined on all such elements. Mathematically this is the standard observation
that one-units (and, after a finite-order twist, all integral units) of a p-adic
extension are reachable by `log_p` after passing to a suitable power.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic / base prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` —
  a complete ultrametric extension of `ℚ_p` (`[CompleteSpace L]` is **omitted**
  for this theorem via `omit [CompleteSpace L] in`).

Hypotheses (Lean side):
- `hz : IsIntegral ℤ z` — `z` is a root of a monic integer polynomial (lies in
  the ring of integers / integral closure).
- `hz1 : ‖z‖ = 1` — `z` is a unit of norm one.

Conclusion (math): a norm-one integral element has a power lying (up to a `p^k`
factor, here `k = 0`) inside the exponential convergence ball — i.e. it is in
the domain of the extended Iwasawa-branch logarithm.

Conclusion (Lean): `ExtLogDomain p z`, i.e.
`∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ z ^ m = (p : L) ^ k * y ∧ InExpBall p (y - 1)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG caveat)
Reason: As a *standalone declaration* it is a supporting membership lemma
(`P → Q`), not a named theorem and not itself a new structure. **However**, it is
the API entry point into a BIG construction — the extended p-adic logarithm
`extLog` / its domain predicate `ExtLogDomain`, which *are* new mathematical
structures absent from mathlib. The docstring explicitly calls it "the domain
engine". So the lemma is small but it lives at the doorway of a BIG, mathlib-
absent development, and that is exactly what makes the verdict borderline.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL did not gate the
channels run in Phase 3.)

### One-line check (Phase 2b)

Body line count: ~6 substantive lines (two `obtain`s, a `have`, and a `refine`
with two field goals).
One-liner verdict: **n/a (kind is theorem, not def)**. The Phase-2b def
exemptions do not apply. Recorded as a one-line note per the skill.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic logarithm extended to units rational valuation Iwasawa branch log_p(p)=0 Washington cyclotomic fields" | yes | Iwasawa's `log_p` with `log p = 0`; "raise to a power until valuation is integral, divide by power of p to get a unit, apply the log series" | Exactly the construction this file formalizes; Washington §5.1, Iwasawa. Surfaced arXiv:1904.09850, 1907.06437 on `log` image on principal units. |
| 2 | WebSearch (general form) | "unit ring of integers local field power close to 1 p-adic logarithm convergence ball one-units pro-p" | yes | log converges on 1-units `1 + m_K`; unique extension of `log_p` to all of `C_p^×` with `log(ζ p^s)=0` | Confirms the maximally-general classical target: the extension exists on **all** of `C_p^×`, not just integral norm-one elements. |
| 3 | WebSearch (named-after / aliases) | "root of unity times one-unit decomposition unit group local field finite residue pigeonhole power congruent 1 mod p" | yes | `O_K^×` units reduce onto residue field; kernel = principal units `1 + m_K`; `x^{q-1}=1` mod m; Hensel lift | The precise sub-fact used here (a power of a norm-one element is `≡ 1`) is the standard unit-filtration / finite-residue pigeonhole; no special name. |
| 4 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of the extended p-adic log domain") | n/a | — | ChatGPT MCP not available in this session. Substituted by WebSearch rows 1–2 which already asked for standard form + generality, and recovered Iwasawa's historical normalisation `log p = 0`. |
| 5 | Local references | grep `.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir; no `refs` symlink) | `.mathlib-quality/` has only `overview/`; no PDFs present. Recorded n/a per skill. |
| 6 | nLab | `p-adic+logarithm`, `principal units / 1-units logarithm isomorphism` | partial | nLab page `/show/p-adic+logarithm` returns 404; via search, 1-unit log isometry discussed | No clean standalone "extended-log domain" statement on nLab; concept is treated inside local-field / formal-group material. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept (a concrete p-adic analytic predicate); nothing to categorify. |
| 8 | Stacks Project | searched modules-over-PID / finite modules + p-adic log | n/a (for the log) | finite-module structure theory exists; **no p-adic logarithm** | Stacks is algebraic geometry / commutative algebra; the analytic p-adic logarithm is out of scope. Only the *building-block* finiteness lives there (structure of f.g. modules, 0ASL/00NV). |
| 9 | MathOverflow / Math.StackExchange | "extend p-adic logarithm C_p multiplicative group log(p)=0 unique homomorphism power into convergence disc" | yes | unique extension to `C_p^×`, `log p = 0`, via powering into the convergence disc | Confirms rows 1–2; the extension is folklore-standard. MIT 18.785 PS10 has it as a graded exercise. |
| 10 | recent arXiv (last 5 years) | "image of p-adic logarithm on principal units" | yes | arXiv:1904.09850, 1907.06437, 2302.14491 (Lean-3 p-adic L-functions) | Active topic. **arXiv:2302.14491 (Narayanan)** is a prior Lean-3 formalization of p-adic L-functions — checked (Phase 5): it builds the L-function via Bernoulli measures and does **not** formalize an extended p-adic logarithm / domain predicate. |

Protocol pass check:
- WebSearch ran ≥3 distinct queries at different generality (specific form,
  most-general `C_p^×` form, named-after/aliases): ✓ (rows 1–3).
- ChatGPT-MCP standard-form/generality/history query: substituted (MCP absent) —
  rows 1–2 covered standard form + generality, row 1 recovered the historical
  `log p = 0` normalisation. Recorded honestly as `n/a` with substitution.
- Local references checked (absent, n/a): ✓.
- nLab checked: ✓. Stacks / nCatLab / MathOverflow / arXiv each checked or n/a
  with reason: ✓.

### Literature summary (Phase 3)

Concept identified as: **the extension of the p-adic (Iwasawa-branch) logarithm
beyond its convergence disc**, and specifically its *domain-membership* sub-fact:
a norm-one integral element of a p-adic field has a power inside the exponential
convergence ball.
Sources agree on the standard form: **yes** — Iwasawa's `log_p` (normalised
`log p = 0`) extends uniquely to all of `C_p^×`; the construction is "power up to
integral valuation, factor out `p^k`, apply the log series to the resulting
1-unit". (Washington §5.1; Iwasawa; MIT 18.785; arXiv:1904.09850.)
Most general standard form: the extended log is defined on **all of `C_p^×`** (or
`L^×` for any complete extension `L`), not merely on norm-one integral elements.
The "domain" in the maximally-general treatment is the entire multiplicative
group; the norm-one-integral hypothesis here is a *sufficient* condition used
because those are exactly the arguments `1 − ε_N^c` that arise in RJW Thm 6.1(ii).
Generality dimensions where the literature varies:
- **What the log is defined on:** literature = all of `C_p^×`/`L^×`; this lemma =
  the integral norm-one subset (a sufficient-membership statement, not the full
  domain characterisation).
- **Ambient field:** literature ranges `Q_p` → finite extensions → `C_p`; this
  file = any complete ultrametric `ℚ_p`-algebra `L` (already very general).
Disagreement with the literature: **none** — the lemma is a correct, standard
sufficient condition; it is simply *narrower than* the full-domain statement the
literature ultimately reaches, because it is tailored to the consumers in this
project.

Signal: the literature search did **not** return any pre-existing *named* result
or any *library* (mathlib or otherwise) that packages this exact predicate. It is
a standard textbook intermediate step, not a citable standalone theorem — which
biases away from `YES-add-as-is` (no identifiable mathlib gap that this precise
statement, as opposed to the whole construction, fills) and toward NO/BORDERLINE.

---

### Generality analysis — `extLogDomain_of_integral_norm_one`

Literature-standard form (from Phase 3): the extended `log_p` is defined on the
*entire* multiplicative group `L^×` (resp. `C_p^×`); "membership in the domain" is
not the interesting statement classically because the domain is everything. The
nearest standard *sufficient-condition* form is "every unit of the ring of
integers (norm-one element) becomes a 1-unit after raising to a power, hence is in
the log domain".

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` | complete ultrametric `ℚ_p`-algebra (CompleteSpace omitted) | any complete extension of `Q_p`, or `C_p` | NO | already at/near the maximal natural generality; the proof needs the ultrametric inequality (used in `mul_mem_expBall`) and the `ℚ_p`-algebra norm. Not narrower than the literature. |
| 2 | `(hz : IsIntegral ℤ z)` | integral over `ℤ` | "is a unit of `O_L`" / "`‖z‖ ≤ 1`" | **borderline-yes** | Integrality is used only to make `ℤ[z]/p` finite (pigeonhole). The classically-cleaner hypothesis is `z ∈ O_L` (the ring of integers), or more abstractly `‖z‖ = 1` plus a completeness/local-field hypothesis that already forces a finite residue field — but in the stated generality (arbitrary complete ultrametric `ℚ_p`-algebra) `‖z‖ = 1` alone is NOT enough (no finiteness), so integrality is genuinely needed *here*. |
| 3 | `(hz1 : ‖z‖ = 1)` | norm exactly one | norm one (unit) | NO | exactly the unit condition; cannot weaken to `≤ 1` (then `z` could be a non-unit and the pigeonhole cancellation `‖z^i‖=1` fails). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** for the ambient field; **arguably
narrower than the classical full-domain statement** on the argument side (the
literature ultimately defines the log on *all* of `L^×`, of which this is a
sufficient-membership special case).
Number of weakening opportunities found: 1 soft one (hypothesis #2:
`IsIntegral ℤ` could be re-expressed as `z ∈ 𝓞 L` in a local-field setting, but
that is a *reformulation*, not a strict weakening, and in the present abstract
generality integrality is load-bearing for finiteness).
Proposed restatement (the literature target, were one to upstream the
construction): the full-domain development would instead state and use the
*total* extended logarithm `extLog : L → L` and its additivity, with this lemma
being one membership input among several. There is no single "more general
version of this lemma" to drop in; rather, the lemma is a leaf of a larger object
that mathlib lacks entirely.
Cost of any restatement: **MODERATE-to-EXPENSIVE** — it is inseparable from
porting the whole `padicLog` / `InExpBall` / `extLog` / `ExtLogDomain` API, which
does not exist in mathlib.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | Already fully typeclass-driven (`NormedAlgebra ℚ_[p] L`, `IsUltrametricDist L`). | — |
| 2 | sequences/metric → filters/topological? | no | The statement is a pure membership predicate; no limit/convergence notion to filter-ise. The `InExpBall` ball is already a clean rpow-free norm inequality. | — |
| 3 | construction → universal-property class? | **partially** | The *real* modernisation question is upstream of this lemma: should the extended log be packaged as a typeclass / bundled homomorphism (a `LogDomain` submonoid + a `MonoidHom`-flavoured `extLog`) rather than a junk-total `def` + ad-hoc `Prop`? `ExtLogDomain` as a bare `Prop` is the set-with-predicate idiom; mathlib would likely want a bundled submonoid. | a bundled domain would compose with mathlib's submonoid/`MonoidHom` API, additivity, and `IsLocalRing`/`Valued` machinery. |
| 4 | set-with-closure-predicate → bundled substructure? | **yes (upstream of this lemma)** | `ExtLogDomain p` is exactly "a set defined by a closure-style predicate" and the file already proves `ExtLogDomain.mul`, `ExtLogDomain.prod`, `inExpBall_one_sub_one` (the unit) — i.e. it is *morally a submonoid*. Mathlib idiom: make it a `Submonoid L` and this theorem becomes `z ∈ extLogSubmonoid p`. | lattice/closure API, `Submonoid.closure`, interaction with `padicLog` as a `MonoidHom` to the additive group. |
| 5 | vector-space/metric/field-specific → weaker typeclass? | no | Already at normed-field / ℚ_p-algebra generality, which is appropriate for a p-adic log. | — |
| 6 | 1-categorical → higher-categorical? | no | Not a categorical statement. | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure? | no | The `ℤ` in `IsIntegral ℤ` is intrinsic (the ring of integers / characteristic-0 integral closure); not a spurious concrete index. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it targets the surrounding construction, not
this individual theorem.** The genuinely mathlib-idiomatic move is to bundle
`ExtLogDomain p` as a `Submonoid L` (rows 3–4: the file already proves it is
closed under `*`, finite products, and contains `1`) and to present `extLog` as a
`MonoidHom` to the additive group. Were that done, `extLogDomain_of_integral_norm_one`
would restate as a *membership-in-submonoid* lemma. This is a real organisational
improvement (it would let the additivity lemmas `extLog_mul` / `extLog_prod` be
`MonoidHom.map_mul` / `map_prod`, composing with mathlib's monoid-hom API).
However, the cost is the whole-development port, and it does not change the
fundamental fact that **nothing in this dependency closure exists in mathlib
yet**. So the modern idiom informs *how* one would eventually upstream, not
whether *this lemma alone* is addable.
Real mathematical improvement (one sentence): bundling the domain as a submonoid
and `extLog` as a monoid hom would replace a junk-total `def` + bespoke `Prop` +
hand-rolled `mul`/`prod` closure lemmas with standard mathlib submonoid/monoid-hom
API — but only as part of upstreaming the entire extended-log construction.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is **theorem** (no definitional equalities or
typeclass-search paths introduced). (The diamond/defeq questions *would* matter
for the underlying `def ExtLogDomain` / `def extLog` if those were assessed; they
are out of scope for this single-theorem run.)

---

### Mathlib search-status: `extLogDomain_of_integral_norm_one`

[A] Lean-Finder    — natural-language "p-adic logarithm domain of integral unit"   n/a: Lean-Finder MCP not available in this session.
[B] Loogle         — JSON API: `IsIntegral ℤ _ → Finite _`; `‖_ ^ _ - 1‖`; `Algebra.adjoin ℤ _`   no hits for the composite forms; `Algebra.adjoin ℤ _` returned only cyclotomic-specific / general adjoin lemmas (`Algebra.adjoin_int`, `IsPrimitiveRoot.adjoinEquivRingOfIntegers`, …), none about an extended-log domain.
[C] LeanSearch     — natural language "p-adic logarithm on units"   n/a: LeanSearch web frontend is JS-only and returns no content via WebFetch; MCP not available. (Loogle JSON + grep substituted.)
[D] Grep mathlib src — `padicLog`, `extLog`, `ExtLogDomain`, `InExpBall`, `expBall`, `def padicLog`, `Padic.*exp`, over `.lake/packages/mathlib/Mathlib/`   **no hits for any p-adic logarithm.** The only `padicLog`/`PadicLog`-shaped hits are `PadicVal` (p-adic *valuation*) and real/complex `log` in `Harmonic/Int.lean`, `LSeries/Nonvanishing.lean` — false positives. `def padicLog` over all of Mathlib: **empty**.
[E] Name pattern   — `extLog`, `ExtLogDomain`, `logDomain`, `extendedLog`, `InExpBall`, `expBall` in mathlib   no hits.

Searched for both:
- the user's current form (`ExtLogDomain p z` for integral norm-one `z`) —
  impossible to exist: `ExtLogDomain` is project-defined and mathlib has no
  p-adic log;
- the literature-standard form (the extended `log_p` on `C_p^×` / its domain) —
  also absent: **mathlib has no p-adic logarithm or p-adic exponential at all**
  (confirmed: `Padics/` directory has `PadicVal`, `PadicNorm`, `Hensel`,
  `MahlerBasis`, etc., but no `Exp`/`Log`).

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard form). Mathlib lacks not only this lemma but the entire
concept (p-adic logarithm) it is stated in terms of. The *building blocks* of the
proof, however, are in mathlib generically: `Finite.exists_ne_map_eq_of_infinite`
(pigeonhole, used in `FieldTheory/PrimitiveElement.lean`), `Module.finite_of_finite`
/ f.g.-torsion finiteness (`RingTheory/Finiteness/`), `Ideal.Quotient.*`,
`spectralNorm` API (`Analysis/Normed/.../SpectralNorm.lean`) — these power the
project's *own* helper lemmas, but none assemble into our statement directly
(see Phase 6).

---

### Call sites — `extLogDomain_of_integral_norm_one`

Internal use count: **5** (within `PadicLFunctions`, NOT counting the declaring
file `ExtLog.lean`).
External-to-file callers: **1 distinct file** (`PadicLFunctions/ValuesAtOne.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ValuesAtOne.lean:979 | `extLogDomain_of_integral_norm_one p (((… hξ …).pow i).mul ((… hε …).pow c)).sub isIntegral_one)` — domain of `ξ^i ε^c − 1` |
| ValuesAtOne.lean:1080 | `extLog_mul p (extLogDomain_of_integral_norm_one p ((hεint.pow c).sub isIntegral_one) …) …` |
| ValuesAtOne.lean:1096 | `ExtLogDomain.mul p (extLogDomain_of_integral_norm_one p ((IsIntegral.neg isIntegral_one).pow k) …) hx` |
| ValuesAtOne.lean:1161 | `extLog_neg_one_pow_mul (extLogDomain_of_integral_norm_one p (((hεint.pow c).pow p).sub isIntegral_one) hnorm_pc)` |
| ValuesAtOne.lean:1754 | `extLogDomain_of_integral_norm_one p ((isIntegral_of_pow_eq_one … hε.pow_eq_one).pow c |>.sub isIntegral_one) hc1` |

(Line 1336 is a docstring mention, not a call.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using the
lemma?): **(none)** — `exists_pow_sub_one_norm_le` appears only inside
`ExtLog.lean`; every external consumer of "norm-one integral ⟹ in the log domain"
routes through `extLogDomain_of_integral_norm_one`. No bypassing re-derivation.

What this tells us: **K = 5 internal uses, no inline re-derivation** → this is a
*real API surface within the project*; consumers depend on it. By the Phase-6.0
table this is a genuine YES-leaning composability signal **within the project**.
The catch is that all consumers are *also* project-internal and *also* built on
the project-local `ExtLogDomain` — so the strong-API signal argues for keeping it
as a first-class lemma in the project (and for upstreaming the whole cluster
together), not for upstreaming this leaf in isolation.

### Composition check (Phase 6)

Can `extLogDomain_of_integral_norm_one` be derived from **mathlib** in ≤3 chained
calls? **No — vacuously**, because the goal `ExtLogDomain p z` is a project-defined
predicate that does not exist in mathlib; there is no mathlib decl producing it.

Attempt 1 (within the project): `⟨m·p^j, 0, z^(m·p^j), _, _, _⟩` after
`obtain ⟨m,…⟩ := exists_pow_sub_one_norm_le …` and
`obtain ⟨j,…⟩ := exists_pPow_pow_inExpBall …`.
  - Mathlib decls used: none directly — both `exists_*` lemmas are **project-local**
    (in `ExtLog.lean` / `PadicExp.lean`), and neither is in mathlib.
  - Result: succeeds *as the actual proof*, but it is not a mathlib composition;
    it is a 6-tuple existential assembled from two non-trivial project lemmas
    (one of which, `exists_pow_sub_one_norm_le`, is itself a ~30-line pigeonhole
    argument).
  - Notes: this is "a proof", not a ≤3-call mathlib composition per the Phase-6
    heuristics table (multiple `obtain`s + non-trivial reasoning + assembling an
    existential).

Conclusion: **NOT-COMPOSABLE** from mathlib. (It *is* composable from the project's
own `exists_pow_sub_one_norm_le` + `exists_pPow_pow_inExpBall`, but those are not
mathlib and are not trivial.)

---

## Verdict: `extLogDomain_of_integral_norm_one`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the extended Iwasawa-branch `log_p` and its
  domain are standard (Washington §5.1; Iwasawa; arXiv:1904.09850), but the
  literature defines it on *all* of `C_p^×`; this lemma is a *sufficient-
  membership* special case with no standalone name. No library (incl. the Lean-3
  formalization arXiv:2302.14491) packages it.
- Generality analysis (Phase 4): MAXIMALLY GENERAL in the ambient field; the
  modern-idiom check (4c) found a real improvement (bundle `ExtLogDomain` as a
  `Submonoid`, `extLog` as a `MonoidHom`) — but it targets the *surrounding
  construction*, not this leaf lemma.
- Mathlib search (Phase 5): **not in mathlib**, and mathlib has **no p-adic
  logarithm/exponential at all** — the conclusion type cannot exist there.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (the proof rests on
  two non-trivial project-local lemmas); but K = 5 internal call sites with no
  inline re-derivation = a real *project* API.

**Rationale:**

This theorem sits in an unusual spot. On the one hand, every "YES" precondition
is met in spirit: the mathematics is standard and genuinely useful, mathlib does
not have it, and it is not a cheap composition. On the other hand, the literal
question "should mathlib have *this declaration*" is ill-posed in isolation,
because its statement is written entirely in terms of project-local objects
(`ExtLogDomain`, which depends on `padicLog` and `InExpBall`) that mathlib lacks
*in their entirety*. You cannot upstream `extLogDomain_of_integral_norm_one`
without first upstreaming the whole extended-p-adic-logarithm development — and
*that* is a BIG decision (a new analytic object, with a real design choice about
bundling as a submonoid + monoid hom per Phase 4c) that is squarely a matter of
mathematical taste and library policy. The skill is explicitly forbidden from
making that call alone.

Two further signals push to BORDERLINE rather than a clean YES or NO. (1) The
*generality mismatch*: the literature's extended log lives on all of `C_p^×`,
whereas this is a sufficient condition for the integral-norm-one subset tailored
to the consumers `1 − ε_N^c` in RJW Thm 6.1(ii) — so even within a hypothetical
upstreaming, the "right" mathlib statement might be the full-domain construction
plus *separate* membership inputs, of which this would be one (possibly merged
with the cleaner `z ∈ 𝓞 L` hypothesis from Phase 4 row 2). (2) The *strong but
inward-facing API signal*: 5 internal uses, zero external/downstream consumers,
and an entirely project-local dependency closure — classic "genuinely useful, but
only inside its own development (so far)". That is the textbook BORDERLINE shape:
real content, but the upstreaming decision hinges on judgments (port the whole
log? bundle it how? which hypothesis?) the author must make.

**Numbered questions (≤5):**

1. **Scope of upstreaming.** Do you intend to contribute the *entire* extended
   p-adic logarithm development (`padicLog`, `InExpBall`, `extLog`,
   `ExtLogDomain`, the `mul`/`prod`/additivity API) to mathlib? If **no**, this
   lemma stays project-local and the verdict collapses to "keep as-is, do not
   PR". If **yes**, proceed to Q2–Q4.

2. **Bundling (Phase 4c).** If upstreaming, should `ExtLogDomain p` be a bare
   `Prop` (as now) or a bundled `Submonoid L` with `extLog` as a `MonoidHom` to
   the additive group? The file already proves closure under `*`, finite
   products, and membership of `1` — i.e. it is morally a submonoid. Mathlib
   would very likely require the bundled form. Is that restructuring acceptable?

3. **Hypothesis idiom (Phase 4 row 2).** Should the membership hypothesis be
   `IsIntegral ℤ z` (current — load-bearing for finiteness in the abstract
   setting) or the local-field-idiomatic `z ∈ 𝓞 L` / "`z` is a unit of the ring
   of integers"? In a local-field setting these coincide; the latter is more
   mathlib-idiomatic but needs the local-field typeclasses.

4. **Target generality.** Mathlib's natural target is the full extended log on
   `L^×` (or `C_p^×`) with this as one of several *sufficient* membership inputs.
   Are you content for this specific lemma to become a corollary/membership-lemma
   of that construction (rather than a headline result)?

5. **Audience.** Is the extended Iwasawa-branch logarithm something you expect
   *other* mathlib developments (outside p-adic L-functions) to consume? A "yes"
   strengthens the case for upstreaming the cluster; a "no" suggests keeping it
   local to this project.

Next action: user answers Q1 first. If Q1 is "no", keep `extLogDomain_of_integral_norm_one`
as a project-local lemma — no mathlib PR. If Q1 is "yes", the realistic path is a
**`/develop`-scale upstreaming of the whole extended-log cluster** (not a single
PR for this lemma); re-run `/mathlibable` on the *bundled* `ExtLogDomain` /
`extLog` defs first (def-first), since this theorem's fate is downstream of those
design decisions. Answers to Q2–Q5 then determine the restated form before any
PR.

---

## Next step

User answers Q1. If "no": keep project-local, do not PR. If "yes": treat as a
`/develop`-scale port of the entire extended-p-adic-logarithm development —
assess the bundled `ExtLogDomain` / `extLog` *defs* with `/mathlibable` first
(def-first), settle Q2–Q5 (submonoid bundling, hypothesis idiom, full-domain
target), then PR the cluster as a unit with this lemma as a membership corollary.
