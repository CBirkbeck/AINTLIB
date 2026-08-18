# /mathlibable report — `Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH`

_Step-9 mathlibable assessment (single declaration). Generated 2026-06-18._

### Baseline (Phase 0)
- lake build:               not run (pin `d90090f`/rc2; local build stale — reasoned from source per task note)
- decl `Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Abelian.lean:851`
- qualified name:           ✓ VERIFIED — `namespace Chebotarev` opens at line 56, `end Chebotarev` at 1595; decl at 851 ⇒ `Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Chebotarev's theorem, abelian case — density of primes of `K` unramified in abelian `L/K` with Frobenius `σ` is `1/|Gal(L/K)|`, proved by cyclotomic crossing.

---

### Statement (Phase 1)

`liminf_density_S_sigma_ge_card_H_n_div_GH` is a **theorem** stating the following:

Let `L/K` be an abelian Galois extension of number fields, `G = Gal(L/K)`, `σ ∈ G`, and `m ≥ 1`
an integer with `m % 4 ≠ 2` and `gcd(|disc L|, m) = 1`. Write `H = (ℤ/m)ˣ` (the unit group whose
order is `|H| = φ(m)`), and `H_n = {τ ∈ (ℤ/m)ˣ : |G| ∣ ord(τ)}`. Then the **lower Dirichlet
density** of the set `S_σ` of primes `𝔭` of `𝓞 K`, unramified in `L`, with Frobenius conjugacy
class `{σ}`, is bounded below:

  `|H_n| / (|G| · |H|) ≤ δ_inf(S_σ)`,

where `δ_inf(S_σ) = liminf_{s ↓ 1} (Σ_{𝔭 ∈ S_σ} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`.

This is **Sharifi, *Algebraic Number Theory*, §7.2.2 Step 2** (docstring source quote, p. 144:
"δ_inf(S_σ) ≥ |H_n|/(|G|·|H|)"). It is the per-modulus partial lower bound; the consumer
`liminf_ratio_ge_inv_card_G` drives `m` along admissible primes so `|H_n|/|H| → 1`, yielding
`δ_inf ≥ 1/|G|`.

Variables / typeclasses (Lean side):
- `K L : Type*` `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` — the number-field extension.
- `[hAb : IsMulCommutative Gal(L/K)]` — abelian Galois group `G`.
- `σ : Gal(L/K)` — the fixed automorphism.
- `m : ℕ` — the cyclotomic crossing modulus.

Hypotheses (Lean side):
- `_hm : 1 ≤ m` — nontrivial modulus.
- `hm4 : m % 4 ≠ 2` — feeds the cyclotomic case (avoids the degenerate `2·odd` modulus).
- `hcop : ((NumberField.discr L).natAbs).Coprime m` — linear-disjointness of `L` and `K(μ_m)` over `K` (everywhere-unramified intersection, via `discr_dvd_discr`).

Conclusion (math): `|H_n| / (|G| · |H|) ≤ δ_inf(S_σ)`.

Conclusion (Lean):
```
(Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ) / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ))
  ≤ Filter.liminf (fun s : ℝ ↦ primeIdealZetaSum {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      / primeIdealZetaSum (Set.univ) s) (𝓝[>] 1)
```
(Note: the RHS is `HasLowerDirichletDensity` unfolded — the proof uses `rfl` to identify it with `δ_inf(S_σ)`.)

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A proof-internal partial-bound step (Sharifi §7.2.2 *Step 2*), not under `## Main results`, not named after a person/place, introduces no new structure. The Main result is `chebotarev_abelian`; this is a lemma three layers below it.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: ~24 substantive lines (`classical … exact hmono`).
One-liner verdict: **MULTI-LINE** — `set` declarations, `obtain` destructuring, several `have`s, a `rw … at`, then `exact`. The Phase-2b exemption table is therefore n/a.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Chebotarev density abelian case proof cyclotomic crossing lower bound liminf density Sharifi"          | partial | the *crossing argument* is standard (Di Meglio, Triantafillou, MIT 18.785 LN28, Stevenhagen–Lenstra) | the bound `δ_inf ≥ |H_n|/(|G||H|)` appears only **inside** the proof; no standalone name |
|  2 | WebSearch (general form / abstract ingredients) | "Dirichlet density lower density liminf disjoint union finite subfamily bound proof number field"        | yes  | Dirichlet density is **NOT** finitely additive (only sub-additive); lower density monotone under inclusion (Wikipedia, EoM, Kedlaya ANT ch.4) | confirms the two abstract facts are textbook; the *combined* per-m bound is not |
|  3 | WebSearch (named-after / aliases)| "mathlib4 Chebotarev density theorem Dirichlet density prime ideals Frobenius formalization"            | partial | weak Chebotarev: density of `Frob = C` is `|C|/|G|`; no mathlib formalisation found | confirms the *end* theorem is named; this *intermediate step* is not |
|  4 | ChatGPT MCP                      | self-contained Q: is the bound standalone? are the reusable facts (a) disjoint-union additivity + (b) lower-density monotonicity? | **n/a** | — | Codex backend **down** (both `gpt-5.4` and `gpt-5.4-mini` returned `Codex failed`); fallback channels used instead, per task note |
|  5 | Local references                 | `ls projects/Chebotarev/.mathlib-quality/references/`, `ls refs/Chebotarev/`                            | **n/a** | (no references dir; `refs/` absent in this checkout) | recorded n/a — dir absent |
|  6 | nLab                             | "Dirichlet density" / Chebotarev density theorem                                                       | no   | nLab has no dedicated "Dirichlet density of a finite disjoint union" / no standalone for this bound | not a categorical concept; nLab's Chebotarev coverage is the statement, not this step |
|  7 | nCatLab (if categorical)         | —                                                                                                      | **n/a** | — | not a categorical concept (analytic density inequality) |
|  8 | Stacks Project (if alg geom)     | Chebotarev / Dirichlet density                                                                          | **n/a** | — | not an algebraic-geometry / scheme-theoretic concept; Stacks has no Dirichlet-density tag |
|  9 | MathOverflow / Math.StackExchange| "Dirichlet density" generality, additivity of density                                                  | yes  | reaffirms density additivity fails in general / lower density is monotone; nothing about this *combined* bound as a named lemma | via search aggregation (results #1–#3) |
| 10 | recent arXiv (last 5 years)      | effective Chebotarev / supplement to Chebotarev (2210.13412, 2508.09480, 1703.08194, 1811.07084)        | partial | modern work is on *effective/quantitative* Chebotarev with error terms — orthogonal to this qualitative liminf step | none isolates this bound as a reusable lemma |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (specific
Sharifi-step / abstract density ingredients / named-theorem aliases); ChatGPT MCP was attempted
twice and recorded `n/a — backend down` with the specific failure; local refs checked (absent →
n/a); nLab, nCatLab, Stacks, MO/MSE, arXiv each checked or n/a with reason.

### Literature summary (Phase 3)

Concept identified as: the **Step-2 partial lower bound in the cyclotomic-crossing proof of the
abelian Chebotarev density theorem** (Sharifi §7.2.2).
Sources agree on the standard form: **yes** — but the agreement is precisely that *this is an
internal step, not a standalone theorem*. Every reference (Di Meglio, Triantafillou, MIT 18.785,
Stevenhagen–Lenstra, Sharifi) presents the inequality only *within* the proof of Chebotarev; none
names it.
Most general standard form: the *abstract* reusable facts the step rests on are two textbook
properties of Dirichlet density —
  (a) **finite-disjoint-union additivity**: the Dirichlet density of `⊔_{i<N} S_i` of pairwise-
      disjoint sets each of density `d` is `N·d`;
  (b) **monotonicity of lower density under inclusion**: `S ⊆ T ⇒ δ_inf(S) ≤ δ_inf(T)`.
Generality dimensions where the literature varies:
  - the **density notion**: natural vs. Dirichlet vs. analytic — for *Dirichlet*, only sub-additivity
    holds in general; the *finite-disjoint* additivity used here is the special case that does hold.
  - the **base object**: stated for prime ideals of a number field; the two abstract facts (a)/(b)
    are really facts about `liminf`/`limsup` of a ratio of partial sums and would generalise to any
    global field.
Disagreement with the literature: **none** — the Lean form is a faithful transcription of Sharifi's
Step 2 (the docstring even quotes p. 144). The hypotheses `m % 4 ≠ 2` and `coprime disc` are the
proof's *admissibility* conditions, exactly as in the source.

---

### Generality analysis — `liminf_density_S_sigma_ge_card_H_n_div_GH` (Phase 4)

Literature-standard form (from Phase 3): there is **no** standalone literature form to weaken
*toward* — the statement is an internal step. The relevant generality question is whether the
hypotheses are stronger than the proof needs.

| # | Parameter / hypothesis                        | Current Lean form           | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------|-----------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K]`, `[NumberField L]`          | number fields               | number field (could be global field) | NO (in practice) | the whole `primeIdealZetaSum` / `frobeniusClass` / `UnramifiedIn` API is built for `𝓞 K` of a `NumberField`; "generalising to global fields" means rebuilding that API, not weakening this lemma |
| 2 | `[IsGalois K L]` + `[IsMulCommutative …]`     | abelian Galois              | abelian Galois                   | NO                  | the crossing argument *is* the abelian case; non-abelian uses a different reduction |
| 3 | `hm4 : m % 4 ≠ 2`                              | admissibility condition     | same (cyclotomic-case feeder)    | NO                  | a **correctness** hypothesis fed to `exists_cyclotomicCrossing_fibres`, not a generality dial; dropping it breaks the crossing |
| 4 | `hcop : (disc L).natAbs.Coprime m`            | linear-disjointness condition | same (`discr_dvd_discr`)        | NO                  | a **correctness** hypothesis (everywhere-unramified intersection); not a generality dial |
| 5 | conclusion uses `liminf` (lower density)      | `δ_inf`                     | `δ_inf` (Sharifi's notation)     | n/a                 | lower bound on `liminf` is exactly what the consumer needs; an `=` is false at finite `m` |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** for what it is — every hypothesis is either structural
(number field / abelian Galois) or a genuine proof-correctness condition (`hm4`, `hcop`), none is a
loosenable generality dial.
Number of weakening opportunities found: **0** (mechanical weakenings).
Proposed restatement: none.
Cost of restatement: n/a.

This MAXIMALLY-GENERAL verdict is *not* a point in favour of upstreaming — it means the lemma is
already pinned to the narrowest correct hypotheses for a Chebotarev-internal step. Its generality is
exactly "as general as Sharifi Step 2", which is to say project-specific.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                                | no       | — | already typeclass-driven (`[IsGalois]`, `[IsMulCommutative]`); the `m`-admissibility cannot be a typeclass (it's `m`-dependent data) |
|  2 | sequences/metric → filters/nets?                                                                          | partial-but-irrelevant | — | the proof already uses `Filter.liminf` over `𝓝[>] 1` — the modern filter idiom is **already in use** |
|  3 | construct an object → universal-property class?                                                          | no       | — | nothing is constructed; it's a density inequality |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | — | `S_σ` is a plain set of ideals; no lattice structure to bundle |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                                          | no       | — | already at `NumberField`; weakening means a *new* global-field API, not a typeclass swap |
|  6 | 1-categorical → higher-categorical?                                                                       | no       | — | not categorical |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive group/monoid?                                                 | no       | — | the `liminf` is over `ℝ` because `s ↓ 1` is intrinsically real (the Dirichlet-series abscissa); not an index to abstract |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement already uses mathlib's contemporary `Filter.liminf` /
`𝓝[>] 1` idiom for the density. There is no organisational redundancy to eliminate by restating: the
content is genuinely a Chebotarev-internal inequality whose vocabulary (`primeIdealZetaSum`,
`HasLowerDirichletDensity`, `frobeniusClass`, `UnramifiedIn`) is **project-defined** and absent from
mathlib. "Modernising" would just rename project notions to other project notions.

---

### Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (introduces no definitional equalities or typeclass-search
paths).

---

### Mathlib search-status: `Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH` (Phase 5)

Five-method search. (`lean_loogle` / `lean_leansearch` MCP tools were not available in this session;
substituted direct grep over the pinned mathlib source `.lake/packages/mathlib/Mathlib/` + WebSearch
against the mathlib docs, which is the authoritative ground truth.)

```
[A] Lean-Finder       "Chebotarev density", "Dirichlet density lower bound prime ideal"   no hits (no mathlib Chebotarev/Dirichlet-density API exists to find)
[B] Loogle (≈grep)    grep `liminf_density|density_S_sigma|frobeniusClass` over Mathlib/   no hits  (empty)
[C] LeanSearch (≈Web) "mathlib4 Chebotarev density theorem Frobenius prime ideal"          no hits  (WebSearch found NO mathlib formalisation)
[D] Grep mathlib src  `chebotarev|dirichletDensity|DirichletDensity` over Mathlib/         no hits  (empty)
                      `density.*[Uu]nion|biUnion.*[Dd]ensity` over Mathlib/NumberTheory/   no hits  (mathlib has NO density-additivity API)
[E] Name pattern      `theorem.*[Cc]hebotarev|chebotarev_abelian` over Mathlib/            no hits  (empty)
```

Searched for both:
  - the user's current form (the combined `|H_n|/(|G||H|) ≤ δ_inf` bound) — absent.
  - the literature-standard abstract ingredients (finite-disjoint-union density additivity;
    lower-density monotonicity) — **also absent**: mathlib has no Dirichlet-density notion at all.
    The *closest* mathlib content is `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` (Dirichlet's
    theorem on primes in arithmetic progressions — a **different** result, no density set-function),
    and the purely-abstract `Filter.liminf_le_liminf` (`Mathlib/Order/LiminfLimsup.lean:205`), which
    is the order-theoretic skeleton beneath fact (b) but says nothing about density.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard abstract form).
Mathlib has neither the combined bound, nor a Dirichlet-density set-function, nor a
density-of-disjoint-union additivity lemma, nor a Chebotarev density theorem.

---

### Call sites — `Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH` (Phase 6.0)

Internal use count: **1** (within the Chebotarev project, excluding the declaring lines).
External-to-file callers: **0 distinct files** (sole consumer is in the *same* file).

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| Abelian.lean:1349              | `have hbnd := liminf_density_S_sigma_ge_card_H_n_div_GH K L σ (m k) (hm1 k) (hm4 k) …` (inside `liminf_ratio_ge_inv_card_G`) |

(Lines 107/149/1304 are *docstring mentions*, not call sites.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - (none) — the bound is derived in exactly one place and consumed in exactly one place.

**What the pattern tells us:** K = 1 internal use, 0 external, single consumer. Per the Phase-6.0.1
table this is the "possibly the wrong abstraction — could be inlined / lean toward NO-composable"
signal. It is a single-consumer glue step extracted for readability of the
`liminf_ratio_ge_inv_card_G` proof, not a reused API surface.

### Composition check (Phase 6)

Can `liminf_density_S_sigma_ge_card_H_n_div_GH` be derived in ≤3 chained calls?

Attempt 1 (from **project** helpers — what the proof actually does):
  `(hasDirichletDensity_biUnion_const t S c hpd' hd).hasLower.mono hUsub hSσlow`, after
  `exists_cyclotomicCrossing_fibres K L σ m _hm hm4 hcop` produces the disjoint family `S` and the
  `htcard` arithmetic rewrite `(t.card)•c = |H_n|/(|G||H|)`.
  - Decls used: `exists_cyclotomicCrossing_fibres` (PROJECT), `hasDirichletDensity_biUnion_const`
    (PROJECT, `private`), `HasDirichletDensity.hasLower` (PROJECT), `HasLowerDirichletDensity.mono`
    (PROJECT).
  - Result: **succeeds** — but every block is a **project** decl, plus a `Finset.card_univ` /
    `smul_eq_mul` / `div_eq_mul_inv` arithmetic step. There is essentially no proof content left
    once those are in hand; it is genuine glue.
  - Notes: this is the very reason it reads as a one-consumer helper.

Attempt 2 (from **mathlib** primitives only — the bucket-relevant question):
  - Impossible. Mathlib supplies neither `HasDirichletDensity`, nor `primeIdealZetaSum`, nor the
    disjoint-union additivity, nor `frobeniusClass`, nor the cyclotomic crossing. The only mathlib
    primitive in reach is `Filter.liminf_le_liminf` — which gives **fact (b)** abstractly but
    requires the entire Dirichlet-density scaffolding (absent from mathlib) to even state the goal.
  - Result: **fails** from mathlib alone.

Conclusion: **NOT-COMPOSABLE from mathlib.** (It *is* a ≤4-call composition from **project**
helpers, which is a project-internal observation, not a mathlib-composability one.)

---

## Verdict: `Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the bound is uniformly an **internal step** of the abelian-Chebotarev proof (Sharifi §7.2.2 Step 2); no standalone named theorem; the genuinely-reusable substance is the two abstract density facts, not this combined inequality.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for a Chebotarev-internal step — 0 loosenable hypotheses (`hm4`, `hcop` are correctness conditions); no modern-idiom restatement (already uses `Filter.liminf`/`𝓝[>] 1`).
- Mathlib search (Phase 5): **not in mathlib** — and neither is *any* Dirichlet-density set-function, density-additivity lemma, or Chebotarev theorem; closest is `PrimesInAP` (different result).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (composable only from project helpers, single internal call site).

**Rationale (why BORDERLINE rather than a clean NO or YES):**

This declaration is a single-consumer glue step (K = 1, 0 external uses) that bakes in the entire
Chebotarev-specific construction (`exists_cyclotomicCrossing_fibres`, `frobeniusClass`,
`UnramifiedIn`) and whose conclusion is phrased in a **project-defined** vocabulary
(`HasLowerDirichletDensity` / `primeIdealZetaSum`) that **does not exist in mathlib**. As stated, it
is plainly *not* mathlib-worthy: it is too narrow (one call site, a proof-internal partial bound),
and it cannot even be *expressed* in mathlib today. That pushes hard toward NO.

But the two clean NO buckets do not fit the evidence, and that mismatch is the whole reason this is
BORDERLINE:
- **NO-mathlib-has-it** is false — Phase 5's conclusion was "not in mathlib", in *any* form.
- **NO-composable-from-mathlib** is *technically* false too: the gate requires Phase 6 to be
  COMPOSABLE *from mathlib*, and it is NOT (the composition only works from project helpers). The
  "delete it and inline at the K call sites" refactor that the NO-composable bucket prescribes would
  inline `hasDirichletDensity_biUnion_const` + `HasLowerDirichletDensity.mono` — i.e. inline
  *project* API, not mathlib API. That is a reasonable **project-internal** cleanup decision, but it
  is not the "mathlib already gives you this" claim that NO-composable asserts.

So the honest reading is: *this specific lemma* should not go to mathlib (everyone can agree on
that), but the verdict the skill is really being asked for collapses to a **judgment call the
skill cannot make alone** — namely whether the *underlying Dirichlet-density framework* (the
`HasDirichletDensity` / `HasLowerDirichletDensity` def, the finite-disjoint-union additivity
`hasDirichletDensity_biUnion_const`, the monotonicity `HasLowerDirichletDensity.mono`, and the
`frobeniusClass` / `UnramifiedIn` API) is something AINTLIB intends to upstream to mathlib. If yes,
the *reusable* pieces (the density def + its additivity/monotonicity lemmas) are strong YES
candidates on their own and this lemma stays a project-internal application of them. If no (the
framework stays project-local), this lemma should simply be left as the readable single-use helper
it is, or inlined into `liminf_ratio_ge_inv_card_G`. Either way the decision is about the
*framework*, not this lemma — which is exactly a human/project-policy call.

**Refactor-actionable detail.** This lemma is *not* itself a refactor target. The actionable
follow-up is at the framework level: run `/mathlibable` on the **reusable primitives**
— `Chebotarev.HasLowerDirichletDensity` (def, `Density.lean:89`),
`Chebotarev.HasDirichletDensity` (def, `Density.lean:64`),
`Chebotarev.hasDirichletDensity_biUnion_const` (currently `private`, `Abelian.lean:108`), and
`Chebotarev.HasLowerDirichletDensity.mono` (`Density.lean:256`). Those are where the genuine
mathlib-worthiness question lives. This combined bound is a faithful, correctly-stated, but
intentionally project-specific Chebotarev step that should ride along *inside* AINTLIB regardless of
what happens to the framework.

**Numbered questions for the human (≤5):**
  1. Does AINTLIB intend to upstream a **Dirichlet-density framework** (`HasDirichletDensity` /
     `HasLowerDirichletDensity` + the additivity/monotonicity lemmas) to mathlib? (If yes, assess
     *those* for mathlib; this lemma then stays a project-internal application.)
  2. If the framework is *not* upstreamed, do you want this single-use helper **inlined** into its
     sole consumer `liminf_ratio_ge_inv_card_G` (Abelian.lean:1307), or kept as a named readable
     step? (Either is fine; it is purely a project-readability choice — no mathlib action.)
  3. Confirm: you agree that *this specific combined bound* (which bundles the full Chebotarev
     cyclotomic-crossing construction) is **not** a mathlib target in its own right, independent of
     the framework question?

**Next action:** answer Q1 (the framework decision drives everything). If Q1 = yes, run
`/mathlibable Chebotarev.HasLowerDirichletDensity` and `/mathlibable
Chebotarev.hasDirichletDensity_biUnion_const` to assess the reusable primitives. If Q1 = no, treat
this lemma as project-internal (optionally inline per Q2); no mathlib PR.

---

## Next step

Answer Q1 — whether AINTLIB upstreams the Dirichlet-density framework. That decision, not this
lemma, is the real mathlibable question; this combined bound is a correctly-stated, intentionally
project-specific Chebotarev §7.2.2 Step 2 and is not a standalone mathlib target.
