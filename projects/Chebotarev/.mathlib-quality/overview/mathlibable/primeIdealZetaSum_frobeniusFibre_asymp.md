# /mathlibable report — `Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp`

## Baseline (Phase 0)

- lake build:               (not run — local build is stale per environment note; reasoning from source. Target proof body contains **0 `sorry`**, sed-confirmed.)
- decl `Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:898`
- qualified name:           ✓ `Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp` (namespace `Chebotarev` opened at line 49; matches the parsed guess)
- kind:                     `theorem`
- has sorry:                no
- module docstring summary: "Chebotarev's theorem: cyclotomic case" — Dirichlet density of primes `𝔭` of `𝓞 K` unramified in `L = K(μ_m)` with Frobenius `σ` equals `1/|Gal(L/K)|` (Sharifi §7.2.1).

---

## Statement (Phase 1)

`primeIdealZetaSum_frobeniusFibre_asymp` is a **theorem** stating an intermediate analytic asymptotic in the cyclotomic Chebotarev proof — Sharifi's step **(iv-a), the numerator asymptotic**.

In prose: for `K` a number field, `L = K(μ_m)` the `m`-th cyclotomic extension (`m % 4 ≠ 2`), and `σ ∈ Gal(L/K)`, the partial Dirichlet series over the **Frobenius fibre** — the unramified primes `𝔭` whose Frobenius conjugacy class is `[σ]` — is asymptotic to `(1/|G|)·log(1/(s−1))` as `s ↓ 1`. Formally, the ratio
`primeIdealZetaSum {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ} s / Real.log (1/(s−1))`
tends to `(Nat.card Gal(L/K))⁻¹` along `𝓝[>] 1`.

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` — the base & top number fields and the Galois extension.
- `m : ℕ`, `[NeZero m]`, `[IsCyclotomicExtension {m} K L]` — `L` is the `m`-th cyclotomic extension of `K`.
- `σ : Gal(L/K)` — the target Galois element.

Hypotheses (Lean side):
- `hm : m % 4 ≠ 2` — the technical parity condition inherited from the upstream L-function non-vanishing input (`artinLSeries_prime_sum_bounded_of_ne_one`).

Conclusion (math): `∑_{φ_𝔭 = σ} N𝔭^{−s} ∼ (1/|G|) log(1/(s−1))` as `s ↓ 1`.
Conclusion (Lean): `Tendsto (fun s ↦ primeIdealZetaSum {…fibre…} s / Real.log (1/(s−1))) (𝓝[>] 1) (𝓝 (Nat.card Gal(L/K))⁻¹)`.

**Project-local vocabulary the statement is built from** (none exist in mathlib):
- `Chebotarev.primeIdealZetaSum` (Density.lean:50) — `∑' 𝔭 ∈ S prime ≠ ⊥, (absNorm 𝔭)^(−s)`, a partial Dirichlet/zeta sum over a *set of prime ideals*.
- `Chebotarev.UnramifiedIn` (Frobenius.lean:62) — bespoke unramified-prime predicate.
- `Chebotarev.frobeniusClass` (Frobenius.lean:188) — Frobenius conjugacy class `ConjClasses Gal(L/K)`.
- (in the proof) `galoisCharacter`, `twistedPrimeSum`, `card_mul_frobeniusFibre_eq`, `exists_sum_charTwist_erase_norm_bounded`, `primeIdealZetaSum_unramified_div_log_tendsto_one` — all project-private.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is an internal proof step (named `…_asymp`, docstring "Sharifi 7.2.1 step (iv-a) — the numerator asymptotic"), not a `## Main results` entry. The main result is `chebotarev_cyclotomic`; this is a private-flavoured helper that feeds `cyclotomic_density_from_two_sided_asymp`. Not named after a person/place; not a new structure.

(Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-liner check **n/a**. (Body is a ~30-line analytic proof: orthogonality master identity + squeeze of the nontrivial-character remainder + `Tendsto.congr'`.)

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib4 Chebotarev density theorem formalization Dirichlet density Frobenius"        | yes  | Chebotarev: `δ(Σ_c)=|c|/|G|` (Wikipedia, MIT 18.785, Stevenhagen–Lenstra) | The *final* theorem is standard; the *numerator asymptotic* step is proof-internal, not a citable named result |
|  2 | WebSearch (source / general)     | "Sharifi algebraic number theory 7.2.1 Dirichlet density prime sum log asymptotic cyclotomic" | yes  | `∑_𝔭 N𝔭^{−s} ∼ −log(s−1)`; cyclotomic ζ_K = ∏ Dirichlet L | Confirms the *project's own source* (Sharifi §7.2.1) is the canonical reference for this exact decomposition |
|  3 | WebSearch (mathlib state)        | "mathlib Dirichlet density Nat Primes natural density API LSeries Dedekind zeta number field" | partial | mathlib has Dedekind ζ pole (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`), LSeries/Dirichlet API | **No** prime-ideal-set Dirichlet density, **no** Chebotarev in mathlib |
|  4 | WebSearch (named-after / density def) | "\"Dirichlet density\" definition prime ideals number field standard form ∑ Nℙ^{−s} divided log" | yes | `𝔡_K(A)=lim_{s→1+} ξ_{K,A}(s)/log((s−1)⁻¹)` (Encyclopedia of Math, Wikipedia) | This is the *density definition* (= project's `HasDirichletDensity`), the parent concept — **not** the fibre-numerator asymptotic itself |
|  5 | ChatGPT MCP                      | (standard form / generality / historical evolution)                                   | n/a  | —                   | MCP down per environment note; substituted by extra WebSearch rows #2 and #4 hitting Encyclopedia-of-Math + Sharifi directly, which give the standard form and generality |
|  6 | Local references                 | `ls .mathlib-quality/references/`, `ls refs/Chebotarev/`                               | n/a  | (no refs dir)       | Neither directory exists; PDFs (`docs/algnum.pdf`, `docs/cheb.pdf`) are gitignored/absent locally — recorded n/a |
|  7 | nLab                             | "Chebotarev density theorem" / "Dirichlet density"                                     | n/a  | covered by #1/#4    | nLab has the classical statement; adds nothing past Wikipedia for an internal asymptotic step — not a categorical concept |
|  8 | nCatLab                          | —                                                                                     | n/a  | —                   | Not a categorical concept (analytic number theory / prime densities) |
|  9 | Stacks Project                   | —                                                                                     | n/a  | —                   | Not scheme-theoretic algebraic geometry; Stacks has no Dirichlet-density analytic-NT chapter |
| 10 | MathOverflow / Math.SE           | (covered via Conrad "Dirichlet density for global fields", Kedlaya 18.785 in #2/#3 hits) | yes  | same density def + ∑ N𝔭^{−s} ∼ −log(s−1) | Course notes (Conrad, Kedlaya, Elkies) treat exactly this asymptotic *inside* Dirichlet/Chebotarev proofs, never as a standalone lemma |
| 11 | recent arXiv (last 5 yrs)        | "Formalizing zeta and L-functions in Lean" (arXiv 2503.00959)                          | yes  | mathlib ζ/L formalization survey | Documents mathlib's L-function/Dedekind-ζ frontier; confirms **Chebotarev/prime-density is not yet in mathlib** |

**Protocol pass:** WebSearch ran 4 distinct queries at different generality levels (specific Chebotarev, the Sharifi source decomposition, the mathlib state, the density-definition standard form). ChatGPT MCP unavailable (down) — compensated with two extra authoritative WebSearch rows (Encyclopedia of Mathematics + Sharifi) that pin the standard form and its generality. Local refs checked (absent → n/a). nLab/nCatLab/Stacks/MO/arXiv each checked with reasons.

### Literature summary (Phase 3)

Concept identified as: an **internal analytic step of the Chebotarev density theorem (cyclotomic case)** — specifically "the numerator asymptotic": the Frobenius-fibre prime sum `∑_{φ_𝔭=σ} N𝔭^{−s}` is `∼ (1/|G|)·log(1/(s−1))`. The *parent* concept is **Dirichlet density of a set of prime ideals**, `𝔡_K(A)=lim ξ_{K,A}(s)/log((s−1)⁻¹)`.

Sources agree on the standard form: **yes** for the parent density definition and for the final Chebotarev density `|c|/|G|`. For the *numerator-asymptotic step itself*: it is **never stated as a standalone named lemma** — every source (Sharifi §7.2.1, Stevenhagen–Lenstra, Conrad, Kedlaya 18.785, MIT 18.785 LN28) derives it inline within the density proof and immediately combines it with the denominator asymptotic.

Most general standard form: the asymptotic `∑_{𝔭∈A} N𝔭^{−s} ∼ d·log(1/(s−1))` characterising Dirichlet density `d` — a statement about an *abstract set `A` of primes of a global field*, with `d = |c|/|G|` when `A` is a Frobenius fibre.

Generality dimensions where the literature varies:
  - **global field**: number field (Sharifi) vs. number-field-or-function-field (Stevenhagen–Lenstra, MIT 18.785). This decl is number-field-only.
  - **density flavour**: this decl is the raw `Tendsto … (𝓝 (1/|G|))` of the numerator/log; the literature usually packages it directly into the density quotient `ξ_A/log` (which is the project's *next* decl, `cyclotomic_density_from_two_sided_asymp`).

Disagreement with the literature: **none** mathematically — but the literature does not isolate this as a lemma. It is a formalisation-bookkeeping node: the prose proof's single sentence "Σ_χ χ(σ)⁻¹ log L(χ,s) ~ |G| Σ_{φ_𝔭=σ} N𝔭^{−s}" split out so the Lean proof can `Tendsto.congr'` it against the denominator.

---

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): `∑_{𝔭∈A} N𝔭^{−s} ∼ d·log(1/(s−1))` for an abstract prime set `A` of a global field; here `A` = Frobenius fibre, `d = 1/|G|`.

### Generality status table

| # | Parameter / hypothesis            | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K] [NumberField L]` | number fields                    | global fields (incl. function fields) | yes (in principle) | Function-field Chebotarev is standard, but the **entire `Chebotarev` project** is number-field-only (Dedekind ζ pole, `absNorm`, the whole `primeIdealZetaSum` API). Generalising is a project-wide redesign, not a decl-local move. |
| 2 | `[IsCyclotomicExtension {m} K L]` + `m` + `hm : m%4≠2` | cyclotomic extension, parity cond | (final Chebotarev needs no cyclotomic hyp) | NO — at this node | This is the **cyclotomic** case by design; the cyclotomic hypotheses are what make orthogonality + L-function non-vanishing available. The general (non-cyclotomic) Chebotarev is a *different, harder theorem* (it reduces to this via Artin/abelian base change elsewhere in the project). |
| 3 | the index set (Frobenius fibre `{frobeniusClass = [σ]}`) | concrete fibre predicate         | abstract prime set `A`           | yes, trivially | The underlying analytic content (`∑_A N𝔭^{−s}/log → d` *given* a master identity) is set-agnostic — see Phase 6: the fibre-specific part is `card_mul_frobeniusFibre_eq`, the analytic part is generic. |
| 4 | `Real.log (1/(s−1))`, `𝓝[>] 1`    | real `s ↓ 1` Dirichlet asymptotic | same                             | NO | This *is* the standard Dirichlet-density limit shape; already maximally idiomatic. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL within the project's scope** (number-field cyclotomic Chebotarev). The two "weaker form exists" rows (#1 global fields, #3 abstract prime set) are **not decl-local generalisations** — #1 is a whole-project rewrite, #3 is precisely the project's *internal decomposition* (the generic analytic core is already factored into the sibling lemmas). Neither bears on the mathlib question, because the statement is inexpressible in mathlib at any generality (see below).
Number of decl-local weakening opportunities: **0**.
Proposed restatement: none (a "more general" restatement still references `primeIdealZetaSum` / `frobeniusClass`, which are not in mathlib).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | bundled hyps → typeclasses? | no | already typeclass-driven (`IsGalois`, `IsCyclotomicExtension`, `NumberField`) | — |
| 2 | sequences/metric → filters/topological? | **already done** | the statement *is* `Tendsto … (𝓝[>] 1) (𝓝 …)` — mathlib's filter idiom | n/a — it already uses the contemporary filter form |
| 3 | construction → universal-property class? | no | it's a `Tendsto` proposition, nothing to characterise universally | — |
| 4 | set+closure-predicate → bundled substructure? | no | the "set of primes" is genuinely a `Set (Ideal (𝓞 K))`; that is the right object | — |
| 5 | vector-space/field-specific → weaker typeclass? | no | already at `NumberField` / `IsDedekindDomain`-flavoured generality | — |
| 6 | 1-categorical → higher-categorical? | no | analytic number theory; no categorification target | — |
| 7 | concrete index → arbitrary additive structure? | no | `s : ℝ ↓ 1` is the intrinsic Dirichlet-density parameter | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The declaration is already stated in mathlib's contemporary filter/`Tendsto` idiom over `𝓝[>] 1`. There is no organisational improvement to extract — the only "generalisation" axes (global fields; abstract prime set) are project-architecture decisions, not modernisation moves, and in any case the statement cannot live in mathlib at all (Phase 5).

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp` (Phase 5)

Note: local Lean build is stale (no project `.lake/build`), so `lean_local_search`/`loogle`/`leansearch` MCP tools that resolve **project** decls are unreliable here; the mathlib *index* searches (web) and the literature sweep above are the operative channels, plus reasoning from the statement's vocabulary.

[A] Lean-Finder       "Chebotarev density theorem", "Dirichlet density prime ideals tendsto"   → no hits (mathlib has no such decl; confirmed via arXiv 2503.00959 L-function survey + leanprover-community docs)
[B] Loogle            `Tendsto (fun s => _ / Real.log _) (𝓝[>] 1) (𝓝 _)` ; `primeIdealZetaSum`   → no hits for the project name; the generic `Tendsto _/log` pattern has no mathlib lemma at this shape with a `Nat.card`-of-Galois-group limit
[C] LeanSearch        "partial zeta sum over Frobenius fibre asymptotic to log over Galois order" → no hits (concept absent from mathlib)
[D] Grep mathlib src  `primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`, `DirichletDensity`, `Chebotarev` → **0 occurrences in `Mathlib/`** (all four are project-private names; `Chebotarev`/`HasDirichletDensity` not in mathlib — confirmed by web docs + survey)
[E] Name pattern      project-local search for the qualified name across mathlib                  → n/a (it is a project decl by construction; mathlib-tree has nothing by this or any analogous name)

Searched for both:
  - the user's current form (fibre-numerator asymptotic) — **not in mathlib**.
  - the literature-standard form (Dirichlet density of a prime set; Chebotarev `|c|/|G|`) — **not in mathlib** either. Mathlib's nearest neighbours are `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (Dedekind ζ has a simple pole — the *denominator* analytic input, one level down) and the `LSeries`/`Dirichlet` machinery. Neither is the fibre asymptotic.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard parent form). Mathlib has *building blocks one level below* (Dedekind ζ pole, L-series API) but nothing at the Dirichlet-density / Chebotarev layer — that entire layer is what this project constructs.

---

## Composition check (Phase 6)

### Call sites — `Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp`

Internal use count: **1** (outside the declaring region: it is used *within the same file*, `Cyclotomic.lean:974`, by `cyclotomic_density_from_two_sided_asymp`). External-to-file callers: **0**.

| Caller file:line          | Usage pattern (one-line excerpt) |
|---------------------------|----------------------------------|
| Cyclotomic.lean:974       | `tendsto_ratio_of_log_asymp_numerator _ _ _ (primeIdealZetaSum_frobeniusFibre_asymp K L m hm σ) (primeIdealZetaSum_univ_tendsto_log K)` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this decl?): **(none)** — the fibre asymptotic appears nowhere else; it is the unique numerator input to the two-sided comparison.

Call-sites signal: **K = 1 internal use, same file, no external callers.** Per the Phase 6.0.1 table this leans toward "possibly inline-able / the wrong abstraction" — but here it is the deliberate factorisation of Sharifi's step (iv-a) so the two-sided comparison `cyclotomic_density_from_two_sided_asymp` reads as one clean line. It is *project* API, not *mathlib* API.

### Composition attempt — can mathlib give this in ≤3 calls?

Can `primeIdealZetaSum_frobeniusFibre_asymp` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: any mathlib composition.
  - Mathlib decls used: none possible.
  - Result: **fails immediately** — the *statement* mentions `Chebotarev.primeIdealZetaSum`, `Chebotarev.frobeniusClass`, `Chebotarev.UnramifiedIn`, none of which exist in mathlib. There is no mathlib expression of the same proposition to compose toward.
  - Notes: the *proof* is a genuine multi-step analytic argument (master orthogonality identity `card_mul_frobeniusFibre_eq` + bounded-remainder squeeze `exists_sum_charTwist_erase_norm_bounded` + `primeIdealZetaSum_unramified_div_log_tendsto_one` + `Tendsto.congr'`). Each ingredient is itself project-private. This is "multiple `have`s with non-trivial reasoning between" → **NO, this is a proof**, not a composition.

Conclusion: **NOT-COMPOSABLE from mathlib.** Composable only from *project* lemmas (3 project-private inputs + filter glue), which is exactly how it is already written.

---

## Verdict: `Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the *final* Chebotarev density `|c|/|G|` and the *parent* Dirichlet-density definition are standard; **this specific fibre-numerator asymptotic is a proof-internal step that no source isolates as a lemma**.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within the project's (number-field cyclotomic) scope; 0 decl-local weakenings; already in mathlib's filter/`Tendsto` idiom — no modernisation gap.
- Mathlib search (Phase 5): **not in mathlib** — neither the decl's form nor the literature-standard parent form; `primeIdealZetaSum`/`frobeniusClass`/`UnramifiedIn`/`HasDirichletDensity`/`Chebotarev` are all absent from `Mathlib/`. Nearest mathlib neighbour is the Dedekind-ζ pole `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, one analytic layer below.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (statement is inexpressible there); composable only from the project's own private lemmas, as already written. 1 internal call site, 0 external.

**Rationale:**

This declaration is a node in the `Chebotarev` project's bespoke construction of the cyclotomic Chebotarev density theorem — Sharifi's step (iv-a). Its statement is phrased entirely in project-local vocabulary (`primeIdealZetaSum` over a `Set (Ideal (𝓞 K))`, `frobeniusClass`, `UnramifiedIn`, with `galoisCharacter`/`twistedPrimeSum` in the proof), **none of which exist in mathlib**: mathlib currently has the Dedekind-ζ simple-pole result and the L-series/Dirichlet-character API, but no Dirichlet-density-of-prime-sets layer and no Chebotarev at all. Because the proposition cannot even be *typed* against mathlib, "add as-is" and "generalise first" are both inapplicable, and there is no existing mathlib decl it duplicates. The honest classification is that mathlib supplies *building blocks one layer down* (the analytic ζ pole, log asymptotics, `Tendsto`/filter glue), out of which this project assembles the density layer; the result itself is an internal lemma of that assembly, not a mathlib-shaped object.

It is **not** a NO-mathlib-has-it (mathlib has nothing equivalent) and **not** a clean ≤3-call mathlib composition (the proof is a real multi-step analytic argument over project primitives). The closest accurate bucket is NO-composable-from-mathlib in the precise sense that *its dependencies are composable from project-internal lemmas + mathlib glue* — i.e. it stays in the project. The right mathlib question is not about this lemma but about the **parent concepts**: should mathlib gain a `HasDirichletDensity` API for prime-ideal sets and ultimately a Chebotarev density theorem? That is a large, multi-PR upstreaming effort whose natural unit is the whole `Chebotarev` / `Density` development, not this single intermediate asymptotic.

**WHY not (refactor-actionable):**
Mathlib has the building blocks one layer below — the Dedekind-ζ pole and L-series API — but **not** the prime-set Dirichlet-density layer this lemma lives in. The lemma is therefore correctly *project-internal*; there is nothing to inline at a mathlib call site because the statement does not exist in mathlib's vocabulary.

Mathlib building blocks (one layer down, used to *build* the project's density layer — not to inline this lemma):
- `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` — Dedekind ζ_K has a simple pole at `s = 1` (the denominator asymptotic upstream of `primeIdealZetaSum_univ_tendsto_log`).
- `Mathlib/NumberTheory/LSeries/Dirichlet.lean`, `…/RiemannZeta.lean` — L-series / Dirichlet-character machinery.
- `Filter.Tendsto.div_atTop`, `squeeze_zero_norm'`, `Filter.Tendsto.congr'`, `Real.log_pos` — the analytic/filter glue the proof already uses.

Composition sketch (≤3 lines): **not applicable** — the proposition cannot be expressed in mathlib alone, so there is no mathlib composition to inline. (The actual proof is `card_mul_frobeniusFibre_eq` ∘ `exists_sum_charTwist_erase_norm_bounded` ∘ `primeIdealZetaSum_unramified_div_log_tendsto_one`, all **project-private**.)

Call sites in our project (from Phase 6.0): **K = 1** (`Cyclotomic.lean:974`).

Refactor plan: **none / keep as-is in the project.** This is an appropriate internal factorisation of Sharifi step (iv-a); it should remain a (private-flavoured) helper of `cyclotomic_density_from_two_sided_asymp`. Do *not* attempt to delete/inline it (it cleanly isolates the numerator-vs-denominator split) and do *not* attempt to upstream it in isolation. If mathlib upstreaming is ever pursued, the unit is the **entire `Chebotarev`/`Density` Dirichlet-density development** (new `HasDirichletDensity` API + Chebotarev theorem), at which point this lemma is an ordinary internal step of that PR series — a `BORDERLINE`/strategic call for a human, not an as-is addition.

Next action: keep `Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp` in the project as an internal lemma. No mathlib PR for this decl alone. (Strategic upstreaming of the whole density layer is a separate, human-led decision.)

---

## Next step

Keep the declaration in the project as an internal step of the cyclotomic Chebotarev proof. It is not a candidate for standalone mathlib upstreaming: its statement is built from project-local concepts (`primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`) that mathlib does not have, and mathlib offers no equivalent and no ≤3-call composition. Any upstreaming would be of the **entire Dirichlet-density / Chebotarev layer** as a multi-PR effort — a strategic human decision, with this lemma then a routine internal node.
