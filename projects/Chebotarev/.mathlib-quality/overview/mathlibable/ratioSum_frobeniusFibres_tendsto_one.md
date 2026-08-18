# /mathlibable report — `Chebotarev.ratioSum_frobeniusFibres_tendsto_one`

## Baseline (Phase 0)
- lake build:               stale (per task; on `main` @ `c77747b`, mathlib pin `d90090f`). Reasoned from source — the decl is sorry-free and elaborates; its dependencies all resolve by grep. Build not re-run (task says local build stale; project decls may not resolve via lean_* tools).
- decl `Chebotarev.ratioSum_frobeniusFibres_tendsto_one`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Abelian.lean:1377`
- qualified name:           `Chebotarev.ratioSum_frobeniusFibres_tendsto_one` — VERIFIED. The base name parsed correctly; namespace is `Chebotarev` (`namespace Chebotarev` at `Abelian.lean:56`, `end Chebotarev` at `:1595`; the theorem at 1377 sits inside). It is a public `theorem` (not `private`).
- kind:                     theorem
- has sorry:                no
- module docstring summary: Abelian case of Chebotarev's density theorem (Sharifi 7.2.2 Step 2) — density of unramified primes with a given Frobenius is `1/|Gal(L/K)|`; this file builds the analytic/pigeonhole machinery for it.

## Statement (Phase 1)

`ratioSum_frobeniusFibres_tendsto_one` states: **for an abelian Galois extension `L/K` of number
fields, as `s ↓ 1` the sum over `σ ∈ Gal(L/K)` of the density ratios of the Frobenius fibres `S_σ`
tends to `1`.** Here the fibre `S_σ = {𝔭 prime of 𝓞 K | 𝔭 unramified in L, frobeniusClass 𝔭 = [σ]}`,
and its density ratio at `s` is `primeIdealZetaSum (S_σ) s / primeIdealZetaSum univ s` — i.e.
`(Σ_{𝔭 ∈ S_σ} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`. The content is the analytic bookkeeping step "the |G| Frobenius
fibres partition the unramified primes, and the ramified primes (being finite) contribute density 0,
so the fibre ratios sum to a quantity that tends to 1."

Variables / typeclasses involved (Lean side):
- `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]` — two number fields.
- `[Algebra K L] [IsGalois K L]` — `L/K` is a (finite) Galois extension.
- `[hAb : IsMulCommutative Gal(L/K)]` — the Galois group is abelian (used here only so `ConjClasses.mk`
  is injective; mathematically the fibres are singletons, but the statement only needs disjointness).

Hypotheses (Lean side): none beyond the instances (the abelian hypothesis is an instance).

Conclusion (math): `∑_{σ ∈ Gal(L/K)} (Σ_{𝔭∈S_σ} N𝔭^{-s} / Σ_𝔭 N𝔭^{-s})  →  1` as `s ↓ 1`.

Conclusion (Lean):
`Filter.Tendsto (fun s : ℝ ↦ ∑ σ : Gal(L/K), primeIdealZetaSum {…frobeniusClass = mk σ} s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 1)`.

**Proof shape** (≈12 lines): set `S σ`, the ramified set `R`, and `D = primeIdealZetaSum univ`; show the
fibres are pairwise disjoint (`hpd`, from `ConjClasses.mk_injective`) and disjoint from `R` (`hdisjR`),
and that fibres-∪-`R` cover all nonzero primes (`hcover`). Since `R` is finite (`finite_ramifiedIn`),
its density ratio `→ 0` (`hasDirichletDensity_of_finite`), so `1 - (Σ_R/D) → 1` (`const_sub`). Then
`congr'` the goal to that: eventually (where `D > 0` and `s > 1`) the finite sum of fibre ratios equals
`(Σ_{⋃S_σ}/D) = (D - Σ_R)/D = 1 - Σ_R/D` — using `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`,
`primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, then `field_simp`/`linarith`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma feeding `chebotarev_abelian` (Abelian.lean:1578). It is not a `## Main results`
entry (the project's mains are `chebotarev_density`, `dirichlet_primes_in_AP`, `density_split_completely`),
introduces no new structure/def, and is not named after a person/place. It is the "fibres sum to 1" half
of Sharifi 7.2.2 Step 2 (the other half being the per-fibre `liminf ≥ 1/|G|` bound).

(Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — the one-liner *definition* check does not apply.
Note for narrative: the proof is ~12 substantive lines (a genuine if routine argument), not a one-liner,
so even the "thin wrapper" heuristic doesn't bite on length; the NO verdict below comes from
inexpressibility-in-mathlib + composability, not from triviality of the proof.

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Frobenius classes partition unramified primes Dirichlet density sum Chebotarev proof"                  | yes  | fibres over conj-classes partition unramified primes; densities sum, complement (ramified) is density 0 | MIT 18.785 LectureNotes28; Lenstra "Chebotarev"; Di Meglio; Wikipedia. Always an in-proof step, **unnamed** |
|  2 | WebSearch (general form)         | "ramified primes finite Dirichlet density zero sum over conjugacy classes equals one"                   | yes  | "finite sets have Dirichlet density 0"; "if Σ has a density, its complement does, and they sum to 1"     | Conrad *Dirichlet density for global fields* (Stanford 676); arXiv 2210.13412. The two abstract facts behind the step |
|  3 | WebSearch (named / additivity)   | "Dirichlet density finitely additive disjoint union of prime sets sum of densities Serre Neukirch"      | yes  | "if S₁..Sₘ are disjoint with densities δ₁..δₘ then their union has density δ₁+…+δₘ"                       | **Wikipedia *Dirichlet density*** states exactly this finite-additivity; Kedlaya ANT ch.4; cited to Serre/Neukirch. Caveat: Dirichlet density is only *finitely* additive and not always defined — but for a *finite* partition it is, which is our case |
|  4 | ChatGPT MCP                      | asked: is the "fibres sum to 1" a named lemma? what generality? is it just finite-additivity + finite⟹density-0? | n/a  | —                   | **MCP DOWN** (Codex exec failed, as the task warned). Fell back to the extra WebSearch channels #1–#3 at three generality levels per the skill's fallback guidance |
|  5 | Local references                 | grep `.mathlib-quality/references/`; `refs/Chebotarev/`                                                  | n/a  | —                   | no `references/` dir in this project; `refs/Chebotarev/` absent (PDFs are local-only and not present in this checkout). Recorded n/a |
|  6 | nLab                             | "Chebotarev density theorem" / "Dirichlet density"                                                       | n/a  | —                   | nLab has a Chebotarev page but treats the partition-and-sum-to-1 as an immediate internal step of the proof, not a separately-stated lemma; nothing more general than #1–#3 |
|  7 | nCatLab                          | —                                                                                                       | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                                       | n/a  | —                   | analytic number theory; Stacks (scheme-theoretic alg. geom.) has no Dirichlet-density / Chebotarev material |
|  9 | MathOverflow / Math.SE           | surfaced via WebSearch #1–#3 (SE/Wikipedia threads)                                                     | yes  | same in-proof step, unnamed | no thread states it as a standalone named lemma; all treat it as the partition step inside the Chebotarev argument |
| 10 | recent arXiv (≤5y)               | surfaced in #1/#2 (e.g. arXiv 2210.13412 "A supplement to Chebotarev", 2508.09480 effective Chebotarev)  | yes  | use it as a black-box step | modern Chebotarev papers invoke "ramified primes are density 0 ⟹ fibres partition unramified primes" without naming it |

### Literature summary (Phase 3)

Concept identified as: the **partition step of the Chebotarev density argument** — "the Frobenius fibres
`S_σ` partition the unramified primes, whose complement (the ramified primes) is finite, hence the fibre
densities sum to the density of the unramified primes, which is 1." (Sharifi 7.2.2 Step 2.)
Sources agree on the standard form: **yes** — every source presents this as an internal, **unnamed**
bookkeeping step. It carries no theorem name and no dedicated number anywhere.
Most general standard form: the step decomposes into two genuinely-standard abstract facts —
  (a) **finite additivity of Dirichlet density over a finite disjoint union** (Wikipedia *Dirichlet
  density*: "if S₁,…,Sₘ disjoint with densities δᵢ then ⋃Sᵢ has density Σδᵢ"); and
  (b) **finite sets have Dirichlet density 0** (so the ramified complement vanishes and the cover has
  density 1). Both are stated concretely for Dirichlet density of prime sets; neither is abstracted
  further in the literature.
Generality dimensions where the literature varies:
  - density notion: Dirichlet/analytic vs. natural density — the same partition argument works for both;
    parallel instances, neither strictly more general.
  - extension generality: the *general-G* Chebotarev statement gives fibre density `|C|/|G|` per
    conjugacy class `C`; the abelian case (this decl) is the special case where every `|C| = 1`. The
    "sum to 1" partition step is identical in both and does not depend on abelianness.
Disagreement with the literature: **none**. The project's statement is exactly the standard partition
step, specialised to the analytic ratio-of-partial-sums (`primeIdealZetaSum`) formulation the project uses.

## Generality analysis — `ratioSum_frobeniusFibres_tendsto_one` (Phase 4)

Literature-standard form (from Phase 3): "the Frobenius fibres partition the unramified primes; the
ramified primes are finite (density 0); hence the fibre densities sum to 1." Decomposes into finite
additivity of density + finite⟹density-0.

### Generality status table (Phase 4a)

| # | Parameter / hypothesis                | Current Lean form                              | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|------------------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K] [NumberField L]`    | `S_σ ⊆ Set (Ideal (𝓞 K))`, ratios via `primeIdealZetaSum` | density of prime sets of a number field | NO (within this notion) | `primeIdealZetaSum` is *defined* only for `Set (Ideal (𝓞 K))` with `[NumberField K]`; the statement is unstatable without that scaffold |
| 2 | `[IsMulCommutative Gal(L/K)]` (abelian) | abelian Galois group                        | general finite Galois (fibres = conj-classes, density `|C|/|G|`) | yes (drop abelian) | The partition/sum-to-1 step does **not** use abelianness — it only needs `ConjClasses.mk` to index the fibres and `mk_injective`/disjointness. The general-`G` form would index by `ConjClasses G` and is strictly more general. **But** the generalisation target is itself stated in project-local `primeIdealZetaSum`/`frobeniusClass`, not mathlib — see Phases 5–6 |
| 3 | conclusion `→ 1` (`Tendsto … 𝓝 1`)   | full two-sided limit                           | density of unramified primes = 1         | no                  | `→ 1` is the correct/maximal conclusion; cannot be weakened without losing the result |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** on one axis (abelian vs. general finite Galois,
row 2) — but this is a narrowing *internal to the project's own `primeIdealZetaSum`/`frobeniusClass`
formulation*, and the more-general target is **equally unstatable in mathlib** (mathlib has neither
predicate). So the narrowing is irrelevant to the mathlib question.
Number of weakening opportunities found: 1 (drop the abelian instance and index by `ConjClasses G`).
Cost of restatement: CHEAP (the proof never uses abelianness; only `ConjClasses.mk` indexing) — but
**irrelevant**, because Phases 5–6 show the statement cannot be expressed in mathlib at all, so there is
no mathlib restatement target.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | "let X be a foo" preambles → typeclasses? | no | hypotheses are already instances | — |
| 2  | sequences/metric → filters/nets/topology? | no | already filter-based: `Tendsto … (𝓝[>] 1) (𝓝 1)`, and the proof already uses `Tendsto.congr'`/`const_sub` | — |
| 3  | construction → universal-property class? | no | nothing is constructed | — |
| 4  | set-with-closure-predicate → bundled substructure? | no | `S_σ`/`R` are bare `Set`s of ideals; no lattice structure is relevant to the statement | — |
| 5  | vector-space/metric/field-specific → weaker typeclass? | no | already over `ℝ` with `Tendsto`; the only "structure" is the project's `primeIdealZetaSum` | — |
| 6  | 1-categorical → higher-categorical? | no | not categorical | — |
| 7  | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure? | no | the index `s : ℝ` is a genuine analytic limit parameter, not an artificial concretisation | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already maximally idiomatic for what it is — a
filter-limit (`Tendsto … 𝓝 1`) of a finite sum of analytic ratios, proved with the generic filter API
(`Tendsto.congr'`, `Tendsto.const_sub`) already. There is no Bourbaki-2.0 reformulation, because the
only "abstraction" available is the project's `primeIdealZetaSum`/`HasDirichletDensity` API — the very
thing the statement is *about* — and mathlib does not contain it.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).

## Mathlib search-status: `ratioSum_frobeniusFibres_tendsto_one` (Phase 5)

[A] Lean-Finder       (MCP unavailable in this env)                                  n/a: tool not present; substituted by authoritative grep of mathlib source [D]
[B] Loogle            (MCP unavailable in this env)                                  n/a: tool not present; substituted by [D]
[C] LeanSearch        (MCP unavailable in this env)                                  n/a: tool not present; substituted by [D]
[D] Grep mathlib src  over `.lake/packages/mathlib/Mathlib/` (rev `d90090f`):
      • `DirichletDensity|analyticDensity|naturalDensity|NaturalDensity` → **0 files**.
      • `Chebotarev` (case-insensitive) → **0 hits**. Mathlib has no Chebotarev density theorem.
      • `frobeniusClass|FrobeniusClass` → **0 hits**. (Mathlib has `arithFrobAt`/decomposition-group
        Frobenius data, but no "Frobenius conjugacy class of a prime" packaged as `frobeniusClass`.)
      • `primeIdealZetaSum` → **0 hits**. Closest is `DedekindZeta.lean`, but that is the *global,
        complex-analytic* `dedekindZeta (s : ℂ) := ∑ N(I)^{-s}` over **all** ideals — not a partial
        sum restricted to a prime set, and with no density/ratio API.
      Generic building blocks DO exist: `Tendsto.congr'` (`Mathlib/Order/Filter/Tendsto.lean:105`),
      `Finset.sum_div` (`Mathlib/Algebra/BigOperators/Field.lean:26`); `Tendsto.const_sub` exists in the
      topological-algebra API (used by the proof). | hits for generic plumbing only
[E] Name pattern      grep `ratioSum|frobeniusFibres|*tendsto_one` against namespaced mathlib decls       no relevant hits

Searched for both:
  - the user's current form (`∑_σ primeIdealZetaSum (S_σ)/primeIdealZetaSum univ → 1`) — **not in
    mathlib**, and not even *statable*: it mentions `primeIdealZetaSum` and `frobeniusClass`, both
    project-only.
  - the literature-standard / abstract form ("finite additivity of Dirichlet density" + "finite sets have
    Dirichlet density 0", giving "fibres sum to 1") — **not in mathlib**: mathlib has **no Dirichlet/
    analytic density concept at all**, so neither abstract fact is present as a packaged lemma.

Concluded:
  - **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib has neither
    `primeIdealZetaSum`, `HasDirichletDensity`, `frobeniusClass`, nor a Chebotarev density theorem. The
    only mathlib ingredients are generic plumbing: `Tendsto.congr'`, `Tendsto.const_sub`, `Finset.sum_div`.

## Composition check (+ call-sites) (Phase 6)

### Call sites — `ratioSum_frobeniusFibres_tendsto_one`

Internal use count: **1** (within the project, excluding the declaring-file's own docstring mention).
External-to-file callers: 0 files (the one use is in the same file, `Abelian.lean`).

| Caller file:line  | Usage pattern (one-line excerpt)                                          |
|-------------------|---------------------------------------------------------------------------|
| Abelian.lean:1592 | `(ratioSum_frobeniusFibres_tendsto_one K L) σ` — fed as the "sum → 1" hypothesis to `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` inside `chebotarev_abelian` |
| Abelian.lean:1575 | (docstring of `chebotarev_abelian`, names it as the "sum to 1" half — not a code use) |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?):
  - (none) — the "fibres partition the unramified primes ⟹ ratios sum to 1" argument appears **only**
    here; it is not re-derived inline anywhere in the monorepo.

Call-site signal: K = 1 internal use, no inline re-derivation → "possibly the wrong abstraction / could be
inlined" — leans NO-composable. The single consumer is `chebotarev_abelian`, where it is exactly the
`sum → 1` premise of the pigeonhole glue lemma.

### Composition check (Phase 6a)

Can `ratioSum_frobeniusFibres_tendsto_one` be derived in ≤3 chained mathlib calls?

Attempt 1 (the actual proof): NO. The proof is a genuine ~12-line argument: it builds the pairwise
disjointness of the fibres, their disjointness from the ramified set, the covering of all nonzero primes,
applies `finite_ramifiedIn` + `hasDirichletDensity_of_finite` to kill the ramified tail, then glues with
`primeIdealZetaSum_biUnion_of_pairwiseDisjoint` / `primeIdealZetaSum_union_of_disjoint` /
`primeIdealZetaSum_eq_univ_of_forall_prime_mem` and a `Tendsto.congr'`. That is **not** a ≤3-call
composition of *mathlib* primitives — and crucially every load-bearing lemma in it
(`primeIdealZetaSum_*`, `finite_ramifiedIn`, `hasDirichletDensity_of_finite`, `frobeniusClass`,
`UnramifiedIn`) is **project-local**.

Conclusion: **NOT-COMPOSABLE *from mathlib primitives alone*** — and not even *expressible* in mathlib,
since `primeIdealZetaSum` and `frobeniusClass` (which appear in the statement) are project-only. It *is*
a routine composition over **project** code (finite-additivity of `primeIdealZetaSum` + density-0 of the
finite ramified set), which is exactly why it belongs in the project, not upstream.

## Verdict: `Chebotarev.ratioSum_frobeniusFibres_tendsto_one`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the result is the **unnamed** partition step of the Chebotarev argument
  (Sharifi 7.2.2 Step 2); ≥3 WebSearch channels at three generality levels + nLab/Stacks/arXiv triaged.
  Its abstract kernel = "Dirichlet density is finitely additive over a finite disjoint union" (Wikipedia
  *Dirichlet density*) + "finite sets have density 0" — both standard, both unnamed.
- Generality analysis (Phase 4): STRICTLY NARROWER on the abelian-vs-general-`G` axis, but the
  generalisation target is equally project-local and equally unstatable in mathlib; no modern-idiom move
  (the statement is already filter-based and uses generic `Tendsto` API directly).
- Mathlib search (Phase 5): **not in mathlib** — mathlib has no Dirichlet-density notion, no
  `primeIdealZetaSum`, no `frobeniusClass`, no Chebotarev theorem; only generic plumbing
  (`Tendsto.congr'`, `Tendsto.const_sub`, `Finset.sum_div`) exists.
- Composition check (Phase 6): NOT-COMPOSABLE *from mathlib alone* — the ~12-line proof is a composition
  over **project** lemmas (`primeIdealZetaSum_*`, `finite_ramifiedIn`, `hasDirichletDensity_of_finite`);
  one call site (`chebotarev_abelian`), no inline re-derivation.

**Rationale.**
The statement is phrased entirely in terms of `primeIdealZetaSum` and `frobeniusClass`, both of which
live **only in this project** — mathlib has no Dirichlet/analytic density notion, no partial prime-ideal
zeta sum, no Frobenius-class-of-a-prime, and no Chebotarev density theorem (Phase 5 grep = 0 hits on every
one). So this theorem cannot be added to mathlib *as written*: its very signature mentions project-private
objects. Mathematically the content is the textbook partition step inside the Chebotarev proof (Phase 3):
the Frobenius fibres partition the unramified primes, the ramified complement is finite hence density 0,
so the fibre density ratios sum to 1. Every source treats this as an immediate, unnamed bookkeeping step,
and its abstract kernel is just finite-additivity of density plus "finite ⟹ density 0." In Lean it is a
routine ~12-line composition whose every substantive ingredient — `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`,
`primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, `finite_ramifiedIn`,
`hasDirichletDensity_of_finite` — is project-local; the only mathlib parts are generic filter/finsum
plumbing (`Tendsto.congr'`, `Tendsto.const_sub`, `Finset.sum_div`). The right home is therefore the
project (it is the natural "Step 2 partition" helper of `chebotarev_abelian`), not mathlib. This is the
same situation as the sibling `infinite_of_hasDirichletDensity_pos` (also NO-composable: a result whose
statement references the project-only density API).

**WHY not (refactor-actionable).**
Mathlib has the *generic* plumbing but neither the statement, the objects it mentions, nor the abstract
density facts it rests on. The proof is a composition over **project** code, not a 1–3-call mathlib
composition — so the honest reading of "NO-composable-from-mathlib" here is: *do not upstream; keep it as
the project's own Step-2 helper.* There is nothing to inline-replace with a mathlib call, because mathlib
offers no Dirichlet-density API to inline.

Mathlib building blocks (generic plumbing only, NOT a route to the statement):
  `Tendsto.congr'`     — `Mathlib/Order/Filter/Tendsto.lean:105`
  `Tendsto.const_sub`  — `Mathlib/Topology/Algebra/*` (topological-group sub-continuity)
  `Finset.sum_div`     — `Mathlib/Algebra/BigOperators/Field.lean:26`
Project building blocks (the real content, all project-local — none are mathlib candidates either, since
`primeIdealZetaSum`/`HasDirichletDensity` are project-only):
  `primeIdealZetaSum_biUnion_of_pairwiseDisjoint` — `CebotarevDensity/Density.lean:181`
  `primeIdealZetaSum_union_of_disjoint`           — `CebotarevDensity/Density.lean:150`
  `primeIdealZetaSum_eq_univ_of_forall_prime_mem` — `CebotarevDensity/Density.lean:197`
  `hasDirichletDensity_of_finite`                 — `CebotarevDensity/Density.lean:588`
  `finite_ramifiedIn`                             — `CebotarevDensity/Frobenius.lean:325`

Call sites in our project (from Phase 6.0): **K = 1** (`Abelian.lean:1592`, inside `chebotarev_abelian`).
Refactor plan: **none for mathlib.** Keep `ratioSum_frobeniusFibres_tendsto_one` as a project-local lemma —
it is well-named, documents Sharifi 7.2.2 Step 2's partition step, and is the natural `sum → 1` input to
the pigeonhole glue at its single call site. (Optionally it could be inlined into `chebotarev_abelian`,
but at ~12 lines it earns its own name; recommended: leave as-is.) Do **NOT** open a mathlib PR.

**Note.** Not `NO-mathlib-has-it`: mathlib has neither the statement nor any of its objects. Not a YES
bucket: the statement references project-private definitions, so it is unstatable upstream, and the
mathematical content is a universally-known unnamed partition step. Under the five-bucket scheme the honest
classification is **NO-composable-from-mathlib**, read as "routine composition over **project** API; keep
local, do not upstream" — with the recorded caveat (for the human) that the composition rests on project
lemmas rather than pure mathlib, because the entire Dirichlet-density layer is project-local. A genuine
mathlib contribution in this vicinity would be the *upstream Dirichlet-density + Chebotarev development
itself* (a large, separate undertaking), not this individual Step-2 helper.

---

## Next step

This is a project-local helper. Do **not** open a mathlib PR. Keep `ratioSum_frobeniusFibres_tendsto_one`
in the Chebotarev project as the "fibres sum to 1" half of Sharifi 7.2.2 Step 2 (its single consumer is
`chebotarev_abelian`). No upstreaming action. If/when the project's whole Dirichlet-density + Chebotarev
layer is proposed for mathlib, this lemma travels with it — it is not an independent contribution.
