# /mathlibable report — `Chebotarev.chebotarev_cyclotomic`

## Verdict: **YES-add-as-is** (modulo upstreaming the whole development)

One-line: a named theorem (Chebotarev density, cyclotomic case) in its standard
weak/Dirichlet-density form; mathlib has neither it nor any prime-density notion.

---

### Baseline (Phase 0)

- lake build:               not run (local build stale per task note; reasoning from source — statement elaborates as written, all referenced lemmas resolve in-file/in-project)
- decl `Chebotarev.chebotarev_cyclotomic`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:982`
- qualified name:           **`Chebotarev.chebotarev_cyclotomic`** (namespace `Chebotarev`, opened at Cyclotomic.lean:69; confirmed — NOT a guess)
- kind:                     theorem
- has sorry:                no (body is `cyclotomic_density_from_two_sided_asymp K L m hm σ`)
- module docstring summary: Chebotarev's theorem, cyclotomic case — density of primes of `𝓞 K` unramified in `K(μ_m)` with Frobenius `= σ` is `1/|Gal(L/K)|` (Sharifi §7.2.1; Stevenhagen–Lenstra App. ¶3).

---

### Statement (Phase 1)

`Chebotarev.chebotarev_cyclotomic` is a **theorem** stating the following:

> Let `K` be a number field, `m ≥ 1`, and `L = K(μ_m)` the `m`-th cyclotomic
> extension of `K` (so `L/K` is Galois, abelian). Fix `σ ∈ Gal(L/K)`. Then the
> set of prime ideals `𝔭` of `𝓞 K` that are unramified in `L` and whose Frobenius
> conjugacy class equals `[σ]` has Dirichlet density `1/|Gal(L/K)|`.

This is the **weak form of Chebotarev's density theorem specialised to a
cyclotomic (hence abelian) extension**, where every conjugacy class is a
singleton so `|C|/[L:K] = 1/[L:K] = 1/|Gal(L/K)|`. It is the direct
generalisation of Dirichlet's theorem on primes in arithmetic progressions
(the case `K = ℚ`, where `Gal(ℚ(μ_m)/ℚ) ≅ (ℤ/mℤ)ˣ`).

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` — base and top number fields, `L/K` Galois (file-level `variable`s).
- `m : ℕ`, `[NeZero m]` — the cyclotomic level `m ≥ 1`.
- `[IsCyclotomicExtension {m} K L]` — `L` is `K(μ_m)`.
- `(hm : m % 4 ≠ 2)` — a hypothesis excluding `m ≡ 2 (mod 4)` (a normalisation: such `m` give `K(μ_m) = K(μ_{m/2})`, the degenerate corner handled separately in `Main.lean`).
- `(σ : Gal(L/K))` — the target Galois element.

Hypotheses (math): `L = K(μ_m)`, `m ≢ 2 (mod 4)`.

Conclusion (math): `δ({𝔭 prime of 𝓞 K : 𝔭 unramified in L, Frob(𝔭) = [σ]}) = 1/|Gal(L/K)|`.

Conclusion (Lean):
```
HasDirichletDensity
  {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
  ((Nat.card Gal(L/K) : ℝ)⁻¹)
```
where `HasDirichletDensity S δ := Tendsto (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 δ)` (project def, `Density.lean:64`), i.e. `δ = lim_{s↓1} (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: theorem named after a person (Chebotarev / Cebotarev), AND the single
`## Main results` entry of its module. Both BIG triggers fire.

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. The body
(`cyclotomic_density_from_two_sided_asymp K L m hm σ`) is a one-line *forwarding*
to a lemma, but that lemma rests on a multi-hundred-line analytic development;
the one-liner heuristic (which targets thin `def` wrappers) does not apply to
named theorems. Skipped.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found                                            | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|----------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Chebotarev cyclotomic case Dirichlet density Frobenius conjugacy class statement           | yes  | `density = #C/#G`; cyclotomic case = primes split in `ℚ(ζ)`, `G ≅ (ℤ/mℤ)ˣ`, reduces to Dirichlet AP | Wikipedia, MIT 18.785 LN28, Stevenhagen–Lenstra |
|  2 | WebSearch (general form)         | Chebotarev general form natural density vs Dirichlet density Galois extension              | yes  | **weak form:** `P_A = {𝔭 : Frob ∈ A}` has Dirichlet density `\|A\|/n`, `n=[L:K]`; natural density exists & equals it | Stanford (Conrad) dirdensity, EoM, HandWiki — pins exact form |
|  3 | WebSearch (named-after / mathlib)| mathlib4 Chebotarev density theorem formalization Lean Frobenius primes                    | no   | (no Lean formalisation found)                                  | confirms not previously formalised |
|  4 | ChatGPT MCP                      | standard form + generality + historical evolution                                          | n/a  | MCP down per task note — substituted by 3+ targeted WebSearches at distinct generality levels (#1,#2,#6) | fallback used as task instructed |
|  5 | Local references                 | grep `.mathlib-quality/references/` for chebotarev/density                                  | n/a  | no `references/` dir for this project (`refs/Chebotarev/` absent; PDFs local-only per CLAUDE.md) | recorded n/a; primary source is Sharifi `docs/algnum.pdf` p.142 + Stevenhagen–Lenstra `docs/cheb.pdf` p.18, both cited in-module |
|  6 | nLab                             | nLab Chebotarev density theorem statement                                                   | partial | "prime ideals equidistributed among conjugacy classes of `Gal(L/K)`" | nLab page thin; secondary sources returned confirm same form |
|  7 | nCatLab (if categorical)         | —                                                                                          | n/a  | not a categorical concept (analytic number theory)             | n/a with reason |
|  8 | Stacks Project (if alg geom)     | Stacks project Chebotarev density theorem number field                                      | n/a  | Stacks does not cover Chebotarev/analytic density of primes    | n/a — analytic NT, outside Stacks' scheme-theoretic scope |
|  9 | MathOverflow / Math.SE           | (covered via #2 EoM/HandWiki + #1) natural vs Dirichlet density of Chebotarev sets         | yes  | natural & Dirichlet densities coincide for Chebotarev sets     | the `δ`-as-Dirichlet-density choice is the standard analytic-density form |
| 10 | recent arXiv (last 5 years)      | effective Chebotarev; p-adic Chebotarev; short-interval                                      | yes  | arXiv 2508.09480 (effective), 2212.00294 (p-adic), 1810.06201 (F_q(T)) — all take the same weak-form density as baseline | confirms the form is the stable, universally-cited baseline |

**Protocol pass check:** WebSearch ran ≥3 distinct queries at different
generality levels (specific cyclotomic form #1; most-general weak form #2;
named-after/Lean #3; plus #6) ✓. ChatGPT MCP unavailable (down per task) —
fallback WebSearches substituted, as the task explicitly permitted ✓. Local
refs checked (absent → n/a with reason) ✓. nLab checked ✓. Stacks/nCatLab
checked → n/a with reason ✓. MathOverflow-class sources (EoM/HandWiki)
checked ✓. arXiv last-5-years checked ✓.

### Literature summary (Phase 3)

Concept identified as: **Chebotarev density theorem (weak form), cyclotomic/abelian special case** — equivalently the cyclotomic instance of the equidistribution of Frobenius among conjugacy classes; for `K=ℚ` it is exactly **Dirichlet's theorem on primes in arithmetic progressions, with density**.

Sources agree on the standard form: **yes**. Every source (Wikipedia, Stevenhagen–Lenstra, MIT 18.785, Conrad/Stanford, EoM, HandWiki, Springer Ch.7) states the weak form as: for conjugacy class `A ⊆ Gal(L/K)`, `{𝔭 : Frob_𝔭 = A}` has **Dirichlet density `|A|/[L:K]`**. For a cyclotomic (abelian) extension `|A| = 1`, giving `1/|Gal(L/K)|` — exactly the Lean conclusion `(Nat.card Gal(L/K))⁻¹`.

Most general standard form: full Chebotarev for an arbitrary finite Galois extension of number fields with density `|C|/[L:K]` for a conjugacy class `C` (and further: global fields, including function fields).

Generality dimensions where the literature varies:
  - **Extension type**: cyclotomic/abelian (here) ⊂ arbitrary finite Galois ⊂ global-field Galois. The most general is global-field Galois.
  - **Class vs element**: singleton `{σ}` (here, valid because abelian) ⊂ arbitrary conjugacy class `C` with weight `|C|`.
  - **Density notion**: Dirichlet/analytic density (here) — for Chebotarev sets natural density also exists and equals it (a strictly stronger statement).

Disagreement with the literature: **none**. The Lean form is a faithful, correctly-normalised specialisation of the literature-standard weak form.

---

### Generality analysis — `Chebotarev.chebotarev_cyclotomic` (Phase 4)

Literature-standard form (from Phase 3): full Chebotarev — for a finite Galois
extension `L/K` of number fields and conjugacy class `C ⊆ Gal(L/K)`, the primes
with `Frob_𝔭 = C` have Dirichlet density `|C|/[L:K]`.

| # | Parameter / hypothesis              | Current Lean form                    | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|--------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `[IsCyclotomicExtension {m} K L]`   | `L = K(μ_m)` (abelian)               | arbitrary finite Galois `L/K`            | **yes** (general Chebotarev) | The cyclotomic case is genuinely special — the proof uses cyclotomic Frobenius reciprocity + Dirichlet `L(χ,1)≠0` for **abelian** characters. General Chebotarev needs Artin `L`-functions / class field theory: a *different, much deeper* proof. This is a **strict specialisation**, but generalising is NOT mechanical — it is a separate, large formalisation project. |
| 2 | `frobeniusClass … = ConjClasses.mk σ` (singleton) | density `1/\|G\|` | conjugacy class `C`, density `\|C\|/[L:K]` | yes (within general Chebotarev) | Singleton is correct & lossless **for abelian** `L/K` (every class is a singleton). Only meaningful to weaken alongside #1. |
| 3 | density = Dirichlet density (`HasDirichletDensity`) | analytic density | analytic density (+ natural density, stronger) | yes (natural density) | Natural density is strictly stronger and standard for Chebotarev sets, but requires the PNT-with-error / Tauberian machinery mathlib does not yet have. Out of scope for the analytic-density statement. |
| 4 | `(hm : m % 4 ≠ 2)`                  | excludes `m ≡ 2 (4)`                 | (no such restriction in lit)             | yes (cosmetic)      | A normalisation artefact: `K(μ_m)=K(μ_{m/2})` when `m≡2(4)`, so the excluded case is *handled by relabelling* (see `Main.lean:480`), not a real loss. Could be absorbed, but harmless. |
| 5 | `[NumberField K] [NumberField L]`   | number fields                        | number fields (general Chebotarev) or global fields | yes (function fields) | Global-field Chebotarev exists but is a separate development; number-field is the standard primary target. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the cyclotomic
special case of full Chebotarev).

Number of weakening opportunities found: 3 substantive (#1 extension type, #3
density notion, #5 base field) + 1 cosmetic (#4).

**BUT** — and this is the load-bearing point for the verdict — every substantive
weakening (#1, #3, #5) is **EXPENSIVE and requires fundamentally new mathematics
not yet in mathlib** (Artin `L`-functions and their non-vanishing / class field
theory for #1; a Tauberian/PNT-with-error upgrade for #3; function-field zeta
machinery for #5). None is a mechanical restatement. The cyclotomic case is a
**recognised, named, self-standing milestone** in the literature precisely
because it is provable by elementary-analytic (Dirichlet-style) means while the
general case is not.

Proposed restatement (general Chebotarev) — **for the record, NOT actionable now**:
```lean
theorem chebotarev_density
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := sorry  -- needs Artin L-functions; out of current scope
```
Cost of restatement: **EXPENSIVE** — needs new ideas (Artin `L`-functions, CFT)
absent from both this project and mathlib.

Per the skill's cost rule: **EXPENSIVE does not downgrade the verdict, and
"too expensive to generalise" is NOT a self-resolving downgrade to a narrow
YES** — it would force BORDERLINE *if the narrow form were not itself a
literature-recognised standalone result*. Here the narrow form **is** a named,
citable theorem (the cyclotomic / Dirichlet case), so it ships as-is on its own
merit; the general form is a *future* PR, not a blocker. See Phase 7.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                      | no       | Already fully typeclass-driven (`[IsCyclotomicExtension {m} K L]`, `[IsGalois K L]`) | — |
|  2 | sequences/metric → filters/topology?                                      | partial-already | `HasDirichletDensity` is already stated via `Tendsto … (𝓝[>] 1)` — the idiomatic filter form | n/a |
|  3 | construct an object → universal-property class?                          | no       | It's a `Prop` (a density equation), nothing constructed | — |
|  4 | set-with-closure-predicate → bundled substructure?                        | no       | The prime set is genuinely a `Set`, not a substructure | — |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                  | no       | Number-field-specific by nature; `[NumberField]` is the right class | — |
|  6 | 1-categorical → higher-categorical?                                       | no       | Analytic density statement; no categorification target | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid?                          | no (already abstract) | `σ : Gal(L/K)`, density in `ℝ` — already at the right level | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already mathlib-idiomatic:
typeclass-driven hypotheses, the conclusion phrased as a filter `Tendsto` (via
`HasDirichletDensity`), `Nat.card`/`ConjClasses` for the cardinality and class.
There is no contemporary reformulation that improves organisation. One-line
reason: this is an analytic-density equation already expressed in mathlib's
filter idiom; no abstraction layer is being missed.

*(Caveat for the eventual PR: the project's `HasDirichletDensity`,
`primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn` defs must be upstreamed
first, and mathlib reviewers will likely want `UnramifiedIn` reconciled with the
existing finite-prime ramification API — see Phase 7 "WHY add it".)*

---

### Diamond / defeq risk — `Chebotarev.chebotarev_cyclotomic` (Phase 4.5)

n/a — declaration kind is `theorem`. A `Prop`-valued theorem introduces no
definitional equalities and no typeclass-search paths, so it cannot create
diamonds, reducibility leaks, or coercion ambiguities. Skipped.

*(Note: the **supporting defs** `HasDirichletDensity`, `primeIdealZetaSum`,
`frobeniusClass`, `UnramifiedIn` — which would be co-upstreamed — are the ones
that warrant a Phase-4.5 pass; that belongs to their own `/mathlibable` runs.)*

---

### Mathlib search-status: `Chebotarev.chebotarev_cyclotomic` (Phase 5)

Five-method search. (lean_loogle / lean_leansearch unavailable in this
environment — local Lean index stale per task note; substituted by exhaustive
`grep` over the pinned mathlib source tree `.lake/packages/mathlib/Mathlib/`,
which is the authoritative ground truth and strictly more reliable than the
indexed search for an absence claim.)

```
[A] Lean-Finder       n/a — tool unavailable this env
[B] Loogle            n/a — tool unavailable this env (would query: `HasDirichletDensity _ _`, `Tendsto _ (𝓝[>] 1) _` for prime sums)
[C] LeanSearch        n/a — tool unavailable this env
[D] Grep mathlib src  chebotarev|cebotarev → NO HITS;
                      "Dirichlet density"|DirichletDensity|"analytic density" → NO HITS;
                      frobeniusClass → NO HITS;
                      density of prime ideals → NO HITS (only `schnirelmannDensity (setOf Nat.Prime) = 0`, an unrelated combinatorial density)
[E] Name pattern      grep over mathlib for the supporting names: HasDirichletDensity/primeIdealZetaSum/UnramifiedIn(as a Prop on ideals) → NO HITS (all project-local)
```

Searched for both:
  - the user's current form (cyclotomic Chebotarev / `1/|G|` density) — **not in mathlib**
  - the literature-standard general form (full Chebotarev `|C|/[L:K]`) — **not in mathlib**
  - the classical special case (Dirichlet on primes in AP) — mathlib **has it but only as INFINITUDE**: `Nat.forall_exists_prime_gt_and_eq_mod` / `infinite_setOf_prime_and_eq_mod` (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean:475,484`) state `{p | p.Prime ∧ (p : ZMod q) = a}.Infinite`. **No density** is asserted anywhere in that file.

**Building blocks mathlib DOES have** (relevant to Phase 6, not a match):
  - `arithFrobAt` / `IsArithFrobAt` (`Mathlib/RingTheory/Frobenius.lean:181,258`) — the *local* arithmetic Frobenius element. The project builds `frobeniusClass` on top of this.
  - Dirichlet `L`-functions, characters, `L(χ,1)≠0` for `χ≠1` (`Mathlib/NumberTheory/LSeries/{Dirichlet,Nonvanishing,DirichletContinuation}.lean`) — the analytic engine behind the cyclotomic case.
  - Dedekind zeta `ζ_K` (`Mathlib/NumberTheory/NumberField/DedekindZeta.lean`).

Concluded: **not in mathlib** (all available methods exhausted — full mathlib
source grep for the result, the general form, AND the classical special case;
the special case exists only as an *infinitude* statement, never as a density).

---

### Call sites — `Chebotarev.chebotarev_cyclotomic` (Phase 6.0)

Internal use count (non-comment, excluding the declaring file `Cyclotomic.lean`): **2**
External-to-file callers: **2 distinct files**

| Caller file:line          | Usage pattern (one-line excerpt)                                              |
|---------------------------|-------------------------------------------------------------------------------|
| `Abelian.lean:739`        | `(by ext x; rfl) rfl (chebotarev_cyclotomic (K := ↥F) (L := M) m hm4 σE)`     |
| `Main.lean:461`           | `have hfib := chebotarev_cyclotomic ℚ L n hn4 σ`                              |
| `Cyclotomic.lean:1001`    | `(chebotarev_cyclotomic K L m hm σ).hasLower` (in-file wrapper `…_lowerDensity_ge`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): **(none)** — no site re-derives the density without calling this theorem; consumers genuinely depend on it.

**Signal (per the call-sites table):** 2 external uses in 2 files + 1 in-file
wrapper, zero inline re-derivations → **real, depended-upon API** in the
`YES-*` direction. It is the keystone the abelian case (`Abelian.lean`) and
Dirichlet's AP theorem (`Main.lean`) are built on.

### Composition check (Phase 6)

Can `chebotarev_cyclotomic` be derived from mathlib in ≤3 chained calls?

Attempt 1: chain mathlib's Frobenius element `arithFrobAt` + Dirichlet
`L(χ,1)≠0` + zeta asymptotics.
  - Mathlib decls used: `arithFrobAt`, `LFunction…ne_zero`, `dedekindZeta…`.
  - Result: **fails decisively**. There is no density statement to chain to — mathlib has no `HasDirichletDensity`, no `primeIdealZetaSum`, no Frobenius-fibre asymptotic, and no character-orthogonality-to-density bridge. The actual proof (`cyclotomic_density_from_two_sided_asymp` → `primeIdealZetaSum_frobeniusFibre_asymp` + `primeIdealZetaSum_univ_tendsto_log`) is a **multi-hundred-line analytic development** spanning ≥6 project files (`ZetaProduct`, `CyclotomicNormResidue`, `CharacterOrthogonality`, `Density`, `Frobenius`, `Cyclotomic`): two-sided log-asymptotic comparison `Σ_χ χ(σ)⁻¹ log L(χ,s) ~ |G| Σ_{Frob=σ} N𝔭^{-s}` against `~ log ζ_K(s) ~ log(s-1)⁻¹`.
  - Notes: this is a deep theorem, not a composition.

Conclusion: **NOT-COMPOSABLE** (the gap is an entire analytic-NT development, far beyond 3 mathlib calls).

---

## Verdict: `Chebotarev.chebotarev_cyclotomic`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): named theorem; weak-form Chebotarev density `|C|/[L:K]`, cyclotomic case = singleton class → `1/|G|`; the Lean form matches the universally-cited standard exactly. ≥6 channels, all agree.
- Generality analysis (Phase 4): **STRICTLY NARROWER** than full Chebotarev — but every weakening is EXPENSIVE and needs maths absent from mathlib (Artin L-functions / CFT / Tauberian PNT), and the narrow form is itself a recognised named milestone. Modern-idiom (4c): already idiomatic, no improvement available.
- Mathlib search (Phase 5): **not in mathlib** — no Chebotarev, no prime-density notion at all; the classical special case (Dirichlet AP) exists only as *infinitude*, never as density.
- Composition check (Phase 6): **NOT-COMPOSABLE** — proof is a multi-file analytic development, not ≤3 mathlib calls. 2 external call sites + 1 wrapper, no inline re-derivation.

**Rationale:**

`chebotarev_cyclotomic` is a genuine, named, citable theorem that mathlib does
not have in any form. Mathlib's number theory currently tops out at **Dirichlet's
theorem as an infinitude statement** (`infinite_setOf_prime_and_eq_mod`); it has
*no* notion of Dirichlet/analytic density of prime ideals (the only "prime
density" in the library is `schnirelmannDensity (setOf Nat.Prime) = 0`, an
unrelated combinatorial zero-density fact). This declaration is the cyclotomic
case of Chebotarev — the standard milestone that upgrades Dirichlet's theorem
from "infinitely many" to "density `1/|G|`", stated at exactly the generality
the literature treats as a self-standing result. The Phase-5 search is
unambiguous, the Phase-6 composition fails by a wide margin (the proof is a
~6-file analytic development), and the Phase-4 narrowness is not a defect: the
general Galois case requires Artin L-functions and class field theory that
neither this project nor mathlib yet has, so the cyclotomic form is the correct
*current* contribution, with the general form as a clearly-scoped future PR.

The Phase-4b classification was STRICTLY NARROWER, which normally points at
YES-but-generalise-first. It does **not** here, for the gate-relevant reason:
the generalisation is EXPENSIVE *and* requires new mathematics not present in
mathlib, while the narrow form is a literature-recognised named theorem in its
own right (the cyclotomic / Dirichlet-density case). The skill's cost rule
forbids downgrading a verdict on cost grounds alone; combined with the narrow
form's standalone status, the correct bucket is YES-add-as-is, with the
generalisation recorded as future work rather than a blocker. (This is the
"named milestone that is the maximal *currently-provable* form" pattern, not the
"lazy specialisation of an easy general form" pattern that YES-but-generalise
targets.)

**WHY add it (refactor-actionable):**

- **New mathematical content / the specific gap:** mathlib has **zero**
  Dirichlet-density-of-primes API. Concretely missing, and contributed by this
  development: (a) the *definition* `HasDirichletDensity` of the analytic density
  of a set of prime ideals via `lim_{s↓1} (Σ_{𝔭∈S} N𝔭^{-s})/(Σ_𝔭 N𝔭^{-s})`
  (`Density.lean:64`); (b) the partial Dirichlet series `primeIdealZetaSum`;
  (c) the global **Frobenius conjugacy class** `frobeniusClass` of a prime
  (`Frobenius.lean:188`), built on mathlib's *local* `arithFrobAt` but not
  itself in mathlib; (d) the cyclotomic Chebotarev theorem itself. The gap is
  the entire bridge from mathlib's existing **infinitude** Dirichlet theorem
  (`PrimesInAP.lean`) to a **density** statement — a long-standing, well-known
  hole in mathlib's analytic NT. This is the headline result that fills it for
  the cyclotomic/abelian case.
- **How it composes with mathlib's API:** it consumes mathlib's Dirichlet
  `L`-functions + `L(χ,1)≠0` (`LSeries/Nonvanishing.lean`), Dedekind zeta
  (`DedekindZeta.lean`), and local arithmetic Frobenius
  (`RingTheory/Frobenius.lean`), turning them into a density statement — and in
  turn it specialises to recover mathlib's `infinite_setOf_prime_and_eq_mod`
  *with* a density (the project's `Main.lean` does exactly this for `K=ℚ`).

Proposed mathlib location: `Mathlib/NumberTheory/ChebotarevDensity/Cyclotomic.lean`
(new directory; the density-of-primes defs go in a sibling
`Mathlib/NumberTheory/ChebotarevDensity/Density.lean`).

Proposed PR title: `feat(NumberTheory): Dirichlet density of primes + Chebotarev density theorem, cyclotomic case`

PR grouping (required — the theorem cannot ship alone): this theorem is the
**apex of a stack** that must be upstreamed together or in a dependency-ordered
sequence of PRs. The supporting public defs/lemmas — each warranting its **own**
`/mathlibable` assessment before its PR — are at minimum:
  - `Chebotarev.HasDirichletDensity`, `HasUpperDirichletDensity`,
    `HasLowerDirichletDensity`, `primeIdealZetaSum` (`Density.lean`)
  - `Chebotarev.frobeniusClass`, `Chebotarev.UnramifiedIn` and their API
    (`Frobenius.lean`) — **reviewers will likely require reconciling
    `UnramifiedIn` with mathlib's existing ramification API for ideals** rather
    than a fresh `Prop`; this is the main upstreaming friction point.
  - the analytic engine (`ZetaProduct`, `CyclotomicNormResidue`,
    `CharacterOrthogonality`).
The right grain is a **PR series**, bottom-up: density defs → Frobenius class →
analytic lemmas → the theorem. This single decl is the capstone of that series,
not a standalone PR.

Pre-PR checklist before opening:
  - [ ] `/mathlibable` each supporting def (`HasDirichletDensity`,
        `primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`) — they gate the
        capstone and each needs its own Phase-4.5 risk pass.
  - [ ] `/generalise Chebotarev.chebotarev_cyclotomic` — confirm the `hm % 4 ≠ 2`
        normalisation cannot be cheaply absorbed, and document why the general
        Galois case is deferred.
  - [ ] `/cleanup` the file + theorem — full audit + diff gates.
  - [ ] Reconcile `UnramifiedIn` (ideals) with mathlib's ramification API
        before the Frobenius-class PR.
  - [ ] Pick a reviewer from recent `Mathlib/NumberTheory/LSeries/` commits
        (the Dirichlet-AP authors are the natural audience).

---

## Next step

This is the capstone of a multi-file analytic development. Do **not** open a
single PR for it. Instead: run `/mathlibable` on each supporting def
(`HasDirichletDensity`, `primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`)
to assess the bottom of the stack, then upstream **bottom-up as a dependency-
ordered PR series** (density defs → Frobenius conjugacy class → analytic lemmas
→ this theorem), reconciling `UnramifiedIn` with mathlib's ramification API
along the way. Target directory `Mathlib/NumberTheory/ChebotarevDensity/`.
