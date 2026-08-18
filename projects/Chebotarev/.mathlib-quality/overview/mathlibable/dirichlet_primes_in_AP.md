# /mathlibable report — `Chebotarev.dirichlet_primes_in_AP`

> Step-9 (overview) mathlibable assessment, run as the full 10-phase `/mathlibable`
> workflow on a single declaration. Environment notes (per the task + the sibling
> `chebotarev_density.md` run): the ChatGPT-math MCP is down, and the Loogle /
> LeanSearch / Lean-Finder MCPs are not loadable in this env, so the literature
> channel uses the documented WebSearch + WebFetch + nLab/EoM fallback, and Phase 5
> ("is it in mathlib") is answered by **direct grep over the vendored mathlib tree**
> `.lake/packages/mathlib/` plus a **live fetch of the mathlib4 docs page**, both of
> which are authoritative. The local Lean build is stale (Phase 0a reasoned from
> source, not rebuilt).

---

## Phase 0 — Baseline

```
### Baseline (Phase 0)
- lake build:               (stale — not rebuilt; reasoned from source per task note)
- decl `Chebotarev.dirichlet_primes_in_AP`:  ✓ resolved at
                            projects/Chebotarev/CebotarevDensity/Main.lean:517
- true qualified name:      Chebotarev.dirichlet_primes_in_AP
                            (namespace `Chebotarev` opened Main.lean:60; `end Chebotarev`
                            Main.lean:528; theorem at 517 ⇒ the parsed guess is CORRECT)
- kind:                     theorem
- has sorry:                no (proof complete: case-splits on `n % 4 = 2`, then routes
                            to `dirichlet_AP_two_mul` / `dirichlet_AP_main`, both of which
                            reduce through `chebotarev_cyclotomic` + a symmetric-difference
                            density-closure lemma)
- module docstring summary: Chebotarev's density theorem (conjugacy-class form) with
                            corollaries — Dirichlet primes in AP (this decl) and density of
                            completely-split primes.
```

---

## Phase 1 — Statement (prose)

`Chebotarev.dirichlet_primes_in_AP` is **Dirichlet's theorem on primes in
arithmetic progressions, in its Dirichlet-density form**:

> Let `n ≥ 1` and let `a ∈ (ℤ/nℤ)×` (a unit mod `n`, i.e. `gcd(a, n) = 1`).
> Then the set of rational primes `p` with `p ≡ a (mod n)` has **Dirichlet
> density** `1/φ(n)` (as a set of prime ideals `(p) ⊆ 𝓞 ℚ = ℤ`).

This is the classical equidistribution refinement of "there are infinitely many
primes ≡ a mod n": not just infinitude, but the precise analytic *proportion*
`1/φ(n)`, uniform over all `φ(n)` invertible residue classes. It is the abelian
(cyclotomic) specialisation of Chebotarev, `K = ℚ`, `L = ℚ(μ_n)`, where
`Gal(ℚ(μ_n)/ℚ) ≅ (ℤ/nℤ)×`, every conjugacy class is a singleton, and `|G| = φ(n)`.

**Variables / typeclasses (Lean side):**
- `(n : ℕ)` — the modulus.
- `(a : ZMod n)` — the target residue class.

**Hypotheses (Lean side):**
- `(hn : 1 ≤ n)` — positive modulus (so `ZMod n` is a genuine finite ring and `φ(n) ≥ 1`).
- `(ha : IsUnit a)` — `a` is a unit in `ZMod n`, i.e. `gcd(a, n) = 1` (the coprimality hypothesis).

**Conclusion (math):** the prime-ideal set `{ (p) : p prime, p ≡ a (mod n) }` has
Dirichlet density `1/φ(n)`.

**Conclusion (Lean):**
```lean
HasDirichletDensity
  ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a})
  ((Nat.totient n : ℝ)⁻¹)
```
where:
- `HasDirichletDensity S δ` (project def, `Density.lean:64`, Sharifi 7.1.13) :=
  `Tendsto (fun s ↦ (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})) (𝓝[>] 1) (𝓝 δ)` — the
  analytic (Dirichlet) density via the Dedekind-zeta-style ratio as `s ↓ 1⁺`.
- the image-set is the set of *principal prime ideals* `(p)` of `𝓞 ℚ (= ℤ)` for
  rational primes `p ≡ a (mod n)`.
- `(Nat.totient n : ℝ)⁻¹` = `1/φ(n)`.

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

**Verdict: BIG.** Two independent triggers fire:
1. It is a **theorem named after a person** (Dirichlet) — a recognised, named
   landmark of analytic number theory, essentially guaranteed to be in the
   literature in some form.
2. It is a **declared main result** of the project — `## Main results`, second
   bullet of the `Main.lean` module docstring
   ("`Chebotarev.dirichlet_primes_in_AP` — Dirichlet's theorem on primes in
   arithmetic progressions, as a corollary").

(Note: literature width is EXHAUSTIVE regardless. Recorded for framing: this is a
headline corollary, not a helper.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`. (Body is a ~10-line proof: a `by_cases` on
`n % 4 = 2` dispatching to two sub-lemmas.)

---

## Phase 3 — Literature search (EXHAUSTIVE)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Dirichlet theorem primes AP **Dirichlet density** 1/phi(n), p ≡ a mod n" | **yes** | "For all coprime `a, m`, the set of primes `p ≡ a mod m` has **Dirichlet density `1/φ(m)`**" | Wikipedia, MIT 18.785 L18, Kedlaya ANT ch.4, Conrad (Stanford) "Dirichlet density for global fields" — **verbatim match to the Lean form** |
| 2 | WebSearch (general form / density axis) | "Serre Course in Arithmetic Dirichlet density vs natural density 1/phi(m), de la Vallée Poussin PNT for AP" | **yes** | both flavours hold with value `1/φ(N)`: **Dirichlet density** (Serre, real-variable, no PNT) ⊊ **natural density** (de la Vallée Poussin, needs PNT-for-AP) | Serre *A Course in Arithmetic* is the canonical reference for the **Dirichlet-density** form — exactly this project's form. Natural-density is strictly stronger. |
| 3 | WebSearch (named-after parent / specialisation) | "Chebotarev density theorem specialises to Dirichlet AP, cyclotomic field `ℚ(ζ_m)`, abelian case, density 1/phi(m)" | **yes** | `K = ℚ`, `L = ℚ(ζ_m)`, `Gal ≅ (ℤ/m)×`, each class a singleton, `|G| = φ(m)` ⇒ density of `p ≡ a` is `1/φ(m)` | Wikipedia (Chebotarev), MIT 18.785 L28, Triantafillou notes — **confirms the exact proof route** the project takes (Sharifi 7.2.3) |
| 4 | WebSearch (Lean/mathlib status) | "mathlib4 Lean Dirichlet **density** primes AP formalization 1/phi, natural density, not yet" | **partial** | — | The "Formalizing zeta and L-functions in Lean" project (arXiv 2503.00959) — which produced mathlib's `PrimesInAP` — states its goal as **infinitude** ("there are infinitely many prime numbers `p`"). No density result mentioned. |
| 5 | ChatGPT MCP | self-contained 3-part standard-form / generality / mathlib-status query | **n/a — MCP down** | — | fell back to WebSearch + WebFetch + nLab/EoM per the skill's documented fallback |
| 6 | Local references | grep `.mathlib-quality/references/` (and `refs/Chebotarev/`) | **n/a — absent** | — | no references dir in the project; `refs/` shared store not present in this checkout (PDFs are local-only: Sharifi `algnum.pdf` §7.2.3, SL `cheb.pdf`) |
| 7 | nLab | "Dirichlet theorem arithmetic progressions / Dirichlet density" | **partial** | — | nLab has no dedicated standalone page giving the density value; the concept lives under analytic NT / L-functions. Not a categorical concept. |
| 8 | Encyclopedia of Mathematics | "Dirichlet density" page | **yes** | "for each congruence class `c ∈ (ℤ/Nℤ)×` the set of primes `p ≡ c (mod N)` has **Dirichlet density `1/φ(N) = 1/|(ℤ/Nℤ)×|`**"; also states the natural-density (PNT-for-AP) version separately | EoM is an authoritative encyclopedic source — gives **both** the exact form and the Dirichlet-vs-natural distinction |
| 9 | Stacks Project / nCatLab | "Dirichlet density primes residue class" | **n/a** | — | Stacks: not in scope (no analytic-density-of-primes material). nCatLab: not a categorical concept. |
| 10 | recent arXiv (last 5y) | "primes arithmetic progression density / PNT for AP effective uniform" | **yes** | the strictly-stronger axes: **natural density** + **effective/quantitative** PNT-for-AP (error terms, large-modulus uniformity) | e.g. arXiv 2301.13457 "PNT for primes in AP at large values" — strengthenings, not weakenings, of the Dirichlet-density statement |

### Literature summary (Phase 3)

**Concept identified as:** Dirichlet's theorem on primes in arithmetic
progressions, **Dirichlet-density form** (value `1/φ(n)`).

**Sources agree on the standard form:** **yes.** Wikipedia, MIT 18.785 (L18 & L28),
Kedlaya (*Algebraic Number Theory* ch.4), Conrad's "Dirichlet density for global
fields", Serre (*A Course in Arithmetic*), and the Encyclopedia of Mathematics all
give exactly: *for coprime `a, n`, the set of primes `p ≡ a (mod n)` has Dirichlet
density `1/φ(n)`*. This is verbatim the Lean statement
(`HasDirichletDensity … (φ(n))⁻¹`).

**Most general standard form:** the *value* `1/φ(n)` is fixed across the literature;
the generality axes are the **density notion** and **error terms**, not the
hypotheses:
- **Dirichlet density `1/φ(n)`** — the weakest/cleanest statement (Serre: pure
  real-variable estimates, no PNT). **This is what the project formalises.**
- **Natural density `1/φ(n)`** — strictly stronger (de la Vallée Poussin; natural
  density ⇒ Dirichlet density, not conversely); requires PNT-for-AP-grade input.
- **Effective / uniform PNT-for-AP** — quantitative error terms, large-modulus
  uniformity (Siegel–Walfisz, Bombieri–Vinogradov, GRH-conditional). Far stronger.

**Generality dimensions where the literature varies:**
- *Density notion*: Dirichlet (weakest) ⊊ natural ⊊ effective/quantitative. The
  Lean form sits at the **weakest, cleanest** rung — the canonical textbook
  Dirichlet-density statement.
- *Hypotheses*: invariant — every source requires exactly `1 ≤ n` and `gcd(a,n)=1`
  (i.e. `a ∈ (ℤ/n)×`). No source weakens these; they are necessary (if `gcd(a,n)>1`
  the class contains at most one prime, density 0).

**Disagreement with the literature:** **none.** The Lean form is the
literature-standard Dirichlet-density statement at its canonical (weakest, cleanest)
generality, with the exact necessary hypotheses.

---

## Phase 4 — Generality analysis

**Literature-standard form (from Phase 3):** for `1 ≤ n` and `a ∈ (ℤ/n)×`, the
primes `p ≡ a (mod n)` have **Dirichlet density** `1/φ(n)`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `(hn : 1 ≤ n)` | `n ≥ 1` | `n ≥ 1` (positive modulus) | **no** | `n = 0` makes `ZMod 0 = ℤ` and `φ(0) = 0`, so `1/φ(n)` is undefined; the statement is vacuous/false there. Exactly the standard hypothesis. |
| 2 | `(ha : IsUnit a)` | `a ∈ (ℤ/n)×`, i.e. `gcd(a,n)=1` | `gcd(a,n)=1` | **no** | **Necessary.** If `gcd(a,n) = d > 1`, the residue class `a mod n` contains at most the prime divisors of `d` (finitely many), so its Dirichlet density is `0 ≠ 1/φ(n)`. Coprimality is exactly the content. Every source assumes it. |
| 3 | density notion (`HasDirichletDensity`) | Dirichlet density | Dirichlet (weak) **or** natural (strong) | the *natural-density* form is strictly **stronger**, not weaker | Natural density ⇒ Dirichlet density (not conversely); the stronger form needs PNT-for-AP input mathlib does not have. A **strengthening**, not a weakening. |
| 4 | base field (implicit `ℚ` / `𝓞 ℚ`) | `ℚ`, prime ideals of `ℤ` | (this *is* the classical Dirichlet statement; the global-field lift *is* Chebotarev) | n/a — already the special case | The "more general" object here is Chebotarev over a general number field — which the project **already has** as `chebotarev_density`. This decl is precisely its `ℚ`/cyclotomic corollary. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** for the Dirichlet-density statement —
it is exactly the canonical textbook theorem, with the exact necessary hypotheses
(`n ≥ 1`, `gcd(a,n)=1`) and the weakest (cleanest) density notion.

Number of weakening opportunities found: **0**. Neither hypothesis can be
weakened (both are necessary). The only "more general" directions are
*strengthenings* (natural density; effective error terms) requiring analytic
machinery mathlib lacks — and these are different/stronger theorems, not
assumption-weakenings of this proof.

Cost of "strengthening" to natural density or effective PNT-for-AP: **EXPENSIVE —
needs new ideas** (PNT-for-AP-grade analytic input). Per the skill's cost rule
this does **not** downgrade the verdict and does **not** make it
YES-but-generalise — those are follow-on theorems, not a better statement of
*this* result.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Downstream this enables |
|---|----------|----------|------------------------|-------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | **already done** | hypotheses are `1 ≤ n` (a `Prop` arg) and `IsUnit a` (the idiomatic mathlib unit predicate, matching `Nat.infinite_setOf_prime_and_eq_mod`) | already maximally idiomatic; mirrors mathlib's own `PrimesInAP` API shape |
| 2 | sequences/metric → filters/topology? | **already done** | density is `Tendsto … (𝓝[>] 1) (𝓝 δ)` (filter form), not an ε-sequence | composes with mathlib's filter-limit API |
| 3 | construct an object → universal-property class? | no | — | the statement is a `Prop` asserting a density value; nothing to characterise universally |
| 4 | set-with-closure → bundled substructure? | no | — | `Set (Ideal …)` + `HasDirichletDensity` is the right shape; the value is a real number |
| 5 | vector-space/field-specific → weaken typeclasses? | no | — | already at `ℚ`; this *is* the classical special case (the general-field version is `chebotarev_density`, already present) |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorical statement |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary structure? | **partial — but the general object already exists** | the "index-generalised" form is Chebotarev over a general number field, i.e. `chebotarev_density` (Main.lean:71), of which this is the `ℚ`/cyclotomic specialisation | mathlib will want **both**: the general Chebotarev *and* this named classical corollary (Dirichlet AP is the famous statement users search for by name) |

**Modern-idiom verdict: no further modernisation move available.** The statement
already uses contemporary mathlib idioms (`IsUnit` unit predicate matching
mathlib's own AP API; filter-based `Tendsto` density; `Ideal.span` / prime
ideals). The "more general index" is the general-number-field Chebotarev, which the
project **already** ships as `chebotarev_density` — and this decl is deliberately
the *named classical corollary* of it. Mathlib wants the corollary under its
famous name (Dirichlet) **in addition to** the general theorem, exactly as it
already keeps `Nat.infinite_setOf_prime_and_eq_mod` as a named statement rather
than only a one-off specialisation. So this is **not** a "generalise-first" case:
the general form coexists, and the named corollary is independently wanted.

---

## Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (no definitional equalities / typeclass-search
paths introduced). Skipped.

> Carried to Phase 7 (shared with the `chebotarev_density` assessment): the
> *supporting definition* `HasDirichletDensity` (`Density.lean:64`) is a `def` and
> warrants its own Phase-4.5 pass when **it** is upstreamed. It is out of scope for
> this single-declaration (theorem) assessment but is the real definitional
> prerequisite this theorem travels with.

---

## Phase 5 — Mathlib search (five-method)

```
### Mathlib search-status: Chebotarev.dirichlet_primes_in_AP

[A] Lean-Finder       (MCP unavailable in this env)   n/a — tool not loadable; substituted grep [D] + live docs fetch
[B] Loogle            (MCP unavailable in this env)    n/a — tool not loadable; substituted grep [D]
[C] LeanSearch        (MCP unavailable in this env)    n/a — tool not loadable; substituted grep [D] + WebFetch of mathlib4 docs
[D] Grep mathlib src  "DirichletDensity|dirichlet_density|analyticDensity|naturalDensity"   NO HITS in .lake/packages/mathlib/
                      "density of (the )?primes|natural density.*prime"                       NO HITS
                      "chebotarev|cebotarev|čebotarev"                                         NO HITS
                      "totient n.*⁻¹ | / .*totient (as a density value)"                       NO HITS (only PrimeCounting.lean upper bounds, unrelated)
                      "infinite_setOf_prime_and_eq_mod | forall_exists_prime_gt_and_eq_mod"   HITS — NumberTheory/LSeries/PrimesInAP.lean (INFINITUDE only)
                      "HasDirichletDensity|frobeniusClass" (project defs in mathlib?)          NO HITS
                      ("IsUnramifiedIn" hit = mathlib's *infinite-place* ramification, unrelated to the project's prime-ideal `UnramifiedIn`)
[E] Name pattern      (lean_local_search unavailable; grep over project + mathlib used)        as above

[live] WebFetch mathlib4 docs PrimesInAP.html — enumerated all 26 decls on the page:
       21 auxiliary + 6 "Main" results, ALL infinitude (set is Infinite / ∃ prime > n / frequently atTop).
       Fetch conclusion, verbatim: "No density statements appear."
```

**Searched for both forms:**
- *User's form* (Dirichlet density `1/φ(n)` of primes `≡ a mod n`): **not in mathlib.**
- *Literature-standard / stronger forms* (natural density `1/φ(n)`; any
  "density / asymptotic proportion of primes in a residue class"; Chebotarev):
  **not in mathlib.** Mathlib's `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`
  proves Dirichlet's theorem in **infinitude form only** — its own module docstring
  (lines 58–64) says "We give two versions of Dirichlet's Theorem", and **both** are
  infinitude (`Nat.infinite_setOf_prime_and_eq_mod`: the set is `Infinite`;
  `Nat.forall_exists_prime_gt_and_eq_mod`: `∃ p > n`). There is **no density layer**
  anywhere in mathlib (no `HasDirichletDensity`, no analytic density of prime
  ideals at all).

**Concluded:** **not in mathlib** (all available methods exhausted, plus the
live docs-page fetch, plus the literature-standard and stronger forms). The
closest mathlib result, `Nat.infinite_setOf_prime_and_eq_mod`
(`PrimesInAP.lean:475`), is the **infinitude** statement that this theorem
**strictly refines** — and the project's own docstring (Main.lean:511–512) names it
exactly so: *"a density refinement of `Nat.infinite_setOf_prime_and_eq_mod`"*.

---

## Phase 6 — Composition check (+ call-sites)

### 6.0. Call sites — `Chebotarev.dirichlet_primes_in_AP`

Internal use count: **0** (within the project, excluding the declaring site).
External-to-file callers: 0. The only other repo occurrences are a **docstring
mention** (Main.lean:39, `## Main results`) and a **section header**
(Main.lean:160, "Sub-lemmas for `dirichlet_primes_in_AP`"). No `.lean` consumer
calls it.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | — this is a terminal `## Main results` deliverable, not an API root |

Inline-derivation grep (was the `1/φ(n)`-density statement re-derived elsewhere
without this lemma?): **none.**
(`grep -rnE "totient.*HasDirichletDensity|HasDirichletDensity.*totient"` outside
`Main.lean` → empty.)

**Reading per the Phase-6 call-site table:** `K = 0` here is the **"terminal
headline theorem"** pattern, *not* the "dead one-liner / wrapper consumers bypass"
pattern. This decl is a named `## Main results` corollary (Phase 2a BIG) — the
project's *output*, the thing a downstream user would `import` and cite by name.
Such capstones legitimately have zero internal callers (nothing in the project sits
*above* Dirichlet's theorem). It is built *from* the project's machinery
(`chebotarev_cyclotomic`, via `dirichlet_AP_main` / `dirichlet_AP_two_mul`), so it
is a genuine consumer of the API, not dead code. The K=0 therefore does **not**
weaken the YES case (contrast: a K=0 *one-liner with no exemption* would).

### 6a. Composition attempt

Can `dirichlet_primes_in_AP` be derived from **mathlib** in ≤3 chained calls?

- **Attempt 1 — from mathlib's `Nat.infinite_setOf_prime_and_eq_mod`:** **fails.**
  This is the crux. Mathlib's theorem gives only that the set is *infinite*;
  the target asserts a precise *Dirichlet density* `1/φ(n)`. **Infinitude does not
  imply density** (a set can be infinite with any density in `[0,1]`, or no density
  at all). There is no mathlib lemma turning "infinite residue class of primes"
  into "Dirichlet density `1/φ(n)`" — that implication *is* the theorem.
- **Attempt 2 — from any mathlib density-of-primes lemma:** **fails at step 0.**
  Mathlib has **no** notion of Dirichlet/analytic density of a set of primes at all
  (Phase 5). There is nothing to chain from.
- **Attempt 3 — assemble from L-function non-vanishing + Dedekind zeta:** **fails.**
  This is not a 1–3-call composition; it is the entire analytic content. The project
  proof routes through `chebotarev_cyclotomic` (the cyclotomic/abelian case of
  Chebotarev — itself a large multi-file development on top of
  `HasDirichletDensity`) plus a symmetric-difference density-closure lemma. The
  building blocks (Dirichlet L-functions, their non-vanishing on `re s ≥ 1`) exist
  in mathlib; the *density theorem* does not, and bridging the gap is a substantial
  development, not a composition.

**Conclusion: NOT-COMPOSABLE.** Mathlib has the infinitude statement (which this
strictly strengthens) and the L-function bricks, but neither composes in ≤3 calls
to the density statement — the missing piece (an analytic density layer +
Chebotarev's cyclotomic case) is exactly the new content.

---

## Phase 7 — Verdict

## Verdict: `Chebotarev.dirichlet_primes_in_AP`

**Category:** YES-add-as-is

**Evidence:**
- **Literature search (Phase 3):** the Dirichlet-density form `1/φ(n)` is *the*
  canonical textbook statement — agreed verbatim across Wikipedia, MIT 18.785,
  Kedlaya, Conrad, Serre (*A Course in Arithmetic*), and the Encyclopedia of
  Mathematics; the Lean form matches exactly, with the exact necessary hypotheses.
- **Generality analysis (Phase 4):** MAXIMALLY GENERAL for the Dirichlet-density
  statement (both hypotheses necessary, weakest/cleanest density notion). The only
  "more general" axes (natural density; effective PNT-for-AP) are
  *stronger/different* theorems, not weakenings (cost EXPENSIVE, non-downgrading per
  the rules). Modern-idiom: already idiomatic (`IsUnit`, filter `Tendsto` density);
  the "general index" (general-field Chebotarev) already coexists as
  `chebotarev_density`, so this is a wanted *named corollary*, not generalise-first.
- **Mathlib search (Phase 5):** not in mathlib by any method, confirmed by a live
  fetch of the mathlib4 `PrimesInAP` docs page ("No density statements appear").
  Mathlib has Dirichlet's theorem in **infinitude form only**; **no** analytic
  density of primes exists anywhere in the library.
- **Composition check (Phase 6):** NOT-COMPOSABLE — infinitude does not imply
  density, and mathlib has no density-of-primes layer to chain from; the missing
  content is exactly the analytic density layer + Chebotarev's cyclotomic case.

**Rationale.**
Dirichlet's theorem on primes in arithmetic progressions is a named landmark, and
mathlib has it — but only as **infinitude** (`Nat.infinite_setOf_prime_and_eq_mod`
and friends in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`, whose own docstring
says it gives "two versions", both of which are "the set is infinite / there exists
a prime `> n`"). This declaration proves the strictly stronger **density**
statement: not merely that infinitely many primes are `≡ a (mod n)`, but that they
occupy a precise Dirichlet density `1/φ(n)` — the equidistribution refinement. A
live fetch of mathlib's docs page and an exhaustive grep of the vendored tree both
confirm mathlib has **no** notion of Dirichlet/analytic density of primes at all;
the gap is total, not partial. And the gap is genuine new content, not a
composition: infinitude does not imply density (the implication *is* the theorem),
and there is no density-of-primes primitive in mathlib to chain from — so the
NOT-COMPOSABLE finding is firm. The statement is, moreover, exactly the
literature-standard Dirichlet-density form (Serre; EoM) at its canonical generality,
with both hypotheses (`n ≥ 1`, `gcd(a,n)=1`) necessary and the weakest clean density
notion, written in modern mathlib idiom (`IsUnit`, filter `Tendsto`). There is no
weaker hypothesis set this proof supports, and the stronger statements (natural
density; effective PNT-for-AP) are separate analytic developments rather than
reformulations — so the verdict is add-as-is, not generalise-first.

This decl is the abelian/cyclotomic **corollary** of the project's
`chebotarev_density` (`K = ℚ`, `L = ℚ(μ_n)`, Sharifi 7.2.3), exactly as the
literature presents the Chebotarev → Dirichlet specialisation. It therefore
upstreams **with** Chebotarev, as the named capstone corollary in the same PR chain
— mathlib wants it under its famous name (Dirichlet) *in addition to* the general
theorem, just as it already keeps `Nat.infinite_setOf_prime_and_eq_mod` as a named
statement. The `K = 0` internal-call count is the normal "terminal headline result"
pattern (nothing in the project sits above Dirichlet's theorem), not a dead-wrapper
signal, so it does not weaken the YES.

**The one real subtlety** is packaging, not mathematical content (shared with the
`chebotarev_density` assessment): the statement is phrased via the *project*
definition `HasDirichletDensity`, which does not exist in mathlib. Mathlib will want
that promoted to a canonical definition (with its own `def`-level diamond/defeq and
naming review) **before or together with** this theorem. That is sequencing, not a
downgrade: the theorem is the right statement; it travels with its definitional
prerequisite.

**WHY add it (refactor-actionable):**
- *New mathematical content mathlib is missing:* the **density** refinement of
  Dirichlet's theorem. Mathlib today proves only infinitude
  (`Nat.infinite_setOf_prime_and_eq_mod`); it has **no** Dirichlet/analytic density
  of primes whatsoever. This supplies the equidistribution constant `1/φ(n)`.
- *The specific gap, named:* mathlib's `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`
  is **explicitly infinitude-only** (module docstring: "two versions of Dirichlet's
  Theorem", both infinitude; live docs fetch: "No density statements appear"). The
  project's own docstring names this decl as *"a density refinement of
  `Nat.infinite_setOf_prime_and_eq_mod`"* — i.e. it fills the exact stated gap atop
  the existing mathlib theorem. (Broader: the analytic density layer it needs is the
  same one the FLT and PNT+ projects want for Chebotarev — see
  `chebotarev_density.md`.)
- *How it composes with mathlib:* it sits directly on mathlib's Dirichlet
  L-function infrastructure (`DirichletCharacter.LFunction*`, the non-vanishing on
  `re s ≥ 1` already in `PrimesInAP`) and on `Nat.totient` / `ZMod n` units; once
  present it is the named, citable density form of `infinite_setOf_prime_and_eq_mod`,
  and the `ℚ`-shadow of the general `chebotarev_density`.

**Proposed mathlib location:**
`Mathlib/NumberTheory/NumberField/Chebotarev.lean` (the capstone file, alongside
`chebotarev_density`), with the analytic density layer in
`Mathlib/NumberTheory/NumberField/DirichletDensity.lean`
(the `HasDirichletDensity` definition + Dedekind-zeta `s→1⁺` asymptotics). Placing
the named Dirichlet-AP-density corollary next to Chebotarev (rather than editing
`LSeries/PrimesInAP.lean`) keeps it with the theorem it is a corollary of; a
one-line cross-reference can be added near `Nat.infinite_setOf_prime_and_eq_mod`.

**Proposed PR title:**
`feat(NumberTheory): Dirichlet's theorem on primes in AP, Dirichlet-density form (1/φ(n))`

**PR grouping (required — ship with the Chebotarev chain):** this is the capstone
corollary of `chebotarev_density`; it cannot be stated without
`HasDirichletDensity` and cannot be proved without the cyclotomic case
`chebotarev_cyclotomic`. Per the sibling `chebotarev_density.md` plan, the chain is:
1. `feat(NumberTheory): Dirichlet density of a set of prime ideals` — the
   `HasDirichletDensity` def + Dedekind-zeta `s→1⁺` asymptotics (`Density.lean`).
2. `feat(NumberTheory): Frobenius conjugacy class of an unramified prime`
   (`Frobenius.lean`) — needed for the general Chebotarev, not strictly for this
   `ℚ`-corollary, but part of the same upstreaming.
3. `feat(NumberTheory): Chebotarev abelian/cyclotomic case`
   (`Abelian.lean`, `FixedFieldDensity.lean`, `Cyclotomic.lean`) — the analytic core
   this corollary consumes.
4. `feat(NumberTheory): Chebotarev's density theorem` + **its corollaries**
   `density_split_completely` **and this `dirichlet_primes_in_AP`** — the capstone PR.

The single-declaration verdict here is YES-add-as-is; in practice it ships in PR (4)
as the named corollary, since it depends on (1) and (3).

**Pre-PR checklist before opening:**
- [ ] `/generalise Chebotarev.dirichlet_primes_in_AP` — confirm no easy weakening
      (expected: none; both hypotheses are necessary). Optionally surface a
      `ZMod`-free `Nat.Coprime a n` restatement variant matching mathlib's
      `forall_exists_prime_gt_and_modEq` API shape.
- [ ] `/mathlibable` the supporting **def** `HasDirichletDensity` individually — it
      needs a Phase-4.5 diamond/defeq pass before upstreaming (this theorem-level run
      skipped 4.5).
- [ ] `/cleanup` the files in the PR chain (style audit + diff gates).
- [ ] Pick a reviewer from recent `Mathlib/NumberTheory/LSeries/` (PrimesInAP
      authors: Stoll / Loeffler) and `Mathlib/NumberTheory/NumberField/` committers;
      flag that this is the density refinement of the existing infinitude theorem.

---

## Next step

YES-add-as-is. Upstream as the **named capstone corollary** of `chebotarev_density`
in PR (4) of the Chebotarev chain (see `chebotarev_density.md`): land the
`HasDirichletDensity` definition layer (PR 1) and the cyclotomic/abelian core
(PR 3) first, then ship `dirichlet_primes_in_AP` alongside `density_split_completely`
under the Chebotarev capstone PR, with a cross-reference added near mathlib's
existing infinitude theorem `Nat.infinite_setOf_prime_and_eq_mod`. Before opening:
`/mathlibable` the `HasDirichletDensity` def, then `/generalise` (expect no
weakening) and `/cleanup` the chain.
