# `/mathlibable` report — `PadicLFunctions.zetaNum_one`

Mode A (single declaration), full 10-phase workflow with the exhaustive 9-channel
literature search. ChatGPT MCP was unavailable in this environment (recorded `n/a`);
all other channels ran.

---

## Verdict (summary)

**`NO-composable-from-mathlib` is NOT applicable; the verdict is `BORDERLINE-needs-human`,
leaning strongly `NO` (do not upstream as-is).**

See Phase 7 for the full evidence trail and numbered questions. In one line: the
*theorem* (residue of the Kubota–Leopoldt p-adic zeta at `s = 1` is `1 − p⁻¹`) is
canonical, but **`zetaNum_one` is not that theorem** — it is an intermediate
"total-mass" bookkeeping identity stated entirely in terms of this project's own
construction stack (`PadicMeasure`, `zetaNum`, `muA`, `extLog`, `padicLog`), **none
of which exists in mathlib**. It cannot enter mathlib until that entire stack does,
and even then its mathlib-idiomatic form would look different.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task instruction — `.lake/build/lib` exists; on `main`, not re-elaborated)
- decl `PadicLFunctions.zetaNum_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:1666`
- kind:                      theorem
- has sorry:                 no (0 sorries in body lines 1666–1681; transitive dependencies `constantCoeff_mahlerK_rhoA_eq_algebraMap`, `constantCoeff_mahlerK_rhoA`, `map_extLog_natCast` are all real proofs, no sorry)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7)" — analyticity/pole and residue `1 − p⁻¹` of the Kubota–Leopoldt p-adic zeta branches, via the §4 numerator measure and the T523 exp/log bridge.

---

### Statement (Phase 1)

`PadicLFunctions.zetaNum_one` is a **theorem** stating the following.

Fix an odd prime `p`. Let `a` be a natural number with `p ∤ a` and `a ≠ 0`. Consider
the project's numerator measure `μ_a = zetaNum p a`, a `ℤ_p`-valued p-adic measure on
the units `ℤ_p^×` (defined as `x⁻¹ · Res_{ℤ_p^×}(μ_a)`, where `μ_a` is RJW's §4
measure whose Mahler transform is `F_a`). The theorem computes the **total mass** of
this measure — its pairing against the constant function `1 ∈ C(ℤ_p^×, ℤ_p)` — and
asserts, after coercing `ℤ_p ↪ ℚ_p`:

> `∫_{ℤ_p^×} x⁻¹ dμ_a = − (1 − p⁻¹) · log_p(a)`,

where `log_p` here is the project's **extended (Iwasawa-branch, `log_p p = 0`)
logarithm** `extLog`, evaluated at `(a : ℚ_[p])`.

This is RJW Theorem 7's "`eq:zeta p residue 2`" total-mass identity (TeX 2268), the
key analytic input to the residue computation: it is computed in a field `ℂ_p ⊇ ℚ_p(μ_p)`
containing a primitive `p`-th root of unity, then descended to `ℚ_p` by injectivity of
the structure map `ℚ_p ↪ ℂ_p`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the fixed prime (project-wide `variable`).
- (implicit at use) `ℂ_[p]` carries `NeZero (p : ℂ_[p])`, is algebraically closed and char 0 — supplies the primitive `p`-th root of unity in the proof.

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — odd prime (needed for `extLog`/Teichmüller machinery and the integer topological generator).
- `{a : ℕ}`, `ha : ¬ (p : ℕ) ∣ a` — `a` is a `p`-adic unit (so `extLog(a)` is on-domain via the Fermat witness `a^{p−1} ∈ 1 + p·ℤ_p`).
- `ha0 : a ≠ 0` — nonzero (needed for `constantCoeff_mahlerK_rhoA`).

Conclusion (math): the total mass of the numerator measure equals `−(1 − p⁻¹)·log_p a`.

Conclusion (Lean):
```lean
(((PadicMeasure.zetaNum p a (1 : C(ℤ_[p]ˣ, ℤ_[p]))) : ℤ_[p]) : ℚ_[p])
  = -(1 - (p : ℚ_[p])⁻¹) * extLog p (((a : ℕ) : ℚ_[p]))
```

---

### Size classification (Phase 2a)

Verdict: **BIG**

Reason: it is a *main analytic input* of the project's §7 residue computation — the
total-mass identity TeX 2268 that the simple-pole/residue theorem (`zetaPBranch`
residue at `s = 1`) consumes directly at `ResidueZeta.lean:1819`. It is named after
the source equation (`eq:zeta p residue 2`) and is the substance of a paper theorem,
not a helper.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing.)

### One-line check (Phase 2b)

Body line count: ~6 substantive lines (a `haveI`, `obtain`, `refine`, and a 4-line `rw` chain).
One-liner verdict: **n/a** — kind is `theorem`, not a `def`/`abbrev`/`structure`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic L-function residue at s=1 Kubota-Leopoldt total measure ∫ x⁻¹ μ = −(1−p⁻¹) log_p a"            | partial | residue `1 − p⁻¹` confirmed; the specific total-mass identity not found by name | residue is canonical; the exact `∫ x⁻¹ dμ_a` step is not a named result |
|  2 | WebSearch (general form / residue)| "p-adic zeta function residue s=1 simple pole 1 − p⁻¹ Iwasawa p-adic logarithm measure"               | yes  | "simple pole at `s=1` with residue `1 − p⁻¹`", mirrors `ζ(s)` at `1`; pseudo-measure construction | matches the module docstring verbatim (RJW Thm 7.1) |
|  3 | WebSearch (construction / aliases)| "Kubota-Leopoldt p-adic zeta numerator measure μ_a Mahler transform F_a antiderivative log residue"   | yes (context) | Mazur/Coleman measure construction via Mellin/Amice/Mahler transform; residue via measures | Guitart, Coates (Astérisque), Rodrigues-Jacinto/Williams; route-specific bookkeeping |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of the residue/total-mass identity")     | n/a  | tool not available in this environment | recorded n/a — no ChatGPT MCP tool present; compensated by extra WebSearch + WebFetch channels |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` for extLog / zetaNum / residue            | n/a  | directory absent (`.mathlib-quality/` has only `overview/`) | recorded n/a — no `references/` dir for this project |
|  6 | nLab                             | `ncatlab.org/nlab/show/p-adic+L-function`                                                              | n/a  | HTTP 404 — no such nLab page | nLab has no dedicated p-adic-L-function page; concept is analytic-NT, not categorical |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not a categorical concept | the residue/total-mass of a p-adic measure is analytic number theory, no categorical statement |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept | p-adic L-function residue is not in the Stacks scope (schemes/stacks) |
|  9 | MathOverflow / Math.StackExchange| "p-adic zeta residue at s=1 = 1 − 1/p Coleman map total mass logarithm"                                | yes  | residue `1 − p⁻¹` reconfirmed; Coleman-map context | no MO thread surfacing the exact `∫ x⁻¹ dμ_a` identity as a standalone named lemma |
| 10 | recent arXiv (last 5 years)      | "introduction to p-adic L-functions" (2309.15692 Rodrigues-Jacinto/Williams); "Sum expressions for KL" (2201.08870); Lean-3 formalization (2302.14491) | yes | residue `1 − p⁻¹` in the standard intro notes (= the project's RJW source); a *Lean 3* KL formalization exists but is NOT in current mathlib | the intro notes are exactly RJW; the residue is textbook, the intermediate measure-mass step is construction-internal |

Protocol pass check:
- WebSearch ran **≥3 distinct queries** at different levels (specific identity, residue/general, construction/aliases). ✓
- ChatGPT MCP: **n/a, with reason** (tool absent) — compensated by two extra WebFetch attempts + a fourth WebSearch. ✓ (honest n/a, not a skip)
- Local references: **checked**, recorded n/a (directory absent). ✓
- nLab: **checked** (404; no page). ✓
- Stacks / nCatLab / MathOverflow / arXiv: **each checked or n/a with reason**. ✓
  (WebFetch of the source PDFs — arXiv 2309.15692, Guitart's KL notes, the LTCC notes —
  returned binary/403/404 and could not be parsed for verbatim quotes; the residue value
  was nonetheless confirmed by the search snippets of those same documents.)

### Literature summary (Phase 3)

Concept identified as: **the residue of the Kubota–Leopoldt p-adic zeta function at
`s = 1`** (canonical: simple pole, residue `1 − p⁻¹`), of which `zetaNum_one` is the
**total-mass / numerator-measure input** in one specific construction route (RJW =
Rodrigues-Jacinto/Williams §7, mirroring Mazur–Coleman).

Sources agree on the standard form: **yes** for the *headline residue* `1 − p⁻¹`
(Wikipedia-level, all intro notes, the project's own RJW source). **No** standard
named form exists for the *intermediate identity itself*: the total mass
`∫_{ℤ_p^×} x⁻¹ dμ_a` is construction-specific bookkeeping. Different constructions
(Mazur measure `μ_c`, Coleman map, Amice/Mahler transform) package this step
differently; there is no canonical "lemma name" for it across the literature.

Most general standard form: the *residue theorem* (`ζ_{p,p−1}` has a simple pole at
`s=1` with residue `1 − p⁻¹`). The *total-mass identity* is a means to that end, tied
to the chosen measure `μ_a` and to a chosen normalisation of the p-adic logarithm
(here the Iwasawa branch `log_p p = 0`).

Generality dimensions where the literature varies:
- **Construction route**: Mazur (`μ_c`, `c` an auxiliary unit) vs. RJW's `μ_a` numerator
  measure vs. Coleman/Mellin. The mass-identity's exact shape depends on the route.
- **Logarithm normalisation**: Iwasawa branch (`log_p p = 0`, used here via `extLog`) vs.
  other branches. The `−(1 − p⁻¹)·log_p(a)` form is branch-dependent.
- **Base ring of computation**: the project computes in `ℂ_p` (needs `μ_p ⊂ ℂ_p`) then
  descends; other treatments work directly over `ℚ_p(μ_p)` or via distributions.

Disagreement with the literature: **none** on the residue value. The project's
`zetaNum_one` is a faithful, branch-explicit, construction-internal restatement of a
TeX-2268 step from its named source (RJW). It is **not** a result the literature
states standalone under a recognizable name.

---

### Generality analysis — `PadicLFunctions.zetaNum_one`

Literature-standard form (from Phase 3): there is no standalone literature-standard
form for *this identity*; the standard object is the residue `1 − p⁻¹`, of which this
is a route-specific input. The comparison below is therefore against "the most natural
mathlib-idiomatic phrasing if the whole construction stack existed".

| # | Parameter / hypothesis        | Current Lean form                      | Literature-standard / idiomatic form | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|----------------------------------------|--------------------------------------|---------------------|---------------------------------|
| 1 | `[Fact p.Prime]`, `hp2 : p ≠ 2` | odd prime                             | odd prime (`p = 2` excluded everywhere in the theory) | NO | the entire `extLog`/Teichmüller/integer-topological-generator machinery genuinely needs `p` odd; `p = 2` is a real exclusion in the literature too |
| 2 | `{a : ℕ}`, `ha : ¬ p ∣ a`     | `a` a natural, prime to `p`            | `a` a `p`-adic unit / element of `ℤ_p^×` | partial-but-pointless | the proof uses the Fermat witness `a^{p−1} ≡ 1` which holds for any unit, but `a : ℕ` is exactly what RJW's integer topological generator needs at the call site (`ResidueZeta.lean:1819`); generalising to `ℤ_p^×` would not serve the one consumer |
| 3 | `extLog p ((a : ℚ_[p]))`       | project's extended Iwasawa-branch log  | a mathlib `padicLog` / p-adic log API | YES (but blocked) | the *right* statement uses a mathlib p-adic logarithm — **which does not exist** (Phase 5). Until it does, the form is forced to use the project's `extLog`. This is the dominant blocker. |
| 4 | `PadicMeasure.zetaNum p a`     | project's numerator measure (continuous dual `C(ℤ_p^×,ℤ_p) →ₗ ℤ_p`) | a mathlib p-adic-measure / Coleman-map object | YES (but blocked) | the *right* statement uses a mathlib notion of p-adic measure on `ℤ_p^×` — **also does not exist** (Phase 5). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what the single consumer needs**, but
**STRICTLY NARROWER / NON-IDIOMATIC relative to any future mathlib form** — because it
is phrased over project-local objects (`zetaNum`, `extLog`) that mathlib would replace
with general p-adic-measure and p-adic-logarithm APIs.

Number of weakening opportunities found: **2 substantive** (rows 3 and 4), but **both
are blocked**: they require mathlib infrastructure that does not exist. The weakening
is not "weaken a hypothesis" but "restate against absent mathlib primitives".

Proposed restatement (if/when the stack is upstreamed): a `Mathlib`-namespaced
`zetaNum_one`/`KubotaLeopoldt.totalMass` stated against a mathlib p-adic measure and a
mathlib `padicLog`, with `a ∈ ℤ_p^×` rather than `a : ℕ` prime to `p`.

Cost of restatement: **EXPENSIVE** — not a mechanical rewrite; it presupposes that
`PadicMeasure`, `zetaNum`, `muA`, the Mahler/Amice transform, `padicExp`/`padicLog`,
and `extLog` are all first upstreamed to mathlib. (Cost does not by itself downgrade a
verdict — but here the *absence of the prerequisites*, not the cost, is decisive.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | Could "let X be a foo" preambles become typeclasses / instances?                                       | no       | hypotheses are already minimal (`Fact p.Prime`, `p ≠ 2`, `p ∤ a`) | n/a |
|  2 | Sequences/metric where filters/topological would generalise?                                           | no       | the statement is an equation of `ℚ_p` values, no limit here (the limit/`Tendsto` lives in the *consumer* at line 1819, already filter-based via `nhdsWithin`) | n/a |
|  3 | Construct an object where a universal-property class would characterise it?                            | partial  | the *whole p-adic-measure layer* could be the continuous dual / Amice-transform universal object — but that is a mathlib-infrastructure project, not a reformulation of *this* lemma | would enable the entire p-adic-L-function API; far beyond one lemma |
|  4 | Set-with-closure-predicate where a bundled substructure would compose?                                 | no       | n/a — `PadicMeasure` is already a bundled `LinearMap` (`C(X,ℤ_p) →ₗ[ℤ_p] ℤ_p`) | n/a |
|  5 | Vector-space/metric/field-specific result mathlib would weaken to modules/(semi)ring?                  | no       | already over `ℚ_p`/`ℤ_p`/`ℂ_p` at the correct generality for the statement | n/a |
|  6 | 1-categorical statement with a higher-categorical generalisation?                                      | no       | this is an arithmetic identity, not categorical | n/a |
|  7 | Concrete index (ℕ,ℤ,ℝ) that would generalise to additive groups/monoids?                               | no (substantively) | `a : ℕ` → `a ∈ ℤ_p^×` is possible (row 2) but does not help the sole consumer | none — see Phase 4a row 2 |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this lemma in isolation*). The only "modernisation"
is the wholesale upstreaming of the p-adic-measure + p-adic-log infrastructure (4c row 3),
which is an infrastructure programme, not a reformulation of `zetaNum_one`. There is no
contemporary-idiom restatement of this single declaration that is a real organisational
improvement *given mathlib as it stands today*.

One-line reason this is not a modernisation move: every "better" form requires mathlib
primitives that do not exist, so the improvement is "build the whole theory in mathlib",
not "restate this lemma".

---

### Diamond / defeq risk — `PadicLFunctions.zetaNum_one`

n/a — declaration kind is **theorem** (Phase 4.5 is skipped for `theorem`/`lemma`; no
definitional equalities or typeclass-search paths are introduced).

---

### Mathlib search-status: `PadicLFunctions.zetaNum_one`

[A] Lean-Finder       (tool not available here; substituted by targeted WebSearch "mathlib Lean Kubota Leopoldt p-adic L-function") → **no hit in current mathlib**; only the Lean 3 formalization (Narayanan, arXiv:2302.14491) which is not in mathlib
[B] Loogle            type-pattern `extLog`, `PadicMeasure`, `C(ℤ_[p]ˣ, ℤ_[p]) →ₗ ℤ_[p]`, `padicLog` (tool not directly callable; resolved by grep of mathlib source, method D) → **n/a: resolved via D**
[C] LeanSearch        natural language "p-adic zeta residue", "total mass of p-adic measure on units", "extended p-adic logarithm" (tool not directly callable; substituted by WebSearch on mathlib formalization) → **no hit in mathlib**
[D] Grep mathlib src  `grep -rln` over `.lake/packages/mathlib/Mathlib/` for: `Kubota|Leopoldt|padicLFunction|p-adic L-function|p-adic zeta` → **0 files**; `extLog|ExtLogDomain` → **0 files**; `padicLog`/`padicExp`/p-adic logarithm/exponential → **0 files** (the only superficial match, `NumberTheory/Padics/ProperSpace.lean`, was the word "compactSpace", unrelated); `PadicMeasure|Amice transform|Mahler transform` → **0 relevant** (only `Padics/AddChar.lean`, p-adic additive characters, unrelated)
[E] Name pattern      project grep confirmed every dependency is project-local: `padicLog` at `PadicLFunctions/PadicExp.lean:384`; `extLog` at `ExtLog.lean:286`; `zetaNum`/`muA`/`PadicMeasure` in `KubotaLeopoldt/` and `Measure/Basic.lean` → **none in mathlib namespace**

Searched for both:
  - the user's current form (`zetaNum p a 1 = −(1−p⁻¹)·extLog a`) — absent.
  - the literature-standard form (residue `1 − p⁻¹` of the KL p-adic zeta; any
    p-adic-measure total-mass or p-adic-logarithm API) — **the entire prerequisite
    layer is absent from mathlib**.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard
form). More strongly: mathlib has **none of the prerequisites** — no Kubota–Leopoldt
p-adic L-function, no p-adic zeta on `ℤ_p^×`, no p-adic measure / Amice / Mahler
transform layer, no p-adic logarithm (`padicLog`) or exponential. `zetaNum_one` is not
findable because the theory it lives in is not in mathlib at all.

---

### Call sites — `PadicLFunctions.zetaNum_one`

Internal use count: **1** (within the project, not counting the declaring file's own
declaration line).
External-to-file callers: **0 distinct files** (the single use is in the *same* file,
`ResidueZeta.lean`).

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| ResidueZeta.lean:1819          | `rw [hbr1, zetaNum_one p hp2 hpm hm0]` — supplies `num 1`, the numerator value at `s = 1`, inside the residue/pole limit computation (`zetaPBranch` residue) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `zetaNum_one`?):
  - (none) — the total-mass identity is computed once, here, and consumed once at 1819.

What the pattern tells us: **K = 1 internal use, same file, no external consumers, no
inline re-derivation.** Per the Phase-6 signal table this leans toward
NO-composable / "possibly the wrong granularity to upstream" — but here it is better
read as: this is a genuine, non-trivial *step* of one paper-theorem's proof, extracted
as a named lemma for readability, with exactly one consumer (its sibling residue
theorem). It is real (not dead code, not a bypassed wrapper), but it is *internal to
this project's §7 development*, not a reusable public API.

---

### Composition check (Phase 6)

Can `zetaNum_one` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: any mathlib one-liner producing the total mass `∫ x⁻¹ dμ_a`.
  - Mathlib decls used: **none available** — mathlib has no `zetaNum`, no `PadicMeasure`,
    no `extLog`, no `padicLog`. There is nothing to compose *from* in mathlib.
  - Result: **fails immediately** — the statement is not even expressible in mathlib
    vocabulary.

Attempt 2: compose from the *project's* primitives (for completeness — note this is
about whether the lemma is a thin wrapper, not about mathlib).
  - The actual proof: (i) `haveI : NeZero (p : ℂ_[p])`; (ii)
    `obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p`; (iii)
    `refine (algebraMap ℚ_[p] ℂ_[p]).injective ?_` (descent by injectivity);
    (iv) rewrite by **three** project lemmas
    (`← constantCoeff_mahlerK_rhoA_eq_algebraMap`, `constantCoeff_mahlerK_rhoA`,
    `map_extLog_natCast`) plus a chain of `map_mul/map_neg/map_sub/map_one/map_inv₀/map_natCast`.
  - This is a genuine multi-step descent argument with three substantive helper-lemma
    invocations and a structural `map_*` rewrite chain — **not** a `.symm`/`.trans`/
    single-call composition.
  - Result: **NOT a composition** — it is a real proof.

Conclusion: **NOT-COMPOSABLE** — both because mathlib lacks every building block, and
because even within the project it is a multi-step derivation, not 1–3 chained calls.
The `NO-composable-from-mathlib` bucket is therefore *unavailable* (it would require
mathlib building blocks that do not exist).

---

## Verdict: `PadicLFunctions.zetaNum_one`

**Category:** `BORDERLINE-needs-human` (leaning strongly toward NO / not-yet)

**Evidence:**
- Literature search (Phase 3): the headline residue `1 − p⁻¹` is canonical and matches
  the project's RJW source; **but** the specific total-mass identity `∫ x⁻¹ dμ_a =
  −(1−p⁻¹)·log_p a` is **not** a standalone named literature result — it is
  construction-internal bookkeeping, varying by route and by log-branch normalisation.
- Generality analysis (Phase 4): STRICTLY NARROWER / NON-IDIOMATIC relative to any
  future mathlib form (it is stated over project-local `zetaNum`/`extLog`); the two
  real weakenings (rows 3–4) are **blocked** by missing mathlib infrastructure. Phase 4c:
  no modern-idiom restatement of *this lemma alone* is a real improvement today.
- Mathlib search (Phase 5): **not in mathlib, and none of its prerequisites are
  either** — no KL p-adic L-function, no p-adic zeta on `ℤ_p^×`, no p-adic measure /
  Amice / Mahler transform, no `padicLog`/`padicExp`. The whole theory is absent.
- Composition check (Phase 6): NOT-COMPOSABLE (no mathlib building blocks exist; the
  proof is a genuine descent argument).

**Rationale (1–2 paragraphs):**

`zetaNum_one` is mathematically meaningful and correctly proved (sorry-free), and it
sits underneath a result mathlib genuinely lacks and would eventually want: the
analytic theory of the Kubota–Leopoldt p-adic L-function, including the residue
`1 − p⁻¹` at `s = 1`. So at the *programme* level the answer is "yes, mathlib should
have this theory". But `zetaNum_one` is **not the theorem to upstream**. It is an
intermediate total-mass identity stated entirely in terms of this project's bespoke
construction layer — `PadicMeasure` (the continuous dual `C(ℤ_p^×, ℤ_p) →ₗ ℤ_p`),
`zetaNum`/`muA` (the §4 numerator measure via the Mahler transform `F_a`), and
`extLog` (the project's extended Iwasawa-branch logarithm, with `padicLog`/`padicExp`
also project-local). **None of these objects exists in mathlib** (Phase 5 grep: zero
hits for the entire stack). A mathlib version of this fact cannot be stated, let alone
proved, until that infrastructure is upstreamed first — and at that point its idiomatic
form would be different (stated against a mathlib p-adic measure and a mathlib
`padicLog`, with `a ∈ ℤ_p^×`).

This is not a clean `NO-mathlib-has-it` (mathlib has neither the lemma nor anything to
specialise from) and not `NO-composable-from-mathlib` (there are no mathlib building
blocks to compose, and the proof is a real descent argument). It is also not a
self-evident `YES`: the lemma has a single in-file consumer, no recognizable
standalone name in the literature, and its "right" form depends on an infrastructure
programme that hasn't happened. The honest verdict is **BORDERLINE** — the decision is
a strategic/sequencing judgment about whether (and in what order) the project intends
to upstream its p-adic-L-function tower to mathlib, which only the maintainer can make.

**WHY this is BORDERLINE (not a self-resolving NO or YES):**

The lemma's mathlib-worthiness is entirely contingent on a decision the skill cannot
make: *does the project intend to upstream the Kubota–Leopoldt construction stack to
mathlib, and if so, is this granular total-mass identity a public lemma in that effort
or an internal proof step of the residue theorem?* If the stack is never upstreamed,
the answer is a firm NO (project-internal forever). If it is upstreamed, this is plausibly
an internal lemma of `KubotaLeopoldt.residue_at_one`, not a headline declaration —
i.e. it ships, but renamed/restated and possibly inlined into the residue proof.

**Numbered questions (≤5):**

1. Does the project intend to upstream its p-adic-L-function tower (`PadicMeasure`,
   `zetaNum`/`muA`, `extLog`/`padicLog`/`padicExp`, the Mahler/Amice transform) to
   mathlib at all? (If **no** → verdict collapses to NO: keep `zetaNum_one`
   project-local.)
2. If yes: should the **residue theorem** (`ζ_{p,p−1}` has a simple pole at `s=1` with
   residue `1 − p⁻¹`) be the upstreamed headline, with `zetaNum_one` as an internal
   helper of its proof rather than a standalone public lemma? (Likely **yes** — the
   literature names the residue, not this total-mass step.)
3. If `zetaNum_one` is itself upstreamed, should it be **re-stated against a mathlib
   `padicLog`** (Iwasawa-branch p-adic logarithm) and a **mathlib p-adic measure** with
   `a ∈ ℤ_p^×` (rather than `a : ℕ`, `p ∤ a`)? (This is the EXPENSIVE Phase-4b restatement
   — but it presupposes those mathlib APIs exist first.)
4. Is the `extLog` (extended, `log_p p = 0`) normalisation the one mathlib should adopt
   as the canonical p-adic logarithm, or would mathlib prefer the standard `log_p`
   restricted to `1 + p·ℤ_p` plus a separate `extLog` extension? (Affects whether the
   `−(1 − p⁻¹)·log_p a` form is the canonical statement.)
5. Given there is exactly **one** in-file consumer (`ResidueZeta.lean:1819`), is keeping
   `zetaNum_one` as a *named, project-local* lemma (current state) the right
   granularity, or should it be inlined into the residue proof until/unless the stack is
   upstreamed?

**Next action:** the maintainer answers Q1 (the gating question). If **no** to Q1 →
record NO (project-local), no mathlib action. If **yes** → the correct follow-up is to
plan upstreaming the *infrastructure first* (a much larger effort: `padicLog`/`padicExp`,
the p-adic measure / Amice transform layer), with `zetaNum_one` re-assessed *after* those
land — at which point it is most likely an internal helper of an upstreamed
`KubotaLeopoldt.residue_at_one`, restated per Q3/Q4. Re-run `/mathlibable` on the
re-stated form at that time.

---

## Next step

The maintainer answers the gating question (Q1 above): **does the project intend to
upstream its p-adic-L-function construction stack to mathlib?** If no, keep
`zetaNum_one` project-local (verdict resolves to NO). If yes, sequence the
*infrastructure* (`padicLog`/`padicExp`, the p-adic measure / Mahler–Amice transform
layer) first, then re-run `/mathlibable` on the re-stated `zetaNum_one` — which will
most likely be an internal helper of an upstreamed `residue_at_one` theorem, not a
standalone public declaration.
