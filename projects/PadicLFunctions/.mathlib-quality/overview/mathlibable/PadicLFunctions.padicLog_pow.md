# `/mathlibable` report — `PadicLFunctions.padicLog_pow`

Mode A (single declaration), full 10-phase workflow with the exhaustive
literature + mathlib search.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task note — `lake build` is stale/slow here; declaration + all dependencies read directly from source)
- decl `PadicLFunctions.padicLog_pow`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:79`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  ExtLog.lean defines the extended (Iwasawa-branch) p-adic logarithm `extLog` on rational-valuation elements (RJW Thm 6.1(ii), decomposition W6a); this theorem is helper W6a-a2, "log of a power on the ball".

Dependencies read from source (so the elaborated meaning is fully known despite no fresh build):
- `PadicLFunctions.padicLog` — `PadicExp.lean:384`, the project's own `L`-valued p-adic log `∑' n, (-1)^n (n+1)⁻¹ • (x-1)^(n+1)`, junk-total (meaningful only on the ball).
- `PadicLFunctions.InExpBall` — `PadicExp.lean:65`, `‖x‖^(p-1) < p⁻¹` (rpow-free form of the open exp-convergence ball).
- `PadicLFunctions.padicLog_mul` — `PadicExp.lean:973`, multiplicativity of `padicLog` on `1 + 𝔪`.
- `PadicLFunctions.pow_mem_expBall` — `ExtLog.lean:67`, the ball is closed under powers.
- `PadicLFunctions.padicLog_one` — `PadicExp.lean:388` (`@[simp]`), `padicLog 1 = 0`.

---

### Statement (Phase 1)

`PadicLFunctions.padicLog_pow` is a theorem stating the following:

Let `L` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra,
and let `log_p` denote the (junk-total) `p`-adic logarithm given by the power
series `log_p(x) = Σ_{n≥0} (-1)^n (n+1)⁻¹ (x-1)^{n+1}`, which converges on the
open ball `B = { x : ‖x-1‖^{p-1} < p⁻¹ }`. If `y` lies in the translated ball
(`y - 1 ∈ B`, i.e. `‖y-1‖^{p-1} < p⁻¹`), then for every natural number `n`,
`log_p(y^n) = n · log_p(y)`. This is the "logarithm of a power" / additive-on-
exponents property of the `p`-adic logarithm, restricted to the ball where the
series is valid (so that the underlying multiplicativity holds).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [Fact p.Prime]` — the prime.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — the complete ultrametric normed `ℚ_p`-algebra in which the logarithm lives.
- `(y : L)` — the base element.
- `(n : ℕ)` — the exponent.

Hypotheses (Lean side):
- `(hy : InExpBall p (y - 1))` — `y` is in the translated convergence ball, i.e. `‖y-1‖^{p-1} < p⁻¹`. This is exactly the domain on which `padicLog` is multiplicative.

Conclusion (math): `log_p(y^n) = n · log_p(y)`.

Conclusion (Lean): `padicLog p (y ^ n) = n • padicLog p y` (`n • _` is the `ℕ`-scalar action on `L`).

Proof (read from source): induction on `n`. Base case `simp` (`padicLog_one`,
`pow_zero`, `zero_nsmul`). Step: `pow_succ` then
`padicLog_mul p (pow_mem_expBall p hy k) hy` (multiplicativity, using that
`y^k` and `y` are both in the ball), the IH, and `succ_nsmul`. So it is exactly
the iterate of `padicLog_mul`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A helper lemma (`W6a-a2` in the decomposition) — the iterate of
multiplicativity (`padicLog_mul`); not a new structure, not a named main result,
not named after a person.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for
framing only and does not gate Phase 3.)

### One-line check (Phase 2b)

Body line count: n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`.
One-liner verdict: n/a (the one-line check is a definition check).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm log(x^n) = n log(x) power property convergence ball"                                  | yes  | `log_p(x^n) = n·log_p(x)` follows from `log(xy)=log x+log y` | dms.umontreal.ca App. 16.6, arXiv:2304.02789; power property explicitly noted as a corollary of multiplicativity on `‖x‖_p<1` / `1+𝔪` |
|  2 | WebSearch (general form)         | "Iwasawa p-adic logarithm homomorphism property log_p(x^n) Washington cyclotomic fields"                | yes  | `log_p : ℚ_p^× → (ℚ_p,+)` is the **unique group homomorphism** with `log_p(p)=0` extending the series on `1+pℤ_p` | the standard form is the *homomorphism* — the power rule is automatic for any hom |
|  3 | WebSearch (named-after / aliases)| "p-adic logarithm definition Neukirch Robert Gouvea log_p group homomorphism units"                     | yes  | "a branch of the p-adic logarithm is a group homomorphism, determined by `log(p)`"; converges as `log_p(1+x)=x−x²/2+…` on `𝔪_K` | aliases: "Iwasawa logarithm", "log_p", branch logarithm; the additive-hom framing is universal |
|  4 | ChatGPT MCP                      | (intended) "standard form of p-adic log, generality, historical evolution"                              | n/a  | —                                                    | ChatGPT MCP server not configured in this environment; substituted by WebSearch #1–3 + #9–10 (≥3 distinct generality levels covered: specific power rule, general hom form, named/branch form) |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (no references dir)                                  | only `.mathlib-quality/overview/` exists; no source-paper PDFs present — recorded n/a |
|  6 | nLab                             | `https://ncatlab.org/nlab/show/p-adic+logarithm`                                                        | no   | —                                                    | HTTP 404 — nLab has no dedicated p-adic-logarithm page; the power rule there would be subsumed under "group homomorphism" anyway |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                                    | not a categorical concept — a concrete analytic function on a normed field; n/a |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                                    | not an algebraic-geometry / scheme-theoretic concept; n/a |
|  9 | MathOverflow / Math.StackExchange| "p-adic logarithm" generality / image on principal units                                                | yes  | `log_p` restricted to `1+𝔪_K^r` is an isomorphism onto `𝔪^r` for `r>e/(p-1)`; an additive hom throughout | confirms the hom/iso framing and the ball-of-validity; ResearchGate "image of p-adic logarithm on principal units" |
| 10 | recent arXiv (last 5 years)      | "arithmetic properties of the p-adic logarithm"                                                         | yes  | functional equation `log_p(xy)=log_p(x)+log_p(y)`; `log_p(x^n)=n log_p(x)` immediate | Dion (UQAM report), arXiv:2410.20934, arXiv:2304.02789 — all treat the power rule as a trivial consequence of additivity |

The protocol passes:
- WebSearch ran 3 distinct queries at different generality levels (#1 specific power rule, #2 general hom form, #3 named/branch aliases). ✓
- ChatGPT MCP unavailable in this environment; explicitly substituted by extra WebSearch + MathOverflow + arXiv channels covering the standard form, its generality, and (historically) the branch/hom evolution. Recorded as `n/a` with reason, not skipped silently.
- Local references checked (`n/a`, dir absent). ✓
- nLab checked (404 — no page). ✓
- nCatLab / Stacks recorded `n/a` with reason; MathOverflow + arXiv checked with hits. ✓

### Literature summary (Phase 3)

Concept identified as: the **power (homomorphism) property of the `p`-adic
logarithm** — `log_p(x^n) = n·log_p(x)` — a corollary of the multiplicative
functional equation `log_p(xy)=log_p(x)+log_p(y)`.
Sources agree on the standard form: **yes** — universally, and they agree the
*right object* is the additive **group homomorphism** `log_p` (Washington
*Intro. to Cyclotomic Fields* §5.1, cited in the file's own docstring; Neukirch;
Gouvêa; the arXiv/MathOverflow sources above). The power rule is never stated as
a standalone theorem; it is "automatic for a homomorphism".
Most general standard form: `log_p : (1+𝔪)^× → (K,+)` (equivalently extended to
`K^×` with `log_p(p)=0`) is a **group homomorphism**; the power rule is the
`map_pow`/`map_zpow` instance of that homomorphism. The exponent generalises
from `ℕ` to `ℤ` (and the codomain action to `zsmul`) for free once it is a hom.
Generality dimensions where the literature varies:
  - **the base object**: from "log of a power" (this Lean lemma) up to "`log_p`
    is a group homomorphism" (the literature standard) — the latter is strictly
    stronger and makes the power rule a one-liner.
  - **the exponent**: `ℕ` here; the literature/hom form gives `ℤ` immediately.
  - **the field**: stated over `ℚ_p`, `C_p`, or a general complete normed
    extension `K/ℚ_p` — the Lean form's `[NormedAlgebra ℚ_[p] L] … [CompleteSpace L]`
    matches the most general "complete extension" setting.
Disagreement with the literature: none on the *truth*; but the literature
packages this as a **homomorphism**, whereas the Lean form is a bespoke
hand-proved lemma about a **junk-total function** that is not a bundled hom.

---

### Generality analysis — `PadicLFunctions.padicLog_pow`

Literature-standard form (from Phase 3): `log_p` is a group homomorphism
`(1+𝔪)^× → (K,+)`; the power rule is `map_pow` (and `map_zpow` for `ℤ`).

| # | Parameter / hypothesis                        | Current Lean form                              | Literature-standard form                          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------|------------------------------------------------|---------------------------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` | complete ultrametric normed `ℚ_p`-algebra | complete extension `K/ℚ_p` (= `C_p` and finite extensions) | NO  | this is already the general "complete normed extension" setting the literature uses; not over-specialised to `ℚ_p` |
| 2 | `(hy : InExpBall p (y - 1))`                  | `y-1` in the open exp ball `‖y-1‖^{p-1}<p⁻¹` | `y ∈ 1+𝔪` (the domain where `log_p` is a hom) | NO (essential)      | multiplicativity (`padicLog_mul`) is only available on the ball; the proof iterates it, so the hypothesis cannot be dropped while `padicLog` stays junk-total |
| 3 | `(n : ℕ)`                                     | natural exponent, `n • _`                      | `ℤ` exponent, `zsmul` (hom gives `map_zpow`)      | **YES (strengthen)**| once `log_p` is a hom, the same statement holds for `n : ℤ`; the `ℕ` form is the special case |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (along axis #3: the
literature/hom form is the `ℤ`-exponent `map_zpow`, of which this is the `ℕ`
special case) — but, more importantly, the narrowing is *structural*: the
literature's object is a bundled homomorphism, not a hand-proved power lemma.
Number of weakening/strengthening opportunities found: 1 mechanical (ℕ→ℤ),
subsumed by the structural point below.
Proposed restatement: see Phase 4c — the right move is not "tweak this lemma"
but "bundle `padicLog` (on the ball) as an `AddMonoidHom`/`MonoidHom`", after
which this lemma is `map_pow`.
Cost of restatement: depends entirely on the bundling decision in 4c.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | hypotheses are already typeclasses; the only bundled hypothesis is `InExpBall` membership, which is genuinely a domain restriction, not a preamble |
|  2 | sequences/metric → filters/topological? | no | — | no limits/sequences in the statement; it is an algebraic identity |
|  3 | **construct → universal-property / bundled object?** | **yes** | Package the restriction of `padicLog` to the multiplicative group of the ball as a **`MonoidHom (expBall-units) (Multiplicative L?)`** — or, cleaner, an **`AddMonoidHom`** / monoid-to-additive hom `log_p : (1+𝔪, ×) →* (L, +)` (the literature's "group homomorphism"). Then `padicLog_pow` **is `map_pow`** and the `ℤ` version is **`map_zpow`** — no bespoke lemma. | the entire `map_pow`/`map_zpow`/`map_prod`/`map_one`/`map_mul` API applies for free; `extLog_mul`, `extLog_prod`, `extLog_eq_zero_of_pow_eq_one` (all in this file) become hom-lemma instances instead of hand proofs |
|  4 | set-with-closure-predicate → bundled substructure? | partial | `InExpBall` is currently a `Prop` predicate; the multiplicative units of `1+𝔪` could be a bundled `Submonoid`/`Subgroup` of `Lˣ`, which is the domain of the hom in #3 | composes with mathlib's `Submonoid`/`Subgroup` + `MonoidHom.restrict` API; lets the hom in #3 be stated cleanly |
|  5 | vector-space/field-specific → weaken typeclasses? | no | — | already at the general complete-normed-extension level (Phase 4a #1) |
|  6 | 1-categorical → higher-categorical? | no | — | not categorical |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | yes (minor) | exponent `ℕ → ℤ` via `map_zpow` once #3 is done | unifies with `zpow` API; but this is exactly subsumed by #3 |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**
  - Proposed mathlib-idiomatic restatement: bundle `padicLog` restricted to
    the ball as a monoid-to-additive homomorphism (literature's "the p-adic
    logarithm is a group homomorphism"), e.g.
    ```lean
    /-- The p-adic logarithm as a homomorphism from the units of the
        exponential ball to the additive group. -/
    noncomputable def padicLogHom : expBallUnits p L →* Multiplicative? L  -- (additive target)
    ```
    so that `padicLog_pow` becomes `map_pow padicLogHom y n` and the `ℤ`-form
    is `map_zpow`.
  - Cost: MODERATE-to-EXPENSIVE — requires first defining the bundled domain
    (the units `1+𝔪` as a `Subgroup`/`Submonoid`) and proving `map_mul`
    (= `padicLog_mul`, already done) + `map_one` (= `padicLog_one`, already
    done). The raw ingredients exist in the file; bundling them is real work.
  - Mathlib downstream this enables: the full `MonoidHom`/`AddMonoidHom` API —
    `map_pow`, `map_zpow`, `map_prod`, `map_one`, `map_mul`, `map_inv` — which
    in this very file would replace the hand proofs of `padicLog_pow`,
    `extLog_mul`, `extLog_prod`, and `extLog_eq_zero_of_pow_eq_one`.
  - Real mathematical improvement (not just "looks cooler"): yes — it removes a
    family of hand-proved hom-lemmas (the project currently even has a
    *duplicate* power lemma, `padicLog_pow_of_norm_lt_one` in `ValuesAtOne.lean`)
    by deriving them all from one bundled object, exactly the
    `Submodule`/`MonoidHom`-not-ad-hoc-predicate modernisation in the verdicts
    doc.

This means Phase 7 must NOT pick `YES-add-as-is` for the lemma as written: the
contemporary mathlib form is the bundled hom, of which this lemma is a free
`map_pow` instance.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or
typeclass-search paths introduced). Skipped per scope rule.

---

### Mathlib search-status: `PadicLFunctions.padicLog_pow`

[A] Lean-Finder        p-adic log of a power / padicLog map_pow              n/a: Lean-Finder MCP/endpoint not available in this environment
[B] Loogle             `Padic, _ ^ _` (via loogle.lean-lang.org/json)        no hits — no mathlib decl mentions a p-adic logarithm applied to a power
[C] LeanSearch         "p-adic logarithm of a power equals n times log"      n/a: leansearch.net API endpoint returned HTTP 404 in this environment (substituted by exhaustive grep [D] + mathlib4 docs web search)
[D] Grep mathlib src   `padicLog`, `padicExp`, `*[Ll]og` in `Mathlib/NumberTheory/Padics/`, `log_pow` library-wide   `padicLog`/`padicExp`: ZERO hits anywhere in mathlib. `log_pow` exists ONLY for `Real.log_pow` (`Analysis/SpecialFunctions/Log/Basic.lean:287`), `ENNReal.log_pow`, `Nat.log_pow`, and the continuous-functional-calculus `log_pow` — none p-adic. `NumberTheory/Padics/` has only `padicVal*`/`padicNorm` ("logarithm" there = `Nat.log` base-p of the valuation), NO transcendental functions.
[E] Name pattern       padicLog / padicExp / p-adic + Log                    no hits in mathlib (confirmed by [D] grep and by the mathlib4 docs web search, which finds PadicNorm/PadicVal/PadicNumbers/PadicIntegers but no padicLog/padicExp)

Searched for both:
  - the user's current form (`padicLog (y^n) = n • padicLog y`) — not in mathlib (no `padicLog` exists).
  - the literature-standard form (`log_p` as a group homomorphism, power rule = `map_pow`) — the *generic* `map_pow`/`AddMonoidHom.map_pow`/`MonoidHom.map_pow` exist (`Algebra/Group/Hom/Defs.lean:470,883`), but there is **no p-adic logarithm hom** to apply them to in mathlib.

Concluded: **not in mathlib** (all available methods exhausted — Loogle no-hit, exhaustive grep no-hit, mathlib4 docs web search no-hit — plus the literature-standard hom form: the generic hom lemmas exist but the p-adic-log object they would apply to does not). Mathlib has the *generic machinery* (`map_pow`) but neither the `padicLog` object nor this specialised lemma.

---

### Call sites — `PadicLFunctions.padicLog_pow`

Internal use count: **2** (within the same project, NOT counting the declaring line)
External-to-file callers: **0 distinct files** (both uses are inside ExtLog.lean; no other project file imports/uses *this* lemma — the `ValuesAtOne.lean` hits are a different, parallel lemma; see inline-derivation note)

| Caller file:line                                           | Usage pattern (one-line excerpt)                                              |
|------------------------------------------------------------|-------------------------------------------------------------------------------|
| projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:327   | `rw [padicLog_pow p hy, padicLog_pow p hy'] at hlog` (in `extLog_witness_smul_eq`, well-definedness) |
| projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:375   | `padicLog_pow p ha, padicLog_pow p hb]` (in `extLog_mul`, additivity)         |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `padicLog_pow`?):
  - **YES — a parallel copy exists.** `PadicLFunctions.padicLog_pow_of_norm_lt_one` (`ValuesAtOne.lean:577`) is the *same* "log of a power" statement, stated over the hypothesis `‖x-1‖ < 1` (its own namespace/file) instead of `InExpBall p (y-1)`, and proved by its own induction via `padicLog_mul_of_norm_lt_one` (`ValuesAtOne.lean:543`). So the project independently re-derives the power rule under a different hypothesis spelling — a duplication signal that points at the missing bundled-hom abstraction (Phase 4c #3), not at "ship this exact lemma".

Call-sites reading: K = 2 internal uses, both load-bearing for `extLog`'s
well-definedness and additivity → it is *real* internal API (leans away from
dead code / wrong-abstraction). But the existence of a second, independently
re-derived copy is exactly the "consumers re-derive it because the canonical
form is missing" pattern — and the canonical form is the hom of Phase 4c.

---

### Composition check (Phase 6)

Can `PadicLFunctions.padicLog_pow` be derived from **current mathlib** in ≤3 chained calls?

Attempt 1: `map_pow <padicLogHom> y n` (or `AddMonoidHom.map_pow …`).
  - Mathlib decls used: `map_pow` / `MonoidHom.map_pow` (`Mathlib/Algebra/Group/Hom/Defs.lean`).
  - Result: **fails against current mathlib** — there is no `padicLogHom` (no p-adic logarithm, bundled or otherwise) in mathlib for `map_pow` to apply to. The composition is only available *after* the Phase-4c bundling, which exists in neither mathlib nor the project.
  - Notes: this is the "composition in disguise of work that doesn't exist yet" case — the hom must be built first.

Attempt 2: derive from the project's own `padicLog_mul` directly.
  - Mathlib decls used: none — `padicLog_mul` is a project lemma about a project def.
  - Result: this is the *existing* proof (a genuine induction with a `have` per step), not a ≤3-call mathlib composition. Per the Phase-6 heuristics table ("`have h := …; have h' := …`; multiple haves with reasoning between" = NO; "anything requiring induction" = a real proof), this is NOT a composition.

Conclusion: **NOT-COMPOSABLE** from *current* mathlib (the only honest composition, `map_pow`, requires a hom that does not yet exist; the in-project derivation is a real induction, not a ≤3-call mathlib composition).

---

## Verdict: `PadicLFunctions.padicLog_pow`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): standard fact; the literature's *object* is a group homomorphism `log_p`, of which the power rule is the automatic `map_pow` consequence (Washington §5.1, Neukirch, Gouvêa, arXiv:2304.02789 / 2410.20934, MathOverflow). 9 channels run (ChatGPT MCP + Lean-Finder/LeanSearch unavailable, substituted/recorded n/a with reason).
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — the literature/hom form gives the `ℤ`-exponent (`map_zpow`) and this is the `ℕ` special case; and structurally the standard object is a bundled hom (Phase 4c #3), not a hand-proved lemma.
- Mathlib search (Phase 5): **not in mathlib** — mathlib has NO p-adic logarithm at all (`padicLog`/`padicExp` = zero hits; `log_pow` exists only for `Real`/`ENNReal`/`Nat`/CFC). The generic `map_pow` exists but has no p-adic-log object to act on.
- Composition check (Phase 6): NOT-COMPOSABLE from current mathlib (the `map_pow` composition needs a hom that does not yet exist; the in-project proof is a genuine induction).

**Rationale (1–2 paragraphs):**

This theorem is true, standard, and useful (2 load-bearing internal call sites
driving the well-definedness and additivity of `extLog`), and its hypotheses
sit at the right level of generality (a complete ultrametric normed `ℚ_p`-
algebra — i.e. `C_p` and finite extensions, not over-specialised to `ℚ_p`). But
it is **a lemma about `PadicLFunctions.padicLog`, a project-private function with
no mathlib counterpart whatsoever** — mathlib4 has no p-adic logarithm or
exponential (Phase 5 is conclusive: zero hits for `padicLog`/`padicExp`, and
`NumberTheory/Padics/` contains only valuations/norms). A lemma cannot be
upstreamed in isolation from its subject, so in its current form it is *not*
addable to mathlib as-is; the prerequisite is upstreaming the whole p-adic
exp/log convergence theory from `PadicExp.lean`.

The decision that actually controls this lemma's fate is a judgment call the
skill cannot make alone, which is why the verdict is BORDERLINE rather than a
self-resolving YES/NO. The literature is unanimous that the *right object* is
the **group homomorphism** `log_p : (1+𝔪)^× → (L,+)` (the file's own cited
source, Washington §5.1, says exactly this). If the p-adic log is upstreamed
*as a bundled `MonoidHom`/`AddMonoidHom`* — the Bourbaki-2.0 / `Submodule`-not-
ad-hoc-predicate modernisation in the verdicts doc — then `padicLog_pow`
**evaporates into `map_pow`** (and the `ℤ` form into `map_zpow`), and so do
`extLog_mul`, `extLog_prod`, and `extLog_eq_zero_of_pow_eq_one`; no bespoke
`padicLog_pow` lemma is warranted, and the project's existing *duplicate*
(`padicLog_pow_of_norm_lt_one` in `ValuesAtOne.lean`) is the smell that confirms
the missing abstraction. If instead the maintainers prefer to keep `padicLog`
junk-total (no bundled hom), then a hand-proved `padicLog_pow` *is* the right
artifact and should ship with the rest of the p-adic-log API. The skill cannot
choose between "bundle as a hom (lemma disappears)" and "keep junk-total (lemma
ships)" — that is a project/mathlib-policy and mathematical-taste call. Gate
note: NO-composable-from-mathlib is *not* available, because the only honest
composition (`map_pow`) requires a hom that exists in neither mathlib nor the
project today, so Phase 6's conclusion is NOT-COMPOSABLE; and YES-add-as-is is
barred by the Phase-4c "modern idiom available + real improvement" gate.

**Numbered questions (≤5):**

1. Do you intend to upstream the p-adic exponential/logarithm theory
   (`PadicExp.lean` + `ExtLog.lean`) to mathlib at all? (If no → this lemma
   stays project-local and `/mathlibable` is moot for it.)
2. If yes: should the p-adic logarithm be upstreamed **as a bundled
   homomorphism** `log_p : (1+𝔪)^× →* (L,+)` (literature-standard; makes
   `padicLog_pow = map_pow`, `extLog_mul`/`extLog_prod` free), or kept as the
   current **junk-total function** with hand-proved hom-lemmas?
3. If bundled-as-hom (Q2): do you agree `padicLog_pow` should be **dropped** in
   favour of `map_pow` (and the `ℤ`-exponent obtained from `map_zpow`), rather
   than added as a standalone lemma?
4. If kept junk-total (Q2): should the statement be **strengthened to a `ℤ`
   exponent** (`zpow` / `zsmul`) so mathlib gets the maximal form, or is the
   `ℕ` form sufficient for the intended downstream use?
5. The project already has a parallel copy (`padicLog_pow_of_norm_lt_one`,
   `ValuesAtOne.lean`, over `‖x-1‖<1`). Do you want these two
   reconciled/deduplicated (a cleanup-ticket on `main`) before any mathlib
   submission of the power rule?

**Next action:** user answers the questions; re-run
`/mathlibable PadicLFunctions.padicLog_pow` to resolve. Likely outcomes:
  - Upstream + bundle-as-hom → drop this lemma; it becomes `map_pow` of the new
    `padicLogHom`. (Verdict would resolve to NO-composable-from-mathlib *relative
    to the upstreamed hom*.)
  - Upstream + keep junk-total → YES, ship with the p-adic-log API, ideally
    strengthened to a `ℤ` exponent (then likely YES-but-generalise-first).
  - Not upstreaming → out of mathlib scope; keep project-local and dedup with
    `ValuesAtOne.lean`.

---

## Next step

User answers questions 1–5; re-run `/mathlibable PadicLFunctions.padicLog_pow`.
The pivotal decision is Q2 (bundle the p-adic log as a homomorphism vs keep it
junk-total): bundling makes this lemma a free `map_pow` instance (so it should
not be a standalone mathlib lemma), whereas keeping it junk-total makes a
hand-proved `padicLog_pow` the right artifact to ship — but either way the
whole `PadicExp`/`ExtLog` p-adic-log theory must be upstreamed first, since
mathlib currently has no p-adic logarithm.
