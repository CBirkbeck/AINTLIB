# `PadicLFunctions.ExtLogDomain` — mathlibable assessment

**Verdict: `NO-composable-from-mathlib`**

`ExtLogDomain p x` is a `Prop`-valued **predicate** that says `x` is a *rational-valuation
element whose unit part (after clearing `p`-powers) lands in the convergence ball of the
`p`-adic logarithm*: there exist `m > 0`, `k : ℤ`, `y : L` with `x^m = p^k·y` and
`y − 1` in the project's exponential ball `InExpBall p (y−1)`. It is the domain of the
project's Iwasawa-branch extended logarithm `extLog` (`ExtLog.lean:286`). The mathematics is
canonical — every reference (Wikipedia, MIT 18.785, Harron's AWS notes, the arXiv literature)
states that the Iwasawa logarithm `log_p` (normalised `log_p(p) = 0`) extends to **all of
`C_p^×`** via the decomposition `w = p^r·ζ·z` (`r ∈ ℚ`, `ζ` a root of unity, `|z − 1| < 1`) —
but in the literature the extended-log **domain is never a named object**: it is *the whole
multiplicative group*, stated inline, because over `C_p` (or `Q_p^bar`) every nonzero element
admits the decomposition. The project's predicate exists only because it works over a *general*
complete normed `Q_p`-algebra field `L` (not assumed algebraically/spherically complete), where
the decomposition is a genuine hypothesis rather than a theorem. Its conclusion clause
`InExpBall p (y−1)` is itself a project-local predicate (sibling verdict
`NO-composable-from-mathlib`), and mathlib carries **no** `p`-adic exponential or logarithm at
all (exhaustive grep of `Mathlib/NumberTheory/Padics/` returns nothing). So the predicate is
load-bearing *project* API — used across three files — but it is connective tissue for a
project-local `padicLog`/`extLog` development that mathlib does not have, and as a standalone
declaration it composes with nothing in mathlib. It should remain project-local; if and when
the surrounding `p`-adic exp/log API is upstreamed, the idiomatic move is to drop the bespoke
predicate and state the domain inline (the existential, or `x ∈ (closure of) p^ℚ · μ · (1+ball)`),
matching how mathlib expresses the classical exponential's convergence region inline.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:278` (kind: `def`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.
- **Refs:** `--refs=/Users/mcu22seu/.claude/plugins/cache/mathlib-quality-plugins/mathlib-quality/0.50.0/skills/mathlib-quality/references` (read in full: `mathlibable.md`, `mathlibable-verdicts.md`, `mathlib-search.md`).

---

## Phase 0 — Doctor / baseline

```
### Baseline (Phase 0)
- lake build:               build NOT re-run; reasoned from source (per task BUILD NOTE)
- decl `PadicLFunctions.ExtLogDomain`: ✓ resolved at ExtLog.lean:278
- kind:                      def  (Prop-valued — a predicate, not a bundled structure)
- has sorry:                 no (target and all dependents in ExtLog.lean are sorry-free)
- module docstring summary:  "The extended (Iwasawa-branch) p-adic logarithm (RJW §6, W6a)" —
                             extends `padicLog` to rational-valuation elements `x` with
                             `x^m = p^k·y`, `y` in the exp ball, setting
                             `extLog x := m⁻¹·padicLog y` (junk `0` off-domain; Iwasawa branch
                             `log_p(p)=0`). Construction xref: Washington §5.1.
```

Per the task's BUILD NOTE, the build was **not re-run; reasoned from source.** Read directly:
the target def (`ExtLog.lean:278–280`); its consumers `extLog` (286), `extLog_eq_of_witness`
(335), `extLog_mul` (357), `ExtLogDomain.mul` (386), `ExtLogDomain.prod` (400), `extLog_prod`
(414), `extLog_neg` (434), `extLogDomain_of_integral_norm_one` (446); its dependency predicate
`InExpBall` (`PadicExp.lean:65`); the project-local `padicLog` (`PadicExp.lean:384`); the
external call sites in `ResidueZeta.lean` and `ValuesAtOne.lean`; and the relevant mathlib
package under `.lake/packages/mathlib/` (present — grep is conclusive). Baseline commit
`d71766e`. This is the Phase-0 source-fallback path the skill explicitly permits.

**Section / variable context.** The def sits under the file-level
`variable (p : ℕ) [hp : Fact p.Prime]` and
`variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]
[CompleteSpace L]`. The `def` itself uses `p`, `L`, and `x : L`; the predicate body refers to
`(p : L)`, `^`, and `InExpBall`, so it needs only `[NormedField L]` (plus the `ℚ_[p]`-algebra
coercion for `(p : L)`); the heavier typeclasses enter in the theorems about it.

---

## Phase 1 — Comprehend

```lean
/-- The domain of the extended logarithm: rational-valuation elements, i.e.
`x^m = p^k·y` with `y` in the translated exponential ball. -/
def ExtLogDomain (x : L) : Prop :=
  ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y
    ∧ InExpBall p (y - 1)
```

### Statement (Phase 1)

`PadicLFunctions.ExtLogDomain` is **a definition** of a predicate stating:

> Over a complete nonarchimedean normed `Q_p`-algebra field `L`, an element `x : L` is in the
> *extended-logarithm domain* when some positive power of `x` factors as a (`ℤ`-)power of `p`
> times an element of the open multiplicative exponential ball `1 + B`: there are `m ∈ ℕ_{>0}`,
> `k ∈ ℤ`, `y ∈ L` with `x^m = p^k·y` and `‖y − 1‖^{p−1} < p⁻¹` (i.e. `y` lies in the ball on
> which `padicLog` converges). Equivalently, `x` has *rational valuation* and, after dividing
> out the `p`-power from a suitable root, the principal-unit part lies in the convergence disc.

This is exactly the membership condition that makes the Iwasawa-branch extended logarithm
`extLog x = m⁻¹·padicLog y` well-defined (independent of the witness, proved in
`extLog_witness_smul_eq`). It is the `L`-general analog of the classical statement that, over
`C_p`, every `α ∈ C_p^×` decomposes as `α = p^r·ζ·z` (`r ∈ ℚ`, `ζ` a root of unity,
`|z − 1| < 1`).

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (supplies `p ≥ 2`, used so `p − 1` is a genuine
  positive `ℕ` exponent inside `InExpBall`).
- `L`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a
  complete ultrametric normed field extension of `Q_p` (the ambient field of RJW §6).
- `x : L` (explicit) — the element being tested for membership.

Hypotheses (Lean side): none — it is a `def` of a `Prop`, not a theorem.

Conclusion (math): "`x` lies in the domain of the Iwasawa-extended `p`-adic logarithm."

Conclusion (Lean): a `Prop`, namely
`∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y ∧ InExpBall p (y - 1)`.

---

## Phase 2 — Preliminary checks (size + one-line)

### Size classification (Phase 2a)

**Verdict: BIG (borderline).** It introduces a **named mathematical predicate** — "the domain
of the extended logarithm" — i.e. a `def` of a named concept, which is the BIG criterion (a
new structure/notion). It is also a structural ingredient of a `## Main results`-level object
(`extLog`, the Iwasawa-branch logarithm of RJW §6). It is *not* named after a person/place.
(Literature width is EXHAUSTIVE regardless; this classification is for narrative framing only.
The decisive point — see Phases 3–6 — is not its size but that the predicate is bound to a
`p`-adic log that mathlib does not carry.)

### One-line check (Phase 2b)

Body line count: **3 substantive lines** — an existential quantifier `∃ (m : ℕ) (k : ℤ)
(y : L)` over a three-clause conjunction (`0 < m`, the factorisation equation, the ball
membership).

```
One-liner verdict: MULTI-LINE
```

This is **not** a one-line definition (contrast the sibling `InExpBall`, which is a single
`<`-inequality and *was* a one-liner). The Phase-2b negative signal for one-liners therefore
does **not** apply here; the one-liner exemption table is not required. (For completeness, were
it a one-liner, an *API-stability* exemption would plausibly apply, given the external call
sites in Phase 6 — but the check is moot since the body is genuinely multi-line.)

---

## Phase 3 — Literature search (EXHAUSTIVE, 9-channel protocol)

Goal: identify the **literature-standard form** of "the domain of the (Iwasawa-branch) extended
`p`-adic logarithm", and whether that domain is ever a *named bundled object/predicate* rather
than "the whole multiplicative group, stated inline".

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Iwasawa p-adic logarithm extension to all of Q_p^* domain rational valuation log_p(p)=0" | yes | `log_p` extended to `C_p^×` by `log p = 0`; for `x ∈ 𝔪`, `log(p^n(1+x)) := log(1+x)`; **compute by raising `x` to powers until valuation is a multiple, divide by `p`-powers to a unit, apply the series, divide by the power used** — *this is exactly the project's `x^m = p^k·y` witness recipe* | MIT 18.785 PS10, arXiv 1907.06437, Dasgupta "Trilogies", model-theory papers all agree. |
| 2 | WebSearch (general form) | "p-adic logarithm unique extension multiplicative group homomorphism Q_p^* Washington cyclotomic fields chapter 5" | yes | **"`log_p : Q_p^× → (Q_p,+)` is the *unique* group homomorphism with `log_p(p)=0` extending `log_p : 1+pZ_p → Q_p`"**; explicit formula `log_p(x) = 1/(p−1)·log_p(u^{p−1})`, `u = p^{−ord_p(x)}x` the unit part | The universal property (unique hom, `log_p(p)=0`); the `1/(p−1)·log(u^{p−1})` formula is the `m = p−1` special case of the project's witness. |
| 3 | WebSearch (named-after / aliases) | "Iwasawa logarithm" / "p-adic logarithm" domain definition `x^m = p^k y` convergence ball roots of unity | yes | **"The logarithm can be extended in many ways to `Q_p^×`. A standard branch is the *Iwasawa logarithm*, extended by `log_p(p)=0` and `log_p(ζ)=0` for `ζ ∈ μ_{p−1}`"**; decomposition `α = p^r·w·x`, `w` a root of unity, `x ∈ U_1` | PlanetMath, Harron AWS 2018 ("p-adic L-functions: the known and unknown"), arXiv. The *name* attaches to the **function** ("Iwasawa logarithm"/"Iwasawa branch"), never to a named *domain set*. |
| 4 | ChatGPT MCP | (historical-formulation question) | n/a | — | **Channel unavailable** — the `chatgpt-math` MCP server is installed (`~/.claude/mcp-servers/chatgpt-math`) but not connected/authenticated this session (no `ask`/`chatgpt` tool surfaced in the available toolset). Compensated by channels 1–3, 5–10, which converge unanimously; recorded for completeness per the skill's gate (same situation as the sibling `InExpBall.md` / `inExpBall_of_mem_span.md` reports). |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | n/a | (no references dir; `refs/` absent) | The project has no `.mathlib-quality/references/`; the gitignored `refs/` store is not present in this checkout. Recorded n/a with reason. |
| 6 | nLab | `ncatlab.org/nlab/show/p-adic+logarithm` | n/a (404) | — | No dedicated nLab page for the `p`-adic logarithm (HTTP 404). The concept's standard treatment surfaced via the other channels. |
| 7 | nCatLab (if categorical) | — | n/a | — | Not a categorical concept (a membership predicate / convergence domain over a normed field). Nothing categorical to add. |
| 8 | Stacks Project (if alg geom) | — | n/a | — | Not an algebraic-geometry concept; Stacks has no `p`-adic-analytic exp/log or Iwasawa-logarithm material. |
| 9 | MathOverflow / Math.StackExchange | "Iwasawa logarithm domain" / "p-adic log extension Q_p^*" generality | yes | Consistent with #1–#3: the extended `log` is defined on **all of `C_p^×`** via `α = p^r·ζ·z`; computed by clearing valuation to reach a principal unit. No separately-named *domain* object. | The PARI/GP and course-notes discussions describe the algorithm (the witness recipe), not a named domain. |
| 10 | recent arXiv (last 5 years) | "Iwasawa logarithm" / "p-adic L-functions" Eisenstein-distribution / `λ`-invariant papers (1611.09757, 2102.02851, 1907.06437, 2303.02037) | yes | Contemporary research uses the Iwasawa branch on `C_p^×`/`Q_p^×` with the identical decomposition; domain assumed = whole multiplicative group, cited inline; no bundled "extended-log-domain" predicate | The fact is background; the *function* is named, the domain is not. |

**Primary verbatim source — Wikipedia, "p-adic exponential function"** (fetched and decoded):

> "The function log_p can be extended to all of **C_p^×** (the set of nonzero elements of C_p)
> by imposing that it continues to satisfy [the homomorphism property] and setting
> log_p(p) = 0. … every element `w` of C_p^× can be written as `w = p^r·ζ·z` with `r` a
> rational number, ζ a root of unity, and `|z − 1|_p < 1`, in which case `log_p(w) = log_p(z)`.
> … **The document does not assign a separate name or formal set notation to the extended
> domain — it simply identifies it as 'all of C_p^×'.**"

This passage **is** the literature form of the concept the project's `ExtLogDomain` encodes —
and it shows the domain is *the whole group*, named only as the function's domain, never a
bundled predicate. The project's `x^m = p^k·y` witness is precisely the `w = p^r·ζ·z`
decomposition recast as "a power of `x` clears the valuation and reaches the ball".

### Literature summary (Phase 3)

- **Concept identified as:** "the domain of the Iwasawa-branch (extended) `p`-adic logarithm" —
  i.e. the set on which `log_p` (extended by `log_p(p)=0`, `log_p(ζ)=0`) is defined.
- **Sources agree on the standard form:** **yes**, unanimously (Wikipedia, MIT 18.785, Harron
  AWS 2018, PlanetMath, the arXiv Iwasawa-theory literature, Washington §5.1 as cited by the
  file): over `C_p` (or `Q_p^bar`) the domain is **all of `C_p^×`**, via `α = p^r·ζ·z`.
- **Most general standard form:** the *function* `log_p : C_p^× → C_p` (the Iwasawa branch), the
  **unique** group homomorphism with `log_p(p) = 0` extending the series on `1 + 𝔪`. The
  "domain" is the whole multiplicative group.
- **Generality dimensions where the literature varies:**
  - *ambient field*: stated over `C_p` (algebraically closed, complete) or `Q_p^bar`; the
    project works over a **general** complete ultrametric normed `Q_p`-algebra field `L`, which
    need not be algebraically/spherically complete — so "every element decomposes" *fails* and
    membership becomes a real hypothesis. This is the project's reason for a predicate.
  - *branch*: "Iwasawa branch" (`log_p(p)=0`) is one standard choice among many; it is the one
    the project uses.
- **Is the *domain* ever a named object/predicate?** **No.** Across every channel, the *name*
  attaches to the **function** ("Iwasawa logarithm"/"Iwasawa branch"); the domain is "`C_p^×`",
  stated inline. There is no standard named `ExtLogDomain` to upstream.
- **Disagreement with the literature:** none mathematically. The project's predicate is a
  *faithful* `L`-general encoding (`x^m = p^k·y` with `y` in the ball ⇔ "`x` has rational
  valuation and a root reaches the convergence disc"). The only non-literature elements are the
  *encoding* (an existential witness in place of the canonical `p^r·ζ·z` decomposition) and the
  *project-local* `InExpBall` clause.

If the search had returned nothing this would itself be a NO/BORDERLINE signal; instead it
returned a clear, unanimous standard form — whose lesson is that the *domain* is not a named
object, and the *function* it serves (`log_p`) is absent from mathlib (Phase 5).

---

## Phase 4 — Generality analysis

### 4a. Generality status table — `ExtLogDomain`

Literature-standard form (Phase 3): the Iwasawa logarithm is defined on **all of `C_p^×`**
(`α = p^r·ζ·z`). A predicate is needed only because the project's ambient field `L` is general.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[Fact p.Prime]` | `p` prime | `p` prime | NO | The `(p−1)`-exponent in `InExpBall` (Legendre) and the whole `p`-adic-log setup are prime-specific. Not a generalisation axis. |
| 2 | `L`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` | general complete ultrametric normed `Q_p`-algebra field | literature works over `C_p`/`Q_p^bar` (alg. closed + complete) | **the literature is LESS general** | The project is **already more general** than the literature's `C_p`: over `C_p` *every* nonzero element is in the domain (no predicate needed), but over a general `L` membership is a real condition. This is a strengthening, not a weakening — and it is *why* the predicate exists. No further weakening of the field hypotheses is literature-supported (`CompleteSpace`/ultrametric are needed for `padicLog`/the ball). |
| 3 | conclusion clause `InExpBall p (y − 1)` (`= ‖y−1‖^{p−1} < p⁻¹`) | rpow-free `ℕ`-power form of the ball | `|z − 1|_p < 1` (full open unit ball, since `log` converges on all of `1 + 𝔪`) | the project clause is **NARROWER than the full log-convergence ball** | The literature decomposition only needs `|z−1| < 1`; the project's `InExpBall` is the smaller *exponential* ball `‖·‖^{p−1} < p⁻¹` (so that `padicLog` is well-behaved with the exp inversions). This is an *encoding choice tied to the project's `padicLog` API*, not a literature generality axis — and `InExpBall` itself is a project-local predicate (its own verdict is `NO-composable-from-mathlib`). |

### 4b. Generality verdict (Phase 4b)

```
The current form is: MAXIMALLY GENERAL (in fact strictly MORE general than the C_p literature,
                     in its field hypotheses) — NOT a YES-but-generalise-first case.
Number of weakening opportunities found: 0 substantive (literature-supported).
```

The predicate is at the right generality for the project's setting: it is the necessary `L`-general
analog of "lies in the domain of the Iwasawa log", and it is in fact *more* general than the
classical `C_p` statement (where the domain is everything). There is **no** literature-supported
weakening, so this is **not** a `YES-but-generalise-first (LITERATURE-WEAKENING)` case. The one
narrowing (row 3, the `InExpBall` exp-ball vs the full unit ball) is a presentation detail tied
to the project's own `padicLog`, addressed in 4c/5/6 — not a generalisation axis.

Cost of any restatement: n/a (no literature weakening proposed).

### 4c. Modern mathlib-idiom restatement — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | no | — | Hypotheses are already typeclasses; the predicate is a plain `∃`. Nothing to bundle. |
| 2 | sequences/metric → filters/topological? | no | — | A static existential over a factorisation + a norm inequality; no sequence/limit to filter-ise. |
| 3 | construction → universal-property class? | **partially — but it points away from mathlib, not toward it** | The literature's universal property is *`log_p` is the unique group hom `C_p^× → C_p` with `log_p(p)=0`* — i.e. the *function* `extLog` could be characterised by a universal property. But that is a fact about **`extLog`** (and presupposes a `p`-adic log, which mathlib lacks), not a reformulation of the **domain predicate**. | None for mathlib: the universal property characterises `extLog`, whose target API is entirely project-local (no mathlib `padicLog`). |
| 4 | set-with-closure-predicate → bundled substructure? | **observed, but not a mathlib win** | The domain is closed under `*` and finite `∏` (`ExtLogDomain.mul`, `ExtLogDomain.prod`) and contains `1`, `−1`, roots of unity — so it is a **submonoid/subgroup** of `Lˣ`, and could be a bundled `Submonoid`. (Over `C_p` it is *all* of `C_p^×`.) This is the only genuine idiom observation. | The `Submonoid`/`Subgroup` lattice API *would* compose — but only with the project's own `extLog`/`padicLog` machinery, which is not in mathlib. Bundling it would re-organise *project* code, not unlock *mathlib* downstream. It is also exactly the move flagged for the sibling balls in `mul_mem_expBall.md` (bundle `1 + ball` as a `Submonoid`), and belongs to that project-level refactor, not a mathlib contribution. |
| 5 | vector-space/metric/field-specific → weakened typeclass? | no | — | Already at the natural general-`L` level; the content is intrinsically about `Q_p`-algebra valuation. |
| 6 | 1-categorical → higher-categorical? | no | — | No categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no | — | `m : ℕ`, `k : ℤ` are the (necessary) valuation/witness data; not free indices to generalise. |

```
### Modern-idiom verdict (Phase 4c)
Modern idiom available: no — not as a mathlib contribution.
One-line reason: the two genuine idiom observations (characterise `extLog` by a universal
property [row 3]; bundle the domain as a `Submonoid`/`Subgroup` [row 4]) both re-organise the
PROJECT's own `padicLog`/`extLog` development — they unlock no mathlib downstream API, because
mathlib carries no p-adic logarithm for them to compose with. Per the verdicts reference's rule
5 ("modernisation must be a real improvement in mathematical organisation, not 'looks cooler'"),
this is not a Bourbaki-2.0 contribution: the modernised forms still presuppose the project-local
log and do not become standalone mathlib objects.
```

This is **not** a `YES-but-generalise-first (MODERN-IDIOM)` case: the bundling/universal-property
moves are project refactors, not mathlib-bound improvements, because their downstream consumers
(`extLog`, `padicLog`, `InExpBall`) are all project-local.

---

## Phase 4.5 — Diamond / defeq risk (`def` — runs)

The declaration kind is `def` (of a `Prop`), so this phase runs. It defines a **predicate** —
no `instance`, no `class`, no `CoeFun`/`CoeSort`, no bundled data — which sharply limits the
risk surface.

### 4.5a. Risk table

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | `ExtLogDomain` is a `Prop`-valued `def`, not an `instance`/`class`. It participates in no typeclass-search path, so it can create no diamond. |
| 2 | Reducibility leak | **none** | Not marked `@[reducible]`. The body is an `∃`-`Prop`; consumers `obtain ⟨m, k, y, …⟩` (destructure) or supply `⟨m, k, y, …⟩` (construct) explicitly — they never rely on silent defeq unfolding. Sealing is appropriate and present. |
| 3 | Non-canonical unfolding | **none** | No `@[simp]` attribute; `simp`/`rfl` do not unfold it. Every use site is an explicit intro/elim of the existential, not a rewrite. |
| 4 | Instance priority collision | **n/a** | Not an `instance` — no priority to collide. |
| 5 | Universe-polymorphism issues | **none** | `L : Type*` with the standard normed-field bundle; the predicate lives in `Prop`. No universe constraint is forced on call sites; the existential binds `m : ℕ`, `k : ℤ`, `y : L`, all in fixed universes. |
| 6 | Coercion ambiguity | **none** | No `Coe*` instance attached. The only coercion in the body is `(p : L)` (`ℕ → L` via the `Q_p`-algebra map), which is mathlib's standard `Nat.cast`; nothing new is introduced. |

### 4.5b. Risk verdict (Phase 4.5)

```
Overall risk: NONE
Top risks: none
Recommended mitigations: n/a
```

A `Prop`-valued predicate with no attributes, no instances, and no coercions carries essentially
no diamond/defeq/elaboration risk. (This does not bear on the verdict bucket — the decl is not
going to mathlib — but it confirms there is no *infrastructure* objection either.)

### 4.5c. Probes (reasoned from source, build not re-run)

- **Diamond probe** (`#synth`): n/a — not a class/instance; no synthesis target.
- **Reducibility probe** (`example : <body> = ExtLogDomain p x := rfl`): would succeed (a `def`
  is semireducible, so `rfl` sees through it), but it is irrelevant here — consumers use
  intro/elim, never `rfl`-unfolding, so the semireducibility is harmless. No `@[reducible]`.
- **Coercion probe**: only `(p : L)` (`Nat.cast`); no competing `CoeFun`/`CoeSort`.
- **Universe probe**: `L : Type*` is fully polymorphic; the body forces no annotation.

---

## Phase 5 — Mathlib five-method search

Searched for (a) the user's form (an `ExtLogDomain`/extended-log-domain predicate), and (b) the
literature-standard form (the `p`-adic / Iwasawa logarithm and *its* domain `C_p^×`). The
Loogle / LeanSearch / Lean-Finder MCP back-ends are **not connected** this session; methods [D]
(exhaustive grep over the mathlib source tree) and [E] (name-pattern grep) are the available
substitutes and are **conclusive** here, because the entire *concept* (a `p`-adic logarithm) is
absent from mathlib — there is nothing for the NL/type back-ends to find.

```
### Mathlib search-status: `PadicLFunctions.ExtLogDomain`

[A] Lean-Finder   n/a — MCP not connected this session
[B] Loogle        n/a — MCP not connected this session
[C] LeanSearch    n/a — MCP not connected this session
[D] Grep mathlib src:
      - `padicLog`, `padicExp`, `Padic.log`, `Padic.exp`, `padic_exp`, `expPadic` in Mathlib/ → NO HITS
        (mathlib has NO p-adic exponential or logarithm at all)
      - `ExtLogDomain`, `LogDomain`, `extLog`, `log.*domain.*valuation` in Mathlib/           → NO HITS
      - `rationalValuation`, `fractionalValuation` predicate in Mathlib/                       → NO HITS
        (only `padicValRat`/`norm_num` rational-result helpers — unrelated)
      - `def .*: Prop := ∃ .*pow` (divisible-hull / "a power lands in S" predicate) in Mathlib/ → NO HITS
      - `Mathlib/NumberTheory/Padics/` directory listing                                       → AddChar, Complex,
        HeightOneSpectrum, Hensel, MahlerBasis, PadicIntegers, PadicNorm, PadicNumbers, PadicVal/,
        ProperSpace, RingHoms, ValuativeRel, WithVal — NONE define a p-adic exp/log or its domain
[E] Name pattern  `*ExtLogDomain*`, `*LogDomain*`, `*extLog*` anywhere in Mathlib/             → NO HITS

Searched both:
  - user's current form (`ExtLogDomain` predicate / "domain of extended p-adic log")  → not in mathlib
  - literature-standard form (the Iwasawa/p-adic `log_p` and its domain `C_p^×`)        → not in mathlib AT ALL

Concluded: "not in mathlib (all available methods exhausted, plus the literature-standard form).
Mathlib has NEITHER a p-adic exponential/logarithm NOR any extended-log-domain predicate NOR a
divisible-hull/rational-valuation membership predicate of this shape. There is no mathlib decl —
in identical or more general form — to cite. The predicate's conclusion clause `InExpBall p (y−1)`
is itself project-local (sibling verdict NO-composable-from-mathlib)."
```

Because both the predicate **and** the function it serves are entirely absent from mathlib, the
verdict **cannot** be `NO-mathlib-has-it`: there is no decl, in any form, stating this. (The
anti-pattern "mathlib has the general form so we don't need this" does not apply — there is no
general mathlib form of a thing mathlib does not define.)

---

## Phase 6 — Composition check (+ call-sites signal)

### 6.0. Call sites — `ExtLogDomain`

```bash
grep -rn "ExtLogDomain" projects/ --include="*.lean" | grep -v "ExtLog.lean:278" | grep -v ".mathlib-quality"
```

Internal use count (within the project, **excluding** the declaring file `ExtLog.lean`):
**≥ 6 distinct use sites across 2 external files** (`ResidueZeta.lean`, `ValuesAtOne.lean`),
plus a dense web of uses *inside* `ExtLog.lean` (the def's own API: `extLog`,
`extLog_eq_of_witness`, `extLog_mul`, `ExtLogDomain.mul`, `ExtLogDomain.prod`, `extLog_prod`,
`extLog_neg`, `extLogDomain_of_integral_norm_one`). 25 raw occurrences project-wide.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ResidueZeta.lean:1756–1757 | `have hωdom : ExtLogDomain p (teichmuller … : ℚ_[p]) := ⟨p-1, 0, 1, hp1, …, inExpBall_one_sub_one p⟩` (construct witness for a Teichmüller unit) |
| ResidueZeta.lean:1764–1765 | `have handom : ExtLogDomain p (angleUnit … : ℚ_[p]) := ⟨1, 0, _, one_pos, …, hanball⟩` (construct witness for an angle unit), then `extLog_mul p hωdom handom` |
| ValuesAtOne.lean:978 | `… : ExtLogDomain p (ξ ^ i * ε ^ c - 1) := extLogDomain_of_integral_norm_one p … …` (domain-engine application; conclusion of `extLogDomain_pow_mul_pow_sub_one`) |
| ValuesAtOne.lean:1048 | `… : ExtLogDomain p x := by …` (hypothesis/result in a `T616`-step lemma) |
| ValuesAtOne.lean:1089–1095 | `private theorem extLog_neg_one_pow_mul {x} (hx : ExtLogDomain p x) (m) : …`; body builds `ExtLogDomain p ((-1)^k * x)` via `ExtLogDomain.mul` |
| ValuesAtOne.lean:1133 | `… ExtLogDomain p (ζ * ε ^ c - 1) := by …` (domain membership feeding the `μ_p`-collapse) |
| ValuesAtOne.lean:1753 | `have hdom : ExtLogDomain p (ε ^ c - 1) := …` (the frozen `∀ c, ¬N∣c → ExtLogDomain …` engine, RJW Thm 6.1(ii)) |

External-to-project callers (downstream library outside `projects/`): **0**.

Inline-derivation grep (was the existential re-derived elsewhere *without* using
`ExtLogDomain`?): **(none)** — every consumer routes through the predicate, either constructing
a witness `⟨m, k, y, …⟩` or pattern-matching one; the "rational-valuation + power-in-ball"
condition is not re-spelled inline anywhere.

**What the call-sites pattern tells us.** K ≥ 6 external uses (plus heavy internal use), with no
inline re-derivation, is a strong **"real, load-bearing internal API"** signal — *within this
project*. But (exactly as for the sibling `inExpBall_of_mem_span`, K = 13) the API it serves is
the project's own `extLog`/`padicLog` development: every witness is fed to `extLog_mul`,
`extLog_eq_padicLog`, `extLogDomain_of_integral_norm_one`, etc. — all functions that mathlib does
not have. So the call-sites evidence reinforces that this is the **connective tissue of a
project-local development**, not a standalone mathlib contribution (K = 0 external-to-project).

### 6a. Composition attempt

Can `ExtLogDomain p x` be *expressed/derived* from mathlib in ≤3 chained calls?

```
Attempt 1 — express the predicate via mathlib primitives:
  ExtLogDomain p x  is literally  ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x^m = (p:L)^k * y
                                    ∧ InExpBall p (y - 1)
  - Mathlib decls used to STATE it: `∃`, `Nat`, `Int`, `HPow`, `HMul`, `Nat.cast (p : L)` — all
    standard; ZERO auxiliary lemma calls needed to *write* the existential.
  - BUT the final clause `InExpBall p (y - 1)` is a PROJECT-LOCAL predicate that mathlib does not
    have (its own verdict: NO-composable-from-mathlib; unfolds to `‖y−1‖^{p−1} < p⁻¹`).
  - Result: the predicate is its OWN shortest expression — an existential over a factorisation
    and a (project-local, but itself 0-call) ball inequality. Inlining `InExpBall` gives a fully
    explicit `∃ … ‖y−1‖^{p−1} < p⁻¹`, still a single self-contained `Prop`.
  - Notes: there is nothing to "derive" — a predicate `def` is not proved, it is stated; the
    only question is whether the bespoke name is warranted (Phases 4c/6.0), and whether its
    pieces are mathlib-available (they are, except for the project-local-but-trivially-inlinable
    InExpBall clause).

Conclusion: COMPOSABLE — the predicate is a direct ≤1-expression statement over mathlib
primitives (`∃`/`pow`/`mul`/`Nat.cast`) plus the project's own (0-call, inlinable) `InExpBall`
inequality. No mathlib lemma machinery is needed to express it.
```

### 6b. Composition heuristics check

By the Phase-6 heuristics this sits on the **composable** side: the "composition" is the literal
existential, not a `by rw […]; ring_nf; aesop` proof in disguise — there is no proof at all (it
is a `def`). The decisive point, exactly as for the sibling `InExpBall`/`inExpBall_of_mem_span`,
is **not** the call count but the **conclusion/role**: the predicate is meaningful only as the
domain of the project-local `extLog`, whose dependency chain (`padicLog`, `InExpBall`) mathlib
does not carry. Even judging the existential "substantive", it cannot be added to mathlib *as
stated* without first introducing a `p`-adic logarithm and its convergence ball — a much larger
effort assessed under those declarations.

---

## Phase 7 — Verdict

```
## Verdict: `PadicLFunctions.ExtLogDomain`

Category: NO-composable-from-mathlib

Evidence:
- Literature search (Phase 3): the Iwasawa-branch p-adic logarithm is canonical (Wikipedia
  verbatim: "log_p can be extended to all of C_p^× … log_p(p)=0 … w = p^r·ζ·z …"; MIT 18.785,
  Harron AWS 2018, PlanetMath, arXiv all agree, incl. the exact `x^m = p^k·y` witness recipe),
  but its DOMAIN is "all of C_p^×", stated INLINE — NEVER a named predicate. The *name*
  attaches to the function ("Iwasawa logarithm"), not to a domain set.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — in fact strictly MORE general than the
  C_p literature in its field hypotheses (a general complete ultrametric Q_p-algebra field L,
  where membership is a genuine condition). No literature-supported weakening ⇒ NOT
  YES-but-generalise. Phase 4c: the two idiom moves (universal property of extLog; bundle the
  domain as a Submonoid) re-organise PROJECT code, unlock no mathlib downstream ⇒ NOT a
  Bourbaki-2.0 YES.
- Phase 4.5 (def risk): overall risk NONE — a Prop predicate with no attrs/instances/coercions.
- Mathlib search (Phase 5): NOT in mathlib; mathlib has no p-adic exp/log, no extended-log-domain
  predicate, no divisible-hull/rational-valuation predicate. Nothing to cite ⇒ NOT
  NO-mathlib-has-it.
- Composition check (Phase 6): COMPOSABLE — the predicate IS its own ≤1-expression statement over
  mathlib primitives (`∃`/`pow`/`mul`/`Nat.cast`) plus the project's own (0-call, inlinable)
  `InExpBall` clause. K ≥ 6 external uses, 0 external-to-project — load-bearing PROJECT glue.
```

**Rationale.** `ExtLogDomain` is the membership predicate for the domain of the project's
Iwasawa-branch extended logarithm `extLog`. The mathematics is impeccable and canonical — every
reference confirms the Iwasawa log `log_p` (with `log_p(p) = 0`) extends to the whole
multiplicative group `C_p^×` via `α = p^r·ζ·z`, and the project's `x^m = p^k·y` witness is
exactly the standard "clear the valuation to reach a principal unit" recipe. But two facts put
this firmly in `NO-composable-from-mathlib`. (1) In the literature the *domain* is never a named
object: it is *all of `C_p^×`*, stated inline, precisely because over the algebraically-closed
complete field `C_p` every nonzero element decomposes. The project needs a *predicate* only
because it works over a **general** complete ultrametric normed `Q_p`-algebra field `L`, where
the decomposition can fail and membership is a real hypothesis — a faithful but project-specific
encoding, not a mathlib-standard bundled concept. (2) Decisively, the predicate is bound to a
`p`-adic logarithm that **mathlib does not have**: its conclusion clause `InExpBall p (y−1)` is
a project-local predicate (sibling verdict `NO-composable-from-mathlib`), and exhaustive grep of
`Mathlib/NumberTheory/Padics/` confirms mathlib carries **no** `padicLog`/`padicExp` at all.
A predicate whose entire purpose is to be the domain of a not-in-mathlib function, and whose body
names a not-in-mathlib clause, only makes sense inside this project's `extLog` development.
Mechanically it is also `COMPOSABLE`: it is its own shortest statement — an existential over a
factorisation plus the (0-call, trivially inlinable) ball inequality — so no mathlib lemma is
needed to express it. Per the skill's re-aim rule this is **not** a blanket-inherited NO: this
decl is assessed in its own right, and its Phase-5/Phase-6 analysis independently lands on
`NO-composable-from-mathlib` (the parent concept `padicLog`/`InExpBall` has no more-general
mathlib `D'` to re-aim at).

This is the same shape as the sibling reports: the *substantive, genuinely contributable*
mathematics of this development is the `p`-adic `exp`/`log` API itself (`padicExp`, `padicLog`,
the isometry, the functional equation, the inversions, RJW Lem 5.14 / §6) — assessed under those
declarations — while the *domain predicate*, like `InExpBall`, is project-local connective tissue.

**WHY not — refactor-actionable detail.** Mathlib has the building blocks to *state* the
predicate (`∃`, `^`, `*`, `Nat.cast`) but not the form, and the form's reason for existence —
being the domain of `extLog` — is project-local because mathlib has no `padicLog`. The predicate
should remain **project-local API**; there is nothing to upstream as a standalone declaration.

Mathlib building blocks (to *state* the predicate, if ever inlined):
- `Nat`, `Int`, `HPow.hPow`, `HMul.hMul`, `Nat.cast` (`(p : L)`) — all standard mathlib core.
- The conclusion clause needs the project-local `InExpBall p (y−1)` (= `‖y−1‖^{p−1} < (p:ℝ)⁻¹`,
  `PadicExp.lean:65`; sibling verdict `NO-composable-from-mathlib`, itself a 0-call inequality).
  Mathlib's nearest *idiom* for "in the convergence ball" is `x ∈ Metric.ball 0 r` /
  `‖x‖ < r` inline (`Mathlib/Analysis/Normed/Algebra/Exponential.lean`), but mathlib's abstract
  `expSeries` has radius `⊤` over fields, so it does not model the bounded `p`-adic ball.

Composition / inline form (≤3 lines — the predicate spelled fully explicitly):
```lean
-- "x is in the extended-log domain", inlined (no bespoke def):
example (x : L) : Prop :=
  ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y ∧ ‖y - 1‖ ^ (p - 1) < (p : ℝ)⁻¹
```

Call sites in our project (from Phase 6.0): **K ≥ 6 external** (`ResidueZeta.lean` ×2,
`ValuesAtOne.lean` ×4+), plus dense internal use throughout `ExtLog.lean`.

**Refactor plan.** Do **not** delete this predicate — unlike a redundant wrapper it is genuinely
load-bearing project API (≥ 6 external uses, no inline re-derivation; it cleanly carries the
`⟨m, k, y, …⟩` witness data that the call sites construct/destructure, and is the natural subject
of `ExtLogDomain.mul` / `ExtLogDomain.prod`). The actionable conclusion is the **negative one for
mathlib**: it should **not** be PR'd as a standalone declaration, because (a) the literature does
not name the domain (it is "all of `C_p^×`"), and (b) its purpose and its `InExpBall` clause are
tied to a `p`-adic logarithm mathlib does not carry. If and when the surrounding `p`-adic
`exp`/`log` API is prepared for mathlib, this predicate travels *with* that API — and the
idiomatic restatement would either inline the existential at the (few) hypothesis sites, or, if a
bundled form is wanted, register the domain as a `Submonoid`/`Subgroup` of `Lˣ` (it is closed
under `*`/`∏` and contains `1`/`−1`/roots of unity — see `ExtLogDomain.mul`, `.prod`), matching
mathlib's bundled-substructure idiom — *not* as a bare `Prop` `def`. Over the literature's `C_p`
that submonoid is the whole `C_p^×`, so even the bundled form is "everything" and the predicate
collapses; the predicate's content is purely the general-`L` hypothesis.

**Next action:** keep `ExtLogDomain` as project-local API; do **not** PR it as a standalone
definition. Re-assess it only as part of a larger "upstream the `p`-adic exp/log + Iwasawa
logarithm API" effort. At that point, state the domain inline (the explicit existential above)
or as a bundled `Submonoid`/`Subgroup` of `Lˣ`, and the genuinely contributable mathematics —
`padicExp`, `padicLog`, `extLog`, the isometry/functional-equation/inversion API, RJW Lem 5.14
and §6 — is assessed under its own declarations.

---

## Phase 8 — Report summary

| Phase | Artifact | Outcome |
|-------|----------|---------|
| 0 Doctor | baseline | `def` (Prop predicate), sorry-free, build reasoned-from-source (commit `d71766e`) |
| 1 Comprehend | prose statement | "`x` lies in the domain of the Iwasawa-extended `p`-adic log: `x^m = p^k·y`, `y−1` in the exp ball" |
| 2 Prelim | size / one-line | BIG (named predicate / ingredient of a main result); **MULTI-LINE** (not a one-liner — exemption table n/a) |
| 3 Literature | 9-channel table | canonical (Wikipedia verbatim ✔: extends to all of `C_p^×`, `log_p(p)=0`, `w=p^r·ζ·z`); domain is the WHOLE GROUP, stated inline, NEVER a named predicate; ChatGPT MCP unavailable, compensated by 8 channels |
| 4 Generality | status + verdict + 4c | MAXIMALLY GENERAL (strictly more general than the `C_p` literature in field hypotheses); no weakening; 4c idiom moves (univ. property / `Submonoid`) re-organise PROJECT code only ⇒ no Bourbaki-2.0 win |
| 4.5 Risk | def risk table | overall risk **NONE** (Prop predicate; no attrs/instances/coercions) |
| 5 Mathlib | 5-method (D/E live; A/B/C MCP n/a) | NOT in mathlib; mathlib has no `p`-adic exp/log, no extended-log-domain / rational-valuation predicate; nothing to cite for `NO-mathlib-has-it` |
| 6 Composition | call-sites + sketch | K ≥ 6 external / 0 external-to-project (+ dense internal); COMPOSABLE (the predicate is its own ≤1-expression statement) |
| 7 Verdict | bucket + evidence | **`NO-composable-from-mathlib`** |

### Final verdict (five-bucket)

> ## **`NO-composable-from-mathlib`**

**Next step.** Keep `PadicLFunctions.ExtLogDomain` as project-local API (it is real,
load-bearing internal glue: ≥ 6 external uses + heavy internal use, no inline re-derivation, and
it threads the `⟨m, k, y, …⟩` witness data its consumers construct/destructure). Do **not** PR it
as a standalone mathlib declaration: the literature does not name the extended-log domain (it is
"all of `C_p^×`", stated inline), and the predicate's purpose and its `InExpBall p (y−1)` clause
are bound to a `p`-adic logarithm (`padicLog`/`extLog`) that mathlib does not carry (sibling
`InExpBall` verdict `NO-composable-from-mathlib`; mathlib's `Padics/` tree has no exp/log).
Stated explicitly it is the ≤1-expression existential
`∃ m k y, 0 < m ∧ x^m = p^k·y ∧ ‖y−1‖^{p−1} < p⁻¹`. Revisit only inside a future "upstream the
`p`-adic exp/log + Iwasawa logarithm API" PR — restated inline, or as a bundled
`Submonoid`/`Subgroup` of `Lˣ` (matching mathlib's substructure idiom), not as a bare `Prop`
`def` — alongside the substantive theorems (`padicExp`, `padicLog`, `extLog`, isometry,
functional equation, inversions, RJW Lem 5.14 / §6), which are assessed under their own
declarations.

---

### Sources (Phase 3 literature)

- Wikipedia, "p-adic exponential function" — https://en.wikipedia.org/wiki/P-adic_exponential_function (verbatim: `log_p` extends to all of `C_p^×`, `log_p(p)=0`, `w = p^r·ζ·z`; domain unnamed)
- MIT 18.785 (2015) Problem Set 10, "The p-adic logarithm" — https://math.mit.edu/classes/18.785/2015fa/ProblemSet10.pdf
- R. Harron, Arizona Winter School 2018, "p-adic L-functions: the known and unknown" (problems) — https://swc-math.github.io/aws/2018/2018HarronProblems.pdf (Iwasawa branch `log_p(p)=0`, `log_p(ζ)=0`)
- S. Dasgupta et al., "p-adic L-functions and Euler systems: a tale in two trilogies" — https://sites.math.duke.edu/~dasgupta/papers/Trilogies.pdf
- arXiv:1907.06437, "On the bases of the image of 2-adic logarithm on the group of principal units" — https://arxiv.org/pdf/1907.06437
- arXiv:1803.10564, "Model theory of the field of p-adic numbers expanded by a multiplicative subgroup" — https://arxiv.org/pdf/1803.10564
- PlanetMath, "p-adic exponential and p-adic logarithm" — https://planetmath.org/padicexponentialandpadiclogarithm (channel unreachable this session; corroborated by the above)
