# /mathlibable report — `LutzNagell.NumberField.lutz_nagell_number_field_cubicDisc_discriminant`

## Verdict (one line)

**BORDERLINE-needs-human** — the mathematical content (Nagell–Lutz "y² | cubic
discriminant" over a class-number-1 ring of integers) is a genuine, recently-active
research result that mathlib does **not** have. But *this specific declaration* is a
one-line `R := 𝓞 K` specialization of the more general project theorem
`PID.lutz_nagell_cubicDisc_discriminant`. The PID theorem is the real
mathlib-worthy unit; whether to *also* ship the number-field face (and how to grain
the PR family) is a packaging judgment for the maintainer. See the numbered
questions in Phase 7.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoning from source — task-sanctioned)
- decl `LutzNagell.NumberField.lutz_nagell_number_field_cubicDisc_discriminant`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:554`
- kind:                      theorem
- has sorry:                 no (delegates to `PID.lutz_nagell_cubicDisc_discriminant`, also sorry-free)
- module docstring summary:  "The Lutz–Nagell theorem over PIDs and number fields" —
                            generalizes classical Nagell–Lutz from ℤ/ℚ to a char-0 PID `R`
                            with fraction field `K`.

True qualified name confirmed: namespaces `LutzNagell` → `NumberField`, base name
`lutz_nagell_number_field_cubicDisc_discriminant`. (The parsed name in the task
prompt matches the source.)

---

### Statement (Phase 1)

`lutz_nagell_number_field_cubicDisc_discriminant` is the **short-Weierstrass
Nagell–Lutz discriminant-divisibility theorem for number fields of class number 1**.

In prose: Let `K` be a number field whose ring of integers `𝓞 K` is a principal
ideal ring (equivalently `classNumber K = 1`). Let `W : y² = x³ + a₂x² + a₄x + a₆`
be a Weierstrass curve over `𝓞 K` with `a₁ = a₃ = 0`. Let `(x, y)` be a nonsingular
point on `W / K` of finite additive order, and suppose that for every prime `p`
dividing the order of the point, `p` is squarefree in `𝓞 K` (the "unramified"
hypothesis). Suppose moreover the coordinates are already integral: `x = ι x₀`,
`y = ι y₀` with `x₀, y₀ ∈ 𝓞 K` and `y₀² = x₀³ + a₂x₀² + a₄x₀ + a₆`. Then

  `y₀ = 0`  OR  `y₀² ∣ 4a₄³ + 27a₆² + 4a₂³a₆ − a₂²a₄² − 18a₂a₄a₆`  in `𝓞 K`.

The right-hand divisor is the **cubic discriminant** disc(x³ + a₂x² + a₄x + a₆); note
the full Weierstrass discriminant satisfies `Δ = −16 · (cubic discriminant)` when
`a₁ = a₃ = 0` (the project's own `shortCurveZ_delta` confirms `Δ = −16(4A³+27B²)`
for `a₂ = 0`).

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K] [NumberField K] [DecidableEq K]` — the number field.
- `[IsPrincipalIdealRing (𝓞 K)]` — class number 1.
- `W : WeierstrassCurve (𝓞 K)`, `ha₁ : W.a₁ = 0`, `ha₃ : W.a₃ = 0` — short curve.

Hypotheses (Lean side):
- `hpt` — `(x, y)` nonsingular on the base-changed curve over `K`.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — torsion point.
- `hsf_all` — every prime dividing the order is squarefree in `𝓞 K` (unramified).
- `hx, hy` — coordinates are images of `x₀, y₀ ∈ 𝓞 K`.
- `hcurve` — `(x₀, y₀)` satisfies the integral short-Weierstrass equation.

Conclusion (math): `y₀ = 0 ∨ y₀² ∣ disc(x³+a₂x²+a₄x+a₆)` in `𝓞 K`.
Conclusion (Lean): `y₀ = 0 ∨ y₀ ^ 2 ∣ 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 + 4 * W.a₂ ^ 3 * W.a₆ − W.a₂ ^ 2 * W.a₄ ^ 2 − 18 * W.a₂ * W.a₄ * W.a₆`.

**Proof body:** one line —
`PID.lutz_nagell_cubicDisc_discriminant W ha₁ ha₃ hpt htor hsf_all hx hy hcurve`.
The entire mathematical work lives in the PID theorem (PIDMain.lean:424, ~50 lines:
reduces to `lutz_nagell_pid_discriminant_of_torsion`, then a division-polynomial
argument `kappa_sq_dvd_four_Psi3_of_torsion` + `ring`/`linear_combination`
manipulations of Ψ₂, Ψ₃). This decl just instantiates `R := 𝓞 K`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a theorem named after people (Nagell, Lutz), and a `## Main results`
headline of the project. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`PID.lutz_nagell_cubicDisc_discriminant …`).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. The Phase-2b def
exemption machinery does not apply to theorems. BUT the structural observation is
load-bearing for the verdict: this theorem's *proof* is a one-line delegation to a
strictly-more-general project theorem. That makes it a **specialization wrapper**,
which is exactly the NO-/BORDERLINE-flavored situation the skill's "re-aim" logic
is built for (see Phase 6/7).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "Nagell-Lutz torsion point y divides discriminant elliptic curve"                          | yes  | `y=0 ∨ y² ∣ Δ` for `y²=x³+ax²+bx+c`, a,b,c∈ℤ | Wikipedia, HandWiki, PlanetMath all agree verbatim |
| 2  | WebSearch (general form)         | "Nagell-Lutz number field ring of integers generalization torsion integral"                | yes  | generalizes to number fields / 𝓞_K; class-number conditions | arXiv 2509.07524 (Sep 2025), MIT 18.782 Lec 24 |
| 3  | WebSearch (named-after/short)    | "Silverman arithmetic elliptic curves Nagell-Lutz … y² divides discriminant"               | yes  | `β=0 ∨ β² ∣ (4A³+27B²)` for `Y²=X³+AX+B` | Silverman *Arithmetic of EC*; classical short form |
| 4  | WebSearch (exact identity)       | "cubic discriminant 4a³+27b² 4a2³a6 − a2²a4² − 18a2a4a6 Weierstrass"                        | yes  | confirms `Δ = −16·(cubic disc)`, `Δ_short = −4c³−27d²` | Wikipedia EC, mathlib Weierstrass docs, Stanford notes |
| 5  | Local references                 | `ls .mathlib-quality/references/`                                                           | n/a  | directory absent     | only `overview/` present; no source-paper PDFs |
| 6  | nLab                             | "nLab Nagell-Lutz torsion elliptic curve"                                                   | n/a  | nLab has no Nagell-Lutz page | not a category-theoretic concept; recorded n/a |
| 7  | nCatLab (if categorical)         | —                                                                                          | n/a  | —                    | not a categorical concept |
| 8  | Stacks Project (if alg geom)     | —                                                                                          | n/a  | —                    | arithmetic/Diophantine, not scheme-theoretic Stacks material |
| 9  | MathOverflow / Math.SE           | covered via WebSearch hits (Galperin REU, lecture notes, blogs)                            | yes  | same short + long form | UChicago REU (Galperin), Northeastern Dummit Lec 19 |
| 10 | recent arXiv (last 5 yrs)        | "arXiv 2509.07524 Nagell-Lutz imaginary quadratic class number one"                        | yes  | **NL for imag. quadratic fields, class number 1** | Mondal et al., Sep 2025 — exactly the 𝓞_K/PID setting |

Protocol pass check: WebSearch ran 4 distinct queries at three generality levels
(specific short form / number-field general form / named-after-Silverman); ChatGPT
MCP **down** (Codex error — task warned of this; substituted an extra WebSearch on
the exact discriminant identity, #4, as the fallback); local refs absent (n/a);
nLab checked (no page); Stacks/nCatLab n/a with reason; MathOverflow/arXiv covered.

### Literature summary (Phase 3)

Concept identified as: **Nagell–Lutz theorem** (torsion-divisibility half), short-
Weierstrass / depressed-cubic form, generalized to a class-number-1 ring of integers.

Sources agree on the standard form: **yes**. Universally: a finite-order point on
`y² = x³ + …` with integer (resp. 𝓞_K-integral) coordinates has `y = 0` or
`y² ∣ Δ`. For the short curve `Y² = X³ + AX + B`, `Δ = 4A³ + 27B²` (Silverman,
Wikipedia, PlanetMath). For the `a₁=a₃=0` long curve with an `a₂` term, the
divisor is disc(x³+a₂x²+a₄x+a₆) = `4a₄³+27a₆²+4a₂³a₆−a₂²a₄²−18a₂a₄a₆` — **exactly**
the project's RHS. The normalization-by-cubic-discriminant (rather than the full
`Δ = −16·(…)`) is the natural and standard choice for the short form.

Most general standard form: classically over ℤ/ℚ. The number-field extension is
**recent active research**: arXiv 2509.07524 (Sept 2025) proves it for imaginary
quadratic fields of class number 1 — i.e. precisely the `IsPrincipalIdealRing (𝓞 K)`
hypothesis. The literature notes the theorem "generalizes to arbitrary number
fields and more general cubic equations." General class number (>1) needs fractional
ideals; the class-number-1 case is where the clean `y² ∣ disc` divisibility survives.

Generality dimensions where the literature varies:
- base ring: ℤ (classical) → 𝓞_K class number 1 (2025 research) → Dedekind/ideals (general).
- curve shape: short `Y²=X³+AX+B` (textbook) → `a₁=a₃=0` with `a₂` (this decl) → full Weierstrass (the project's *other* theorem `lutz_nagell_number_field_discriminant`, full Δ).

Disagreement with the literature: **none**. The Lean statement is a faithful,
correctly-normalized rendering of the standard divisibility conclusion, at a
generality (any char-0 PID's fraction field, specialized to 𝓞_K) that *exceeds*
the published 2025 imaginary-quadratic result.

---

### Generality analysis — `lutz_nagell_number_field_cubicDisc_discriminant`

Literature-standard form (Phase 3): NL divisibility over a class-number-1 ring of
integers (arXiv 2509.07524 does imaginary quadratic; "generalizes to arbitrary
number fields"). The *project's own* `PID.lutz_nagell_cubicDisc_discriminant` is
strictly more general than this decl: it holds for **any** char-0 PID `R` (with
`[IsDomain] [IsPrincipalIdealRing] [CharZero]`, fraction field `K`), of which
`𝓞 K` for a class-number-1 number field is one instance.

| # | Parameter / hypothesis | Current Lean form (this decl) | Literature-standard / project-general form | Weaker form exists? | Reason |
|---|------------------------|-------------------------------|---------------------------------------------|---------------------|--------|
| 1 | base ring | `𝓞 K`, `[NumberField K] [IsPrincipalIdealRing (𝓞 K)]` | char-0 PID `R` (the PID theorem) | **yes** | The PID theorem already proves it for any char-0 PID. This decl re-specializes to 𝓞 K. |
| 2 | `[NumberField K]` | requires a number field | not needed by the PID proof | **yes** | the divisibility argument never uses finiteness of `[K:ℚ]`; only PID + char 0. |
| 3 | `ha₁ = ha₃ = 0` | short curve | matches the textbook short-form NL | NO (intentional) | this is the named short-Weierstrass case; a separate general-Δ theorem handles `a₁,a₃ ≠ 0`. |
| 4 | `hsf_all` (unramified) | squarefree primes ∣ order | standard "good reduction at p" hypothesis | NO | essential to the argument (controls denominators at ramified primes). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but narrower than a
*project* theorem, not narrower than anything in mathlib. The maximally-general
form already exists in the repo as `PID.lutz_nagell_cubicDisc_discriminant` (rows
1–2). This decl is the deliberate `R := 𝓞 K` "number-field face."

Number of weakening opportunities: 2 (drop to char-0 PID; drop `[NumberField]`).
Proposed restatement: none needed — the general form is *already written* as the
PID theorem. The right mathlib unit is the PID theorem, not a re-generalization of
this wrapper.
Cost of restatement: n/a (the general theorem exists; this is a packaging question).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | bundled hyps → typeclasses? | no | already idiomatic: `[NumberField K] [IsPrincipalIdealRing (𝓞 K)]` are the standard mathlib classes for "class number 1." | — |
| 2 | sequences → filters? | no | no limiting process; purely algebraic divisibility. | — |
| 3 | construction → universal property? | no | it's a divisibility theorem, not a construction. | — |
| 4 | set+closure → bundled substructure? | no | n/a. | — |
| 5 | field/metric-specific → weaker typeclass? | **yes** | the base ring should be a char-0 **PID** (and arguably a Dedekind/Krull domain with the squarefree hypothesis), not `𝓞 K`. | this is the Phase-4b point: the PID theorem already realizes it. |
| 6 | 1-categorical → higher? | no | n/a. | — |
| 7 | concrete index → general algebra? | **yes** (mild) | `𝓞 K` → general PID; matches row 5. | unifies with the project's own PID track. |

Modern idiom available: **yes**, but it is **already realized** by
`PID.lutz_nagell_cubicDisc_discriminant`. The "generalise first" target is the PID
theorem, which the project already has. So Phase 4c does not point to new work on
*this* decl — it points to the PID theorem being the canonical unit.

### Modern-idiom verdict (Phase 4c)
Real mathematical improvement: stating over a char-0 PID (done in the project)
eliminates the `[NumberField]` redundancy and unifies the ℤ-case and 𝓞_K-case
under one statement. This is exactly mathlib's "modules not vector spaces" ethos —
and the project already followed it. This decl is the specialization shadow.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities / instances introduced).

---

### Mathlib search-status: `lutz_nagell_number_field_cubicDisc_discriminant`

[A] Lean-Finder       (index tool unavailable in this env)              n/a: tool not loadable here
[B] Loogle            (index tool unavailable in this env)              n/a: tool not loadable here
[C] LeanSearch        (index tool unavailable in this env)              n/a: tool not loadable here
[D] Grep mathlib src  `Nagell` / `Lutz` (word-boundary, case-sens) over `.lake/packages/mathlib/`   **no hits** — only "Patrick Lutz" (Galois-theory author) in copyright headers; no Nagell-Lutz theorem
[D'] Grep mathlib src `IsLocalization.IsInteger` / `IsFractionRing.den` under `AlgebraicGeometry/`   **no hits** — mathlib never links elliptic-curve torsion to coordinate integrality
[D''] Grep mathlib src `torsion` under `AlgebraicGeometry/EllipticCurve/`   hits are only **2-torsion polynomials** / `twoTorsionPolynomial` / EDS degree lemmas — not the NL divisibility result
[E] Name pattern      `lutz_nagell_number_field_cubicDisc_discriminant` (qualified) over mathlib   **no hits**

Searched for both:
  - this decl's form (𝓞 K, class number 1) — absent.
  - the literature-standard general form (`y² ∣ Δ` for any torsion point) — absent.
  - mathlib's building blocks present: `WeierstrassCurve.Ψ₂Sq`, `twoTorsionPolynomial`,
    `Mathlib.NumberTheory.EllipticDivisibilitySequence`, `DivisionPolynomial.{Basic,Degree}`,
    `IsFractionRing.den`, `IsLocalization.IsInteger` — but no lemma combining them into NL.

Concluded: **not in mathlib** (grep over the whole tree exhausted, plus the general
form; the index tools were unavailable, but a name/word grep is authoritative for a
*named theorem* — a Nagell–Lutz theorem would carry the name, and it does not exist).
Mathlib has the **building blocks** (division polynomials, EDS, fraction-ring
denominators) but not the result.

---

### Call sites — `lutz_nagell_number_field_cubicDisc_discriminant`

Internal use count: **0** (project-wide grep, excluding the declaring line 554).
External-to-file callers: **0**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | no call site anywhere in `projects/` |

Inline-derivation grep: the *general* PID theorem `lutz_nagell_cubicDisc_discriminant`
also has **0** external callers — its only use is this very wrapper at PIDMain.lean:569.
So the entire short-Weierstrass-cubicDisc result (PID + number-field faces) is, at
present, terminal API: proven as a headline `## Main result`, not yet consumed
downstream. This is the expected shape for a freshly-formalized named theorem that
*is itself* the deliverable (cf. `lutz_nagell` over ℤ at Main.lean:66).

Signal reading: K = 0 internal uses, no inline re-derivation. For a **named main
theorem** this reads as "genuinely-new headline result," not "dead wrapper" — the
theorem is the product, not a helper. (Contrast: a K=0 one-line *helper* def would
read as junk; a K=0 named Nagell–Lutz theorem is the point of the project.)

---

### Composition check (Phase 6)

Can `lutz_nagell_number_field_cubicDisc_discriminant` be derived from **mathlib** in
≤3 chained calls?

Attempt 1: instantiate some mathlib NL/torsion-divisibility lemma at `R := 𝓞 K`.
  - Mathlib decls used: none exist (Phase 5: no NL in mathlib).
  - Result: **fails** — there is nothing in mathlib to instantiate.

Attempt 2: compose from mathlib division-polynomial + EDS + fraction-ring API.
  - The actual proof (in the PID theorem) is ~50 lines: `lutz_nagell_pid_discriminant_of_torsion`
    → `kappa_sq_dvd_four_Psi3_of_torsion` (a division-polynomial divisibility result,
    itself a multi-file development over the project's forked DivisionPolynomial/EDS),
    then `linear_combination`/`ring` discriminant algebra and a `dvd_add`/`dvd_sub`
    chain. None of these intermediate lemmas are mathlib lemmas.
  - Result: **fails** — this is a real, long proof, not a 1–3 call composition.

Conclusion: **NOT-COMPOSABLE** from mathlib.

BUT — and this is the decisive point — it **IS** a ≤1-call composition from the
*project's own* `PID.lutz_nagell_cubicDisc_discriminant` (literally its one-line
body). The composition that trivializes this decl is internal to the project, not
internal to mathlib. So mathlib-composability is NO, but project-redundancy-vs-the-
PID-theorem is the real question (Phase 7).

---

## Verdict: `LutzNagell.NumberField.lutz_nagell_number_field_cubicDisc_discriminant`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz "y² ∣ cubic discriminant" is the
  universally-standard divisibility conclusion (Silverman, Wikipedia, PlanetMath);
  the 𝓞_K / class-number-1 generalization is genuine recent research (arXiv
  2509.07524, Sept 2025). The Lean statement matches the standard form exactly and
  is *more* general than the published number-field result.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — but narrower
  only than the *project's own* `PID.lutz_nagell_cubicDisc_discriminant`, which is
  the maximally-general char-0-PID form and already exists in the repo.
- Mathlib search (Phase 5): **not in mathlib**, in any form; mathlib has the
  building blocks (division polynomials, EDS, `IsFractionRing.den`) but no NL result.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the proof is ~50
  lines of division-polynomial reasoning), but a trivial ≤1-call specialization of
  the project's PID theorem.

**Rationale:**

The mathematical content here is unambiguously mathlib-worthy and absent from
mathlib: the Nagell–Lutz divisibility theorem is a classical named result that
mathlib lacks entirely, and the class-number-1 number-field generalization is at the
frontier of current research (a Sept-2025 arXiv paper proves exactly the imaginary-
quadratic case; this formalization covers all char-0 PIDs). So this is decidedly not
a NO-mathlib-has-it.

The reason it is **not a clean YES-add-as-is** is structural, and it is the precise
situation the skill flags rather than auto-resolves. This declaration is a one-line
`R := 𝓞 K` *specialization wrapper* over `PID.lutz_nagell_cubicDisc_discriminant`,
which lives in the **same project** and is strictly more general (Phase 4b rows 1–2:
the `[NumberField K]` hypothesis is unused by the proof; only char-0 + PID is needed).
Under mathlib's "add the most general form" rule, the canonical contribution is the
**PID theorem**, from which both the ℤ-case and the 𝓞_K-case fall out. Whether
mathlib *also* wants the number-field-specialized face as a separate convenience
lemma — and how to group the PR family (the project also has `lutz_nagell` over ℤ at
Main.lean:66, `lutz_nagell_discriminant` over ℤ, and the full-Δ number-field version
`lutz_nagell_number_field_discriminant` at PIDMain.lean:533) — is a packaging /
taste call that depends on maintainer preference. It is not a cost-based downgrade
(which the gate forbids as a self-resolving verdict); it is a genuine "which grain of
API does mathlib want, and is the PID theorem or the 𝓞_K face the right primitive?"
judgment. Hence BORDERLINE, with the PID theorem strongly indicated as the real unit.

**Numbered questions (≤5):**
1. Should mathlib receive the **general PID/char-0 theorem**
   `PID.lutz_nagell_cubicDisc_discriminant` as the primitive, with this 𝓞_K theorem
   as a thin specialization shipped alongside it — yes/no? (Recommended: yes to the
   PID theorem; the 𝓞_K face is optional sugar.)
2. If only one is shipped, prefer the **PID/char-0** form (max generality, the
   mathlib idiom) over the number-field form — yes/no?
3. Should the short-Weierstrass `cubicDisc` theorem ship in **one PR together with**
   the companion full-Δ theorem `lutz_nagell_number_field_discriminant` (and their
   PID parents), as the "Nagell–Lutz divisibility" bundle — yes/no?
4. Does shipping this require first upstreaming the project's **forked DivisionPolynomial /
   EllipticDivisibilitySequence development** (the proof depends on
   `kappa_sq_dvd_four_Psi3_of_torsion`, built on the forked API) — i.e. is this
   blocked on a larger mathlib PR chain? (Likely yes — flag as a dependency.)
5. Is the `[IsPrincipalIdealRing (𝓞 K)]` (class-number-1) restriction acceptable for
   mathlib, or should the maintainer wait for the general-class-number (fractional-
   ideal) statement before adding the named "number field" theorem — yes/no?

**Next action:** user answers the questions; then run `/mathlibable
LutzNagell.PID.lutz_nagell_cubicDisc_discriminant` to assess the general parent
directly (it is the recommended primary contribution), and `/generalise` on the PID
theorem to confirm no further weakening (char-0 PID → Dedekind domain?). If the
maintainer decides the PID theorem is the unit and this 𝓞_K wrapper is redundant
sugar, the practical disposition of *this* decl trends toward
NO-composable-from-(the-project's-own)-PID-theorem — but that is an internal-API
call the maintainer makes, not a mathlib-composability fact.

---

## Next step

Answer the five questions above (especially Q1/Q4). The mathematically-correct
mathlib unit is the **general PID theorem** `PID.lutz_nagell_cubicDisc_discriminant`,
not this number-field specialization; assess that decl next, and treat the forked
DivisionPolynomial/EDS upstreaming as a likely prerequisite PR chain.
