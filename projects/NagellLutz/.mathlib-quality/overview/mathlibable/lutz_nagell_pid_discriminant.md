# /mathlibable report — `LutzNagell.PID.lutz_nagell_pid_discriminant`

## Baseline (Phase 0)

- lake build:               not run (env: local build stale — task instruction; reasoned from source)
- decl `LutzNagell.PID.lutz_nagell_pid_discriminant`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:227`
- qualified name:           `LutzNagell.PID.lutz_nagell_pid_discriminant`
  (namespaces `namespace LutzNagell` → `namespace PID`, base name `lutz_nagell_pid_discriminant`)
- kind:                     `theorem`
- has sorry:                no (proof is `by_cases` + two prior helper lemmas)
- module docstring summary: "The Lutz–Nagell theorem over PIDs and number fields" — generalizes
  classical Nagell–Lutz from ℤ/ℚ to a char-0 PID `R` with fraction field `K`.

## Statement (Phase 1)

`lutz_nagell_pid_discriminant` is a **theorem** stating the *discriminant-divisibility half of
the Nagell–Lutz theorem*, in its general-Weierstrass form, as a **purely algebraic divisibility
fact over an arbitrary commutative ring**.

For a general Weierstrass curve `W : WeierstrassCurve R` and ring elements `x₀, y₀ ∈ R` lying on
the curve (`y₀² + a₁x₀y₀ + a₃y₀ = x₀³ + a₂x₀² + a₄x₀ + a₆`), set `κ₀ = 2y₀ + a₁x₀ + a₃` (so
`κ₀² = Ψ₂Sq(x₀) = 4x₀³ + b₂x₀² + 2b₄x₀ + b₆`). If `κ₀² ∣ 4·Ψ₃(x₀)` (where
`Ψ₃(x₀) = 3x₀⁴ + b₂x₀³ + 3b₄x₀² + 3b₆x₀ + b₈` is the 3-division polynomial evaluated at `x₀`),
then `κ₀ = 0` **or** `κ₀² ∣ 4Δ`, where `Δ` is the discriminant of `W`.

Although the surrounding section fixes `[IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`, this
theorem **`omit`s all three** (line 221): the statement and proof hold over any `CommRing R`.

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R]` — the (only effective) ring. Domain / PID / CharZero are `omit`-ted.
- `W : WeierstrassCurve R` — a general Weierstrass curve.

Hypotheses (Lean side):
- `hcurve` — `(x₀, y₀)` satisfies the affine Weierstrass equation.
- `hdvd_Psi3` — `(2y₀+a₁x₀+a₃)² ∣ 4·(3x₀⁴ + b₂x₀³ + 3b₄x₀² + 3b₆x₀ + b₈)`, i.e. `κ₀² ∣ 4Ψ₃(x₀)`.

Conclusion (math): `κ₀ = 0 ∨ κ₀² ∣ 4Δ`.
Conclusion (Lean): `(2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4 * W.Δ`.

The hypotheses/conclusion are written with **open-coded polynomial expressions** in the `bᵢ`,
not via mathlib's named `eval x₀ W.Ψ₂Sq` / `eval x₀ W.Ψ₃`. This matters in Phase 4c.

## Size classification (Phase 2a)

Verdict: BIG
Reason: theorem named after a person (Nagell–Lutz) — it is the discriminant-divisibility half of a
named classical theorem, and is listed under `## Main results` (`### Discriminant`) of the module.
(Literature width is EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Multi-line proof: `by_cases` + two
helper-lemma applications.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz … y divides discriminant integral coordinates"                                            | yes  | `y \| D` ⟹ `y² \| D` for `y²=x³+ax²+bx+c`            | Wikipedia, HandWiki, multiple lecture notes: canonical statement |
|  2 | WebSearch (general form)         | Nagell Lutz "y² divides" discriminant general Weierstrass `b₂ b₄ b₆` division polynomial               | yes  | "y² divides Δ" extends to general Weierstrass `bᵢ`   | confirms general-Weierstrass version with `b₂,b₄,b₆,b₈`; same Δ formula as mathlib |
|  3 | WebSearch (resultant/identity)   | resultant 2-div poly / 3-div poly = discriminant Bézout identity                                       | partial | `ψ₂ = 2y+a₁x+a₃`, `ψ₃ = 3x⁴+b₂x³+3b₄x²+3b₆x+b₈`; Δ↔div-poly links in valuation papers | the explicit Bézout cofactors not stated in surveyed excerpts — it's "folklore"/computational |
|  4 | ChatGPT MCP                      | standard form, generality, history of `κ₀²\|4Δ` + the resultant identity                                | n/a  | —                                                    | **MCP down** (Codex exec failed; task warned of this) — fell back to channels 1-3,6-10 |
|  5 | Local references                 | `.mathlib-quality/references/` for NagellLutz                                                          | n/a  | (no references dir)                                  | dir absent; no `refs/` symlink either — recorded n/a |
|  6 | nLab                             | "Nagell–Lutz theorem" / "division polynomial"                                                          | n/a  | nLab has no Nagell–Lutz / elliptic-torsion page      | not a higher-categorical concept; recorded n/a |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                                    | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | Nagell–Lutz / torsion of elliptic curves                                                               | n/a  | Stacks has no elliptic-curve torsion / Nagell–Lutz   | Stacks is scheme-theoretic foundations; this arithmetic result is out of its scope |
|  9 | MathOverflow / Math.SE           | (covered via WebSearch #1–3; lecture notes + Harvard "Nagell-Lutz, quickly" surfaced)                  | yes  | same `y² \| Δ` statement; proofs via 2P-doubling     | Alpoge "Nagell-Lutz, quickly" gives the doubling-formula proof route |
| 10 | recent arXiv (last 5 years)      | division polynomials valuations / discriminant (de Jong, Au-Yeung, Stange, arXiv 1108.3051, 1207.5387) | yes  | div-poly ↔ discriminant valuation results            | confirms the `ψ₂`/`ψ₃`/Δ relationship is studied; no cleaner closed identity than the Bézout one |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (specific
`y\|D`, general-Weierstrass `bᵢ`, the underlying resultant identity); ChatGPT MCP was attempted and
recorded `n/a` with the failure reason; local refs / nLab / Stacks / nCatLab / MathOverflow / arXiv
each checked or recorded `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: **the discriminant-divisibility half of the Nagell–Lutz theorem** — "if a
torsion point has integral coordinates then `y₀² ∣ Δ`" — in its **general-Weierstrass refinement**
`κ₀² ∣ 4Δ` with `κ₀ = ψ₂(x₀,y₀) = 2y₀ + a₁x₀ + a₃`.
Sources agree on the standard form: yes (Wikipedia / HandWiki / lecture notes all state `y \| D ⟹
y² \| D`; the general-`bᵢ` version is the standard upgrade).
Most general standard form: for a general Weierstrass curve over ℤ (or any commutative ring), the
2-division value `ψ₂(P) = 2y₀+a₁x₀+a₃` satisfies `ψ₂(P)² ∣ 4Δ` (for `P` a non-2-torsion integral
torsion point). The **purely-algebraic core** — drop "torsion" and instead assume the divisibility
`κ₀² ∣ 4Ψ₃(x₀)` directly — is exactly this theorem; that algebraic core is the natural
ring-theoretic lemma underneath the named theorem.
Generality dimensions where the literature varies:
  - curve form: short `y²=x³+ax²+bx+c` (states `y \| D`) … general `y²+a₁xy+a₃y=…` (states the `bᵢ`
    version). The most general is the general-Weierstrass `bᵢ` form — **this theorem uses it.**
  - base ring: classically ℤ. This theorem's *core* is over an **arbitrary `CommRing`** — strictly
    more general than every literature source (which all work over ℤ).
Disagreement with the literature: none. The theorem is the literature statement, refactored as a
hypothesis-on-divisibility algebraic lemma over a general ring (the "torsion ⟹ `κ₀²∣4Ψ₃`" input is
factored out into the consumer `lutz_nagell_discriminant_general` / `kappa_sq_dvd_four_Psi3`).

## Generality analysis — `LutzNagell.PID.lutz_nagell_pid_discriminant`

Literature-standard form (from Phase 3): `ψ₂(P)² ∣ 4Δ` for an integral torsion point on a general
Weierstrass curve over ℤ; the algebraic core holds over any commutative ring.

| # | Parameter / hypothesis            | Current Lean form                                  | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------------------------|-------------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]` (effective)        | arbitrary commutative ring                          | classically ℤ                             | NO (already maximal)| proof is two `ring`/`linear_combination` polynomial identities + `dvd_*`; holds over any CommRing. Already strictly more general than the literature. |
| 2 | curve = general Weierstrass `W`   | `2y₀+a₁x₀+a₃`, full `b₂,b₄,b₆,b₈`, `Δ`              | general Weierstrass (or short)            | NO (already maximal)| uses the general-Weierstrass `κ₀`/`Δ`; short form is the *specialisation* `a₁=a₃=0`. |
| 3 | `hdvd_Psi3 : κ₀² ∣ 4Ψ₃(x₀)`       | a *hypothesis* (the torsion input is factored out) | derived from torsion in the named theorem | n/a                 | Factoring the arithmetic input out as a hypothesis is what makes the lemma ring-general and reusable — a deliberate, good design, not a narrowing. |
| 4 | polynomial expressions            | **open-coded** `3*x₀^4 + b₂*x₀^3 + …`               | `eval x₀ W.Ψ₃`, `eval x₀ W.Ψ₂Sq`          | yes (idiom, see 4c) | mathlib has named `W.Ψ₂Sq`, `W.Ψ₃`; the idiomatic form evaluates those. Not a *generality* gap but an *idiom* gap → Phase 4c. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (on the mathematical axes — ring and curve generality
both already exceed the literature).
Number of weakening opportunities found: 0 (on generality axes).
Cost of restatement: n/a for generality. But Phase 4c finds an **idiom** restatement (open-coded
polynomials → mathlib's `W.Ψ₂Sq` / `W.Ψ₃`), which flips the final verdict — see 4c.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                       | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                             | no       | hypotheses already point-and-divisibility; nothing to bundle                           | — |
|  2 | sequences/metric → filters/topological?                                                        | no       | finite algebraic identity; no limits                                                   | — |
|  3 | construct an object → universal-property class?                                                | no       | it's a divisibility proposition                                                        | — |
|  4 | set-with-closure-predicate → bundled substructure?                                             | no       | no substructure here                                                                   | — |
|  5 | vector-space/field-specific → weaken typeclasses?                                              | no       | already over arbitrary `CommRing` — maximally weak                                     | — |
|  6 | 1-categorical → higher-categorical?                                                            | no       | n/a                                                                                    | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary algebraic structure?                                        | yes (done)| already generic `R`                                                                    | already general |
|  8 (extra) | **open-coded polynomial coefficients → mathlib's named division polynomials** `W.Ψ₂Sq`,`W.Ψ₃` | **yes** | hypothesis `(eval x₀ W.Ψ₂Sq) ∣ 4 * eval x₀ W.Ψ₃` (and `κ₀² = eval x₀ W.Ψ₂Sq` from `C_Ψ₂Sq`); conclusion unchanged `… ∣ 4*W.Δ` | composes with `WeierstrassCurve.Ψ₂Sq`/`Ψ₃` API, `C_Ψ₂Sq`, `ΨSq_two`, `Ψ_three`, `map_Ψ₂Sq`, `map_Ψ₃`, the EDS recurrences, and the `Φ`/`ΨSq` coordinate formulas — the whole `DivisionPolynomial/Basic.lean` surface |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**
  - Proposed mathlib-idiomatic restatement (sketch):
    ```lean
    theorem WeierstrassCurve.Ψ₂Sq_dvd_four_Δ {R} [CommRing R] (W : WeierstrassCurve R)
        {x₀ y₀ : R}
        (hcurve : y₀^2 + W.a₁*x₀*y₀ + W.a₃*y₀ = x₀^3 + W.a₂*x₀^2 + W.a₄*x₀ + W.a₆)
        (hdvd : (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4 * (W.Ψ₃.eval x₀)) :
        (2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4 * W.Δ
    ```
    (and a companion `(2y₀+a₁x₀+a₃)^2 = (W.Ψ₂Sq).eval x₀` via `C_Ψ₂Sq` + the curve equation, which
    is essentially the project's `kappa_sq_eq_Psi2Sq`).
  - Cost: **CHEAP** — the project *already* proved the exact eval-bridge lemmas needed
    (`Psi2Sq_eval_eq`, `Psi3_eval_eq` at PIDMain.lean:302/313; and the General-track twins), so
    converting open-coded ↔ `eval … Ψ₂Sq`/`Ψ₃` is a mechanical `rw`. The Bézout core (`bezout_identity`,
    `kappa_sq_dvd_four_delta`) is unchanged.
  - Mathlib downstream this enables: a `Δ`-divisibility lemma keyed on mathlib's *own* `Ψ₂Sq`/`Ψ₃`
    rather than open-coded coefficients composes with every existing division-polynomial lemma
    (`C_Ψ₂Sq`, `ΨSq_two`, `Ψ_three`, `map_Ψ₂Sq`/`map_Ψ₃`, the `preΨ`/`ΨSq`/`Φ` recurrences) and with
    the `twoTorsionPolynomial`↔`Δ` bridge (`twoTorsionPolynomial_discr`). The open-coded form blocks
    all of that (a user must re-prove the eval bridge every time).
  - Real mathematical improvement (not just "looks cooler"): yes — it states the Nagell–Lutz
    divisibility as a fact about the *division polynomials mathlib already defines*, eliminating the
    redundant open-coded copies of `Ψ₂Sq`/`Ψ₃` and slotting the result into the existing API.

Because Phase 4c says "modern idiom available" and the restatement is a real, CHEAP organisational
improvement, Phase 7 produces **YES-but-generalise-first (reason MODERN-IDIOM)** rather than
YES-add-as-is — per the skill's gate (a YES-add-as-is would be rejected when a real modern-idiom
restatement exists).

## Diamond / defeq risk — `LutzNagell.PID.lutz_nagell_pid_discriminant`

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search
paths). Phase 4.5 skipped.

## Mathlib search-status: `LutzNagell.PID.lutz_nagell_pid_discriminant`

[A] Lean-Finder       (mathlib index unavailable in env)                       n/a — index tool not loadable here; substituted with direct grep of the mathlib source tree (method D), which is authoritative for "does the lemma exist".
[B] Loogle            `WeierstrassCurve _, _ ∣ 4 * _.Δ` / `_ ∣ _.Δ` patterns   n/a — loogle tool not loadable here; covered by grep over `EllipticCurve/` (method D).
[C] LeanSearch        "Nagell Lutz discriminant divisibility torsion"          n/a — leansearch tool not loadable here; covered by web lit search + grep.
[D] Grep mathlib src  `nagell`/`lutz` (whole tree); `Δ` + `Ψ`/`Psi`/`division`/`twoTorsion` in `EllipticCurve/`; `Δ` in `DivisionPolynomial/`  →  **no hits for any `Δ`-divisibility / Nagell–Lutz lemma.** Found only `twoTorsionPolynomial_discr : W.twoTorsionPolynomial.discr = 16 * W.Δ` (Weierstrass.lean:308) — a *discriminant-of-the-2-torsion-cubic* identity, NOT a divisibility-by-a-point-value statement. `DivisionPolynomial/Basic.lean` defines `Ψ₂Sq`, `Ψ₃`, `Φ`, `preΨ`, EDS recurrences — but contains **no lemma mentioning `Δ`** at all.
[E] Name pattern      grep `lutz_nagell` / `Nagell` across mathlib              no hits (the only "Lutz" in mathlib is the author Patrick Lutz on Galois-theory files — unrelated).

Searched for both:
  - the user's current form (open-coded `κ₀² ∣ 4Δ`): not in mathlib.
  - the literature-standard / idiomatic form (`eval x₀ W.Ψ₂Sq ∣ 4·eval x₀ W.Ψ₃ → … ∣ 4·W.Δ`, or
    "Δ ∈ ideal(Ψ₂Sq, Ψ₃)" resultant identity): **not in mathlib.** Mathlib has the *pieces*
    (`Ψ₂Sq`, `Ψ₃`, `Δ`, `twoTorsionPolynomial_discr`) but **no lemma connecting a division-polynomial
    value to divisibility of `Δ`**, and no Nagell–Lutz result of any kind.

Concluded: **not in mathlib** (grep of the source tree exhausted, plus the literature-standard /
idiomatic form; closest existing decl is `twoTorsionPolynomial_discr`, which is a different — and
non-divisibility — statement).

## Call sites — `LutzNagell.PID.lutz_nagell_pid_discriminant`

Internal use count: **1** (within the project, excluding the declaring file)
External-to-file callers: 1 distinct file

| Caller file:line                                                     | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------------------------|---------------------------------------------------------------------|
| `LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean:201`          | `exact PID.lutz_nagell_pid_discriminant (R := ℤ) W hcurve (kappa_sq_dvd_four_Psi3 …)` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the decl?):
  - `GeneralDiscriminant.lean` has private twins of the *helper* lemmas (`kappa_sq_eq_Psi2Sq_eval_general`
    at :37, `kappa_sq_dvd_four_Psi3` at :123) — but it does **not** re-derive the Bézout/discriminant
    conclusion: it explicitly *delegates* that to `PID.lutz_nagell_pid_discriminant` (see the comment
    at GeneralDiscriminant.lean:195–199: "Delegate the discriminant conclusion … to the general PID
    lemma"). So the core is used, not bypassed.

Signal reading: K=1 internal use, no inline re-derivation of the core. This is the single canonical
entry point for the discriminant step across the project's two tracks (the General/ℚ track routes
through it over `R=ℤ`). It is real API, not dead code; the K=1 reflects that the project consolidated
both tracks onto this one ring-general lemma. (For a theorem, the YES-leaning bar is met: the named
result is the project's `## Main results` discriminant theorem, and it has a downstream consumer.)

## Composition check (Phase 6)

Can `lutz_nagell_pid_discriminant` be derived from mathlib in ≤3 chained calls?

Attempt 1: `dvd_*` plumbing only.
  - Mathlib decls available: `dvd_add`, `dvd_sub`, `dvd_mul_of_dvd_right`, `twoTorsionPolynomial_discr`.
  - Result: **fails.** The proof's heart is the explicit **Bézout identity** (`bezout_identity`,
    PIDMain.lean:189): `(432x³+108b₂x²+216b₄x + (−b₂³+36b₂b₄−108b₆))·Ψ₂Sq(x) +
    (−48x²−8b₂x + (b₂²−32b₄))·(6x²+b₂x+b₄)² = 4Δ`, plus the second identity
    `(6x²+b₂x+b₄)² + 4Ψ₃(x) = (12x+b₂)·Ψ₂Sq(x)` (PIDMain.lean:205). These are discharged by
    `simp only [b₂,b₄,b₆,b₈,Δ] ; ring` — bespoke degree-≤6 polynomial identities with hand-computed
    integer cofactors. Mathlib has no lemma supplying these cofactors.
  - Notes: `twoTorsionPolynomial_discr` gives `discr(2-torsion cubic) = 16Δ`, which is *related* but
    is the resultant/discriminant of one cubic — it does not give the two-polynomial Bézout
    combination needed to push `κ₀² ∣ 4Ψ₃` to `κ₀² ∣ 4Δ`.

Attempt 2: route through `Cubic.discr` / resultant API.
  - Mathlib decls used: `Cubic.discr`, `twoTorsionPolynomial`.
  - Result: **partial/fails.** Even granting `discr = 16Δ`, expressing `4Δ` as
    `(divisor of κ₀²-multiple) + (κ₀²-multiple)` still requires the explicit cofactor polynomials.
    No ≤3-call mathlib chain produces them; this is a genuine multi-step `ring`-backed proof.

Conclusion: **NOT-COMPOSABLE.** The two Bézout identities with explicit integer cofactors are the
mathematical content; they are a real proof, not a 1–3-call composition.

## Verdict: `LutzNagell.PID.lutz_nagell_pid_discriminant`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): identified as the **discriminant-divisibility half of the Nagell–Lutz
  theorem** (`y²|Δ`), here in its general-Weierstrass refinement `κ₀²|4Δ`; standard form confirmed
  across Wikipedia / HandWiki / lecture notes; the algebraic core over an arbitrary `CommRing` is
  *more* general than every source (all of which work over ℤ).
- Generality analysis (Phase 4): MAXIMALLY GENERAL on the ring/curve axes (already exceeds the
  literature). Phase 4c found a CHEAP **modern-idiom** restatement: phrase the hypothesis/conclusion
  via mathlib's named `W.Ψ₂Sq` / `W.Ψ₃` polynomials instead of open-coded coefficients.
- Mathlib search (Phase 5): **not in mathlib** — no Nagell–Lutz result, and no `Δ`-divisibility
  lemma in `DivisionPolynomial/`; closest is the unrelated `twoTorsionPolynomial_discr`.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the Bézout identities with explicit cofactors are
  genuine content, not a ≤3-call composition.

**Rationale:**

This is a genuine, named, classical result that mathlib lacks entirely (no `Nagell`/`Lutz` anywhere,
no division-polynomial-to-discriminant divisibility lemma). The statement is mathematically maximally
general — it holds over an arbitrary commutative ring (the domain/PID/CharZero typeclasses are
`omit`-ted), strictly stronger than every literature source, which works over ℤ — and it correctly
uses the general-Weierstrass `κ₀ = 2y₀+a₁x₀+a₃` rather than the short-form `2y₀`. The proof is a
real two-identity Bézout argument with hand-computed integer cofactors that no small mathlib
composition reproduces. All of that says **YES, mathlib should have this.**

The reason it is YES-**but-generalise-first** rather than YES-add-as-is is the Phase 4c idiom gap:
the theorem currently writes its hypothesis (`κ₀² ∣ 4·(3x₀⁴+b₂x₀³+…)`) and the `κ₀²=Ψ₂Sq(x₀)` step
with **open-coded polynomial coefficients**, duplicating polynomials that mathlib already defines
as `WeierstrassCurve.Ψ₂Sq` and `WeierstrassCurve.Ψ₃` in `DivisionPolynomial/Basic.lean`. The
mathlib-idiomatic contribution states the same fact against those named polynomials (hypothesis
`(eval x₀ W.Ψ₂Sq) ∣ 4 * eval x₀ W.Ψ₃`, with `κ₀² = eval x₀ W.Ψ₂Sq` supplied via `C_Ψ₂Sq` + the curve
equation), so it composes with the entire existing division-polynomial API instead of re-introducing
open-coded copies. This is not cosmetic: it removes a redundancy and slots the result into mathlib's
own EDS/division-polynomial surface. Critically, the restatement is **CHEAP** — the project already
proved the precise eval-bridge lemmas (`Psi2Sq_eval_eq`, `Psi3_eval_eq`) that convert between the two
forms, and the Bézout core is unchanged. Per the skill's gate, when a real, cheap modern-idiom
restatement exists, the verdict is YES-but-generalise-first, not YES-add-as-is.

Reason for the generalisation: **MODERN-IDIOM (Bourbaki 2.0)** — Phase 4c found a contemporary
mathlib formulation (state via the library's own `Ψ₂Sq`/`Ψ₃`) that is a real organisational
improvement. (Not LITERATURE-WEAKENING: the form is already maximally general on the math axes.)

Proposed restatement:
```lean
-- in Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/ (a new NagellLutz-ish file),
-- stated against mathlib's named division polynomials:
theorem WeierstrassCurve.eval_Ψ₂Sq_dvd_four_Δ {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {x₀ y₀ : R}
    (hcurve : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ =
      x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
    (hdvd : (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * (W.Ψ₃.eval x₀)) :
    2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 ∨
      (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ := by
  sorry -- proof = current `bezout_identity` + `kappa_sq_dvd_four_delta`, with the open-coded
        -- Ψ₂Sq(x₀)/Ψ₃(x₀) replaced by `eval x₀ W.Ψ₂Sq` / `eval x₀ W.Ψ₃` via `Psi2Sq_eval_eq`/`Psi3_eval_eq`.
        -- The companion `(2y₀+a₁x₀+a₃)^2 = (W.Ψ₂Sq).eval x₀` comes from `C_Ψ₂Sq` + `hcurve`.
```
Estimated cost of regeneralisation: **CHEAP** (eval bridges already exist; Bézout core unchanged).
Note: cost is not the reason for the verdict — the verdict is driven by the idiom improvement, which
is real regardless of cost.

Mathlib downstream this enables (required for MODERN-IDIOM):
- Composes with `WeierstrassCurve.Ψ₂Sq`, `Ψ₃`, `C_Ψ₂Sq`, `ΨSq_two`, `Ψ_three`, `map_Ψ₂Sq`,
  `map_Ψ₃`, and the `preΨ`/`ΨSq`/`Φ` recurrences in `DivisionPolynomial/Basic.lean`.
- Composes with the `twoTorsionPolynomial`↔`Δ` bridge `twoTorsionPolynomial_discr` (16Δ identity).
- The open-coded form **blocks** all of the above: any consumer must re-prove the eval bridge.
- Proofs that were blocked by the old form: deriving the Nagell–Lutz bound directly from a
  division-polynomial valuation statement (the arXiv 1108.3051 / de Jong line of work) would, in a
  formal setting, want the `Ψ₃.eval`/`Ψ₂Sq.eval`-keyed form.

**WHY add it (the gap, concretely):**
Mathlib's elliptic-curve corner has the *full machinery* — `Affine`/`Jacobian`/`Projective` point
groups, `DivisionPolynomial/Basic.lean` (`Ψ₂Sq`, `Ψ₃`, `Φ`, EDS recurrences), `Δ`,
`twoTorsionPolynomial_discr` — but has **no torsion-arithmetic results at all**: no Nagell–Lutz, no
"torsion points are integral", no `y² ∣ Δ`. This theorem is the discriminant half of that missing
arithmetic layer, and the named gap is concrete: `grep -ri "nagell\|lutz" Mathlib/` returns nothing
(only the unrelated author Patrick Lutz), and `DivisionPolynomial/Basic.lean` contains no lemma
mentioning `Δ`. The division-polynomial↔discriminant bridge is exactly the kind of result the
`DivisionPolynomial` API was built to support but currently stops short of.

Next action: run `/generalise LutzNagell.PID.lutz_nagell_pid_discriminant` (it will tension the
current open-coded form against both the literature-standard `κ₀²|4Δ` and the Phase-4c
`eval … Ψ₂Sq`/`Ψ₃` idiom), restate against mathlib's named division polynomials, then `/cleanup` and
open a PR to `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` (likely a new file
grouping the Nagell–Lutz divisibility lemma with `kappa_sq_dvd_four_Psi3_of_integral`, the natural
companion that supplies the `κ₀²∣4Ψ₃` hypothesis).

---

## Next step

Run `/generalise LutzNagell.PID.lutz_nagell_pid_discriminant`: restate the hypothesis and
`κ₀²=Ψ₂Sq(x₀)` step against mathlib's named `WeierstrassCurve.Ψ₂Sq` / `WeierstrassCurve.Ψ₃`
(CHEAP — the project's `Psi2Sq_eval_eq` / `Psi3_eval_eq` already bridge open-coded ↔ `eval`), keep
the Bézout core, then `/cleanup` and PR to `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`.
