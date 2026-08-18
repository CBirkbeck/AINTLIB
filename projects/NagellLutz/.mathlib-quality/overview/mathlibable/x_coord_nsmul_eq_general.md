# /mathlibable report — `LutzNagell.LutzNagellTheorem.x_coord_nsmul_eq_general`

## Verdict: YES-but-generalise-first

**One-line:** This is the canonical division-polynomial identity for the x-coordinate of `n•P`
(`x([n]P) = Φₙ(x)/ΨSqₙ(x)`, Silverman AEC Ex 3.7) — genuinely missing from mathlib, which defines
`Φ`/`ΨSq` but never links them to the group law. But the decl here is a **one-line `ℤ/ℚ`
specialisation wrapper** over the strictly-more-general `PID.x_coord_nsmul_eq` (arbitrary
integral domain `R` + fraction field `K`); the general form is what should be upstreamed, not its
`ℚ` shadow.

---

### Baseline (Phase 0)
- lake build:               NOT re-run (env stale per task brief; reasoned from source + the vendored
  mathlib checkout under `.lake/packages/mathlib/…`, which is the exact pinned mathlib).
- decl `LutzNagell.LutzNagellTheorem.x_coord_nsmul_eq_general`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralIntegralMultiple.lean:43`.
- kind:                      theorem
- has sorry:                 no (1-line proof, `:= PID.x_coord_nsmul_eq W hns hn hns' hnP`).
- module docstring summary:  "Integral multiple implies integral point (general Weierstrass curves)"
  — the `ℤ/ℚ` specialisations of the `LutzNagell.PID` track (over a UFD `R`, fraction field `K`).

**Qualified name VERIFIED.** Namespaces nest `LutzNagell` (line 26) → `LutzNagellTheorem` (line 27),
both closed at the file end (lines 93–94). So the parsed
`LutzNagell.LutzNagellTheorem.x_coord_nsmul_eq_general` is correct.

---

### Statement (Phase 1)

For an integral Weierstrass curve `W` over `ℤ`, its base-change `curveQ W` to `ℚ`, a nonsingular
affine point `P = (x, y)` on `curveQ W`, a nonzero integer `n`, and a nonsingular affine point
`(x', y')` with `n • P = (x', y')` (in the affine group `Affine.Point`), one has:

> `x' · (ΨSqₙ)(x) = (Φₙ)(x)`

where `ΨSqₙ, Φₙ ∈ ℚ[X]` are the (squared / numerator) division polynomials of `curveQ W`.

This is the **cleared-denominator form** of the classical multiplication-by-`n` x-coordinate
formula `x([n]P) = φₙ(x)/ψₙ²(x) = Φₙ(x)/ΨSqₙ(x)` (Wikipedia "Division polynomials"; Silverman,
*The Arithmetic of Elliptic Curves*, Exercise 3.7).

Variables / typeclasses (Lean side):
- `(W : WeierstrassCurve ℤ)` — the integral Weierstrass curve (section variable, line 31).
- `{x y : ℚ}` — coordinates of `P`.
- `{n : ℤ}` — the multiplier.
- `{x' y' : ℚ}` — coordinates of `n • P`.

Hypotheses (Lean side):
- `(hns : (curveQ W).toAffine.Nonsingular x y)` — `P` is a nonsingular point.
- `(hn : n ≠ 0)` — nonzero multiplier (needed so `ΨSqₙ` is not the zero polynomial; degree control).
- `(hns' : (curveQ W).toAffine.Nonsingular x' y')` — `n • P` is a nonsingular point.
- `(hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')` — the multiplication relation.

Conclusion (math): `x' = Φₙ(x) / ΨSqₙ(x)`, in cleared form `x' · ΨSqₙ(x) = Φₙ(x)`.
Conclusion (Lean): `x' * ((curveQ W).ΨSq n).eval x = ((curveQ W).Φ n).eval x`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline, but BIG by content).
Reason: it is a *named classical formula* — the multiplication-by-`n` x-coordinate identity, the
backbone of the division-polynomial theory. Not named after a person, but it is the central
mathematical fact the whole `DivisionPolynomial` ⇄ group-law bridge exists to express, and a main
ingredient of the Nagell–Lutz development. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1** substantive line (`PID.x_coord_nsmul_eq W hns hn hns' hnP`).
One-liner verdict: **n/a — kind is `theorem`, not `def`/`abbrev`/`structure`.**

The Phase-2b one-liner machinery targets *definitions* whose body is one line (defeq/diamond/API
exemptions). For a `theorem`, a one-line body is not a negative signal — it just means the proof is
a single application. The relevant structural observation (this theorem is a thin **specialisation
wrapper** over `PID.x_coord_nsmul_eq`) is captured in Phases 4–7 instead; it drives the
generalise-first verdict, not a "delete the wrapper" verdict, because the *general* lemma is the
mathlib target.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "x-coordinate of n times point division polynomials phi_n psi_n x([n]P)=phi_n/psi_n^2"             | yes  | `x([n]P) = φₙ(x)/ψₙ²(x)`, `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`     | Wikipedia "Division polynomials"; arXiv 1103.4560, 1108.3051 — universal in EC theory |
|  2 | WebSearch (general form / base)  | "division polynomials Weierstrass arbitrary base ring scheme multiplication-by-n universal formula" | yes  | `nP = (αₙ:βₙ:γₙ)` over **any ring** via Thm of the Cube | Yelton arXiv 1303.4327 ("Homogeneous division polynomials"); mathlib4 docs DivisionPolynomial/Degree |
|  3 | WebSearch (named-after / textbook)| "Silverman Arithmetic of Elliptic Curves division polynomial x([n]P) multiplication-by-n exercise" | yes  | Silverman AEC **Exercise 3.7**; `[n]P=(φ/ψ², ω/ψ³)`  | Standard textbook statement; also Washington, Lang |
|  4 | ChatGPT MCP                      | "standard reference + generality of x'·ψ_n²(x)=φ_n(x); holds over arbitrary commutative ring?"      | n/a  | —                                                    | **MCP DOWN** (Codex exec failed twice, both reasoning_effort levels) — per task brief; covered by #1/#2/#3 |
|  5 | Local references                 | (none in repo)                                                                                     | n/a  | —                                                    | `refs/NagellLutz/` is local-only/gitignored and absent in this checkout; recorded n/a |
|  6 | nLab                             | "division polynomial" / "multiplication by n elliptic curve"                                       | n/a  | —                                                    | nLab has no dedicated division-polynomial page; concept is classical AG, well-covered by #1–#3 |
|  7 | nCatLab (if categorical)         | —                                                                                                  | n/a  | —                                                    | Not a categorical concept (concrete polynomial identity) |
|  8 | Stacks Project (if alg geom)     | "elliptic curve division polynomial multiplication map"                                            | n/a  | —                                                    | Stacks treats abelian schemes / `[n]` abstractly but has no explicit division-polynomial x-coordinate formula |
|  9 | MathOverflow / MathSE            | "x coordinate n*P division polynomials generality over a ring"                                     | yes  | confirms #1; numerous EC threads                     | folded into #1/#2 web results |
| 10 | recent arXiv (last ~5y)          | "division polynomials arbitrary isogenies / base ring"                                             | yes  | Stange arXiv 2503.15428; Yelton 1303.4327            | modern treatments keep the formula over arbitrary rings |

Protocol pass check: WebSearch ran 3+ distinct queries at different generality levels (specific
form #1, general-base form #2, named-after/textbook #3) ✓. ChatGPT MCP attempted but DOWN
(recorded n/a with reason) — the brief flagged this; the three web channels + Yelton's paper
answer the generality question definitively. Local refs / nLab / nCatLab / Stacks / MO / arXiv each
checked or n/a'd with reason ✓.

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` x-coordinate formula via division polynomials**,
`x([n]P) = φₙ(x)/ψₙ²(x)` (equivalently `Φₙ(x)/ΨSqₙ(x)`). Standard name: Silverman AEC Exercise 3.7;
ubiquitous in Washington, Lang, and every elliptic-curve text.
Sources agree on the standard form: **yes** — the identity and the definition `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`
are uniform across the literature.
Most general standard form: the formula is a **polynomial identity valid over an arbitrary
commutative base ring** (Yelton arXiv 1303.4327 establishes `nP = (αₙ:βₙ:γₙ)` over any ring via the
Theorem of the Cube; mathlib's own `ΨSq`/`Φ` are defined over any `CommRing R`). After clearing
denominators, `x' · ΨSqₙ(x) = Φₙ(x)` needs only that the points live in a field/fraction field for
the *coordinates* to make sense — no characteristic and no field-of-definition restriction to `ℚ`.
Generality dimensions where the literature varies:
  - **base ring**: from `ℚ`/number fields/finite fields up to **arbitrary commutative ring**; the
    most general is "any ring", and the cleared-denominator identity lives there.
  - **model**: short Weierstrass (`y²=x³+ax+b`) vs **general Weierstrass** (`a₁…a₆`); the general
    Weierstrass model is the modern/mathlib standard (and what this decl uses) ✓.
Disagreement with the literature: **none** on content. The only gap is *generality of the Lean
statement*: this decl fixes `ℤ/ℚ`, whereas the literature standard is the general-base form.

---

### Generality analysis — `x_coord_nsmul_eq_general`

Literature-standard form (from Phase 3): the identity over an **arbitrary commutative base ring**
(integral domain → fraction field for the coordinate version). The general Weierstrass model is
already used here.

| # | Parameter / hypothesis            | Current Lean form                | Literature-standard form                      | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------|-----------------------------------------------|---------------------|---------------------------------|
| 1 | base ring of `W`                  | `WeierstrassCurve ℤ` (`ℤ`)       | `WeierstrassCurve R`, any `CommRing`          | **YES**             | The relation is a coordinate-ring identity; nothing uses `R = ℤ`. The project's `PID.x_coord_nsmul_eq` already states it for any `[CommRing R] [IsDomain R]` with a fraction field. |
| 2 | coordinate field                  | `ℚ` (`curveQ W`)                 | `K = Frac(R)`, any field with the points      | **YES**             | The proof works in `curveK R K W`; `ℚ` is just `K = ℚ`. `PID.x_coord_nsmul_eq` uses `{K} [Field K] [Algebra R K] [IsFractionRing R K]`. |
| 3 | `(hns)/(hns')` nonsingular        | nonsingular affine points        | same                                          | NO                  | The group `Affine.Point` is built on nonsingular points; intrinsic, not a weakening target. |
| 4 | `(hn : n ≠ 0)`                    | `n ≠ 0` in `ℤ`                   | same                                          | NO                  | Needed for `ΨSqₙ ≠ 0`/degree; the general lemma keeps it (and in fact only uses it nominally — see PID source `_hn`). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**.
Number of weakening opportunities found: **2** (base ring `ℤ → R`; coordinate field `ℚ → K = Frac R`).
Proposed restatement: **it already exists, verbatim, in the project** as
`LutzNagell.PID.x_coord_nsmul_eq` (`PIDIntegralMultiple.lean:39`):

```lean
theorem x_coord_nsmul_eq
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R)
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {n : ℤ} (_hn : n ≠ 0)
    {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
    x' * ((curveK R K W).ΨSq n).eval x = ((curveK R K W).Φ n).eval x
```

Cost of restatement: **CHEAP** — already proved. The general lemma's proof (PIDIntegralMultiple.lean
:44–62) actually uses an even weaker typeclass cluster than the `_general` docstring suggests: the
`omit` on line 37 drops `[IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R K]`, so the
core identity needs only `CommRing R` + `Algebra R K` machinery to make `curveK` and the points
land. The `ℤ/ℚ` wrapper adds nothing mathematically; it exists only to feed the concrete
`∃ x₀ : ℤ, …` downstream consumers.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation                                  | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------|----------|---------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                         | no       | already fully typeclass-driven                          | — |
|  2 | sequences/metric → filters/topological?                                                    | no       | no analytic content                                     | — |
|  3 | construct an object → universal-property class?                                            | no       | it's an identity, not a construction                    | — |
|  4 | set-with-closure-predicate → bundled substructure?                                          | no       | n/a                                                     | — |
|  5 | vector-space/field-specific → modules/(semi)ring weakening?                                 | **yes**  | base ring `ℤ`/field `ℚ` → general `R`/`K = Frac R` (= Phase 4b axes 1–2) | the whole division-polynomial group-law bridge over any base; EDS / Nagell–Lutz / Mazur-type developments reuse it |
|  6 | 1-categorical → higher-categorical?                                                          | no       | n/a                                                     | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                              | no       | `n : ℤ` is intrinsic to the multiplication-by-`n` map   | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and it coincides with the literature-weakening from Phase 4b
(generalise base `ℤ → R`, field `ℚ → K`). It is the `PID`-track form already in the project.
  - Proposed mathlib-idiomatic restatement: `PID.x_coord_nsmul_eq` (signature above), renamed into
    the `WeierstrassCurve` namespace for upstream (e.g. `WeierstrassCurve.x'_mul_ΨSq_eval_eq_Φ_eval`
    or similar — naming TBD with a reviewer).
  - Cost: **CHEAP** (the general proof is done).
  - Mathlib downstream this enables: this is the **missing link** between `WeierstrassCurve.Φ`/`ΨSq`
    (mathlib already has the polynomials + their recurrences/degrees) and `Affine.Point`/`Jacobian`
    multiplication. With it, mathlib gains the first lemma that says what the division polynomials
    *compute* about the group law — the foundation for torsion-point bounds, Nagell–Lutz, reduction
    arguments, and elliptic divisibility sequences indexed by actual points.
  - Real mathematical improvement: not cosmetic — it generalises across every base ring at zero
    proof cost and is the canonical bridge result, currently absent from mathlib entirely.

(Phase 4.5 diamond/defeq risk: **n/a — declaration kind is `theorem`.**)

---

### Mathlib search-status: `x_coord_nsmul_eq_general`

[A] Lean-Finder       (web index unavailable in this env; folded into web channels) — n/a: tool not wired here
[B] Loogle            `WeierstrassCurve.Φ`, `_ * (WeierstrassCurve.ΨSq _).eval _ = (WeierstrassCurve.Φ _).eval _`  — n/a: `lean_loogle` MCP not registered in this env (only WebSearch/DesignSync/ChatGPT/Cron loaded). Substituted by Method D over the pinned checkout.
[C] LeanSearch        "x-coordinate of n•P equals Phi over Psi squared division polynomial"  — n/a: `lean_leansearch` MCP not registered. Substituted by Method D + WebSearch #1 (which returns the mathlib4 docs).
[D] Grep mathlib src  `grep -rnE 'nsmul|smul|addX|x.?coord|coordinate|Point' .lake/.../DivisionPolynomial/ EllipticDivisibilitySequence.lean`; `grep -rlniE 'x_coord_nsmul|nsmul.*ΨSq|coordinate.*\[n\]' .lake/.../Mathlib/`  — **NO HITS** linking `Φ`/`ΨSq` to a point's coordinate, across all of mathlib.
[E] Name pattern      `x_coord`, `_nsmul_eq`, `coord_.*smul`, `smul.*_eval` over mathlib  — hits are unrelated (`AddCircle.addOrderOf_nsmul_eq_zero`, `Angle.two_nsmul_eq_iff`, `Module.smul_eq_eval`); **none** about elliptic-curve division polynomials.

Searched for both:
  - the user's current form (`ℤ/ℚ`) — absent.
  - the literature-standard general-base form — also absent.

What mathlib **does** have (the building blocks, all in `DivisionPolynomial/Basic.lean`): the
definitions `Ψ₂Sq`, `preΨ'`, `preΨ`, `ΨSq`, `Ψ`, `Φ`, `φ`, `ψ` over any `CommRing R`, plus their
zero/one/.../four/neg/even/odd recurrences and the coordinate-ring congruences
`Affine.CoordinateRing.mk_ψ₂_sq`, `mk_Ψ_sq` — and degree/leading-coeff facts in `Degree.lean`.
**None** of these connects the polynomials to `n • P` in the group `Affine.Point`/`Jacobian.Point`.

Concluded: **not in mathlib** (all methods exhausted — Methods A–C unavailable in-env and
substituted by authoritative grep over the exact pinned mathlib + web; Methods D, E ran in full;
both the user's form and the general-base form are absent).

---

### Call sites — `x_coord_nsmul_eq_general`

Internal use count: **1** (within NagellLutz, excluding the declaring file).
External-to-file callers: **1** distinct file.

| Caller file:line                         | Usage pattern (one-line excerpt)                                         |
|------------------------------------------|--------------------------------------------------------------------------|
| LutzNagell/.../GeneralDiscriminant.lean:147 | `have hcoord := x_coord_nsmul_eq_general W hpt (show (2:ℤ)≠0 …) hns' h2P_zsmul` (the `n=2` 2-torsion case, feeding `PsiSq_two_eval_eq`/`Phi2_eval_eq`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `x_coord_nsmul_eq_general`?):
  - `PIDMain.lean:369` calls the **general** `PID.x_coord_nsmul_eq` directly (the PID-track twin of
    GeneralDiscriminant). So the `_general` `ℚ`-wrapper and the `PID` form are used in parallel
    tracks — the `ℚ` one only because the `GeneralDiscriminant` consumer wants `ℚ`-concrete output.
  - No third inline re-derivation of the identity from scratch.

Signal: K = 1 internal use → thin abstraction; combined with the body being a literal
`PID.x_coord_nsmul_eq …` call, this is a **specialisation wrapper**, not standalone API. Leans the
verdict away from "ship this decl as-is" and toward "ship the general parent".

---

### Composition check (Phase 6)

Can `x_coord_nsmul_eq_general` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: apply some mathlib lemma relating `n • P` to `Φ`/`ΨSq`.
  - Mathlib decls used: — none exist (Phase 5: mathlib has no `Φ`/`ΨSq` ⇄ group-law lemma).
  - Result: **fails**. There is no mathlib primitive that even mentions the multiplication-by-`n`
    map alongside the division polynomials, so no 1–3 call composition can produce this.

Attempt 2: assemble from `mk_Ψ_sq` (coordinate-ring congruence) + `Jacobian` smul + evaluation.
  - This is essentially the *proof* of `PID.x_coord_nsmul_eq` (PIDIntegralMultiple.lean:44–62): it
    needs `Jacobian.Point.toAffineAddEquiv`, `map_zsmul`, `X_eq_of_equiv`, `evalEval_φ_eq_eval_Φ`,
    `evalEval_Ψ_sq_eq_eval_ΨSq`, several `simp`/`norm_num` rewrites — ~18 lines of real reasoning,
    not a composition.
  - Result: **NOT a composition** (proof in disguise).

Conclusion: **NOT-COMPOSABLE** from mathlib. (It *is* a 1-call composition over the **project's own**
`PID.x_coord_nsmul_eq`, but that lemma is itself the candidate for mathlib — composability over a
not-yet-upstreamed project lemma does not make the result composable from mathlib.)

---

## Verdict: `LutzNagell.LutzNagellTheorem.x_coord_nsmul_eq_general`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): the multiplication-by-`n` x-coordinate formula `x([n]P)=Φₙ/ΨSqₙ`
  (Silverman AEC Ex 3.7; Yelton arXiv 1303.4327) — standard, and standard **over an arbitrary base
  ring**.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — current form fixes `ℤ/ℚ`; the
  literature (and the project's own `PID` track) state it over any integral domain `R`/fraction
  field `K`.
- Mathlib search (Phase 5): **not in mathlib** under either form; mathlib has `Φ`/`ΨSq` and their
  recurrences but no link to the group law `n • P`.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the only short derivation is over the
  project's own general lemma, which is itself the upstream target).

**Rationale:**

The mathematical content — "the x-coordinate of `n•P` is `Φₙ(x)/ΨSqₙ(x)`" — is the keystone of
division-polynomial theory and is genuinely absent from mathlib: the pinned mathlib defines all of
`Ψ₂Sq, preΨ, ΨSq, Ψ, Φ, φ, ψ` over an arbitrary `CommRing` and proves their recurrences, degrees,
and coordinate-ring congruences (`mk_Ψ_sq`), but **nowhere** connects them to the actual group law
on `Affine.Point`/`Jacobian.Point`. Searching every mathlib file for any lemma mentioning a point's
coordinate alongside `Φ`/`ΨSq` returns nothing. This is exactly the kind of "the polynomials are
there but the theorem that gives them meaning is missing" gap that mathlib wants filled.

But the decl under assessment is the **wrong form to upstream**. Its body is the single application
`PID.x_coord_nsmul_eq W hns hn hns' hnP`, a `ℤ/ℚ` specialisation of the project's own
`LutzNagell.PID.x_coord_nsmul_eq`, which proves the identical statement over an arbitrary integral
domain `R` with fraction field `K` (and whose proof, per the `omit` on PIDIntegralMultiple.lean:37,
uses an even weaker typeclass cluster than its docstring advertises). Mathlib's iron rule is to add
the most general form; here the general form is already proved, at zero extra cost, sitting one file
away. The `_general` wrapper exists only to hand the downstream `GeneralDiscriminant` consumer a
`ℚ`-concrete output (`∃ x₀ : ℤ, …`), which is a project-internal convenience, not a mathlib concern.
Hence: generalise first — upstream `PID.x_coord_nsmul_eq` (suitably renamed into the
`WeierstrassCurve` namespace), and let any `ℤ/ℚ` use be a call-site specialisation rather than a
named lemma.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING**: Phase 4b found the `ℤ/ℚ` form strictly narrower than the
    arbitrary-base literature standard.
  - **MODERN-IDIOM (Bourbaki 2.0)**: Phase 4c row 5 — base ring `ℤ`/field `ℚ` weaken to general
    `R`/`K = Frac R`, the contemporary mathlib idiom (and exactly how mathlib already states `Φ`/`ΨSq`).

**Proposed restatement** (already proved in-project as `PID.x_coord_nsmul_eq`; rename for upstream):

```lean
-- to live near Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/ (a new file, e.g.
-- .../DivisionPolynomial/Point.lean, that may import Affine/Jacobian Point), namespace WeierstrassCurve
theorem x'_mul_ΨSq_eval_eq_Φ_eval   -- name TBD with reviewer
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R)
    {x y : K} (hns : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : K} (hns' : (W.map (algebraMap R K)).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
    x' * ((W.map (algebraMap R K)).ΨSq n).eval x = ((W.map (algebraMap R K)).Φ n).eval x := by
  sorry -- already proved as LutzNagell.PID.x_coord_nsmul_eq; transcribe + adjust namespacing
```

Estimated cost of regeneralisation: **CHEAP** — the general proof already exists
(`PIDIntegralMultiple.lean:44–62`); the work is naming + placement + de-forking the EDS/DivPoly copy.
(Note: EXPENSIVE would not downgrade the verdict anyway; here it is not even expensive.)

Mathlib downstream this enables:
  - The first bridge from `WeierstrassCurve.Φ`/`ΨSq` to the group law `n • P` — foundation for
    torsion bounds, the Nagell–Lutz theorem, reduction-mod-`p` injectivity, and point-indexed
    elliptic divisibility sequences.
  - Composes immediately with mathlib's existing `Φ`/`ΨSq` recurrence and degree API
    (`Degree.lean`) to compute torsion x-coordinates.

**Caveat / blockers to flag at PR time** (these do not change the bucket, but the upstreamer must
handle them):
  1. The proof depends on several **project-local** bridge lemmas not yet in mathlib —
     `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq` (EvalBridge.lean), the `Jacobian.smulEval`
     machinery (`ZSMul.lean`), and `Jacobian.Point.toAffineAddEquiv`. Upstreaming `x_coord_nsmul_eq`
     means upstreaming that dependency cone first (some of it — e.g. `evalEval_Ψ_sq_eq_eval_ΨSq` —
     was separately assessed NO-composable, i.e. inline-from-mathlib). This is a multi-PR effort.
  2. The project currently **forks** `DivisionPolynomial.lean` and `EllipticDivisibilitySequence.lean`
     (to dodge a `normEDS`/`complEDS` name clash). Upstreaming must use mathlib's originals, not the
     fork — i.e. de-duplicate against `Mathlib.…DivisionPolynomial.Basic` first.

Pre-PR checklist before opening:
  - [ ] `/generalise LutzNagell.PID.x_coord_nsmul_eq` — confirm the typeclass cluster is minimal
        (the `omit` hints `IsDomain`/`UFD`/`IsFractionRing` may be further removable for the bare
        identity) and tension against the arbitrary-`CommRing` literature form.
  - [ ] De-fork: re-prove against `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
        and `Mathlib.NumberTheory.EllipticDivisibilitySequence` (drop the `LutzNagell.*` copies).
  - [ ] Upstream the bridge dependency cone (`evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`,
        `Jacobian.smulEval`) or inline each from mathlib where it was found composable.
  - [ ] `/cleanup` the resulting file; pick a reviewer from recent
        `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (David Angdinata authors the DivPoly files).

Next action: run `/generalise LutzNagell.PID.x_coord_nsmul_eq` (tension against the
arbitrary-base literature form + the modern-idiom form), then plan the de-fork + dependency-cone
upstream as a small PR series. The `ℤ/ℚ` `x_coord_nsmul_eq_general` itself is **not** upstreamed —
it becomes (or stays) a project-local specialisation of the general lemma.

---

## Next step

Run `/generalise LutzNagell.PID.x_coord_nsmul_eq` (the general parent, not the `ℤ/ℚ` wrapper)
before any mathlib PR; then de-fork against mathlib's `DivisionPolynomial`/`EllipticDivisibilitySequence`
and upstream the general lemma + its bridge dependency cone.
