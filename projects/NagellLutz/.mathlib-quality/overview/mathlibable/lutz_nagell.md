# /mathlibable report — `LutzNagell.LutzNagellTheorem.lutz_nagell`

## Verdict: **YES-but-generalise-first** (reason: LITERATURE-WEAKENING)

One-line: The classical Nagell–Lutz theorem is genuinely missing from mathlib, but
this is the *short-Weierstrass specialisation*. The project already proves the
general-Weierstrass form (`lutz_nagell_integrality_general` +
`lutz_nagell_discriminant_general`); that general pair is the right mathlib target,
with `lutz_nagell` shipped as the short-form corollary.

---

### Baseline (Phase 0)
- lake build:               ✓ clean — `Build completed successfully (2071 jobs)` (only `unusedVariables`/`unusedSectionVars` style warnings; the earlier "stale" caution did not materialise)
- decl `LutzNagell.LutzNagellTheorem.lutz_nagell`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/Main.lean:66`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The Lutz–Nagell Theorem" — Theorem 1.1 of Alpöge, *Nagell-Lutz, quickly*; torsion points of `y²=x³+Ax+B/ℚ` are integral with `y²∣Δ`.

---

### Statement (Phase 1)

`lutz_nagell` is the **classical Nagell–Lutz theorem** in short-Weierstrass form:

> Let `A, B ∈ ℤ` with `Δ_{A,B} := -16·(4A³ + 27B²) ≠ 0`, and let `E/ℚ` be the
> elliptic curve `y² = x³ + Ax + B`. If `(x, y)` is a non-identity rational point
> of finite order on `E`, then `x, y ∈ ℤ`, and either `y = 0` or `y² ∣ Δ_{A,B}`.

Variables / typeclasses (Lean side):
- `A B : ℤ` — the (integral) short-Weierstrass coefficients.
- `shortCurveZ A B : WeierstrassCurve ℤ` = `{a₁=0,a₂=0,a₃=0,a₄=A,a₆=B}`; `shortCurveQ A B` is its base change along `algebraMap ℤ ℚ`.

Hypotheses (Lean side):
- `hΔ : (shortCurveZ A B).Δ ≠ 0` — nonsingularity (elliptic, not nodal/cuspidal). (Note: linter flags `hΔ` as unreferenced in `lutz_nagell` itself — it is threaded into the called lemmas; harmless.)
- `hpt : (shortCurveQ A B).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular ℚ-point.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point has finite additive order (is torsion).

Conclusion (math): `x,y ∈ ℤ` and (`y=0` or `y²∣Δ`).
Conclusion (Lean): `∃ (x₀ y₀ : ℤ), (x₀:ℚ)=x ∧ (y₀:ℚ)=y ∧ (y₀=0 ∨ y₀^2 ∣ (shortCurveZ A B).Δ)`.

Proof body: a 2-line assembly — `obtain` the integrality witnesses from
`lutz_nagell_integrality`, then pair with `lutz_nagell_discriminant`. Both of
those are themselves thin short-form wrappers over the project's `*_general`
theorems. So `lutz_nagell` is the project's top-level *presentation* statement.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a theorem named after people (Nagell, Lutz) and the project's headline
main result (Theorem 1.1 of the cited paper). Guaranteed to be in the literature.

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → n/a. (The body is a 2-line
proof assembling two lemmas; not a one-line definition.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell-Lutz torsion integral coordinates discriminant divisibility                             | yes  | `y²=x³+Ax+B`, P torsion ⇒ x,y∈ℤ and (y=0 or y²∣(4A³+27B²))                          | Wikipedia, numberanalytics, Galperin REU all agree on the short form |
|  2 | WebSearch (general form)         | "Nagell-Lutz" most general form number field elliptic curve                                    | yes  | general Weierstrass `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆/ℤ`; over ℚ either integral or order-2 with x=m/4,y=n/8; generalises to number fields | Wikipedia "generalizes to arbitrary number fields and more general cubic equations" |
|  3 | WebSearch (named-after / proof)  | Nagell-Lutz proof Silverman Tate division polynomial elliptic divisibility integrality          | yes  | Silverman-Tate pp.47-56 (y²∣Δ left as exercise); EDS/division-polynomial proof = Alpöge's method | matches the project's machinery exactly |
|  4 | ChatGPT MCP                      | full standard-form + generality + "is it in mathlib" question                                  | n/a  | —                                                                                    | **MCP DOWN** (Codex `exec` error). Compensated by extra WebSearch + WebFetch + nLab (≥4 independent channels). |
|  5 | Local references                 | `.mathlib-quality/references/` grep                                                            | n/a  | (directory absent in this project)                                                   | only `overview/` exists under `.mathlib-quality/`; no refs dir |
|  6 | nLab                             | torsion points of an elliptic curve                                                            | yes  | Nagell-Lutz stated for `Y²=X³+AX+B/ℤ`: β²∣(4A³+27B²); notes integrality is model-dependent | ncatlab.org/nlab/show/torsion+points+of+an+elliptic+curve |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | —                                                                                    | not a categorical concept (concrete Diophantine statement) |
|  8 | Stacks Project (alg geom)        | Nagell-Lutz / integral torsion Weierstrass                                                     | n/a  | —                                                                                    | Stacks covers schemes/general AG; this arithmetic-of-elliptic-curves result is out of its scope |
|  9 | MathOverflow / Math.SE           | (covered via WebSearch aggregator) torsion integral y²∣disc generality                          | yes  | confirms y∣D ⇒ y²∣D; theorem not iff; general-Weierstrass denominators bounded by 4,8 | Algebra Teahouse, Northeastern/Dummit lecture #19, surya-teja blog |
| 10 | recent arXiv (last 5y)           | Nagell-Lutz imaginary quadratic / global fields                                                | yes  | arXiv:2509.07524 (imag. quadratic, class no. 1): x,y∈𝒪_K, y=0 or y²∣(4A³+27B²); Springer manuscripta math "global field" version | active generalisation frontier → the canonical statement is the general one |

Protocol pass check: WebSearch ran 3 distinct generality levels (✓ #1,#2,#3);
ChatGPT MCP attempted but down, compensated by an extra independent channel (nLab
#6) per the fallback rule; local refs checked (absent → n/a ✓); nLab checked (✓);
nCatLab/Stacks recorded n/a with reasons (✓); MathOverflow/arXiv checked (✓ #9,#10).

### Literature summary (Phase 3)

Concept identified as: **the Nagell–Lutz theorem** (a.k.a. Lutz–Nagell), classical 1935/1937.
Sources agree on the standard form: **yes** — the short form `y²=x³+Ax+B` with
`x,y∈ℤ` and `y=0 ∨ y²∣(4A³+27B²)` is the universally-quoted statement.
Most general standard form: **general integral Weierstrass model**
`y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆` with `aᵢ∈ℤ`: a torsion point either has integral
coordinates, or has order 2 with `x∈¼ℤ, y∈⅛ℤ`; the divisibility is against the
curve discriminant. This further generalises to rings of integers of number fields
(active research, arXiv:2509.07524; Springer "global field").
Generality dimensions where the literature varies:
  - Curve model: short `y²=x³+Ax+B` ⟶ **general Weierstrass** (the maximal classical form).
  - Base: ℚ/ℤ ⟶ number field/𝒪_K (research-level; NOT yet a "settled textbook" target for mathlib).
  - Divisibility strength: `y∣D` (Wikipedia/nLab, stronger) vs `y²∣D` (the project's, weaker but standard, "Silverman-Tate exercise" form); and `D=4A³+27B²` vs `D=Δ=-16(4A³+27B²)`.
Disagreement with the literature: none — the project's form is a faithful, valid
(slightly weaker on divisibility) special case of the standard statement.

---

### Generality analysis — `lutz_nagell`

Literature-standard form (Phase 3): general integral Weierstrass model over ℤ
(short form is the `a₁=a₂=a₃=0` slice).

| # | Parameter / hypothesis                          | Current Lean form                                  | Literature-standard form                          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|----------------------------------------------------|----------------------------------------------------|---------------------|---------------------------------|
| 1 | curve `shortCurveZ A B` (`a₁=a₂=a₃=0`)          | short Weierstrass `y²=x³+Ax+B`                      | general Weierstrass `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆`    | **yes**             | The project ALREADY has the general form: `lutz_nagell_integrality_general` (GeneralMain.lean:110) handles arbitrary `W : WeierstrassCurve ℤ`; `lutz_nagell` is literally derived from it by specialising `a₁=a₃=0`. |
| 2 | conclusion: full integrality `x,y∈ℤ`            | always integral                                    | integral OR (order 2 ∧ `4x,8y∈ℤ`)                  | n/a (this is *stronger*, correct for short form) | For short Weierstrass the order-2 branch collapses (ψ₂=2y ⇒ y=0 ⇒ x a root of monic `X³+AX+B`), so full integrality is the *correct* short-form conclusion. The general theorem keeps the `¼ℤ,⅛ℤ` branch. |
| 3 | divisibility `y²∣Δ`                             | `y₀²∣(shortCurveZ A B).Δ`                          | `y∣D` / `y²∣(4A³+27B²)`                             | (orthogonal)        | Project's `lutz_nagell_discriminant_general` (GeneralDiscriminant.lean:187) gives the general-`W` divisibility `(2y)²∣…` (via `κ₀=ψ₂`); short form divides out the 4. |
| 4 | base ring ℚ/ℤ                                   | ℚ points, ℤ coefficients                            | number field / 𝒪_K (research)                       | yes, but EXPENSIVE/research | Out of scope for a first mathlib contribution; the ℚ/ℤ statement is the settled textbook one. Flag only. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: 1 primary (row 1 — short ⟶ general Weierstrass), already realised inside the project.
Proposed restatement (the target mathlib should receive): the project's existing
general pair, packaged as one theorem:

```lean
-- general-Weierstrass Nagell–Lutz (already proved in the project; bundle the two halves)
theorem nagellLutz_general (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {x y : ℚ} (hpt : (W.map (algebraMap ℤ ℚ)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    ((∃ x₀ y₀ : ℤ, (x₀:ℚ)=x ∧ (y₀:ℚ)=y) ∧ (some y₀-divisibility against W.Δ))
    ∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
        (∃ n : ℤ, (n:ℚ)=4*x) ∧ ∃ m : ℤ, (m:ℚ)=8*y) := …
```

Cost of restatement: **CHEAP** — no new mathematics. `lutz_nagell_integrality_general`
and `lutz_nagell_discriminant_general` are already proved sorry-free in the
project; the "generalise-first" work is repackaging + naming, then re-deriving
`lutz_nagell` as the short-form corollary (which the project already does).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                     | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                           | partial  | mathlib already has `WeierstrassCurve.IsIntegral R W` and `EllipticCurve` — state against those rather than a bespoke `shortCurveZ` | composes with `EllipticCurve.Reduction`, `integralModel`, `EllipticCurve` API |
|  2 | sequences/metric → filters/topological?                                                       | no       | purely Diophantine/algebraic; no limit notion to filter-ise | — |
|  3 | construction → universal property?                                                            | no       | a divisibility/integrality *theorem*, nothing to characterise universally | — |
|  4 | set-with-closure-predicate → bundled substructure?                                            | no       | conclusion is about coordinates of a single point | — |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                         | partial  | The general statement is about a `WeierstrassCurve ℤ` and its base change to ℚ; the natural mathlib home is exactly that (ℤ→ℚ), not a weaker ring — Nagell-Lutz is intrinsically about the DVR/PID structure of ℤ_(p). True generalisation is to PID/number-field, which the project's `PID*` track explores. | mathlib `IsPrincipalIdealRing`/DVR valuation API |
|  6 | 1-categorical → higher-categorical?                                                           | no       | — | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group?                                              | partial  | base ℤ → 𝒪_K (number field) — but that is the *research* frontier (arXiv:2509.07524), not a settled mathlib target | future PR |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **partially** (use `WeierstrassCurve.IsIntegral`/`EllipticCurve`
typeclasses and state the general-Weierstrass form), but the dominant move is the
plain literature weakening of row 1 (short ⟶ general), not a categorical
reformulation.
  - Real mathematical improvement: the general-Weierstrass statement is strictly
    more applicable and is the form every textbook proves; the short form is its
    one-line corollary. This is organisation, not decoration.
  - The number-field / PID generalisation is real but EXPENSIVE/research-grade —
    flag for a *future* PR, do not gate this verdict on it.

(Phase 4.5 diamond/defeq risk: **n/a** — declaration kind is `theorem`.)

---

### Mathlib search-status: `LutzNagell.LutzNagellTheorem.lutz_nagell`

[A] Lean-Finder       n/a — MCP tool not exposed in this environment
[B] Loogle            n/a — MCP tool not exposed in this environment
[C] LeanSearch        n/a — MCP tool not exposed in this environment
[D] Grep mathlib src  `nagell`, `lutz`(+theorem), `torsion.*integ`, `Δ.*dvd`, `mordell`, `torsionSubgroup`, `integral.?model`, `IsOfFinAddOrder.*integ` over `Mathlib/NumberTheory` + `Mathlib/AlgebraicGeometry/EllipticCurve` — **no hits** for the theorem (the only `lutz` hits are author *Patrick Lutz* in Galois-theory files; `nagell` absent entirely as a decl)
[E] Name pattern      grep `def/theorem/lemma .*nagell` over all of Mathlib — **no hits**

Searched for both:
  - user's form (short Weierstrass integral torsion + `y²∣Δ`): not present.
  - literature-standard form (general Weierstrass integral torsion, denominator bounds, discriminant divisibility): not present.

What mathlib *does* have (the building blocks, not the result):
  - `WeierstrassCurve`, `EllipticCurve`, `Affine`/`Jacobian.Point` group law (`AlgebraicGeometry/EllipticCurve/*`)
  - `WeierstrassCurve.twoTorsionPolynomial` + `twoTorsionPolynomial_discr` (`Weierstrass.lean:305,308`)
  - `Mathlib.NumberTheory.EllipticDivisibilitySequence` (EDS axioms) and `DivisionPolynomial/{Basic,Degree}` (ψ_n)
  - `WeierstrassCurve.IsIntegral`, `integralModel`, `Reduction`, `IsGoodReduction` (`Reduction.lean`)
  - These are exactly the *tools* the project forks/extends to build the proof.

Concluded: **not in mathlib** (grep methods D+E exhausted over both the project's
form and the literature-standard general form; A/B/C tools unavailable here but
the source grep over the relevant trees is authoritative for existence). NB: the
project explicitly forks `DivisionPolynomial.*` and `EllipticDivisibilitySequence`
precisely because mathlib lacks the downstream torsion-integrality result.

---

### Call sites — `LutzNagell.LutzNagellTheorem.lutz_nagell`

Internal use count (excluding the declaring file `Main.lean`): **0**
External-to-file callers: **0** distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | `lutz_nagell` is the project's top-level presentation theorem; nothing downstream consumes it. |

Inline-derivation grep: the *workhorses* `lutz_nagell_integrality_general` /
`lutz_nagell_discriminant_general` (and the short wrappers `lutz_nagell_integrality`,
`lutz_nagell_discriminant`, `lutz_nagell_integrality_short`) are what the proof
chain actually uses; `lutz_nagell` only bundles the two short wrappers. So the
`K=0` here is the expected signature of a "headline" theorem, **not** dead code —
the mathematical content lives in the general theorems it specialises.

Interpretation: `K=0` for the *bundled short form* reinforces that the
contribution-worthy object is the **general** theorem (which IS used internally to
derive the short form), not this top-level wrapper. This pushes the verdict toward
"ship the general form" rather than "ship `lutz_nagell` verbatim".

---

### Composition check (Phase 6)

Can `lutz_nagell` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: integrality of torsion points directly from any mathlib lemma.
  - Mathlib decls available: `twoTorsionPolynomial`, EDS axioms, division polynomials, point group law.
  - Result: **fails** — mathlib has no lemma asserting torsion ⇒ integral coordinates, nor `y²∣Δ`. The proof needs p-adic valuation control on the formal group / EDS denominators across all primes (the entire `General*`/`PID*` machinery: ~15-20 project files).
  - Notes: this is a genuine theorem with a multi-page proof, not a composition.

Conclusion: **NOT-COMPOSABLE** (from mathlib). (It *is* a ≤2-call composition of
the project's OWN `*_general` lemmas — which is exactly why the right mathlib unit
is those general lemmas, packaged, with `lutz_nagell` as their corollary.)

---

## Verdict: `LutzNagell.LutzNagellTheorem.lutz_nagell`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz is a classical named theorem; the universally-quoted *standard* form is the **general Weierstrass** model over ℤ (short form is its slice). ≥4 channels (Wikipedia, nLab, Silverman-Tate, arXiv) concur.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — `lutz_nagell` is the `a₁=a₂=a₃=0` specialisation; the project already proves the general form (`lutz_nagell_integrality_general`, `lutz_nagell_discriminant_general`).
- Mathlib search (Phase 5): **not in mathlib** under either form; only the building blocks (EDS, division/2-torsion polynomials, integral models) are present.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (multi-file proof).

**Rationale:**

The Nagell–Lutz theorem is a flagship classical result that mathlib genuinely
lacks: a direct grep over `Mathlib/NumberTheory` and `Mathlib/AlgebraicGeometry/EllipticCurve`
finds the *machinery* (`twoTorsionPolynomial`, `EllipticDivisibilitySequence`,
`DivisionPolynomial.*`, `IsIntegral`/`integralModel`/`Reduction`) but **no**
statement that a rational torsion point is integral, and **no** discriminant-
divisibility result. The named gap is concrete: mathlib's elliptic-curve point
theory is purely formal (group law over an arbitrary base) and has never bridged
to the *arithmetic* fact that torsion forces integrality over ℤ — this is the
canonical first such bridge, and the project forks `DivisionPolynomial.*` /
`EllipticDivisibilitySequence` precisely because that bridge is missing upstream.

But `lutz_nagell` itself is the **short-Weierstrass corollary**: its 2-line proof
specialises the project's own `lutz_nagell_integrality_general` (general
Weierstrass `y²+a₁xy+a₃y=…`, GeneralMain.lean:110) and
`lutz_nagell_discriminant_general` (GeneralDiscriminant.lean:187). The literature
(Wikipedia, nLab, Silverman) states Nagell–Lutz for the general integral
Weierstrass model — over ℚ a torsion point is either integral or has order 2 with
`x∈¼ℤ, y∈⅛ℤ` — and mathlib's iron rule is to add the most general settled form.
Since the general form is already proved here at **CHEAP** cost (it is the source,
not the consequence, of the short form) and has `K≥1` internal uses while the
bundled `lutz_nagell` has `K=0`, the correct mathlib contribution is the
**general-Weierstrass theorem**, with `lutz_nagell` retained as its named
short-form corollary. Shipping only the short form would be adding the
specialisation while leaving the more-general (and already-proven) statement on
the floor — exactly the YES-but-generalise-first pattern.

The number-field / 𝒪_K generalisation (arXiv:2509.07524; the project's `PID*`
track) is real but research-grade and EXPENSIVE; per the cost rule it does **not**
downgrade the verdict and is flagged only as a possible *future* PR, not a
precondition.

**Reason for the generalisation:** LITERATURE-WEAKENING (Phase 4b: STRICTLY
NARROWER — short Weierstrass is the `a₁=a₂=a₃=0` slice of the literature-standard
general Weierstrass form, which the project already proves).

**Proposed restatement** (bundle the project's two general theorems; both already
sorry-free):

```lean
theorem nagellLutz_general (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {x y : ℚ} (hpt : (W.map (algebraMap ℤ ℚ)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    ((∃ x₀ y₀ : ℤ, (x₀:ℚ)=x ∧ (y₀:ℚ)=y) ∧
        (y = 0 ∨ ∃ d : ℤ, /- y-coordinate -/ ... ∣ W.Δ))
    ∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
        (∃ n : ℤ, (n:ℚ) = 4 * x) ∧ ∃ m : ℤ, (m:ℚ) = 8 * y) := by
  -- assemble from lutz_nagell_integrality_general + lutz_nagell_discriminant_general
  sorry
-- then:  lutz_nagell  :=  the a₁=a₂=a₃=0 corollary (already in Main.lean)
```

Estimated cost of regeneralisation: **CHEAP** (repackaging + naming; the maths is
done). EXPENSIVE only if one also chases the number-field form — which is NOT
required for this verdict.

Mathlib downstream this enables:
  - Composes with `WeierstrassCurve.IsIntegral`, `integralModel`, `EllipticCurve.Reduction`, `twoTorsionPolynomial` — the general form applies to ANY integral model, not just `a₁=a₃=0`.
  - Foundational for any future `E(ℚ)_tors` *finiteness*/*computation* API (the standard application: torsion is a finite checkable set), which mathlib currently has no path to.

**Next action:** run `/generalise LutzNagell.LutzNagellTheorem.lutz_nagell`
(it will tension the short form against both the general-Weierstrass literature
form from Phase 3 and the project's already-proven `*_general` theorems). Then
package `nagellLutz_general` (+ the short corollary `lutz_nagell`) for a
`feat(NumberTheory/EllipticCurve): add Nagell–Lutz theorem` PR targeting
`Mathlib/NumberTheory/EllipticCurve/` (new file, e.g. `NagellLutz.lean`).
Pre-PR: `/cleanup` the full `General*` chain (it is the real content), pick a
reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits
(division-polynomial / EDS authors).

---

## Next step

Run `/generalise LutzNagell.LutzNagellTheorem.lutz_nagell`, then upstream the
**general-Weierstrass** theorem (`nagellLutz_general`, assembled from the project's
already-proven `lutz_nagell_integrality_general` + `lutz_nagell_discriminant_general`)
with `lutz_nagell` as the short-form corollary, to
`Mathlib/NumberTheory/EllipticCurve/NagellLutz.lean`.
