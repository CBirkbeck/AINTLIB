## /mathlibable report — `WeierstrassCurve.Universal.Affine.smulY_one`

### Baseline (Phase 0)
- lake build:               ✓ assumed clean (build stale locally; reasoned from source — per task instructions)
- decl `WeierstrassCurve.Universal.Affine.smulY_one`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:174`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval` — `n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coords for an integer `n` and a nonsingular affine point `P` on a Weierstrass curve over a field, via the universal curve + division polynomials + elliptic divisibility sequences.

Exact source line:
```lean
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]
```
Qualified name **VERIFIED**: file has `namespace WeierstrassCurve` → `namespace Universal` (ZSMul.lean:86) → `namespace Affine` (ZSMul.lean:157), so the parsed `WeierstrassCurve.Universal.Affine.smulY_one` is correct.

Note: this lemma is **duplicated verbatim** at `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:249` (the HasseWeil project forks the same Junyan-Xu universal-curve development). Both copies are project-local; neither is in mathlib.

---

### Statement (Phase 1)

`smulY_one` states that the Y-coordinate function of the point `1 • (X,Y)` on the *universal* pointed elliptic curve equals the formal variable `Y`.

Here `smulY n : Universal.Field` is defined (ZSMul.lean:168) as `polyToField (curve.ω n) / (ψᵤ n) ^ 3` — the rational function `ωₙ/ψₙ³`, the candidate Y-coordinate of `n • (X,Y)`. The lemma is the **`n = 1` base case**: since the universal `ω₁ = Y` (project lemma `ω_one`, DivisionPolynomialOmega.lean:96) and `ψ₁ = 1` (project lemma `ψ_one`, DivisionPolynomial.lean:334), we get `smulY 1 = Y / 1³ = Y`.

The objects involved are **entirely project-local**:
- `Universal.Field := FractionRing Universal.Ring`, `Universal.Ring := curve.CoordinateRing`, `Poly := (MvPolynomial Coeff ℤ)[X][Y]` (Universal.lean:94–99).
- `polyToField : Poly →+* Universal.Field` (Universal.lean:108) — the map from the 7-variable polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]` to the universal field.
- `Y` = `Polynomial.Y`, the formal bivariate `Y` variable.
- `smulY`, `ψᵤ` (= `polyToField (curve.ψ n)`) — project definitions.

Variables / typeclasses (Lean side): none beyond the fixed universal setup (this is a closed statement about specific universal objects; `n` is specialised to `1`).
Hypotheses (Lean side): none.
Conclusion (math): the Y-coordinate of `1·P = P` for the universal point `P = (X,Y)` is `Y`. (Trivial base case of `[m]P = (φₘ/ψₘ², ωₘ/ψₘ³)`.)
Conclusion (Lean): `smulY 1 = polyToField Y`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A base-case `@[simp]` glue lemma (`n=1`) about a bespoke project-local rational-function definition; not a named theorem, not a new structure, not a `## Main results` entry. It is an internal computation step toward the main result `zsmul_eq_smulEval`.

### One-line check (Phase 2b)

Body line count: this is a `lemma` (proof `by simp [smulY, ψᵤ]`), not a `def`/`abbrev`/`structure`. The one-liner exemption framework targets one-line **definitions**; for a lemma it is n/a.

One-liner verdict: **n/a (kind is lemma, not def)**. Recorded for narrative: the lemma is a one-line `simp`-glue base case (proof is a single `simp` unfolding `smulY` + `ψᵤ` and applying `ω_one`/`ψ_one`), which is itself a strong "do-not-upstream-standalone" signal — it is the kind of definitional unfolding that lives inline in a proof development, not a reusable mathlib API lemma.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | EC mult-by-n via division polynomials, `φₙ/ψₙ²`, `ωₙ/ψₙ³`                                              | yes  | `n(x,y) = (φₙ/ψₙ², ωₙ/ψₙ³)`       | Standard; multiple arXiv refs (1108.3051, 1103.4560, 2102.07573) and Silverman |
|  2 | WebSearch (general form / base)  | `"division polynomial" … "psi_1 = 1" "omega_1"` base case, Silverman                                    | yes  | `ψ₀=0, ψ₁=1, ψ₂=2y`; `[1]P=(x,y)` | The `m=1` base case is `[1]P=(x,y)`; entirely standard, trivial |
|  3 | WebSearch (named-after/aliases)  | division polynomials / elliptic divisibility sequences base case                                       | yes  | same; "EDS" framing               | The `smulY` object = `ωₙ/ψₙ³`; at `n=1` reduces to `y`. No special name for the base case |
|  4 | ChatGPT MCP                      | (not run — MCP flagged down in this environment; channels 1–3 + mathlib source already decisive)        | n/a  | —                                 | The math content is unambiguous and standard; fallback channels suffice |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "smulY"/"division polynomial"                                   | n/a  | (no references dir present for NagellLutz) | dir absent — recorded n/a |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                                | n/a  | not an nLab-style categorical concept | concrete arithmetic-geometry formula; nLab has no entry of relevance |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not categorical                   | no higher-categorical content |
|  8 | Stacks Project (if alg geom)     | division polynomial / multiplication-by-n on elliptic curve                                             | n/a  | not a Stacks topic (no explicit division-polynomial coordinate formulas) | Stacks is scheme-theoretic; no `ωₙ/ψₙ³` base-case lemma |
|  9 | MathOverflow / Math.SE           | division polynomials base case ψ₁=1, ω₁                                                                 | yes  | confirms `ψ₁=1`, `[1]P=(x,y)`     | universally treated as trivial base case |
| 10 | recent arXiv (last 5 years)      | division polynomials / EDS recurrence                                                                   | yes  | 2102.07573 (EDS recurrence)       | confirms the recursive setup + `ψ₁=1` base value |

### Literature summary (Phase 3)

Concept identified as: the **`m=1` base case of the multiplication-by-`m` formula `[m]P = (φₘ/ψₘ², ωₘ/ψₘ³)`** for elliptic curves via **division polynomials / elliptic divisibility sequences**.
Sources agree on the standard form: **yes** — `ψ₀=0, ψ₁=1, ψ₂=2y`; `θₘ=φₘ=xψₘ²−ψₘ₋₁ψₘ₊₁`; `ωₘ=ψ₂ₘ/(2ψₘ)`; and `[1]P=(x,y)` is the trivial base case.
Most general standard form: the full formula over a general Weierstrass curve (mathlib already has `ψ`, `φ`, `ω` as `WeierstrassCurve.Ψ/Φ/Ω`-style division polynomials in `DivisionPolynomial/Basic.lean`).
Generality dimensions where the literature varies: short-Weierstrass `y²=x³+ax+b` (textbook) vs general Weierstrass `a₁..a₆` (mathlib + this project). This project uses the **fully general** Weierstrass form via the universal curve `ℤ[A₁..A₆,X,Y]/⟨P⟩` — the maximally general setting.
Disagreement with the literature: **none**. The math is standard and trivial at `n=1`. The novelty (such as it is) is purely *formalization-structural*: `smulY` is a bespoke Lean rational-function object on a bespoke universal field, and `smulY_one` is the Lean unfolding of its base case — not a mathematical statement the literature would name.

---

### Generality analysis — `WeierstrassCurve.Universal.Affine.smulY_one`

Literature-standard form (from Phase 3): `[1]P = (x,y)`, i.e. the Y-coordinate of `1•P` is `y`; the maximally general home is "for any Weierstrass curve over any commutative ring/field, `1 • P = P`".

| # | Parameter / hypothesis             | Current Lean form                       | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------|-----------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | the curve                          | fixed `Universal.pointedCurve` over `Universal.Field` | arbitrary Weierstrass curve / `W.Point` | N/A — by design specialised | The whole point of the universal curve is to be specialised *later* (`ringEval`/`polyEval`) to every `W` over every field. Generalising *this lemma* would mean restating it about an abstract `W.Point`, which is exactly the project's downstream goal `zsmul_eq_smulEval`, not this base case |
| 2 | the multiplier `n`                 | specialised to `1`                       | general `m`                       | n/a (it is the base case) | This lemma *is* the `n=1` base case; it is not meant to generalise in `n` (the `n`-general statement is `smulX_eq`, `smulY_sub_negY`, etc.) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *in the only dimension that matters* — it is stated on the universal curve, which is the most general Weierstrass setting and from which every concrete case is obtained by specialisation. As a *standalone mathlib candidate*, however, it is a degenerate base case with nothing to generalise.
Number of weakening opportunities found: 0 (meaningful ones).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | bundled-hypotheses → typeclasses/instances?                                                | no       | —                      | already instance-based (the universal `IsElliptic` instance, `FractionRing`) |
|  2 | sequences/metric → filters/topology?                                                       | no       | —                      | no topology; pure algebra |
|  3 | construction → universal-property class?                                                   | no       | —                      | `smulY` is a concrete rational function; the universal *curve* already is the universal property here |
|  4 | set+closure-predicate → bundled substructure?                                              | no       | —                      | n/a |
|  5 | vector-space/field-specific → modules/(semi)ring?                                          | no       | —                      | already over the universal field by necessity (needs `FractionRing`); `smulY` genuinely needs a field (division) |
|  6 | 1-categorical → higher-categorical?                                                        | no       | —                      | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary group/monoid?                                             | no       | —                      | the index is `ℤ` (the EC group); `n=1` is the unit; nothing to abstract |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
Reason: This is a one-line `simp` base-case unfolding of a project-internal rational-function definition; there is no contemporary mathlib reformulation that would be an organisational improvement — it is glue, not API.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is **lemma** (not `def`/`class`/`instance`). No definitional equalities or typeclass-search paths introduced.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulY_one`

[A] Lean-Finder       "smulY one", "Y-coordinate of 1 • P universal curve"            n/a (index offline locally) — substituted by direct mathlib-source grep below
[B] Loogle            `WeierstrassCurve.Universal.Affine.smulY`, `?a = polyToField _` n/a (index offline locally) — `smulY`/`polyToField` symbols do not exist in mathlib (grep-confirmed), so any type-pattern query is vacuous
[C] LeanSearch        "first multiple of point equals point division polynomial"       n/a (index offline locally) — superseded by source grep
[D] Grep mathlib src  `smulY`, `smulX`, `polyToField`, `namespace Universal` (for WeierstrassCurve) over `.lake/packages/mathlib/Mathlib/` | **no hits** — `smulY`/`smulX`/`polyToField` appear nowhere; the only `namespace Universal` matches are `UniversallyOpen.lean` and `Lie/UniversalEnveloping.lean` (unrelated). There is **no universal-elliptic-curve development in mathlib at all** |
[E] Name pattern      grep for `smulY_one`, `smulY`, universal pointed curve            **no hits in mathlib**; only hits are the two project copies (NagellLutz, HasseWeil)

Searched for both:
  - the user's current form (`smulY 1 = polyToField Y`) — not in mathlib (the objects don't exist there).
  - the literature-standard form ("`1 • P = P`" / coordinate `= y` for an EC point) — mathlib **does** have `one_smul` via the `AddCommGroup W.Point` instance (`Affine/Point.lean:770`, `Jacobian/Point.lean:588`), but mathlib has **no** lemma expressing any `n • P` (let alone `1 • P`) through `ωₙ/ψₙ³`/division-polynomial coordinates. Mathlib has the division polynomials (`DivisionPolynomial/Basic.lean`, `EllipticDivisibilitySequence.lean`) and the group law, but **not the bridge** `n•P = (φₙ/ψₙ², ωₙ/ψₙ³)` — that bridge is exactly what this project is building and has not yet upstreamed.

Concluded: **not in mathlib** (source grep exhausted, plus the literature-standard `1•P=P` coordinate-via-division-polynomial form). The supporting objects `smulY`/`polyToField`/`Universal` curve are themselves absent from mathlib.

---

### Call sites — `WeierstrassCurve.Universal.Affine.smulY_one`

Internal use count (within NagellLutz, excluding the declaring file ZSMul.lean): **0**.
Within the declaring file ZSMul.lean, it is used at lines 248, 281, 351 (and the parallel `smulX_one` at 246/319/352) — i.e. it is a `@[simp]`/rewrite helper consumed locally inside the multiplication-formula proof (`slopeOne_eq_*`, the `n=1` base case of `zsmul_point_eq_smulX_smulY`).
External-to-file callers: **0 distinct files** (within NagellLutz). The HasseWeil copy is an independent fork, not a cross-import.

| Caller file:line                                  | Usage pattern (one-line excerpt) |
|---------------------------------------------------|----------------------------------|
| ZSMul.lean:248 (same file)                        | `simp only [smulX_one, smulY_one, pointedCurve_a₁, …]` |
| ZSMul.lean:281 (same file)                        | `rw [… smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]` |
| ZSMul.lean:351 (same file)                        | `simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]` |

Inline-derivation grep (re-derived elsewhere without using `smulY_one`?): (none found) — but note the duplicate *definition+lemma* in HasseWeil/Auxiliary/DivisionPolynomial.lean:249, which is a whole-development fork, not an inline re-derivation.

Signal: **K = 0 external uses**; used only inside its own file as a local `simp` base case. Per the Phase 6.0.1 table, "K = 1 internal use / local-only" leans toward NO-composable. Here it is genuinely just a definitional unfolding step.

---

### Composition check (Phase 6)

Can `smulY_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: From mathlib alone — **fails**. The statement mentions `smulY` and `polyToField`, which are project-local; mathlib cannot even state it. So "compose from mathlib" is vacuously impossible *as written*.

Attempt 2 (the honest framing — compose from the *project's own* immediate API): `smulY_one` follows in essentially one `simp` step from project lemmas:
  - `smulY` (def, ZSMul.lean:168) : `smulY 1 = polyToField (curve.ω 1) / (ψᵤ 1) ^ 3`
  - `ω_one` (DivisionPolynomialOmega.lean:96) : `curve.ω 1 = Y`
  - `ψ_one` (DivisionPolynomial.lean:334) : `curve.ψ 1 = 1` ⇒ `ψᵤ 1 = polyToField 1 = 1`
  Then `polyToField Y / 1³ = polyToField Y`. This is precisely what `by simp [smulY, ψᵤ]` does.
  - Decls used: project `smulY`, `ψᵤ`, `ω_one`, `ψ_one`. Result: succeeds in 1 `simp` line.
  - Notes: the entire content is unfolding a definition + two already-existing base-case values. No mathematical step.

Conclusion: **COMPOSABLE** (a 1-line `simp` from the project's own definitions; and *trivially/vacuously* not-from-mathlib because the objects are project-local). This is a glue lemma, not a contribution.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulY_one`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the statement is the trivial `n=1` base case of the standard `[m]P=(φₘ/ψₘ²,ωₘ/ψₘ³)` formula; `ψ₁=1`, `[1]P=(x,y)`. No literature names a standalone "base case" lemma.
- Generality analysis (Phase 4): nothing meaningful to generalise; no modern-idiom improvement (Phase 4c all "no").
- Mathlib search (Phase 5): **not in mathlib**; moreover the objects `smulY`/`polyToField`/universal curve are absent from mathlib entirely. Mathlib has `one_smul` on `W.Point` and the division polynomials, but **not** the `n•P = (φₙ/ψₙ²,ωₙ/ψₙ³)` bridge.
- Composition check (Phase 6): **COMPOSABLE** — a 1-line `simp [smulY, ψᵤ]` from the project's own `ω_one`/`ψ_one`.

**Rationale:**

`smulY_one` is a one-line `@[simp]` *glue lemma* — the `n=1` base-case unfolding of the project-local rational function `smulY n = ωₙ/ψₙ³` on the bespoke "universal pointed elliptic curve" `Frac(ℤ[A₁..A₆,X,Y]/⟨P⟩)`. Its proof is a pure definitional unfolding (`smulY 1 = ω₁/ψ₁³ = Y/1 = Y`) using two base values (`ω_one`, `ψ_one`) the project already has. Mathematically it is the trivial fact "`1·P = P`, whose Y-coordinate is `y`", at the `n=1` corner of a standard textbook formula — nothing the literature would isolate as a named result.

It is correctly **not** in mathlib, but it should **not** be added: the object it is about (`smulY`) is not a mathlib concept. `smulY`, `smulX`, `polyToField`, and the entire `Universal` elliptic-curve construction are an **in-progress, not-yet-upstreamed development** (Junyan Xu's "multiplication-by-`n` via division polynomials", here forked into both NagellLutz and HasseWeil — note the verbatim duplicate at HasseWeil/Auxiliary/DivisionPolynomial.lean:249, and the module docstring's own statement that Universal.lean provides "lemmas missing from the released mathlib"). The genuinely mathlib-worthy artifact of this development is the **final** bridge theorem `WeierstrassCurve.zsmul_eq_smulEval` (`n • P = (φₙ:ωₙ:ψₙ)` in Jacobian coordinates), **not** an internal base-case `simp` step toward it. If/when the universal-curve development is upstreamed as a unit, `smulY_one` would ride along as a private/local helper inside it — never as a standalone PR.

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks for the *mathematical content* — `one_smul` on the `AddCommGroup W.Point` instance, and the division polynomials `ψ`/`φ`/`ω` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`). But the *lemma as written* is about project-only objects, so it composes from the **project's** own primitives, not mathlib's:

  Mathlib building blocks (for the underlying math): `WeierstrassCurve.Affine.Point` `one_smul` (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:770`), `WeierstrassCurve.preΨ_one`/`normEDS_one` (`DivisionPolynomial/Basic.lean:206`, `EllipticDivisibilitySequence.lean:302`).
  Project building blocks (what actually discharges it): `Universal.Affine.smulY` (def), `ψᵤ` (def), `Universal.ω_one`, `Universal.ψ_one`.

  Composition sketch (≤3 lines, the existing proof):
  ```lean
  example : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]   -- unfolds to ω₁/ψ₁³ = Y/1; uses ω_one, ψ_one
  ```

  Call sites in the project (from Phase 6.0): **K = 0** external; 3 internal uses inside ZSMul.lean only (lines 248, 281, 351).

  Refactor plan: **no refactor needed and no mathlib PR.** Keep `smulY_one` exactly where it is — a local `@[simp]` helper inside the universal-curve development. Do **not** open a standalone mathlib PR for it. The two existing copies (NagellLutz + HasseWeil) are the real cleanup signal: when the universal-curve machinery is consolidated (`Common/`) or upstreamed, deduplicate the two `smulY`/`smulX` definitions and their base-case lemmas (`smulX_one`, `smulY_one`, …) into a single shared module; this lemma then survives as a private helper of that module, not as an independent declaration.

  Next action: **none for mathlib.** (Optional project hygiene: file a *dedup* cleanup ticket to merge the duplicated NagellLutz/HasseWeil `Universal.Affine.smul{X,Y}` development into `Common/`, where `smulY_one` rides along.)

---

## Next step

No mathlib PR. `smulY_one` is a project-internal base-case `simp`-glue lemma about a not-yet-upstreamed universal-curve construction; it is not in mathlib (the objects don't exist there) and should not be added standalone. The mathlib-worthy target of this development is the final `WeierstrassCurve.zsmul_eq_smulEval` bridge, not this step. Optional: dedup the duplicated NagellLutz/HasseWeil `smul{X,Y}` development into `Common/`.
