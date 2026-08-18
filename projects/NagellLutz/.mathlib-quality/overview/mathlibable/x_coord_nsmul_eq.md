# /mathlibable report — `LutzNagell.PID.x_coord_nsmul_eq`

Verdict: **YES-but-generalise-first** (reason: MODERN-IDIOM / index-generalisation — drop the
unused `R/K` base-change scaffolding and state directly over a single field).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); reasoned from source.
- decl `LutzNagell.PID.x_coord_nsmul_eq`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:39` (base name at line 39;
  signature spans 39–44; task pointed at line 42 which is the `{x' y' : K}` line — same decl).
- kind:                      theorem
- has sorry:                 no
- qualified name VERIFIED:   `LutzNagell.PID.x_coord_nsmul_eq` (namespace `LutzNagell.PID`, base name
  `x_coord_nsmul_eq`). The parsed guess in the task matches.
- module docstring summary:  "Integral multiple implies integral point (over UFDs)" — generalises the
  `ℤ/ℚ` track to a UFD `R` with fraction field `K`.

---

### Statement (Phase 1)

`x_coord_nsmul_eq` is a theorem stating the **cleared-denominator multiplication-by-`n` formula for the
x-coordinate** on a Weierstrass curve. Let `W : WeierstrassCurve R`, base-changed to its fraction field
`K` as `curveK R K W = W.map (algebraMap R K)`. Let `P = (x, y)` be a nonsingular affine point and
`P' = (x', y')` another nonsingular affine point with `n • P = P'` (`n ≠ 0`). Then

  `x' · ΨSqₙ(x) = Φₙ(x)`

where `Φₙ`, `ΨSqₙ` are mathlib's univariate division polynomials (`Φₙ ≡ φₙ`, `ΨSqₙ ≡ ψₙ²`). This is the
classical formula `x([n]P) = φₙ(x)/ψₙ²(x)` with denominators cleared, so it stays valid even when
`ψₙ(x) = 0`.

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` — but the **last two are
  `omit`ted** for this theorem (see the `omit [IsDomain R] [UniqueFactorizationMonoid R]
  [IsFractionRing R K]` on line 37). So `R` is used only as a `CommRing`.
- `K : Type*` `[Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]` — `IsFractionRing R K`
  is **also `omit`ted**. So effectively only `[Field K] [DecidableEq K] [Algebra R K]` are live.
- `W : WeierstrassCurve R`.

Hypotheses (Lean side):
- `hns : (curveK R K W).toAffine.Nonsingular x y` — `P=(x,y)` nonsingular.
- `_hn : n ≠ 0` (named with leading underscore; used only indirectly).
- `hns' : (curveK R K W).toAffine.Nonsingular x' y'` — `P'=(x',y')` nonsingular.
- `hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns'` — `n • P = P'`.

Conclusion (math): the x-coordinate of `n•P` satisfies `x' · ΨSqₙ(x) = Φₙ(x)`.
Conclusion (Lean): `x' * ((curveK R K W).ΨSq n).eval x = ((curveK R K W).Φ n).eval x`.

The proof is a genuine multi-step derivation: it lifts to Jacobian coordinates via
`Jacobian.Point.toAffineAddEquiv`, applies the project's big multiplication-formula theorem
`WeierstrassCurve.zsmul_eq_smulEval` (`n • P = ⟦smulEval⟧` in Jacobian coords, where `smulEval` is the
evaluation of `φₙ, ωₙ, ψₙ`), extracts the X-coordinate from the Jacobian equivalence
(`Jacobian.X_eq_of_equiv`), then converts the bivariate evaluations to the univariate `Φₙ`/`ΨSqₙ`
evaluations via the project's `EvalBridge` lemmas `evalEval_φ_eq_eval_Φ` and
`evalEval_Ψ_sq_eq_eval_ΨSq`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the geometric-meaning bridge of the division polynomials — the statement that mathlib's
`Φₙ`/`ΨSqₙ` actually compute the x-coordinate of `n•P` — a named, foundational result in the Silverman /
Washington / Sutherland literature. (Lit width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is theorem → n/a. (Body is a ~10-line tactic proof, not a one-liner.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "x-coordinate of nP equals phi_n/psi_n^2 multiplication by n formula" | yes | `x([n]P) = φₙ(x)/ψₙ²(x)`, `φₙ = x·ψₙ² − ψₙ₊₁ψₙ₋₁` | MIT 18.783 notes (Sutherland), arXiv:1103.4560, arXiv:1108.3051; φₙ monic deg n², ψₙ² deg n²−1 |
| 2 | WebSearch (general form) | "division polynomials over arbitrary commutative ring universal Weierstrass curve multiplication formula generality" | yes | `nP = (αₙ:βₙ:γₙ)`, homogeneous in `ℤ[a₁..a₆][x,y,z]`, valid for **all Weierstrass curves over any ring R** | arXiv:1303.4327 (homogeneous division polys); top hit is mathlib's own Degree.html |
| 3 | WebSearch (named-after / aliases) | "Silverman elliptic curves division polynomials multiplication-by-m map x([n]P)=phi_n/psi_n^2 standard" | yes | confirms #1; "x∘[m] and φₘ/ψₘ² are equal" | Silverman, Washington; Wikipedia "Division polynomials" |
| 4 | ChatGPT MCP | (3-part question on cleared-denom form / generality / mathlib significance) | n/a | — | MCP errored (Codex stdin failure, as task warned); compensated with extra web channels #2,#10 + Wikipedia fetch |
| 5 | Local references | no `.mathlib-quality/references/` PDFs in project (only `overview/`) | n/a | — | refs dir absent; PDFs are local-only per CLAUDE.md and not present |
| 6 | nLab | https://ncatlab.org/nlab/show/division+polynomial | no | — | 404 — no nLab page (not a categorical concept) |
| 7 | nCatLab | (same as #6) | n/a | — | not a higher-categorical concept |
| 8 | Stacks Project | division polynomials / elliptic curve mult-by-n | n/a | — | Stacks has no elliptic-curve-group-law / division-polynomial development |
| 9 | Wikipedia (fetch) | "Division polynomials" page | yes | `x([n]P) = φₙ(x)/ψₙ²(x)`, `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`, stated **over a general field K** | confirms exact form + φₙ definition + field-level generality |
| 10 | recent arXiv (last 5y) | multiplication polynomials over rings / local rings | yes | arXiv:2302.03650 "Multiplication polynomials for elliptic curves over finite local rings"; arXiv:1303.4327 over any ring | confirms generality trend toward arbitrary rings |

Protocol pass check: WebSearch ran 3 distinct generality levels (#1 specific, #2 most-general,
#3 named-after) ✓; ChatGPT MCP attempted, errored, compensated ✓; local refs checked (absent) ✓;
nLab checked (404) ✓; Stacks/nCatLab/MathOverflow/arXiv each addressed ✓.

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` formula for the x-coordinate via division
polynomials** — `x([n]P) = φₙ(x)/ψₙ²(x)`, `φₙ = x·ψₙ² − ψₙ₊₁ψₙ₋₁`.
Sources agree on the standard form: **yes** (Silverman, Washington, Sutherland 18.783, Wikipedia all
identical).
Most general standard form: over an **arbitrary commutative ring** `R` via universal/homogeneous
division polynomials (`nP = (αₙ:βₙ:γₙ)`, Sutherland / arXiv:1303.4327); over a **field** the affine
ratio form is the classical statement.
Generality dimensions where the literature varies:
  - base structure: field (classical) → Dedekind/local ring → **arbitrary commutative ring** (most
    general, modern).
  - form: rational-function `x = φₙ/ψₙ²` (needs `ψₙ(x) ≠ 0`) → **cleared-denominator** `x·ψₙ² = φₙ`
    (valid unconditionally, incl. n-torsion). **Our decl uses the cleared-denominator form** — the
    more robust one.
Disagreement with the literature: none. Our statement is the standard cleared-denominator form,
specialised to a fraction field `K` but **provably only needing `K` a field** (the `R`-side hypotheses
are `omit`ted).

---

### Generality analysis — `LutzNagell.PID.x_coord_nsmul_eq`

Literature-standard form: the cross-multiplied x-coordinate formula over a field (most generally over
any commutative ring, but the field statement is the natural mathlib home given mathlib's `Affine.Point`
group law currently lives over fields).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `R` + `[CommRing R]` and the whole `R → K` base-change `curveK R K W` | curve obtained by base-changing `W : WeierstrassCurve R` along `algebraMap R K` | a plain `W : WeierstrassCurve K` over a field | **yes** | The statement is purely about `curveK R K W : WeierstrassCurve K`. Nothing forces it to come from an `R`. State it for an arbitrary `W : WeierstrassCurve K`. |
| 2 | `[IsDomain R]`, `[UniqueFactorizationMonoid R]`, `[IsFractionRing R K]` | required in the `variable` block | not needed | **yes — already `omit`ted** | Line 37 `omit`s all three; they are genuinely unused here. |
| 3 | `[Field K] [DecidableEq K]` | field with decidable eq | field (DecidableEq is a Prop-irrelevant convenience) | partially | `Field K` is essential (mathlib's `Affine.Point` `AddCommGroup` is over a field). `DecidableEq K` is incidental. |
| 4 | `n ≠ 0` (`_hn`) | nonzero integer | `n ≠ 0` standard (n=0 gives `Φ₀=−1`, `ΨSq₀=0`, formula degenerate) | NO | genuinely needed. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (in the sense of carrying unnecessary
scaffolding, not weaker hypotheses on the math). The mathematical content is exactly the field-level
standard form, but it is *dressed* in an `R → K = Frac(R)` framing whose `R`-side hypotheses are all
`omit`ted.
Number of cleanups found: 1 substantive (drop `R`/base-change; state over `W : WeierstrassCurve K`).
Proposed restatement:

```lean
theorem x_coord_nsmul_eq {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y : K} (hns : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : K} (hns' : W.toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
    x' * (W.ΨSq n).eval x = (W.Φ n).eval x
```

Cost of restatement: **CHEAP** — the proof already factors through `curveK R K W` only as "some
`WeierstrassCurve K`"; replacing it by a bare `W : WeierstrassCurve K` is mechanical. (`DecidableEq K`
may be dischargeable via `Classical` or kept; it is not load-bearing for the statement.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream this enables |
|---|----------|----------|------------------------|-------------------------|
| 1 | bundled hyps → typeclasses? | no | — | hypotheses are already minimal/data, not "let X be a foo" preambles |
| 2 | sequences/metric → filters? | no | — | no limits/topology here |
| 3 | construction → universal property? | no | — | division polys already defined in mathlib; this is their *property* |
| 4 | set+closure → bundled substructure? | no | — | n/a |
| 5 | field/metric-specific → weaken typeclass? | **yes** | the result holds over any field `K`; the `R → Frac(R)` wrapper adds nothing. State over `W : WeierstrassCurve K`. (Further, over any comm-ring once mathlib has the ring-level group law — future.) | unifies with mathlib's `Affine.Point` API directly; no base-change indirection |
| 7 | concrete index `ℤ/ℚ`/`R` → general structure? | **yes** | drop the specific `R = `PID/UFD framing; the lemma's `n : ℤ` is already general, but the *base ring* `R` should disappear in favour of just the field `K` | the lemma stops being a NagellLutz-internal `curveK`-flavoured statement and becomes a clean `WeierstrassCurve K` API lemma mathlib can host next to `DivisionPolynomial/Basic` |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**.
  - Proposed mathlib-idiomatic restatement: the `WeierstrassCurve K` signature in Phase 4b above
    (no `R`, no `IsFractionRing`, no base change).
  - Cost: CHEAP.
  - Mathlib downstream this enables: a clean lemma stated directly in terms of mathlib's
    `WeierstrassCurve.Φ` / `WeierstrassCurve.ΨSq` and `WeierstrassCurve.Affine.Point` `n • _`, sitting
    naturally beside `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`. It is the
    first lemma connecting the (currently purely algebraic) division-polynomial defs to the group law.
  - Real mathematical improvement: removes incidental `Frac(R)` scaffolding so the result expresses its
    true content — a fact about division polynomials over a field — and composes with the rest of the
    elliptic-curve API without a base-change detour.

NOTE: this generalisation **depends on the supporting machinery** (`zsmul_eq_smulEval`, `smulEval`,
`EvalBridge`) also being phrased / available over a bare `WeierstrassCurve K`. In the project that
machinery (`ZSMul.lean`, `EvalBridge.lean`) is **already stated for `W : WeierstrassCurve F`, `[Field F]`**
(see `zsmul_eq_smulEval` at `ZSMul.lean:590` and the `EvalBridge` lemmas over `[Field F]`). So the
field-level restatement is genuinely within reach — but it is itself a sizeable upstreaming project (see
Phase 6 / Phase 7), because none of that machinery is in mathlib yet.

### Risk assessment (Phase 4.5)

n/a — declaration kind is theorem (no defeq/instance/diamond surface).

---

### Mathlib search-status: `LutzNagell.PID.x_coord_nsmul_eq`

[A] Lean-Finder       n/a (index tool not reachable in this env)
[B] Loogle            n/a (index tool not reachable; reasoned from direct mathlib source grep instead)
[C] LeanSearch        n/a (index tool not reachable)
[D] Grep mathlib src  searched `.lake/packages/mathlib/Mathlib/`:
      - `smulEval`, `zsmul_eq_smulEval`, `smul_eq_divisionPolynomial`, `x_coord.*nsmul`,
        `ΨSq.*eval`, `nsmul.*x_coord` → **NO HITS**
      - `Φ`, `ΨSq`, `ψ`, `φ` division-poly defs → found in
        `DivisionPolynomial/Basic.lean` (defs only; `ΨSq` L242, `Φ` L349)
      - who connects `DivisionPolynomial`/`EllipticDivisibilitySequence` to `Point`/`nsmul`/`zsmul`?
        Only `DivisionPolynomial/Degree.lean` imports `Basic` — and it is purely about *degrees*.
        `EllipticDivisibilitySequence.lean` has **no** `Point`/`Affine`/`Jacobian`/`nsmul` reference.
[E] Name pattern      `x_coord`, `xCoord`, `coordinate.*nsmul` under `AlgebraicGeometry/` → NO HITS.

Searched for both:
  - the user's current form (cleared-denominator `x'·ΨSqₙ = Φₙ`) → not in mathlib.
  - the literature-standard form (`x([n]P) = φₙ/ψₙ²`, and the general ring/Jacobian form) → not in
    mathlib in any guise. Mathlib has the **polynomials and their degrees only**; the **geometric
    meaning** (that they compute `n•P`) is entirely absent.

Concluded: **not in mathlib** (all reachable methods exhausted, plus the literature-standard form).
Mathlib has the building-block *definitions* `WeierstrassCurve.Φ` / `WeierstrassCurve.ΨSq` and the
`AddCommGroup W.Point` group law, but **no lemma linking them**.

---

### Call sites — `LutzNagell.PID.x_coord_nsmul_eq`

Internal use count: **2** (outside the declaring file).
External-to-file callers: 2 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `PIDMain.lean:369` | `have hcoord := x_coord_nsmul_eq W hpt (show (2:ℤ) ≠ 0 …) hns' (…)` — the `n=2` case of the PID Lutz-Nagell integrality argument |
| `GeneralIntegralMultiple.lean:43–49` | `theorem x_coord_nsmul_eq_general … := PID.x_coord_nsmul_eq W hns hn hns' hnP` — the `ℤ/ℚ` specialisation is **literally** this lemma applied |
| `GeneralDiscriminant.lean:147` | `have hcoord := x_coord_nsmul_eq_general W hpt` — uses it transitively via the `_general` alias |

Inline-derivation grep: none — nobody re-derives `x'·ΨSqₙ = Φₙ` by hand elsewhere; this lemma is the
single source.

Composability signal: **K = 2 internal direct uses + a re-exported specialisation, no inline
re-derivation → real API.** Strong YES-side signal. The `_general` alias is exactly the
"General*/PID* duplicated track" the task flagged: `x_coord_nsmul_eq_general` adds nothing — it is
`PID.x_coord_nsmul_eq` at `ℤ/ℚ`. After the Phase-4b generalisation to bare `WeierstrassCurve K`, the
`_general` alias becomes entirely redundant.

---

### Composition check (Phase 6)

Can `x_coord_nsmul_eq` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: compose mathlib's `WeierstrassCurve.Φ`/`ΨSq` defs with the `Affine.Point` group law.
  - Mathlib decls available: `WeierstrassCurve.Φ`, `WeierstrassCurve.ΨSq`, `AddCommGroup W.Point`.
  - Result: **fails.** Mathlib provides no lemma relating `n • P` to evaluations of `Φ`/`ΨSq`. The
    entire bridge (`n • P` in Jacobian coords `= ⟦φₙ,ωₙ,ψₙ⟧`, i.e. `zsmul_eq_smulEval`, plus the
    bivariate→univariate `evalEval_φ_eq_eval_Φ` / `evalEval_Ψ_sq_eq_eval_ΨSq`) does not exist in mathlib.
  - Notes: this is a multi-hundred-line development in the project (`ZSMul.lean`, `EvalBridge.lean`,
    the `Universal.*` even-odd-induction machinery). It is **emphatically not** a 1–3 call composition.

Conclusion: **NOT-COMPOSABLE** from mathlib. The result requires genuine new content that mathlib lacks.

---

## Verdict: `LutzNagell.PID.x_coord_nsmul_eq`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): the formula `x([n]P) = φₙ/ψₙ²` (cleared-denom `x'·ψₙ² = φₙ`) is a
  foundational, universally-stated result (Silverman/Washington/Sutherland/Wikipedia). Standard over a
  field; modern treatments push to arbitrary rings.
- Generality analysis (Phase 4): STRICTLY NARROWER-by-scaffolding — content is field-level but dressed
  in an `R → Frac(R)` wrapper whose `R`-side hypotheses (`IsDomain`, `UFD`, `IsFractionRing`) are
  `omit`ted. Phase 4c: MODERN-IDIOM restatement over bare `WeierstrassCurve K`, CHEAP.
- Mathlib search (Phase 5): not in mathlib; mathlib has `Φ`/`ΨSq` defs + degrees only, no geometric
  link to `n • P`.
- Composition check (Phase 6): NOT-COMPOSABLE (the bridge is a large project-only development).

**Rationale:**

This is a genuinely valuable, genuinely missing result: it is the theorem that gives mathlib's division
polynomials their *geometric meaning* — that `Φₙ`/`ΨSqₙ` actually compute the x-coordinate of `n • P`.
Mathlib currently defines these polynomials (and their degrees) in
`DivisionPolynomial/{Basic,Degree}.lean` but never connects them to the elliptic-curve group law; the
`EllipticDivisibilitySequence` file likewise never mentions a `Point`. The forked project supplies
exactly this bridge, and it is not composable from mathlib primitives — the supporting machinery
(`zsmul_eq_smulEval`, `smulEval`, the universal even-odd-induction, the `EvalBridge` lemmas) is a
substantial development absent from mathlib. So this is not NO-mathlib-has-it and not
NO-composable-from-mathlib.

It is **not** YES-add-as-is, however, because the *current statement* carries the NagellLutz project's
`R = `(PID/UFD), `K = Frac(R)` framing — base-changing `W : WeierstrassCurve R` to `curveK R K W` — when
the result is purely a fact about a Weierstrass curve over a field `K` (the `R`-side hypotheses are
literally `omit`ted in the proof). The mathlib-idiomatic form drops `R` entirely and states the lemma
over `W : WeierstrassCurve K`, `[Field K]` (Phase 4b/4c). That restatement is CHEAP for *this* lemma.
Hence YES-but-generalise-first.

**Reason for the generalisation:** MODERN-IDIOM (Bourbaki 2.0) — remove the unused base-change/`Frac(R)`
scaffolding so the statement lives over a bare field, matching mathlib's `DivisionPolynomial` and
`Affine.Point` API and eliminating the duplicated `x_coord_nsmul_eq_general` `ℤ/ℚ` alias.

**Proposed restatement:**
```lean
theorem x_coord_nsmul_eq {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y : K} (hns : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : K} (hns' : W.toAffine.Nonsingular x' y')
    (hnP : n • (WeierstrassCurve.Affine.Point.some _ _ hns) =
           WeierstrassCurve.Affine.Point.some _ _ hns') :
    x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  sorry -- current proof survives: curveK R K W is just *some* WeierstrassCurve K
```

Estimated cost of regeneralisation: **CHEAP** (for this lemma's own statement/proof). EXPENSIVE in the
*aggregate*, because shipping it to mathlib requires first upstreaming the whole supporting tower
(`smulEval` / `zsmul_eq_smulEval` / the `Universal.*` multiplication-formula development / the
`EvalBridge` `evalEval_φ_eq_eval_Φ` & `evalEval_Ψ_sq_eq_eval_ΨSq` lemmas). That tower is the real
mathlib contribution; this lemma is its clean x-coordinate corollary. EXPENSIVE does not downgrade the
verdict — it informs sequencing.

**Mathlib downstream this enables:**
- The first link between `Mathlib/.../DivisionPolynomial/Basic.lean` (`Φ`, `ΨSq`) and
  `Mathlib/.../Affine/Point.lean` (`n • P`). After it, the y-coordinate analogue (`ωₙ/ψₙ³`),
  Nagell–Lutz integrality, torsion-point computations, and division-polynomial-based isogeny/torsion API
  all become reachable.
- Removes the need for any `curveK`-style base-change wrapper in downstream consumers.

**PR grouping:** ship as part of (or immediately after) a PR that upstreams the supporting machinery
(`smulEval` + `zsmul_eq_smulEval` + the `EvalBridge` univariate-bridge lemmas). The natural grouping is:
(1) `smulEval` / multiplication formula in Jacobian coords; (2) the bivariate→univariate `Φ`/`ΨSq`
bridge; (3) this x-coordinate corollary. Also fold in the y-coordinate analogue if/when proved.

Next action: run `/generalise LutzNagell.PID.x_coord_nsmul_eq` to lock the field-level statement (it
will tension against both the literature-standard form and the modern-idiom form), then coordinate the
larger upstreaming of the supporting tower before opening the mathlib PR. Proposed mathlib home:
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` (a new file, e.g.
`Multiplication.lean` or `Point.lean`).

---

## Next step

Run `/generalise LutzNagell.PID.x_coord_nsmul_eq` to restate over a bare `WeierstrassCurve K` (dropping
the `R`/`Frac(R)` scaffolding and the redundant `x_coord_nsmul_eq_general` alias); then upstream the
supporting `smulEval` / `zsmul_eq_smulEval` / `EvalBridge` tower as the substantive mathlib PR, with this
lemma as its x-coordinate corollary.
