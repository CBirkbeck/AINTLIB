# /mathlibable report — `WeierstrassCurve.evalEval_φ_eq_eval_Φ`

Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic
divisibility sequences). Step-9 (overview) full mathlibable assessment, single declaration.

> **Project context.** This project *forks* `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
> and `Mathlib.NumberTheory.EllipticDivisibilitySequence` into `LutzNagell/DivisionPolynomial.lean`
> + `LutzNagell/EllipticDivisibilitySequence.lean` (to dodge `normEDS`/`complEDS` name clashes — see
> the fork's own header docstring). Consequence: the `φ`, `Φ`, and the congruence
> `Affine.CoordinateRing.mk_φ` that this lemma is built on are **byte-for-byte copies of mathlib's**
> (only the EDS import differs). The mathlib originals are therefore the correct reference targets.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note; reasoning from source).
  The decl elaborates against the pinned mathlib (`09b373db6e24`) — its proof terms
  (`evalEval_eq_of_mk_eq`, `Affine.CoordinateRing.mk_φ`, `evalEval_C`) all resolve in the fork + mathlib.
- decl `WeierstrassCurve.evalEval_φ_eq_eval_Φ`:  ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:54`
- kind:                      theorem
- has sorry:                 no (proof: `have h := evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_φ W n); rwa [evalEval_C] at h`)
- module docstring summary:  "Eval bridge lemmas for Lutz–Nagell" — bridges the coordinate-ring
  congruences (`mk_ψ`, `mk_φ`, `mk_Ψ_sq`) to concrete equalities after evaluating bivariate
  division polynomials at an on-curve point `(x, y)`.

---

### Statement (Phase 1)

`WeierstrassCurve.evalEval_φ_eq_eval_Φ` is a theorem stating the following:

> Let `W` be a Weierstrass curve over a field `F`, and let `(x, y)` be a point *on* the curve
> (i.e. satisfying the affine Weierstrass equation, `W.toAffine.Equation x y`). For every integer
> `n`, evaluating the **bivariate** division polynomial `φₙ ∈ F[X][Y]` at `(x, y)` equals
> evaluating the **univariate** polynomial `Φₙ ∈ F[X]` at the x-coordinate `x`.

Here `φₙ = X·ψₙ² − ψₙ₊₁·ψₙ₋₁` (the numerator of the x-coordinate of `nP` in the multiplication
formula `x(nP) = φₙ(x)/ψₙ²(x)`), and `Φₙ` is its image after reducing modulo the Weierstrass
equation — i.e. `φₙ` and `C(Φₙ)` are equal in the coordinate ring `F[X][Y]/(W.polynomial)`. The
lemma says this coordinate-ring congruence descends to *concrete values* once you plug in a point
that actually lies on the curve.

Variables / typeclasses involved (Lean side):
- `{F : Type*} [Field F]` — the base field.
- `(W : WeierstrassCurve F)` — the curve.
- `{x y : F}` — the coordinates of a point.
- `(n : ℤ)` — the division index.

Hypotheses (Lean side):
- `(heq : W.toAffine.Equation x y)` — `(x, y)` is on the curve.

Conclusion (math): `φₙ(x, y) = Φₙ(x)` for `(x, y)` on the curve.
Conclusion (Lean): `(W.φ n).evalEval x y = (W.Φ n).eval x`

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper bridge lemma in a `## Main results`-listed *file* but not a main result itself; it
transports a coordinate-ring congruence (`mk_φ`) to a concrete on-curve evaluation. Not named after
a person/place; introduces no structure. Its job is plumbing between mathlib's bivariate
division-polynomial API and the project's integrality argument.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (`have h := evalEval_eq_of_mk_eq W heq (mk_φ W n)` ; `rwa [evalEval_C] at h`).
One-liner verdict: n/a — kind is `theorem`, not `def`. (The proof is a 2-step term; this reinforces
the composability signal but the def-specific one-line exemption table does not apply.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                      | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial φₙ ψₙ x-coordinate multiplication formula nφ/ψ²"                                       | yes  | `x(nP) = φₙ(x)/ψₙ²(x)`, `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`        | MIT 18.783 L5; arXiv:1108.3051. Classical multiplication formula. |
|  2 | WebSearch (general / coord-ring) | "division polynomials evaluate at point coordinate ring quotient Weierstrass Silverman"                    | yes  | EDS over `ℚ[x,y,A,B]/(y²−x³−Ax−B)`; eval at `P∈E(K)` | Wikipedia "Division polynomials"; arXiv:2102.07573; Sage `ell_generic`. Division polys live in the coordinate ring; their *values* at `P` are studied. |
|  3 | WebSearch (named-after / nLab/Stacks) | "nLab elliptic curve division polynomial; Stacks Weierstrass coordinate ring evaluation"             | partial | coord-ring `k[u,v]/(v²−u³−Au−B)`; ψ recursion        | nLab `elliptic+curve`; no *named* "eval-commutes-with-reduction" lemma anywhere. |
|  4 | ChatGPT MCP                      | "is `evalEval x y φ_n = eval x Φ_n` a named theorem; what generality?"                                      | n/a  | (MCP down — Codex backend errored, per task note)    | Fell back to channels 1–3 + commutative-algebra reasoning below. |
|  5 | Local references                 | `.mathlib-quality/references/` for "division polynomial" / "Φ"                                              | n/a  | (no references dir present in project)               | recorded n/a. |
|  6 | nLab                             | `elliptic curve`                                                                                            | partial | Weierstrass invariants, ψ recursion                | no φ→Φ reduction-then-evaluate statement; not a categorical concept worth an abstract page. |
|  7 | nCatLab (if categorical)         | —                                                                                                          | n/a  | —                                                    | n/a — not a categorical concept; it is a concrete polynomial-evaluation identity. |
|  8 | Stacks Project (if alg geom)     | Weierstrass equation coordinate ring                                                                        | n/a  | —                                                    | n/a — Stacks treats curves scheme-theoretically; no division-polynomial `evalEval` bookkeeping. |
|  9 | MathOverflow / MSE               | "x-coordinate of nP division polynomial value at point"                                                     | partial | restates `x(nP)=φₙ/ψₙ²`                              | the *quotient* `φₙ/ψₙ²` is the studied object; the numerator-only evaluation step is never isolated as a result. |
| 10 | recent arXiv (last 5 years)      | "division polynomials elliptic divisibility sequence evaluate"                                              | yes  | arXiv:2302.03650, 2102.07573                          | division-poly *values* over local rings/EDS; still no named "evalEval φₙ = eval Φₙ" lemma. |

### Literature summary (Phase 3)

Concept identified as: the **division-polynomial multiplication formula** numerator,
`φₙ = X·ψₙ² − ψₙ₊₁·ψₙ₋₁`, and its reduction `Φₙ` modulo the Weierstrass equation (Silverman, *AEC*
Exercise 3.7; Washington §9.5; MIT 18.783).
Sources agree on the standard form: yes — `φₙ` and the formula `x(nP) = φₙ(x)/ψₙ²(x)` are universal
and classical.
Most general standard form: division polynomials form a **generic EDS over the coordinate ring**
`R[x,y]/(Weierstrass eqn)` for an arbitrary base ring `R`; their values at a point `P` satisfying
the equation are obtained by the quotient evaluation map.
Generality dimensions where the literature varies:
  - base ring: from `ℚ` / a field up to an **arbitrary commutative ring** (Sage `ell_generic`,
    arXiv:2302.03650 "elliptic curves over finite local rings"). The most general is *any* `CommRing`.
Disagreement with the literature: **none**. But the *specific Lean statement here is NOT a named
result*. It is the elementary commutative-algebra fact that **evaluation at a point satisfying the
defining equation factors through the quotient by that equation** — i.e. the ring map
`F[X][Y] → F`, `p ↦ p.evalEval x y`, kills `(W.polynomial)` when `Equation x y` holds, hence equal
classes in `F[X][Y]/(W.polynomial)` (here `[φₙ] = [C Φₙ]`) have equal images. The literature uses
this implicitly every time it writes "evaluate the division polynomial at `P`"; it is never stated,
named, or proved as a standalone lemma because it is immediate from the universal property of the
quotient. This is a **formalisation-bookkeeping lemma**, not a mathematical theorem.

---

### Generality analysis — `WeierstrassCurve.evalEval_φ_eq_eval_Φ`

Literature-standard form (from Phase 3): the transport "`mk`-equal ⟹ equal-on-curve-values" holds
over any commutative ring; nothing about `φ`/`Φ` specifically needs a field.

| # | Parameter / hypothesis           | Current Lean form        | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened   |
|---|----------------------------------|--------------------------|----------------------------------|---------------------|------------------------------------|
| 1 | `[Field F]`                      | base is a field          | any `CommRing R`                 | **yes**             | The proof uses only `AdjoinRoot.evalEval_mk` (stated over `CommRing` — `Bivariate.lean:391`), the congruence `mk_φ` (stated over `CommRing` — `Basic.lean:482`), and `evalEval_C` (over `CommRing` — `Bivariate.lean:49`). `Field` is **never used**; it is inherited from the surrounding Lutz–Nagell context, not required by this lemma. |
| 2 | specialised to `φ`/`Φ`           | the `φ`/`Φ` pair         | any `mk`-equal pair `p, C q`     | **yes**             | The general statement is the *parent* `evalEval_eq_of_mk_eq` (`mk W p = mk W q ⟹ p.evalEval x y = q.evalEval x y`) composed with `evalEval_C`. This lemma is its `φ`/`Φ` instance. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (gratuitous `[Field F]`; specialised to one
polynomial family).
Number of weakening opportunities found: 2.
Proposed restatement (only relevant if this were going *in*): drop `[Field F]` to `[CommRing R]` and
recognise it as the `φ`-instance of the ring-level transport `evalEval_eq_of_mk_eq` + `evalEval_C`.
Cost of restatement: CHEAP — the proof term is already ring-level; only the `variable` line changes.

**However** — see Phase 5/6: the ring-level transport and `evalEval_C` are already in mathlib, so the
"generalisation" is not "ship a more general lemma" but "inline the two-call mathlib composition".
The narrowness pushes toward a NO bucket (compose at the call site), not YES-but-generalise.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | —                      | already typeclass-driven (`Field`/`CommRing`). |
|  2 | sequences/metric → filters/topological?                                                    | no       | —                      | purely algebraic evaluation identity; no limits. |
|  3 | construction → universal-property class?                                                   | no (already!) | —                | the proof already *uses* `AdjoinRoot`'s universal property (`evalEval` = `lift`); nothing to upgrade. |
|  4 | set+closure-predicate → bundled substructure?                                              | no       | —                      | no substructure here. |
|  5 | field/metric-specific → modules/(semi)ring weakening?                                       | **yes**  | `[CommRing R]` instead of `[Field F]` | matches mathlib's `mk_φ`/`evalEval_mk`, both `CommRing`. |
|  6 | 1-categorical → higher-categorical?                                                        | no       | —                      | not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid?                                                 | no       | `n : ℤ` is correct (EDS are ℤ-indexed). | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (beyond the row-5 ring weakening already captured in 4b). This is a
two-line bridge, not a structure or a construction; there is no contemporary mathlib reformulation
that reorganises it. The only "improvement" is the `CommRing` weakening, and that improvement
*coincides with inlining the existing mathlib composition* — there is nothing new to state.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.evalEval_φ_eq_eval_Φ`

[A] Lean-Finder       `evalEval φ Φ on-curve`                              n/a — index MCP tool not exposed in this environment; substituted by authoritative source grep [D].
[B] Loogle            `(Polynomial.evalEval _ _ (WeierstrassCurve.φ _ _)) = _`  n/a — Loogle MCP not exposed here; source grep [D] is definitive for "does a φ/Φ evalEval bridge exist".
[C] LeanSearch        "value of bivariate division polynomial at on-curve point equals univariate"  n/a — LeanSearch MCP not exposed here; covered by [D] + literature Phase 3.
[D] Grep mathlib src  `evalEval_φ`, `evalEval_Φ`, `eval_Φ`, `evalEval.*Equation`, `evalEval_eq_of_mk_eq`  **no hits** for any φ/Φ/ψ/Ψ evalEval bridge anywhere in `Mathlib/`; **no hit** for `evalEval_eq_of_mk_eq` or `evalEval_φ_eq_eval_Φ`. Mathlib's DivisionPolynomial API stops at coordinate-ring congruences (`mk_ψ`, `mk_φ`, `mk_Ψ_sq`, `mk_ψ₂_sq` in `Basic.lean`) and **never evaluates at a concrete point**. The only `Equation x y`+`evalEval` link is the trivial `equation_iff'` (`Basic.lean:152`, unfolding `Equation` to `evalEval_polynomial = 0`).
[E] Name pattern      `evalEval_φ_eq_eval_Φ`, `evalEval_eq_of_mk_eq` across mathlib   **no hits** (exist only in the project).

Searched for both:
  - the user's current form (`(W.φ n).evalEval x y = (W.Φ n).eval x`) — not in mathlib.
  - the literature-standard / ring-level form (transport `mk`-equality to on-curve evaluation) — the
    *building blocks* are in mathlib but the assembled `φ`/`Φ` bridge is not.

Building blocks located in mathlib (all on `CommRing`):
  - `WeierstrassCurve.Affine.CoordinateRing.mk_φ` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`
    (`mk W (W.φ n) = mk W (C <| W.Φ n)`). [Project fork: `LutzNagell/DivisionPolynomial.lean:405`, identical.]
  - `AdjoinRoot.evalEval_mk` — `Mathlib/Algebra/Polynomial/Bivariate.lean:391`
    (`evalEval h (mk p g) = g.evalEval x y`, where `h : p.evalEval x y = 0`).
  - `Polynomial.evalEval_C` — `Mathlib/Algebra/Polynomial/Bivariate.lean:49`
    (`(C p).evalEval x y = p.eval x`).

Concluded: **found building blocks (`mk_φ`, `AdjoinRoot.evalEval_mk`, `evalEval_C`); composition
would yield our form**. The exact `φ`/`Φ` on-curve bridge is NOT in mathlib (all source-grep methods
exhausted, plus the literature-standard ring-level form).

---

### Call sites — `WeierstrassCurve.evalEval_φ_eq_eval_Φ`

Internal use count: **K = 1**  (within the project, excluding the declaring `EvalBridge.lean`).
External-to-file callers: 1 distinct file.

| Caller file:line                                                  | Usage pattern (one-line excerpt)                                   |
|-------------------------------------------------------------------|--------------------------------------------------------------------|
| `LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:58`        | `rw [evalEval_φ_eq_eval_Φ (curveK R K W) hns.left n] at hX`         |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `evalEval_φ_eq_eval_Φ`?):
  - (none) — the sibling bridges `evalEval_Ψ_sq_eq_eval_ΨSq`, `evalEval_ψ_eq_evalEval_Ψ` are used at
    the *same* site (`PIDIntegralMultiple.lean:59–60`) via the same `evalEval_eq_of_mk_eq` engine; the
    family is a small, internally-consistent local API, not duplicated logic.

Call-sites signal: **K = 1**, single use, no external (downstream-library) consumer. Per the
call-sites rubric this leans **NO-composable** (the wrapper is used once and is a ≤3-call mathlib
composition; it could be inlined). It is not dead code, and it is not a heavily-reused public API.

---

### Composition check (Phase 6)

Can `evalEval_φ_eq_eval_Φ` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the file's own proof, with the parent inlined to mathlib primitives):
```lean
example (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  -- `Equation x y` is *definitionally* `W.polynomial.evalEval x y = 0`
  have h := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq    -- the transport engine
  rw [← h (W.φ n), ← h (C (W.Φ n)), Affine.CoordinateRing.mk_φ W n, evalEval_C]
```
  - Mathlib decls used: `AdjoinRoot.evalEval_mk` (`Bivariate.lean:391`),
    `Affine.CoordinateRing.mk_φ` (`Basic.lean:482`), `Polynomial.evalEval_C` (`Bivariate.lean:49`).
  - Result: **succeeds**. Three mathlib calls: lift both sides through `evalEval_mk`, rewrite by the
    `mk_φ` congruence, simplify the `C` with `evalEval_C`.
  - Notes: `heq : W.toAffine.Equation x y` *is* the `evalEval_polynomial = 0` hypothesis
    `AdjoinRoot.evalEval_mk` wants (`Equation` is defined as `W.polynomial.evalEval x y = 0`), so no
    extra conversion is needed.

Attempt 2 (factoring through the project's own engine, exactly as written in the file):
```lean
example (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  have h := evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_φ W n)
  rwa [evalEval_C] at h
```
  - This is the file's actual proof. `evalEval_eq_of_mk_eq` is *itself* a NO-composable 2-call
    composition (`AdjoinRoot.evalEval_mk` + `congrArg`), so even via the engine the whole thing is a
    ≤3-call mathlib composition.

Conclusion: **COMPOSABLE** — a 3-call mathlib composition (`AdjoinRoot.evalEval_mk` ∘ `mk_φ` ∘ `evalEval_C`).
No new lemma is needed; inline at the single call site.

---

## Verdict: `WeierstrassCurve.evalEval_φ_eq_eval_Φ`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the φ/ψ multiplication formula is classical (Silverman *AEC* Ex 3.7,
  MIT 18.783), but this *specific* statement ("evaluating φₙ at an on-curve point = evaluating its
  reduction Φₙ at x") is **not a named result** — it is the elementary fact that evaluation at a
  point on the curve factors through the coordinate-ring quotient.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — gratuitous `[Field F]` (the proof
  is ring-level) and specialised to the φ/Φ pair; the general statement is the ring-level transport
  already inlinable from mathlib.
- Mathlib search (Phase 5): not in mathlib as a φ/Φ bridge; **all three building blocks are**
  (`Affine.CoordinateRing.mk_φ` @ `Basic.lean:482`, `AdjoinRoot.evalEval_mk` @ `Bivariate.lean:391`,
  `evalEval_C` @ `Bivariate.lean:49`).
- Composition check (Phase 6): COMPOSABLE — a 3-call composition; succeeds (Attempt 1).

**Rationale:**

Mathlib's division-polynomial development deliberately stops at *coordinate-ring congruences* —
`mk_ψ`, `mk_φ`, `mk_Ψ_sq` (all in `DivisionPolynomial/Basic.lean`) — and never evaluates a division
polynomial at a concrete on-curve point, because doing so is a one-step application of the generic
machinery in `Mathlib/Algebra/Polynomial/Bivariate.lean`: the ring hom `evalEval x y : F[X][Y] → F`
is `AdjoinRoot.evalEval`-lifted precisely when `(x,y)` satisfies the equation, so equal classes
modulo `(W.polynomial)` — which is exactly what `mk_φ` provides — map to equal values, and
`evalEval_C` collapses the `C (Φ n)` on the right to `(Φ n).eval x`. The file's own proof is two
lines and the assembled identity is a ≤3-call mathlib composition, so no new mathlib lemma is
warranted: the right move is to inline the composition at the call site (or, if the project wants the
named convenience, keep it strictly *local* to NagellLutz). The `[Field F]` hypothesis is moreover
unused — every primitive in the proof is `CommRing`-level — so even the narrow form is over-stated.

**WHY not (refactor-actionable):**
Mathlib has the building blocks, not this exact bridge; the user's form is a 3-mathlib-call
composition. The blocks are: the on-curve transport `AdjoinRoot.evalEval_mk`
(`Mathlib/Algebra/Polynomial/Bivariate.lean:391`), the division-polynomial congruence
`WeierstrassCurve.Affine.CoordinateRing.mk_φ`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`), and the constant-eval
lemma `Polynomial.evalEval_C` (`Mathlib/Algebra/Polynomial/Bivariate.lean:49`). Note this lemma is
*already* essentially inlined: its proof is the engine `evalEval_eq_of_mk_eq` (itself NO-composable)
applied to `mk_φ`, then `rwa [evalEval_C]`.

Mathlib building blocks:
  - `AdjoinRoot.evalEval_mk`  — `Mathlib/Algebra/Polynomial/Bivariate.lean:391`
  - `WeierstrassCurve.Affine.CoordinateRing.mk_φ` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:482`
  - `Polynomial.evalEval_C` — `Mathlib/Algebra/Polynomial/Bivariate.lean:49`

Composition sketch (≤3 lines):
```lean
-- `heq : W.toAffine.Equation x y` is defeq to `W.polynomial.evalEval x y = 0`
example (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  have h := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq
  rw [← h (W.φ n), ← h (C (W.Φ n)), Affine.CoordinateRing.mk_φ W n, evalEval_C]
```

Call sites in our project (from Phase 6.0): **K = 1**
  - `LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:58`:
    `rw [evalEval_φ_eq_eval_Φ (curveK R K W) hns.left n] at hX`

Refactor plan:
  - **Preferred (keep the local API):** this lemma is one member of a coherent, internally-reused
    bridge family (`evalEval_eq_of_mk_eq` + the ψ/Ψ/φ/ΨSq members), all consumed together at
    `PIDIntegralMultiple.lean:58–60`. Since the family is built on *mathlib's own* `mk_*` congruences
    and the generic `evalEval` machinery, the cleanest outcome is for the project to drop its
    **forked** `DivisionPolynomial.lean` (and the EDS fork) in favour of
    `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
    (+ `import Mathlib.NumberTheory.EllipticDivisibilitySequence`), then keep this 2-line bridge as a
    *local* convenience over mathlib's `mk_φ`. It is **not** a mathlib contribution.
  - **Alternative (full inline):** at the single call site `PIDIntegralMultiple.lean:58`, replace the
    `rw [evalEval_φ_eq_eval_Φ …]` with the 3-call composition above (matching `curveK R K W` for `W`,
    `hns.left` for `heq`); then delete `evalEval_φ_eq_eval_Φ`.

Next action: do **not** open a mathlib PR. Either (a) de-fork onto mathlib's `mk_φ` and keep this as a
local 2-line bridge, or (b) inline the 3-call composition at `PIDIntegralMultiple.lean:58` and delete
the lemma. If the de-fork lands and the project decides the on-curve bridge family is broadly useful,
a *separate* discussion (BORDERLINE) about contributing the **parent** `evalEval_eq_of_mk_eq`
(ring-level `mk`→`evalEval` transport) — not this φ-specialisation — would be the right scope.

---

## Next step

Do not open a mathlib PR. De-fork onto mathlib's `Affine.CoordinateRing.mk_φ` (+ the generic
`Bivariate`/`AdjoinRoot` machinery) and keep `evalEval_φ_eq_eval_Φ` as a *local* 2-line convenience,
**or** inline the 3-call composition (`AdjoinRoot.evalEval_mk` ∘ `mk_φ` ∘ `evalEval_C`) at the single
call site `PIDIntegralMultiple.lean:58` and delete the lemma. The `[Field F]` hypothesis is unused and
should be `[CommRing R]` in either case.
