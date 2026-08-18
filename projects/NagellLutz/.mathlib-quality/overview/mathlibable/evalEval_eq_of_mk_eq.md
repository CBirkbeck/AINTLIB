# /mathlibable report — `WeierstrassCurve.evalEval_eq_of_mk_eq`

## Verdict: **NO-composable-from-mathlib**

> One-line: a 2-call composition of `AdjoinRoot.evalEval_mk` (already in mathlib) + `congrArg`;
> the source proof *is* that composition. Triplicated across AINTLIB; no new mathematical content.

---

### Baseline (Phase 0)
- lake build:               not re-run (env stale per task); decl + mathlib primitives read directly
  from source, verified against the pinned mathlib checkout.
- decl `WeierstrassCurve.evalEval_eq_of_mk_eq`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:32`.
- kind:                      theorem
- has sorry:                 no (proof body, EvalBridge.lean:35–36, shown below)
- module docstring summary:  "Eval bridge lemmas for Lutz–Nagell" — bridges the coordinate-ring
  congruences (`mk_ψ`, `mk_φ`, `mk_Ψ_sq`) to concrete equalities after evaluating bivariate
  polynomials at an on-curve point `(x, y)`.

Qualified name VERIFIED: the decl sits inside `namespace WeierstrassCurve` (EvalBridge.lean:24),
so the parsed `WeierstrassCurve.evalEval_eq_of_mk_eq` is correct.

---

### Statement (Phase 1)

For a Weierstrass curve `W` over a field `F` and a point `(x, y)` satisfying the Weierstrass
equation (`W.toAffine.Equation x y`), if two bivariate polynomials `p, q : F[X][Y]` become **equal
in the affine coordinate ring** `F[W]` (`Affine.CoordinateRing.mk W.toAffine p = … q`), then they
have **equal evaluations at the point**: `p.evalEval x y = q.evalEval x y`.

Mathematically: *evaluation at an on-curve point factors through the coordinate ring*
`F[W] = F[X,Y]/(W(X,Y))` — i.e. the universal property of the quotient ring. A point on the curve is
a root of the defining polynomial, so the evaluation homomorphism kills the ideal `(W(X,Y))` and
descends to a well-defined map on the quotient.

- Parameters: `W : WeierstrassCurve F`, `[Field F]`, `x y : F`, `p q : F[X][Y]`.
- Hypotheses: `heq : W.toAffine.Equation x y` (point on curve); `h : mk W p = mk W q`.
- Conclusion: `p.evalEval x y = q.evalEval x y`.

Source proof (EvalBridge.lean:35–36) — already the composition:
```lean
have hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq
exact hev p ▸ hev q ▸ congrArg _ h
```

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a helper/glue lemma (functoriality of evaluation through a quotient ring); not
a named theorem, not a new structure. It is a *bridge* lemma feeding the project's real results
(`evalEval_ψ_odd`, the prime-order integrality argument), and not a `## Main results` headline in the
mathematical sense.

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → the one-liner-definition exemption table is n/a.
(For the record: the *proof body* is 2 lines and is literally the mathlib composition.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "evaluation map factors through quotient ring AdjoinRoot polynomial coordinate ring EC"    | yes  | `F[W]=F[X,Y]/(W)`; eval factors through it | mathlib `Affine/Point.lean`, isogeny lecture notes — confirms coordinate-ring + eval picture |
|  2 | WebSearch (general form)         | "coordinate ring elliptic curve evaluation at point well-defined polynomial congruence"    | yes  | well-defined eval on `R[W]` for any comm ring `R` | Sage docs, division-poly-over-rings literature |
|  3 | WebSearch (mathlib API form)     | "mathlib AdjoinRoot.evalEval_mk lift evalRingHom bivariate polynomial RingHom factor"      | yes  | `AdjoinRoot.evalEval : AdjoinRoot p →+* R`, `evalEval_mk` | the EXACT primitive — eval factors through the `AdjoinRoot p` quotient |
|  4 | ChatGPT MCP                      | not invoked — the mathlib-API hit (#3) pins the standard form exactly; undergraduate-level quotient-ring functoriality with no historical ambiguity | n/a  | —                   | nothing to resolve |
|  5 | Local references                 | none surfaced for this decl this run                                                       | n/a  | —                   | — |
|  6 | nLab / nCatLab                   | "elliptic curve" coordinate ring as quotient; eval = point of the scheme                   | yes  | coordinate ring = quotient; eval ∈ `Hom(R[W],F)` | standard scheme-theoretic framing; not a higher-categorical concept |
|  7 | Stacks Project                   | quotient ring / evaluation at a point (functor of points)                                  | n/a  | `Hom(R[W],F)` ↔ curve points | standard, below Stacks granularity for this glue lemma |
|  8 | MathOverflow / MSE               | eval factors through quotient by defining ideal                                            | n/a  | —                   | textbook universal property (Atiyah–Macdonald); no discussion needed |
|  9 | recent arXiv                     | division polys over rings                                                                   | yes  | eval of division polys at ring points | confirms ambient setting; glue lemma itself is not a paper result |

Protocol passed: WebSearch at three generality levels (specific EC / general-ring / mathlib-API);
ChatGPT MCP recorded n/a-with-reason; refs, nLab/nCatLab, Stacks, MO, arXiv each checked or
n/a-with-reason.

### Literature summary (Phase 3)

Concept: *evaluation at a point factors through the coordinate ring* — the universal property of the
quotient `R[X,Y]/(W(X,Y))`, specialised to the evaluation homomorphism. In mathlib's vocabulary this
is exactly `AdjoinRoot.evalEval` (the lift of `evalRingHom`) together with its computation rule
`AdjoinRoot.evalEval_mk`.

Sources agree on the standard form. Most general standard form: any **commutative ring** `R` (not
just a field) — confirmed by the literature AND by the parallel AINTLIB HasseWeil/Auxiliary copy,
which states it over `[CommRing R]`. The only generality dimension that varies is the base ring
(field here vs. general comm ring). No disagreement with the literature: the statement is correct; it
is merely a specialisation of a fact mathlib already provides one unfold-step away.

---

### Generality analysis (Phase 4)

Literature-standard / mathlib-primitive form: `AdjoinRoot.evalEval_mk` over `[CommRing R]`.

| # | Parameter / hypothesis     | Current Lean form        | Literature-standard form | Weaker exists? | Reason |
|---|----------------------------|--------------------------|--------------------------|----------------|--------|
| 1 | `[Field F]`                | field                    | commutative ring         | yes            | proof uses only `congrArg` + `evalEval_mk` (stated over `[CommRing R]`); no field axioms. The HasseWeil/Auxiliary copy is verbatim over `[CommRing R]`. |
| 2 | `heq : Equation x y`       | point on curve           | same                     | NO             | feeds `AdjoinRoot.evalEval`; `Equation` ≝ `polynomial.evalEval x y = 0` — essential. |
| 3 | `p q : F[X][Y]`            | bivariate over the field | over the comm ring       | yes            | tracks the base-ring weakening in row 1. |

### Generality verdict (Phase 4b)

Current form is **STRICTLY NARROWER THAN STANDARD** (field instead of comm ring); 1 weakening
opportunity (`Field F` → `CommRing R`), cost CHEAP/mechanical (the HasseWeil/Auxiliary copy already
does it). This does **not** push the verdict to YES-but-generalise-first, because Phases 5–6 show the
*comm-ring* form is itself a ≤2-call composition of an existing mathlib lemma — so even the general
form should be inlined via `AdjoinRoot.evalEval_mk`, not added to mathlib as a new declaration.

### Modern-idiom check (Phase 4c)

The mathlib idiom for "construction satisfying a universal property" is *already present*:
`AdjoinRoot.evalEval` is the lifted ring hom, and `evalEval_mk` is its computation rule. The right
move is to *use that RingHom*, not to restate the lemma. This reinforces NO-composable.

---

### Diamond / defeq risk (Phase 4.5)

n/a — kind is `theorem` (no defeq / typeclass-search surface introduced).

---

### Mathlib search-status (Phase 5) — verified against the pinned mathlib checkout

(`/Users/mcu22seu/Documents/GitHub/aintlib-decompose/.lake/packages/mathlib`, the monorepo's mathlib.)

[B] Loogle      `AdjoinRoot.evalEval _ (AdjoinRoot.mk _ _) = _`        HIT — `AdjoinRoot.evalEval_mk`
[C] LeanSearch  "evaluation factors through coordinate ring of curve"  HIT — `AdjoinRoot.evalEval`, `evalEval_mk`
[D] Grep mathlib src — verified line-for-line:
- `AdjoinRoot.evalEval` — `Mathlib/Algebra/Polynomial/Bivariate.lean:388`
  `@[simps!] noncomputable def evalEval : AdjoinRoot p →+* R := lift (evalRingHom x) y <| eval₂_evalRingHom x ▸ h`
- `AdjoinRoot.evalEval_mk` — `Mathlib/Algebra/Polynomial/Bivariate.lean:391`
  `lemma evalEval_mk (g : R[X][Y]) : evalEval h (mk p g) = g.evalEval x y`
  — over `variable {R} [CommRing R] {x y : R} {p : R[X][Y]} (h : p.evalEval x y = 0)`. **The exact
  factorization rule.**
- `WeierstrassCurve.Affine.CoordinateRing` ≝ `AdjoinRoot W'.polynomial` — `Affine/Point.lean:90` (`abbrev`).
- `WeierstrassCurve.Affine.CoordinateRing.mk` ≝ `AdjoinRoot.mk W'.polynomial` — `Affine/Point.lean:111`
  (`noncomputable abbrev` → `mk W p = mk W q` is *definitionally* `AdjoinRoot.mk … p = AdjoinRoot.mk … q`).
- `WeierstrassCurve.Affine.Equation` ≝ `W.polynomial.evalEval x y = 0` — `Affine/Basic.lean:149`
  (`def` — DEFINITIONALLY the hypothesis `evalEval_mk` needs).
- `Affine.CoordinateRing.mk_ψ`, `mk_φ`, `mk_Ψ_sq` (the congruences the bridge lemmas feed in) live in
  `Mathlib/.../EllipticCurve/DivisionPolynomial/Basic.lean`.

[E] Name pattern `evalEval_eq_of_mk_eq` — **NOT in mathlib** (the only `*_eq_of_mk_eq` hit is the
unrelated `dim_eq_of_mk_eq` in `AlgebraicTopology/SimplicialSet/Simplices.lean`). Present 3× in
AINTLIB only.

Searched for BOTH the field-level form and the comm-ring form. Neither packaging is in mathlib; the
**building block** `evalEval_mk` is, at full `[CommRing R]` generality.

---

### Call sites (Phase 6.0) — verified by grep across `projects/`

Internal use count in NagellLutz, excluding the declaring file EvalBridge.lean: **2**.

| Caller file:line                          | Usage pattern (one-line excerpt)                         |
|-------------------------------------------|----------------------------------------------------------|
| NagellLutz/.../GeneralPrimeOrder.lean:178 | `have h := evalEval_eq_of_mk_eq (curveQ W) hns.left …`   |
| NagellLutz/.../PIDPrimeOrder.lean:186     | `have h := evalEval_eq_of_mk_eq (curveK R K W) hns.left …` |

Within EvalBridge.lean it is also the engine for `evalEval_ψ_eq_evalEval_Ψ` (:44),
`evalEval_Ψ_sq_eq_eval_ΨSq` (:49), `evalEval_φ_eq_eval_Φ` (:56) — 3 more uses.

Cross-project duplication grep: the SAME lemma is independently re-declared in **two other AINTLIB
files** (triplication confirmed):
- `HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:718` — `{x y : R}`, over `[CommRing R]`
  (the most general copy; different, longer proof).
- `HasseWeil/HasseWeil/EC/MulByIntUnramified.lean:96` — `{x y : F}` (field-level, like NagellLutz).

Composability signal: a real local convenience lemma (≥3 internal uses + 2 external), BUT the
triplication + the ≤2-call mathlib composition means the right home is mathlib's existing
`AdjoinRoot.evalEval_mk`, not a fourth copy.

### Composition check (Phase 6)

Can it be derived from mathlib in ≤3 chained calls? **Yes — the source proof is exactly that.**

Attempt 1 (the shipped proof, verbatim, 2 calls):
```lean
example (heq : W.toAffine.Equation x y) {p q : F[X][Y]}
    (h : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) :
    p.evalEval x y = q.evalEval x y := by
  -- heq : W.toAffine.polynomial.evalEval x y = 0  (definitionally; `Equation` is that eq)
  have hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq   -- mathlib lemma
  exact hev p ▸ hev q ▸ congrArg _ h                                    -- congrArg + two rewrites
```
- Mathlib decls used: `AdjoinRoot.evalEval_mk` (the only non-core lemma) + `congrArg` (core); the
  `abbrev`/`def` unfoldings `CoordinateRing.mk = AdjoinRoot.mk` and `Equation = (… = 0)` are
  definitional (free).
- Result: **succeeds** — this IS the shipped proof.

Conclusion: **COMPOSABLE** (2 mathlib calls; well within the ≤3 bound).

---

## Verdict: `WeierstrassCurve.evalEval_eq_of_mk_eq`

**Category:** NO-composable-from-mathlib

**Evidence (all verified against the live mathlib pin):**
- Literature (Phase 3): the fact = "evaluation at an on-curve point factors through the coordinate
  ring `F[W]=F[X,Y]/(W)`", i.e. the quotient's universal property; mathlib realises this exactly as
  `AdjoinRoot.evalEval` + `evalEval_mk`.
- Generality (Phase 4): STRICTLY NARROWER (field vs comm ring) — but the comm-ring form is itself a
  composition, so generalising-and-keeping is not warranted.
- Mathlib search (Phase 5): building block `AdjoinRoot.evalEval_mk` present at
  `Mathlib/Algebra/Polynomial/Bivariate.lean:391` over `[CommRing R]`; `CoordinateRing.mk` /
  `Equation` are abbrev/def that unfold to exactly what it needs. The packaging is not in mathlib.
- Composition (Phase 6): COMPOSABLE in 2 calls — the source proof is the composition.

**Rationale:**
`evalEval_eq_of_mk_eq` adds no mathematical content beyond mathlib. Its proof body is a two-call
composition of `AdjoinRoot.evalEval_mk` and `congrArg`. The three ingredients all sit in the pinned
mathlib: (i) `Affine.CoordinateRing.mk W = AdjoinRoot.mk W.polynomial` is an `abbrev`
(`Affine/Point.lean:111`), so `mk W p = mk W q` is *definitionally* `AdjoinRoot.mk … p = AdjoinRoot.mk
… q`; (ii) `Equation x y` is *definitionally* `W.polynomial.evalEval x y = 0` (`Affine/Basic.lean:149`),
the precise hypothesis `AdjoinRoot.evalEval` is built from; (iii) `AdjoinRoot.evalEval_mk h g :
evalEval h (mk p g) = g.evalEval x y` (`Bivariate.lean:391`) does the factorization. Applying (iii) to
`p` and `q` and transporting `congrArg evalEval h` finishes — exactly the shipped proof. This is the
textbook universal property of the quotient ring, already packaged by mathlib as a `RingHom`.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the user's form is a 2-call composition. No new lemma is needed. It
is already triplicated across NagellLutz, HasseWeil/EC, and HasseWeil/Auxiliary (the last over
`[CommRing R]`).

Mathlib building blocks (qualified, with paths):
- `AdjoinRoot.evalEval_mk` — `Mathlib/Algebra/Polynomial/Bivariate.lean:391`
- `AdjoinRoot.evalEval` (the lifted RingHom it computes) — `Mathlib/Algebra/Polynomial/Bivariate.lean:388`
- `WeierstrassCurve.Affine.CoordinateRing.mk` (abbrev for `AdjoinRoot.mk W.polynomial`) —
  `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:111`
- `WeierstrassCurve.Affine.Equation` (def `= polynomial.evalEval x y = 0`) —
  `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:149`

Composition sketch (≤3 lines — already the shipped proof):
```lean
example (heq : W.toAffine.Equation x y) {p q : F[X][Y]}
    (h : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) :
    p.evalEval x y = q.evalEval x y :=
  have hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq
  hev p ▸ hev q ▸ congrArg _ h
```

**Next action:** This is a consolidation monorepo, so the cleanest fix is to keep ONE shared copy.
Pick the most general statement (the HasseWeil/Auxiliary `[CommRing R]` version), promote it to a
`Common/` module, and have NagellLutz and HasseWeil/EC import it; delete the duplicates (the
field-level call sites are instances of the comm-ring lemma and typecheck unchanged). Alternatively,
inline the 2-line `AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq` composition at the call
sites. No mathlib PR is warranted — the building block `AdjoinRoot.evalEval_mk` is already in mathlib.
