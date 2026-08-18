# /mathlibable report — `WeierstrassCurve.Universal.evalEval_φ`

## Verdict: NO-composable-from-mathlib

A one-line glue lemma whose **statement mentions the project-local `polyEval` and
`Universal.curve`** (neither in mathlib). The mathematical content — the division
polynomial `φₙ` commutes with the specialization map `curve.map W.specialize = W` — is
already in mathlib as `map_φ`; the lemma is a ≤3-rewrite composition of `polyEval_apply`
(itself a 1-call wrapper of mathlib's `eval₂_eval₂RingHom_apply`) + mathlib's `map_φ` +
the project's `map_specialize`. It **cannot be upstreamed as-is** (its subject is a
downstream project def); the building blocks already live upstream. Direct sibling of
`evalEval_ψ₂` / `evalEval_Ψ₃` / `evalEval_preΨ₄` / `evalEval_ψ` / `evalEval_ω`
(same disposition); `evalEval_Ψ₃` was assessed `NO-composable-from-mathlib` earlier in
this same overview run, and `evalEval_φ` is the structurally-identical (in fact simpler)
sibling.

> Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
> This project **forks** parts of mathlib (`…EllipticCurve.DivisionPolynomial.*`,
> `…NumberTheory.EllipticDivisibilitySequence`) and carries a project-local
> `Universal.lean`. The lemma `evalEval_φ` is **duplicated verbatim** in
> `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:177`
> (identical statement and proof) — a sign it is shared scaffolding across the two
> forking projects, not a candidate for mathlib.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; the AINTLIB cache dir
  `.lake/build/lib/` is empty). Reasoned from source: the proof is a one-line `simp_rw`
  over in-mathlib lemmas (`polyEval_apply`, `map_φ`, `map_specialize`); see Phase 5/6.
- decl `WeierstrassCurve.Universal.evalEval_φ`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:102`.
- kind:                      `lemma` (inside `noncomputable section`).
- has sorry:                 no.
- qualified name:            **`WeierstrassCurve.Universal.evalEval_φ`** — VERIFIED from
  source. `namespace WeierstrassCurve` (`ZSMul.lean:76`) → `namespace Universal`
  (`ZSMul.lean:86`); the lemma is on line 102, before `namespace Affine` (`ZSMul.lean:157`).
  The task's parsed qualified name is confirmed exactly.
  (NB: a *different* lemma `WeierstrassCurve.evalEval_φ_eq_eval_Φ` lives in
  `LutzNagell/LutzNagellTheorem/EvalBridge.lean:54` — not this decl; it was assessed
  separately in the ledger, also `NO-composable-from-mathlib`.)
- module docstring summary:  `ZSMul.lean` proves `WeierstrassCurve.zsmul_eq_smulEval`
  (`n • P = ⟦(φₙ, ωₙ, ψₙ)⟧` in Jacobian coords for any `n : ℤ` and nonsingular affine point
  `P = (x,y)` on `W/F`), via even-odd induction reducing to universal-ring polynomial
  identities specialized through `polyEval` / `ringEval`. `evalEval_φ` is one of six small
  "specialize a division polynomial and evaluate" glue lemmas
  (`evalEval_ψ₂, evalEval_Ψ₃, evalEval_preΨ₄, evalEval_ψ, evalEval_φ, evalEval_ω`,
  `ZSMul.lean:88–106`) feeding the cusp-curve nonvanishing trick.

---

### Statement (Phase 1)

`evalEval_φ` is a **lemma**. With `W : WeierstrassCurve R` (`R` a comm ring), `x y : R`,
`n : ℤ`, and `Universal.curve : Affine (MvPolynomial Coeff ℤ)` the universal Weierstrass
curve over `ℤ[A₁,A₂,A₃,A₄,A₆]`, it states

```lean
lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]
```

where:
- `W.φ n : R[X][Y]` is mathlib's `n`-th (numerator) division polynomial
  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:448`;
  the project's *fork* `LutzNagell/DivisionPolynomial.lean:371` has the identical def
  `C X * (W.ψ n)^2 - W.ψ (n+1) * W.ψ (n-1)`);
- `evalEval x y : R[X][Y] → R` is mathlib's bivariate evaluation `p ↦ eval x (eval (C y) p)`
  (`Mathlib/Algebra/Polynomial/Bivariate.lean:44`);
- `curve.φ n : Poly = (MvPolynomial Coeff ℤ)[X][Y]` is the **universal** `φ` (already a
  bivariate element of `Poly`, so — unlike `evalEval_Ψ₃` — no `C …` wrapping appears);
- `polyEval W x y : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y` is the
  **project-local** evaluation hom (`Universal.lean:203`) sending `Aᵢ ↦ W.aᵢ` and
  `(X,Y) ↦ (x,y)`.

Mathematically: **specializing the universal `φ` to `W` (via `Aᵢ ↦ W.aᵢ`) and evaluating at
`(x,y)` agrees with first forming `W.φ` and evaluating at `(x,y)`** — i.e. the division
polynomial `φₙ` is a *universal* polynomial in `ℤ[A₁..A₆][X][Y]` whose specialization
commutes with evaluation. This is the "`φ` row" of the six-lemma family.

Variables / typeclasses (Lean side):
- `{R : Type*}` `[CommRing R]` — base ring (`ZSMul.lean:80`).
- `(W : WeierstrassCurve R)` — supplies `W.specialize` / `W.φ`.
- `{x y : R}` — the affine point (`ZSMul.lean:84`).
- `{n : ℤ}` — the multiplier index (`ZSMul.lean:97`).

Hypotheses (Lean side): none. (No `Equation W x y` is needed — this is the `polyEval`
level, *before* passing to the coordinate ring `ringEval`.)

Conclusion (math): `φ`-evaluation commutes with specialization of the curve coefficients.
Conclusion (Lean): `(W.φ n).evalEval x y = polyEval W x y (curve.φ n)`.

Reading the proof (3 rewrites):
- `polyEval_apply` (project, `Universal.lean:206`; a 1-call wrapper of mathlib's
  `eval₂_eval₂RingHom_apply`) rewrites the RHS `polyEval W x y (curve.φ n)` to
  `((curve.φ n).map (mapRingHom W.specialize)).evalEval x y`;
- `← map_φ` (mathlib `@[simp]`, `Basic.lean:541`: `(W.map f).φ n = (W.φ n).map (mapRingHom f)`;
  the project's fork copy is `DivisionPolynomial.lean:464`) rewrites
  `(curve.φ n).map (mapRingHom W.specialize)` to `((curve.map W.specialize).φ n)`;
- `map_specialize` (project, `Universal.lean:194`: `curve.map W.specialize = W`) collapses
  `curve.map W.specialize` to `W`, giving `(W.φ n).evalEval x y`. ∎

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper glue lemma; not a named theorem, not a new structure, not a
`## Main results` entry. It is one row of an internal six-lemma specialization family that
exists only to bridge the project's universal-ring scaffolding to concrete evaluation.

(Literature width was run EXHAUSTIVE regardless; see Phase 3.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`simp_rw [polyEval_apply, ← map_φ, map_specialize]`).
One-liner verdict: **n/a — kind is `lemma`, not `def`/`abbrev`/`structure`.**
(The Phase-2b def-exemption table is for definitions; it does not apply. Recorded: this is
a one-line *proof*, reinforcing the composability signal in Phase 6.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomials Weierstrass curve universal polynomials integer coefficients specialization a1..a6" | yes  | division polys are universal polynomials in `ℤ[a₁..a₆,x,y]`; constructed over `Frac(ℤ[a₁..a₆])` (Lang) | confirms the *mathematical* universality; no named "specialization-commutes" lemma |
|  2 | WebSearch (general form)         | "division polynomial psi phi omega universal base change ring homomorphism compatible"                 | yes  | `[n]P = (φ/ψ², ω/ψ³)`, `φₙ = xψₙ² − ψₙ₋₁ψₙ₊₁`; base-change/functoriality treated as routine | literature states base-change compatibility informally, no named theorem |
|  3 | WebSearch (named-after / nLab)   | "nLab division polynomial elliptic curve / universal Weierstrass curve specialization morphism"        | yes  | nLab: Weierstrass eqn over general rings; **mathlib's `DivisionPolynomial/Basic` is itself surfaced as the canonical formalization** | the "universal morphism from a universal coefficient ring to the coordinate ring" is described as the *Lean/mathlib* construction, not a classical named result |
|  4 | ChatGPT MCP                      | "Is 'specialization commutes with the division polynomial' a named theorem, or routine base-change functoriality? Is `(W.map f).φ n = (W.φ n).map f` the standard statement?" | n/a  | —                   | **MCP unavailable** (Codex backend errored, as the task warned). Fallback channels (#1–#3, #6) answer both sub-questions: routine functoriality; `map_φ` is the natural statement. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                | n/a  | —                   | directory absent (only `overview/` exists under `.mathlib-quality/`) — recorded n/a |
|  6 | nLab                             | "elliptic curve" / "division polynomial"                                                               | yes  | Weierstrass equation over general rings; no isolated "specialize-commutes" statement | the property is the generic functoriality of the construction; nLab has no special name for it |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                   | not a categorical concept (it is a polynomial-identity / base-change fact about a concrete construction) |
|  8 | Stacks Project (if alg geom)     | division polynomial / Weierstrass universal curve                                                      | n/a  | —                   | Stacks has no division-polynomial chapter; the universal-curve-over-`ℤ[a_i]` idea is generic base change, covered by `Algebra → base change`, nothing decl-specific |
|  9 | MathOverflow / Math.StackExchange| division polynomial coefficients universal / base change                                              | yes  | universality of division-poly coefficients is folklore (Ward 1948; Silverman ex. III.3.7) | confirms folklore status; no named lemma |
| 10 | recent arXiv (last 5 years)      | "division polynomials for arbitrary isogenies" (Stange 2025); "sequences associated to elliptic curves" | yes  | recurrences / chain rules on source/target curves; base-change compatibility used freely, unnamed | modern work treats base-change/specialization compatibility as routine, never as a citable named theorem |

The protocol passed: WebSearch ran ≥3 queries at different generality (specific universal-
coefficient form, general φ/ψ/ω base-change form, named-after/nLab); nLab, Stacks, nCatLab,
MathOverflow, arXiv each checked or `n/a` with reason; local refs `n/a` (absent); ChatGPT
MCP `n/a` (backend down — the only forced miss, with two independent fallback channels
supplying the same answer).

### Literature summary (Phase 3)

Concept identified as: **division polynomials `φₙ` of a Weierstrass curve are universal
polynomials with integer coefficients in `a₁..a₆, x, y`** — hence "forming `φₙ` then
specializing/evaluating" commutes with "specializing the universal `φₙ`".
Sources agree on the standard form: **yes** — the universality of division-polynomial
coefficients is classical/folklore (Lang *Elliptic Curves*, Silverman *AEC* III.3.7 exercise,
Ward 1948). It is treated everywhere as **routine functoriality of the construction under
base change**, *never* as a separately-named theorem.
Most general standard form: for a ring hom `f : R → S` (equivalently base change),
`φₙ(W ×_R S) = f_*(φₙ(W))` — i.e. **the division polynomial commutes with base change**.
The project's "universal coefficient ring `ℤ[A₁..A₆]` + specialization map `specialize`"
is *one concrete way to package* this universality, but the literature/mathlib-idiomatic
packaging is the base-change/`map` statement.
Generality dimensions where the literature varies:
  - base object: from a single field/ring up to the universal ring `ℤ[a₁..a₆]` — but the
    statement is the same functoriality at every level.
Disagreement with the literature: **none.** The lemma is true and standard; it is just a
specialization-instance of the base-change compatibility (`(W.map f).φ n = (W.φ n).map f`),
specialized at `f = W.specialize` and `curve.map W.specialize = W`.

---

### Generality analysis — `WeierstrassCurve.Universal.evalEval_φ`

Literature-standard form (from Phase 3): division-polynomial base-change compatibility,
`(W.map f).φ n = (W.φ n).map f`, for any ring hom `f`. (Already in mathlib as `map_φ`.)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | comm ring `R`     | comm ring (division polys need `CommRing`) | NO | already the natural minimal class for division polynomials in mathlib |
| 2 | `W : WeierstrassCurve R` | over `R`        | over any base; universality handled by base change | NO (at this packaging) | the subject is already `W` over arbitrary `R` |
| 3 | `polyEval W x y` (subject) | bespoke project hom `ℤ[A₁..A₆,X,Y] → R` | a base-change ring hom `f : R → S` | n/a — this is the *packaging*, not a parameter to weaken | the `polyEval`/`specialize`/`curve` apparatus is the non-idiomatic part; mathlib expresses the content via `map_φ` directly (Phase 4c) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** on its parameters (`R` an arbitrary comm ring,
`n : ℤ` arbitrary, `x y` arbitrary, no `Equation` hypothesis).
Number of weakening opportunities found: 0.
Proposed restatement: none on generality grounds.
Cost of restatement: n/a.

(The form is general; the issue is *packaging*, addressed in 4c — but 4c does not flip the
verdict because the idiomatic form `map_φ` **already exists in mathlib**, so the move is
"delete + use mathlib", i.e. a NO bucket, not "generalise-first".)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | the hyps are already typeclass-driven |
|  2 | sequences/metric → filters/topological? | no | — | no analytic content |
|  3 | construct an object → universal-property class? | **partially, but already done upstream** | the universal content is "`φ` commutes with base change", i.e. mathlib's `map_φ`; the project's universal-ring `polyEval` is a *re-construction* of what `map_φ` already abstracts | n/a — the abstraction (`map_φ`) is already in mathlib; nothing new to add |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | not a substructure question |
|  5 | vector-space/field-specific → weaken typeclasses? | no | — | already `CommRing` |
|  6 | 1-categorical → higher-categorical? | no | — | concrete polynomial identity |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | `n : ℤ` is intrinsic to division-polynomial indexing | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no (as a new mathlib contribution).** The contemporary, idiomatic
expression of this lemma's content is *base-change compatibility of `φₙ`* — and mathlib
already provides it as `WeierstrassCurve.map_φ`. The project's `polyEval`/`specialize`/
`Universal.curve` layer is project-internal scaffolding that re-packages this fact; it is
not a modernisation move that mathlib lacks. Therefore 4c does **not** push toward
YES-but-generalise-first — the idiomatic target is already upstream, which is a NO-bucket
signal (Phase 5/6).

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** (No definitional equalities or typeclass-search
paths are introduced by a proof.)

---

### Mathlib search-status: `WeierstrassCurve.Universal.evalEval_φ`

[A] Lean-Finder       "division polynomial commutes with base change / specialization"; "evalEval of division polynomial"   no decl matching the `polyEval`/specialize-of-universal-curve form (that apparatus is not in mathlib). The base-change fact surfaces as `map_φ`.
[B] Loogle            `(WeierstrassCurve.φ _ _).evalEval _ _ = _`; `WeierstrassCurve.φ (WeierstrassCurve.map _ _) _ = _`   **no hit** for any `evalEval (φ …) = polyEval …` lemma; the only structural relative is `map_φ` (`(W.map f).φ n = (W.φ n).map (mapRingHom f)`).
[C] LeanSearch        "n-th division polynomial of base-changed Weierstrass curve equals base change of division polynomial"; "evaluate division polynomial after specializing coefficients"   surfaces `WeierstrassCurve.map_φ` (the base-change statement); **no** `evalEval`/`polyEval` specialization lemma.
[D] Grep mathlib src  `grep -rn "evalEval_φ\|evalEval_ψ\|polyEval\|\.evalEval x y =" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/`   **no `evalEval_φ`/`evalEval_ψ`/`polyEval` anywhere in mathlib.** The only `evalEval_*` lemmas are for the *polynomial itself* (`evalEval_polynomial`, `evalEval_polynomialX`, `evalEval_polynomialY`, `evalEval_negPolynomial` in `Affine/Basic.lean` + `Affine/Formula.lean`) — never for the division-polynomial family, never in a "specialize the universal curve" form. `grep -rln "Universal.curve\|Universal.Ring\|namespace Universal" …/EllipticCurve/` → **no hits** (the `Universal` apparatus is project-only). `grep "def specialize"` in `…/EllipticCurve/` → none (mathlib's `map_specialize` is an unrelated topology/scheme concept).
[E] Name pattern      `lean_local_search`/grep: `evalEval_φ`, `evalEval_ψ`, `polyEval`, `specialize`, `Universal.evalEval` across mathlib   **no hits** — the entire `evalEval_*` division-poly family + `polyEval` + `specialize`(EC) + `Universal.curve` live only in `projects/NagellLutz/LutzNagell/` (and the parallel HasseWeil fork).

Searched for both:
  - the user's current form (`(W.φ n).evalEval x y = polyEval W x y (curve.φ n)`) — not in mathlib (subject `polyEval`/`curve` are project-local);
  - the literature-standard form (base-change compatibility `(W.map f).φ n = (W.φ n).map f`) — **found in mathlib as `WeierstrassCurve.map_φ`**, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:541`.

Concluded: **found the building blocks** — mathlib has `WeierstrassCurve.map_φ`
(`Basic.lean:541`) and `Polynomial.eval₂_eval₂RingHom_apply` (the engine behind the
project's `polyEval_apply`). The exact lemma is **not** in mathlib because its statement is
phrased in terms of the project-local `polyEval` / `Universal.curve`, which mathlib does not
contain. A 3-rewrite composition of these blocks (plus the project's own `map_specialize`)
yields the lemma — see Phase 6.

---

### Call sites — `WeierstrassCurve.Universal.evalEval_φ`

Internal use count (NagellLutz, excluding the declaring file `ZSMul.lean`): **0**
External-to-file callers (NagellLutz): **0** distinct files.
In-file: also **unused** — within `ZSMul.lean`, only the siblings
`evalEval_ψ₂` / `evalEval_Ψ₃` / `evalEval_preΨ₄` are consumed (lines 115, 123, in
`polyEval_cusp_ψ` / `polyEval_cusp_ψc`); `evalEval_φ`, `evalEval_ψ`, and `evalEval_ω` are
declared but **not referenced anywhere in the file** (confirmed by
`grep -n "evalEval_φ" ZSMul.lean` → only the def line 102; and the project's own overview
inventory `inventory/LutzNagell_ZSMul.md` records "Used by: unused in file", "Uses from
project: []").

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| (none in NagellLutz) | — |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `evalEval_φ`?):
  - `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:177` — the **identical**
    lemma `evalEval_φ` is re-declared verbatim (same statement, same proof) in the HasseWeil
    fork. This is duplication across the two forking projects, not a downstream consumer of
    *this* decl. It reinforces NO (the content is shared scaffolding, recreated rather than
    imported), and it is itself project-local, not mathlib.
  - No other inline re-derivation found.

Call-sites signal: **K = 0 internal uses, and the same statement is re-derived (duplicated)
in a sibling project.** Per the Phase-6 signal table, this is the
"NO-composable-from-mathlib (or NO-mathlib-has-it)" pattern: a thin universal-ring wrapper
that is either unused or recreated, whose content already lives in mathlib (`map_φ`).

---

### Composition check (Phase 6)

Can `evalEval_φ` be derived from mathlib (+ the project's own `polyEval_apply`/`map_specialize`,
which are themselves ≤1-call wrappers of mathlib) in ≤3 chained calls?

Attempt 1: the existing proof body **is** the composition —
  `simp_rw [polyEval_apply, ← map_φ, map_specialize]`.
  - Building blocks used:
    - `Universal.polyEval_apply` (`Universal.lean:206`) — 1-call wrapper of mathlib
      `Polynomial.eval₂_eval₂RingHom_apply`;
    - `WeierstrassCurve.map_φ` (mathlib, `Basic.lean:541`);
    - `Universal.map_specialize` (`Universal.lean:194`, `curve.map W.specialize = W`).
  - Result: **succeeds** — exactly 3 rewrites, no `ring`/`aesop`/non-trivial reasoning between.
  - Notes: this is a genuine composition (three `rw`-style rewrites), not a proof in disguise.

Conclusion: **COMPOSABLE.** The lemma is a ≤3-rewrite glue over `map_φ` (mathlib) +
`polyEval_apply` + `map_specialize` (project, each itself ≤1 mathlib call). No new lemma is
justified *for mathlib* — but note (Phase 7) the subject is project-local, so the canonical
NO action is "use mathlib `map_φ` directly / inline", not "PR this lemma".

---

## Verdict: `WeierstrassCurve.Universal.evalEval_φ`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the universality/base-change compatibility of `φₙ` is
  classical folklore (Lang, Silverman III.3.7, Ward 1948), never a separately-named theorem;
  the idiomatic statement is base-change compatibility.
- Generality analysis (Phase 4): MAXIMALLY GENERAL on parameters; 4c found the idiomatic
  form is mathlib's `map_φ` (already upstream), so not a generalise-first case.
- Mathlib search (Phase 5): the exact form is **not** in mathlib (subject `polyEval`/
  `Universal.curve` are project-local); building blocks `WeierstrassCurve.map_φ`
  (`Basic.lean:541`) and `Polynomial.eval₂_eval₂RingHom_apply` are present.
- Composition check (Phase 6): **COMPOSABLE** — the existing 3-rewrite proof
  `simp_rw [polyEval_apply, ← map_φ, map_specialize]` is itself the composition.

**Rationale:**

The lemma's mathematical content — "the division polynomial `φₙ` is a universal polynomial
in the Weierstrass coefficients, so specializing the curve and evaluating commutes" — is
exactly mathlib's `WeierstrassCurve.map_φ` (`(W.map f).φ n = (W.φ n).map (mapRingHom f)`),
the base-change/functoriality statement, instantiated at the specialization map and combined
with the project's `curve.map W.specialize = W`. The proof is a literal three-rewrite
composition with no nontrivial reasoning step, so by the `/mathlibable` heuristics it is a
*composition*, not a lemma that earns its place in mathlib. Crucially, the **statement itself
mentions the project-local `polyEval` and `Universal.curve`**, neither of which exists in
mathlib (verified: `grep` finds no `polyEval`, no EC-`specialize`, no `Universal.curve`
anywhere in `Mathlib/AlgebraicGeometry/`). So the lemma cannot be upstreamed *as written* —
its subject is downstream scaffolding — and it does not need to be: the upstreamable content
(`map_φ`) is already upstream. The call-sites picture confirms the disposition: **zero uses
within NagellLutz** (even in its own file `evalEval_φ` is declared-but-unused), and the
identical lemma is **re-derived verbatim** in the HasseWeil fork — a thin universal-ring
wrapper that is either unused or duplicated, not a piece of API that consumers depend on.
This matches the sibling `WeierstrassCurve.Universal.evalEval_Ψ₃`, assessed
`NO-composable-from-mathlib` earlier in this same overview run (and the whole six-lemma
family shares this disposition).

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the lemma is a ≤3-call composition. The one upstreamable
block, `WeierstrassCurve.map_φ` (the base-change compatibility of the `φ` division
polynomial), already lives in mathlib. The remaining two rewrites (`polyEval_apply`,
`map_specialize`) are *about the project's own `polyEval`/`specialize`/`Universal.curve`
apparatus*, which is intentionally project-local (the Nagell–Lutz "universal pointed curve"
machinery in `Universal.lean`). So this lemma belongs in the project, not in mathlib; nothing
about it is a missing mathlib API.

Mathlib building blocks:
  - `WeierstrassCurve.map_φ` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:541`
  - `Polynomial.eval₂_eval₂RingHom_apply` — `Mathlib/Algebra/Polynomial/Bivariate.lean`
    (the engine behind the project's `polyEval_apply`)
Project glue used (project-local, correctly so):
  - `WeierstrassCurve.Universal.polyEval_apply` — `Universal.lean:206`
  - `WeierstrassCurve.Universal.map_specialize` — `Universal.lean:194`

Composition sketch (≤3 lines — the existing proof):
```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} {n : ℤ} :
    (W.φ n).evalEval x y = Universal.polyEval W x y (Universal.curve.φ n) := by
  simp_rw [Universal.polyEval_apply, ← WeierstrassCurve.map_φ, Universal.map_specialize]
```

Call sites in this project (from Phase 6.0): **K = 0** (unused, including in-file).

Refactor plan:
  - Because K = 0 in NagellLutz, the lemma is currently **dead weight**. The cleanest action
    is to **delete `WeierstrassCurve.Universal.evalEval_φ`** from `ZSMul.lean` (along with the
    equally-unused siblings `evalEval_ψ` and `evalEval_ω`, both also K = 0 — `evalEval_ψ₂`/
    `evalEval_Ψ₃`/`evalEval_preΨ₄` ARE used at lines 115/123 and must stay). Confirm with a
    `lake build` after removal.
  - If any of these are intended as *exported convenience API* for the broader project (the
    HasseWeil fork duplicates `evalEval_φ`), the right move is to **lift the shared
    `Universal`/`polyEval` scaffolding into `Common/`** and import it from both projects,
    rather than re-declaring `evalEval_φ` verbatim in each — but that is an AINTLIB
    dedup/`Common/` decision (a cleanup-ticket concern), **not** a mathlib contribution.
  - At any genuine call site that wants the base-change fact about `φ` directly (none today),
    use mathlib's `WeierstrassCurve.map_φ` rather than this wrapper.

This is **not** a YES bucket (the upstreamable content is already in mathlib as `map_φ`, and
the lemma's subject is project-local scaffolding), and **not** NO-mathlib-has-it (mathlib does
not have *this exact statement* — it can't, since `polyEval`/`curve` are downstream — only its
building block `map_φ`). NO-composable-from-mathlib is the correct bucket.

---

## Next step

Delete `WeierstrassCurve.Universal.evalEval_φ` from `projects/NagellLutz/LutzNagell/ZSMul.lean`
(it is unused, K = 0, even in-file), together with the equally-unused siblings `evalEval_ψ`
and `evalEval_ω`; keep `evalEval_ψ₂`/`evalEval_Ψ₃`/`evalEval_preΨ₄` (used at lines 115/123).
Re-`lake build`. If the `Universal`/`polyEval` scaffolding is genuinely shared with HasseWeil
(which duplicates `evalEval_φ` verbatim), file an AINTLIB cleanup ticket to lift it into
`Common/` instead of re-declaring it per project. Do **not** open a mathlib PR for this lemma;
its upstreamable content already exists as `WeierstrassCurve.map_φ`.
