# /mathlibable report — `WeierstrassCurve.evalEval_ψ_odd`  (lowercase ψ; EvalBridge.lean:68)

> FILENAME NOTE: the target `evalEval_ψ_odd` (lowercase ψ, on-curve lemma, line 68) and its twin
> `evalEval_Ψ_odd` (capital Ψ, pure-unfolding lemma, line 62) differ only by letter case. On this
> case-insensitive (macOS) filesystem they map to ONE filename, so the canonical report for the
> **lowercase** target lives here as `evalEval_psi_odd.md` to avoid clobbering `evalEval_Ψ_odd.md`
> (the capital-Ψ twin's report). The task asked to write `evalEval_ψ_odd.md`; that path *is* the
> capital twin's file on this FS, so writing the lowercase report there would destroy the twin —
> hence this canonical disambiguated filename instead.
>
> Step-9 (overview) mathlibable assessment, single declaration, full workflow.
> Local Lean build is stale; assessment reasons from the source statement and is cross-checked
> against the **actual upstream mathlib source** present under `.lake/packages/mathlib/`.
> Literature via WebSearch (3 queries at different generality levels); ChatGPT MCP unavailable in
> this thread — substituted by primary-source mathlib reads + the standard references.
>
> SUPERSEDES the earlier BORDERLINE write-up of this same decl (see "Reconciliation" at the end):
> the corrected verdict is NO-composable-from-mathlib, made consistent with the rest of the family.

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (build stale per task brief; decl read directly from source).
                            All mathlib claims verified against `.lake/packages/mathlib/` source.
- decl `WeierstrassCurve.evalEval_ψ_odd`:  ✓ resolved at
                            `projects/NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:68`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Eval bridge lemmas for Lutz–Nagell" — bridges the coordinate-ring
                             congruence lemmas (`mk_ψ`, `mk_φ`, `mk_Ψ_sq`) to concrete equalities
                             after evaluating bivariate polynomials at an on-curve point `(x, y)`.

**True qualified name (verified):** `WeierstrassCurve.evalEval_ψ_odd`
(namespace `WeierstrassCurve` opened at EvalBridge.lean:24; lowercase ψ; the brief's parsed name is correct.)

---

### Statement (Phase 1)

`WeierstrassCurve.evalEval_ψ_odd` states: let `W` be a Weierstrass curve over a field `F`, let `(x, y)`
satisfy the affine Weierstrass equation of `W`, and let `n` be an **odd** integer. Then the `n`-th
bivariate division polynomial `ψₙ ∈ F[X][Y]`, evaluated at `(x, y)`, equals the univariate auxiliary
polynomial `preΨₙ ∈ F[X]` evaluated at `x`:

  ψₙ(x, y) = preΨₙ(x).

Mathematically: on the curve, at odd index, the bivariate `n`-division polynomial collapses to a
polynomial in the `x`-coordinate alone (the classical "x-only" form). This is the fact that powers the
prime-order integrality step of Nagell–Lutz: for odd order the `x`-coordinate is a root of the
univariate division polynomial whose leading coefficient is `n`.

Variables / typeclasses (Lean side):
- `{F : Type*} [Field F]` — base field.
- `(W : WeierstrassCurve F)` — the curve.
- `{x y : F}` — coordinates of the point.
- `(n : ℤ)` — division index.

Hypotheses (Lean side):
- `(heq : W.toAffine.Equation x y)` — `(x, y)` lies on the curve. ← KEY difference from twin `evalEval_Ψ_odd`
- `(hodd : ¬Even n)` — `n` is odd.

Conclusion (math): ψₙ(x, y) = preΨₙ(x).
Conclusion (Lean): `(W.ψ n).evalEval x y = (W.preΨ n).eval x`.

Proof body (1 line, EvalBridge.lean:70):
```lean
rw [evalEval_ψ_eq_evalEval_Ψ W heq, evalEval_Ψ_odd W n hodd]
```
i.e. the composition of two already-named sibling lemmas from the same file:
`evalEval_ψ_eq_evalEval_Ψ` (ψ ≡ Ψ on the curve, line 42) then `evalEval_Ψ_odd` (Ψ collapses to
`C preΨ` at odd n, line 62).

> Relation to the twin `evalEval_Ψ_odd` (line 62): that one is `(Ψ n).evalEval x y = (preΨ n).eval x`
> with **no `heq`** (pure unfolding of the def of `Ψ`). THIS one is about `ψ` (lowercase), needs the
> on-curve hypothesis, and equals (`evalEval_ψ_eq_evalEval_Ψ`) ∘ (`evalEval_Ψ_odd`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a corollary / specialisation — the odd-`n` evaluation collapse for `ψ`, derived in one `rw`
from two sibling lemmas. Not a new structure, not a named theorem; the project's `## Main results`
headline is the Nagell–Lutz theorem itself, of which this is plumbing.
(Literature width is EXHAUSTIVE regardless; recorded for framing.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. (The proof body is a single `rw`, which is
the dominant signal feeding Phases 6–7: this is a glue/composition lemma.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                       | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific / odd-index) | elliptic curve division polynomial odd index univariate in x Nagell–Lutz                    | yes  | for **odd** n, ψₙ ∈ k[x]; even n carries a factor of ψ₂; "shorter Nagell–Lutz proof uses only division polys" | Alpöge "Nagell–Lutz, quickly"; Anqi Li 18.784; MIT 18.783 PS3; Magma handbook; Moody eprint 2010/630; Wikipedia "Nagell–Lutz" |
|  2 | WebSearch (general / eval form)  | division polynomial ψₙ evaluated at point on curve coordinate ring substitute Weierstrass eqn | yes  | "evaluate only on points of the curve; substitute (2y+a₁x+a₃)²=4x³+b₂x²+b₄x+b₆ ⇒ φₙ,ψₙ²∈ℤ[x,…]" | arXiv 2102.07573, 1108.3051, 1303.4327; the substitution slogan verbatim |
|  3 | WebSearch (named-after/aliases)  | WeierstrassCurve division polynomial evalEval coordinate ring AdjoinRoot Lean mathlib        | yes  | confirms mathlib's own design note (evaluate at a point ↔ congruence mod the curve eqn) | mathlib4 `DivisionPolynomial/Basic` docstring; building blocks `AdjoinRoot.evalEval`, `mk_ψ`, `evalEval_mk` exist |
|  4 | ChatGPT MCP                      | "is ψₙ(x,y)=preΨₙ(x) (odd n) a named theorem or a routine corollary of congruence-mod-curve?"| n/a  | — (MCP unavailable this thread)                       | fallback = primary-source mathlib reads + channels 1–2; all sources treat it as routine |
|  5 | Local references                 | `.mathlib-quality/references/` and `refs/` for "division polynomial" / "Nagell"             | n/a  | (no references dir present for this project)           | dir absent — recorded n/a |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                     | no   | no dedicated nLab page                                 | classical AG, not categorical |
|  7 | nCatLab (if categorical)         | —                                                                                           | n/a  | not a categorical concept                              | evaluation of a concrete polynomial at a point |
|  8 | Stacks Project (if alg geom)     | "division polynomial"                                                                        | no   | Stacks has no division-poly / EDS material             | n/a — scheme-theoretic foundations, not curve-torsion polynomials |
|  9 | MathOverflow / MSE               | division polynomial odd is univariate in x on the curve                                      | yes  | folklore: "on the curve y² is rewritten; odd ψₙ ∈ k[x]" | exercise-level; no canonical name |
| 10 | recent arXiv (≤5y)               | division polynomials evaluated at points; "homogeneous division polynomials" (1303.4327)     | yes  | reaffirms classical evaluation/substitution setup      | modern treatments; same fact, no new name |

### Literature summary (Phase 3)

Concept identified as: **the n-division polynomial evaluated at a rational point on the curve**, and
specifically the classical fact that on the curve the **odd** division polynomial is univariate in `x`
(the "x-only" form). Sources: Silverman *AEC* (the reference mathlib's file cites), Wikipedia, the
p-adic / EDS literature (arXiv 2102.07573, math/0404412), Magma, Moody (2010/630), and the
Nagell–Lutz expositions that build the *entire* theorem out of this (Alpöge "Nagell–Lutz, quickly";
Anqi Li; MIT 18.783).

Sources agree on the standard form: **yes** — `ψₙ(P)` is the canonical object; for odd `n` it is a
polynomial in `x` only (even `n` carries exactly one factor `ψ₂ = 2y + a₁x + a₃`). That is *exactly*
`evalEval_ψ_odd`. The evaluation-on-the-curve step is performed by substituting the Weierstrass
equation — precisely what `AdjoinRoot.evalEval` / `Equation` encode in mathlib.

Most general standard form: the algebraic identity holds over any **CommRing** `R` for `(x,y)`
satisfying the Weierstrass equation; a field is needed only downstream (integrality/torsion), not for
this identity.

Disagreement with the literature: **none**. The Lean statement faithfully (if specialised to `Field`)
renders a standard fact that every source treats as an immediate corollary — **not** a named theorem.
Notably, mathlib's own `DivisionPolynomial/Basic.lean` docstring states the intent verbatim
("evaluating these polynomials at a rational point on `W` recovers their original definition up to
linear combinations of the Weierstrass equation … avoiding the need to work in the coordinate ring"),
so mathlib *anticipates* this bridge but ships no `evalEval` lemma for it.

---

### Generality analysis — `WeierstrassCurve.evalEval_ψ_odd`

Literature/mathlib-uniform target: **CommRing R**. Mathlib's `ψ`, `Ψ`, `preΨ`, the congruences
`mk_ψ` etc., `AdjoinRoot.evalEval_mk`, and `evalEval_C` are all stated over `[CommRing R]`.

| # | Parameter / hypothesis     | Current Lean form | Literature/mathlib-standard | Weaker form? | Reason |
|---|----------------------------|-------------------|------------------------------|--------------|--------|
| 1 | `[Field F]`                | base field        | arbitrary `CommRing R`       | **yes**      | The identity is just the coordinate-ring congruence + the def of `Ψ`; no inverses/char/domain used. Every building block is `CommRing`. |
| 2 | `(heq : …Equation x y)`    | on-curve point    | same (`polynomial.evalEval x y = 0`) | no   | Essential — `AdjoinRoot.evalEval_mk` needs the equation to vanish. `Equation` is *defeq* to `polynomial.evalEval x y = 0` (Affine/Basic.lean:149), so the composition needs no massaging. |
| 3 | `(n : ℤ)`, `¬Even n`       | odd index         | same                         | no           | "odd" is exactly what collapses the `if Even n` branch of `Ψ` to `1`. |

### Generality verdict (Phase 4b)

Current form is **STRICTLY NARROWER THAN STANDARD** on one axis (`Field F` → `CommRing R`).
Weakening opportunities: **1**. Restatement (proof unchanged):
```lean
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
theorem evalEval_ψ_odd (heq : W.toAffine.Equation x y) (n : ℤ) (hodd : ¬Even n) :
    (W.ψ n).evalEval x y = (W.preΨ n).eval x := by
  rw [evalEval_ψ_eq_evalEval_Ψ W heq, evalEval_Ψ_odd W n hodd]
```
Cost: **CHEAP** — the `Field` is an artifact of the file's `variable` block; the whole `EvalBridge.lean`
family inherits this same gap.

*Bearing on the verdict:* this only matters for a YES path. As Phase 6 establishes the lemma is
COMPOSABLE (mathlib already has the pieces), the verdict is a NO bucket, for which the
`Field → CommRing` point is moot — the lemma is not added to mathlib at any generality.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | "let X be a foo" → typeclass? | no | — | already typeclass-based |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic polynomial identity, no analysis |
| 3 | construct → universal property? | no | — | the universal-ring construction is already upstream; this is its evaluation |
| 4 | set+closure-pred → bundled substructure? | no | — | no substructure |
| 5 | field/metric-specific → weaken typeclass? | **yes** | `Field F` → `CommRing R` (= 4b) | ring-level eval bridge composes with mathlib's universal-ring & base-change EDS API |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general structure? | no | — | `n : ℤ` is already the right index (EDS are ℤ-indexed) |

Modern-idiom verdict: only the `Field → CommRing` weakening (row 5), already in 4b. It is a
correctness-of-generality move, not a reformulation. Not decisive, since the verdict is NO-composable.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`.

---

### Mathlib search-status: `WeierstrassCurve.evalEval_ψ_odd`

[A] Lean-Finder / [B] Loogle / [C] LeanSearch — index tools not callable in this thread; substituted by
    direct mathlib-source grep ([D]) over the locally-present `.lake/packages/mathlib/` tree.
[B] Loogle (intent) `(WeierstrassCurve.ψ _).evalEval _ _ = (WeierstrassCurve.preΨ _).eval _`   → no hit
[D] Grep mathlib src
    - `evalEval` in `EllipticCurve/DivisionPolynomial/*`        → **NO hits** (0 evalEval lemmas in the whole dir)
    - `evalEval` re ψ/Ψ/preΨ/φ/Φ anywhere in `Mathlib/`        → **NO hits** (mathlib has no evalEval lemma about any division polynomial)
    - `ψ_odd`/`Ψ_odd`/`preΨ_odd` in mathlib                    → hits, but these are **recurrence** lemmas (value at `2m+1` via lower indices), NOT the "odd ⇒ univariate" collapse. Different content.
    - `evalEval_polynomial(X/Y)` in `Affine/Basic.lean`        → hits, but evaluate the **Weierstrass polynomial** & its partials, never the division polys
    - mk→evalEval bridge (`evalEval_eq_of_mk_eq`-like)         → **NO hits** in mathlib
[E] Name pattern `evalEval_ψ`/`evalEval_Ψ`/dot-notation        → **NO hits** in mathlib

Searched for BOTH the current `Field` form and the more general `CommRing` form — neither is in mathlib.

Building blocks confirmed present in mathlib (verified line numbers, this pin):
  - `Polynomial.evalEval` (abbrev) + `Polynomial.evalEval_C` — `Mathlib/Algebra/Polynomial/Bivariate.lean:44, 49`
  - `AdjoinRoot.evalEval` + `AdjoinRoot.evalEval_mk` — `Bivariate.lean:388, 391` (the genuine `mk`→eval bridge primitive)
  - `WeierstrassCurve.Ψ` def `= C (preΨ n) * if Even n then ψ₂ else 1` — `DivisionPolynomial/Basic.lean:290–291` (**byte-identical** to the project fork)
  - `WeierstrassCurve.Affine.CoordinateRing.mk_ψ : mk W (W.ψ n) = mk W (W.Ψ n)` — `Basic.lean:438`
  - `WeierstrassCurve.Affine.Equation` `:= W.polynomial.evalEval x y = 0` — `Affine/Basic.lean:149` (defeq to `evalEval_mk`'s hypothesis)

Concluded: **not in mathlib** (all methods exhausted, both forms). Mathlib has the *building blocks*
(`AdjoinRoot.evalEval_mk`, `mk_ψ`, the def of `Ψ`, `evalEval_C`) but not the `evalEval`-of-division-
polynomial bridge nor its odd-`n` specialisation.

> FORK NOTE: `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` is a *verbatim copy* of
> `Mathlib.…DivisionPolynomial.Basic` (identical header/docstring/`Ψ`/`preΨ`/`mk_ψ` definitions),
> forked ONLY to import the project's expanded `EllipticDivisibilitySequence` and dodge
> `normEDS`/`complEDS` name clashes. So `evalEval_ψ_odd` is stated against polynomials definitionally
> identical to mathlib's; the fork is not a mathematical divergence and does not affect the verdict.

---

### Call sites — `WeierstrassCurve.evalEval_ψ_odd`

Internal use count: **2** (within NagellLutz, excluding EvalBridge.lean).
External-to-file callers: **2 distinct files** (the duplicated General* / PID* tracks).

| Caller file:line                              | Usage pattern (one-line excerpt)                                       |
|-----------------------------------------------|------------------------------------------------------------------------|
| LutzNagellTheorem/GeneralPrimeOrder.lean:88   | `rw [evalEval_ψ_odd (curveQ W) hns.left (p : ℤ) hodd_int] at hψ`       |
| LutzNagellTheorem/PIDPrimeOrder.lean:121      | `rw [evalEval_ψ_odd (curveK R K W) hns.left (p : ℤ) hodd_int] at hψ`   |

Both sites are the SAME step (the General-field / PID duplicate of one mathematical argument): rewrite
`ψ_p(x,y) = 0` into `preΨ_p(x) = 0` so the odd-prime integrality argument (leading coeff of `preΨ_p`
is `p`) can run. So distinct *mathematical* demand = 1, realised at 2 sites by track duplication.

Inline-derivation grep (re-derived without `evalEval_ψ_odd`?): **(none)** — both consumers use the
named lemma; no site re-derives the ψ→preΨ collapse inline.

Sibling EvalBridge.lean family (all already assessed in this overview; ledger verdicts):
  - `evalEval_eq_of_mk_eq` — **NO-composable** (= `AdjoinRoot.evalEval_mk` + `congrArg`, 2 calls)
  - `evalEval_ψ_eq_evalEval_Ψ` — **NO-composable** (= `AdjoinRoot.evalEval_mk` + `mk_ψ`) ← first half of THIS lemma
  - `evalEval_Ψ_odd` — **NO-composable** (`simp only [Ψ, if_neg hodd, mul_one, evalEval_C]`) ← second half of THIS lemma
  - `evalEval_Ψ_sq_eq_eval_ΨSq` — **NO-composable**
  - `evalEval_φ_eq_eval_Φ` — **NO-composable**

Signal: K=2 external callers, no inline re-derivation → a real used corollary *within the project*. But
the two callers are the General/PID duplicate of one step, and the lemma is a thin specialisation whose
two constituent halves are *each* independently NO-composable (see Phase 6).

---

### Composition check (Phase 6)

Can `evalEval_ψ_odd` be derived in ≤3 chained calls?

Attempt 1 — the lemma's own proof (composition of two siblings):
```lean
rw [evalEval_ψ_eq_evalEval_Ψ W heq, evalEval_Ψ_odd W n hodd]
```
A 2-`rw` chain, no reasoning between. Textbook ≤3-call composition — **of the two sibling lemmas**.

Attempt 2 — expand both halves to PURE mathlib (what a mathlib call site would write). The two halves
are *each* a clean mathlib composition (per the family's own NO-composable verdicts):
  - `evalEval_ψ_eq_evalEval_Ψ` = `AdjoinRoot.evalEval_mk` (with `p := W.toAffine.polynomial`, hyp `heq`
    defeq) transporting `Affine.CoordinateRing.mk_ψ` — 2 mathlib lemmas.
  - `evalEval_Ψ_odd` = `simp only [WeierstrassCurve.Ψ, if_neg hodd, mul_one, evalEval_C]` — the def of
    `Ψ` + the mathlib lemma `evalEval_C`.
Combined, a fully-inlined mathlib derivation:
```lean
example (heq : W.toAffine.Equation x y) (n : ℤ) (hodd : ¬Even n) :
    (W.ψ n).evalEval x y = (W.preΨ n).eval x := by
  have hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq   -- mathlib
  rw [← hev (W.ψ n), Affine.CoordinateRing.mk_ψ W n, hev (W.Ψ n),       -- mathlib mk_ψ + evalEval_mk
      WeierstrassCurve.Ψ, if_neg hodd, mul_one, evalEval_C]             -- def Ψ + mathlib evalEval_C
```
Mathlib pieces: `AdjoinRoot.evalEval_mk`, `Affine.CoordinateRing.mk_ψ`, `evalEval_C` (+ the def of `Ψ`,
`if_neg`, `mul_one`). Result: **succeeds**. Fully inlined it is a `have` + multi-step `rw` (a small
proof), but the natural call-site form is the 2-line "rewrite by each half", and **each half is itself
a sub-3-call mathlib composition already ruled NO-composable for this exact project.**

Conclusion: **COMPOSABLE.** The honest reading: `evalEval_ψ_odd` is the odd-`n` specialisation of
`evalEval_ψ_eq_evalEval_Ψ`, one `evalEval_Ψ_odd` rewrite away — and both of those are NO-composable
mathlib compositions. There is no new mathematical content here that mathlib's primitives don't already
deliver; only the convenience of bundling two composable steps under one name.

---

## Verdict: `WeierstrassCurve.evalEval_ψ_odd`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the "odd ψₙ is univariate in x on the curve" fact is classical and
  ubiquitous (Silverman, Wikipedia, Magma, the Nagell–Lutz expositions that build the whole theorem on
  it) — but treated everywhere as a *routine corollary of substituting the Weierstrass equation*, never
  a named theorem. Mathlib's own `DivisionPolynomial/Basic` docstring states the intent.
- Generality analysis (Phase 4): STRICTLY NARROWER (`Field F` should be `CommRing R`; cheap) — moot for
  a NO bucket (not added to mathlib).
- Mathlib search (Phase 5): **not in mathlib**; **all building blocks present** —
  `AdjoinRoot.evalEval_mk` (`Bivariate.lean:391`), `Affine.CoordinateRing.mk_ψ` (`Basic.lean:438`),
  `evalEval_C` (`Bivariate.lean:49`), the def of `Ψ` (`Basic.lean:290`), `Equation ↔ evalEval = 0`
  (`Affine/Basic.lean:149`).
- Composition check (Phase 6): **COMPOSABLE** — its two halves (`evalEval_ψ_eq_evalEval_Ψ`,
  `evalEval_Ψ_odd`) are *each* independently NO-composable mathlib compositions; their 2-`rw` chain is
  this lemma.

**Rationale:**

`evalEval_ψ_odd` is a one-line `rw` that chains two sibling lemmas, and both of those siblings were
themselves assessed in this same overview as `NO-composable-from-mathlib`: `evalEval_ψ_eq_evalEval_Ψ`
(= `AdjoinRoot.evalEval_mk` ▸ `Affine.CoordinateRing.mk_ψ`) and `evalEval_Ψ_odd` (= `simp only [Ψ,
if_neg hodd, mul_one, evalEval_C]`). A composition of two NO-composable mathlib compositions is itself a
NO-composable mathlib composition: mathlib already exports every primitive — the `mk`→eval transport
(`AdjoinRoot.evalEval_mk`), the coordinate-ring congruence (`mk_ψ`), the constant-evaluation lemma
(`evalEval_C`), and the def of `Ψ` whose `if Even n` branch the oddness collapses. Nothing new is
proved; the lemma only bundles two composable steps for the convenience of the two duplicated call
sites. Mathlib's own division-polynomial module docstring names the underlying fact ("evaluating these
polynomials at a rational point on `W` recovers their original definition … avoiding the coordinate
ring"), so this is library slogan, not new content.

This also makes the family verdict internally consistent: all five other EvalBridge members
(`evalEval_eq_of_mk_eq`, `evalEval_ψ_eq_evalEval_Ψ`, `evalEval_Ψ_odd`, `evalEval_Ψ_sq_eq_eval_ΨSq`,
`evalEval_φ_eq_eval_Φ`) are `NO-composable-from-mathlib`; `evalEval_ψ_odd` — strictly *more* composable
than any of them, being their downstream chain — is the same. The earlier BORDERLINE on this single
member raised a grain/policy question ("upstream the bridge family as a group?") that is identical for
all six members and does not single this one out; per the skill's gate, cost/grain is not a
self-resolving reason to escalate a clearly-composable lemma. (For completeness: IF the project ever
decides to upstream the bridge family, the genuinely reusable abstraction is the parent
`evalEval_eq_of_mk_eq` — the ring-level `mk`→eval transport — assessed separately; the ψ/Ψ/odd
specialisations are then one-line corollaries or inlined, exactly the NO-composable outcome.)

This is **not** a cost-driven downgrade: the composition is cheap and mechanical. It is a genuine
"mathlib already has the pieces" verdict.

**WHY not (refactor-actionable):**

Mathlib has the building blocks; `evalEval_ψ_odd` is a ≤3-call composition. The mathlib building blocks:
  - `AdjoinRoot.evalEval_mk` — `Mathlib/Algebra/Polynomial/Bivariate.lean:391`
  - `Affine.CoordinateRing.mk_ψ` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`
  - `evalEval_C` — `Mathlib/Algebra/Polynomial/Bivariate.lean:49`
  - the def `WeierstrassCurve.Ψ` (`if Even n then ψ₂ else 1`) — `Basic.lean:290`
  (project-internally, these are pre-packaged as the two NO-composable siblings `evalEval_ψ_eq_evalEval_Ψ`
  and `evalEval_Ψ_odd`.)

Composition sketch (≤3 lines, the call-site form via the two siblings):
```lean
-- replaces `rw [evalEval_ψ_odd C hns.left (p:ℤ) hodd_int] at hψ`
rw [evalEval_ψ_eq_evalEval_Ψ C hns.left (p : ℤ), evalEval_Ψ_odd C (p : ℤ) hodd_int] at hψ
-- where C is the curve (curveQ W or curveK R K W)
```
or fully inlined to pure mathlib (the `have hev := AdjoinRoot.evalEval_mk …; rw […]` block in Phase 6).

Call sites in the project (from Phase 6.0): **K = 2**.
Refactor plan (mathlib-upstreaming view; NOT a directive to delete from the dev branch — see caveat):
  - GeneralPrimeOrder.lean:88 — replace `rw [evalEval_ψ_odd (curveQ W) hns.left (p : ℤ) hodd_int] at hψ`
    with `rw [evalEval_ψ_eq_evalEval_Ψ (curveQ W) hns.left (p : ℤ), evalEval_Ψ_odd (curveQ W) (p : ℤ) hodd_int] at hψ`.
  - PIDPrimeOrder.lean:121 — replace `rw [evalEval_ψ_odd (curveK R K W) hns.left (p : ℤ) hodd_int] at hψ`
    with `rw [evalEval_ψ_eq_evalEval_Ψ (curveK R K W) hns.left (p : ℤ), evalEval_Ψ_odd (curveK R K W) (p : ℤ) hodd_int] at hψ`.
  Argument flow is identical (curve, `hns.left`, `(p : ℤ)`, `hodd_int`); only the lemma name(s) change.
  Then delete `evalEval_ψ_odd` from EvalBridge.lean. (If even the siblings are upstreamed, inline the
  pure-mathlib block instead.)

**Project caveat (do not delete locally just for this).** This verdict answers the *mathlib* question
("should mathlib carry this standalone?" → no, it is composable). Within the NagellLutz dev branch the
EvalBridge family is a legitimate, reused local mini-API that keeps the Nagell–Lutz integrality proofs
readable, and is exactly the WIP helper AINTLIB tolerates on `dev/*`. Local cleanup (inline the two-rw
collapse and drop the one-line wrapper) is reasonable but optional and orthogonal to the mathlib call.

---

## Next step

Do **not** propose `evalEval_ψ_odd` to mathlib as a standalone lemma — it is a ≤3-call composition
whose two halves are themselves NO-composable mathlib compositions (`AdjoinRoot.evalEval_mk` + `mk_ψ`,
then `Ψ`-unfold + `evalEval_C`). If any part of `EvalBridge.lean` is ever upstreamed, route a separate
`/mathlibable` (then `/generalise` to `CommRing`) at the **parent** `evalEval_eq_of_mk_eq` — the
ring-level `mk`→eval transport is the genuinely reusable abstraction; this odd-`n` ψ specialisation then
becomes a one-line corollary or an inlined call.

---

### Reconciliation with the earlier BORDERLINE write-up

The earlier pass filed this decl as **BORDERLINE-needs-human**, hinging on the grain/policy question
"upstream the EvalBridge family as a group, and if so ship the odd-`n` convenience named or inline?".
This report supersedes that with **NO-composable-from-mathlib** for three reasons:
1. **Family consistency.** All five other EvalBridge members are NO-composable in the ledger;
   `evalEval_ψ_odd` is strictly their downstream chain, so it cannot be *less* composable.
2. **Both halves are composable.** With `evalEval_ψ_eq_evalEval_Ψ` and `evalEval_Ψ_odd` both
   NO-composable, the chain is a clean composition by construction — the composability question is
   resolved, not open.
3. **The skill's gate.** The open question was a grain/cost/policy call, and the skill explicitly
   forbids escalating a clearly-composable lemma to BORDERLINE on grain/cost grounds. The grain question
   ("group-upstream the bridges?") is real but belongs to the **parent** `evalEval_eq_of_mk_eq`, not to
   this trivial specialisation, and its answer (upstream the parent; inline the specialisations) is
   itself the NO-composable outcome for this decl.

---

### Sources (literature search)

- Nagell–Lutz, quickly — A. Alpöge: https://people.math.harvard.edu/~alpoge/papers/nagell-lutz,%20quickly.pdf
- Elliptic curves over p-adic numbers: Nagell–Lutz — Anqi Li: https://aqlithium.github.io/anqili/784paper.pdf
- MIT 18.783 Elliptic Curves, Problem Set #3: https://math.mit.edu/classes/18.783/2022/ProblemSet3.pdf
- Magma handbook, division polynomials: https://magma.maths.usyd.edu.au/magma/handbook/text/1545
- D. Moody, Division Polynomials for Alternate Models of Elliptic Curves (eprint 2010/630): https://eprint.iacr.org/2010/630.pdf
- Nagell–Lutz theorem — Wikipedia: https://en.wikipedia.org/wiki/Nagell-Lutz_theorem
- A recurrence relation for elliptic divisibility sequences (arXiv 2102.07573): https://arxiv.org/pdf/2102.07573
- Integral points on elliptic curves and explicit valuations of division polynomials (arXiv 1108.3051): https://arxiv.org/pdf/1108.3051
- Homogeneous division polynomials for Weierstrass elliptic curves (arXiv 1303.4327): https://arxiv.org/pdf/1303.4327
