# /mathlibable report — `WeierstrassCurve.evalEval_Ψ_odd`

## Verdict: **NO-composable-from-mathlib**

One-line: trivial 3-step definitional simp over the *project-local* `evalEval` bridge API
(`unfold Ψ` + `if_neg` + `evalEval_C`); not a mathlib concept, inline it.

---

### Baseline (Phase 0)
- lake build:               (not re-run — local build is stale per task note; reasoning from source)
- decl `WeierstrassCurve.evalEval_Ψ_odd`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:62`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Eval bridge lemmas for Lutz–Nagell" — bridges coordinate-ring
  congruences (`mk_ψ`, `mk_φ`, `mk_Ψ_sq`) to concrete equalities after evaluating bivariate
  polynomials at an on-curve point `(x, y)`.

**True qualified name confirmed:** `WeierstrassCurve.evalEval_Ψ_odd`
(file opens `namespace WeierstrassCurve`, line 24; the decl is a bare `theorem`, line 62).

---

### Statement (Phase 1)

`evalEval_Ψ_odd` states: for an odd integer `n`, the bivariate "dressed" division polynomial
`W.Ψ n` evaluated at any pair `(x, y) ∈ F × F` equals the univariate pre-division polynomial
`W.preΨ n` evaluated at `x`:

> For `n` odd, `(W.Ψ n).evalEval x y = (W.preΨ n).eval x`.

The underlying mathematics: `Ψ n` is *defined* (identically in mathlib and in this fork) as
`C (W.preΨ n) * (if Even n then W.ψ₂ else 1)`. For odd `n` the `if` selects the `else 1`
branch, so `Ψ n = C (W.preΨ n)`, a constant-in-`Y` polynomial; evaluating a `C p` at `(x,y)`
gives `p.eval x` regardless of `y`. The on-curve equation is **not** needed and is **not**
a hypothesis of this lemma.

Variables / typeclasses involved (Lean side):
- `{F : Type*} [Field F]` — the base field (only `CommRing` is actually used).
- `(W : WeierstrassCurve F)` — the Weierstrass curve.
- `{x y : F}` — an arbitrary point; **no** on-curve hypothesis.

Hypotheses (Lean side):
- `(n : ℤ)` — the index.
- `(hodd : ¬Even n)` — `n` is odd; the sole load-bearing input.

Conclusion (math): for odd `n`, `Ψₙ` is independent of `y` and reduces to the univariate `preΨₙ`.
Conclusion (Lean): `(W.Ψ n).evalEval x y = (W.preΨ n).eval x`.

Proof body (one line):
```lean
simp only [WeierstrassCurve.Ψ, if_neg hodd, mul_one, evalEval_C]
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper bridge lemma — not a named theorem, not a new structure, not a `## Main results`
entry. It is one definitional simp step feeding the immediately-following `evalEval_ψ_odd`.

(Literature width run EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. (The check applies to definitions; the
one-line *proof* is itself a strong NO-composable signal, captured in Phases 5–6.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial psi_n odd equals univariate polynomial evaluation x-coordinate"                   | yes  | for odd `n`, `ψₙ ∈ K[x]` after substituting `y² = x³+ax+b` | MIT 18.783 notes; mathlib4 docs; arXiv 1303.5002 |
|  2 | WebSearch (general form / y-free)| "division polynomial odd n function of x only Weierstrass curve y free"                                 | yes  | "for odd m, ψₘ is a polynomial in K[x] of degree ≤ ½(m²−1), leading coeff m" | Stange eprint 2025/521; arXiv 1108.3051 |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2 — division polynomials have no person-name; aliases "torsion polynomial")             | yes  | same concept; roots = x-coords of m-torsion | standard EC theory |
|  4 | ChatGPT MCP                      | —                                                                                                      | n/a  | MCP down per task note | fell back to WebSearch ×3 + mathlib-doc reading; the fact ("odd division polynomials are univariate in x") is textbook (Silverman, Washington) and not in doubt |
|  5 | Local references                 | find `.mathlib-quality/references/`, `refs/NagellLutz/`                                                 | n/a  | both absent on this machine | no PDFs to grep |
|  6 | nLab                             | "division polynomial"                                                                                  | n/a  | nLab has no division-polynomial page | concept is computational/arithmetic, not categorical |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept | — |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                                                  | n/a  | Stacks does not cover EC division polynomials | classical arithmetic-geometry, outside Stacks scope |
|  9 | MathOverflow / Math.SE           | "division polynomial odd univariate x" (subsumed by #1/#2 web hits)                                     | yes  | confirms odd ⇒ function of x | folklore; many MO/SE threads |
| 10 | recent arXiv (≤5 yr)             | Stange "Division polynomials for arbitrary isogenies" 2025/521                                          | yes  | same odd/even x-vs-y dichotomy | modern treatment, same statement |

### Literature summary (Phase 3)

Concept identified as: **division polynomials of a Weierstrass curve** (`ψₙ`), and specifically
the classical fact that **for odd `n`, `ψₙ` is a univariate polynomial in `x`** (it lies in the
subring generated by `x`, `a`, `b`; the `y` only enters for even `n`).

Sources agree on the standard form: **yes**. Every source states the odd/even dichotomy: odd
`ψₙ ∈ K[x]`, even `ψₙ ∈ y·K[x]`.

Most general standard form: the *mathematical* fact (odd ⇒ x-only after the curve substitution)
is one thing; the *Lean lemma here* is **strictly weaker and more elementary** than that fact —
it does NOT perform the `y² = x³+ax+b` substitution and needs no on-curve point. It is purely:
"the definition `Ψ n = C(preΨ n) · (Even n ? ψ₂ : 1)` collapses, for odd `n`, to `C(preΨ n)`,
and `evalEval (C p) = eval p`." The literature fact is the *motivation* for splitting `Ψ` into
`preΨ` and a parity factor; this lemma is just reading the parity factor off the definition.

Generality dimensions where the literature varies: none relevant — the lemma is a definitional
unfolding, below the level at which the literature's generality (base ring, isogeny vs.
multiplication-by-n) bites.

Disagreement with the literature: none. The lemma is a (much weaker) consequence of the standard
structural fact, specialised all the way down to the mathlib `Ψ`/`preΨ` definitions.

---

### Generality analysis — `WeierstrassCurve.evalEval_Ψ_odd`

Literature-standard form (from Phase 3): "for odd `n`, `ψₙ` is univariate in `x`." The Lean lemma
is a definitional restatement, not the substitution theorem.

| # | Parameter / hypothesis        | Current Lean form     | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-----------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[Field F]`                   | field                 | any comm. ring (`ψₙ` defined over `ℤ[a₁..a₆]`) | **yes** | proof uses only `CommRing` (`evalEval_C`, `if_neg`, `mul_one`); `Field` is unused. mathlib's `Ψ`/`preΨ` live over `[CommRing R]`. |
| 2 | `(hodd : ¬Even n)`            | `n` odd               | `n` odd                  | NO                  | essential — selects the `else 1` branch; even `n` keeps the `ψ₂` factor and the statement is false. |
| 3 | `{x y : F}`                   | arbitrary point       | arbitrary point          | NO (already maximal)| no on-curve hypothesis used; already as general as possible. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but only on the inessential axis
`[Field F]` (should be `[CommRing R]`). This narrowing is *inherited from the file's `variable`
block* (`{F : Type*} [Field F]`), which the whole Lutz–Nagell development needs elsewhere; it is
not intrinsic to this lemma. It does **not** push the verdict toward
YES-but-generalise-first, because (Phase 5/6) the lemma should not go to mathlib at all — it is a
project-local `evalEval`-bridge step. The `Field`→`CommRing` weakening is, at most, a local cleanup
note for `EvalBridge.lean`, not a mathlib-upstreaming action.

Number of weakening opportunities: 1 (the `Field`→`CommRing` axis), cosmetic.
Cost of restatement: CHEAP (mechanical) — but moot given the NO-composable verdict.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | bundled-hyp → typeclass? | no  | `hodd` and `n` are genuine inputs; nothing to classy-fy | — |
|  2 | sequences/metric → filters? | no | no analysis here; pure algebra | — |
|  3 | construction → universal property? | no | it's an evaluation identity, not a construction | — |
|  4 | set+closure → bundled substructure? | no | n/a | — |
|  5 | field-specific → module/ring weakening? | yes (minor) | `[CommRing R]` instead of `[Field F]` (same as Phase 4b row 1) | matches mathlib `Ψ`/`preΨ` generality — but only relevant if upstreamed, which it isn't |
|  6 | 1-cat → higher-cat? | no | n/a | — |
|  7 | concrete index → general monoid? | no | `n : ℤ` is the natural index for division polynomials | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the only move is the `Field`→`CommRing` weakening, which is a
mechanical generality bump, not an organisational modernisation). One-line reason: the lemma is a
definitional `simp` over an existing definition; there is no abstraction to modernise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or instance-search paths introduced.)

---

### Mathlib search-status: `WeierstrassCurve.evalEval_Ψ_odd`

[A] Lean-Finder       "division polynomial Ψ evaluated odd equals preΨ"    no hits (index unavailable / nothing of this shape)
[B] Loogle            `WeierstrassCurve.Ψ → Polynomial.evalEval` ; `(WeierstrassCurve.Ψ _ _).evalEval _ _ = _`   no hits — mathlib has zero `evalEval`-of-`Ψ` lemmas
[C] LeanSearch        "value of division polynomial at a point for odd index is the pre-division polynomial"   no hits
[D] Grep mathlib src  `evalEval` ∩ `EllipticCurve/` ; `evalEval_Ψ` ; `Ψ.*evalEval` over `.lake/packages/mathlib/Mathlib/`   no hits in `DivisionPolynomial/`. `evalEval` appears only for `polynomial`/`polynomialX`/`polynomialY` in `Affine/`,`Jacobian/` — never for `Ψ`/`ψ`/`φ`. **mathlib has no `evalEval` bridge for division polynomials at all.**
[E] Name pattern      grep `evalEval_Ψ_odd`, `evalEval_ψ`, `evalEval_φ` across repo   the ENTIRE `evalEval_*` division-poly family lives only in `projects/NagellLutz/.../EvalBridge.lean`; absent from mathlib.

Searched for both:
  - user's current form (`(W.Ψ n).evalEval x y = (W.preΨ n).eval x`) — not in mathlib.
  - the literature-standard form ("odd ⇒ univariate") — mathlib encodes this *structurally* by
    defining `Ψ n = C (preΨ n) * (Even n ? ψ₂ : 1)` (Basic.lean:290) but ships **no lemma** that
    evaluates it; the `if`-collapse for odd `n` is left to the user.

**Building blocks that ARE in mathlib (identical names, same namespace):**
- `WeierstrassCurve.Ψ` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:290`,
  definition byte-identical to the fork: `C (W.preΨ n) * if Even n then W.ψ₂ else 1`.
- `Polynomial.evalEval_C` — `Mathlib/Algebra/Polynomial/Bivariate.lean:49`:
  `(C p).evalEval x y = p.eval x`.
- `if_neg`, `mul_one` — core.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form). But
mathlib has the building blocks; the composition is trivial (Phase 6).

---

### Call sites — `WeierstrassCurve.evalEval_Ψ_odd`

Internal use count: **0** (within the project, NOT counting the declaring file).
External-to-file callers: **0** distinct files.

| Caller file:line               | Usage pattern (one-line excerpt)                                  |
|--------------------------------|-------------------------------------------------------------------|
| EvalBridge.lean:70 (SAME FILE) | `rw [evalEval_ψ_eq_evalEval_Ψ W heq, evalEval_Ψ_odd W n hodd]`     |

The **only** consumer is `evalEval_ψ_odd`, three lines below it in the *same* file. There are no
external callers and no inline re-derivations elsewhere (grep for
`WeierstrassCurve.Ψ, if_neg` / `if_neg hodd, mul_one, evalEval_C` outside EvalBridge.lean: none).

Inline-derivation grep: (none found outside the declaring file)

Signal: K = 0 external + single same-file consumer ⇒ this is an internal proof step, not an API
surface. Per the Phase-6.0.1 table ("K = 1 internal use only … could be inlined") this leans
strongly NO-composable.

---

### Composition check (Phase 6)

Can `evalEval_Ψ_odd` be derived from mathlib in ≤3 chained calls? **Yes — it IS the composition.**

Attempt 1: the lemma's own proof is already a single `simp only` over mathlib + the (mathlib-identical)
`Ψ` definition:
```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) (n : ℤ) (hodd : ¬Even n) :
    (W.Ψ n).evalEval x y = (W.preΨ n).eval x := by
  simp only [WeierstrassCurve.Ψ, if_neg hodd, mul_one, Polynomial.evalEval_C]
```
  - Mathlib decls used: `WeierstrassCurve.Ψ` (unfold), `if_neg`, `mul_one`, `Polynomial.evalEval_C`.
  - Result: **succeeds** — 1 simp call, 4 simp lemmas, no hypotheses beyond `hodd`.
  - Notes: identical to the project proof; works verbatim once `Ψ`/`preΨ` are mathlib's (they are).

Conclusion: **COMPOSABLE** — a 1-line `simp only` from mathlib primitives. No new lemma needed.

---

## Verdict: `WeierstrassCurve.evalEval_Ψ_odd`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the math fact (odd `ψₙ` is univariate in `x`) is textbook; but this
  lemma is a definitional restatement *below* that fact (no `y²` substitution, no on-curve point).
- Generality analysis (Phase 4): STRICTLY NARROWER only on the inessential `[Field F]` axis
  (proof needs just `CommRing`); no modern-idiom move. Cosmetic, and moot.
- Mathlib search (Phase 5): not in mathlib; but the building blocks `WeierstrassCurve.Ψ` (identical
  def) and `Polynomial.evalEval_C` are.
- Composition check (Phase 6): COMPOSABLE — `simp only [WeierstrassCurve.Ψ, if_neg hodd, mul_one,
  Polynomial.evalEval_C]`, one call.

**Rationale:**

`evalEval_Ψ_odd` is not a theorem about elliptic curves so much as a one-step unfolding of the
mathlib definition `Ψ n = C (preΨ n) * (Even n ? ψ₂ : 1)`: for odd `n` the conditional collapses to
`* 1`, leaving `C (preΨ n)`, and `evalEval (C p) x y = p.eval x` is the mathlib lemma
`Polynomial.evalEval_C`. The proof is literally that — four simp lemmas in one `simp only`. There is
no `y² = x³+ax+b` substitution and no on-curve hypothesis; the deep arithmetic content of the
literature fact ("odd division polynomials are functions of `x` alone") is *not* what this lemma
proves — that content is already baked into the `preΨ`/parity-factor split that mathlib uses to
*define* `Ψ`. The lemma just reads the parity factor off the definition.

Decisively, this sits inside a *project-local* `evalEval`-bridge layer (`EvalBridge.lean`) that
mathlib does not have and (on current evidence) does not want: mathlib's division-polynomial API
stops at the coordinate-ring congruences `mk_ψ`, `mk_Ψ_sq`, `mk_φ`, and never evaluates a division
polynomial at a concrete point. Its sole consumer is `evalEval_ψ_odd` three lines away in the same
file (K = 0 external uses). The right disposition is to **inline the one-line `simp` at that single
call site**, not to ship a named lemma to mathlib.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; `evalEval_Ψ_odd` is a 1-call `simp only` composition of them. The
named lemma adds nothing mathlib is missing — it is a private unfolding step.

Mathlib building blocks:
- `WeierstrassCurve.Ψ` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:290`
  (definition identical to the project fork)
- `Polynomial.evalEval_C` — `Mathlib/Algebra/Polynomial/Bivariate.lean:49`
- `if_neg`, `mul_one` (core)

Composition sketch (≤3 lines):
```lean
-- in place of `evalEval_Ψ_odd W n hodd`, write:
by simp only [WeierstrassCurve.Ψ, if_neg hodd, mul_one, Polynomial.evalEval_C]
```

Call sites in the project (from Phase 6.0): **1** — `EvalBridge.lean:70`, inside the proof of
`evalEval_ψ_odd`.

Refactor plan: at that single site, replace
```lean
rw [evalEval_ψ_eq_evalEval_Ψ W heq, evalEval_Ψ_odd W n hodd]
```
with the inlined unfolding, e.g.
```lean
rw [evalEval_ψ_eq_evalEval_Ψ W heq]
simp only [WeierstrassCurve.Ψ, if_neg hodd, mul_one, evalEval_C]
```
then delete the `evalEval_Ψ_odd` declaration.

**Caveat / lighter alternative (project-policy note):** This is a *forked-mathlib* project. The
practical bar here is not "delete vs. mathlib" but "keep the bridge layer small and consistent." If
the `EvalBridge.lean` authors prefer the named step for readability (it parallels
`evalEval_φ_eq_eval_Φ` and `evalEval_Ψ_sq_eq_eval_ΨSq` in the same file), keeping it as a local
private/`@[local simp]`-style helper is perfectly reasonable — it simply should not be *upstreamed
to mathlib* as a standalone lemma. The mathlibable verdict (NO-composable) concerns mathlib
inclusion; the keep/inline choice inside the fork is a local cleanup call, not a mathlib PR.

**Next action:** do **not** open a mathlib PR for this lemma. Inline the one-line `simp` at
`EvalBridge.lean:70` (or retain it as an explicitly-local helper). If anything in this division-poly
bridge is worth upstreaming, it is the *general* `evalEval`-of-division-polynomial bridge as a
family (`evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`, the `evalEval_eq_of_mk_eq` engine) —
assess those on their own; this odd-`Ψ` unfolding is the trivial leaf of that family and rides along
with whichever decision is made there.
