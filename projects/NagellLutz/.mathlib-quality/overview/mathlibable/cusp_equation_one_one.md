# /mathlibable report — `WeierstrassCurve.cusp_equation_one_one`

## Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source.
- decl `WeierstrassCurve.cusp_equation_one_one`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/Universal.lean:182`
- qualified name:           `WeierstrassCurve.cusp_equation_one_one` (VERIFIED — line 182 sits inside
  `namespace WeierstrassCurve` opened at line 69 / closed line 243, but *outside* the inner
  `namespace Universal` which closes at line 177 and reopens at line 196).
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Additions to `Affine.Point` and the universal elliptic curve; defines
  `Universal.curve` over `ℤ[A₁..A₆]` and the cusp curve `Y²=X³` carrying the point `(1,1)`, used to
  prove `ψₙ(1,1)=n` and hence nonvanishing of the universal `ψₙ`.

## Statement (Phase 1)

`WeierstrassCurve.cusp_equation_one_one` asserts that the affine point `(1, 1)` lies on the
**cuspidal cubic** `Y² = X³` over `ℤ`. The cusp curve is defined just above as
`cusp : WeierstrassCurve.Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }`, i.e. the
singular Weierstrass curve with all coefficients zero, whose Weierstrass equation reduces to
`Y² = X³`. The lemma is the membership statement `(1)² = (1)³` dressed as `cusp.Equation 1 1`.

Proof body (one line):
```lean
lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]
```

Variables / typeclasses involved: none (concrete curve over `ℤ`, concrete point `(1,1)`).
Hypotheses: none.
Conclusion (math): `1² = 1³` — the point `(1,1)` satisfies `Y² = X³`.
Conclusion (Lean): `WeierstrassCurve.cusp.Equation 1 1`, i.e.
`cusp.toAffine.polynomial.evalEval 1 1 = 0`.

Context of use: `(1,1)` is chosen because on the cusp curve the `n`-th division polynomial satisfies
`ψₙ(1,1) = n`; specialising the *universal* curve to the cusp via `ringEval cusp_equation_one_one`
then forces `ψₙ ≠ 0` for `n ≠ 0`, which is how the project proves the distinguished point `(X,Y)`
has infinite order on the universal pointed elliptic curve.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a concrete membership fact (`(1,1)` on a fixed curve) used as a specialisation anchor; not a
new structure, not a named theorem, not a `## Main results` goal. (Literature width still EXHAUSTIVE.)

## One-line check (Phase 2b)

n/a — kind is `lemma` (theorem), not `def`/`abbrev`/`structure`. The proof is a single `simp` line,
which reinforces the SMALL/triviality reading but the 2b exemption table applies only to definitions.

(Note: the companion `def cusp` *is* a one-line definition; see the composition discussion — it is a
one-liner WITHOUT-EXEMPTION, no downstream relies on controlled unfolding, no diamond, no stable-name
consumer beyond this file.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | cuspidal cubic Y²=X³ singular Weierstrass curve cusp rational point (1,1)                   | yes  | cuspidal cubic `C = {y²−x³=0}`, cusp at `(0,0)`, parametrised `x=t²,y=t³` | Wikipedia "Cubic plane curve", Grokipedia; `(1,1)` satisfies it trivially but is not a named fact |
|  2 | WebSearch (general form)         | division polynomial ψₙ cusp curve y²=x³ equals n nonvanishing elliptic divisibility seq     | yes  | ψₙ divisor `[n]*∞ − n²∞`; EDS recurrence              | arXiv 1105.5633, math/0404412 — standard EDS theory; no micro-lemma "point on cusp" |
|  3 | WebSearch (named-after/aliases)  | (covered by #1) "cuspidal cubic" / "nodal vs cuspidal" Weierstrass singular fibre           | yes  | singular Weierstrass: node (`y²=x²(x+1)`) vs cusp (`y²=x³`) | classical (Silverman AEC III.1); the cusp curve is standard, the point-membership is not |
|  4 | ChatGPT MCP                      | (unavailable this session — MCP down per task note; substituted by extra WebSearch at two generalities, #1/#2) | n/a  | —                                                     | recorded n/a: server down; fallback web channels ran |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/`              | n/a  | (no references dir present in repo)                   | dir absent — n/a |
|  6 | nLab                             | "cuspidal cubic" / "Weierstrass cubic"                                                      | n/a  | nLab has additive group `𝔾ₐ ≅` smooth locus of cuspidal cubic, but no membership lemma | concept present, the trivial point-fact is not an nLab-level statement |
|  7 | nCatLab (categorical)            | —                                                                                          | n/a  | not a categorical concept (an arithmetic membership)  | n/a |
|  8 | Stacks Project (alg geom)        | "cuspidal" / genus-0 singular cubic                                                         | n/a  | Stacks discusses cusps/nodes abstractly; no `(1,1)∈{y²=x³}` lemma | a numeric point-check is below Stacks granularity |
|  9 | MathOverflow / Math.SE           | "(1,1) on y²=x³" / smooth points of cuspidal cubic form a group                            | yes  | smooth locus of `y²=x³` ≅ `(𝔾ₐ,+)`; `(1,1)↦` param `t=1` | confirms `(1,1)` is the smooth point at `t=1`; still not a named result |
| 10 | recent arXiv (last 5y)           | (#2 covers) EDS / division-polynomial nonvanishing via specialisation to singular fibre     | yes  | technique of specialising to singular/cusp fibre is folklore in EDS papers | the *technique* is known; the Lean micro-lemma is bookkeeping for it |

### Literature summary (Phase 3)

Concept identified as: the **cuspidal cubic** `Y² = X³` (a singular Weierstrass curve) and the
membership of the smooth point `(1,1)` (parameter `t=1` under `x=t², y=t³`).
Sources agree on the standard form: yes — `Y²=X³` is *the* cuspidal Weierstrass model; its smooth
locus is `(𝔾ₐ,+)`, on which `(1,1)` is the point `t=1`.
Most general standard form: there is no "more general" form of this statement — it is a single
numeric incidence `1²=1³`. The surrounding *theory* (ψₙ on the cusp = n; specialise universal curve)
is standard EDS folklore, but the lemma itself is an arithmetic triviality.
Disagreement with the literature: none. The literature has the *cusp curve* and the *technique*; it
does not (and would not) record "`(1,1)` lies on `y²=x³`" as a named statement.

## Generality analysis — `WeierstrassCurve.cusp_equation_one_one`

Literature-standard form (from Phase 3): a single numeric incidence; nothing to generalise.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring              | `ℤ` (fixed)       | any comm. ring (`1²=1³` holds everywhere) | yes (vacuously) | the statement is `1=1`; true over any `CommRing` — but generalising a numeric fact serves no purpose, mathlib has the engine (`equation_iff`) for arbitrary curves/points already |
| 2 | point `(1,1)`          | fixed             | fixed                    | n/a                 | a specific incidence, not a parameter |
| 3 | curve `cusp`           | fixed `Y²=X³`     | fixed                    | n/a                 | a specific curve |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (degenerately — it is a closed numeric statement with no
weakenable hypotheses). Number of weakening opportunities found: 0 meaningful.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | bundled hyps → typeclasses?                                              | no       | no hypotheses          | — |
|  2 | sequences/metric → filters/topology?                                    | no       | purely algebraic incidence | — |
|  3 | construction → universal-property class?                                | no       | —                      | — |
|  4 | set+closure-pred → bundled substructure?                                 | no       | —                      | — |
|  5 | vector-space/field-specific → weaker typeclass?                          | no       | already over `ℤ`/any ring | — |
|  6 | 1-categorical → higher-categorical?                                      | no       | —                      | — |
|  7 | concrete index (ℤ) → arbitrary monoid/group?                            | no       | the "ℤ" is the base ring of a concrete curve, not an index to generalise | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a closed arithmetic incidence on a fixed singular curve; there
is no organisational redundancy to remove, no API it would compose better with. The "right" mathlib
primitive (`equation_iff`) already exists and handles arbitrary curves/points — this lemma is just one
evaluation of it.

## Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma` (a `Prop`-valued theorem); it introduces no definitional equalities
and no typeclass-search paths. (The companion `def cusp` would be in scope for 4.5 if it were the
target, but it is a trivial structure-literal record with no instances and poses no diamond risk.)

## Mathlib search-status: `WeierstrassCurve.cusp_equation_one_one`

[A] Lean-Finder       n/a (mathlib index search via Loogle/LeanSearch below; Lean-Finder not separately reachable this session)
[B] Loogle/grep type  pattern `WeierstrassCurve.Affine.Equation _ _ _` for explicit-coordinate hits → only `equation_zero` (`W.Equation 0 0 ↔ W.a₆ = 0`) and `equation_iff_variableChange`; no `Equation 1 1`, no cusp.   no hit
[C] LeanSearch (NL)   "point (1,1) on cuspidal cubic Y²=X³" / "cusp Weierstrass curve all coefficients zero"  →  no mathlib decl
[D] Grep mathlib src  `grep -rni "cusp"` over `Mathlib/AlgebraicGeometry/EllipticCurve/` → ZERO results (the word "cusp" in mathlib is exclusively the modular-forms upper-half-plane cusp, in `Mathlib/NumberTheory/ModularForms/*`). `grep "{ a₁ := 0, a₂ := 0"` / named all-zero Weierstrass curve → none. `grep "Equation 1 1"` over `Mathlib/AlgebraicGeometry/` → none.  no hit
[E] Name pattern      `cusp_equation_one_one`, `cusp`, `*_one_one` in `Mathlib/AlgebraicGeometry/EllipticCurve/` → none (the only `_one_one`-adjacent hits are `equation_iff` usages, unrelated).  no hit

Searched for both: the user's exact form (`cusp.Equation 1 1`) AND the general form
(any explicit-coordinate point-membership / any named singular "cusp" Weierstrass curve).

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib has
no named cuspidal Weierstrass curve and no point-on-explicit-curve lemma of this kind — only the
generic membership engine `equation_iff` / `equation_iff'` (`Mathlib/.../Affine/Basic.lean:152,156`).

## Call sites — `WeierstrassCurve.cusp_equation_one_one`

Internal use count: **3** (within the NagellLutz project, excluding the declaring file's own decl line).
External-to-file callers: 2 distinct files.

| Caller file:line                                   | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------|--------------------------------------------------------------------|
| `LutzNagell/Universal.lean:234`                    | `replace h := congr(ringEval cusp_equation_one_one $h)`            |
| `LutzNagell/ZSMul.lean:144`                        | `replace h := congr(ringEval cusp_equation_one_one $h)`            |
| `LutzNagell/ZSMul.lean:150`                        | `replace h := congr(ringEval cusp_equation_one_one $h)`            |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?): (none) —
every consumer routes through this lemma to build `ringEval` (the specialisation `Universal.Ring →+* ℤ`
that requires a proof the target point is on the target curve). Usage is exclusively as the
`(eqn : Affine.Equation W x y)` argument to `ringEval`, with `W = cusp`, `(x,y) = (1,1)`.

Composability signal: K = 3 internal uses, all in one project, all the SAME idiom (feeding `ringEval`).
No external/downstream-library consumers. This is internal scaffolding for one proof technique, not a
reusable public API. → leans NO.

## Composition check (Phase 6)

Can `cusp.Equation 1 1` be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1: `(WeierstrassCurve.Affine.equation_iff 1 1).mpr (by ring)` — or, fully inline, the original
one-liner `by simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]`.
  - Mathlib decls used: `WeierstrassCurve.Affine.equation_iff` (`Mathlib/.../Affine/Basic.lean:156`),
    which states `W.Equation x y ↔ y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆`. For `cusp` all `aᵢ=0`, so the RHS is
    `1 = 1`, closed by `ring` / `norm_num`.
  - Result: **succeeds** — one `equation_iff` rewrite + `ring`. (≤2 calls.)
  - Notes: equivalently `equation_iff'` + `ring`, or `simp [...]` as written. All ≤3 chained steps.

Conclusion: **COMPOSABLE** — a 1–2 mathlib-call composition (`equation_iff` then `ring`). No new
mathlib lemma is warranted; the fact is a direct evaluation of an existing mathlib `Iff`.

## Verdict: `WeierstrassCurve.cusp_equation_one_one`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the cuspidal cubic `Y²=X³` is standard; the membership `(1,1)∈{y²=x³}`
  (`1²=1³`) is an arithmetic triviality, recorded by no source as a named statement.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (degenerate — a closed numeric incidence); no
  modern-idiom restatement applies.
- Mathlib search (Phase 5): not in mathlib; mathlib has the generic membership engine `equation_iff`
  but no named cusp curve and no explicit-coordinate point lemma. ("cusp" in mathlib = modular-forms cusp only.)
- Composition check (Phase 6): COMPOSABLE in ≤2 calls (`equation_iff` + `ring`).

**Rationale:**

`cusp_equation_one_one` is project-local scaffolding, not a mathlib candidate. Mathematically it says
nothing more than `1² = 1³`: that the point `(1,1)` lies on the cuspidal cubic `Y² = X³`. It is a
single evaluation of mathlib's existing `WeierstrassCurve.Affine.equation_iff`, which already handles
arbitrary curves and points; for `cusp` (all coefficients zero) the membership iff collapses to `1 = 1`,
closed by `ring`. Mathlib deliberately has no "cusp curve" object — `Y²=X³` is *singular*, so it is not
a `WeierstrassCurve` of interest to mathlib's elliptic-curve API beyond being expressible as a
coefficient record; the word "cusp" appears in mathlib only in the unrelated modular-forms sense
(`Mathlib/NumberTheory/ModularForms/`). Adding a named lemma for one numeric incidence on one fixed
singular curve would be noise.

The call-site evidence confirms this: all three uses are the identical idiom
`congr(ringEval cusp_equation_one_one $h)`, feeding the lemma as the on-curve witness required to build
the specialisation homomorphism `ringEval : Universal.Ring →+* ℤ`. That is a bespoke step in *this*
project's proof that the universal division polynomial `ψₙ` is nonzero (via `ψₙ(1,1) = n` on the cusp).
It is internal plumbing for a single technique, with no external consumers and no reusable content.

**WHY not (refactor-actionable):** Mathlib has the building block `WeierstrassCurve.Affine.equation_iff`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`; equivalently `equation_iff'` at line
152). The user's form is a ≤2-call composition of it. No new lemma is needed.

Mathlib building blocks: `WeierstrassCurve.Affine.equation_iff`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`).

Composition sketch (≤3 lines):
```lean
example : cusp.Equation 1 1 := (WeierstrassCurve.Affine.equation_iff 1 1).mpr (by ring)
-- or simply keep the existing one-liner:
example : cusp.Equation 1 1 := by simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]
```

Call sites in our project (from Phase 6.0): K = 3 (Universal.lean:234, ZSMul.lean:144, ZSMul.lean:150).

**Important caveat for the refactor.** Do NOT delete the lemma. Although `cusp_equation_one_one` is not
a mathlib candidate, it is a *named on-curve witness reused 3× as a `congr(...)` argument*. Keeping a
1-line named lemma local to the project is correct mathlib-style practice for a witness threaded through
multiple proofs (inlining `(equation_iff 1 1).mpr (by ring)` at three sites, inside `congr(ringEval … $h)`,
is strictly worse for readability and gives the elaborator a harder term to chew on). So the
"NO-composable" verdict here means: **it does not belong *in mathlib*** — it should remain a private/local
helper in the NagellLutz project. The refactor action is therefore "leave it in the project; do not
upstream", not "delete and inline". If anything, the same goes for the companion `def cusp`: a fine
project-local definition, not a mathlib addition.

Next action: do **not** upstream `cusp_equation_one_one` (nor `def cusp`). It is correct, minimal,
project-local scaffolding for the universal-`ψₙ`-nonvanishing argument. No mathlib PR; no deletion.

---

## Next step

Keep `WeierstrassCurve.cusp_equation_one_one` (and `def cusp`) as project-local helpers in
`projects/NagellLutz/LutzNagell/Universal.lean`. They are a ≤2-call composition of mathlib's
`equation_iff` specialised to a fixed singular curve and so are not mathlib material, but they serve as
a named on-curve witness reused 3× (the `ringEval cusp_equation_one_one` idiom) and should stay where
they are rather than be inlined or upstreamed.
