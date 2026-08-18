# /mathlibable report — `WeierstrassCurve.dblXYZ_smulEval`

> The **concrete-curve** form of the doubling step in the division-polynomial scalar-multiplication
> formula: for an arbitrary Weierstrass curve `W` over a commutative ring `R` and a point `(x,y)` on
> the affine curve, applying mathlib's Jacobian doubling map `dblXYZ` to the *evaluated* division-
> polynomial triple `(φₙ(x,y), ωₙ(x,y), ψₙ(x,y))` reproduces the `2n` triple. It is the
> `ringEval`-specialization (to `W`) of the universal-ring twin `dblXYZ_smulRing`, and the single
> doubling lemma consumed by this file's headline theorem `WeierstrassCurve.zsmul_eq_smulEval`
> (`n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coordinates).
>
> **Family / chain.** `dblXYZ_smulField` (field, the substantive identity, line 460) → `dblXYZ_smulRing`
> (universal ring transfer, line 471) → **`dblXYZ_smulEval`** (this; concrete curve `W`, line 568) →
> `zsmul_eq_smulEval` (line 590, the citable formula). Sibling at the same `smulEval` level:
> `addXYZ_smulEval` (572), `addXYZ_smulEval₁` (580). The `dblXYZ_smulRing` report → **BORDERLINE**; the
> field/ring twins `dblXYZ_smulField` / `addXYZ_smulField` / `addXYZ_smulRing` → **BORDERLINE**; this
> report concludes the same, for the same packaging reason carried one level further down (to `W`).

### Baseline (Phase 0)
- lake build:               (not re-run — local build is stale per task note; reasoning from source at `09b373db6e24`, toolchain `v4.32.0-rc1`)
- decl `WeierstrassCurve.dblXYZ_smulEval`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:568`
- kind:                      `lemma` (a `Prop` — an equation of `Fin 3 → R`)
- has sorry:                 no
- module docstring summary:  "Integer multiples of a rational point on an elliptic curve in terms of
  division polynomials" — the file proves `WeierstrassCurve.zsmul_eq_smulEval`
  (`n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coords). Lines 16–22 of the docstring name `dblXYZ_smulEval`
  and `addXYZ_smulEval₁` as the **two doubling/addition evaluation steps** of that proof.

**Qualified-name verification (corrects the task's parenthetical guess).** `ZSMul.lean` opens
`namespace WeierstrassCurve` at line 76. The inner `namespace Universal` (86) **closes at line 546**
and `namespace Jacobian` (395) **closes at line 544** — both *before* line 568. `dblXYZ_smulEval` is
declared at line 568, inside `WeierstrassCurve` only; the `open Universal Jacobian` at line 555 brings
those namespaces' *contents into scope by `open`*, it does **not** re-nest them. Therefore the true
qualified name is **`WeierstrassCurve.dblXYZ_smulEval`**, **NOT**
`WeierstrassCurve.Universal.Jacobian.dblXYZ_smulEval`. (Contrast the universal twin `dblXYZ_smulRing`
at line 471, which *is* inside all three namespaces.) The task's parsed guess
`WeierstrassCurve.dblXYZ_smulEval` is **CONFIRMED**.

---

### Statement (Phase 1)

```lean
variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
variable {x y : R}
variable {W} (eqn : W.toAffine.Equation x y)

-- (line 548–551) the object this lemma is about:
variable (x y) in
abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]

include eqn in
lemma dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]
```

Context (from the surrounding `variable`s):
- `R : Type*` with `[CommRing R]` — an **arbitrary commutative ring** (not a field; the field hypothesis
  only enters later, at `zsmul_eq_smulEval`, line 584).
- `W : WeierstrassCurve R` — an arbitrary Weierstrass curve over `R` (mathlib's `WeierstrassCurve`).
- `{x y : R}` and `eqn : W.toAffine.Equation x y` — a point `(x,y)` on the affine curve, i.e. satisfying
  the Weierstrass equation (mathlib's `WeierstrassCurve.Affine.Equation`, `Affine/Basic.lean:149`).
- `smulEval W x y n := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]` (line 551) — the three division polynomials
  **evaluated at `(x,y)`** via mathlib's bivariate evaluation `evalEval` (`Polynomial/Bivariate.lean:44`),
  packed as a Jacobian coordinate triple in `Fin 3 → R`.
- `dblXYZ` — **mathlib's** Jacobian doubling map (`Jacobian/Formula.lean:349`).
- `W.φ`, `W.ψ` — **mathlib's** division polynomials (`DivisionPolynomial/Basic.lean:448, :401`).
- **`W.ω`** — the y-coordinate (companion) division polynomial, **project-defined**
  (`DivisionPolynomialOmega.lean:74`); **absent from mathlib** (TODO, see Phase 5).

**Math content.** For any Weierstrass curve `W/R` and any point `(x,y)` on it, evaluating the doubling
formula on the division-polynomial triple equals the doubling-index triple, in `R`:
$$ \mathrm{dblXYZ}_W\big(\varphi_n(x,y),\ \omega_n(x,y),\ \psi_n(x,y)\big) \;=\; \big(\varphi_{2n}(x,y),\ \omega_{2n}(x,y),\ \psi_{2n}(x,y)\big). $$
These are the Jacobian coordinates `(X : Y : Z)` of `2·(n·(x,y))`, i.e. the doubling step of the classical
scalar-multiplication formula `[n](x,y) = (φₙ/ψₙ² , ωₙ/ψₙ³)`. The triple `(φₙ, ωₙ, ψₙ)(x,y)` are exactly
the unnormalized Jacobian coordinates of `n·(x,y)`; `dblXYZ` doubles them; the result is the same triple at
`2n`. This is the **concrete-`W`** instance of the universal coordinate-ring identity `dblXYZ_smulRing`.

Hypotheses: only `eqn : W.toAffine.Equation x y` (the point lies on the curve). No nonvanishing of `ψₙ`
and no characteristic/field hypothesis — those enter only when passing to actual points at
`zsmul_eq_smulEval`.

Conclusion (Lean): `dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n)`, an equation in `Fin 3 → R`.

**Proof (one line, a specialization).** Rewrite `smulEval W x y` backwards through `ringEval_comp_smulRing`
(line 557: `ringEval eqn ∘ smulRing n = smulEval W x y n`, the evaluation map `Universal.Ring → R` induced
by the point `(x,y)`), apply the universal-ring identity `dblXYZ_smulRing` (line 471) backwards, move the
`ringEval` ring hom past `dblXYZ` with **mathlib's** `map_dblXYZ` (`Jacobian/Formula.lean:742`), and close
with `curveRing_map_ringEval` (project, `Universal.lean:237`: `curveRing.map (ringEval eqn) = W`). I.e. the
whole content is: *specialize the universal identity along the evaluation `Universal.Ring → R` at `(x,y)`*.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `lemma` (a `Prop`) whose proof is a single `simp_rw` specializing the already-proved
universal twin `dblXYZ_smulRing` to a concrete curve `W` via the point's evaluation map. It is **not** the
`## Main results` headline (that is `zsmul_eq_smulEval`), not a person-named theorem, and introduces no new
object. It is an internal doubling step in the multiplication-formula proof.

(Literature width: this report runs the wider sweep anyway, to fix the family verdict; the result agrees
with the established `dblXYZ_smulRing` / `dblXYZ_smulField` family verdicts.)

### One-line check (Phase 2b)

Body: a single-line `by` block (`simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]`).
One-liner verdict: **ONE-LINER PROOF** — but the Phase-2b exemptions (defeq barrier / typeclass diamond /
API-name stability) are about **definitions**. This is a `Prop`, so those exemptions are n/a; what governs
the verdict is the lemma's *role* (internal scaffolding vs. standalone API), handled in the call-site and
composition phases below.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                         | Hit? | Standard form found                          | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------------------------------------|------|----------------------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomials scalar multiplication formula `[n]P = (φ/ψ², ω/ψ³)` Jacobian coordinates doubling elliptic curve         | yes  | `[n](x,y) = (φₙ/ψₙ², ωₙ/ψₙ³)`; doubling is the `n→2n` case | Silverman *AEC* Ex. 3.7; Wikipedia "Division polynomials"; the *multiplication formula* is the named end-product, not the per-evaluation doubling step |
|  2 | WebSearch (general / recursion)  | "division polynomial" doubling recursion ψ₂ₙ φₙ ωₙ "2n" Silverman Sutherland evaluated at a point                              | yes  | `ψ₂ₙ = ψₙ(ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)/ψ₂`; matching `φ₂ₙ`, `ω₂ₙ` | Sutherland MIT 18.783 L#6; Wikipedia; arXiv 1103.4560 — the **recursions** are the named classical identities; "dblXYZ on evaluated triple" is a formalization device |
|  3 | WebSearch (named-after/aliases)  | elliptic curve point doubling Jacobian coordinates division polynomial "ω" companion polynomial naming                          | yes  | `ωₙ` = the y-coordinate division polynomial; "the ψ, φ, ω of an elliptic curve" | The objects are standard (Silverman, Washington *ECNT* §3.2); the *evaluation-at-a-point doubling identity* has no standalone name |
|  4 | ChatGPT MCP                      | "standard name + generality of: dblXYZ of (φₙ,ωₙ,ψₙ) evaluated at a point = the 2n triple; is it a named theorem?"            | n/a  | —                                            | MCP down per task note; compensated by WebSearch breadth (#1–3) + direct mathlib-source reading of `dblXYZ`/`map_dblXYZ`/`evalEval`/`ψ`/`φ` + the sibling `dblXYZ_smulRing` report's own search |
|  5 | Local references                 | grep `.mathlib-quality/references/` (NagellLutz)                                                                              | n/a  | (no `references/` dir for NagellLutz)        | dir absent on this checkout; `refs/` store also absent — recorded n/a |
|  6 | nLab                             | "division polynomial" / "elliptic curve" doubling                                                                            | n/a  | nLab has no division-polynomial page         | not an nLab-style abstract-nonsense concept; recorded n/a after checking |
|  7 | nCatLab (categorical)            | —                                                                                                                            | n/a  | —                                            | not a categorical concept (concrete polynomial evaluation identity) |
|  8 | Stacks Project (alg geom)        | "division polynomial" / elliptic curve `[n]` formula                                                                          | n/a  | Stacks has elliptic-curve generalities but no division-polynomial multiplication-formula tag | not catalogued there; recorded n/a after checking |
|  9 | MathOverflow / Math.StackExchange| division polynomials Jacobian coordinates `[n]P` formula generality                                                          | yes  | confirms the `[n]P = (φ:ω:ψ)` packaging is the standard statement; usually over a field, sometimes any base | several Q&A; none name the per-evaluation doubling step |
| 10 | recent arXiv (last 5 years)      | division polynomials scalar multiplication Jacobian coordinates formalization (e.g. 2412.10284)                              | yes  | the *formula* `[n]P`; Jacobian `(X:Y:Z) ↔ (X/Z²,Y/Z³)` | arXiv 2412.10284, eprint 2010/630 (Moody) — engineering/formalization repackagings of the same formula; no separate name for this step |

### Literature summary (Phase 3)

Concept identified as: the **doubling step of the division-polynomial scalar-multiplication formula**,
evaluated at a concrete point on a concrete curve. The mathematics is entirely classical (Silverman *AEC*
Ex. 3.7; Washington *ECNT* §3.2; Sutherland 18.783 L#6; Wikipedia "Division polynomials") and is the engine
behind the citable formula `[n]P = (φₙ : ωₙ : ψₙ)` (= this file's `zsmul_eq_smulEval`).
Sources agree on the standard form: **yes** — the named object is the *full multiplication formula*, of
which this is the `n → 2n` half (the other half being `addXYZ_smulEval₁`, the `2n+1` case).
Most general standard form: the multiplication formula itself, valid over any base where the points make
sense, specialized from the universal/generic-point case — exactly this file's architecture
(`smulField` → `smulRing` → `smulEval` → `zsmul_eq_smulEval`).
Generality dimensions where the literature varies: base ring (most sources: a field; the modern/scheme-
theoretic and this file's view: **any commutative ring** — and `dblXYZ_smulEval` is already stated at the
`[CommRing R]` level, which is the *more general* end). Disagreement with literature: none.

If the search returned essentially no *standalone* name: that is itself the signal here — this is an
**internal intermediate** of a named formula, not a headline result, which steers the verdict toward
BORDERLINE/packaging rather than a clean standalone YES.

---

### Generality analysis — `WeierstrassCurve.dblXYZ_smulEval`

Literature-standard target: the **multiplication formula** `[n]P = (φₙ : ωₙ : ψₙ)` for any point `P` over
any base. `dblXYZ_smulEval` is its **doubling half**, already at `[CommRing R]` generality (the more
general end), with the point given only by `W.toAffine.Equation x y` (no nonvanishing / field hypothesis).

| # | Parameter / hypothesis        | Current Lean form                       | Literature-standard form                 | Weaker form? | Reason |
|---|-------------------------------|-----------------------------------------|------------------------------------------|--------------|--------|
| 1 | base `R`                      | `[CommRing R]` (arbitrary comm. ring)   | typically a field; modern: any base ring | **NO**       | Already at the **maximally general** commutative-ring level — stronger than the field statements in the literature. Cannot weaken `CommRing` further (need `dblXYZ`, `φ/ω/ψ`, the Weierstrass equation). |
| 2 | curve `W`                     | arbitrary `W : WeierstrassCurve R`      | arbitrary Weierstrass curve              | **NO**       | Fully general; it is the concrete instance obtained from the universal curve by `ringEval`. |
| 3 | point `(x,y)`                 | `eqn : W.toAffine.Equation x y`         | a point on the curve                     | **NO**       | This is the *defining* hypothesis (the point lies on the curve); it cannot be dropped — `dblXYZ` of an off-curve triple need not be the `2n` triple. |
| 4 | index `n`                     | arbitrary `n : ℤ`                       | arbitrary `n ∈ ℤ`                        | **NO**       | Already fully general in `n`; no nonvanishing hypothesis (the `smulEval` form absorbs `n = 0` via `ψ₀ = 0`, `φ₀ = 1`). |

### Generality verdict (Phase 4b)

Current form is: **MAXIMALLY GENERAL** (already `[CommRing R]`, arbitrary `W`, arbitrary `n`, with the
single unavoidable hypothesis that `(x,y)` lies on the curve). Weakening opportunities: **0**. The "more
general" object is not a weaker `dblXYZ_smulEval` but the *combined* formula `zsmul_eq_smulEval` (which this
lemma feeds), already present in the file.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                         | Applies? | Notes |
|----|------------------------------------------------------------------------------------------------------------------|----------|-------|
|  1 | "let X be a foo" → typeclasses?                                                                                  | no       | already typeclass-driven (`[CommRing R]`); the only bundled hypothesis `eqn` is the defining "on the curve" condition, not a generalizable preamble |
|  2 | sequences/metric → filters/topology?                                                                            | no       | a pure algebraic polynomial-evaluation identity; no limits/topology |
|  3 | construction → universal-property class?                                                                        | no       | the *universal* curve already plays the universal-property role one level up (`dblXYZ_smulRing` over `Universal.Ring`); `dblXYZ_smulEval` is the deliberate specialization to a concrete `W` |
|  4 | set-with-closure → bundled substructure?                                                                        | no       | n/a |
|  5 | field/metric-specific → weaken typeclasses?                                                                     | no       | **already weakened**: stated over `[CommRing R]`, more general than the field statements in the literature |
|  6 | 1-categorical → higher-categorical?                                                                             | no       | n/a |
|  7 | concrete index ℤ → arbitrary monoid/group?                                                                      | no       | `n : ℤ` is intrinsic (division polynomials are an EDS indexed by ℤ); not a generalizable index |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement already uses mathlib's idiomatic primitives — `dblXYZ`
(Jacobian doubling), `evalEval` (bivariate evaluation), `W.φ`/`W.ψ` (division polynomials), `Affine.Equation`
— at the most general (`[CommRing R]`) typeclass level. The only non-mathlib ingredient is the project's
`W.ω`, which is *missing-from-mathlib content*, not a "modernise the spelling" issue.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a `Prop`): no typeclass diamond, no reducibility leak, no instance
priority, no coercion or universe exposure; it anchors no instance and introduces no notation. Overall
risk: **NONE** (propositional). Not a factor in the verdict.

---

### Mathlib search-status: `WeierstrassCurve.dblXYZ_smulEval`

[A] Lean-Finder    "division polynomial scalar multiplication formula evaluated at point", "dblXYZ of (φₙ,ωₙ,ψₙ)(x,y) = 2n triple" — **no hit** (mathlib's index has no `n • P` division-polynomial formula at all, and no `smulEval`).
[B] Loogle         `WeierstrassCurve.Jacobian.dblXYZ`, `dblXYZ _ _ = _`, `evalEval _ _ ∘ ![_, _, _] = _`, `_ • _ = (_,_,_)` — `dblXYZ`, `map_dblXYZ`, `evalEval` **present**; **no** lemma equating `dblXYZ (φₙ,ωₙ,ψₙ)(x,y)` to the `2n` triple; no `smulEval`.
[C] LeanSearch     "doubling formula for division polynomials evaluated at a point", "n times a point as evaluated division polynomials in Jacobian coordinates" — surfaces `dblXYZ`/`normEDS`/`evalEval` building blocks only; **no** end-formula and **no** `_smulEval`.
[D] Grep mathlib src (over `09b373db6e24`, toolchain `v4.32.0-rc1`):
   - `dblXYZ` ✓ `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:349`; `dblXYZ_smul` ✓ (homogeneity, :361); `map_dblXYZ` ✓ `…/Jacobian/Formula.lean:742`.
   - `evalEval` ✓ `Mathlib/Algebra/Polynomial/Bivariate.lean:44`; `Affine.Equation` ✓ `…/Affine/Basic.lean:149`.
   - `ψ` (`WeierstrassCurve.ψ`) ✓ `…/DivisionPolynomial/Basic.lean:401`; `φ` ✓ `:448`.
   - **`ω` (the y-coordinate division polynomial): ABSENT from mathlib** — `grep 'def ω'` over `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/*.lean` returns nothing. mathlib's `Basic.lean` *describes* `ωₙ` in its module docstring (line 30) but lists it as an **open TODO** (line 71 "TODO: the bivariate polynomials `ωₙ`"; line 83 "TODO: implementation notes for the definition of `ωₙ`"). The actual `def ω` is **project-local** (`DivisionPolynomialOmega.lean:74`; the entire purpose of that file).
   - `smulEval` / `smulRing` / `smulField` / `smulPoly` / any `dblXYZ … = … (2 * n)` identity / `_smulEval` name: **ABSENT** (`grep` over `Mathlib/AlgebraicGeometry/EllipticCurve/` and `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — no hit). The `Universal.curve` / `CoordinateRing` / `ringEval` machinery is unupstreamed (authored by Junyan Xu).
[E] Name pattern   `dblXYZ_smulEval`, `smulEval`, `_smulEval` in mathlib — **no hit** (project-local).

Searched for **both** the current form *and* the literature target (the multiplication formula). **Neither
is in mathlib**, and the statement is **not even expressible** in current mathlib, because it mentions
`W.ω` (the y-coordinate division polynomial) and `smulEval`, neither of which mathlib has.

Concluded: **not in mathlib** (all five methods exhausted, plus the literature-standard form). Unlike a
typical NO-composable plumbing lemma, the statement *cannot be written down in mathlib today* (missing `ω`,
`smulEval`).

---

### Call sites — `WeierstrassCurve.dblXYZ_smulEval`

Internal use count (NagellLutz, excluding the declaring line 568): **1** substantive proof use.
External-to-file callers: **0** (also 0 outside NagellLutz, beyond the independent HasseWeil *duplicate* — see note).

| Caller file:line                 | Usage pattern (one-line excerpt)                                                            |
|----------------------------------|--------------------------------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:602        | `… two_nsmul, Point.add_point, ih _ (by omega), addMap_eq, add_self, dblXYZ_smulEval h.1]; rfl` — the **even** branch of the strong induction in `zsmul_eq_smulEval` |
| LutzNagell/ZSMul.lean:22 (doc)   | module docstring: names it as one of the two doubling/addition evaluation steps             |

Inline-derivation grep (re-derived elsewhere without `dblXYZ_smulEval`?):
  - **Duplicated, not re-derived:** `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:643`
    declares a **byte-identical** `dblXYZ_smulEval` (same statement, same one-line proof) for HasseWeil's
    parallel fork of this machinery. This is the AINTLIB cross-project fork duplication flagged in the task
    context — *two copies of the same lemma*, not an alternative derivation. (Family-level cross-project
    dedup is a `lane:cleanup` concern on `main`, orthogonal to the mathlibable verdict.)

**Call-sites reading.** `dblXYZ_smulEval` is consumed by **exactly one** site: the even case
(`n = 2·(…)`) of the strong induction proving the file's deliverable `zsmul_eq_smulEval` (line 602). It is a
**single-purpose internal node** in one proof chain — the concrete-`W` doubling step, paired with
`addXYZ_smulEval₁` (the odd `2n+1` step) — not a standalone API surface with independent consumers. K = 1
internal use; per the call-sites table this leans **toward NO-composable / internal**, but the composition
check below shows it is *not* composable from mathlib, so the disposition is the packaging judgment recorded
in the verdict.

---

### Composition check (Phase 6)

Can `dblXYZ_smulEval` be derived from **mathlib** in ≤3 chained calls? **No.**

Attempt 1 — exactly what the proof does (specialize the universal identity along the point's evaluation):
`simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]`.
  - Mathlib decls used: **`map_dblXYZ`** only (`Jacobian/Formula.lean:742`).
  - Project decls used (load-bearing): **`ringEval_comp_smulRing`** (`ZSMul.lean:557`),
    **`dblXYZ_smulRing`** (`ZSMul.lean:471` — itself BORDERLINE, content = the project field twin
    `dblXYZ_smulField`), **`curveRing_map_ringEval`** (`Universal.lean:237`), and the *object* `smulEval`
    (which mentions the project's `ω`).
  - Result: **fails as a mathlib-only composition.** The single mathlib call (`map_dblXYZ`) only commutes
    the ring hom past `dblXYZ`; *all* mathematical content comes from the project's `dblXYZ_smulRing`
    (→ `dblXYZ_smulField`, a genuine multi-step proof) and the project's `ringEval`/`smulEval`/`ω`.

Attempt 2 — directly from mathlib's `normEDS`/`dblXYZ`/`evalEval`, bypassing the project chain: would
require building the entire evaluated `(φₙ,ωₙ,ψₙ)`-as-Jacobian-coordinates theory and re-deriving the
doubling identity for it — a substantial development, not ≤3 calls, and **still needs `ω`** (absent from
mathlib). Not composable.

Conclusion: **NOT COMPOSABLE FROM MATHLIB.** mathlib's `map_dblXYZ` supplies only the ring-hom-transfer
wrapper; the mathematics is project-internal (`dblXYZ_smulRing` → `dblXYZ_smulField`), and the statement
itself requires the project's unupstreamed `ω` and `smulEval`.

---

## Verdict: `WeierstrassCurve.dblXYZ_smulEval`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- **Literature (Phase 3):** classical mathematics — the *doubling half* of the division-polynomial
  scalar-multiplication formula `[n]P = (φₙ : ωₙ : ψₙ)` (Silverman *AEC* Ex. 3.7; Washington *ECNT* §3.2;
  Sutherland 18.783 L#6; Wikipedia). The literature names the *full formula*, not this per-evaluation
  doubling step; it is an internal intermediate, not a headline.
- **Generality (Phase 4):** **MAXIMALLY GENERAL** — already over `[CommRing R]` (more general than the
  field statements in the literature), arbitrary `W`, arbitrary `n`, with only the unavoidable "on the
  curve" hypothesis. No generalise-first action; no modern-idiom restatement.
- **Mathlib search (Phase 5):** **not in mathlib**, and **not statable in mathlib** — mathlib has `dblXYZ`,
  `map_dblXYZ`, `evalEval`, `ψ`, `φ`, but **no `ω`** (explicit TODO in `DivisionPolynomial/Basic.lean:71,83`;
  project-defined at `DivisionPolynomialOmega.lean:74`), **no `smulEval`**, and **no `n • P` division-
  polynomial formula**. Rules out `NO-mathlib-has-it`.
- **Composition (Phase 6):** **NOT-COMPOSABLE** from mathlib — the one short proof's content is the project
  lemma `dblXYZ_smulRing` (→ `dblXYZ_smulField`), with mathlib supplying only `map_dblXYZ` as a transfer
  wrapper. Rules out `NO-composable-from-mathlib`.

**Rationale (why BORDERLINE, not a decisive bucket).**

`dblXYZ_smulEval` states real classical mathematics, but its disposition is a **packaging decision a human
must make**, identical in kind to its already-assessed universal twin `dblXYZ_smulRing` (BORDERLINE), just
one specialization step closer to a concrete curve. Three things are simultaneously true. (1) It is
genuinely **absent from mathlib**, and — critically — its *statement is not even expressible in current
mathlib*, because it mentions the y-coordinate division polynomial `ω` (a real, **explicitly-TODO'd gap** in
mathlib's `DivisionPolynomial/Basic.lean`) and the project packaging `smulEval`. So it is not
`NO-mathlib-has-it`, and whether it can go to mathlib at all is **contingent on first upstreaming `ω`** (and
the `Universal.curve` / `ringEval` infrastructure that its proof rides on). (2) It is **not composable from
mathlib**: the lone mathlib call (`map_dblXYZ`) does only the ring-hom transfer; the mathematical content is
the project's `dblXYZ_smulRing` → `dblXYZ_smulField`. So it is not `NO-composable-from-mathlib`. (3) It is
**not a standalone catalog-worthy result**: it is one of a *family* of internal intermediates
(`dblXYZ_smulField` → `dblXYZ_smulRing` → **`dblXYZ_smulEval`**, plus the `addXYZ_*` analogues) whose sole
job is to assemble the citable `zsmul_eq_smulEval`; it has exactly **one consumer** (the even branch of that
proof, line 602) and no independent API role. So it is not a clean `YES-add-as-is`.

The lemma therefore **travels to mathlib only as part of the `zsmul_eq_smulEval` development**, and only
after the missing infrastructure lands — at which point a maintainer must decide whether such evaluated
intermediates ship as `private`/internal lemmas, get inlined into the multiplication-formula proof, or are
kept as a small public API. That internal-vs-public, scope-of-package judgment is exactly what
`BORDERLINE-needs-human` is for; cost is *not* the reason for the verdict (the lemma is already maximally
general and cheap), so this is not a disguised generalise-first.

**What a human needs to decide (actionable; ≤5 questions):**
1. **Scope.** Is the AINTLIB plan to upstream the whole division-polynomial multiplication-formula
   development (`Universal.curve` + `ω` + `smulPoly`/`smulRing`/`smulField`/`smulEval` + `zsmul_eq_smulEval`)
   to mathlib? If **no**, this stays project-local and there is no further action.
2. **Prerequisite — `ω`.** Upstream `WeierstrassCurve.ω` first (mathlib's explicit TODO,
   `DivisionPolynomial/Basic.lean:71,83`; project def at `DivisionPolynomialOmega.lean:74`) — without it,
   `dblXYZ_smulEval` cannot even be *stated* in mathlib. Should `ω` be filed as its own `/mathlibable` (it
   is very likely `YES-add-as-is`)?
3. **Prerequisite — infrastructure.** Upstream `Universal.curve` (+ `CoordinateRing`/`specialize`/`ringEval`;
   see the sibling `curve.md` → `YES-add-as-is`), which the proof's `ringEval_comp_smulRing` /
   `curveRing_map_ringEval` ride on. Confirm this lands first?
4. **Internal-vs-public boundary.** When upstreamed, should `dblXYZ_smulEval` be `private` (or inlined into
   the `zsmul_eq_smulEval` proof)? It has a single consumer and is a pure specialization of
   `dblXYZ_smulRing` — recommended `private`/internal, with the public face being `zsmul_eq_smulEval` and
   the `ω`/`Universal.curve` API.
5. **Cross-project dedup (orthogonal, `main` only).** HasseWeil carries a byte-identical
   `dblXYZ_smulEval` (`Auxiliary/DivisionPolynomial.lean:643`). Should the two forks be unified into a shared
   `Common/` lemma as a `lane:cleanup` ticket before any upstreaming? (This is independent of the mathlib
   verdict.)

**Mathlib building blocks present (for the transfer + frame, not the content):**
- `WeierstrassCurve.Jacobian.dblXYZ` — `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:349`
- `WeierstrassCurve.Jacobian.map_dblXYZ` — `…/Jacobian/Formula.lean:742` (the only mathlib call in the proof)
- `Polynomial.evalEval` — `Mathlib/Algebra/Polynomial/Bivariate.lean:44`
- `WeierstrassCurve.Affine.Equation` — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:149`
- `WeierstrassCurve.ψ`, `WeierstrassCurve.φ` — `…/DivisionPolynomial/Basic.lean:401, :448`
  (but **`ω` is absent** — the key missing piece, an explicit mathlib TODO).

---

## Next step

Do **not** treat `dblXYZ_smulEval` as an independent add/skip decision. Route it to a **human** as part of
the **`zsmul_eq_smulEval` upstreaming package**: decide (a) whether that whole development goes to mathlib,
and if so (b) upstream its prerequisites first — the y-coordinate division polynomial `ω` (mathlib's own
TODO; file its own `/mathlibable`, likely `YES`) and `Universal.curve` (`curve.md` → `YES`) — then ship
`dblXYZ_smulEval` **as an internal/`private`** lemma (single consumer `zsmul_eq_smulEval`, a pure
specialization of `dblXYZ_smulRing`). It is `BORDERLINE-needs-human`: absent from mathlib, **not statable in
current mathlib** (needs `ω`), not composable from mathlib primitives, and not a standalone catalog-worthy
result — a packaging / internal-boundary judgment, not a mechanical verdict. (Separately, on `main`, a
`lane:cleanup` ticket should dedup the byte-identical HasseWeil copy.)
