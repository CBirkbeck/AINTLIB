# Mathlibable assessment: `WeierstrassCurve.Universal.cusp_Ψ₃`

> Qualified name **verified from source**. The lemma sits at
> `projects/NagellLutz/LutzNagell/ZSMul.lean:111`, inside `namespace WeierstrassCurve`
> (opened line 76) → `namespace Universal` (opened line 86). Hence the full name is
> **`WeierstrassCurve.Universal.cusp_Ψ₃`** (the parsed name in the prompt was correct).

## Baseline (Phase 0)

- lake build: stale locally (assessment reasons from the source statement, per the run brief).
- decl `WeierstrassCurve.Universal.cusp_Ψ₃`: resolved at `ZSMul.lean:111`.
- kind: `lemma`.
- has sorry: no.
- module docstring summary: ZSMul.lean proves `WeierstrassCurve.zsmul_eq_smulEval`
  (`n • P` in Jacobian coordinates via division polynomials); `cusp_Ψ₃` is one of the
  small "value at the cusp" helpers feeding the universal-`ψₙ`-non-vanishing argument.

## The declaration

```lean
lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
```

- `cusp` is the **project-local** singular cubic `Y² = X³`, defined at
  `projects/NagellLutz/LutzNagell/Universal.lean:180` as
  `def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }`,
  i.e. the Weierstrass record `⟨0,0,0,0,0⟩`.
- `Ψ₃` is the (univariate) 3-division polynomial. In this project (a fork of mathlib's
  `DivisionPolynomial.*`) it is
  `noncomputable def Ψ₃ : R[X] := 3*X^4 + C b₂*X^3 + 3*C b₄*X^2 + 3*C b₆*X + C b₈`
  (`projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:65`) — **identical, character for
  character, to mathlib's** `WeierstrassCurve.Ψ₃`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:142`).
- `X` is mathlib's `Polynomial` variable (`Polynomial.X`); the `b₂,b₄,b₆,b₈` are mathlib's
  b-invariants (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:101-113`).

**Mathematical content.** The 3-division polynomial of any Weierstrass curve is
`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`. The cusp `Y²=X³` has
`a₁=a₂=a₃=a₄=a₆=0`, hence every b-invariant vanishes (`b₂=a₁²+4a₂=0`, `b₄=2a₄+a₁a₃=0`,
`b₆=a₃²+4a₆=0`, `b₈=a₁²a₆+4a₂a₆−a₁a₃a₄+a₂a₃²−a₄²=0`), collapsing the formula to `3X⁴`. So this
lemma is a single **numeric specialisation** of an already-existing mathlib formula to one fixed
singular curve. (This matches the textbook short-Weierstrass formula `ψ₃ = 3x⁴+6ax²+12bx−a²`,
which for `a=b=0` is `3x⁴`.)

## Statement (Phase 1)

`cusp_Ψ₃` states that the univariate 3-division polynomial of the cuspidal cubic `Y²=X³`,
viewed over `ℤ[X]`, equals `3X⁴`.

- Variables / typeclasses: none free — `cusp : Affine ℤ` is a fixed constant; `Ψ₃` is
  evaluated over `R = ℤ`.
- Hypotheses: none.
- Conclusion (math): `Ψ₃(cusp) = 3X⁴` in `ℤ[X]`.
- Conclusion (Lean): `cusp.Ψ₃ = 3 * X ^ 4`.

## Size classification (Phase 2a)

Verdict: **SMALL**. A numeric value of one fixed polynomial at one fixed singular curve; a
helper, not a structure or named theorem. (Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner def-exemption machinery does
not apply. (It *is* a one-line proof, which is a NO-leaning signal for mathlib inclusion, but the
2b exemption table is for definitions.)

## Role in the project

`cusp_Ψ₃` is one of three companion value lemmas on the same source-line block:

```lean
lemma cusp_ψ₂    : cusp.ψ₂    = 2 * Y       := …   -- ZSMul.lean:110
lemma cusp_Ψ₃    : cusp.Ψ₃    = 3 * X ^ 4   := …   -- ZSMul.lean:111  (this decl)
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6   := …   -- ZSMul.lean:112
```

These three feed `polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n` (ZSMul.lean:114) and
`polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2` (ZSMul.lean:122), via
`rw […, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]` + `normEDS_two_three_two` / `compl₂EDS_two_three_two`.
Those in turn drive `ψᵤ_ne_zero` (ZSMul.lean:142): the universal division polynomial `ψₙ` is
non-zero for `n ≠ 0`, proved by specialising the universal ring to `ℤ` at the cusp point `(1,1)`
(where `ψₙ(1,1)=n`). This is the project's bespoke **"degenerate-fibre" technique** for universal
non-vanishing — the same plumbing the siblings `cusp_ψ₂` and `cusp_equation_one_one` support.

## Call sites — `WeierstrassCurve.Universal.cusp_Ψ₃`

Internal use count (excluding the declaring line): **2** — both **inside the same file**
ZSMul.lean. External-to-file callers: **0**.

| Caller file:line | Usage pattern |
|---|---|
| ZSMul.lean:115 | `rw [ψ, map_normEDS, ←evalEval_ψ₂, ←evalEval_Ψ₃, ←evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]` |
| ZSMul.lean:124 | `simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, compl₂EDS_two_three_two]` |

Inline-derivation grep (was `cusp.Ψ₃ = 3X⁴` re-derived elsewhere without the lemma?): none.
The value is computed once, named, and reused at the two `rw`/`simp` sites — correct local API
hygiene. (K=2 same-file uses, no external consumers: textbook local-scaffolding signal.)

## (3) Literature search — EXHAUSTIVE protocol

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---|---|---|---|---|
| 1 | WebSearch (specific) | "elliptic curve 3-division polynomial cuspidal curve y²=x³ evaluation 3x⁴" | partial | general `ψ₃ = 3x⁴+6ax²+12bx−a²`; for `a=b=0` ⇒ `3x⁴` | confirms the value; no source names the cusp evaluation as a theorem |
| 2 | WebSearch (general) | "3-division polynomial Weierstrass ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈" | yes | the full b-invariant form (mathlib's form) | standard; Silverman AEC III.§, Washington §3.2 |
| 3 | WebSearch (aliases / EDS) | "division polynomial singular cubic cusp elliptic divisibility sequence Wₙ = n" | yes | degenerate EDS on additive reduction `Wₙ = n` | Ward; arXiv:2102.07573, arXiv:0710.1316 — known device, not a named lemma for `Ψ₃` |
| 4 | ChatGPT MCP | "standard def of the 3-division polynomial, its generality, and whether its evaluation on the cuspidal cubic Y²=X³ is a named result" | n/a — MCP down | — | brief notes the run brief: ChatGPT MCP may be down; covered by channels 1–3,9,10 |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` | n/a | references dir absent (only `overview/` present) | recorded n/a |
| 6 | nLab | "division polynomial" / "elliptic divisibility sequence" | partial | nLab has EDS / division-polynomial recurrence, general curve | no cusp-specialisation statement |
| 7 | nCatLab | — | n/a | not a categorical concept | recorded n/a |
| 8 | Stacks Project | "division polynomial" | n/a | Stacks has elliptic curves but not the division-polynomial value table | recorded n/a |
| 9 | MathOverflow / MSE | "3-division polynomial y²=x³ cusp value 3x⁴" | partial | confirms `ψ₃` of `y²=x³` is `3x⁴` as a computation | treated as exercise/computation, not a quotable named theorem |
| 10 | arXiv (recent) | "division polynomials singular Weierstrass cubic" | yes | division polys defined for possibly-singular cubics (e.g. arXiv:1105.5633, 1108.3051) | the *general* polynomial is studied; the cusp value is a substitution, not a headline result |

The general `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` is textbook and standard. The cusp evaluation
`cusp.Ψ₃ = 3X⁴` is a one-line substitution (`b₂=b₄=b₆=b₈=0`) that **no source records as a named
statement**.

### Literature summary (Phase 3)

Concept identified as: the **3-division polynomial `Ψ₃`** of a Weierstrass curve, evaluated on the
**cuspidal cubic `Y²=X³`**.
Sources agree on the standard form: yes — `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` (b-invariant form,
= mathlib's definition); short-Weierstrass form `3x⁴+6ax²+12bx−a²`.
Most general standard form: the b-invariant polynomial over an arbitrary `[CommRing R]` curve —
**this is exactly mathlib's `WeierstrassCurve.Ψ₃`**.
Generality dimensions where the literature varies: only the base ring / model (short vs. long
Weierstrass); the b-invariant form is the maximal one, already in mathlib. The cusp evaluation is a
*specialisation*, the opposite of a generalisation.
Disagreement with the literature: none — `3X⁴` is the correct value, and the project's `Ψ₃` is
verbatim mathlib's.

## (4) Generality analysis — `WeierstrassCurve.Universal.cusp_Ψ₃`

Literature-standard form: `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` over arbitrary `[CommRing R]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|---|---|---|---|---|
| 1 | the curve | fixed `cusp = ⟨0,0,0,0,0⟩ : Affine ℤ` | arbitrary Weierstrass curve over `[CommRing R]` | n/a | this is a *value at one fixed curve*, not a parametric statement; the "general form" **is** mathlib's `Ψ₃` def, which this evaluates |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY SPECIALISED** (a numeric value at one fixed singular curve) — the
opposite of a generalisation target. Its general parent — `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`
over any `[CommRing R]` curve — **already lives in mathlib** as the *definition*
`WeierstrassCurve.Ψ₃`. Number of weakening opportunities: 0. There is no more-general restatement
to upstream; any generalisation simply *is* mathlib's existing `Ψ₃`.

### Modern-idiom check (Phase 4c)

No modern-idiom move applies: this is a closed-form numeric evaluation of a concrete polynomial
over `ℤ`. There is no preamble to typeclass-ify, no sequence/metric to filter-ise, no construction
to characterise by a universal property, no set-with-closure to bundle, no field-specific
hypothesis to weaken, no 1-categorical statement to lift, and the index (the curve) is a fixed
constant, not a varying `ℕ/ℤ/ℝ`. Modern idiom available: **no**.

## (4.5) Diamond / defeq risk

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths
introduced).

## (5) Mathlib search-status: `WeierstrassCurve.Universal.cusp_Ψ₃`

[A] Lean-Finder — "3-division polynomial of cuspidal curve equals 3X^4" — no hit (mathlib has no
    `cusp` object; only the general `Ψ₃`).
[B] Loogle — `WeierstrassCurve.Ψ₃ = _`, `_ = 3 * Polynomial.X ^ 4` — the general `Ψ₃` def appears
    (`DivisionPolynomial/Basic.lean:142`); no cusp-specialised lemma.
[C] LeanSearch — "value of third division polynomial on the cusp Y²=X³" — no hit.
[D] Grep mathlib src —
    `grep -rn "Ψ₃" Mathlib/AlgebraicGeometry/EllipticCurve/` → the **general** def
    (`Basic.lean:142`) and its degree lemmas (`Degree.lean:93-121`: `natDegree_Ψ₃`, `coeff_Ψ₃`,
    `leadingCoeff_Ψ₃`, `Ψ₃_ne_zero`). `grep -rn "cusp" Mathlib/` → only the **modular-forms** sense
    (`cuspFunction`, `ModularForms/Cusps.lean`, `Analysis/Complex/Periodic.lean`). No `def cusp`
    for `Y²=X³`, no `3 * X ^ 4` evaluation, anywhere in mathlib (incl. `EllipticDivisibilitySequence.lean`).
[E] Name pattern — `cusp_Ψ₃`, `cusp.Ψ₃`, `Ψ₃_cusp` over mathlib → no hit.

Searched for **both** the user's form (cusp value) and the literature-standard form (general
`Ψ₃`). The general form is already mathlib's *definition*; the cusp specialisation is absent and
has no `cusp` object to attach to.

Concluded: the **general** `Ψ₃` is in mathlib as `WeierstrassCurve.Ψ₃`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:142`); the **cusp
specialisation as a named lemma is not in mathlib**, and mathlib has no `cusp` definition.

## (6) Composition check

Can `cusp_Ψ₃` be derived from mathlib in ≤3 chained calls? **Yes.** Given mathlib's definition
`Ψ₃ = 3X⁴ + C b₂·X³ + 3·C b₄·X² + 3·C b₆·X + C b₈` and the b-invariant defs
(`Weierstrass.lean:101-113`), for `cusp` (all `aᵢ=0`) every b-invariant is `0`, so:

```lean
example : cusp.Ψ₃ = 3 * X ^ 4 := by
  simp [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, cusp]
```

The project's own one-liner (`simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]`) is **exactly** this composition
(its `Ψ₃`/`bᵢ` are mathlib's). Mathlib decls used: `Ψ₃`, `b₂`, `b₄`, `b₆`, `b₈` — a single `simp`
unfold. Conclusion: **COMPOSABLE** (≤1 `simp` call over mathlib defs; no new general lemma implied).

---

## Verdict: `WeierstrassCurve.Universal.cusp_Ψ₃`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature (3): the general `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` is textbook
  (Silverman AEC; Washington §3.2); short form `3x⁴+6ax²+12bx−a²`. The cusp value `3X⁴` is a
  one-line `b₂=b₄=b₆=b₈=0` substitution named by no source.
- Generality (4): MAXIMALLY SPECIALISED; its general parent **is** mathlib's `Ψ₃` *definition*.
  Nothing to generalise/upstream. No modern-idiom move (4c: no).
- Mathlib (5): the general `Ψ₃` is already in mathlib (`DivisionPolynomial/Basic.lean:142`); no
  `cusp` object and no cusp-`Ψ₃` lemma exist (mathlib "cusp" = modular forms only). `Y²=X³` is
  singular, deliberately outside the EC API.
- Composition (6): COMPOSABLE in ≤1 `simp` over mathlib's `Ψ₃`/`b₂…b₈`. The project's existing
  one-liner is precisely this.

**Rationale.**
`cusp_Ψ₃` is project-local scaffolding, not a mathlib candidate. It says only that the 3-division
polynomial of the cuspidal cubic `Y²=X³` is `3X⁴` — a single evaluation of mathlib's existing
`WeierstrassCurve.Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` at the coefficient record `⟨0,0,0,0,0⟩`,
where all b-invariants vanish. Mathlib already owns the general formula (verbatim — the project's
`Ψ₃` is a fork-identical copy) and has no notion of a "cusp curve" for a named specialisation to
attach to (`Y²=X³` is singular and out of scope for the elliptic-curve API; "cusp" in mathlib is
the unrelated modular-forms sense). This is exactly the situation of its sibling `cusp_ψ₂`
(`NO-composable-from-mathlib`): both are bespoke witnesses in this project's degenerate-fibre proof
that the universal `ψₙ` is non-zero (via `ψₙ(1,1)=n` on the cusp).

**WHY not (refactor-actionable).** The building block is mathlib's `WeierstrassCurve.Ψ₃`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:142`) together with the
b-invariant defs `b₂,b₄,b₆,b₈` (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:101-113`).
The user's statement is a ≤1-call `simp`-specialisation of these for `cusp`. No new mathlib lemma is
needed.

Mathlib building blocks: `WeierstrassCurve.Ψ₃`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:142`),
`WeierstrassCurve.b₂` / `b₄` / `b₆` / `b₈`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:101-113`).

**Composition sketch (≤3 lines):**
```lean
example : cusp.Ψ₃ = 3 * X ^ 4 := by
  simp [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, cusp]
-- (this is essentially the project's existing one-liner)
```

Call sites in this project (Phase 6.0): **K = 2**, both inside ZSMul.lean (lines 115, 124); no
external consumers.

**Refactor plan — keep the local helper; do NOT add to mathlib, do NOT delete.** Like its siblings
`cusp_ψ₂` / `cusp_preΨ₄` / `cusp_equation_one_one`, `cusp_Ψ₃` is a *named* intermediate value reused
inside `polyEval_cusp_ψ` and `polyEval_cusp_ψc` (the engine for universal-`ψₙ`-non-vanishing).
Inlining the `simp` computation at the two `rw [… cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄ …]` / `simp […]`
sites would be strictly worse for readability — the three companion value lemmas are the right
grain. So "NO-composable" here means it **does not belong *in mathlib***; it should remain a
project-local helper in NagellLutz (alongside `def cusp`, `cusp_ψ₂`, `cusp_preΨ₄`,
`cusp_equation_one_one`).

**Next action:** keep `WeierstrassCurve.Universal.cusp_Ψ₃` as project-local scaffolding for the
universal-`ψₙ`-non-vanishing argument. No mathlib PR; no deletion. If anything is ever upstreamed
here, it is the parent `def cusp` itself (see the `cusp` report — `YES-but-generalise-first`), not
this evaluation lemma.

### Sources
- [Algebraic divisibility sequences over function fields (arXiv:1105.5633)](https://arxiv.org/pdf/1105.5633)
- [Integral points on elliptic curves and explicit valuations of division polynomials (arXiv:1108.3051)](https://arxiv.org/pdf/1108.3051)
- [A recurrence relation for elliptic divisibility sequences (arXiv:2102.07573)](https://arxiv.org/pdf/2102.07573)
- [Elliptic nets and elliptic curves (arXiv:0710.1316)](https://arxiv.org/pdf/0710.1316)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
