# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulY`

## Verdict: BORDERLINE-needs-human

One-line summary: a one-line `def` (`ωₙ/ψₙ³` over the project's bespoke universal
field) that is private scaffolding for the universal-case induction. The genuinely
mathlib-worthy object is the `ω` division-polynomial family + the base-agnostic
multiplication-by-`n` formula `zsmul_eq_smulEval` that this scaffold serves — both
of which **are** missing from mathlib. Whether `smulY` *itself* (as opposed to that
package) goes to mathlib is an API-shape judgment call for a human.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — authoritative grep over `.lake/packages/mathlib`)
- decl `WeierstrassCurve.Universal.Affine.smulY`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:168`
- kind:                      def (noncomputable section)
- has sorry:                 no
- qualified name:            confirmed — namespaces `WeierstrassCurve` (L76) → `Universal` (L86) → `Affine` (L157); `smulY` at L168
- module docstring summary:  proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coords for any integer `n` and nonsingular point on a Weierstrass curve over a field.

### Statement (Phase 1)

`smulY n` is the rational function `ωₙ(x,y) / ψₙ(x,y)³`, evaluated in the project's
**universal field** `Universal.Field = FractionRing (curve.CoordinateRing)` (the
fraction field of the coordinate ring of the universal pointed Weierstrass curve
over `ℤ[a₁,a₂,a₃,a₄,a₆,X,Y]`). It is the candidate `Y`-coordinate of the point
`n • (X, Y)` on the universal curve; the file then proves it *is* that coordinate
(`zsmul_point_eq_smulX_smulY`, L344).

```
def smulY : Universal.Field := polyToField (curve.ω n) / (ψᵤ n) ^ 3
```

- `curve.ω n` — the `ω` family of division polynomials (`WeierstrassCurve.ω`,
  `DivisionPolynomialOmega.lean:74`), the `Y`-coordinate numerator. **PROJECT-LOCAL.**
- `ψᵤ n = polyToField (curve.ψ n)` — the `ψ` family mapped into the universal field.
- `polyToField : Poly →+* Universal.Field` — project-local ring hom (`Universal.lean:108`).

Conclusion (math): defines `Y`-coord of `n·(X,Y)` as `ωₙ/ψₙ³`. Conclusion (Lean): n/a — definition.

### Size classification (Phase 2a)

Verdict: SMALL. Helper `def` (the `Y`-coordinate companion to `smulX`), part of the
universal-field scaffolding for the main result, not itself a `## Main definition`.
(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`polyToField (curve.ω n) / (ψᵤ n) ^ 3`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|--------------------------------------------------------------------------|
| Avoid defeq abuse                 | no       | not sealed for unfolding control; `smulX/smulY` are routinely unfolded via `simp [smulY, ...]` in neighbouring lemmas |
| Avoid typeclass diamonds          | no       | no instance resolution involved; plain field element                     |
| Mark semantic intent / API name   | yes      | named anchor `(smulX, smulY)` is the X/Y coordinate pair threaded through the whole universal-case proof (L172–L390) and the duplicate in HasseWeil; consumers depend on the name |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name). Carried to Phase 7.

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | `nP = (phi_n/psi_n^2, omega_n/psi_n^3)` division polynomials                                            | yes  | `n·(x,y) = (φₙ/ψₙ², ωₙ/ψₙ³)`     | Multiple crypto/NT sources; Silverman cited as canonical |
|  2 | WebSearch (general form / Silverman) | `division polynomial omega_n y-coordinate multiplication-by-n Silverman`                            | yes  | `ωₘ = (4y)⁻¹(ψₘ₊₂ψₘ₋₁² − ψₘ₋₂ψₘ₊₁²)`; `n(x,y)=(φₙ/ψₙ²,ωₙ/ψₙ³)` for `n≥2` | MIT 18.783 Lecture 6 (Sutherland) — the canonical lecture-note reference |
|  3 | WebSearch (general Weierstrass / a₁,a₃) | `Weierstrass omega division polynomial a1 a3 "2 omega" psi phi universal`                       | yes  | `φₙ,ωₙ ∈ ℤ[a₁,a₂,a₃,a₄,a₆,x,y]`; `4yωₙ = Ψₙ₋₁²Ψₙ₊₂ − Ψₙ₋₂Ψₙ₊₁²`; `ψ₂ = 2y+a₁x+a₃` | confirms the **universal/general-Weierstrass** framing matches the project exactly |
|  4 | ChatGPT MCP                      | (server reported up but not exercised — channels 1–3 + Stacks already pinned the standard form unambiguously) | n/a  | —                                | standard form already triangulated by 3 independent web sources + Stacks |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` — directory absent                                   | n/a  | —                                | only `overview/` present under `.mathlib-quality/` |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                                | n/a  | —                                | nLab has no dedicated division-polynomial page; concept is classical-NT, not categorical |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                | not a categorical concept |
|  8 | Stacks Project                   | division polynomials / multiplication-by-n (algebraic geometry)                                         | partial | multiplication-by-`n` map on elliptic curves is standard | Stacks treats `[n]` abstractly; the explicit `ωₙ/ψₙ³` coordinate is in NT texts (Silverman, Sutherland), not Stacks |
|  9 | MathOverflow / Math.SE           | omega division polynomial general Weierstrass form                                                      | yes  | same general form as #3          | corroborates the `ℤ[a₁..a₆,x,y]` universal framing |
| 10 | recent arXiv (last 5 years)      | sequences associated to elliptic curves; integral points & explicit valuations of division polynomials | yes  | uses `φₙ,ωₙ,ψₙ` with the same multiplication formula | arXiv:1909.12654, arXiv:1108.3051 — formula is live in current literature |

### Literature summary (Phase 3)

Concept identified as: the **`ω` (omega) division polynomial** / the `Y`-coordinate
of the **multiplication-by-`n` formula** `n·(x,y) = (φₙ/ψₙ², ωₙ/ψₙ³)`.
Sources agree on the standard form: **yes**. For short Weierstrass `y²=x³+ax+b`:
`ωₙ = (4y)⁻¹(ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)`. For the **general** Weierstrass form the standard
references state `φₙ, ωₙ ∈ ℤ[a₁,a₂,a₃,a₄,a₆,x,y]` with `ψ₂ = 2y + a₁x + a₃` —
i.e. exactly the project's universal setting; the project's `ω_spec`
(`2ωₙ + a₁φₙψₙ + a₃ψₙ³ = ψc`) is the general-form analogue of `4yωₙ = …`.
Most general standard form: over the universal ring `ℤ[a₁,…,a₆,x,y]`, then specialised.
Disagreement with the literature: none — `smulY = ωₙ/ψₙ³` is verbatim the `Y`-coordinate.

### Generality analysis — `smulY`

Literature-standard form (Phase 3): the multiplication-by-`n` `Y`-coordinate
`ωₙ/ψₙ³`, with `ωₙ` a polynomial over the universal coefficient ring, specialised
to a point on any Weierstrass curve over any (commutative ring / field) base.

| # | Parameter / hypothesis      | Current Lean form                         | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|-------------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | ambient field/ring          | bespoke `Universal.Field = FractionRing (curve.CoordinateRing)` | universal ring `ℤ[a₁..a₆,x,y]`, then specialised to **any** base | yes — see note | `smulY` is intentionally the *universal* instance; the base-agnostic statement is a **different decl** (`zsmul_eq_smulEval`, L590, over any field `F`). `smulY` itself is fixed to the universal field by design. |
| 2 | division-polynomial inputs  | `curve.ω`, `curve.ψ` (project `ω`/`ψ`)    | `ωₙ`, `ψₙ`                                | n/a                 | exactly the standard objects |

**Generality verdict (Phase 4b):** `smulY` is NOT a free-standing general statement —
it is the **universal specialisation by construction**. The base-general form already
exists in the project as a separate result (`smulEval`/`zsmul_eq_smulEval`, L551/L590).
So "generalise `smulY`" is not the right framing: `smulY` is scaffolding; the general
deliverable is its own decl. Cost of "generalising" `smulY`: n/a (the general form is a
different declaration that already exists).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | bundled-hypotheses → typeclasses?                                        | no       | already typeclass-driven (`CommRing`, `Field`) | — |
|  2 | sequences/metric → filters/topological?                                 | no       | purely algebraic; no topology | — |
|  3 | explicit construction → universal-property class?                       | partial  | the *whole point* is that the project builds the formula via the **universal pointed curve** (a universal-property-style construction); this is already the modern idiom mathlib would want | the universal-curve approach is what lets `zsmul_eq_smulEval` cover char-2 by specialisation |
|  4 | set-with-predicate → bundled substructure?                              | no       | — | — |
|  5 | field-specific → module/semiring weakening?                             | no       | already as general as the maths allows (`ω` over any `CommRing`) | — |
|  6 | 1-categorical → higher-categorical?                                     | no       | — | — |
|  7 | concrete index (ℤ) → general?                                           | no       | `n : ℤ` is intrinsic (the multiplication index) | — |

**Modern-idiom verdict:** no modernisation move on `smulY` itself. The project already
uses the contemporary "universal curve over `ℤ[a₁..a₆,X,Y]`, then specialise" idiom —
which is precisely the right mathlib framing.

### Diamond / defeq risk — `smulY`

| # | Risk                          | Verdict | Evidence / rationale                                                |
|---|-------------------------------|---------|---------------------------------------------------------------------|
| 1 | Typeclass diamond             | none    | plain field element; no instance produced                           |
| 2 | Reducibility leak             | low     | not `@[reducible]`; routinely unfolded via explicit `simp [smulY]` in neighbours — intended |
| 3 | Non-canonical unfolding       | low     | `simp` unfolds only when `smulY` is named in the simp set; no global surprise |
| 4 | Instance priority collision   | none    | not an instance                                                     |
| 5 | Universe-polymorphism issues  | none    | monomorphic (`Universal.Field : Type`)                              |
| 6 | Coercion ambiguity            | none    | no coercion                                                         |

**Risk verdict (Phase 4.5):** overall **NONE/LOW**. No infrastructure obstacle. (Note:
this assesses `smulY` as-is over the bespoke universal field; a mathlib-facing `ω`/formula
package would be assessed separately.)

### Mathlib search-status: `smulY`

[A] Lean-Finder       n/a — MCP index tool not surfaced in this environment; substituted authoritative source grep (method D, below)
[B] Loogle            n/a — MCP index tool not surfaced; substituted source grep
[C] LeanSearch        n/a — MCP index tool not surfaced; substituted source grep
[D] Grep mathlib src  `smulY|smulX|smulEval|zsmul_eq_smul` in elliptic context → **no hits**; `def ω` in `.../EllipticCurve/` → **no hits**; coordinate-scalar formula in `.../EllipticCurve/` → **no hits**
[E] Name pattern (LSP workspaceSymbol) n/a — no Lean LSP server; covered by D

Searched for both the user's form (`smulY = ωₙ/ψₙ³`) and the literature-standard form
(the `ω` family + multiplication-by-`n` coordinate formula).

Key source-grep findings:
- `.lake/packages/mathlib/.../DivisionPolynomial/Basic.lean` defines `ψ₂, Ψ₂Sq, Ψ₃,
  preΨ', preΨ, ΨSq, Ψ, Φ, ψ, φ` — and **no `ω`**. Mathlib's division-polynomial layer
  stops at the `X`-coordinate numerator `φ`; the `Y`-coordinate numerator `ω` is absent.
- `.lake/packages/mathlib/.../NumberTheory/EllipticDivisibilitySequence.lean` has
  `IsEllSequence, preNormEDS, normEDS, complEDS, complEDS₂` — and **no `ω`, no
  multiplication-by-`n` point formula** (its `## Main statements` are explicit TODOs).
- The prerequisite primitives `smulY` (via `ω`) needs — `redInvarNum`, `redInvarDenom`,
  `invarDenom`, `compl₂EDSAux`, `invar` — are **all project-local, zero in mathlib**.
- No `n • P` rational-coordinate formula for `Affine.Point` anywhere in mathlib's
  `EllipticCurve/`.

Concluded: **not in mathlib** (source grep exhausted both forms; the `ω` family,
the formula, and `ω`'s supporting primitives are all missing). Mathlib has the
*sibling* layer (`ψ`, `φ`, `normEDS`, `complEDS`) but not this.

### Call sites — `smulY`

Internal use count (this project, excluding the declaring `def` line): **~33** within
`ZSMul.lean` alone (the entire `Universal.Affine` scalar-multiplication development).
External-to-file callers: HasseWeil project (`Auxiliary/DivisionPolynomial.lean`) carries
a **verbatim duplicate** `smulY` + its whole lemma family — cross-project reuse.

| Caller file:line                                   | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------|--------------------------------------------------------------------|
| ZSMul.lean:172,174                                 | `smulY_zero`, `smulY_one` (base-case simp lemmas)                   |
| ZSMul.lean:227–231                                 | `smulY_sub_negY`: `smulY n - negY (smulX n) (smulY n) = ψᵤ(2n)/ψᵤ(n)⁴` |
| ZSMul.lean:277–281                                 | `addY_smulX_smulY`: `addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2` |
| ZSMul.lean:290–293                                 | `smulY_neg`: `smulY (-n) = negY (smulX n) (smulY n)`               |
| ZSMul.lean:324–331                                 | `smulY_add_sub_negY` (the addition-formula `Y` identity)          |
| ZSMul.lean:344–356,385–390                         | **main thm** `zsmul_point_eq_smulX_smulY`; `nonsingular_smulX_smulY` |
| ZSMul.lean:414,435                                 | `smulPoly := ![φ, ω, ψ]`; `smulField` (Jacobian); `simp [Affine.smulY]` |
| HasseWeil/Auxiliary/DivisionPolynomial.lean:243…501 | duplicated `smulY` + full lemma family + `zsmul_point_eq_smulX_smulY` |

Inline-derivation grep: none — consumers use `smulY` directly, never re-derive `ωₙ/ψₙ³`.

Signal: **K ≫ 3, no inline bypass, plus cross-project duplication** → real, depended-on
API (for the X/Y-coordinate pair). Strong YES-leaning on the *content*; the only question
is the mathlib-facing *shape* (see verdict).

### Composition check (Phase 6)

Can `smulY` be derived from mathlib in ≤3 chained calls? **NO.**

Attempt 1: `polyToField (curve.ω n) / (ψᵤ n)^3` — but `curve.ω` does not exist in mathlib
(no `ω` family), and `polyToField` / `Universal.Field` are project-local. Fails at the
first symbol.

Attempt 2: reconstruct `ω` from mathlib's `Ψ`/`φ`/`normEDS`? `ω`'s definition uses
`redInvarDenom`, `compl₂EDSAux`, `redInvarNum`, `invarDenom`, `invar` — **none in mathlib**.
Building `ω` would itself be a multi-declaration development (the project spends a whole
file, `DivisionPolynomialOmega.lean`, plus a 76 KB `EllipticDivisibilitySequence.lean`
fork, on it). Far more than 3 calls; real mathematics, not glue.

Conclusion: **NOT-COMPOSABLE.** `smulY` sits atop an entire `ω`/EDS layer that mathlib
lacks.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulY`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature (Phase 3): `n·(x,y) = (φₙ/ψₙ², ωₙ/ψₙ³)` is the canonical multiplication-by-`n`
  formula (Silverman; MIT 18.783); the general-Weierstrass `ωₙ ∈ ℤ[a₁..a₆,x,y]` framing
  matches the project exactly. `smulY = ωₙ/ψₙ³` is verbatim the standard `Y`-coordinate.
- Generality (Phase 4): `smulY` is the **universal specialisation by construction**; the
  base-agnostic deliverable is a separate, already-present decl (`zsmul_eq_smulEval`, L590).
  Modern-idiom: already idiomatic (universal-curve approach). No weakening of `smulY` itself.
- Mathlib search (Phase 5): **not in mathlib** — no `ω`, no multiplication-by-`n` coordinate
  formula, and none of `ω`'s supporting primitives (`redInvarNum/Denom`, `invar`, `compl₂EDSAux`).
- Composition (Phase 6): **NOT-COMPOSABLE** — requires the whole missing `ω`/EDS layer.

**Rationale:**

The *mathematics* here is squarely mathlib-worthy and genuinely missing: mathlib's
division-polynomial development stops at `ψ`/`φ` and has the multiplication-by-`n` formula
as an explicit TODO (`EllipticDivisibilitySequence.lean` `## Main statements`). The `ω`
family and the formula `n • P = (φₙ : ωₙ : ψₙ)` are exactly the gap this project fills, the
form matches the literature standard, and the API is heavily used (K ≫ 3) and even
duplicated across two AINTLIB projects. None of the NO buckets fit: it is not in mathlib,
and it is not a ≤3-call composition.

But `smulY` **itself** is the wrong granularity to hand to mathlib. It is a one-line `def`
fixed to the project's bespoke `Universal.Field`, serving as internal scaffolding for the
universal-case induction. The base-general object a mathlib reviewer would actually want is
the package `(WeierstrassCurve.ω  +  zsmul_eq_smulEval)` — i.e. add `ω` as the public
`Y`-coordinate division polynomial (sibling to the existing `φ`) in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`, and add the
multiplication-by-`n` coordinate theorem over an arbitrary base, discharging mathlib's
standing TODO. `smulY` would then be a private universal-field helper *inside* that proof,
not a standalone mathlib declaration. Choosing between "upstream `smulY` as written" and
"upstream the `ω`/formula package and keep `smulY` as a proof-internal helper" is a genuine
API-shape decision a human owner should make — which is why this is BORDERLINE rather than a
bare YES. (Per the verdict rules, this is also not a cost-driven downgrade: the `ω`/formula
package is worth the work; the open question is packaging, not effort.)

**Numbered questions (≤5):**

1. Should the mathlib contribution be the **`ω` division-polynomial family + the
   multiplication-by-`n` coordinate theorem `zsmul_eq_smulEval`** (the base-agnostic
   deliverables), rather than `smulY` itself? (If yes → this decl is NO-composable
   proof-internal scaffolding, and the YES effort moves to `ω` + `zsmul_eq_smulEval`.)
2. Is mathlib happy to take the **whole `ω`/EDS layer** this rests on — `WeierstrassCurve.ω`,
   `ψc`, `invar`, `redInvarNum/Denom`, `compl₂EDSAux`, and the EDS extensions in the project's
   `EllipticDivisibilitySequence.lean` fork — as a coordinated multi-PR series? (This is the
   real cost centre; `smulY` is the tip.)
3. The project forks mathlib's `complEDS₂`/`complEDS` as `compl₂EDS`/`compl₂EDSAux` (naming +
   API skew). Before upstreaming, should the `ω` development be **rebased onto mathlib's
   existing `complEDS` API** so it extends rather than duplicates? (Affects whether `ω` lands
   cleanly.)
4. If the answer to Q1 is "keep `smulY` too", do you want it stated over the **universal field**
   as now, or refactored to a base-general `W.smulEvalY` (mirroring the existing general
   `smulEval`)? The universal-field version is genuinely proof-internal; the base-general one
   would be the public-facing form.

**Next action:** owner answers Q1–Q4. Most likely resolution: `smulY` → proof-internal helper
(NO-composable, not upstreamed standalone); open the real mathlib effort as a `feat(EllipticCurve):
add ω division polynomial + multiplication-by-n formula` PR series targeting
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`, discharging the
`EllipticDivisibilitySequence` TODO. Re-run `/mathlibable WeierstrassCurve.ω` and
`/mathlibable WeierstrassCurve.zsmul_eq_smulEval` to drive those.

---

## Next step

Owner answers the four questions above. The dominant signal (novel, missing-from-mathlib,
matches the literature standard, heavily used, NOT-composable) is YES-on-the-content; the
BORDERLINE is purely about *which* declaration carries it to mathlib — `smulY` as written,
or the base-agnostic `ω` + `zsmul_eq_smulEval` package that `smulY` scaffolds.
