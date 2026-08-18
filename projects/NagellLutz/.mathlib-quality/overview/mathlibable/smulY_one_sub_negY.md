# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulY_one_sub_negY`

## Verdict: **NO-composable-from-mathlib**

One-line rationale: a one-line `rw` specialization of the sibling lemma
`smulY_sub_negY` at the concrete index `n = 1`; not a standalone mathlib unit.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — task-sanctioned)
- decl `WeierstrassCurve.Universal.Affine.smulY_one_sub_negY`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:233`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  ZSMul.lean proves `WeierstrassCurve.zsmul_eq_smulEval`:
  `n • P = (φₙ : ωₙ : ψₙ)` (Jacobian) / `(φₙ/ψₙ², ωₙ/ψₙ³)` (affine) for any `n : ℤ`
  and any nonsingular affine point `P` on a Weierstrass curve over a field.

Qualified name verified from source: namespaces `WeierstrassCurve` (line 76) →
`Universal` (line 86) → `Affine` (line 157); `lemma smulY_one_sub_negY` at line 233,
before `end Affine` (line 393). The parsed name
`WeierstrassCurve.Universal.Affine.smulY_one_sub_negY` is **correct**.

---

### Statement (Phase 1)

```
lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]
```

Mathematically: at the generic point `(X, Y)` on the universal Weierstrass curve,
**the difference between `Y` and its negative `−Y` equals the 2-torsion /
doubling polynomial `ψ₂`**. For any affine point `(x, y)`, mathlib's
`negY x y = −y − a₁x − a₃`, so `y − negY(x, y) = 2y + a₁x + a₃ = Ψ₂ = ψ₂`. The
lemma states this at `(smulX 1, smulY 1) = (X, Y)` (the generic point), giving
`smulY 1 − negY(smulX 1, smulY 1) = ψᵤ 2`.

It is the **`n = 1` instance** of the general relation `y([n]P) − negY(...) =
ψ₂ₙ/ψₙ⁴` (its sibling lemma `smulY_sub_negY`, see below): putting `n = 1` gives
`ψ₂·₁ / (ψ₁)⁴ = ψ₂ / 1⁴ = ψ₂`, since `ψ₁ = 1`.

Here:
- `smulY n := polyToField (curve.ω n) / (ψᵤ n)^3` — the project's universal-field
  y-coordinate of `n • (X, Y)` (the sibling `def`, assessed separately);
- `smulX n := polyToField (curve.φ n) / (ψᵤ n)^2` — likewise the x-coordinate;
- `smulY 1 = Y`, `smulX 1 = X` — the generic point's own coordinates;
- `ψᵤ n := polyToField (curve.ψ n)` — the n-th division polynomial in the
  universal function field `Universal.Field = Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`;
- `pointedCurve := curve.baseChange Universal.Field`, `negY` is mathlib's
  `WeierstrassCurve.Affine.negY` (`Affine/Formula.lean`).

Variables / typeclasses: **none of its own** — everything (`smulX`, `smulY`,
`ψᵤ`, `pointedCurve`, `Universal.Field`, `curve`) is fixed by the ambient
`Universal` namespace. The scalar is the literal `1 : ℤ`.

Hypotheses: **none.** (The general parent `smulY_sub_negY` carries `n ≠ 0`; at
`n = 1` that side condition is discharged internally by `one_ne_zero`.)

Conclusion: an equation of elements of `Universal.Field`.

Proof: **one line** — `rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one,
map_one, one_pow, div_one]`. It is *literally* `smulY_sub_negY` evaluated at
`n = 1`, then the closed-form simplifications `2 * 1 = 2` (`mul_one`),
`ψ 1 = 1` (`ψ_one`/`map_one`), `1^4 = 1` (`one_pow`), `_/1 = _` (`div_one`). No
new mathematical content beyond the substitution.

---

### Size classification (Phase 2a)

Verdict: **SMALL** lemma — but a member of a **BIG** development (the
universal-curve / `zsmul_eq_smulEval` track). Per protocol the literature width
is taken **EXHAUSTIVE** anyway (done below), because the surrounding development
is a named main result resting on a structure mathlib lacks (the `ω` polynomials
+ the universal function field).

### One-line check (Phase 2b)

Body line count: **1** (the single `rw [...]`).
One-liner verdict: **ONE-LINER** (kind is `lemma`). A one-line `lemma` is a
candidate for *inlining* unless it is a genuinely reusable API fact. Assessment
of its API status: it is a **fixed-numeral specialization** of a sibling general
lemma (`smulY_sub_negY`) — exactly the case the protocol treats as "prefer the
general lemma; the concrete instance is derivable on demand". It does have two
internal consumers (`smulY_one_ne_negY`, `slopeOne_eq_neg_div`) that want the
`n = 1` value in this exact closed form `ψ₂` — see Call sites. See Composition
(Phase 6).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic curve y-coordinate P minus negation 2y+a₁x+a₃ division polynomial ψ₂ₙ/ψₙ⁴" | yes | `y(nP) − negY = ψ₂ₙ/ψₙ⁴`; `Ψ₂ = 2y + a₁x + a₃`; `y(nP) = ωₙ/ψₙ³` | arXiv 2512.09601, 1103.4560, 1108.3051; **Wikipedia "Division polynomials"** gives `ψ₂ = 2y` (short Weierstrass) and the `ω/ψ³` y-coordinate — textbook |
| 2 | WebSearch (general/idiom) | "division polynomial ω ψ y-coordinate nP tangent doubling y − (−y)" | yes | `[n]P = (φ/ψ², ω/ψ³)`; `ωₙ = (ψₙ₋₁²ψₙ₊₂ − ψₙ₋₂ψₙ₊₁²)/(4y)` | **MIT 18.783 Lecture 5** (Sutherland) + Wikipedia — the y-coordinate via `ω/ψ³` and the negation `y ↦ −y − a₁x − a₃` are completely standard |
| 3 | WebSearch (general / mathlib) | "mathlib WeierstrassCurve division polynomial ωₙ omega y-coordinate nP universal ring" | partial | mathlib has `ψ, ψ₂, Ψ₃, preΨ, ΨSq, Ψ₂Sq, φ` **only**; `ωₙ` is an explicit **TODO** | mathlib `DivisionPolynomial/Basic.lean` docstring lines 71, 83: "TODO: the bivariate polynomials `ωₙ`" — so the y-coordinate identity is literally unstatable upstream |
| 4 | ChatGPT MCP | (down per task — substituted by WebSearch ×3 + arXiv + mathlib src/doc grep) | n/a | — | task notes MCP may be down; fallbacks used |
| 5 | Local references | `.mathlib-quality/references/` for NagellLutz | n/a | (dir absent; only `overview/` present) | recorded n/a |
| 6 | nLab / Stacks | "division polynomial", "elliptic curve multiplication", "2-torsion polynomial" | no | abstract EC theory only; no explicit `ω`/`y(nP)` coordinate page | explicit-formula material is out of scope there |
| 7 | recent arXiv (≤5y) | EDS / division-polynomial recurrences, valuations of `ψ` | yes (2102.07573, 2512.09601, 1108.3051) | same `[n]P = (φ/ψ², ω/ψ³)`; `n = 1` is the trivial base | confirms standard form; `n = 1` never named |

### Literature summary (Phase 3)

Concept identified as: **the y-component of the negation/doubling relation at
the generic point** — `Y − negY(X, Y) = 2Y + a₁X + a₃ = Ψ₂ = ψ₂` — i.e. the
`n = 1` instance of `y([n]P) − negY(...) = ψ₂ₙ/ψₙ⁴`. The underlying ingredients
(`negY x y = −y − a₁x − a₃`; `y([n]P) = ωₙ/ψₙ³`; `Ψ₂ = 2y + a₁x + a₃ = ψ₂`) are
all textbook.

Sources agree on the standard form: **yes**, verbatim and elementary. The
identity `2y + a₁x + a₃ = ψ₂` (the 2-torsion / doubling polynomial) is the very
first division polynomial; the y-coordinate of `nP` via `ω/ψ³` is standard. No
source treats the `n = 1` case `Y − (−Y) = ψ₂` as a named standalone result — it
is a one-substitution corollary (indeed a *definitional* boundary case) of the
general formula. The universal-curve-over-ℤ device (prove the identity once for
the generic point, specialize by a ring hom) is standard folklore and is cited
as motivation in mathlib's own `DivisionPolynomial/Basic.lean` docstring.

Most general standard form: the **general** lemma is `smulY_sub_negY`
(`y([n]P) − negY = ψ₂ₙ/ψₙ⁴` for `n ≠ 0`); `smulY_one_sub_negY` is strictly its
`n = 1` shadow.

Disagreement with the literature: none.

---

### Generality analysis — `smulY_one_sub_negY`

Literature-standard form: the **general** `smulY_sub_negY` (any `n ≠ 0`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/more-general form exists? | Reason |
|---|------------------------|-------------------|--------------------------|----------------------------------|--------|
| 1 | scalar index | the literal `1 : ℤ` | arbitrary `n ≠ 0` | **YES — `smulY_sub_negY`** | the lemma is a *fixed-numeral* specialization; the general `n` version already exists **6 lines above** it (`smulY_sub_negY`, line 227). |
| 2 | base ring (implicit) | universal ring `ℤ[A₁..A₆,X,Y]/⟨W⟩` (`Universal.Field`) | same (maximal base) | NO | universal ring is already the initial object; nothing more general. |

### Generality verdict (Phase 4b)

The current form is: **a specialization of an already-present more general lemma**
(`smulY_sub_negY`). Number of generalization opportunities: 1 (the obvious one —
and it is *already realized* by the sibling `smulY_sub_negY`). This is the
decisive structural fact: `smulY_one_sub_negY` adds no generality and no content
over `smulY_sub_negY`; it is a convenience instance at `n = 1` whose RHS
collapses to the clean `ψ₂` form.

### Modern-idiom check (Phase 4c)

No idiom move applies — it is a concrete equation, not a "let X be a foo" /
sequence-vs-filter / bundling situation. The only relevant observation is the
generality one above (it is the `n = 1` case of `smulY_sub_negY`).

---

### Diamond / defeq risk (Phase 4.5)

N/A in substance — it is a `lemma` (a Prop), not a `def`/instance. No typeclass
diamond, no reducibility leak, no coercion or universe concern. Risk: **NONE**.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulY_one_sub_negY`

[A] Lean-Finder       (index unavailable locally; substituted by grep over vendored mathlib + doc reasoning) — n/a
[B] Loogle            pattern `smulY _ - negY _ _ = ψᵤ _` over a universal EC field — the *types* (`smulY`, `smulX`, `ψᵤ`, `Universal.Field`) do not exist in mathlib → no hits possible
[C] LeanSearch        "y-coordinate of P minus its negation equals 2-torsion division polynomial" — mathlib has `negY`, `ψ₂`, but NOT `ω`/the point-coordinate identity → no hit on the statement
[D] Grep mathlib src  `grep -rln "smulY|smulX|Universal.Field|def ψᵤ|smulEval" .lake/packages/mathlib/Mathlib/` → **no hits.** Only `Basic.lean` + `Degree.lean` exist in the `DivisionPolynomial/` dir.
[E] Grep mathlib src (positive) `DivisionPolynomial/Basic.lean` defines `ψ₂ (113), Ψ₂Sq (117), Ψ₃ (142), preΨ₄ (147), preΨ' (153), preΨ (194), ΨSq (242)`; the docstring (lines 71, 83) lists **`ωₙ` as an open TODO** — so the y-coordinate of `nP` (and hence this `n=1` identity) **cannot even be stated** in mathlib yet. `negY` *is* mathlib's (`Affine/Formula.lean`), but the universal-field point coordinates `smulX/smulY` are not.

Searched for:
  - current form (`smulY_one_sub_negY`) — **absent** (its very vocabulary, incl. `ω`/`smulY`, is absent).
  - the general parent `smulY_sub_negY` — **also absent** from mathlib.
  - the literature-standard `y(nP) − negY = ψ₂ₙ/ψₙ⁴` (or the `n=1` case `Y − (−Y) = ψ₂`) — **absent**
    (mathlib has `negY` and `ψ₂` but neither `ω` nor any point-coordinate identity).

Concluded: **not in mathlib** — neither `smulY_one_sub_negY`, nor its parent
`smulY_sub_negY`, nor any nP y-coordinate / negation formula, nor the
universal-field layer (`smulX`/`smulY`) they require. (`ω` itself is a standing
mathlib TODO.)

---

### Call sites — `smulY_one_sub_negY`

Internal use (NagellLutz, excluding the declaring `ZSMul.lean`): used **only
inside `ZSMul.lean`**. Direct consumers (from the inventory):
- `smulY_one_ne_negY` (line 237) — rewrites `← sub_ne_zero` then this lemma to
  reduce `smulY 1 ≠ negY(...)` to `ψᵤ 2 ≠ 0` (the generic point is not
  2-torsion);
- `slopeOne_eq_neg_div` (line 246) — the tangent-slope computation at `(X, Y)`;
  uses `Affine.slope_of_Y_ne` then this lemma to turn the `Y − negY` denominator
  into `ψᵤ 2`.

Both are *internal computational steps* in setting up the doubling formula at the
generic point (the `2 • P` derivation via the tangent line). No other NagellLutz
file imports it.

External-to-file: the **HasseWeil project carries a verbatim duplicate** —
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:304–306`
(identical statement, identical `rw [...]` proof), with the same two downstream
uses (`smulY_one_ne_negY` at 308, `slopeOne_eq_neg_div` at 317). This is
fork/duplicate code, not independent reuse.

Composability signal: 2 internal uses, both as a local convenience for the
tangent-slope / 2-torsion-nonvanishing step at `n = 1`; the duplicate is a copy,
not a second independent client. This is "helper for the generic-point doubling
setup", not a broadly-reused API fact. (It is *slightly* stickier than
`smulX_two`: its two consumers genuinely want the simplified `ψ₂` RHS rather than
the general `ψ₂ₙ/ψₙ⁴`, so it earns its keep **as a local abbreviation** — but
that is a within-project convenience judgment, not a mathlib-API one.)

---

### Composition check (Phase 6)

Can `smulY_one_sub_negY` be derived in ≤3 chained calls?

- **From mathlib directly: NO** — the statement cannot even be *written* in
  mathlib: `smulY`, `smulX`, `ψᵤ`, and `Universal.Field` do not exist upstream,
  and `ω` (which `smulY` is built on) is an open mathlib TODO (Phase 5). So in the
  literal "compose from current mathlib" sense it is **NOT-COMPOSABLE**, exactly
  like its parent `def smulY` — because it presupposes the missing
  universal-curve layer (and the missing `ω`).

- **From the project's own already-present general lemma: YES, trivially** — it is
  **1 call**: `smulY_sub_negY one_ne_zero` followed by closed-form normalization
  of the RHS (`2*1 = 2`, `ψ 1 = 1`, `1^4 = 1`, `_/1 = _`). That is literally its
  proof. The general lemma `smulY_sub_negY` (which *is* the reusable,
  literature-standard object) makes `smulY_one_sub_negY` a zero-content numeral
  specialization.

This split is the crux of the verdict. The question "does mathlib want
`smulY_one_sub_negY`?" is **not** the same as "does mathlib want the
universal-curve n•P y-coordinate / negation formula?" (that is the parent
`smulY`/`smulY_sub_negY`/`zsmul_eq_smulEval` question, whose packaging judgment is
owned by the `smulY.md` / `smulX.md` development-level reports). Conditional on
that whole development being upstreamed, the reusable export is `smulY_sub_negY`
(the general `n` lemma); the concrete `n = 1` value `ψ₂` is then a one-step
corollary that a mathlib reviewer would inline at its two use-sites rather than
ship as a named lemma. A fixed-numeral specialization of an in-library general
lemma is the textbook **NO-composable-from-mathlib** shape (here: composable from
the project's own `smulY_sub_negY` in 1 step).

Conclusion: **COMPOSABLE from the general lemma in 1 step** ⇒ not a standalone
mathlib unit.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulY_one_sub_negY`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Statement (Phase 1): `smulY 1 − negY(smulX 1, smulY 1) = ψᵤ 2` — i.e.
  `Y − (−Y − a₁X − a₃) = 2Y + a₁X + a₃ = ψ₂` at the generic point; the **`n = 1`
  case** of `smulY_sub_negY` (`y(nP) − negY = ψ₂ₙ/ψₙ⁴`). Proof is one `rw [...]`:
  pure substitution + closed-form normalization, no new content.
- Literature (Phase 3): `Ψ₂ = 2y + a₁x + a₃` (the 2-torsion / doubling
  polynomial) and `y(nP) = ωₙ/ψₙ³` are textbook (Wikipedia "Division
  polynomials", MIT 18.783 Lecture 5, arXiv 1103.4560 / 2512.09601); the `n = 1`
  case `Y − (−Y) = ψ₂` is never a named standalone result.
- Generality (Phase 4): the more-general form (`smulY_sub_negY`, arbitrary
  `n ≠ 0`) **already exists 6 lines above** in the same file. `smulY_one_sub_negY`
  adds zero generality.
- Mathlib search (Phase 5): not in mathlib — and neither is its parent
  `smulY_sub_negY` nor any nP y-coordinate / negation formula; mathlib's
  `DivisionPolynomial/Basic.lean` has only `ψ, ψ₂, Ψ₃, preΨ, ΨSq, Ψ₂Sq, φ` and
  lists **`ωₙ` as an open TODO**, so the identity is not even statable upstream.
- Composition (Phase 6): derivable from the project's own general lemma
  `smulY_sub_negY` in **1 call** (its actual proof). It is a fixed-`n = 1`
  specialization, the canonical NO-composable shape.

**Rationale:**

`smulY_one_sub_negY` is a convenience instance, not an independent theorem. The
mathlib-worthy mathematical object here is the **general** formula
`y([n]P) − negY(...) = ψ₂ₙ/ψₙ⁴` (the lemma `smulY_sub_negY`) together with the
universal-curve machinery and the still-missing `ωₙ` — whose upstreaming decision
is handled at the development level (`smulY.md` / `smulX.md`,
BORDERLINE-needs-human, with `smulX`/`smulY`/`smulX_eq`/`smulY_sub_negY`/
`zsmul_eq_smulEval` as the real units). Once that development is upstreamed, the
`n = 1` value `ψ₂` is obtained from the general lemma by one rewrite; mathlib
would not carry a separate named `Y − (−Y) = ψ₂` lemma for two internal
group-law steps (it would inline it, exactly as the proof does). So
`smulY_one_sub_negY` does **not** warrant its own mathlib entry.

Why not the other buckets:
- **NO-mathlib-has-it** — rejected: mathlib has neither `smulY_one_sub_negY`
  *nor* its parent `smulY_sub_negY` nor any nP y-coordinate / negation formula;
  indeed `ω` itself is a mathlib TODO, so the identity cannot even be stated
  upstream (Phase 5).
- **BORDERLINE-needs-human** — rejected for *this* decl: unlike the sibling
  `def smulY`, there is **no packaging judgment** to defer. A fixed-numeral
  specialization of an already-present general lemma is never itself the
  upstreaming unit; the human-judgment call lives entirely with the parent
  `smulY`/`smulY_sub_negY` development (captured in `smulY.md` / `smulX.md`).
  Recording this one as BORDERLINE would just re-raise that same question
  redundantly.
- **YES-add-as-is / YES-but-generalise-first** — rejected: the general form
  already exists (`smulY_sub_negY`); adding the `n = 1` shadow as a mathlib lemma
  would be redundant API. (It is fine to keep it **inside the project** as a local
  abbreviation for its two consumers — that is a project convenience, not a
  mathlib contribution.)

**Cross-references / follow-ups (inherited, not new):**
- The *development-level* upstreaming question (should the whole `Universal`
  curve + `ω`/`smulY`/`smulY_sub_negY` + `zsmul_eq_smulEval` go to mathlib, and is
  the original author already preparing a PR?) is owned by `smulY.md` /
  `smulX.md`. `smulY_one_sub_negY` rides along with that decision; it should
  **not** be a separate PR target. (Note: mathlib closing its `ωₙ` TODO is a
  prerequisite for any of this.)
- The **NagellLutz ↔ HasseWeil verbatim duplication** (this lemma is copied at
  `HasseWeil/.../DivisionPolynomial.lean:304–306`, with its two consumers also
  duplicated) is an AINTLIB dedup/consolidation concern that holds regardless of
  the mathlib decision — file/track it as a `Common/` dedup ticket (same
  follow-up already noted in `smulX.md`).

**Next action:** none specific to `smulY_one_sub_negY`. If the universal-curve
development is upstreamed (per `smulY.md` / `smulX.md`), keep `smulY_sub_negY` as
the exported general lemma and let `Y − (−Y) = ψ₂` be a one-rewrite/inline
corollary; independently, consolidate the NagellLutz ↔ HasseWeil duplicate into
AINTLIB `Common/`.

---

Sources:
- [Division polynomials — Wikipedia](https://en.wikipedia.org/wiki/Division_polynomials)
- [MIT 18.783 Elliptic Curves, Lecture 5 (Sutherland, 2021)](https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/59e0623c0d3454b39d8e07b493a0e9b0_MIT18_783S21_Slides5.pdf)
- [arXiv:1103.4560 — Topics in Elliptic Curves over Finite Fields: The Groups of Points](https://arxiv.org/pdf/1103.4560)
- [arXiv:2512.09601 — Explicit valuation of elliptic nets for elliptic curves with CM](https://arxiv.org/html/2512.09601)
- [arXiv:1108.3051 — Integral points on elliptic curves and explicit valuations of division polynomials](https://arxiv.org/pdf/1108.3051)
- [arXiv:2102.07573 — A recurrence relation for elliptic divisibility sequences](https://arxiv.org/pdf/2102.07573)
- mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (vendored: `ψ₂, Ψ₂Sq, Ψ₃, preΨ, ΨSq, φ`; `ωₙ` is a TODO at lines 71, 83)
- mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` (`WeierstrassCurve.Affine.negY`)
