# /mathlibable report — `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`

Assessment date: 2026-06-22
Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS)
Source: `projects/NagellLutz/LutzNagell/ZSMul.lean:244`

> **Headline verdict: `NO-mathlib-has-it`.** Mathlib already has the general
> tangent-slope-as-`-Fₓ/F_y` identity
> (`WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval`). `slopeOne_eq_neg_div`
> is that identity specialised to the universal pointed curve at the generic
> point `(X, Y)` and transported through the `polyToField` ring hom — and the
> project even re-derives it by hand (`slope_of_Y_ne` + `field_simp`) instead
> of invoking the mathlib lemma it duplicates. The same lemma is duplicated
> verbatim in HasseWeil. This is a forked-mathlib redundancy.

---

### Baseline (Phase 0)

- lake build:               (not run — local build stale per task; reasoning from source, as instructed)
- decl `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:244`
- namespace stack:          `WeierstrassCurve` (76) → `Universal` (86) → `Affine` (157) ⇒ qualified name **`WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`** ✓ (matches the parsed name)
- kind:                     `lemma` (theorem-like; Phase 4.5 diamond check N/A)
- has sorry:                no
- module docstring summary: integer multiples `n • P` of a rational point on a Weierstrass curve expressed via division polynomials (`zsmul_eq_smulEval`); `slopeOne` is the tangent slope at the generic point, a base case of the affine multiplication-by-`n` induction.

---

### Statement (Phase 1)

```lean
def slopeOne : Universal.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  have hψ₂ : ψᵤ 2 ≠ 0 := ψᵤ_ne_zero two_ne_zero
  rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY,
    Affine.polynomialX]
  simp only [smulX_one, smulY_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄,
    map_sub, map_mul, map_pow, map_ofNat, map_add]
  rw [eq_comm, ← sub_eq_zero]; field_simp; norm_num
```

`slopeOne_eq_neg_div` states the **slope of the tangent line to the universal
Weierstrass curve at its generic point `(X, Y)`** equals `-Fₓ(X,Y) / ψ₂(X,Y)`,
where `F` is the Weierstrass polynomial, `Fₓ = polynomialX` its `X`-partial
derivative, and `ψ₂ = polynomialY` (the `Y`-partial derivative, a.k.a. the
2-division polynomial `2y + a₁x + a₃`). All quantities live in the universal
field via `polyToField : Poly →+* Universal.Field`.

This is the classical elliptic-curve **duplication/tangent-slope formula**
`m = -∂F/∂x ⁄ ∂F/∂y`, in the special "doubling a point with itself" branch
(`x₁ = x₂`, `y₁ ≠ negY`), instantiated at the *universal* point so that it can
be specialised back to any concrete curve later by functoriality.

Variables / typeclasses (Lean side):
- `Universal.Field` — fraction field of the universal coordinate ring `ℤ[a₁,a₂,a₃,a₄,a₆,X,Y]/⟨F⟩`; carries `Field` + `DecidableEq` (the latter via a local `Classical.propDecidable`).
- `pointedCurve : WeierstrassCurve Universal.Field` := `curve.baseChange Universal.Field`.
- `polyToField : Poly →+* Universal.Field`, `curve : WeierstrassCurve Poly` (the universal curve), generic point `(polyToField (C X), polyToField Y)`.

Hypotheses (Lean side): none — it is an unconditional equation in the universal field (non-vanishing of `ψᵤ 2` is discharged internally via `ψᵤ_ne_zero two_ne_zero`).

Conclusion (math): tangent slope at the generic point `= -Fₓ(X,Y)/ψ₂(X,Y)`.
Conclusion (Lean): `slopeOne = -polyToField curve.polynomialX / ψᵤ 2`.

---

### Size classification (Phase 2a)

Verdict: **SMALL.**
Reason: a helper/base-case lemma — a closed form for one specific slope at the
universal point, used to anchor the `n = 1 → n = 2` step of the affine
multiplication-by-`n` induction. Not a named theorem, not a new structure, not a
`## Main results` entry.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def` — one-line-def check **N/A**. (One-line note: the
companion `def slopeOne` is a one-liner, but the *target* of this assessment is
the lemma; `slopeOne` itself is a thin alias for a mathlib `slope` application
and is not separately in scope here.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic curve tangent slope Weierstrass 3x²+2a₂x+a₄−a₁y over 2y+a₁x+a₃ division polynomial ψ₂" | yes | `ψ₂ = 2y+a₁x+a₃`; tangent slope from implicit differentiation of the general Weierstrass equation | MIT 18.783 (Sutherland) Lec #6/#2; Wikipedia "Elliptic curve"; arXiv math/0404412 (p-adic division polys) |
| 2 | WebSearch (general form) | "elliptic curve duplication ψ₂ tangent slope partial derivative Silverman Weierstrass implicit differentiation" | yes | `m = (∂F/∂x)/(∂F/∂y)(P) = (3x²+ax+b)/(2y)` (short Weierstrass); general form `−Fₓ/F_y` | Akhtar notes; Dummit "Elliptic Curves" §7; Stanford pbc notes — uniformly the `−Fₓ/F_y` tangent formula |
| 3 | WebSearch (named-after / aliases) | (covered by #1/#2) "duplication formula", "doubling", "2-division polynomial" | yes | same formula; `ψ₂` universally the denominator of the doubling slope | name "duplication/doubling formula"; `ψ₂` standard notation (Silverman AEC III.3) |
| 4 | ChatGPT MCP | self-contained query: "is slopeOne_eq_neg_div the specialization of mathlib's slope_of_Y_ne_eq_evalEval at the generic point, transported by a ring hom?" | n/a | — | **MCP down** in this environment (Codex exec failed, as the task warned). Fell back to direct mathlib-source reading, which is dispositive. |
| 5 | Local references | `.mathlib-quality/references/` grep for "slope"/"tangent"/"division polynomial" | n/a | — | references dir absent for this project; recorded n/a. (Refs are LOCAL-ONLY per CLAUDE.md and not present in this checkout.) |
| 6 | nLab | "elliptic curve", "Weierstrass" tangent/group law | n/a (low value) | — | nLab treats the group law abstractly (Picard/divisor-class); no elementary `−Fₓ/F_y` affine slope formula. Not the right altitude. |
| 7 | nCatLab | (categorical) | n/a | — | not a categorical concept — an affine coordinate computation. |
| 8 | Stacks Project | elliptic curve group law / Weierstrass | n/a | — | Stacks develops the group law scheme-theoretically (Pic⁰), not via explicit affine tangent slopes. No matching elementary lemma. |
| 9 | MathOverflow / MSE | "tangent line slope elliptic curve general Weierstrass form" | yes (background) | `−Fₓ/F_y` everywhere | standard exam/textbook fact; no novelty. |
| 10 | recent arXiv (≤5 yr) | "division polynomials elliptic curves" ψ₂ / EDS | yes (background) | `ψ₂ = 2y+a₁x+a₃` reaffirmed (e.g. arXiv 1303.4327 homogeneous division polys) | the slope formula is classical; arXiv work assumes it. |

### Literature summary (Phase 3)

Concept identified as: the **tangent-line slope at a point of a Weierstrass
curve** (the "doubling"/"duplication" branch of the secant–tangent group law),
`m = -∂F/∂x ⁄ ∂F/∂y`, with `∂F/∂y = ψ₂ = 2y + a₁x + a₃` the 2-division polynomial.
Sources agree on the standard form: **yes** — universally `−Fₓ/F_y` (equivalently
`(3x²+2a₂x+a₄−a₁y)/(2y+a₁x+a₃)`); see Silverman AEC III.2–3, Sutherland 18.783.
Most general standard form: tangent slope of a Weierstrass curve over **any
field** (indeed any commutative ring where `ψ₂` is a unit) at a point with
`ψ₂ ≠ 0` — exactly mathlib's hypothesis set.
Generality dimensions where the literature varies: only **base ring** (short
Weierstrass over a field vs. general Weierstrass over a ring). The project's
"universal field" instance is the *most general possible base* (a free/universal
object), so the project lemma is a single closed instantiation of the standard
formula, not a generalisation of it.
Disagreement with the literature: none.

---

### Generality analysis — `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`

Literature-standard form (Phase 3): `W.slope x x y y = -W.polynomialX.evalEval x y / W.polynomialY.evalEval x y` for a Weierstrass curve `W` over a field, at a point with `y ≠ W.negY x y`. **This is verbatim mathlib's `slope_of_Y_ne_eq_evalEval`.**

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | the curve `W` | the *fixed* `pointedCurve` over `Universal.Field` | arbitrary `W : WeierstrassCurve F`, `[Field F]` | **YES — drastically** | the project hard-codes the universal curve; the standard statement is for any `W`. The universal form is a *specialisation*, not a generalisation. |
| 2 | the point | the *fixed* generic point `(X, Y)` | arbitrary `(x₁,x₂,y₁,y₂)` with `x₁=x₂`, `y₁≠negY` | **YES** | mathlib's lemma is at an arbitrary point; this is the single generic-point instance. |
| 3 | RHS coordinates | pushed through `polyToField` (`polyToField curve.polynomialX`, `ψᵤ 2`) | `polynomialX.evalEval`, `polynomialY.evalEval` directly | n/a (transport artefact) | the `polyToField(...)` wrappers are exactly `evalEval`-at-the-generic-point images; not a genuine generality axis, just the universal-object packaging. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is a single
instantiation (one fixed curve, one fixed point) of mathlib's already-general
`slope_of_Y_ne_eq_evalEval`. There is **no weakening to propose** because the
*more general statement already exists in mathlib*; the right move is not to
generalise this lemma but to **delete it and use the mathlib lemma**.
Number of weakening opportunities: n/a (the general form is upstream already).
Cost of "restatement": n/a — see Phase 5.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | bundled-hyp → typeclass? | no | — | `slope` already an `F`-valued def over `[Field F] [DecidableEq F]`; nothing to typeclass-ify. |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic identity; no limits. |
| 3 | construct → universal property? | no | — | the *universal curve itself* is already the universal-property device; the lemma is just its slope value. |
| 4 | set+closure → bundled substructure? | no | — | n/a. |
| 5 | field/metric-specific → weaken typeclass (module/ring)? | partially (background) | mathlib's `slope` is field-only by nature (it divides); the *partials* `polynomialX/Y` are defined over any `CommRing`, and the universal-vs-specialise pattern is precisely how the project later transports to any field, incl. char 2 | this is already how mathlib + the project are organised; nothing to add. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index → general additive structure? | no | — | the "1" in `slopeOne` is the doubling base case; the general `n` machinery is the surrounding file, not this lemma. |

Modern idiom available: **no.** One-line reason: mathlib's formulation
(`slope_of_Y_ne_eq_evalEval` over `[Field F] [DecidableEq F]`, transported via the
existing `map_slope`/`baseChange_slope`) is already the contemporary idiom; this
lemma is a hand-rolled instance of it.

### Diamond / defeq risk (Phase 4.5)

N/A — declaration kind is `lemma` (no new definitional equalities or
typeclass-search paths introduced). The companion `def slopeOne` is a thin alias
`pointedCurve.toAffine.slope … ` and is not the assessment target.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`

[A] Lean-Finder       — n/a: MCP mathlib-index tools (loogle/leansearch/lean-finder) not available in this environment (ToolSearch: "No matching deferred tools found").
[B] Loogle            — n/a: same (no index MCP). Substituted with authoritative direct source grep over `.lake/packages/mathlib/`.
[C] LeanSearch        — n/a: same.
[D] Grep mathlib src  — `grep -rn "slope" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/` → **HIT**.
[E] Name pattern      — grep for `slope_of_Y_ne`, `polynomialX`, `polynomialY`, `map_slope`, `baseChange_slope` → multiple HITs (see below).

Direct-source findings (the decisive evidence):

- **`WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval`** — `Affine/Formula.lean:194–199`:
  ```lean
  lemma slope_of_Y_ne_eq_evalEval (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
      W.slope x₁ x₂ y₁ y₂ = -W.polynomialX.evalEval x₁ y₁ / W.polynomialY.evalEval x₁ y₁
  ```
  ⇒ **the general form of `slopeOne_eq_neg_div`, verbatim.**
- `WeierstrassCurve.Affine.slope` def + `slope_of_Y_ne` — `Affine/Formula.lean:168–187` (the very lemma the project's proof rewrites with).
- `WeierstrassCurve.Affine.evalEval_polynomialX` (`a₁y −(3x²+2a₂x+a₄)`) and `evalEval_polynomialY` (`2y+a₁x+a₃`) — `Affine/Basic.lean:179,195`. The project's `ψ₂` is *defined as* `W.toAffine.polynomialY` (`DivisionPolynomial.lean:36–37`), so `ψᵤ 2 = polyToField(curve.ψ₂)` is exactly `polynomialY.evalEval` at the generic point.
- `WeierstrassCurve.Affine.map_slope` / `baseChange_slope` — `Affine/Formula.lean:424,459` — the functoriality lemmas that transport `slope` of `curve` to `slope` of `pointedCurve = curve.baseChange Universal.Field`.

Searched for both: (i) the user's universal form, (ii) the general
`slope = -polynomialX/polynomialY` form. The general form **is in mathlib**.

Concluded: **found in mathlib as `WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval`; more general form** (the project lemma is its instantiation at the universal curve's generic point, pushed through `polyToField`).

---

### Call sites — `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`

Internal use count (NagellLutz, excluding the declaring file): **0** distinct other files.
Within the declaring file `ZSMul.lean`: **2** uses — line 265 (`addX_smul_one_smul_one`) and line 281 (`addY_smul_one_smul_one`).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `ZSMul.lean:265` | `rw [Affine.addX, slopeOne_eq_neg_div, smulX_two, smulX_one]` — feeds the closed form of `slopeOne` into the doubling-`X` base case |
| `ZSMul.lean:281` | `rw [… slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, …]` — same for the doubling-`Y` base case |

Inline-derivation grep (re-derived elsewhere?):
- **YES — duplicated verbatim in HasseWeil**: `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:315` has an identical `slopeOne_eq_neg_div` (same statement, same proof). HasseWeil also has a *separate* generic-point variant in `EC/GenericPointZsmul.lean:319–329` (`slopeOne` + `slopeOne_eq` giving `(3x²+2a₂x+a₄−a₁y)/ψ_ff 2`) — the same formula yet again, in a different universal-field packaging.
- Both projects also already import and use mathlib's `Affine.evalEval_polynomialX`/`evalEval_polynomialY` directly elsewhere (e.g. `SingularPoint.lean:74–75,158`, `MulByIntUnramified.lean:989`, `PIDMain.lean:276`), confirming the bridge lemmas are present and idiomatic in-repo.

Composability signal: K=2 uses but **only inside the declaring file**, and the
statement is re-derived in ≥1 other project (HasseWeil). Per the call-sites
table, "K=0 external + re-derived inline elsewhere" ⇒ leans NO; here the deeper
fact is that the *general* statement is already upstream, so the precise bucket
is NO-mathlib-has-it.

---

### Composition check (Phase 6)

Can `slopeOne_eq_neg_div` be obtained from mathlib?

Attempt 1 — direct specialisation of the mathlib lemma:
```lean
-- pointedCurve.slope X X Y Y = -pointedCurve.polynomialX.evalEval X Y / pointedCurve.polynomialY.evalEval X Y
have := pointedCurve.toAffine.slope_of_Y_ne_eq_evalEval (x₁ := smulX 1) … rfl smulY_one_ne_negY
```
- Mathlib decls used: `slope_of_Y_ne_eq_evalEval`.
- Result: gives the RHS in terms of `pointedCurve.polynomialX/Y.evalEval (image X) (image Y)`.
- Remaining: rewrite numerator `pointedCurve.polynomialX.evalEval (img X)(img Y) = polyToField curve.polynomialX` and denominator `pointedCurve.polynomialY.evalEval (img X)(img Y) = ψᵤ 2`. **Both are the `evalEval-at-generic-point ∘ map = polyToField` identity** — which the project *already proves* for the polynomial itself in `equation_point` (`Universal.lean:141–147`: `evalEval (polyToField (C X)) (polyToField Y) (p.map (mapRingHom (algebraMap …))) = polyToField p`). For the denominator, additionally `curve.ψ₂ = curve.toAffine.polynomialY` by definition and `ψ_two`/`ψ₂` give `ψᵤ 2 = polyToField curve.ψ₂`.

Conclusion: **the general statement is in mathlib (NOT-COMPOSABLE-as-≤3-trivial-calls, but NO-mathlib-has-it).** The derivation from the mathlib lemma needs the generic-point transport `evalEval∘map = polyToField` for *both* the numerator and the `polynomialY`/`ψ₂` denominator — a real (if short) bridge, slightly more than a 1-line `exact`. So the honest bucket is **NO-mathlib-has-it** (mathlib owns the general result; this is a transported specialisation), with the refactor being "specialise the mathlib lemma + add/reuse a small `evalEval-generic-point` bridge", rather than a pure ≤3-call inline.

---

## Verdict: `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature (Phase 3): the tangent slope `−Fₓ/F_y` with `F_y = ψ₂ = 2y+a₁x+a₃` is textbook-classical (Silverman AEC III.2–3; Sutherland 18.783). No novelty.
- Generality (Phase 4): **STRICTLY NARROWER THAN STANDARD** — one fixed curve, one fixed point; the general statement is upstream.
- Mathlib search (Phase 5): **found** as `WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval` (`Affine/Formula.lean:194`); strictly more general.
- Composition (Phase 6): derivable from that mathlib lemma + the project's own `equation_point` generic-point transport; not a pure ≤3-call inline, so NO-mathlib-has-it rather than NO-composable.

**Rationale.**
`slopeOne_eq_neg_div` is the classical elliptic-curve tangent-slope identity
`slope = −polynomialX / polynomialY`, specialised to the universal curve at its
generic point. Mathlib states exactly this identity in full generality as
`WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval`. The project lemma is its
image under the ring hom `polyToField` at the point `(X, Y)`: the numerator
`polyToField curve.polynomialX` is `pointedCurve.polynomialX.evalEval` at the
generic point, and the denominator `ψᵤ 2` is `pointedCurve.polynomialY.evalEval`
there (because the project *defines* `ψ₂ := toAffine.polynomialY`). Tellingly, the
proof does **not** call the mathlib lemma — it re-walks `slope_of_Y_ne`, unfolds
`Affine.polynomialX`, and closes with `field_simp; norm_num`, i.e. it re-derives
a lemma mathlib already has. The result is duplicated verbatim in HasseWeil
(`Auxiliary/DivisionPolynomial.lean:315`), and a third generic-point variant of
the same formula lives in `HasseWeil/EC/GenericPointZsmul.lean` — three hand
copies of one upstream fact. This is a forked-mathlib redundancy: the right
library state is one `slope_of_Y_ne_eq_evalEval` plus a tiny generic-point
transport, not three bespoke `slopeOne_eq_neg_div`s.

**WHY not (refactor-actionable):**
Mathlib already owns the general identity. Cite:
- Existing mathlib decl: `WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval`
- Located at: `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean:194`
- Our form follows by specialising it to `pointedCurve` at `(X,Y)` and rewriting
  numerator + denominator through the generic-point evaluation ring-hom identity
  (`Universal.lean:141–147`'s `evalEval (polyToField (C X)) (polyToField Y) (p.map …) = polyToField p`),
  using `curve.ψ₂ = curve.toAffine.polynomialY` (def) and `ψ_two`:
  ```lean
  -- sketch (universal field; DecidableEq via the file's local Classical instance)
  example : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
    rw [slopeOne, pointedCurve.toAffine.slope_of_Y_ne_eq_evalEval rfl smulY_one_ne_negY]
    -- numerator:   pointedCurve.polynomialX.evalEval (img X)(img Y) = polyToField curve.polynomialX
    -- denominator: pointedCurve.polynomialY.evalEval (img X)(img Y) = polyToField curve.ψ₂ = ψᵤ 2
    rw [evalEval_generic_point_polynomialX, evalEval_generic_point_polynomialY, … ]
  ```
  (`evalEval_generic_point_*` is the one small bridge lemma — the same transport
  `equation_point` already uses, applied to `polynomialX`/`polynomialY` instead of
  `polynomial`. It is reusable for several other universal-point lemmas in the
  file, so it is the natural shared helper.)

Refactor plan (this is a `main`-side cleanup, **CLEANER lane**, not a mathlib PR):
1. Add (or lift into `Universal.lean`) one helper:
   `pointedCurve.polynomialX.evalEval (polyToField (C X)) (polyToField Y) = polyToField curve.polynomialX`
   (and the `polynomialY`/`ψ₂` companion) — a 2–3 line consequence of the existing
   `equation_point` transport.
2. Reprove `slopeOne_eq_neg_div` as the 2-line specialisation above (statement
   unchanged — safe for the cleanup/auto-merge bar).
3. **Dedup across projects:** HasseWeil's `Auxiliary/DivisionPolynomial.lean:315`
   twin should be unified with the NagellLutz one (candidate for `Common/`), and
   `HasseWeil/EC/GenericPointZsmul.lean`'s `slopeOne_eq` reconciled to the same
   underlying mathlib lemma. File a cross-project dedup cleanup ticket.

Per CLAUDE.md this is on-`main` CLEANER work (statement-preserving golf + dedup +
best-mathlib-API), **not** a producer task and **not** a mathlib contribution —
mathlib already has the general result.

**Next action:** delete the bespoke derivation; reprove `slopeOne_eq_neg_div`
via `slope_of_Y_ne_eq_evalEval` + a small generic-point `evalEval` bridge; unify
the HasseWeil twin (and the `GenericPointZsmul` variant) against the same upstream
lemma. No mathlib PR.

---

## Next step

Reprove `slopeOne_eq_neg_div` from `WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval`
(specialise at the universal generic point via the existing `equation_point`
transport, extended to `polynomialX`/`polynomialY`); then dedup against the
identical HasseWeil `slopeOne_eq_neg_div` and the `GenericPointZsmul.slopeOne_eq`
variant. Statement-preserving cleanup on `main`; no mathlib PR (mathlib already
has the general identity).
