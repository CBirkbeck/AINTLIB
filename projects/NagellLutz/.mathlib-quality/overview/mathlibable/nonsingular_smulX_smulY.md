# /mathlibable report — `WeierstrassCurve.Universal.Affine.nonsingular_smulX_smulY`

> Step-9 single-declaration mathlibable assessment (NagellLutz / `/overview`).
> Date: 2026-06-22. Local build stale; reasoned from source + mathlib `09b373d` tree + lit search.

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale per task brief; reasoned from source + mathlib tree)
- decl `WeierstrassCurve.Universal.Affine.nonsingular_smulX_smulY`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:385`
- qualified name VERIFIED:  ✓ `namespace WeierstrassCurve` (76) → `namespace Universal` (86) → `namespace Affine` (157).
                            Full name = `WeierstrassCurve.Universal.Affine.nonsingular_smulX_smulY` (matches the parsed guess).
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Expresses `n • P` of a rational point on a Weierstrass curve via division
                             polynomials `(φₙ/ψₙ², ωₙ/ψₙ³)`; builds the *universal* curve over
                             `ℤ[A₁..A₆,X,Y]` and proves `zsmul_eq_smulEval` by even-odd / strong induction.

---

### Statement (Phase 1)

```lean
lemma nonsingular_smulX_smulY (hn : n ≠ 0) :
    Affine.Nonsingular curveField (smulX n) (smulY n) :=
  (zsmul_point_eq_smulX_smulY hn).1
```

In prose: on the **universal** Weierstrass curve — the curve `curve : Affine (MvPolynomial Coeff ℤ)`
with generic coefficients `A₁,…,A₆` and generic point `(X, Y)`, base-changed to its fraction field
`Universal.Field` (this base change is `curveField := curve.baseChange Universal.Field`,
`Universal.lean:173`) — for any nonzero integer `n`, the pair of rational functions
`(smulX n, smulY n) = (φₙ(X,Y)/ψₙ(X,Y)², ωₙ(X,Y)/ψₙ(X,Y)³)` is a **nonsingular point** of the curve,
i.e. it satisfies the Weierstrass equation and at least one partial derivative is nonzero there.

This is the "nonsingularity witness" half of the parent theorem
`zsmul_point_eq_smulX_smulY` (`ZSMul.lean:344`), which states the stronger
`∃ h : Nonsingular _ (smulX n) (smulY n), n • Affine.point = .some _ _ h`.
The lemma is **literally** its first projection, `(… ).1`.

Variables / typeclasses involved (Lean side):
- `n : ℤ` — the multiplier (section variable, `ZSMul.lean:97`).
- `curveField : WeierstrassCurve Universal.Field` — the base-changed **universal** curve
  (`Universal.Field = FractionRing Universal.Ring`, `Universal.Ring = MvPolynomial Coeff ℤ / ⟨Weierstrass poly⟩`).
- `smulX n, smulY n : Universal.Field` — `polyToField (curve.φ n) / ψᵤ n ^ 2` and `… (curve.ω n) / ψᵤ n ^ 3`
  (`ZSMul.lean:164,168`).

Hypotheses (Lean side):
- `hn : n ≠ 0` — needed because `smulX 0 = smulY 0 = 0` give the point at infinity, not an affine point.

Conclusion (math): the affine point `n • (X,Y)` on the universal curve is nonsingular.
Conclusion (Lean): `Affine.Nonsingular curveField (smulX n) (smulY n)` (a `Prop`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step helper — the first projection of an already-proved existential. Not a named theorem,
not a `## Main results` entry (the file's main result is `WeierstrassCurve.zsmul_eq_smulEval`), no new
structure introduced.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1** substantive line (`(zsmul_point_eq_smulX_smulY hn).1`).
One-liner verdict: n/a — kind is `lemma`, not `def`. The defeq/diamond/API-stability exemptions in Phase 2b
apply to **definitions**; a one-line *lemma* carries no definitional content. Recorded as a strong
NO-composable signal nonetheless: the body is a single projection of an existing project theorem.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve n-division point coordinates division polynomial φ/ψ² nonsingular / not singular"      | yes  | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; affine (nonsingular) iff `ψₙ ≠ 0` | Wikipedia *Division polynomials*; arXiv 1103.4560, 1108.3051 |
|  2 | WebSearch (general / universal form) | "universal Weierstrass curve generic point ℤ[a₁..a₆,X,Y] EDS formalization Lean mathlib"            | yes  | universal curve + universal point on smooth locus is a *known* construction | Lean Zulip `thoughts on elliptic curves`; mathlib `DivisionPolynomial.Basic`, `EllipticDivisibilitySequence` docs — but the *universal-ring* packaging is **not** in mathlib |
|  3 | WebSearch (named-after / aliases)| "multiplication-by-n map elliptic curve scalar multiple division polynomial well-defined affine point"  | yes  | same as #1; `[n]P` finite ⇔ `P ∉ E[n]` | Silverman AEC III.; standard |
|  4 | ChatGPT MCP                      | n/a — MCP down per task brief; substituted by extra WebSearch (#3) + Silverman/mathlib-docs cross-check | n/a  | (fallback used; standard form already pinned by #1–#3) | brief flagged ChatGPT MCP may be down; fallbacks used |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                 | n/a  | directory absent                 | no `references/` dir in this project |
|  6 | nLab                             | "division polynomial" / "elliptic curve multiplication by n"                                            | n/a  | nLab has no dedicated division-polynomial page; concept is classical-AG, not categorical | recorded n/a — not a categorical concept |
|  7 | nCatLab                          | —                                                                                                      | n/a  | not a categorical concept        | — |
|  8 | Stacks Project                   | "Weierzstrass equation nonsingular point" / generic point of universal curve                            | n/a  | Stacks covers Weierstrass/elliptic generalities but not the EDS division-polynomial `(φ/ψ²,ω/ψ³)` packaging | recorded n/a for this specific lemma |
|  9 | MathOverflow / Math.SE           | "n-division point of elliptic curve is a nonsingular affine point when ψₙ ≠ 0"                          | yes  | confirms #1: denominator `ψₙ` vanishes exactly at n-torsion ⇒ point at infinity; else affine & smooth | standard folklore |
| 10 | recent arXiv (≤5y)               | "elliptic divisibility sequence division polynomial valuation generic point"                            | yes  | arXiv 1909.12654, 2412.10284 — EDS/division-poly machinery; none package a *universal-ring* `Nonsingular` lemma | confirms it's standard math, not a novel statement |

### Literature summary (Phase 3)

Concept identified as: the **multiplication-by-`n` map on a Weierstrass curve via division polynomials**,
`[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`, and the classical fact that this is a **nonsingular affine point** precisely
when `ψₙ(P) ≠ 0` (equivalently `n • P ≠ O`).
Sources agree on the standard form: **yes**.
Most general standard form: for any Weierstrass curve over a field (or even an integral domain after
localising), for `P` not in the `n`-torsion, `[n]P` is the affine point `(φₙ/ψₙ², ωₙ/ψₙ³)`, which lies on
the curve and is nonsingular.
Generality dimensions where the literature varies:
  - base: from a fixed field, up to the **universal** ring `ℤ[A₁..A₆]` (Lazard-style generic curve). The
    project deliberately picks the *universal* end so the formula holds for every curve simultaneously,
    including characteristic 2.
  - the conclusion "nonsingular" is, in the literature, usually folded into "`[n]P` is a well-defined
    affine point" — it is rarely stated as a standalone lemma, because the group-law machinery carries the
    witness automatically (exactly as the parent theorem here does).
Disagreement with the literature: **none** — but the literature never isolates *this* projection as a
named result; it is a byproduct of `[n]P` being a point.

---

### Generality analysis — `nonsingular_smulX_smulY`

Literature-standard form (from Phase 3): "for a Weierstrass curve `W` over a field `F` and `P : W.Point`
with `n • P ≠ O`, the affine coordinates of `n • P` are nonsingular." The project's lemma is the
**`W = curveField`, `P = Affine.point`** (universal) instance of this.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `curveField` (the curve) | the **universal** curve over `FractionRing (MvPolynomial Coeff ℤ / ⟨W⟩)` | arbitrary Weierstrass curve over a field | (different axis) | The universal curve is the *most general* base in one sense, but the lemma is **pinned** to it — it is not a `variable (W)` result. The genuinely general statement is "any `W` over a field", which is a **different lemma** (the project derives the per-curve case downstream, in HasseWeil's `GenericPointZsmul`, by specialising). |
| 2 | `(smulX n, smulY n)` | the specific division-polynomial coordinates of the universal point | the coordinates of `n • P` for a *general* nonsingular `P` | yes | The general statement quantifies over `P`; this one hard-codes the universal point `(X,Y)`. |
| 3 | `hn : n ≠ 0` | `n ≠ 0` | `n • P ≠ O` (⇔ `ψₙ(P) ≠ 0`) | (already correct here) | On the universal point, `n ≠ 0 ⇒ ψᵤ n ≠ 0` (`ψᵤ_ne_zero`), so `n ≠ 0` is exactly the right hypothesis. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but narrow *by design*. It is the universal-point
instance, the deliberate engine of an induction, not a general-`W`/general-`P` statement. Crucially the
narrowing is the whole point: the proof *is* the hard induction `zsmul_point_eq_smulX_smulY`, and this lemma
just reads off its first component.
Number of weakening opportunities found: the only "generalisation" would be to restate it for an arbitrary
curve/point — which is **a different theorem mathlib could conceivably want**, but it is NOT this declaration,
and (see Phase 5) that general statement is not derivable from anything in mathlib today; it would have to be
proved from scratch (essentially re-deriving the group law ↔ division-polynomial bridge, i.e. the entire
NagellLutz/HasseWeil development).
Proposed restatement: not applicable — see Phase 7. This decl is not the right *unit* to upstream.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | `curveField`, `smulX`, `smulY` are already plain `def`s; no bundled-hypothesis preamble to class-ify. | — |
| 2 | sequences/metric → filters/topology? | no | purely algebraic statement over a field; no limit/topology content. | — |
| 3 | construct an object → universal-property class? | no | `Nonsingular` is already a mathlib predicate; nothing to characterise universally. | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | not a substructure statement. | — |
| 5 | vector-space/field-specific → weaken typeclasses? | no | the conclusion needs a field (denominators `ψₙ²`, `ψₙ³` inverted); already at the right typeclass. | — |
| 6 | 1-categorical → higher-categorical? | no | no categorical content. | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | `n : ℤ` indexes scalar multiplication on an abelian group; ℤ is exactly correct (it *is* the `zsmul`). | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already in the idiomatic mathlib shape
(`WeierstrassCurve.Affine.Nonsingular W x y`). One-line reason: there is no organisational redundancy to
remove — this is a thin projection lemma over existing mathlib predicates, not a re-formulatable concept.

---

### Diamond / defeq risk — `nonsingular_smulX_smulY`

n/a — declaration kind is **lemma** (a `Prop`-valued result). It introduces no definitional equalities and
no typeclass-search paths. Phase 4.5 skipped.

---

### Mathlib search-status: `nonsingular_smulX_smulY`

[A] Lean-Finder       "n-multiple of elliptic curve point is nonsingular via division polynomials"   no hits (n/a: index unreachable offline; substituted by [D]+[E] over mathlib `09b373d` tree)
[B] Loogle            `Nonsingular _ (?φ / ?ψ ^ 2) _`, `WeierstrassCurve.Universal`                  no hits — no `Universal` namespace in mathlib; no `Nonsingular`-of-division-polynomial-coords lemma
[C] LeanSearch        "the n-division point of an elliptic curve is a nonsingular affine point"        no hits (offline; covered by literature Phase 3 + grep)
[D] Grep mathlib src  `nonsingular_smulX_smulY`, `zsmul_point_eq_smulX_smulY`, `smulX`, `smulY`,
                      `namespace Universal` (in `EllipticCurve/`), `WeierstrassCurve.Universal`        **no hits** — none of these exist in `Mathlib/` (commit `09b373d`)
[E] Name pattern      `def Nonsingular`, `nonsingular_neg`, `nonsingular_add`, `Point.some`            **partial** — mathlib HAS the *building blocks*: `Affine.Nonsingular` (Affine/Basic.lean:211), `nonsingular_neg` / `nonsingular_add` (Affine/Formula.lean:139,…), and `Point.some` carries a `Nonsingular` witness (Affine/Point.lean:471). Mathlib does NOT have the n-division-point nonsingularity statement, nor the `Universal` curve.

Searched for both:
  - the user's current form (universal-curve, `smulX/smulY` coords) → **not in mathlib** (the `Universal`
    construction itself is absent; confirmed the namespace does not occur anywhere under `Mathlib/`).
  - the literature-standard form (general `W`, `P` with `n•P ≠ O`) → **not in mathlib** either. Mathlib's
    `DivisionPolynomial` files define `φ, ψ, ω` and prove EDS relations, but there is **no** theorem
    connecting `[n]P` (group-law scalar multiple) to `(φₙ/ψₙ², ωₙ/ψₙ³)`, and hence no nonsingularity
    corollary. (That bridge is exactly what NagellLutz/HasseWeil contribute.)

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard general form). Mathlib has
the building blocks (`Nonsingular`, `nonsingular_neg/add`, `Point.some`) but neither the universal-curve
statement nor the general `[n]P`-coordinate statement.**

---

### Call sites — `nonsingular_smulX_smulY`

Internal use count: **0**  (whole repo grep, excluding the declaring line `ZSMul.lean:385`).
External-to-file callers: **0** distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | — |

Inline-derivation grep: the *content* (the nonsingular witness) is obtained directly from
`zsmul_point_eq_smulX_smulY` at its only real consumers, which destructure the full existential rather than
call this projection:
  - `ZSMul.lean:390` (`zsmul_point_ne_zero`): `obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0` — uses the
    witness `ns` directly, bypassing `nonsingular_smulX_smulY`.
  - `ZSMul.lean:429` (`Jacobian.zsmul_point_eq_smulField`): `obtain ⟨ns, eq⟩ := Affine.zsmul_point_eq_smulX_smulY hn` — same.
  - HasseWeil's fork (`Auxiliary/DivisionPolynomial.lean:459,495`) likewise destructures the parent, not this lemma.

**Signal:** K = 0 internal uses, and every place that needs the witness re-derives it inline from the parent
existential. This is the canonical "wrapper that consumers bypass" pattern → strong NO-composable.

---

### Composition check (Phase 6)

Can `nonsingular_smulX_smulY` be derived in ≤3 chained calls? **Yes — trivially, in 1.**

Attempt 1: `(zsmul_point_eq_smulX_smulY hn).1`
  - Decls used: `WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY` (the project's own parent theorem).
  - Result: **succeeds** — this is verbatim the lemma's own body.
  - Notes: it is a single `.1` projection of an existential `∃ h, …` already proved in the same file.

Conclusion: **COMPOSABLE** (1 call). The composition target is a *project* theorem, not a mathlib one — but
that only strengthens the NO verdict: there is nothing here for mathlib, because the witness is a free
byproduct of the parent result, and the parent itself is not mathlib-bound either (it relies on the
project-only `Universal` construction).

---

## Verdict: `WeierstrassCurve.Universal.Affine.nonsingular_smulX_smulY`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): standard fact `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` is nonsingular when `ψₙ ≠ 0`; never
  isolated as a named lemma — it is a byproduct of `[n]P` being a point.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (universal-point instance, narrow by design);
  modern-idiom: none.
- Mathlib search (Phase 5): NOT in mathlib in either the universal or the general form; the `Universal` curve
  construction does not exist in mathlib at all. Building blocks (`Nonsingular`, `nonsingular_neg/add`,
  `Point.some`) are present.
- Composition check (Phase 6): COMPOSABLE in 1 call — `(zsmul_point_eq_smulX_smulY hn).1`.

**Rationale:**

This is a one-line projection lemma with **zero call sites**, whose body is literally `(parent hn).1`. The
mathematical content — that the affine coordinates of `n • P` form a nonsingular point — is already fully
carried by the parent theorem `zsmul_point_eq_smulX_smulY`, which packages exactly this witness inside its
existential. Every actual consumer in the repo (`zsmul_point_ne_zero`, `Jacobian.zsmul_point_eq_smulField`,
and HasseWeil's fork) destructures the parent's `∃ h, …` directly and uses the witness `h`, never routing
through this projection. So the lemma is a wrapper that even its own project bypasses.

It cannot be a YES of either flavour for two independent reasons. (1) **It is not stateable in mathlib:**
`curveField`, `smulX`, `smulY` all live on the project-only `WeierstrassCurve.Universal` construction (the
universal curve over `ℤ[A₁..A₆,X,Y]` and its fraction field), which does not exist anywhere under `Mathlib/`
— the very `Universal` namespace is absent. (2) Even the *general*-curve analogue ("for any `W` over a field
and `P` with `n•P ≠ O`, the coordinates of `n•P` are nonsingular") is **not** present in or derivable from
mathlib: mathlib's `DivisionPolynomial` files define `φ, ψ, ω` and their EDS relations but contain **no**
theorem linking the group-law scalar multiple `[n]P` to `(φₙ/ψₙ², ωₙ/ψₙ³)`. That bridge is precisely the
NagellLutz/HasseWeil contribution, and it is a large development, not a `≤3`-call composition. Therefore the
right home for this specific lemma is *inline*: at any future call site, write `(zsmul_point_eq_smulX_smulY
hn).1` instead of keeping a named wrapper.

(The interesting upstreaming question — "should mathlib gain the general `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` bridge and
its nonsingularity corollary?" — is a question about the **parent** theorem family
`zsmul_point_eq_smulX_smulY` / `zsmul_eq_smulEval`, assessed separately, not about this projection.)

**WHY not (refactor-actionable):**
Mathlib has the building blocks for *nonsingularity bookkeeping* —
`WeierstrassCurve.Affine.Nonsingular` (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:211`),
`nonsingular_neg` / `nonsingular_add` (`.../Affine/Formula.lean:139` and nearby), and the `Point.some`
constructor that *stores* a `Nonsingular` witness (`.../Affine/Point.lean:471`). But the relevant composition
for *this* lemma is not over mathlib at all — it is the single projection over the project's own parent
theorem. The lemma adds no content beyond `zsmul_point_eq_smulX_smulY`.

Mathlib building blocks (for the witness machinery, not the derivation itself):
  - `WeierstrassCurve.Affine.Nonsingular` — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:211`
  - `WeierstrassCurve.Affine.nonsingular_neg`, `…nonsingular_add` — `…/Affine/Formula.lean:139,…`
  - `WeierstrassCurve.Affine.Point.some` (carries the `Nonsingular` field) — `…/Affine/Point.lean:471`

Composition sketch (≤3 lines) — the actual derivation, over the project parent:
```lean
example (hn : n ≠ 0) : Affine.Nonsingular curveField (smulX n) (smulY n) :=
  (zsmul_point_eq_smulX_smulY hn).1
```

Call sites in our project (from Phase 6.0): **K = 0**.
Refactor plan: since there are zero call sites, **delete `nonsingular_smulX_smulY`** from `ZSMul.lean:385–386`
outright. If a future consumer needs just the nonsingularity witness (without the accompanying
`n • point = .some …` equation), inline `(zsmul_point_eq_smulX_smulY hn).1` at that site rather than
reintroducing the wrapper — matching how `zsmul_point_ne_zero` (`ZSMul.lean:389`) and
`Jacobian.zsmul_point_eq_smulField` (`ZSMul.lean:424`) already destructure the parent.
(Project-policy note: this is a producer/`dev/nagell-lutz` decision — on `main`, deleting an unused
sorry-free helper is a fair `/cleanup` dedup action; flagging here for the cleanup lane.)

Next action: delete `nonsingular_smulX_smulY` from the project; if ever needed, inline
`(zsmul_point_eq_smulX_smulY hn).1` at the call site. No mathlib PR.

---

## Next step

Delete `nonsingular_smulX_smulY` from `ZSMul.lean` (zero call sites); inline `(zsmul_point_eq_smulX_smulY hn).1`
at any future site that needs only the nonsingularity witness. Not a mathlib contribution — the statement is
not even expressible in mathlib (no `WeierstrassCurve.Universal`), and the general `[n]P`-coordinate bridge it
specialises is a separate, large NagellLutz/HasseWeil development to be assessed via the parent theorem
`zsmul_point_eq_smulX_smulY`, not this projection.
