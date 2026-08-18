# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulY_one_ne_negY`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences).
> Single declaration. Literature search run (ChatGPT MCP down — fell back to WebSearch ×2 +
> grep; `lean_loogle`/`lean_leansearch` not available in this env — used mathlib-source grep
> for Phase 5). Decl is SMALL (internal `≠` glue), so the wide sweep is not forced.

## Baseline (Phase 0)

- lake build:               stale (not re-run; per task — reason from source). The decl elaborates in the committed tree.
- decl `WeierstrassCurve.Universal.Affine.smulY_one_ne_negY`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:237`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Integer multiples of a rational point on an elliptic curve in terms of
                             division polynomials — proves `WeierstrassCurve.zsmul_eq_smulEval`,
                             i.e. `n • P = (φₙ : ωₙ, ψₙ)` in Jacobian coords. Author: Junyan Xu.

**Qualified name verified from source.** The parsed name
`WeierstrassCurve.Universal.Affine.smulY_one_ne_negY` is correct:
`namespace WeierstrassCurve` (ZSMul.lean:76) → `namespace Universal` (:86) →
`namespace Affine` (:157); decl at :237. (Verified vs. the task's tentative
`WeierstrassCurve.Universal.Affine.smulY_one_ne_negY` — matches.)

---

## Statement (Phase 1)

`smulY_one_ne_negY` asserts that **the tautological (universal) point is not 2-torsion**:
its `Y`-coordinate differs from its negation's `Y`-coordinate.

Setting (all project-local): on the *universal* Weierstrass curve `pointedCurve`
(`curve.baseChange Universal.Field`, the universal curve over the fraction field
`Universal.Field = Frac(ℤ[a₁..a₆,X,Y]/⟨Weierstrass⟩)`), with `(smulX 1, smulY 1)` the affine
coordinates of `1 • point` — which by `smulX_one`/`smulY_one` (ZSMul.lean:173–174) are just the
images of the indeterminates: `smulX 1 = polyToField (C X)`, `smulY 1 = polyToField Y`. So this is
literally the generic point `(X, Y)`.

Then:
$$\mathrm{smulY}\,1 \;\neq\; \mathrm{negY}(\mathrm{smulX}\,1,\ \mathrm{smulY}\,1).$$

Mathematically: `Y ≠ negY(X, Y)`, i.e. the generic point `(X, Y)` is **not equal to its own
negation** — equivalently, it is not a point of order 2. (`negY x y = -y - a₁x - a₃`; for the
generic point, `y − negY = 2y + a₁x + a₃ = ψ₂(x,y)`, the 2-division polynomial.)

Variables / typeclasses (Lean side):
- none free — everything lives in the fixed field `Universal.Field`; `pointedCurve`, `smulX 1`,
  `smulY 1` are all concrete project constants.

Hypotheses: **none.** It is an unconditional `≠`.

Conclusion (math): `Y ≠ negY(X, Y)` for the generic point of the universal curve.
Conclusion (Lean): `smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1)`.

Proof (1 line, ZSMul.lean:238):
`rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero`
— i.e. reduce `a ≠ b` to `a − b ≠ 0`, rewrite `Y − negY(X,Y) = ψ₂ = ψᵤ 2` via the immediately
preceding lemma `smulY_one_sub_negY` (ZSMul.lean:233), then close with the project fact
`ψᵤ_ne_zero two_ne_zero` (the universal 2-division polynomial is nonzero because `2 ≠ 0`).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a single unconditional `≠` between two concrete elements of `Universal.Field`, proved in
one line from its sibling `smulY_one_sub_negY` (a sub-`negY` value) and the project's
`ψᵤ_ne_zero`. It is pure plumbing: it exists only to feed `Affine.slope_of_Y_ne` and
`add_self_of_Y_ne` in the doubling step. It is **not** a named theorem in the literature; the
underlying *concept* ("y ≠ −y ⟺ not 2-torsion") is standard textbook background, not a citable
result. Hence SMALL — the wider literature sweep is not auto-forced (and `--exhaustive` not set).

(Light sweep performed anyway, Phase 3, to confirm there is no named identity here.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — **n/a**. One-line check skipped.

---

## Literature search table

| #  | Channel                       | Query                                                                                 | Hit? | Standard form found                                                  | Notes |
|----|-------------------------------|---------------------------------------------------------------------------------------|------|----------------------------------------------------------------------|-------|
|  1 | WebSearch (specific)          | EC point not 2-torsion `Y ≠ negY`, `ψ₂` nonzero ⟺ `y ≠ 0`                               | yes  | `ψ₂ = 2y`; `P` is 2-torsion ⟺ `ψ₂(P)=0` ⟺ `y=0` ⟺ `y=−y` (background) | MIT 18.783 PS3; Wikipedia "Division polynomials"; arXiv 1005.4771, 1103.4560 |
|  2 | WebSearch (universal/generic) | generic point universal EC order two, `ψ₂` doubling well-defined                        | yes  | same: `P` is n-torsion ⟺ `ψₙ(P)=0`; doubling needs `y ≠ −y` (= `ψ₂≠0`) | Wikipedia; arXiv 1605.09279 ("Division by 2"), 0706.4379 |
|  3 | ChatGPT MCP                   | named identity for "generic point not 2-torsion"?                                       | n/a  | MCP down (task flagged) — covered by #1–#2                            | fallback |
|  4 | Local references              | grep `.mathlib-quality/references/` for 2-torsion / `ψ₂` / `negY`                        | n/a  | no source-paper PDFs in references dir (only skill docs)              | n/a |
|  5 | nLab / Stacks                 | division polynomial / 2-torsion characterisation                                        | n/a  | no dedicated page; not a categorical/scheme-theoretic named result    | n/a |

### Literature summary (Phase 3)

Concept identified as: **"a point is 2-torsion iff `y = −y` iff `ψ₂ = 0`"** — i.e. the (totally
standard, textbook-background) characterisation of 2-torsion via the 2-division polynomial. The
specific Lean statement is its application to *one specific point* (the universal/generic point):
"the generic point is not 2-torsion." This is **not** a named theorem; it is a one-line corollary
of `ψ₂ ≠ 0` for the generic point. Sources agree on the background fact (Wikipedia, MIT 18.783,
the "division by 2" literature), but none elevate "the generic point isn't 2-torsion" to a citable
named identity — it is the trivial generic case. Most general standard form: the characterisation
`y = W.negY x y ↔ 2-torsion` for an arbitrary point on an arbitrary Weierstrass curve. Disagreement
with the literature: none (the Lean statement is a special case of the standard characterisation).

---

## Generality analysis — `WeierstrassCurve.Universal.Affine.smulY_one_ne_negY`

Literature-standard form (Phase 3): for an arbitrary Weierstrass curve `W` and an arbitrary point
`(x, y)`, `(x,y)` is 2-torsion ⟺ `y = W.negY x y`. The contrapositive "`(x,y)` not 2-torsion ⟺
`y ≠ W.negY x y`" is the reusable shape.

| # | Parameter / hypothesis    | Current Lean form                                              | Literature-standard form                              | Weaker / more-general form exists? | Reason |
|---|---------------------------|---------------------------------------------------------------|-------------------------------------------------------|------------------------------------|--------|
| 1 | the point                 | the *one specific* generic point `(smulX 1, smulY 1) = (X,Y)` of the universal curve | *any* point `(x,y)` on *any* `W`                       | **YES — strictly more general**    | The statement is pinned to a single concrete point. The reusable mathlib-shaped fact is the *characterisation* `y ≠ negY x y ↔ ¬ 2-torsion` (or the criterion `y ≠ negY x y ↔ y − negY x y ≠ 0`, trivially `sub_ne_zero`), quantified over all `(x,y)`. As stated, this lemma is a non-generalisable *instance*, not the general lemma. |
| 2 | the curve                 | universal `pointedCurve` over `Universal.Field`               | any `W / F`                                            | (subsumed by #1)                   | A generic-point statement does not carry over by base change the way an *identity* would: `(X,Y)` not being 2-torsion is specifically a fact about the universal curve's distinguished point. The general statement is the per-point characterisation, not a "universal" packaging of this `≠`. |
| 3 | hypotheses                | none                                                          | none (the criterion is unconditional)                 | n/a                                | already unconditional. |

### Generality verdict (Phase 4b)

The current form is: **a NON-GENERALISABLE INSTANCE** of a more general standard fact.
Number of weakening opportunities: the statement itself cannot be "weakened" — it is a `≠` about a
fixed point, with no hypotheses to drop. The *general* version (`y ≠ negY x y ↔ ¬ 2-torsion`, over
all points/curves) is a **different, more useful lemma**, and — crucially — that general version is
**already realised in mathlib** in the relevant coordinate systems (see Phase 5). So there is
nothing to "generalise-and-add" that mathlib does not already have.
Proposed restatement: none — this exact `≠` is project-internal glue, not a mathlib target.

### Modern-idiom check (Phase 4c)

| #  | Question                                                       | Applies? | Note |
|----|----------------------------------------------------------------|----------|------|
|  1 | "Let X be a foo" preamble → typeclass?                          | no       | already typeclass-free |
|  3 | construction → universal-property class?                        | partial  | the `Universal` curve *is* the universal device, but here it only supplies a *specific point*; the statement is not a generic identity that the universal framing buys generality for — it is a concrete `≠` about that point |
|  7 | concrete → general (over all points/curves)?                    | yes      | the general form is the per-point characterisation `y ≠ negY x y ↔ ¬ 2-torsion` — **already in mathlib** (Phase 5), so this is "mathlib-has-the-general-form", not "generalise-first" |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **n/a as a restatement of this decl** — the contemporary form of the
content (the per-point 2-torsion ⟺ `y = negY` criterion) already exists upstream; this lemma is
just its trivial application to the generic point. No restatement makes *this* `≠` a mathlib
contribution.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. Skipped.

---

## Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulY_one_ne_negY`

[A] Lean-Finder       — not available in this env                          n/a: tool absent
[B] Loogle            — `lean_loogle` not available in this env             n/a: tool absent (reasoned from mathlib source)
[C] LeanSearch        — `lean_leansearch` not available in this env         n/a: tool absent
[D] Grep mathlib src  `smulY_one_ne_negY`, `Universal.Affine`, `pointedCurve`, `smulY`/`smulX`, `Universal.Field` → **no hits** (the whole `Universal` framework is project-only)
[E] Name/shape pattern `*_ne_negY`, `Y_ne_negY*`, `y ≠ .*negY`, `negY` + `ne`/`sub_ne_zero` over the EC files → **HITS for the general criterion** (see below)

Two searches:
  - **the user's exact form** (`smulY 1 ≠ negY (smulX 1) (smulY 1)` on the universal curve):
    **not in mathlib** — `smulY`, `smulX`, `ψᵤ`, `pointedCurve`, `Universal.Field` do not exist
    upstream; there is no "universal curve generic point" object at all.
  - **the general fact it instantiates** (`y ≠ W.negY x y` characterising non-2-torsion / enabling
    doubling): **mathlib HAS this**, as reusable API across coordinate systems:
    - `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean:174` `slope_of_Y_eq`,
      `:184` `slope_of_Y_ne`, `:125` `Y_eq_of_Y_ne`/`Y_eq_or_eq` — the affine slope is defined by
      casing on `y₁ = W.negY x₂ y₂` vs `y₁ ≠ W.negY x₂ y₂` (exactly the doubling dichotomy).
    - `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:677` `add_self_of_Y_eq`,
      `:693` `add_self_of_Y_ne`, `:697` `add_self_of_Y_ne'` — doubling a point, hypothesis
      `hy : y₁ ≠ W.negY x₁ y₁` (the general form of what `smulY_one_ne_negY` supplies for `(X,Y)`).
    - `Mathlib/AlgebraicGeometry/EllipticCurve/{Projective,Jacobian}/Formula.lean:136–145`
      `Y_ne_negY_of_Y_ne`, `Y_ne_negY_of_Y_ne'` — the projective/Jacobian named lemmas for
      `Y ≠ negY` under `[NoZeroDivisors R]`.
    - `negY` and `negY_negY` (Affine/Formula.lean:113,116); `ψ₂ = 2Y + a₁X + a₃` (the 2-division
      polynomial whose nonvanishing *is* `y ≠ negY`) lives in `DivisionPolynomial/Basic.lean`.

What mathlib HAS: the general per-point criterion `y = W.negY x y` (and its negation) as the
doubling dichotomy, in all three coordinate models, plus the `Y_ne_negY_of_Y_ne(')` lemmas.
What mathlib DOES NOT HAVE: the `Universal` curve / generic point, so it cannot have *this specific
instance*. But the instance is exactly an application of the API mathlib already ships.

Concluded: **mathlib has the general form; the specific decl is a project-only instance of it.**

---

## Call sites — `WeierstrassCurve.Universal.Affine.smulY_one_ne_negY`

Internal use count: **3** (within NagellLutz, all in ZSMul.lean; the declaration itself excluded).
External-to-file callers: 0.

| Caller file:line       | Usage pattern (one-line excerpt)                                                                 |
|------------------------|--------------------------------------------------------------------------------------------------|
| ZSMul.lean:246         | `rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, …]` — defines the tangent slope `slopeOne` (proves `slopeOne_eq_neg_div`) |
| ZSMul.lean:355         | `exact ⟨Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2, …⟩` — base case `n=1` of `zsmul_point_eq_smulX_smulY` (the point doubles to `2 • P`) |
| ZSMul.lean:356         | `add_self_of_Y_ne smulY_one_ne_negY` — same base case, supplies the `y ≠ negY` hyp to mathlib's `add_self_of_Y_ne` |

Signal: **K = 3 internal uses, all feeding mathlib's `slope_of_Y_ne` / `add_self_of_Y_ne`** — i.e.
it exists purely to discharge the `y ≠ W.negY x y` side-condition of *mathlib's own* doubling API,
for the universal point. That is glue, not a result. Leans NO (composable/internal).

---

## Composition check (Phase 6)

Can `smulY_one_ne_negY` be obtained in ≤3 chained calls? **Yes — it is one rewrite + a project fact.**

The actual proof IS a 2-step composition (ZSMul.lean:238):
1. `← sub_ne_zero` (mathlib) — reduce `a ≠ b` ⟶ `a − b ≠ 0`.
2. `smulY_one_sub_negY` (project, ZSMul.lean:233) — rewrite `smulY 1 − negY(...) = ψᵤ 2`.
3. `ψᵤ_ne_zero two_ne_zero` (project, ZSMul.lean:142) — `ψᵤ 2 ≠ 0`.

So **given the project's own `smulY_one_sub_negY` and `ψᵤ_ne_zero`**, this is a trivial
`sub_ne_zero`-composition. The only non-mathlib ingredients are those two sibling project lemmas
(themselves part of the ZSMul development). There is no mathlib-only composition (mathlib lacks the
`Universal` point), but within the project this is a 1-line corollary — it carries no independent
content. **COMPOSABLE** (from the project's own immediately-adjacent lemmas; and, conceptually, the
*general* version is composable from mathlib's `Y_ne_negY_of_Y_ne` / 2-division-polynomial API).

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulY_one_ne_negY`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature (Phase 3): the content is the standard textbook background "`y = −y` ⟺ 2-torsion ⟺
  `ψ₂ = 0`" (Wikipedia, MIT 18.783, the division-by-2 literature). **Not a named identity** — this
  decl is its trivial application to the generic point.
- Generality (Phase 4): a **non-generalisable instance** of the per-point criterion
  `y ≠ negY x y ↔ ¬2-torsion`; the general form is a *different* lemma and is **already upstream**.
- Mathlib search (Phase 5): mathlib **already has the general form** — `slope_of_Y_ne`,
  `add_self_of_Y_ne(')` (affine), `Y_ne_negY_of_Y_ne(')` (projective/Jacobian), built on `negY`
  and the 2-division polynomial. It only lacks the project-only `Universal` *point* this is pinned
  to.
- Composition (Phase 6): **composable** — the proof is `sub_ne_zero` + the adjacent project lemma
  `smulY_one_sub_negY` + `ψᵤ_ne_zero`; a 1-line corollary with no standalone content.
- Call sites: all 3 uses merely discharge the `y ≠ W.negY x y` side-condition of *mathlib's* own
  `slope_of_Y_ne` / `add_self_of_Y_ne` for the universal point — pure glue.

**Rationale.**
`smulY_one_ne_negY` is a one-line internal `≠` fact — "the universal curve's generic point `(X,Y)`
is not 2-torsion" — used only to feed the `y ≠ negY` side-condition of mathlib's existing doubling
/ slope API. It is **not** a named result (unlike its sibling `smulX_sub_smulX`, which is a verbatim
Wikipedia identity and was YES-add-as-is). The reusable content here — the criterion `y ≠ negY x y`
characterising non-2-torsion and enabling point doubling — **already lives in mathlib** in all three
coordinate models (`slope_of_Y_ne`, `add_self_of_Y_ne`, `Y_ne_negY_of_Y_ne`). What this lemma adds
on top is solely the *instantiation* "...for the universal generic point", which is (a) impossible
to state in mathlib (the `Universal` curve/point is project-only) and (b) a trivial `sub_ne_zero`
corollary of the adjacent `smulY_one_sub_negY` + `ψᵤ_ne_zero`. So it is not an independent mathlib
candidate.

This does **not** mean the surrounding development should not be upstreamed: the whole ZSMul /
`Universal`-curve multiplication-by-`n` machinery (capstone `zsmul_eq_smulEval`) is a genuine
mathlib gap-filler, and if it lands, `smulY_one_ne_negY` rides along as **internal glue** (a private
`have`/one-liner), not as a standalone lemma worth its own name in the public API. As an independent
upstreaming target — which is what this assessment scores — it is NO: mathlib already has the
general criterion, and this is a composable, non-generalisable instance of it.

**WHY not add it (refactor-actionable).**
- Don't PR this as a named lemma. In any upstreaming of ZSMul, inline it (or keep it `private`) — it
  is the `y ≠ negY` discharge for the `n=1` doubling base case, and mathlib reviewers will expect
  that to be a local `have` produced from `ψ₂ ≠ 0`, not a public declaration.
- The general, reusable statement (`y ≠ W.negY x y ↔ ¬ point is 2-torsion`, i.e. a clean
  `IsTwoTorsion`/`negY`-fixed-point characterisation) is the only "addable" shape in this vicinity,
  and mathlib **already covers its operative direction** via `slope_of_Y_ne` / `add_self_of_Y_ne` /
  `Y_ne_negY_of_Y_ne`. If anything is missing upstream it is a *named iff* packaging
  `y = W.negY x y ↔ 2 • P = 0`, which is a separate, generic lemma — not this instance.

Proposed mathlib location: **none for this decl** (inline inside the larger ZSMul PR if that lands).
Proposed PR title: n/a (not an independent contribution).

---

## Next step

Treat `smulY_one_ne_negY` as **internal glue** of the ZSMul / universal-curve development: keep it
`private`/inline when that development is upstreamed, rather than PR-ing it as a standalone lemma.
Mathlib already provides the general `y ≠ negY x y` doubling/slope criterion
(`slope_of_Y_ne`, `add_self_of_Y_ne`, `Y_ne_negY_of_Y_ne`); this decl is a composable,
non-generalisable instance of it for the generic point. No `/generalise` action is warranted (the
statement is a hypothesis-free `≠` about a fixed point; its general form already exists upstream).
