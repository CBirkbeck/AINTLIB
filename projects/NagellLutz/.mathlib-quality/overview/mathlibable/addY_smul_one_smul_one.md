# /mathlibable report — `WeierstrassCurve.Universal.Affine.addY_smul_one_smul_one`

## Baseline (Phase 0)
- lake build:               not run (env: local build stale by task note); decl read from source
- decl `WeierstrassCurve.Universal.Affine.addY_smul_one_smul_one`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:277`
- enclosing namespaces:     `WeierstrassCurve` (76) → `Universal` (86) → `Affine` (157–393)
                            ⇒ qualified name **`WeierstrassCurve.Universal.Affine.addY_smul_one_smul_one`** (VERIFIED)
- kind:                     lemma (theorem)
- has sorry:                no
- module docstring summary: proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ:ωₙ:ψₙ)` in
                            Jacobian coords for any integer `n` and nonsingular affine point `P=(x,y)`,
                            via a "universal Weierstrass curve" over `ℤ[A₁…A₆,X,Y]/⟨P⟩` and even–odd / strong induction.

## Statement (Phase 1)

`addY_smul_one_smul_one` states the following:

> On the **universal** Weierstrass curve (coefficients `A₁,…,A₆` and a generic point `(X,Y)` adjoined
> as indeterminates, working in `Universal.Field = Frac(ℤ[A₁…A₆,X,Y]/⟨W(X,Y)⟩)`), apply mathlib's
> chord–tangent affine **Y**-coordinate `addY` to the doubled point: base point `(smulX 1, smulY 1) = (X, Y)`
> with itself, using the **tangent slope** `slopeOne = -W.polynomialX / ψ₂`. The result equals `smulY 2`,
> the division-polynomial Y-coordinate `ω₂ / ψ₂³` of `2·(X,Y)`.

In standard notation: writing `λ = (3X² + 2a₂X + a₄ − a₁Y)/(2Y + a₁X + a₃)` for the tangent slope at `P=(X,Y)`,
the chord-tangent doubling Y-coordinate `−(λ(x₃ − X) + Y) − a₁x₃ − a₃` (with `x₃ = addX` the doubled X-coord)
equals `ω₂(X,Y)/ψ₂(X,Y)³`. It is the **n = 2 base case** of the affine multiplication-by-n formula
`n·P = (φₙ/ψₙ², ωₙ/ψₙ³)`, specialised to the universal point.

Variables / typeclasses (Lean side):
- none free — everything is fixed `Universal` data: `curve : Affine (MvPolynomial Coeff ℤ)`, its
  `pointedCurve`, the fraction field `Universal.Field`, and `polyToField`.

Hypotheses (Lean side): none (it is an unconditional equation in `Universal.Field`).

Conclusion (math): `addY P P λ = ω₂/ψ₂³` for the universal point `P=(X,Y)` and tangent slope `λ`.

Conclusion (Lean): `pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2`.

Proof: rewrite `smulY`, `ω`, `redInvarDenom_two`, `compl₂EDSAux_two` (so `ω₂` collapses), unfold mathlib's
`addY`/`negAddY`/`negY`/`negPolynomial`, substitute `addX_smul_one_smul_one`, `smulX_two`,
`slopeOne_eq_neg_div`, `smulX_one`, `smulY_one`, `ψ_three`; push `polyToField` through with `map_*`; then
discharge the resulting rational-function identity with the private field-clearing helper
`addY_smul_one_smul_one_aux` (`field_simp; ring`), using `ψ₂ ≠ 0`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a base-case helper lemma. Not a named theorem, not a `## Main results` entry — it is one of
several intermediate identities (`addX_smul_one_smul_one`, `slopeOne_eq_neg_div`, `smulY_one_sub_negY`, …)
feeding the `n=2` branch of the induction in `zsmul_point_eq_smulX_smulY`. The *headline* result of the file
(`zsmul_eq_smulEval`) is BIG; this leaf is not.

## One-line check (Phase 2b)

Kind is `lemma`, not `def` — one-line check **n/a**.

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | division polynomials ψₙ ωₙ φₙ multiplication-by-n affine-coordinate formula                     | yes  | `nP = (φₙ/ψₙ², ωₙ/ψₙ³)`; `ψ₂=2y`, `φₙ=xψₙ²−ψₙ₊₁ψₙ₋₁`, `ωₙ=(4y)⁻¹(ψₙ₊₂ψₙ₋₁²−ψₙ₋₂ψₙ₊₁²)` | Wikipedia "Division polynomials"; MIT 18.783 notes; Silverman AEC III.3 |
|  2 | WebSearch (doubling base case)   | doubling formula tangent slope λ=(3x²+a)/2y; 2P via ψ₂,ω₂; base case                            | yes  | `λ=(3x₁²+a)/(2y₁)`; doubling = the `n=2` instance of `nP=(φₙ/ψₙ²,ωₙ/ψₙ³)` | confirms the n=2 specialisation is standard, but is never stated as its own named result |
|  3 | WebSearch (named-after/aliases)  | (covered by #1/#2) "division polynomial recursion", "elliptic divisibility sequence"            | yes  | same; EDS framing (Ward) | the ψ recursion ↔ EDS link is the Ward 1948 theory mathlib already formalises as `normEDS` |
|  4 | ChatGPT MCP                      | not run — env note flags ChatGPT MCP may be down; #1/#2/#5 + mathlib source already pin the standard form unambiguously | n/a | — | the multiplication-by-n formula is textbook-canonical; no historical-evolution ambiguity to resolve |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` — directory absent                          | n/a  | —                   | recorded n/a (no refs dir) |
|  6 | nLab                             | "division polynomial" / "elliptic curve multiplication"                                        | n/a  | —                   | nLab has no dedicated division-polynomial page; concept is classical AG/NT, well covered by #1 |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project (alg geom)        | division polynomial / elliptic curve torsion                                                   | n/a  | —                   | Stacks does not treat explicit division-polynomial formulas |
|  9 | MathOverflow / MSE               | "omega division polynomial y-coordinate" generality                                            | yes  | same closed forms as #1; sign/normalisation conventions vary (`ω` vs `ψ₂ₙ/(2ψₙ⁴)`) | only convention drift, not a generality axis |
| 10 | recent arXiv (≤5y)               | division polynomials arbitrary isogenies / alternate models (2010/630, 2503.15428, 0809.2182)  | yes  | generalisations to other curve models / isogenies | none change the Weierstrass `n=2` base case |

Protocol status: WebSearch ran 3 distinct queries at different generality levels; local refs, nLab, Stacks,
nCatLab, MathOverflow, arXiv each checked or recorded n/a with a reason. ChatGPT MCP not run (flagged down in
env); the standard form is nonetheless pinned unambiguously by the web + mathlib-source evidence, so the
generality question is fully answered.

### Literature summary (Phase 3)

Concept identified as: the **affine multiplication-by-n formula** `nP = (φₙ/ψₙ², ωₙ/ψₙ³)` for elliptic
curves, specialised to its **n = 2 base case** (point doubling expressed via division polynomials).
Sources agree on the standard form: **yes** (up to sign/normalisation conventions for `ω`).
Most general standard form: holds for a general Weierstrass curve `y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆` over any
field (the project works over the universal `ℤ[A₁…A₆,X,Y]/⟨W⟩`, i.e. the *most* general base).
Generality dimensions where the literature varies: only the `ω` normalisation convention; no
typeclass/structural generality axis (already at full Weierstrass generality).
Disagreement with the literature: none — the lemma is a faithful, fully-general instance of the standard formula.

**Key literature↔mathlib gap (decisive for the verdict):** every source states `nP = (φₙ/ψₙ², ωₙ/ψₙ³)` as the
bridge between the **group law** and **division polynomials**. Mathlib has the two halves separately
(group law in `…/Affine/Point.lean`; ψ/φ/ω in `…/DivisionPolynomial/Basic.lean`) but **does not connect them**
— see Phase 5. This NagellLutz development is exactly that missing bridge; `addY_smul_one_smul_one` is a
base-case rung of its scaffolding.

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): `nP = (φₙ/ψₙ², ωₙ/ψₙ³)` over a general Weierstrass curve / field.

| # | Parameter / hypothesis            | Current Lean form                                   | Literature-standard form        | Weaker form? | Reason |
|---|-----------------------------------|-----------------------------------------------------|---------------------------------|--------------|--------|
| 1 | base ring / field                 | `Universal.Field = Frac(ℤ[A₁…A₆,X,Y]/⟨W⟩)` (fixed)  | general Weierstrass over a field | NO           | already the *universal* (most general) base; deliberately maximal — the whole `Universal` device exists to be specialised to any field including char 2 |
| 2 | the curve                         | the fixed universal `curve`/`pointedCurve`          | arbitrary `W`                   | n/a          | universal by construction; a concrete `W` is recovered by `ringEval`/specialisation |
| 3 | the point                         | the generic universal point `(X,Y)=(smulX 1,smulY 1)`| arbitrary `(x,y)` on `W`        | n/a          | generic point is the universal object; concrete points specialise from it |
| 4 | which multiple                    | `n = 2` (base case only)                            | all `n` (the full formula)      | — (narrower) | this is **deliberately the base case**; generality in `n` is the *parent* theorem's job, achieved by induction — not a weakening this leaf should absorb |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL in its base** (universal curve = the most general setting) but is
an **intentional `n=2` SPECIALISATION** of the all-`n` formula. The narrowness in `n` is structural: this
lemma is a *base case* whose role is to be consumed by the induction in `zsmul_point_eq_smulX_smulY`, which
is what delivers the general-`n` statement. "Generalising" this leaf to all `n` would just merge it into the
parent theorem — i.e. delete it as a standalone decl, not restate it.
Number of weakening opportunities (as an independent decl): 0 sensible ones.
Proposed restatement: n/a (the right "generalisation" is the parent theorem, which already exists).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
|  1 | bundled-hyp → typeclass/instance | no | no "let X be a foo" preamble; everything is concrete universal data |
|  2 | sequences/metric → filters/topology | no | a finite algebraic identity in a fraction field; no analysis |
|  3 | construct → universal-property class | no | (note: "universal curve" here is a representing object, but this *leaf* is just an equation in it) |
|  4 | set+closure → bundled substructure | no | no substructure in sight |
|  5 | vector-space/field-specific → module/(semi)ring | no | already over the universal ring/its fraction field |
|  6 | 1-categorical → higher-categorical | no | not categorical |
|  7 | concrete index ℕ/ℤ/ℝ → general monoid/group | **partially** | the index `2` is concrete, but generalising over `n` *is* the parent theorem (`zsmul_point_eq_smulX_smulY`), reached by induction — not a reformulation of this leaf |

Modern idiom available: **no** (for this leaf as a standalone decl).
Reason: it is a base-case algebraic identity; the only "modernisation" is to view it as one rung of the
already-existing inductive proof of the general formula — which is organisational, not a restatement of this decl.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

## Mathlib search-status (Phase 5)

Five-method search (run as grep over the pinned mathlib at
`.lake/packages/mathlib/Mathlib`, since the mathlib *names* here are fully qualified and project-bespoke):

[A] Lean-Finder       n/a (offline) — substituted by exhaustive grep [D]/[E] over the actual pinned tree
[B] Loogle            type-pattern `W.addY _ _ _ _ = _` and `_ = ωₙ/ψₙ³`     no relevant hit (mathlib has no
                      lemma equating `Affine.addY` with a division-polynomial expression — Phase-5 grep [D] confirms)
[C] LeanSearch        "elliptic curve n times point division polynomial omega" no hit (no such bridge lemma exists in mathlib)
[D] Grep mathlib src  `smulX|smulY|slopeOne|pointedCurve|zsmul_eq_smulEval|smulEval|zsmul_point` → **0 matches**;
                      `addY_smul|addX_smul` → only Jacobian/Projective `Formula.lean` **scaling-homogeneity**
                      lemmas (`addY (u•P)(v•Q) = (u…v…)•addY P Q`) — a *different* statement, unrelated;
                      `DivisionPolynomial|EllipticDivisibilitySequence` referenced in
                      `AlgebraicGeometry/EllipticCurve/` **only** inside the two `DivisionPolynomial/*.lean`
                      files — i.e. the group-law `Point` files never mention division polynomials
[E] Name pattern      `namespace Universal` in EllipticCurve → **none** (mathlib's only `Universal` namespaces
                      are `UniversallyOpen` and Lie `UniversalEnveloping`, unrelated)

Searched for both: (a) the user's exact form — absent; (b) the literature-standard `nP=(φₙ/ψₙ²,ωₙ/ψₙ³)`
bridge in any guise — also absent. Mathlib's `DivisionPolynomial/Basic.lean` even carries a `TODO` and stops
at defining ψ/φ/ω; it never proves the multiplication-by-n formula.

Concluded: **not in mathlib** (all methods exhausted). Moreover the *entire substrate* this lemma is stated
over — `Universal.Field`, `smulX`, `smulY`, `slopeOne`, `pointedCurve` — does not exist in mathlib. Mathlib
has only mathlib's `Affine.addY`/`negY`/`slope` (which this lemma *applies*) and ψ/φ/ω as bare polynomials;
it has **no bridge** between the group law and division polynomials. Note also: the project explicitly *forks*
mathlib's `DivisionPolynomial.Basic` and `EllipticDivisibilitySequence` (see headers of
`LutzNagell/DivisionPolynomial.lean` and `…/EllipticDivisibilitySequence.lean`) — so any duplication is of the
ψ/φ/ω *infrastructure*, never of this multiplication-formula lemma, which has no mathlib counterpart.

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.Universal.Affine.addY_smul_one_smul_one`

Internal use count: **1** (excluding the declaring file's own `_aux` helper line).
External-to-file callers: 0 (used only within `ZSMul.lean`).

| Caller file:line          | Usage pattern (one-line excerpt) |
|---------------------------|-----------------------------------|
| `ZSMul.lean:354`          | `erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]` — the **n = 2 base case** of `zsmul_point_eq_smulX_smulY` |

(`ZSMul.lean:284` is the body's own use of the private `addY_smul_one_smul_one_aux`, not a call to this lemma.)

Inline-derivation grep (re-derived elsewhere without the lemma?): (none) — the only place this identity is
needed is that one base-case branch; it is not re-proved anywhere else.

Can `addY_smul_one_smul_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: express it via mathlib's `Affine.addY_sub_negY_addY` + ψ closed forms.
  - Result: **fails.** That mathlib lemma is about the *difference* `y₃ − negY x₃ y₃` for a general
    addition, not the absolute `addY = ω₂/ψ₂³` equality, and crucially the right-hand side `ω₂/ψ₂³` is
    expressed through the project's `smulY`/`ω`/`redInvarDenom_two`/`compl₂EDSAux_two` — none of which exist
    in mathlib. There is nothing in mathlib to chain to.

Attempt 2: any direct mathlib path.
  - Result: **fails.** Mathlib provides no division-polynomial-valued formula for the group law at all.

Conclusion: **NOT-COMPOSABLE** — not from a small chain of mathlib calls (mathlib lacks every right-hand-side
ingredient and the whole bridge). The proof is a genuine `field_simp; ring` identity over bespoke objects.

## Verdict: `WeierstrassCurve.Universal.Affine.addY_smul_one_smul_one`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): the `n=2` instance of the canonical `nP=(φₙ/ψₙ²,ωₙ/ψₙ³)` formula; standard, but never a
  named standalone result — and mathlib lacks the whole group-law↔division-polynomial bridge.
- Generality (Phase 4): MAXIMALLY GENERAL base (universal curve) but a deliberate `n=2` base-case specialisation;
  the "generalisation over n" is the *parent* theorem, not a restatement of this leaf.
- Mathlib search (Phase 5): NOT in mathlib; the entire substrate (`Universal.Field`, `smulX/smulY/slopeOne`,
  `pointedCurve`) is project-bespoke; mathlib has no bridge lemma of this kind.
- Composition (Phase 6): NOT-COMPOSABLE (1 internal call site; no mathlib building block for the RHS).

**Rationale.**
This is a **base-case glue lemma** inside a larger, genuinely mathlib-worthy development. The headline theorem
of the file — `WeierstrassCurve.zsmul_eq_smulEval` / `…Affine.zsmul_point_eq_smulX_smulY`, i.e. the
multiplication-by-n formula `n·P = (φₙ/ψₙ², ωₙ/ψₙ³)` connecting the elliptic-curve group law to division
polynomials — is canonical in the literature and **demonstrably absent from mathlib** (the group-law `Point`
files and the `DivisionPolynomial` files never reference one another; `DivisionPolynomial/Basic.lean` even
has a standing `TODO`). That bridge belongs in mathlib. But `addY_smul_one_smul_one` itself is *not* a
free-standing API lemma: it is the `n=2` Y-coordinate rung, stated entirely in terms of the project's
`Universal.Field` and the intermediate constructions `smulX`/`smulY`/`slopeOne`/`pointedCurve`, and it is
consumed exactly once — in the base case of the induction that proves the real theorem (`ZSMul.lean:354`).

So neither a clean YES nor a clean NO is correct, and the choice is a project-/upstreaming-policy judgment, not
something the evidence settles. It is **not** `NO-mathlib-has-it` (mathlib has neither it nor anything it
specialises from) and **not** `NO-composable-from-mathlib` (mathlib offers no building block for the
division-polynomial RHS — composition genuinely fails). It is **not** `YES-add-as-is` for *this decl in this
form*: shipping a lemma phrased over the bespoke `Universal` scaffolding, used once as a base case, is not how
this would enter mathlib — it would go upstream **as part of the whole bridge development**, where this lemma
is most likely an internal/`private` step (or folded into the doubling case), not a public-facing result.
Hence BORDERLINE: the decision is *how to upstream the surrounding development*, which is a human call.

**Numbered questions (≤5):**
  1. Is the plan to upstream the *whole* multiplication-by-n ↔ division-polynomial bridge
     (`zsmul_eq_smulEval` and the `Universal` machinery) to mathlib? If yes, this lemma should be assessed
     as an internal step of that PR series, not as a standalone decl.
  2. In an upstreamed version, would `addY_smul_one_smul_one` be **`private`** (or inlined into the n=2 /
     doubling case)? If yes → it should not ship as a named public lemma, and the standalone verdict is NO.
  3. Should the `Universal`-curve device itself live in mathlib (as the representing object for "generic
     Weierstrass point"), or is it project-internal proof scaffolding to be specialised away before any PR?
     The answer determines whether *any* `smulX/smulY/slopeOne`-phrased lemma is mathlib-shaped at all.
  4. Independently of this leaf: do you want a `/mathlibable` pass on the **parent** results
     (`zsmul_point_eq_smulX_smulY`, `zsmul_eq_smulEval`) — those are the genuinely mathlib-worthy targets and
     the natural unit for the upstreaming decision?

**Next action:** user answers Q1–Q4. Most likely resolution: keep `addY_smul_one_smul_one` **project-local**
(or `private`) as a base-case step, and instead run `/mathlibable` on the parent theorem
`WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY` (and `WeierstrassCurve.zsmul_eq_smulEval`),
which is where the real mathlib gap — the group-law↔division-polynomial bridge — lives.

---

## Next step

Run `/mathlibable WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY` (the parent theorem and the
genuine mathlib-gap candidate); treat this base-case lemma as an internal step of that development rather than
an independent contribution. Confirm whether the `Universal` scaffolding is upstreaming target or
specialise-away-first.
