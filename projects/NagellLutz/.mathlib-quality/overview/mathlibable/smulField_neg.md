# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.smulField_neg`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Author of the source: Junyan Xu.
> Single declaration. Verdict authored from source (local build stale per task brief;
> reasoned from the elaborated statement, the vendored mathlib `.lake` tree, and a full
> literature sweep).

---

## Baseline (Phase 0)

- lake build:               ⚠ NOT RUN — local build stale (per task brief). Reasoned from source +
                            grep over the vendored mathlib (`.lake/packages/mathlib`, pin
                            `rev 09b373db6e24…`). The decl is a one-line `simp_rw … ; rfl` lemma, so
                            its content is unambiguous from source + its dependency chain.
- decl `WeierstrassCurve.Universal.Jacobian.smulField_neg`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:493`
- qualified name:           ✓ **VERIFIED**. Namespace nesting in the file:
                            `WeierstrassCurve` (L76) → `Universal` (L86) → `Jacobian` (L395–544).
                            Line 493 sits inside all three ⇒ the parsed guess
                            `WeierstrassCurve.Universal.Jacobian.smulField_neg` is **exactly correct**.
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: `ZSMul.lean` proves `WeierstrassCurve.zsmul_eq_smulEval`:
                            `n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coordinates for any integer `n` and a
                            nonsingular affine point `P = (x,y)` on a Weierstrass curve over a field.
                            Strategy: prove the universal polynomial identity over
                            `ℤ[A₁..A₆][X][Y]`, lift to the universal field, then specialise via `ringEval`.

```lean
lemma smulField_neg : smulField (-n) = (-1 : Universal.Field) • neg curveField (smulField n) := by
  simp_rw [smulField, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl
```

with `{n : ℤ}` an implicit `variable` in scope.

### Project-fork context (load-bearing)

This project (and `HasseWeil`) **fork** mathlib's division-polynomial stack:
- `LutzNagell/DivisionPolynomial.lean` is a near-verbatim copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` (re-imported to avoid
  `normEDS`/`complEDS` name clashes). `φ`, `ψ` are byte-for-byte mathlib's.
- `LutzNagell/DivisionPolynomialOmega.lean` defines `WeierstrassCurve.ω` — **which mathlib does NOT
  have**: mathlib's `DivisionPolynomial/Basic.lean` lists ω under "Main definitions" as
  `* TODO: the bivariate polynomials ωₙ.` and again `TODO: implementation notes for the definition of ωₙ`.
- `Universal.lean` builds the universal curve `Universal.Ring = ℤ[A₁..A₆,X,Y]/⟨W⟩`,
  `Universal.Field = Frac(Universal.Ring)`, `polyToField`, `curveField`, etc.

So `smulField_neg` sits atop two components that are **not in mathlib**: `ω` (the second Jacobian
coordinate of `smulField`) and the entire `Universal.*` scaffolding.

**Duplicate alert (consolidation-relevant, NOT a mathlib action):** an identical lemma
`smulField_neg` (same statement, same proof — but marked `private`) exists in the sibling fork
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:566`, alongside duplicated
`smulPoly_neg` (L509) and `smulRing_neg` (L512). This is the duplicated General*/PID* track the task
brief warned about — a clean AINTLIB-`main` dedup target regardless of the mathlib verdict.

---

## Statement (Phase 1)

`smulField_neg` is the **negation-of-multiplier identity for the Jacobian-coordinate division-polynomial
triple**, in the universal case, after passing to the fraction field.

Write `smulField n = polyToField ∘ ![φₙ, ωₙ, ψₙ] : Fin 3 → Universal.Field` — the three
division-polynomial families `curve.φ`, `curve.ω`, `curve.ψ` mapped into the universal field
`Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`. This is the Jacobian-coordinate representative of the universal point
`n • (X,Y)` (proved equal to the genuine group-law point in the sibling
`zsmul_point_eq_smulField`). The lemma says:

  `smulField (−n) = (−1) · 𝒩(smulField n)`,

where `𝒩 = neg curveField` is **mathlib's Jacobian negation on representatives**,
`Jacobian.neg P = ![P x, W.negY P, P z]` (i.e. `(X : Y : Z) ↦ (X : −Y−a₁X−a₃Z³ : Z)`), and the
`(−1) •` is the Jacobian scaling action on `Fin 3 → Universal.Field`.

Mathematically this is the **standard fact `[−n]P = −[n]P`** made explicit at the level of the
`(φ : ω : ψ)` coordinate triple. The `(−1) •` factor is bookkeeping: at the level of the
*polynomial* triple, `smulPoly(−n) = ![φ₋ₙ, ω₋ₙ, ψ₋ₙ]` and `neg(smulPoly n)` differ by the unit
`(−1)` in the Jacobian `(λ²x : λ³y : λz)` weighting, because `ψ` is **odd** (`ψ₋ₙ = −ψₙ`, so the
Z-slot picks up a `−1` ⇒ rescale by `λ = −1` to compare). The actual content is:
`φ` even, `ψ` odd, and `ω₋ₙ = −negY(…)` (the project's `ω_neg_eq_neg_negY`), fed through the
ring-hom functoriality of `polyToField`.

The proof is one `simp_rw`: it reduces the field statement to the **polynomial-ring statement**
`smulPoly_neg` (ZSMul.lean:487) and transports it through `polyToField` using mathlib's
`Jacobian.comp_smul` (`f ∘ (u • P) = f u • (f ∘ P)`) and `Jacobian.map_neg`
(`(W.map f).neg (f ∘ P) = f ∘ W.neg P`), then `map_neg`/`map_one` collapse `polyToField (−1) = −1`.
`smulRing_neg` (L490) is the byte-identical sibling over `Universal.Ring`.

Variables / typeclasses (Lean side):
- `{n : ℤ}` — the multiplier; ranges over **all integers** (already full `ℤ` generality).
- ambient: the universal ring/field tower (`Universal.Ring`, `Universal.Field`), `curve`, `polyToField`
  — fixed global objects of this development; no free typeclass parameters at the lemma site.

Hypotheses (Lean side): none (universal identity; holds for all `n : ℤ`, including `n = 0`).

Conclusion (math): the Jacobian-coordinate triple of `(−n)·(X,Y)` equals `−1` scaled by the Jacobian
negation of the triple of `n·(X,Y)` — i.e. `[−n]P = −[n]P` on the `(φ:ω:ψ)` representative.

Conclusion (Lean): `smulField (-n) = (-1 : Universal.Field) • neg curveField (smulField n)`
(an equation of `Fin 3 → Universal.Field`).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an internal stepping-stone lemma — the `(φ:ω:ψ)`-triple form of the negation-of-multiplier
identity in the universal field. Not a named theorem; not under `## Main results`. It is *part of* a
BIG development (the universal multiplication-by-`n` formula `zsmul_eq_smulEval`), but the individual
lemma is glue/bookkeeping in the `addXYZ` case analysis.

(Literature width was run EXHAUSTIVE regardless.)

---

## One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` → the one-liner-**definition** check is **n/a**.
(Note: the *proof* is effectively a single `simp_rw … ; rfl`, which reinforces the SMALL/glue framing
but is not the Phase-2b def check.)

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomials negation `[-n]P = -[n]P` φ ω ψ Jacobian coordinates negative index"               | yes  | `[n]P=(φₙ/ψₙ²,ωₙ/ψₙ³)`; `Ψ₋ₙ = −Ψₙ`; `nP=[φₙψₙ:ωₙ:ψₙ³]` Jacobian | arXiv 1103.4560, 1108.3051; MIT 18.783 L6; arXiv 2102.07573 |
|  2 | WebSearch (general / parity)     | "division polynomial parity ψ odd φ even ω negation formula negative multiplier"                        | yes  | `φₙ=φ₋ₙ`, `ψ₋ₙ=−ψₙ`, `ωₙ=ω₋ₙ`; `φ=xψ²−ψ₋ψ₊`, `4yω=ψ₋₁²ψ₊₂−ψ₋₂ψ₊₁²` | Cambridge PRSE "Common valuations…"; arXiv 1801.02664, 1303.5002 |
|  3 | WebSearch (named / Jacobian neg) | "Weierstrass curve negation Jacobian coordinates `−P=(X:−Y:Z)` representative"                          | yes  | `−(X:Y:Z)=(X:−Y:Z)` (general Weierstrass: `−Y−a₁X−a₃Z³`) | Wikipedia "Jacobian curve"; Doche–Lange ch.13; matches mathlib `Jacobian.neg` |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to channels 1–3 + 6–10)                                             | n/a  | —                                                     | recorded n/a; gap covered by 3 distinct WebSearch generality levels + a direct read of mathlib's `Jacobian/Point.lean`, `DivisionPolynomial/Basic.lean` |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`, `refs/NagellLutz/`                                  | n/a  | (neither directory exists)                            | recorded n/a; relied on Silverman AEC surfaced via WebSearch #2 |
|  6 | nLab                             | "elliptic curve" negation/inversion involution; division polynomial                                    | partial | inversion is the elliptic involution fixing `x`, negating `y` | ncatlab.org/nlab/show/elliptic+curve has the group law; `[−n]P=−[n]P` / ψ-parity is folklore, not a named nLab entry |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                                     | not a categorical concept (concrete coordinate identity) |
|  8 | Stacks Project (alg geom)        | division polynomial / multiplication-by-n on Weierstrass model                                         | n/a  | —                                                     | Stacks treats abelian schemes abstractly; no explicit division-polynomial coordinate formula |
|  9 | MathOverflow / Math.SE           | x/y-coordinate of `−P`; `ψ₋ₙ=−ψₙ`; division-polynomial negative index                                   | yes  | `Ψ₋ₙ:=−Ψₙ`; recurrences extend to `n<0`; `φ₋ₙ=φₙ`, `ω₋ₙ=ωₙ` | recurring as routine exercise; "definition for negative `n`", not a citable named theorem |
| 10 | recent arXiv (≤5 yr)             | EDS recurrence / division polynomials negation; alternate models                                       | yes  | `ψ₋ₙ=−ψₙ`; restated for other curve models             | arXiv 2102.07573 (EDS recurrence) = mathlib's `normEDS_neg`; eprint 2010/630 (alternate models) |

The protocol passes: WebSearch ran 3 distinct generality levels (specific φ/ω/ψ + Jacobian-triple
formula; general parity of φ/ψ/ω; named Jacobian-negation fact); local refs checked (absent → n/a);
nLab/Stacks/nCatLab/MathOverflow/arXiv each checked with reasons; ChatGPT MCP recorded n/a (down) with
the gap covered by the breadth of the other channels + direct mathlib-source reads.

### Literature summary (Phase 3)

Concept identified as: the **negation-of-multiplier identity `[−n]P = −[n]P`**, realised on the explicit
**division-polynomial Jacobian-coordinate triple** `(φₙ : ωₙ : ψₙ)`. Equivalently the conjunction:
`ψ` odd (`ψ₋ₙ = −ψₙ`), `φ` even (`φ₋ₙ = φₙ`), `ω₋ₙ = ωₙ` (general-Weierstrass: `ω₋ₙ = −negY(…)`), and the
Jacobian negation rule `−(X:Y:Z) = (X : −Y−a₁X−a₃Z³ : Z)`. The `(−1) •` in the Lean statement is the
projective rescaling that reconciles "negate the index" with "apply Jacobian neg" (forced by ψ being odd).
Sources agree on the standard form: **yes** — Silverman AEC §III.2/§III.4 (negation, division polynomials),
Washington *Elliptic Curves* §3.2, MIT 18.783 L6, Wikipedia. The negative-index convention `Ψ₋ₙ := −Ψₙ` is
universal.
Most general standard form: the identities `φ₋ₙ=φₙ`, `ψ₋ₙ=−ψₙ`, `ω₋ₙ=ωₙ` and the Jacobian-neg rule are
**integral polynomial identities over `ℤ[a₁..a₆,x,y]`** — valid for any Weierstrass curve over any
commutative ring. The project already realises exactly this maximal (universal) generality.
Generality dimensions where the literature varies:
  - base: short Weierstrass `y²=x³+Ax+B` (textbook) vs general Weierstrass `a₁…a₆` (mathlib + project, strictly more general; the `negY` twist `−Y−a₁X−a₃Z³` appears only in the general model).
  - coefficient ring: fixed field (textbook) up to the universal `ℤ[a₁..a₆,x,y]` (project — most general).
  - index: always `ℤ`; the negative-index extension is the natural home and admits no further generalisation.
Disagreement with the literature: **none**. The Lean form is the universal/most-general instance of the
textbook fact, phrased on the Jacobian representative.

---

## Generality analysis — `smulField_neg`

Literature-standard form (Phase 3): `[−n]P = −[n]P` on the `(φ:ω:ψ)` triple, integral coefficients in
`ℤ[a₁..a₆,x,y]`, general Weierstrass model, all `n : ℤ`.

| # | Parameter / hypothesis | Current Lean form                          | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | base ring / curve      | universal field `Frac(ℤ[a₁..a₆,X,Y]/⟨W⟩)` (`curveField`) | universal ring `ℤ[a₁..a₆,x,y]` | NO (already maximal) | Universal = most general; any ring/field-curve instance is a specialisation via `ringEval`/`map`. The byte-identical ring form is the sibling `smulRing_neg` (L490); the field form is the one used in the `addXYZ_smulField` field computation. |
| 2 | curve model            | general Weierstrass (`a₁…a₆`)              | general Weierstrass               | NO (already maximal) | Uses full `a₁..a₆` (the `negY` twist is essential), not the short form. |
| 3 | multiplier `n`         | `n : ℤ` (all integers)                     | `n ∈ ℤ`                          | NO                  | `ℤ` is the natural/only home for the negative-index identity. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (universal field; the byte-identical ring form
`smulRing_neg` is the universal-ring statement, the most general coefficient setting; specialisation to
any base field/curve is the downstream `ringEval`-transported form).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Note |
|----|-----------------------------------------------------------------------------------------------------|----------|------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                  | no       | no bundled hypotheses; `Universal.Field`/`curve` are fixed objects |
|  2 | sequences/metric → filters/topology?                                                                 | no       | purely algebraic identity in a field; no limit content |
|  3 | construct an object → universal-property class?                                                      | no       | `smulField` is already *the* universal construction; this is a property of it, and it already uses mathlib's "prove in the universal ring, specialise by a ring hom" idiom (via `comp_smul`/`map_neg`) |
|  4 | set-with-closure-predicate → bundled substructure?                                                   | no       | no subobject involved |
|  5 | field/metric-specific → modules/(semi)ring?                                                          | no       | the parity primitives (`ψ_neg`, `φ_neg`, `ω_neg_eq_neg_negY`, `Jacobian.neg_smul`/`comp_smul`/`map_neg`) all hold over any comm. ring; the ring form is already exposed as `smulRing_neg` |
|  6 | 1-categorical → higher-categorical?                                                                  | no       | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                                       | no       | index is `ℤ` = the multiplication-by-`n` endomorphism ring; intrinsic, not an incidental scalar |

Modern idiom available: **no**. The statement already follows mathlib's established universal-curve idiom
(it is literally proved *by* `Jacobian.comp_smul` + `Jacobian.map_neg`, the functoriality lemmas mathlib
provides for exactly this purpose). One-line reason: it is already the contemporary universal-curve form;
there is no cleaner mathlib idiom. The decl is maximally general but **not standalone-mathlib-shaped**
(see Phase 5/6): its subject `smulField` (and the `ω` inside it) is project-only apparatus.

---

## Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.smulField_neg`

Searched the project's pinned mathlib at `.lake/packages/mathlib/Mathlib/` (this project *forks* the
relevant files, so the upstream files are the authoritative check).

```
[A] Lean-Finder       "negation of n•P on division-polynomial triple", "smulField negation"   no hits (no `smulField`/`Universal.Field` notion in mathlib)
[B] Loogle            `smulField (-_) = _ • neg _ _`-shaped; `?f (-_) = _ • neg _ (?f _)`        no hits — `smulField` / `Universal.Jacobian` do not exist in mathlib
[C] LeanSearch        "negative multiple of point equals negation of multiple, division polynomial Jacobian triple"  no direct hit; nearest is Jacobian `neg` fixing X / negating Y, not the `n•P` triple
[D] Grep mathlib src  `smulField`, `smulRing`, `smulPoly`, `polyToField`, `namespace Universal` (in EllipticCurve/), `smulField_neg`, `zsmul_eq`, `def ω`/omega   ALL zero hits (the two `Universal*` files found are `UniversallyOpen`/`UniversalEnveloping`, unrelated)
[E] Name pattern      `smulField_neg`, `smul*_neg`, `Universal.Jacobian.*` in `.lake/.../Mathlib`   zero hits
```

Searched for both:
  - the user's current form (`smulField (-n) = (-1) • neg curveField (smulField n)`) — **absent** (no `smulField`).
  - the literature-standard form. Mathlib **does** have several of the *building blocks* the proof rests on:
    * `WeierstrassCurve.Jacobian.neg` (`Jacobian/Point.lean:91`) — the Jacobian-representative negation `![P x, W.negY P, P z]`. **In mathlib.**
    * `WeierstrassCurve.Jacobian.neg_smul` (`Jacobian/Point.lean:103`): `W'.neg (u • P) = u • W'.neg P`. **In mathlib** (the scaling-compatibility of `neg`).
    * `WeierstrassCurve.Jacobian.comp_smul` (`Jacobian/Basic.lean:147`): `f ∘ (u • P) = f u • (f ∘ P)`. **In mathlib** (used verbatim in the proof).
    * `WeierstrassCurve.Jacobian.map_neg` (`Jacobian/…`): functoriality of `neg` along a ring hom. **In mathlib** (used verbatim in the proof, as `← Jacobian.map_neg`).
    * `WeierstrassCurve.ψ_neg` (`ψ(-n) = -ψ n`, `DivisionPolynomial/Basic.lean:427`) and `φ_neg` (`φ(-n) = φ n`, L478). **In mathlib** (via `normEDS_neg`, `EllipticDivisibilitySequence.lean`).

Two decisive **gaps** (same as the sibling `dblXYZ_smulField`/`smulY_neg` reports):
  - **`ω` is an explicit mathlib TODO** — `DivisionPolynomial/Basic.lean` Main-definitions block lists
    `* TODO: the bivariate polynomials ωₙ.` Mathlib has **no `ω`**. The project supplies it
    (`DivisionPolynomialOmega.lean`). `smulField`'s **second coordinate is `ω`**, and the proof's crux step
    `smulPoly_neg` rests on `ω_neg_eq_neg_negY` (`ω(-n) = -negY curvePoly (smulPoly n)`) — a statement about
    `ω` that **cannot even be written in mathlib**.
  - **No multiplication-by-`n` closed form.** Mathlib's Jacobian group action is `zsmul := zsmulRec`
    (`Jacobian/Point.lean:590`) — purely recursive, with **no** `n • P = (φₙ:ωₙ:ψₙ)`. There is also no
    `WeierstrassCurve.Universal` namespace (`Universal.Field`/`polyToField`/`smulField` are all project-local).

Concluded: **not in mathlib** (all five methods exhausted, incl. the literature-standard universal form).
Mathlib has the *Jacobian-negation + division-polynomial-parity building blocks* (`Jacobian.neg`,
`neg_smul`, `comp_smul`, `map_neg`, `ψ_neg`, `φ_neg`), but is missing **`ω`**, the **`Universal.*`
scaffolding**, and the **multiplication formula** of which this lemma is a bookkeeping step — so the
statement itself is **unexpressible in mathlib's current vocabulary**.

---

## Call sites — `WeierstrassCurve.Universal.Jacobian.smulField_neg`

Internal use count: **1** (within NagellLutz, excluding the declaring line 493).
External-to-file callers: 0 distinct files in NagellLutz (the single use is in the same file).

| Caller file:line   | Usage pattern (one-line excerpt)                                                          |
|--------------------|-------------------------------------------------------------------------------------------|
| ZSMul.lean:509     | `rw [← jac_one_smul (smulField m), smulField_neg, neg_add_cancel, addXYZ_smul, …]` — discharges the `n = −m` case of `addXYZ_smulField` (where `(φₘ:ωₘ:ψₘ)` and its negation are added, giving the identity `O`) |

Inline-derivation grep (re-derived elsewhere without `smulField_neg`?):
  - In NagellLutz: no — the only consumer routes through this lemma; the byte-identical ring sibling
    `smulRing_neg` (L490) is used independently at ZSMul.lean:621 (inside `evalEval_ψ_eq_zero_of_zsmul_eq_zero`),
    so the *negation identity* is genuinely used in two coordinate forms, but each via its own lemma.
  - Cross-project duplicate (NOT a call site — an independent copy): `HasseWeil/Auxiliary/DivisionPolynomial.lean:566`
    holds a `private` identical `smulField_neg`, used there at L583 (the analogous `addXYZ_smulField` `n=−m` case).
    This is the duplicated General*/PID* fork, not a consumer of the NagellLutz lemma.

Call-site signal: K = 1 internal use, no inline re-derivation. On its own K=1 leans "could be inlined",
**but** the def-first / development context overrides (per Phase 6.0.1): it is one bookkeeping step of a
coherent universal-case proof of a genuinely-new, mathlib-TODO result (`ω` + the multiplication formula).
The right upstreaming grain is the *whole development*, not this lemma alone. Notably HasseWeil already
marks its copy `private` — independent corroboration that this is internal scaffolding, not public API.

---

## Composition check (Phase 6)

Can `smulField_neg` be derived from mathlib in ≤3 chained calls? **No — and the question is ill-posed.**

Strictly, the composition question cannot even be *posed* in mathlib: to state the goal you must first
*name* `smulField`, `neg curveField` over `Universal.Field`, `polyToField`, and — critically — the **`ω`
division polynomial**, **none of which exist in mathlib**. There is no mathlib object to compose *into*.

Re-reading the *proof* as a composition over the building blocks mathlib does have:

Attempt 1 (the actual proof): `by simp_rw [smulField, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl`
  - Mathlib decls used: `WeierstrassCurve.Jacobian.comp_smul`, `WeierstrassCurve.Jacobian.map_neg`,
    `map_neg`, `map_one` (all in mathlib).
  - **Project-only, irreducible:** `smulPoly_neg` (ZSMul.lean:487) — the polynomial-ring crux — which in turn
    rests on `ω_neg_eq_neg_negY` (ZSMul.lean:480), a statement **about `ω`**. With no `ω` in mathlib, this
    step has no mathlib counterpart. Also project-only: the `smulField`/`smulPoly`/`curveField`/`polyToField`
    unfolding.
  - Result: **fails as a mathlib composition.** The mathlib lemmas (`comp_smul`, `map_neg`) only do the
    *transport* of an already-established polynomial identity through `polyToField`; the identity itself
    (`smulPoly_neg`, hence `ω_neg_eq_neg_negY`) is irreducibly about `ω` and is not in mathlib.

Attempt 2 (build the parity content from `ψ`/`φ` alone, no `ω`): fails — `ω` is the second coordinate of
`smulField` and the whole point of the lemma is the full triple. There is no `ω`-free path.

Conclusion: **NOT-COMPOSABLE.** Unlike the affine `smulX_neg` (whose subject `φₙ/ψₙ²` needs only mathlib's
`φ_neg`/`ψ_neg`/`neg_sq` and is therefore a genuine ≤3-call composition), `smulField_neg`'s subject contains
`ω` (mathlib-absent) and the entire `Universal.*` apparatus, so the composition route is blocked and the
statement is unexpressible upstream. This matches the sibling `smulY_neg` (BORDERLINE), not `smulX_neg`
(NO-composable).

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.smulField_neg`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the identity `[−n]P = −[n]P` on the `(φ:ω:ψ)` triple — equivalently
  `ψ` odd / `φ` even / `ω₋ₙ=ωₙ` + Jacobian-neg `−(X:Y:Z)=(X:−Y:Z)` — is textbook (Silverman §III.2/4;
  Washington §3.2; MIT 18.783; the `Ψ₋ₙ:=−Ψₙ` convention is universal). Maximally-general form already used.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (universal field; byte-identical universal-ring
  sibling `smulRing_neg`; general Weierstrass; `n:ℤ`); no weakenings; no modern-idiom flip (it already *is*
  the universal-curve idiom, proved via mathlib's own `comp_smul`/`map_neg` functoriality).
- Mathlib search (Phase 5): **not in mathlib**, and the statement is **unexpressible upstream** — `ω` is an
  explicit mathlib **TODO**, there is **no** multiplication-by-`n` closed form (`zsmul := zsmulRec`), and no
  `WeierstrassCurve.Universal` namespace. The *building blocks* `Jacobian.neg`, `Jacobian.neg_smul`,
  `Jacobian.comp_smul`, `Jacobian.map_neg`, `ψ_neg`, `φ_neg` **are** in mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the crux `smulPoly_neg` rests on `ω_neg_eq_neg_negY`
  (about `ω`, mathlib-absent); the mathlib lemmas only transport an already-proved identity through
  `polyToField`. There is no mathlib object to compose into.

**Rationale.**
The mathematics is squarely mathlib-worthy *as a development*: the multiplication-by-`n` formula in
division polynomials, `n • P = (φₙ : ωₙ : ψₙ)`, is the textbook (Silverman) result, and mathlib *already
advertises the gap* — `DivisionPolynomial/Basic.lean` lists `ωₙ` as a TODO and `Jacobian/Point.lean`
defines the group action by bare recursion (`zsmulRec`) with no closed form. The NagellLutz development
(`DivisionPolynomialOmega.lean` + `Universal.lean` + `ZSMul.lean`) fills exactly that gap, culminating in
`zsmul_eq_smulEval`. `smulField_neg` is the Jacobian-triple form of the elementary `[−n]P = −[n]P` step
inside that development — the companion to the affine `smulX_neg`/`smulY_neg`.

It is **not** `NO-composable-from-mathlib` (the sibling verdict for the affine `smulX_neg`): that bucket
fired for `smulX_neg` precisely because `smulX = φₙ/ψₙ²` needs only `φ_neg`/`ψ_neg`/`neg_sq`, all in mathlib,
making it a true ≤3-call composition over an expressible (modulo `polyToField`) goal. Here the subject
`smulField` contains **`ω`**, which is not in mathlib at all — so the goal is *unexpressible* upstream and
there is nothing to compose into. It is **not** `NO-mathlib-has-it` (mathlib has neither the lemma nor the
`smulField`/`ω` apparatus). It is **not** `YES-add-as-is`: shipping this single universal-field bookkeeping
helper in isolation is impossible (no `smulField`/`ω` to state it) and pointless (its content is the
`(−1)•`-rescaled Jacobian-neg of an `ω`-parity fact, meaningful only inside the multiplication formula). It
is **not** `YES-but-generalise-first` in the generality sense (Phase 4b found it maximally general).

The genuine open question is one of **packaging/grain for the upstream development**, which is a
maintainer/human call — exactly what BORDERLINE is for. Whether this `(−1)•neg`-bookkeeping identity should
surface as a *public* mathlib lemma, stay `private` (as HasseWeil already marks its copy), or be absorbed
into a more general `neg`-of-`smulEval` result depends on how the whole `Universal.*` + `ω` API is
structured for mathlib — a decision identical to the one reached for the sibling `smulY_neg`.

**Numbered questions (≤5):**
1. Is the upstream target the **full** `ω` + `Universal` + multiplication-by-`n` development (closing the
   `ωₙ` TODO and giving Jacobian `Point` a closed-form `zsmul`), shipped as one PR? (If yes, `smulField_neg`
   travels as an internal step, not a standalone lemma — likely `private`, as HasseWeil already has it.)
2. In that PR, should the negation identity be exposed publicly **at all**, and if so in which single
   canonical form — the universal-**ring** `smulRing_neg`, the universal-**field** `smulField_neg`, or a
   downstream specialised `neg (smulEval …)` statement? (Three byte-near-identical copies exist; mathlib
   wants one.)
3. Should it instead be stated more idiomatically as `smulPoly (−n) ≈ neg curvePoly (smulPoly n)` using
   mathlib's Jacobian point-equivalence `≈` (absorbing the `(−1) •` unit via `neg_smul_equiv`), rather than
   the explicit `(−1) • …` equation — i.e. is the `≈`-form the public API mathlib would prefer?
4. Independently of mathlib: consolidate the NagellLutz vs HasseWeil duplicate
   `smulPoly_neg`/`smulRing_neg`/`smulField_neg` (one is `private`, one is not) into a single shared copy on
   AINTLIB `main`? (This is an AINTLIB dedup decision, not a mathlib action — recommended regardless.)

**Next action:** user/maintainer answers the questions; re-run `/mathlibable` if the packaging decision
changes the grain. Default recommendation absent an answer: **keep `smulField_neg` as a local step** of the
multiplication-by-`n` development (the companion to `smulX_neg`/`smulY_neg`); it only ever reaches mathlib
*as part of upstreaming the whole `ω` + universal-curve + multiplication-formula apparatus*, at which point
it is an internal (likely `private`) bookkeeping lemma — never a standalone contribution. First consolidate
the NagellLutz/HasseWeil duplicate on AINTLIB `main`.

---

## Next step

BORDERLINE — surface the packaging questions. The math (`[−n]P=−[n]P` on the `(φ:ω:ψ)` triple) is textbook
and the *enclosing* development is genuinely mathlib-grade (it closes the `ωₙ` TODO and gives Jacobian points
a closed-form `zsmul`), but `smulField_neg` is an internal `(−1)•neg`-bookkeeping step whose subject (`ω`,
`smulField`, `Universal.Field`) is unexpressible in mathlib today. Whether it surfaces publicly, stays
`private`, or is absorbed is a maintainer call tied to how the whole `Universal.*`+`ω` API lands. Default:
keep it local; upstream only with the full development. Orthogonal AINTLIB cleanup: dedup the
NagellLutz/HasseWeil copies.
