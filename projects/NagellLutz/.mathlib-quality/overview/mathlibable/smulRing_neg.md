# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.smulRing_neg`

> **TL;DR — `BORDERLINE-needs-human`.** This is the *negation-step* sibling of
> `dblXYZ_smulRing` (already assessed `BORDERLINE`), in the identical `smulRing` /
> `Universal.Ring` family and with the identical single-consumer internal-reduction-step
> role. It is genuinely absent from mathlib, *not statable* in current mathlib (needs the
> project's unupstreamed `Universal.Ring`, `ω`, and the `smulRing` packaging), and *not* a
> mathlib-only composition (its content is the project lemma `smulPoly_neg`; mathlib supplies
> only the `comp_smul` / `map_neg` transfer wrappers). Its disposition is a packaging decision
> that travels with the `zsmul_eq_smulEval` upstream package — a human call, not a mechanical one.

---

### Baseline (Phase 0)
- lake build:               ✓ clean (`lake build LutzNagell.ZSMul` → "Build completed successfully (1958 jobs)"; the `ring_nf` "Try this" lines are info suggestions in `EllipticDivisibilitySequence.lean`, not errors)
- decl `WeierstrassCurve.Universal.Jacobian.smulRing_neg`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:490`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Expresses `n • P` in Jacobian coordinates via division polynomials `(φₙ : ωₙ : ψₙ)`, culminating in `WeierstrassCurve.zsmul_eq_smulEval`.

**Qualified-name verification.** File opens `namespace WeierstrassCurve` (line 76) → `namespace Universal` (line 86) → `namespace Jacobian` (line 395, closed at 544). The decl `smulRing_neg` sits inside all three, so the parsed name **`WeierstrassCurve.Universal.Jacobian.smulRing_neg` is CONFIRMED**.

---

### Statement (Phase 1)

```lean
lemma smulRing_neg : smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl
```

`smulRing_neg` is a **lemma** stating the following.

Let `Universal.Ring = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y] / ⟨P⟩` be the universal Weierstrass coordinate ring
(`AdjoinRoot curve.polynomial`), let `curveRing` be the universal curve base-changed to that ring,
and for `n : ℤ` let `smulRing n = (φₙ, ωₙ, ψₙ) ∈ (Fin 3 → Universal.Ring)` be the Jacobian-coordinate
triple of `[n]·(X,Y)` formed from the division polynomials. Then the triple for `-n` is obtained from
the triple for `n` by applying the curve's Jacobian-representative negation `neg` (which fixes the
`x`- and `z`-coordinates and replaces the `y`-coordinate by `negY`) and scaling by the Jacobian unit
`-1`:

$$ \mathrm{smulRing}(-n) \;=\; (-1)\cdot \big(\mathrm{neg}_{\,\mathrm{curveRing}}(\mathrm{smulRing}\,n)\big). $$

Mathematically this packages the three classical component rules — `ψ₋ₙ = -ψₙ`, `φ₋ₙ = φₙ`,
`ω₋ₙ = -ωₙ` — into a single vector identity that says *"negating the index `n` corresponds to the
geometric point-negation of the representing Jacobian triple"*, in the universal coordinate ring.

Variables / typeclasses involved (Lean side):
- `n : ℤ` (implicit, from `variable {m n : ℤ}` at line 97) — the multiplier.
- (fixed, not parameters of the lemma) `Universal.Ring`, `curveRing`, `curve`, `Poly` — all project-global.

Hypotheses (Lean side): **none**.

Conclusion (math): the Jacobian-coordinate triple of `[-n]·(X,Y)` over the universal ring equals `(-1)`-scaled `Jacobian.neg` of the triple of `[n]·(X,Y)`.

Conclusion (Lean): `smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n)`, an equation in `Fin 3 → Universal.Ring`.

**Supporting definitions (all project-local):**
- `smulPoly n := ![curve.φ n, curve.ω n, curve.ψ n] : Fin 3 → Poly` (ZSMul.lean:414) — the triple in the polynomial ring `Poly = ℤ[A..][X][Y]`.
- `smulRing n := AdjoinRoot.mk curve.polynomial ∘ smulPoly n : Fin 3 → Universal.Ring` (ZSMul.lean:416).
- `curveRing := curve.baseChange Universal.Ring` (Universal.lean:170); `curve` is the universal Weierstrass curve over `Universal.Ring`'s base.
- `neg` here is **`WeierstrassCurve.Jacobian.neg`** (opened at ZSMul.lean:399; mathlib `Jacobian/Point.lean:91`: `neg (P : Fin 3 → R) := ![P x, W'.negY P, P z]`) — representative-level negation of a Jacobian triple.
- `•` is **`WeierstrassCurve.Jacobian`'s scoped `SMul R (Fin 3 → R)`** (mathlib `Jacobian/Basic.lean:137`: `u • ![x,y,z] = ![u²x, u³y, u z]`).
- Proof inputs: `smulPoly_neg` (the *Poly*-level twin, ZSMul.lean:487), `Jacobian.comp_smul` (Basic.lean:147), `Jacobian.map_neg` (Point.lean:617), and `map_neg`/`map_one` for the ring hom `AdjoinRoot.mk`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a hypothesis-free helper **lemma** (not a `def`/`class`/`structure`, not a `## Main results` entry, not named after a person); it is a one-consumer internal reduction step pushing `smulPoly_neg` through the ring hom `AdjoinRoot.mk`.

(Literature width run EXHAUSTIVE regardless. The named citable end-product of the whole development is `WeierstrassCurve.zsmul_eq_smulEval` / the multiplication formula `[n]P = (φₙ:ωₙ:ψₙ)`; `smulRing_neg` is the negation reduction step toward it.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (the `simp_rw [...]; rfl`). But **kind is lemma, not def** → the one-liner def signal does not apply (one-line *proofs* are normal and carry no negative weight). Section skipped; recorded as a one-line note.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomials elliptic curve negation [-n]P psi_{-n}=-psi_n omega phi Jacobian coordinates"     | yes  | `ψ₋ₙ = -ψₙ`; `nP = [φₙψₙ : ωₙ : ψₙ³]` | Wikipedia "Division polynomials"; MIT 18.783 Lec 5 (Sutherland); arXiv 1103.4560. The *component* negation rule + multiplication formula are standard. |
|  2 | WebSearch (general / multn form) | "elliptic curve multiplication by n formula division polynomials phi_n psi_n omega_n projective Silverman" | yes  | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; proj `[φₙψₙ:ωₙ:ψₙ³]` | Silverman *AEC* Ex. 3.7; same projective triple. The named object is the **multiplication formula**, not this neg-packaging. |
|  3 | WebSearch (named-after / aliases)| "elliptic divisibility sequence / division polynomial omega_n companion psi_{n-1} psi_{n+2}"            | yes  | `ωₘ = (ψₘ₋₁²ψₘ₊₂ − ψₘ₋₂ψₘ₊₁²)/(4y)`; `φ₋ₙ=φₙ`, `ω₋ₙ=−ωₙ` | Components & their parities are standard (Ward EDS; Silverman). No source packages neg as `(-1)•Jacobian.neg(triple)` over a coordinate *ring*. |
|  4 | ChatGPT MCP                      | (MCP down per environment note) — fallback: parity facts cross-checked across #1–#3 + nLab/Stacks below | n/a  | n/a                              | MCP unavailable; substituted extra WebSearch generality levels + nLab + Stacks per protocol fallback. Parities `ψ₋ₙ=−ψₙ, φ₋ₙ=φₙ, ω₋ₙ=−ωₙ` agree across all channels. |
|  5 | Local references                 | `ls .mathlib-quality/references/`                                                                       | n/a  | (directory absent)               | `projects/NagellLutz/.mathlib-quality/` has only `overview/`; no `references/` dir. Recorded n/a. |
|  6 | nLab                             | "elliptic curve division polynomial" / "elliptic divisibility sequence"                                 | n/a  | no dedicated page                | nLab has no division-polynomial / EDS page; concept is classical NT, not categorical. n/a with reason. |
|  7 | nCatLab (categorical)            | —                                                                                                       | n/a  | —                                | Not a categorical concept. n/a. |
|  8 | Stacks Project (alg geom)        | "division polynomial" / "Weierstrass" multiplication-by-n                                                | n/a  | not present                      | Stacks treats Weierstrass equations but not division-polynomial multiplication formulas / EDS. n/a with reason. |
|  9 | MathOverflow / Math.SE           | "division polynomial negative index parity", "omega_n sign [-n]P"                                       | yes  | confirms `ψ₋ₙ=−ψₙ`, `ω₋ₙ=−ωₙ`, `φ₋ₙ=φₙ` | Multiple Q&A confirm the *component* parities; none state the universal-ring vector neg-identity. |
| 10 | recent arXiv (last 5 years)      | "elliptic nets / elliptic divisibility sequence valuation division polynomial" (2102.07573, 2512.09601) | yes  | EDS recurrences & `normEDS` parity | Confirms `normEDS(−n) = −normEDS(n)` (= mathlib `normEDS_neg`); still component-level, not the triple packaging. |

### Literature summary (Phase 3)

Concept identified as: the **negative-index (parity) rules for division polynomials** — `ψ₋ₙ = -ψₙ`, `φ₋ₙ = φₙ`, `ω₋ₙ = -ωₙ` — together with the **multiplication-by-`n` formula** `[n]P = (φₙ : ωₙ : ψₙ³)` in projective/Jacobian coordinates (Silverman *AEC* Ex. 3.7; Sutherland MIT 18.783 Lec 5; Wikipedia "Division polynomials"; Ward's elliptic divisibility sequences).
Sources agree on the standard form: **yes** for the *components* (`ψ₋ₙ=−ψₙ` etc.) and for the multiplication formula. **No source** states `smulRing_neg`'s actual content — the **vector identity** `smulRing(−n) = (−1)•Jacobian.neg(smulRing n)` over a *universal coordinate ring*. That packaging (index-negation ↔ Jacobian point-negation of the representing triple) is a Lean-formalisation convenience, not a textbook statement.
Most general standard form: the component parities hold over any base for the `normEDS`-defined `ψ`, with `φ`, `ω` defined from `ψ`; mathlib already has these as `ψ_neg`, `φ_neg`, `Ψ_neg`, `preΨ_neg`, `normEDS_neg`, `preNormEDS_neg`.
Generality dimensions where the literature varies:
  - base ring: stated over fields classically, but the parities are ring-level identities (mathlib has them over `CommRing`); `smulRing_neg`'s base is fixed to the *initial/universal* ring `Universal.Ring`, which is the maximal-generality anchor for its role.
  - object: literature states *components*; the project states a *triple-vector* identity — a strictly more packaged form with no literature antecedent.
Disagreement with the literature: **none** — `smulRing_neg` is a *true* consequence of the standard parities; the literature simply does not name the packaged vector form.

---

### Generality analysis — `WeierstrassCurve.Universal.Jacobian.smulRing_neg`

Literature-standard form (from Phase 3): the component parities `ψ₋ₙ=−ψₙ`, `φ₋ₙ=φₙ`, `ω₋ₙ=−ωₙ` (mathlib has them); the *packaged* form has no literature standard.

| # | Parameter / hypothesis     | Current Lean form                  | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------|------------------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | base ring `Universal.Ring` | the universal coordinate ring `AdjoinRoot curve.polynomial` | any `CommRing` for the components | NO (for its role)   | The whole point of `smulRing` is to be the **universal/initial** instance; a "more general" base is the *specialized* curve `curveRing W` over an arbitrary `W`, obtained by *specializing* this universal identity (via `ringEval`), not by weakening it. The universal form is the strongest. |
| 2 | `n : ℤ`                    | arbitrary integer                  | arbitrary integer                 | NO                  | Already maximal. |
| 3 | curve `curveRing`          | the universal curve over `Universal.Ring` | arbitrary `WeierstrassCurve` | NO (for its role)   | Same as #1 — specializing `curve` to a concrete `W` is *downstream* (`smulRing_neg → smulField/smulEval → zsmul_eq_smulEval`), not a weakening of this lemma. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for its universal/initial role).
Number of weakening opportunities found: **0**. The genuinely "more general" object is not a weaker `smulRing_neg`; it is the *specialized* component facts mathlib already owns (`ψ_neg`/`φ_neg`/`ω`-analogue), of which this is the universal-ring vector packaging. There is no `YES-but-generalise-first` weakening to propose.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses/instances?                                                   | no       | —                      | Hypothesis-free already; nothing to classify. |
|  2 | sequences/metric → filters/topology?                                                                  | no       | —                      | Purely algebraic identity in a polynomial ring; no analysis. |
|  3 | construct an object where a universal-property class would characterise it?                           | no       | —                      | `smulRing` is already the *universal* construction; the lemma is an identity about it, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                    | no       | —                      | No substructure here. |
|  5 | vector-space/field-specific → modules/(semi)ring weakening?                                           | no       | —                      | Already over a `CommRing`; the components are already at `CommRing` generality in mathlib. |
|  6 | 1-categorical → higher/∞-categorical?                                                                 | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive group/monoid?                                             | no       | —                      | The index `n : ℤ` is intrinsic to division polynomials / EDS (negative indices are the whole subject); no generalisation. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: this is a hypothesis-free algebraic identity over a `CommRing` whose every parameter is already at (or, for the universal base, *above*) the literature generality; there is no Bourbaki-2.0 reorganisation to make.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma** (introduces no definitional equalities or typeclass-search paths). Skipped.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.smulRing_neg`

[A] Lean-Finder       "division polynomial negation triple", "smul neg division polynomial elliptic"   no hits (index unavailable here; substituted [B]/[C]/[D]/[E] per protocol)
[B] Loogle            `Jacobian.neg`-vs-`Fin 3 → _` neg-of-triple pattern; `WeierstrassCurve.ω _ (-_)`   no hit — searched mathlib src directly (D); mathlib has **no `ω`** division polynomial at all, so no triple-level neg lemma can exist
[C] LeanSearch        "negation of multiplication-by-n division polynomial Jacobian coordinates"          no hit — concept (universal `smulRing` triple) is project-local
[D] Grep mathlib src  `smulPoly` / `smulRing` / `smulField` / `smulEval` / `zsmul_point_eq` across `.lake/packages/mathlib/Mathlib/` — **0 results**; `neg.*ψ\|ψ.*neg\|neg curve` in `Jacobian/` — **0 results**; `ψ_neg`/`φ_neg`/`Ψ_neg`/`preΨ_neg`/`normEDS_neg`/`preNormEDS_neg` — **present** (the components) | mixed: components yes, the packaged triple identity no |
[E] Name pattern      `smulRing_neg`, `smulRing`, `Universal.Jacobian`, `WeierstrassCurve.ω` in mathlib  no hit (project-local); `WeierstrassCurve.ω` does **not** exist in mathlib

Searched for both:
  - the user's current form (`smulRing(-n) = (-1)•neg curveRing (smulRing n)`) → **not in mathlib**, and **not statable** in current mathlib (needs `Universal.Ring`, `ω`, `smulRing`, none of which mathlib has).
  - the literature-standard *component* form → mathlib **HAS** it: `WeierstrassCurve.ψ_neg` (`DivisionPolynomial/Basic.lean:427`), `φ_neg` (Basic.lean:478), `Ψ_neg` (Basic.lean:320), `preΨ_neg` (Basic.lean:222), and `normEDS_neg` (`NumberTheory/EllipticDivisibilitySequence.lean:318`), `preNormEDS_neg` (:206). Mathlib also has the Jacobian transfer machinery `Jacobian.neg` (Point.lean:91), `Jacobian.comp_smul` (Basic.lean:147), `Jacobian.map_neg` (Point.lean:617), `comp_fin3` (Basic.lean:130). It does **not** have `WeierstrassCurve.ω` (the y-coordinate division polynomial) nor any `smulRing`/triple packaging.

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard form).** Mathlib owns the *component* parities and the Jacobian transfer wrappers, but neither the `ω` polynomial, the `Universal.Ring`/`smulRing` packaging, nor any vector-level neg identity. The statement of `smulRing_neg` cannot even be written in current mathlib.

---

### Call sites — `WeierstrassCurve.Universal.Jacobian.smulRing_neg`

Internal use count (within NagellLutz, excluding the declaring line ZSMul.lean:490): **1**
External-to-file callers: 1 site in this project's `ZSMul.lean` (the declaring file itself, in a different lemma); plus a **verbatim duplicate** of the whole `smulRing` machinery (incl. its own `smulRing_neg` + consumer) in a *different* project, HasseWeil.

| Caller file:line                                         | Usage pattern (one-line excerpt)                                                                 |
|----------------------------------------------------------|---------------------------------------------------------------------------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:621`          | `simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.comp_smul, ← Jacobian.map_neg, curveRing_map_ringEval, map_neg, map_one]` — the **`neg` induction case** of `zsmul_eq_smulEval` |
| `projects/NagellLutz/LutzNagell/ZSMul.lean:493`          | `smulField_neg` (the *field* twin, immediately below) is proved with the **identical tactic block** — a parallel sibling, not a consumer of `smulRing_neg` |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:512` | **duplicate declaration** of `smulRing_neg`, and `:700` its duplicate consumer — confirms this is *shared scaffolding* copied between two projects, not a standalone API |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `smulRing_neg`?):
  - The **field/poly twins** `smulField_neg` (ZSMul.lean:493) and `smulPoly_neg` (ZSMul.lean:487) are the analogous statements over `Universal.Field` / `Poly`; they are siblings produced by the same proof pattern, not bypasses. No site re-derives the *ring* identity inline.

**Call-sites reading.** `smulRing_neg` has **exactly one consumer**, `zsmul_eq_smulEval` (ZSMul.lean:621, the `neg` even-odd-induction case). Per the Phase-6.0.1 table, "K = 1 internal use" leans toward NO-composable / internal-helper — except the composition is over *project* infrastructure (see Phase 6), so the lemma is a genuine internal reduction step rather than mathlib-inlinable. The HasseWeil duplicate is a copy of the same scaffolding (independent confirmation that this is shared internal plumbing for the multiplication formula, not a catalogable result).

---

### Composition check (Phase 6)

Can `smulRing_neg` be derived from **mathlib** in ≤3 chained calls? **No.**

**Attempt 1 — push the Poly twin through the ring hom (what the proof actually does):**
`simp_rw [smulRing, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl`.
- Mathlib decls used: `Jacobian.comp_smul` (Basic.lean:147), `Jacobian.map_neg` (Point.lean:617), `map_neg`/`map_one` (the `AdjoinRoot.mk` ring hom).
- **Load-bearing input is `smulPoly_neg` — a PROJECT lemma (ZSMul.lean:487), not mathlib.** The mathlib calls only do the *Poly → Universal.Ring* transfer (`AdjoinRoot.mk` is a ring hom; negation/smul/`Jacobian.neg` commute with it). They cannot produce the equation from mathlib alone.
- And `smulPoly_neg` itself rests on `ω_neg_eq_neg_negY` (ZSMul.lean:480, a *project* lemma about the project's `ω`) plus the parities — over project-local `curvePoly`/`smulPoly`, using the project's `ω`, which **mathlib does not have**.
- Result: **fails as a mathlib-only composition** — it is a composition over *project* infrastructure.

**Attempt 2 — direct from mathlib's component parities (`ψ_neg`, `φ_neg`) + `Jacobian.neg`:**
Would require (a) the *missing* `ω_neg : ω(-n) = -negY(...)` fact, but mathlib has **no `ω`** at all; and (b) re-assembling the three component parities into the vector `(-1)•Jacobian.neg(...)` form, which still needs the project's `smulRing`/`Universal.Ring`. Not ≤3 calls, and not statable in mathlib.

Conclusion: **NOT COMPOSABLE FROM MATHLIB.** The only short derivation transfers the *project* lemma `smulPoly_neg` across mathlib's ring-hom-commutation wrappers; mathlib's primitives supply the transfer but not the mathematical content, and the statement itself needs the project's unupstreamed `Universal.Ring` / `ω` / `smulRing`.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.smulRing_neg`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- **Not in mathlib, and not even statable in mathlib (Phase 5).** mathlib has the *component* parities `ψ_neg`/`φ_neg`/`Ψ_neg`/`preΨ_neg`/`normEDS_neg` and the Jacobian transfer wrappers `Jacobian.neg`/`comp_smul`/`map_neg`, but **no `ω`** (project-defined, `DivisionPolynomialOmega.lean:74`), **no `Universal.Ring`/`curveRing`**, **no `smulRing`**, and **no vector-level neg identity**. This rules out `NO-mathlib-has-it` *and* means the statement cannot be written in current mathlib.
- **Not composable from mathlib (Phase 6).** The one short proof transfers the *project* lemma `smulPoly_neg` across `Jacobian.comp_smul` + `Jacobian.map_neg` + `map_neg`/`map_one`; mathlib's calls do only the ring-hom-commutation move, and the mathematical content lives in the project's `smulPoly_neg`/`ω_neg_eq_neg_negY` (which need the project's `ω`). This rules out `NO-composable-from-mathlib`.
- **Not a standalone YES, but also not a clean YES-but-generalise (Phases 1–4, call sites).** It is a **single-purpose internal reduction step** (1 consumer, `zsmul_eq_smulEval` at line 621, the `neg` induction case) inside this file's proof of the citable end-product `zsmul_eq_smulEval`. The literature (Silverman *AEC* Ex. 3.7; Sutherland 18.783; Wikipedia "Division polynomials") names the *multiplication formula* `[n]P = (φₙ:ωₙ:ψₙ³)` and the *component parities* `ψ₋ₙ=−ψₙ`, **not** this universal-ring negation-triple identity. Its generality is already maximal-for-its-role (universal/initial — Phase 4b found 0 weakenings), and Phase 4c found no modern-idiom move, so there is no generalise-first action.

**Rationale (why BORDERLINE, not one of the decisive buckets):**

`smulRing_neg` states real, classical mathematics — the negation step of the division-polynomial multiplication formula (`[-n]P` from `[n]P` via point-negation), over the universal coordinate ring. It is the exact negation-step sibling of `dblXYZ_smulRing` (doubling step), which was independently assessed `BORDERLINE-needs-human` in this same `/overview`; the two share infrastructure, role, and disposition. As with that sibling, its **disposition is a packaging decision a human must make**, not a mechanical one, because three things are simultaneously true:

1. It is genuinely absent from mathlib (so not `NO-mathlib-has-it`), and its *statement* depends on unupstreamed project infrastructure — `Universal.curve`/`Universal.Ring`, the y-coordinate division polynomial `ω`, and the `smulRing` packaging. **Whether this lemma can go to mathlib at all is contingent on first upstreaming that infrastructure** (`Universal.curve` is the `YES-add-as-is` object in `curve.md`; `ω` is a real missing mathlib definition; `smulRing`/`curveRing` are `NO-composable` plumbing). That is a multi-decl package decision, not a per-lemma call.
2. It is not composable from mathlib (so not `NO-composable-from-mathlib`): the short proof's content is the *project* lemma `smulPoly_neg`, and mathlib supplies only the ring-hom-commutation wrappers (`comp_smul`, `map_neg`).
3. It is not a standalone result mathlib would catalog on its own (so not a clean `YES-add-as-is`): it is one of a **family of internal intermediates** — `smulPoly_neg`, `smulField_neg`, **`smulRing_neg`**, `dblXYZ_smulRing`, `addXYZ_smulRing`, etc. — whose sole purpose is to assemble `zsmul_eq_smulEval`. When this development is upstreamed, a maintainer must decide whether such universal-ring intermediates ship as `private`/internal lemmas, get inlined, or are kept as a small public API — exactly the judgment the BORDERLINE bucket is for. (The verbatim HasseWeil duplicate underlines that today it is *shared internal scaffolding*, not a catalogued result.)

In short: the lemma **travels to mathlib with the `zsmul_eq_smulEval` development**, but only as part of that package and only after the missing infrastructure (`Universal.curve`, `ω`) lands; as a *standalone* decl assessed in isolation it is neither "add as-is" nor a NO.

**Numbered questions (≤5) for the human:**
1. Is the AINTLIB plan to upstream the whole multiplication-formula development (`Universal.curve` + `ω` + the `smulPoly`/`smulRing`/`smulField` machinery + `zsmul_eq_smulEval`) to mathlib? (If **no**, `smulRing_neg` stays project-local with its dependencies and this is settled — no mathlib action.)
2. If yes: should the universal-ring intermediates like `smulRing_neg` ship as **`private`/internal** lemmas (it has 1 consumer and is a ring-hom transfer of `smulPoly_neg`), be **inlined** into `zsmul_eq_smulEval`, or be kept as a **small public API**?
3. Prerequisite gate: do you agree `smulRing_neg` cannot be assessed independently of first landing `WeierstrassCurve.ω` (genuinely missing from mathlib) and `WeierstrassCurve.Universal.curve` (the `YES-add-as-is` object)?
4. Packaging grain: should `smulRing_neg` ship in **one PR** together with its twins `smulPoly_neg`/`smulField_neg` and the `dblXYZ_smulRing`/`addXYZ_smulRing` family (all the same `smulRing` reduction-step layer), rather than as isolated lemmas?
5. De-duplication: the identical lemma is duplicated in HasseWeil (`Auxiliary/DivisionPolynomial.lean:512`). Should the upstream package be the single source both projects then import (an AINTLIB-internal dedup, independent of the mathlib question)?

**Next action:** user answers the questions above (especially Q1 and Q3). The lemma is correct, sorry-free, and maximally general for its role; it is **flagged for the human deciding the scope and internal/public boundary of the upstream `zsmul_eq_smulEval` package** — it is not an independent add/remove decision. Reference for the maintainer: the citable target is the **multiplication formula** `[n]P = (φₙ:ωₙ:ψₙ³)` (Silverman *AEC* Ex. 3.7; Sutherland MIT 18.783 Lecture 5; Wikipedia "Division polynomials"), of which `smulRing_neg` is the universal-ring negation reduction step.

---

## Next step

User answers the numbered questions (Q1/Q3 are the gate). `smulRing_neg` travels to mathlib only as an (most likely `private`) intermediate of the `zsmul_eq_smulEval` package, after `Universal.curve` and `ω` land; it is not a standalone mathlibable decision. Independently, consider de-duplicating it against the HasseWeil copy inside AINTLIB.
