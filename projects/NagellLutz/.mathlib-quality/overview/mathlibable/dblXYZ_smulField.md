# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulField`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Author: Junyan Xu.
> Verdict authored from source (local build stale; reasoned from the elaborated
> statement, mathlib source, and a full literature sweep).

---

### Baseline (Phase 0)
- lake build:               not run (stale per task brief; reasoned from source)
- decl `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulField`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:460`
  (namespaces `WeierstrassCurve` (76) → `Universal` (86) → `Jacobian` (395–544);
  qualified name **confirmed** = the parsed name)
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: integer multiples `n • P` of a rational point on a
  Weierstrass curve, expressed via division polynomials
  (`WeierstrassCurve.zsmul_eq_smulEval`).

**Duplicate alert (consolidation-relevant):** an identical lemma
`dblXYZ_smulField` with the *same* statement exists in a sibling fork,
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:543`. Both
projects fork the same upstream `WeierstrassCurve.Universal` / division-polynomial
development. This is a clean dedup target for `main` regardless of the mathlib verdict.

---

### Statement (Phase 1)

`dblXYZ_smulField` states the **doubling step of the multiplication-by-`n`
formula**, in the universal case, after passing to the fraction field.

Concretely: let `curve` be the *universal* Weierstrass curve over
`ℤ[a₁,a₂,a₃,a₄,a₆]` (`MvPolynomial Coeff ℤ`), `Poly = R[X][Y]` adjoined with the
universal point `(X, Y)`, `Universal.Field = Frac(ℤ[a₁..a₆,X,Y]/⟨Weierstrass eqn⟩)`,
and `curveField = curve.baseChange Universal.Field`. Write
`smulField n = (φₙ, ωₙ, ψₙ)` (the three division-polynomial families `curve.φ`,
`curve.ω`, `curve.ψ`, mapped into the universal field). Then applying mathlib's
**Jacobian doubling map** `WeierstrassCurve.Jacobian.dblXYZ` to this triple yields
the `2n` triple:

  `dblXYZ curveField (φₙ, ωₙ, ψₙ) = (φ₂ₙ, ω₂ₙ, ψ₂ₙ)`.

Mathematically this is the formula `[2]·[n]P = [2n]P` made explicit at the level of
the division-polynomial coordinates `(φ : ω : ψ)`, in the universal setting where
the coordinates are honest polynomials in `a₁,…,a₆,x,y`.

Variables / typeclasses (Lean side):
- `n : ℤ` — the multiplier (implicit `variable` in scope).
- ambient: the universal ring/field tower (`Universal.Ring`, `Universal.Field`),
  fixed; no free typeclass parameters at the lemma site.

Hypotheses: none (universal statement; holds for all `n : ℤ`).

Conclusion (math): the Jacobian doubling map sends the `n`-th division-polynomial
triple to the `2n`-th, over the universal field.

Conclusion (Lean): `dblXYZ curveField (smulField n) = smulField (2 * n)`
(an equality of `Fin 3 → Universal.Field`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an internal stepping-stone lemma in the inductive proof of the project's
main result `zsmul_eq_smulEval`. Not itself a named theorem; not under `## Main
results`. (It is *part of* a BIG development — the universal multiplication-by-`n`
formula — but the individual lemma is a helper.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure`. n/a — the one-liner check
applies only to definitions. (Note: the *proof* is multi-line — a real
`equiv_iff_eq_of_Z_eq` + `Quotient.exact` argument — so even by spirit this is
substantive, not a defeq alias.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomials multiplication by n Jacobian coordinates doubling phi omega psi"        | yes  | `nP = (φₙ : ωₙ : ψₙ)` in Jacobian; doubling = special case `n→2n` | MIT 18.783 Lecture 6; Moody eprint 2010/630 |
|  2 | WebSearch (general/standard form)| "Silverman Arithmetic of Elliptic Curves φₙ ωₙ ψₙ multiplication-by-m formula"                 | yes  | `[n]P=(φₙ/ψₙ²,ωₙ/ψₙ³)`, `φₙ,ωₙ,ψₙ∈ℤ[a₁,…,a₆,x,y]`     | Silverman AEC III.3.6 / Exercise 3.7 — the *universal-ring* coefficient statement, exactly the project's setting |
|  3 | WebSearch (named-after/aliases)  | covered by #1/#2 ("division polynomial", "multiplication-by-n map [n]", EDS)                   | yes  | same; ω = `(4y)⁻¹(ψₘ₊₂ψₘ₋₁²−ψₘ₋₂ψₘ₊₁²)`, φ = `xψₘ²−ψₘ₊₁ψₘ₋₁` | classical; consistent across sources |
|  4 | ChatGPT MCP                      | (server down per task brief — fallback to #1/#2/#5)                                            | n/a  | —                                                     | substituted by two extra WebSearch generality levels + mathlib-source read |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`, `refs/NagellLutz/`                          | n/a  | (neither dir exists)                                  | recorded n/a; relied on Silverman AEC PDF surfaced via WebSearch #2 |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                       | n/a  | nLab has no division-polynomial entry                 | not a higher-categorical concept; nLab silent |
|  7 | nCatLab                          | —                                                                                              | n/a  | —                                                     | not a categorical concept |
|  8 | Stacks Project                   | division polynomial / Weierstrass                                                              | n/a  | Stacks has no explicit division-polynomial multiplication formula | concrete arithmetic-geometry computation, out of Stacks scope |
|  9 | MathOverflow / Math.SE           | "Jacobian coordinates motivation" / division polynomial degrees                               | yes  | confirms `(λ²x:λ³y:λz)` Jacobian weighting and `nP=(φₙ:ωₙ:ψₙ)` | MathOverflow thread on Jacobian-coordinate motivation |
| 10 | recent arXiv (last 5y)           | "division polynomials in Mumford coordinates" (2412.10284); "Division Polynomials for alternate models" (2010/630) | yes | restate the same `(φₙ,ωₙ,ψₙ)` triple + doubling | confirms the formulation is current/standard, generalised to other models |

The protocol passes: ≥3 WebSearch queries at distinct generality levels; local
refs + nLab + Stacks + nCatLab + MathOverflow + arXiv each checked or n/a-with-reason.
ChatGPT MCP is down per the task brief and substituted by extra WebSearch breadth +
a direct read of mathlib's own division-polynomial source.

### Literature summary (Phase 3)

Concept identified as: the **division-polynomial multiplication-by-`n` formula**
`[n]P = (φₙ : ωₙ : ψₙ)` (Jacobian) / `(φₙ/ψₙ², ωₙ/ψₙ³)` (affine), with the
**doubling case** `[2]·[n]P = [2n]P` expressed on the coordinate triple.
Sources agree on the standard form: **yes** (Silverman AEC III.3.6 + Exercise 3.7;
Lang; Washington; MIT 18.783; arXiv:2412.10284; eprint 2010/630).
Most general standard form: the coefficients are taken in the **universal ring**
`ℤ[a₁,a₂,a₃,a₄,a₆,x,y]` — i.e. independent of the base field. The project's
`Universal.Ring`/`Universal.Field` + `smulRing`/`smulField` realise *exactly* this
universal form. The lemma is stated over the universal field, which is the maximally
general base; specialisation to an arbitrary `WeierstrassCurve F` (any field) is the
*downstream* `dblXYZ_smulEval`/`zsmul_eq_smulEval`.
Generality dimensions where the literature varies:
  - coefficient ring: from a fixed field up to the universal `ℤ[a₁,…,a₆,x,y]` — the
    project is already at the most general (universal) end.
  - curve model: short Weierstrass `y²=x³+Ax+B` (Silverman exercises) up to general
    Weierstrass `a₁,…,a₆` (project + mathlib). Project is at the general end.
Disagreement with the literature: none. The Lean form is the standard form at the
maximal (universal, general-Weierstrass) generality.

---

### Generality analysis — `dblXYZ_smulField`

Literature-standard form (Phase 3): `[2n]P = [2]([n]P)` on the
`(φ : ω : ψ)` triple, coefficients in `ℤ[a₁,…,a₆,x,y]`, general Weierstrass model.

| # | Parameter / hypothesis        | Current Lean form                      | Literature-standard form            | Weaker form exists? | Reason |
|---|-------------------------------|----------------------------------------|-------------------------------------|---------------------|--------|
| 1 | base ring                     | universal field `Frac(ℤ[a₁..a₆,X,Y]/⟨P⟩)` | universal ring `ℤ[a₁,…,a₆,x,y]`     | NO (already maximal) | universal = most general base; the field is the natural place to run the `equiv_iff_eq_of_Z_eq` argument, and `dblXYZ_smulRing` (line 471) immediately transports it back to the ring via `IsFractionRing` injectivity |
| 2 | curve model                   | general Weierstrass (`a₁,…,a₆`)         | general Weierstrass                  | NO (already maximal) | uses full `a₁..a₆`, not short form |
| 3 | multiplier `n`                | `n : ℤ`                                | `n ∈ ℤ`                              | NO                  | already the full integer multiplication map |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is the universal-ring statement,
which is the most general coefficient setting the literature uses; specialisation to
any base field/curve is the downstream `dblXYZ_smulEval`).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Note |
|----|--------------------------------------------------------------------------------------------|----------|------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                         | no       | no bundled hypotheses; already universal |
|  2 | sequences/metric → filters/topology?                                                       | no       | purely algebraic identity in a field; no topology |
|  3 | construct an object → universal-property class?                                            | no       | already *is* the universal construction (universal curve); this is the right modern idiom |
|  4 | set-with-closure-predicate → bundled substructure?                                          | no       | n/a |
|  5 | field/metric-specific → modules/(semi)ring?                                                 | no       | the universal *field* is essential to the proof method (`equiv_iff_eq_of_Z_eq`, inverting `ψₙ`); the ring statement is recovered separately as `dblXYZ_smulRing` |
|  6 | 1-categorical → higher-categorical?                                                         | no       | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                              | no       | the index is `n : ℤ` = the multiplication-by-`n` map; `ℤ` is intrinsic (it indexes the group endomorphisms), not an incidental scalar |

Modern idiom available: **no**. This already follows mathlib's own established
"prove the polynomial identity in the universal ring, specialise by a ring hom"
pattern (mirroring `WeierstrassCurve.Universal` conventions and the
`map_dblXYZ`/`map_ψ` compatibility lemmas). One-line reason: it is already the
contemporary universal-curve formulation; there is no cleaner mathlib idiom.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma`. (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulField`

Searched mathlib pin at `.lake/packages/mathlib/Mathlib/` (the project's own
mathlib; this project *forks* the relevant files, so the upstream files are the
authoritative check).

```
[A] Lean-Finder       n/a (offline index; substituted by direct mathlib-source grep over the exact area)
[B] Loogle            `dblXYZ _ _ = _`, division-polynomial triple = triple   no hit
[C] LeanSearch        "doubling map on division polynomial triple equals 2n triple"   no hit
[D] Grep mathlib src  `dblXYZ_smulField`, `smulField`, `smulRing`, `smulPoly`, `smulEval`,
                      `namespace Universal` (in EllipticCurve/), `zsmul_eq`, `def ω`/omega   no hit
[E] Name pattern      `dblXYZ_smul*`, `*_smulField`, `Universal.Jacobian.*`   no hit
```

Concrete mathlib findings (the load-bearing ones):
- **Building blocks present**: `dblXYZ`, `dblZ`, `addXYZ`, `addZ`, and the
  compatibility lemmas `map_dblXYZ`, `map_dblZ`, `map_addXYZ` exist in
  `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean` (defs at lines
  199/349/425/661; map-lemmas at 722–808). The division polynomials `ψ`, `φ` (`Φ`),
  `Ψ`, `preΨ`, `ΨSq` exist in
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`.
- **Key gap #1 — `ω` is an explicit mathlib TODO.** The Main-definitions block of
  `DivisionPolynomial/Basic.lean` lists `* TODO: the bivariate polynomials ωₙ.` and
  `TODO: implementation notes for the definition of ωₙ.` Mathlib has **no `ω`
  division polynomial**. The project supplies it
  (`projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean`, whose header reads
  "extends the division polynomial development from mathlib with the `ω` family …
  needed for the `ZSMul` proof"). `smulField`/`dblXYZ_smulField` depend on `ω`.
- **Key gap #2 — no multiplication-by-`n` formula.** Mathlib's Jacobian group
  action is `zsmul := zsmulRec` (`Jacobian/Point.lean:590`) — purely recursive, with
  **no closed-form** `n • P = (φₙ : ωₙ : ψₙ)`. Repo-wide grep for any statement
  relating `n • P` to division polynomials in mathlib returns nothing.
- **No `WeierstrassCurve.Universal` namespace in mathlib** (the universal curve over
  `ℤ[a₁,…,a₆]` and its fraction field are project-local).

Concluded: **not in mathlib** (all methods exhausted, incl. the literature-standard
universal form). Mathlib has the *Jacobian-formula and division-polynomial building
blocks*, but is missing `ω`, the universal-curve scaffolding, and the multiplication
formula this lemma is a step of.

---

### Call sites — `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulField`

Internal use count: **1** (within NagellLutz, outside the declaring `ZSMul.lean`): zero.
Inside `ZSMul.lean`: used once, by `dblXYZ_smulRing` (line 473:
`simp_rw [← map_dblXYZ]; exact dblXYZ_smulField`).
External-to-file callers: 0 distinct files in NagellLutz.

| Caller file:line                  | Usage pattern (one-line excerpt)                                  |
|-----------------------------------|-------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:473         | `simp_rw [← map_dblXYZ]; exact dblXYZ_smulField` (proves `dblXYZ_smulRing`) |

Cross-project duplicate (NOT a call site — an independent copy):
| HasseWeil/Auxiliary/DivisionPolynomial.lean:543 | identical lemma, identical proof |

Inline-derivation grep: the equivalent identity is **not** re-derived inline
elsewhere; downstream consumers (`dblXYZ_smulEval`, `zsmul_eq_smulEval`) go through
`dblXYZ_smulRing` → `ringEval_comp_smulRing`, which routes through this lemma. So it
is a genuine link in the chain, even though its *direct* caller count is 1.

Chain (confirmed by reading ZSMul.lean 460–597):
`dblXYZ_smulField` (universal field, 460)
  → `dblXYZ_smulRing` (universal ring, 471; via `IsFractionRing` injectivity)
  → `dblXYZ_smulEval` (any curve/field, 568; via `ringEval`)
  → `zsmul_eq_smulEval` (590; the project's main multiplication-by-`n` theorem).

Call-site signal: K=1 internal use, no inline re-derivation. On its own this leans
"could be inlined", **but** the def-first / development context overrides: it is one
step of a coherent universal-case proof of a genuinely-new, mathlib-TODO result.
The right upstreaming grain is the *whole development*, not this lemma alone.

---

### Composition check (Phase 6)

Can `dblXYZ_smulField` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: `map_dblXYZ` + a hypothetical mathlib `dblXYZ (φₙ,ωₙ,ψₙ) = (φ₂ₙ,…)`.
  - Mathlib decls used: `map_dblXYZ` (exists). The doubling-on-the-triple identity:
    **does not exist** in mathlib.
  - Result: fails. The crux is a genuine computation in the universal field:
    `refine (equiv_iff_eq_of_Z_eq … (ψᵤ_ne_zero …)).mp (Quotient.exact …)` using the
    Z-coordinate identity `dblZ_smulPoly` (which itself unfolds the doubling formula
    and invokes the project's `ω_spec`/`ψc_spec`). This is project-specific reasoning
    about `ω` — and `ω` is not in mathlib at all.

Attempt 2: build it from `ψ`/`φ`/`Φ` alone (no `ω`).
  - `ω` is irreducibly present in `smulField` (the second coordinate). With no `ω` in
    mathlib, there is no composition path.

Conclusion: **NOT-COMPOSABLE**. The result needs new content (`ω` + universal
scaffolding + a real doubling computation), not a 1–3 call mathlib composition.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulField`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): standard form is `[n]P=(φₙ:ωₙ:ψₙ)` with universal-ring
  coefficients (Silverman AEC III.3.6 / Ex. 3.7); this lemma is the `2n` doubling step
  at the maximal (universal) generality. Sources agree.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (universal field/ring, general
  Weierstrass, `n : ℤ`); no weakenings; no modern-idiom flip (it already *is* the
  universal-curve idiom).
- Mathlib search (Phase 5): **not in mathlib**; moreover `ω` is an explicit mathlib
  **TODO**, and there is **no** multiplication-by-`n` formula upstream.
- Composition check (Phase 6): **NOT-COMPOSABLE** (`ω` absent; the doubling identity is
  a real computation).

**Rationale.**
The mathematics here is squarely mathlib-worthy: the multiplication-by-`n` formula in
division polynomials, `n • P = (φₙ : ωₙ : ψₙ)`, is the textbook (Silverman) result, and
mathlib *already advertises the gap* — `DivisionPolynomial/Basic.lean` lists `ωₙ` as a
TODO and `Jacobian/Point.lean` defines the group action by bare recursion (`zsmulRec`)
with no closed form. The NagellLutz development (`DivisionPolynomialOmega.lean` +
`Universal.lean` + `ZSMul.lean`) fills exactly that gap, culminating in
`zsmul_eq_smulEval`. So the *development* is a strong YES for mathlib.

`dblXYZ_smulField` itself, however, is an **internal stepping-stone**, not the unit one
upstreams: it is the universal-*field* form of the doubling step (`K=1` direct caller,
namely `dblXYZ_smulRing`, which is the universal-*ring* form that the rest of the proof
actually consumes). It should not go to mathlib *as a stand-alone lemma in this shape*;
it should travel **with** the whole division-polynomial-multiplication-formula PR, and
the upstreamable surface is the field/ring pair `dblXYZ_smulField`/`dblXYZ_smulRing`
plus its specialisation `dblXYZ_smulEval` — most likely even folded into the proof of
the headline `zsmul_eq_smulEval`/`smulEval` API rather than exposed as a public lemma of
its own. Hence "generalise first" in the sense of *re-scoping to the right grain*: lift
the development, expose the main multiplication-by-`n` theorem and the `ω`/`smulEval`
API, and let this universal-field doubling identity be an internal (or `private`) step
of that PR. The verdict is not NO-mathlib-has-it (mathlib lacks it and the building
blocks can't compose it without `ω`), and not YES-add-as-is (shipping this single
universal-*field* helper, bypassing the ring form its consumers use, would be the wrong
PR grain).

**Reason for the generalisation/re-scoping:** MODERN-IDIOM / right-grain. Phase 4b found
the statement maximally *general*, but the correct mathlib *unit* is the multiplication
formula + `ω` API, not this isolated universal-field lemma.

**Proposed restatement (re-scoping, not weakening):**
```lean
-- Upstream the development, exposing the public API at the level mathlib wants:
--   1. the ω division polynomials (closes the existing `DivisionPolynomial/Basic` TODO)
--   2. `WeierstrassCurve.φ`/`ω`/`ψ` packaged as the Jacobian coordinate triple
--   3. the multiplication-by-n theorem:
theorem WeierstrassCurve.zsmul_eq_smulEval {F} [Field F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some _ _ h)).point =
      ⟦evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]⟧ := by
  sorry  -- the universal-case lemmas (dblXYZ_smulField/Ring, addXYZ_…) become internal steps
```
Estimated cost of re-scoping: **MODERATE** — the math is done; the work is packaging the
`Universal` + `ω` machinery to mathlib standards and deciding which helpers stay
`private`. (Cost does not downgrade the verdict.)

**Mathlib downstream this enables:**
- closes the `DivisionPolynomial/Basic.lean` `ωₙ` TODO (named gap);
- gives `WeierstrassCurve.Jacobian.Point` a *closed-form* scalar multiplication, which
  the current `zsmulRec` lacks — unlocking torsion-point computations (the Nagell–Lutz
  programme), height/`p`-adic valuation estimates on `ψₙ`, and reduction arguments;
- the `map_dblXYZ`/`map_ψ`/`ringEval` compatibility lemmas already in mathlib compose
  directly with the new `smulEval`, so the universal→specific specialisation is free.

**PR grouping (required):** ship as **one** PR for the whole development —
`ω` (DivisionPolynomialOmega) + `WeierstrassCurve.Universal` + the multiplication
formula (`smulEval`, `zsmul_eq_smulEval`), with `dblXYZ_smulField`/`dblXYZ_smulRing`/
`addXYZ_smul*` as internal steps. Author is Junyan Xu (also a mathlib EllipticCurve
contributor), so coordinate upstreaming directly. **Also dedup first:** the identical
`dblXYZ_smulField` in `HasseWeil/Auxiliary/DivisionPolynomial.lean:543` should be
consolidated on AINTLIB `main` before/with upstreaming.

**Pre-PR checklist:**
- [ ] Consolidate the NagellLutz vs HasseWeil duplicate forks into one shared copy.
- [ ] `/generalise` the *public* surface (the `ω` defs + `zsmul_eq_smulEval`), not this
      helper — confirm the universal-ring statement is the exposed one.
- [ ] `/cleanup` the `Universal` + `ω` files to mathlib style; mark internal helpers
      `private`.
- [ ] Proposed location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`
      (new `Omega.lean` + the multiplication formula) and/or
      `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/`.
- [ ] Reviewer: pick from recent `EllipticCurve/DivisionPolynomial` + `Jacobian`
      committers (Angdinata / Xu).

---

## Next step

Re-scope: upstream the **whole** `ω` + universal-curve + multiplication-by-`n`
development as one PR (closing the `ωₙ` mathlib TODO and giving Jacobian points a
closed-form `zsmul`), with `dblXYZ_smulField` as an internal step — not as a stand-alone
lemma. First consolidate the NagellLutz/HasseWeil duplicate on AINTLIB `main`.
