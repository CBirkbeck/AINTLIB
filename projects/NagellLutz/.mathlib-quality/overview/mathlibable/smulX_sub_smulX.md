# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences).
> Single declaration. Full literature search run (ChatGPT MCP was down — fell back to
> WebSearch ×5 + grep; `lean_loogle`/`lean_leansearch` not available in this env — used
> mathlib-source grep for Phase 5).

## Baseline (Phase 0)

- lake build:               stale (not re-run; per task — reason from source). The decl elaborates in the committed tree.
- decl `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:186`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Integer multiples of a rational point on an elliptic curve in terms of
                             division polynomials — proves `WeierstrassCurve.zsmul_eq_smulEval`,
                             i.e. `n • P = (φₙ : ωₙ, ψₙ)` in Jacobian coords. Author: Junyan Xu.

**Qualified name verified from source.** The parsed name
`WeierstrassCurve.Universal.Affine.smulX_sub_smulX` is correct:
`namespace WeierstrassCurve` (ZSMul.lean:76) → `namespace Universal` (:86) →
`namespace Affine` (:157); decl at :186.

---

## Statement (Phase 1)

`smulX_sub_smulX` states the **difference-of-x-coordinates formula** for integer
multiples of a point on an elliptic curve, expressed through division polynomials.

On the *universal* Weierstrass curve (the curve over the field of fractions
`Universal.Field` of the universal coefficient ring `ℤ[a₁,…,a₆,X,Y]/(Weierstrass)`,
with its tautological point `(X, Y)`), write:
- `ψᵤ n` := the `n`-th division polynomial of the universal curve, mapped into `Universal.Field`
  (`ψᵤ = normEDS …`, an elliptic divisibility sequence; `ψᵤ_eq_normEDS`, ZSMul.lean:134);
- `smulX n` := `φₙ / ψₙ²` — the X-coordinate of `n • (X, Y)` (def at ZSMul.lean:164).

Then for `m, n ≠ 0`:
$$\mathrm{smulX}\,m - \mathrm{smulX}\,n \;=\; \frac{\psi_{n+m}\,\psi_{n-m}}{(\psi_n\,\psi_m)^2}.$$

Mathematically: `x([m]P) − x([n]P) = ψ_{n+m}·ψ_{n−m} / (ψ_n·ψ_m)²`.

Variables / typeclasses (Lean side):
- (curve fixed in scope: `curve` = the universal Weierstrass curve over `ℤ`; everything
  takes place in `Universal.Field`, a fixed field — no free typeclass variables).
- `m n : ℤ` — the two multipliers.

Hypotheses (Lean side):
- `hm : m ≠ 0`, `hn : n ≠ 0` — both multipliers nonzero (so `ψₘ, ψₙ ≠ 0`, denominators valid).

Conclusion (math): the difference of the X-coordinates of `[m]P` and `[n]P` equals
`ψ_{n+m}ψ_{n−m}/(ψ_nψ_m)²`.

Conclusion (Lean):
`smulX m - smulX n = ψᵤ (n + m) * ψᵤ (n - m) / (ψᵤ n * ψᵤ m) ^ 2`.

Proof (3 lines): rewrite both sides with `smulX_eq` (`x([k]P) = x − ψ_{k+1}ψ_{k−1}/ψ_k²`),
collapse `c−a−(c−b)=b−a`, combine via `div_sub_div`, then the numerator equality is exactly
the three-term EDS/division-polynomial recurrence `isEllSequence_ψᵤ n m 1`
(`Rel₃`: `ψ_{n+m}ψ_{n−m}ψ_1² = ψ_{n+1}ψ_{n−1}ψ_m² − ψ_{m+1}ψ_{m−1}ψ_n²`), with `ψ_1 = 1`.

---

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a named, classical identity in the elliptic-curve / division-polynomial
literature (the "difference of x-coordinates" formula; stated on Wikipedia) and a structural
lemma in the project's main result (the multiplication-by-`n` formula chain feeding
`zsmul_eq_smulEval`). Not a throwaway helper.

(Literature width is EXHAUSTIVE regardless. BIG recorded for framing.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — **n/a**. One-line check skipped.

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found                                                            | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomials x-coordinate difference `ψ_{m+n}ψ_{m−n}/(ψ_mψ_n)²`                              | yes  | `φ_mψ_n² − φ_nψ_m² = (x(mP)−x(nP))ψ_n²ψ_m²`; squared: `|φ_nψ_m²−φ_mψ_n²|² = ψ_{n+m}²ψ_{|n−m|}²` | arXiv 1005.4771, 1103.4560; Wikipedia |
|  2 | WebSearch (general / EDS form)   | EDS "x(mP) − x(nP)" division-polynomial product formula                                              | yes  | same identity in EDS framing; recurrence `ψ_{m+n}ψ_{m−n}=ψ_{m+1}ψ_{m−1}ψ_n²−ψ_{n+1}ψ_{n−1}ψ_m²` | Wikipedia EDS; Leiden CM-EDS report; arXiv 0802.2651 |
|  3 | WebSearch (named-after / nets)   | Stange elliptic nets x(P+Q) net-polynomial x-coordinate                                              | yes  | **`Ψ_v²Ψ_u²(x(v·P)−x(u·P)) = −Ψ_{v+u}Ψ_{v−u}`** — the SIGNED form, verbatim    | "On Symmetries of Elliptic Nets…", arXiv 1408.6623 (Stange's net generalisation) |
|  4 | WebSearch (Wikipedia verbatim)   | Division_polynomials wiki `psi_{n+m}` squared identity / x∘[n]                                       | yes  | **`Ψ_{n+m}Ψ_{n−m}/Ψ_n²Ψ_m² = x∘[n] − x∘[m]`** — verbatim on Wikipedia          | en.wikipedia.org/wiki/Division_polynomials — *exact statement* |
|  5 | WebSearch (Silverman textbook)   | Silverman AEC division polynomials φ_n ψ_n x(nP) Exercise 3.7                                        | yes  | `φ_n = xψ_n² − ψ_{n−1}ψ_{n+1}`, `x(nP)=φ_n/ψ_n²`; three-term `ψ_{n+m}ψ_{n−m}ψ_r²=…` | Silverman AEC, Exercise 3.7 |
|  6 | ChatGPT MCP                      | standard name + generality + signed-vs-squared + sign convention                                    | n/a  | MCP server down (Codex exec failed) — task flagged this; covered by #1–#5+nLab | fallback used |
|  7 | Local references                 | grep `.mathlib-quality/references/` for division-polynomial / EDS sources                            | n/a  | no project source-paper PDFs in references dir (only skill docs)                | recorded n/a |
|  8 | nLab                             | elliptic divisibility sequence / division polynomial                                                | n/a  | nLab has no dedicated division-polynomial / x-coordinate-formula page          | not a categorical concept; n/a |
|  9 | Stacks Project (alg geom)        | division polynomial / x-coordinate of multiple                                                      | n/a  | Stacks does not cover division polynomials / explicit EC multiplication        | n/a |
| 10 | MathOverflow / arXiv (recent)    | MIT 18.783 notes §5; "Elliptic Net Algorithm Revisited"; net-symmetry papers                          | yes  | MIT 18.783 L5 derives `x(nP)=φ_n/ψ_n²`; net papers give the signed x-coord formula | ocw.mit.edu …notes5.pdf; arXiv 2109.07050, 1408.6623, 2102.07573 |

### Literature summary (Phase 3)

Concept identified as: **the difference-of-x-coordinates formula for division polynomials**
(equivalently, in Stange's generalisation, the net-polynomial x-coordinate formula).

Sources agree on the standard form: **yes.** Multiple independent, authoritative sources give
the identity, in two equivalent packagings:
- **Squared form** (Wikipedia, arXiv 1005.4771/1103.4560): `|φ_nψ_m² − φ_mψ_n²|² = ψ_{n+m}²ψ_{|n−m|}²`.
- **Signed form** (Wikipedia "Division polynomials" *verbatim*; Stange net papers arXiv 1408.6623):
  `Ψ_{n+m}Ψ_{n−m}/Ψ_n²Ψ_m² = x∘[n] − x∘[m]`, resp. `Ψ_v²Ψ_u²(x(v·P)−x(u·P)) = −Ψ_{v+u}Ψ_{v−u}`.

The project's lemma `smulX m − smulX n = ψ_{n+m}ψ_{n−m}/(ψ_nψ_m)²` is **exactly** the signed
Wikipedia form: with `smulX k = x([k]P)`, the LHS is `x([m]P) − x([n]P)`; Wikipedia's RHS is
`x∘[n] − x∘[m] = x([n]P) − x([m]P)`. These agree because `ψ_{n−m} = −ψ_{m−n}` flips the sign to
match the index swap. The signed (unsquared) version is *standard* in the EDS / elliptic-net
framework, where the normalised division-polynomial sequence (`normEDS`) carries the fixed sign
convention that makes the unsquared product come out correctly — which is precisely the
`isEllSequence_ψᵤ`/`Rel₃` structure the project's proof uses.

Most general standard form: stated for an arbitrary Weierstrass curve (any base where the
division polynomials make sense). Stange (elliptic nets) is the modern, *most general*
formulation — it extends the single-point (`ℤ`-indexed) identity to several points
(`ℤ^r`-indexed net polynomials). The single-variable case here is the classical specialisation.

Generality dimensions where the literature varies:
  - base of the curve: from "over ℂ/a number field" (classical) to "over any ring/field"
    (modern; the universal-curve approach is the maximally-general incarnation — proves it
    once over `ℤ[a₁..a₆,X,Y]`, specialises to every curve by a ring hom).
  - number of points: 1 point (this lemma) → `r` points (Stange's net polynomials).

Disagreement with the literature: **none.** The Lean form matches the literature's signed form,
with the index/sign convention handled exactly as the EDS normalisation prescribes.

---

## Generality analysis — `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`

Literature-standard form (from Phase 3): `x([m]P) − x([n]P) = ψ_{n+m}ψ_{n−m}/(ψ_nψ_m)²`, for an
arbitrary Weierstrass curve and a point `P`, with `ψ` the normalised division-polynomial EDS.

| # | Parameter / hypothesis     | Current Lean form                                  | Literature-standard form                        | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------|----------------------------------------------------|-------------------------------------------------|---------------------|----------------------------------|
| 1 | the curve / point          | the *universal* curve over `Universal.Field` and its tautological point `(X,Y)` | any Weierstrass curve `W/F` and point `P`        | already maximal     | The universal-curve statement is the *most general* incarnation: every concrete `(W/F, P)` is obtained by the specialising ring hom `Universal.Field → F` (`ψ`, `smulX` are compatible with base change — `map_ψ`, etc.), so the concrete `x([m]P)−x([n]P)=…` follows from this one by functoriality. This is the module-not-vector-space pattern: prove the universal polynomial identity once. |
| 2 | `hm : m ≠ 0`, `hn : n ≠ 0` | both nonzero                                        | both nonzero (denominators `ψ_m, ψ_n` must be ≠0) | NO                  | Essential: the formula divides by `(ψ_nψ_m)²`; for `m=0` or `n=0`, `ψ=0` and `smulX 0 = 0` (the formula degenerates). Cannot weaken. |
| 3 | index type `ℤ`             | `m n : ℤ`                                          | `ℤ` (single point) — Stange: `ℤ^r` (net)         | yes, in principle   | The Stange/elliptic-net generalisation to `r` points is strictly more general but is **a different theorem with a different object** (net polynomials), not a weakening of *this* statement. Out of scope for this single-point lemma; flagged in Phase 4c. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the single-point division-polynomial identity).
Number of weakening opportunities found: 0 (hypotheses are tight; the universal-curve framing is
already the most general single-point form).
Proposed restatement: none required for generality.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation                                  | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|---------------------------------------------------------|----------------------------------|
|  1 | "Let X be a foo" preamble → typeclass/instance?                                                    | no       | already typeclass-free; works in a fixed field          | — |
|  2 | sequences/metric → filters/topological?                                                            | no       | finite algebraic identity; no topology                  | — |
|  3 | construction → universal-property class?                                                           | partial  | the **universal curve** `Universal` *is* the universal-property device here — the statement is *already* the universal/generic form, specialising to every concrete curve | this is the modern idiom, not a gap |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | n/a                                                     | — |
|  5 | field/metric-specific → weaken typeclasses?                                                        | no       | lives in `Universal.Field` by necessity (need division); concrete instances arrive by base-change ring hom | — |
|  6 | 1-categorical → higher-categorical?                                                                | no       | n/a                                                     | — |
|  7 | concrete index (ℤ) → general additive monoid / **several points (elliptic nets)**?                 | yes      | Stange's net-polynomial form `Ψ_v²Ψ_u²(x(vP)−x(uP)) = −Ψ_{v+u}Ψ_{v−u}` over `ℤ^r` | would unify with a future mathlib `EllipticNet` theory — but is a *separate, larger* development, not a restatement of this lemma |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this declaration as scoped).
Reason: Q3 — the universal-curve formulation *is already* the contemporary
"prove-it-generically, specialise-by-ring-hom" idiom; there is no cleaner restatement of the
single-point identity. Q7 points at the genuinely more general elliptic-net theory (Stange),
but that is a *new object* (`ℤ^r`-indexed net polynomials) and a *much larger development* — it
would not restate `smulX_sub_smulX`, it would be a separate contribution that has this as its
`r = 1` special case. Per the verdict rules, that is not a "generalise-first" target for this
lemma; it is a future direction. So the verdict stays YES-add-as-is rather than
YES-but-generalise-first.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths
introduced). Skipped.

---

## Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`

[A] Lean-Finder       — not available in this env                          n/a: tool absent
[B] Loogle            — `lean_loogle` not available in this env             n/a: tool absent (reasoned from mathlib source instead)
[C] LeanSearch        — `lean_leansearch` not available in this env         n/a: tool absent
[D] Grep mathlib src  `smulX`, `x(nP)`, x-coord difference, `ψ.*n + m`, `_sub_`/`diff` on div-polys/EDS   → **no hits**
[E] Name pattern      `smulX*`, `*_sub_smulX`, x-coordinate-of-multiple, net machinery (`net`/`rel₄`/`Rel₃`/`relFin4`) in mathlib   → **no hits**

Searched for both:
  - the user's current form (`smulX m - smulX n = …`) — mathlib has no `smulX`, no `Universal`
    curve, no x-coordinate-of-multiple object at all.
  - the literature-standard form (`x([m]P)−x([n]P) = ψ_{n+m}ψ_{n−m}/(ψ_nψ_m)²`) — mathlib has the
    *ingredient* `φ_n = X·ψ_n² − ψ_{n+1}ψ_{n−1}` (`DivisionPolynomial/Basic.lean:29–30` doc;
    `φ_two`, `φ_three`, `φ_neg`, `ψ_neg`, the recurrences, `map_*`/`baseChange_*`), but **no
    statement relating `φ_n/ψ_n²` to the coordinate of `n • P`**, and **no difference formula**.

What mathlib has (and does NOT have):
- HAS: `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.{Basic,Degree}` — the
  polynomials `ψ, φ, ω, Ψ, Φ` and their recurrences/degrees/base-change.
- HAS: `Mathlib.NumberTheory.EllipticDivisibilitySequence` — `IsEllSequence`, `normEDS`,
  `preNormEDS`, recurrences (the abstract sequences only).
- HAS: `…/EllipticCurve/{Affine,Jacobian,Projective}/Point.lean` — the group law on points.
- DOES NOT HAVE: any link from division polynomials to `n • P` coordinates (`smulX`/`smulY`),
  the universal-curve `Universal` framework, the multiplication-by-`n` formula
  `n • P = (φₙ/ψₙ², ωₙ/ψₙ³)`, or the x-coordinate difference formula. (The project even forks
  `EllipticDivisibilitySequence` into a *richer* `net`/`rel₄`/`Rel₃` API that is itself not yet
  upstream.)

Concluded: **not in mathlib** (source grep exhausted under both the user's form and the
literature-standard form; the supporting objects `smulX`, `ψᵤ`, `Universal` do not exist
upstream, and neither does any x-coordinate-difference statement).

---

## Call sites — `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`

Internal use count: **3** (within NagellLutz, excluding the declaring lemma).
External-to-file callers: 0 distinct files (all uses are inside `ZSMul.lean`, downstream of
the declaration — this file *is* the elliptic-curve multiplication development).

| Caller file:line          | Usage pattern (one-line excerpt)                                                            |
|---------------------------|---------------------------------------------------------------------------------------------|
| ZSMul.lean:198            | `rw [smulX_sub_smulX sub_ne add_ne]` — proves `smulX_sub_sub_smulX_add` (the `2n`,`2m` form) |
| ZSMul.lean:310            | `rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]` — slope / group-law step |
| ZSMul.lean:329–330        | `simp_rw [… smulX_sub_smulX hn add_ne, smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, …]` — addition-formula step |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — the difference formula is only ever obtained through this lemma.

Signal: **K = 3 internal uses, no inline re-derivation** → real API; the multiplication-formula
proof genuinely depends on it. Leans YES.

---

## Composition check (Phase 6)

Can `smulX_sub_smulX` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: rewrite via mathlib division-polynomial lemmas + a recurrence.
  - The statement is *about* `smulX` (= `φₙ/ψₙ²` in `Universal.Field`) and `ψᵤ` (the universal
    `normEDS`). **Neither `smulX` nor `ψᵤ` nor `Universal.Field` exists in mathlib.** There is no
    mathlib object whose difference this lemma could be a composition over.
  - Result: **fails** — there is nothing to compose. The supporting framework (universal curve,
    `smulX`, `smulX_eq`, `isEllSequence_ψᵤ`) is entirely project-local.

Attempt 2: rebuild from primitives.
  - Even granting the framework, the proof is `smulX_eq` (×2) + `div_sub_div` + the three-term
    EDS recurrence `isEllSequence_ψᵤ n m 1` (`Rel₃`) + `ring`/`congr`/`mul_pow`. The crux is the
    EDS recurrence — a genuine, project-supplied identity (`IsEllSequence` of the universal `ψ`,
    via `normEDS`), not a mathlib one-liner. This is a real proof, not a 1–3 call composition.

Conclusion: **NOT-COMPOSABLE.**

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): 6 hitting channels; the identity is stated **verbatim on
  Wikipedia** (`Ψ_{n+m}Ψ_{n−m}/Ψ_n²Ψ_m² = x∘[n] − x∘[m]`) and in Stange's net-polynomial papers
  (signed form). Standard, named, classical.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — the universal-curve framing is the most
  general single-point form (every concrete curve specialises by a ring hom); hypotheses tight;
  Phase 4c modern-idiom = no (the universal form *is* the modern idiom).
- Mathlib search (Phase 5): **not in mathlib** — no `smulX`, no x-coordinate-of-multiple, no
  difference formula; only the `φ_n` building block exists.
- Composition check (Phase 6): **NOT-COMPOSABLE** — nothing in mathlib to compose over; the proof
  needs the project-local universal-curve + EDS-recurrence framework.

**Rationale.**
This is a textbook, named identity in elliptic-curve theory — the formula for the difference of
x-coordinates of two integer multiples of a point, in terms of division polynomials. It is stated
on Wikipedia and is the `r = 1` case of Stange's elliptic-net x-coordinate formula. The project's
Lean statement matches the literature's signed form exactly (the index ordering `n+m`, `n−m`
absorbs the sign that the EDS normalisation fixes). Mathlib does **not** have it: mathlib's
`DivisionPolynomial` files stop at the polynomials and their recurrences, mathlib's
`EllipticDivisibilitySequence` covers only the abstract sequences, and mathlib's point files
carry the group law — but nothing connects division polynomials to the coordinates of `n • P`,
let alone to a difference formula. It is not composable from mathlib primitives, because the very
objects it speaks about (`smulX`, `ψᵤ`, the `Universal` curve) live only in this project.

The statement is at the right generality: the universal-curve formulation is the maximally-general
single-point form (the "prove the polynomial identity once over `ℤ[a₁..a₆,X,Y]`, then specialise to
every curve by base change" idiom — the elliptic-curve analogue of modules-not-vector-spaces).
The genuinely-more-general direction (Stange's `ℤ^r`-indexed net polynomials) is a separate, much
larger development with this as a special case — a future contribution, not a "generalise-first"
restatement of *this* lemma, so the verdict is YES-add-as-is rather than YES-but-generalise-first.

**WHY add it (refactor-actionable).**
The concrete mathlib gap: mathlib's elliptic-curve division-polynomial API has a **known missing
layer** — it defines `ψ, φ, ω` (`DivisionPolynomial/Basic.lean`) and proves `x(nP) = φ_n/ψ_n²`
*nowhere*; there is no lemma asserting that the division polynomials actually compute the
multiplication-by-`n` map, and a fortiori no difference formula. This whole NagellLutz/ZSMul
development (`zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ, ψₙ)`) is exactly the upstreaming candidate
that fills that gap, and `smulX_sub_smulX` is a load-bearing lemma in it (used at 3 sites to build
the slope and the addition/doubling x-coordinate formulas). Adding it composes with mathlib's
existing API by *consuming* `DivisionPolynomial.φ`/`ψ` and the `IsEllSequence` recurrence and
*producing* the geometric content (x-coordinates of multiples) that downstream torsion/height/
Nagell–Lutz work needs.

Note: this is Junyan Xu's development, which is itself essentially a mathlib-PR-in-progress
(Apache header, mathlib style, forks `Mathlib.NumberTheory.EllipticDivisibilitySequence` into a
richer `net`/`rel₄`/`Rel₃` API). So "add to mathlib" here means **land the whole ZSMul /
universal-curve development**, of which this lemma is one piece — not cherry-pick this lemma alone.

Proposed mathlib location:
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` (a new file in this directory for
  the multiplication-by-`n` / x-coordinate formulas, e.g. `Multiplication.lean` or `SMul.lean`),
  alongside `Basic.lean` and `Degree.lean`.
Proposed PR title:
  "feat(AlgebraicGeometry/EllipticCurve): division polynomials compute `n • P`, and the
   x-coordinate difference formula"
PR grouping:
  ship as part of the full ZSMul development — with its siblings `smulX_eq`,
  `smulX_sub_sub_smulX_add`, `smulX_ne_smulX`, `smulX_eq_smulX_iff`, `smulY_sub_negY`, the
  `Universal` curve framework, and the capstone `zsmul_eq_smulEval`. The atomic PR grain is the
  development, not this single lemma. (And it depends on the forked richer EDS `net` API also
  being upstreamed first — likely a prerequisite PR.)
Pre-PR checklist before opening:
  - [ ] `/generalise WeierstrassCurve.Universal.Affine.smulX_sub_smulX` — confirm no easy further
        weakening (expected: none; hypotheses already tight).
  - [ ] `/cleanup` the ZSMul file + this lemma — full audit + diff gates.
  - [ ] Upstream (or coordinate with) the richer `EllipticDivisibilitySequence` `net`/`rel₄` fork
        first — it is a dependency and is also not yet in mathlib.
  - [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the
        division-polynomial / EDS author — likely the original `normEDS` contributor).

---

## Next step

Run `/generalise WeierstrassCurve.Universal.Affine.smulX_sub_smulX` to confirm no further
weakening, then treat this lemma as part of the larger upstreaming of the ZSMul /
universal-curve multiplication-by-`n` development (with the richer EDS `net` API as a
prerequisite PR), rather than PR-ing the single lemma in isolation.
