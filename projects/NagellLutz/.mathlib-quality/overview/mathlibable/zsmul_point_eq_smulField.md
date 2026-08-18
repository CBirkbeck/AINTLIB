# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.zsmul_point_eq_smulField`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief — no `ZSMul.olean` present); decl elaborates per source.
- decl `WeierstrassCurve.Universal.Jacobian.zsmul_point_eq_smulField`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:424`
- namespace nesting:        `namespace WeierstrassCurve` (76) → `namespace Universal` (86) → `namespace Jacobian` (395) … `end Jacobian` (544)
                            ⇒ qualified name **`WeierstrassCurve.Universal.Jacobian.zsmul_point_eq_smulField`**
                            (VERIFIED; matches the module-docstring reference at line 53 `Universal.Jacobian.zsmul_point_eq_smulField`).
- kind:                     theorem
- has sorry:                no
- module docstring summary: "Integer multiples of a rational point on an elliptic curve in terms of division
                            polynomials" — proves the headline `WeierstrassCurve.zsmul_eq_smulEval`
                            (`n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coords). Copyright (c) 2024 **Junyan Xu**
                            (author of mathlib's division-polynomial files).

---

### Statement (Phase 1)

`zsmul_point_eq_smulField` is the **Jacobian (homogeneous) multiplication-by-`n` formula on the universal
Weierstrass curve**, for its distinguished generic point — and per the module docstring (lines 49–56) it is
*the* central universal identity from which the affine form (`zsmul_point_eq_smulX_smulY`) and the field-level
engine (`zsmul_eq_smulEval`) are derived.

Let `Universal.Field = Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y] / ⟨Weierstrass polynomial⟩)` be the universal field, and let
`Jacobian.point = ⟦![X, Y, 1]⟧` be the distinguished generic point on
`curveField = curve.baseChange Universal.Field` in Jacobian coordinates. Let
`smulField n = polyToField ∘ ![curve.φ n, curve.ω n, curve.ψ n] : Fin 3 → Universal.Field` be the triple of
universal division polynomials specialised to the universal field. Then for **every** integer `n` (including
`n = 0`, which gives the point at infinity `⟦![1,1,0]⟧`),

  `(n • Jacobian.point).point = ⟦(φₙ(X,Y), ωₙ(X,Y), ψₙ(X,Y))⟧`,

i.e. the Jacobian coordinates of `n • P` are the homogeneous triple `(φₙ : ωₙ : ψₙ)` of division polynomials.

Variables / typeclasses (Lean side):
- `n : ℤ` — the multiplier. The curve and field are fixed: the *universal* curve over the *universal* field.
- (implicit) `Classical.propDecidable` local instance (line 397).

Hypotheses (Lean side):
- **none.** Unlike the affine twin (which needs `n ≠ 0` to divide by `ψₙ`), the Jacobian/homogeneous form is
  *unconditional* — `n = 0` is handled internally (`φ_zero, ω_zero, ψ_zero` ⟹ `⟦![1,1,0]⟧`), and for `n ≠ 0`
  the point-class equality is proved up to the unit `ψᵤ n⁻¹` via `Jacobian.equiv_iff…`/`Quotient.sound`.

Conclusion (math): `n • (X:Y:1) = (φₙ : ωₙ : ψₙ)` on the universal curve, as point classes in Jacobian coordinates.
Conclusion (Lean): `(n • Jacobian.point).point = ⟦smulField n⟧`  (an equality of `PointClass Universal.Field`).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a named main result of the development — the universal-curve, homogeneous form of the classical
multiplication-by-`n` formula (Silverman III.3.7 / III.6.4(b); Wikipedia "Division polynomials"). It is named in
the module docstring (line 53) as the linchpin (`Universal.Jacobian.zsmul_point_eq_smulField`) from which the two
key identities `dblXYZ (m•P) = (2m)•P` and `addXYZ (m•P) ((m+1)•P) = (2m+1)•P` follow, and hence the headline
`zsmul_eq_smulEval`. (Lit width is EXHAUSTIVE regardless of size.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → n/a. Proof body is a ~12-line argument (case split on `n = 0`,
then `Quotient.sound` with the unit `ψᵤ n⁻¹`, then `fin_cases` over the three coordinates).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                       | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EC mult-by-n Jacobian/projective coords division polys `(φₙ : ωₙ : ψₙ)`                                | yes  | `nP = (φₙψₙ : ωₙ : ψₙ³)` ~ `(φₙ : ωₙ : ψₙ)` | MIT 18.783 Lec 6; Wikipedia; standard homogeneous form. |
|  2 | WebSearch (general / universal)  | universal Weierstrass curve generic point division-poly mult formula φₙ ωₙ ψₙ Silverman                | yes  | universal pt P; `nP=(αₙ(P):βₙ(P):γₙ(P))` over arbitrary ring | **arXiv 1303.4327** — exactly this file's universal-curve route. |
|  3 | WebFetch Wikipedia "Division polynomials" | mult-by-n affine + projective form; `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`; over general field         | yes  | `nP=(φₙ/ψₙ², ωₙ/ψₙ³)`; `φₙ=xψₙ²−ψₙ₋₁ψₙ₊₁` | Verbatim canonical form, "for any field K". |
|  4 | ChatGPT MCP                      | standard homogeneous form + generality + universal-curve route + historical evolution                  | n/a  | (MCP down per task brief; fallbacks used) | Recorded n/a; covered by #1–#3 + #9–#10. |
|  5 | Local references                 | `.mathlib-quality/references/` (and `refs/NagellLutz/`) for division polynomial / mult formula          | n/a  | (no references dir; `refs/` absent)       | Both dirs absent — recorded n/a. |
|  6 | nLab                             | elliptic curve / division polynomials / universal Weierstrass curve                                    | no   | —                                         | nLab EC page omits division polys + the universal-curve multiplication route. |
|  7 | nCatLab (categorical)            | n/a                                                                                                    | n/a  | —                                         | Not a categorical concept (a polynomial coordinate identity). |
|  8 | Stacks Project (alg geom)        | n/a                                                                                                    | n/a  | —                                         | Stacks has no division-polynomial / multiplication-formula entry. |
|  9 | arXiv (homogeneous form)         | "Homogeneous division polynomials for Weierstrass elliptic curves" (1303.4327)                          | yes  | homogeneous αₙ,βₙ,γₙ; universal curve + universal point; `nP=(αₙ:βₙ:γₙ)` over arbitrary ring | The reference for the *exact* Jacobian/homogeneous, universal-ring statement. |
| 10 | recent arXiv (last 5 yrs)        | division polys / EDS recurrence / mult-by-n / Mumford coords (2412.10284), pseudoprimes (1710.05264)   | yes  | same `(φₙ:ωₙ:ψₙ)` form                    | Consistently the canonical homogeneous form. |

Protocol passes: WebSearch ran ≥3 distinct queries at different generality levels (specific homogeneous form;
universal/general; named-after Silverman + Wikipedia canonical); ChatGPT MCP attempted (down per brief, recorded
n/a with fallback coverage); local refs checked (absent); nLab checked; Stacks/nCatLab recorded n/a with reason;
Wikipedia + multiple arXiv (incl. the dedicated 1303.4327 homogeneous-division-polynomials paper) consulted.

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` (`[n]P`) coordinate formula in homogeneous / Jacobian form** for
Weierstrass curves — `nP = (φₙ : ωₙ : ψₙ)` (equivalently `(φₙψₙ : ωₙ : ψₙ³)` after re-homogenising). Classical:
Silverman, *The Arithmetic of Elliptic Curves*, Exercise III.3.7 & Cor III.6.4(b); Wikipedia "Division polynomials".
Sources agree on the standard form: **yes** — with `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁` and `ωₙ` the y-numerator.
Most general standard form: the homogeneous coordinate identity over an **arbitrary ring**, realised via the
**universal Weierstrass curve over `ℤ[A₁,…,A₆,X,Y]`** with its generic point (arXiv 1303.4327) — exactly the form
in this declaration; every field/ring case specialises from it (here via `ringEval`).
Generality dimensions where the literature varies:
  - base: short Weierstrass `y²=x³+Ax+B` (char ≠ 2,3) ↔ general Weierstrass over a field ↔ **universal curve over ℤ**
    (most general; the homogeneous form is what makes the universal/arbitrary-ring statement clean). The decl sits at
    the maximally-general end.
  - coordinates: affine `(φₙ/ψₙ², ωₙ/ψₙ³)` (needs `n ≠ 0`) ↔ homogeneous `(φₙ : ωₙ : ψₙ)` (**unconditional**, includes
    the point at infinity). The decl uses the homogeneous form — the more general of the two.
Disagreement with the literature: **none**. The Lean form matches the canonical homogeneous form exactly.

---

### Generality analysis — `zsmul_point_eq_smulField`

Literature-standard form (from Phase 3): `nP = (φₙ : ωₙ : ψₙ)` homogeneous; deepest = the universal/generic-point
identity over the arbitrary ring `ℤ[A₁,…,A₆,X,Y]` (arXiv 1303.4327).

| # | Parameter / hypothesis | Current Lean form                                  | Literature-standard form                  | Weaker form exists? | Reason |
|---|------------------------|----------------------------------------------------|--------------------------------------------|---------------------|--------|
| 1 | base field/ring        | the *universal field* `Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`    | any field; **universal curve over ℤ**      | NO                  | This *is* the universal (char-0, generic-coefficient) root; the general-field result specialises from it (`ringEval`), and the universal char-0 route is *required* to reach the char-2 field case (docstring 67–71). Cannot be weakened — it is the root. |
| 2 | point                  | the distinguished generic point `⟦![X,Y,1]⟧`       | a general nonsingular point `(x:y:1)`      | n/a (by design)     | The generic point *is* the universal point; specialisation recovers an arbitrary `(x,y)` over any field (`zsmul_eq_smulEval`, same file). |
| 3 | multiplier / index `n` | `n : ℤ`, **no hypothesis on `n`**                  | `n ∈ ℤ` (all `n`, incl. `0`)               | already maximal     | The homogeneous form is *unconditional* (handles `n = 0` ↦ `⟦![1,1,0]⟧`). Strictly more general than the affine twin's `n ≠ 0`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.** It is the universal/generic-point root in homogeneous coordinates, with
*no* hypothesis on `n` — strictly more general than the affine twin (`zsmul_point_eq_smulX_smulY`, which requires
`n ≠ 0`). The general-field result `zsmul_eq_smulEval` is *derived from this* by specialisation.
Number of weakening opportunities found: 0.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | "let X be a foo" → typeclasses? | no  | Already uses `WeierstrassCurve`/`Field` instances; the universal curve is a `def`, the natural anchor; the point is `Jacobian.Point`. | — |
| 2 | sequences/metric → filters/topology? | no  | Purely algebraic identity; no limits/nets. | — |
| 3 | construct → universal-property class? | no  | The universal curve already *is* the universal-property device (generic point over `ℤ[Aᵢ]`); this is the contemporary route (arXiv 1303.4327, and mathlib's own EDS design). | — |
| 4 | set+closure → bundled substructure? | no  | n/a. | — |
| 5 | field/metric-specific → weaken typeclass? | no  | Already universal-field-then-specialise; the homogeneous form is *more* general than the affine one (no `n ≠ 0`). | — |
| 6 | 1-categorical → higher-categorical? | no  | n/a. | — |
| 7 | concrete index → general algebraic? | no  | Index is `ℤ` (the multiplier of a group element); intrinsic, and already covers all of `ℤ`. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is already the contemporary mathlib idiom — universal curve / generic point over
`ℤ[A₁,…,A₆,X,Y]`, EDS-based division polynomials, homogeneous (Jacobian) coordinates. It *extends* mathlib's own
current division-polynomial formulation (same author, Junyan Xu) by supplying the `ωₙ` family and the multiplication
formula that mathlib still lists as a TODO. The homogeneous coordinate form is itself the right modern choice (it is
unconditional in `n` and works over an arbitrary ring), and it is the form the rest of the development needs.

---

### Diamond / defeq risk — n/a (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or instance-search paths introduced.)

---

### Mathlib search-status: `zsmul_point_eq_smulField`

[A] Lean-Finder       (index tool not loaded in this env)        n/a — `lean_leansearch`/Finder unavailable; covered by [D]/[E] over the vendored mathlib tree.
[B] Loogle            (index tool not loaded in this env)        n/a — `lean_loogle` unavailable; covered by [D]/[E].
[C] LeanSearch        (index tool not loaded in this env)        n/a — unavailable; covered by [D]/[E].
[D] Grep mathlib src  over `.lake/packages/mathlib/Mathlib/`:
      • `zsmul_point_eq_smulField | smulField | Universal.Jacobian | zsmul_eq_smulEval` → **no hits** (the entire
        `WeierstrassCurve.Universal` namespace is **absent** from mathlib).
      • `smulPoly | smulRing | polyToField | smulX | smulY | smulEval` → **no hits**.
      • `nsmul | zsmul` in EC `Jacobian/Point.lean` → only `nsmul := nsmulRec`, `zsmul := zsmulRec` (Point.lean:589–590,
        abstract group-law recursion, **not** a coordinate formula).
      • `smul.*=.*⟦ | ⟦.*φ | ⟦.*ψ | n • .*division` in `EllipticCurve/` → only `smul_eq` (Jacobian/Basic.lean:169,
        Projective/Basic.lean:161): the *scaling-invariance* `⟦u•P⟧ = ⟦P⟧`, **not** a multiplication-by-`n` formula.
      • `def ω / ωₙ` in `DivisionPolynomial/` → **only TODO comments** (Basic.lean:71 "TODO: the bivariate
        polynomials `ωₙ`"; :83 "TODO: implementation notes for `ωₙ`"). mathlib defines `ψ`, `φ`, `Ψ₂Sq` but **not** `ωₙ`.
[E] Name pattern      grep `zsmul_point_eq_smulField` across mathlib → **no hits** (only this repo's two forks:
                      NagellLutz + HasseWeil).

Searched for both:
  - user's current form (universal-curve homogeneous `(n • point).point = ⟦smulField n⟧`): **not in mathlib**.
  - literature-standard / general-field form (`nP = (φₙ : ωₙ : ψₙ)`): **not in mathlib** — mathlib's EC `Point`
    `nsmul`/`zsmul` are abstract recursion with **no** division-polynomial coordinate description, and the `ωₙ`
    polynomial the middle coordinate needs is itself an open mathlib TODO.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard general form, plus the
`ωₙ` prerequisite). Mathlib has *some* inputs (`ψₙ`, `φₙ`, EDS `normEDS`/`preNormEDS`) but neither `ωₙ` nor any
multiplication-by-`n` coordinate theorem in any of Affine / Jacobian / Projective.

---

### Call sites — `zsmul_point_eq_smulField`

Internal use count (NagellLutz `ZSMul.lean`, excluding the declaring line 424 and the docstring mention at line 53):
**4** direct downstream uses, all in the same file — and it is the **core node** of the even/odd induction that
proves the headline `zsmul_eq_smulEval`:
- `ZSMul.lean:447` — `nonsingular_smulField` (`(n • Jacobian.point).nonsingular` transported along it).
- `ZSMul.lean:468–469` — `dblXYZ_smulField` (doubling step: `dblXYZ (smulField n) = smulField (2n)`).
- `ZSMul.lean:520–521` — `addXYZ_smulField` (addition step: `addXYZ (smulField n) (smulField (n+1)) = smulField (2n+1)`).
  These two identities are precisely the engine of the even/odd induction proving `zsmul_eq_smulEval`
  (docstring lines 49–56), which itself has ≥10 downstream consumers across NagellLutz `LutzNagellTheorem/*` and HasseWeil.

External-to-file / cross-project: the **identical theorem (statement *and* proof) is duplicated** in HasseWeil at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:490`, where it likewise feeds `nonsingular_smulField`
(525), `dblXYZ_smulField` (553–554) and `addXYZ_smulField` (594–595) — the same 4-use downstream pattern. Both files
describe themselves as a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`.

| Caller file:line                                                  | Usage pattern |
|-------------------------------------------------------------------|---------------|
| NagellLutz/.../ZSMul.lean:447                                     | `nonsingular_smulField` via `simpa [zsmul_point_eq_smulField]` |
| NagellLutz/.../ZSMul.lean:468–469                                 | `dblXYZ_smulField` (doubling identity) |
| NagellLutz/.../ZSMul.lean:520–521                                 | `addXYZ_smulField` (addition identity) |
| HasseWeil/.../Auxiliary/DivisionPolynomial.lean:490,525,553,594   | duplicated copy + its own identical consumers |

Inline-derivation grep: the consuming identities (`dblXYZ_smulField`, `addXYZ_smulField`) genuinely *re-derive*
nothing — they call `zsmul_point_eq_smulField` directly (via `two_zsmul_point_eq_dblXYZ` / `add_point_of_ne_eq_addXYZ`).
So this is a real, load-bearing API node, **and** it is duplicated across two projects — a textbook dedup/upstream
candidate. Not dead code.

Signal reading (per the Phase-6.0.1 table): K = 4 internal uses, no inline re-derivation, **plus** cross-project
duplication → strong YES-* signal.

---

### Composition check (Phase 6)

Can `zsmul_point_eq_smulField` be derived from mathlib in ≤3 chained calls?

Attempt 1: any mathlib lemma giving the Jacobian coordinates of `n • P`?
  - Mathlib decls available: `Jacobian.Point` group structure with `nsmul := nsmulRec`, `zsmul := zsmulRec` (abstract
    recursion, Point.lean:589–590); `smul_fin3`, `equiv_iff_eq_of_Z_eq`, `addMap_eq`, `dblXYZ`/`addXYZ`
    (the homogeneous arithmetic *primitives*); division polynomials `ψ`, `φ` (no `ω`).
  - Result: **fails** — there is no mathlib lemma relating `n • P` to a division-polynomial coordinate triple; the
    formula simply does not exist in mathlib, and `ωₙ` (needed for the middle coordinate) is absent (open TODO).

Attempt 2: build it inline from EDS + the doubling/addition maps?
  - That is exactly the strategy of the surrounding development: even/odd induction with `dblXYZ_smulField` /
    `addXYZ_smulField`, which themselves *consume* `zsmul_point_eq_smulField` (circular as a "composition"). The base
    machinery (`Universal.Ring`/`Field`, `polyToField`, `smulPoly`, the `ωₙ` family in `DivisionPolynomialOmega.lean`,
    and the affine twin `zsmul_point_eq_smulX_smulY`) is multi-hundred-line project-local code, none of it in mathlib.
  - The proof body *itself* (lines 425–435) is short (case split + `Quotient.sound` with unit `ψᵤ n⁻¹` + `fin_cases`),
    but that brevity is only possible because it stands on `Affine.zsmul_point_eq_smulX_smulY hn` (line 429) — the
    ~40-line affine induction — and the whole universal apparatus. It is **not** a 1–3-call mathlib composition.

Conclusion: **NOT-COMPOSABLE.** Deriving this requires the universal-curve + EDS + `ωₙ` + affine-multiplication
apparatus, essentially none of which is in mathlib (notably `ωₙ` and the universal generic-point machinery).

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.zsmul_point_eq_smulField`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): canonical multiplication-by-`n` formula in homogeneous form `nP = (φₙ : ωₙ : ψₙ)` —
  Silverman III.3.7 / III.6.4(b); Wikipedia "Division polynomials"; the universal-ring/homogeneous version is the
  subject of arXiv 1303.4327. Standard, named, undisputed.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — the universal/generic-point root in homogeneous coordinates,
  with *no* hypothesis on `n` (strictly more general than the affine twin). No modern-idiom move (already idiomatic).
- Mathlib search (Phase 5): NOT in mathlib. No coordinate formula for `n • P` in Affine/Jacobian/Projective; the
  prerequisite `ωₙ` is an open mathlib TODO (`DivisionPolynomial/Basic.lean:71,83`).
- Composition check (Phase 6): NOT-COMPOSABLE — needs the universal-curve + EDS + `ωₙ` + affine-multiplication apparatus.

**Rationale:**

This is a classical, named theorem — the homogeneous (Jacobian) multiplication-by-`n` formula on the universal
Weierstrass curve, `n • (X:Y:1) = (φₙ : ωₙ : ψₙ)` (Silverman III.3.7; the universal/arbitrary-ring homogeneous form is
exactly arXiv 1303.4327) — in its maximally-general form, and mathlib does not have it in any form. Mathlib's
elliptic-curve `Point` defines `nsmul`/`zsmul` purely by abstract group-law recursion (`nsmulRec`/`zsmulRec`,
`Jacobian/Point.lean:589–590`); the only `smul`-on-classes lemmas are `smul_eq` (scaling invariance `⟦u•P⟧ = ⟦P⟧`), not
a multiplication-by-`n` description. The very polynomial the middle coordinate needs (`ωₙ`) is an explicit open TODO in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71` (and :83). The whole NagellLutz
`Universal.lean`/`ZSMul.lean`/`DivisionPolynomialOmega.lean` development is Copyright (c) 2024 **Junyan Xu** — the
author of mathlib's own division-polynomial files — and reads as a mathlib-bound development that simply hasn't landed
yet (it supplies `ωₙ`, the universal generic point, and this formula, all extending mathlib's current API).

The strongest single signal is **cross-project duplication**: the identical theorem (statement *and* proof) lives at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:490`, with the same downstream consumers. Two
independent NT developments in this monorepo each re-forked the same machinery — precisely the redundancy mathlib
inclusion eliminates. This decl is the **homogeneous linchpin** the module docstring (line 53) names as the source of
the doubling/addition identities `dblXYZ (m•P) = (2m)•P`, `addXYZ (m•P) ((m+1)•P) = (2m+1)•P`, hence of the headline
`zsmul_eq_smulEval` (≥10 downstream consumers). It is sorry-free, K = 4 internal uses with no inline re-derivation,
maximally general (homogeneous, unconditional in `n`, universal curve over ℤ), and at the right level of abstraction.
This is the Jacobian twin of `zsmul_point_eq_smulX_smulY` (already assessed YES-add-as-is) — and the *more general* of
the pair (the affine form specialises from it).

WHY add it (refactor-actionable):
- **New content mathlib is missing:** the multiplication-by-`n` *coordinate* formula for elliptic curves — there is
  literally no `n • P = (…)` division-polynomial statement anywhere in `Mathlib/AlgebraicGeometry/EllipticCurve/`
  (Affine, Jacobian, or Projective). The homogeneous form here is the cleanest such statement (unconditional in `n`,
  valid over an arbitrary ring), and it is the natural *capstone* of mathlib's existing division-polynomial files.
- **The named gap:** mathlib has `ψₙ`, `φₙ`, `Ψₙ`, `Φₙ` but **not** `ωₙ` and **not** the multiplication formula; the
  decl directly advances the explicit TODOs `DivisionPolynomial/Basic.lean:71` ("the bivariate polynomials `ωₙ`") and
  `:83` ("implementation notes for `ωₙ`"), since the homogeneous formula's middle coordinate *is* the canonical reason
  to define `ωₙ`.
- **Composition with mathlib API:** once added, mathlib's `Jacobian.Point` group law gains an *explicit* homogeneous
  coordinate description of `n • P`, unlocking division-polynomial-based torsion/reduction arguments (Nagell–Lutz,
  Hasse–Weil) that currently each re-derive the apparatus; and `equiv_iff_eq_of_Z_eq`, `dblXYZ`/`addXYZ`, `smul_fin3`
  (already in mathlib) become directly connectable to multiplication-by-`n`.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Multiplication.lean` (a new
file in the existing `DivisionPolynomial/` directory), built on `DivisionPolynomial/Basic.lean` once `ωₙ` lands there,
and on `Jacobian/Point.lean`.

Proposed PR title: `feat(AlgebraicGeometry/EllipticCurve): multiplication-by-n formula in Jacobian coordinates via division polynomials`

PR grouping (REQUIRED — this decl is not a standalone PR): ship as ONE coherent series with the rest of the Junyan-Xu
universal-curve development it depends on / belongs with — the **same PR series** flagged for its affine twin:
  - the `ωₙ` family + `ψc` + `invar` (`DivisionPolynomialOmega.lean`) — fills the mathlib `ωₙ` TODO (prerequisite);
  - the universal curve / generic-point machinery (`Universal.lean`: `curve`, `polyToField`, `Jacobian.point`,
    `ringEval`, `specialize`);
  - **this** Jacobian formula `zsmul_point_eq_smulField` together with its affine sibling
    `zsmul_point_eq_smulX_smulY`, the helper triple `smulPoly`/`smulRing`/`smulField`, `nonsingular_smulField`,
    `dblXYZ_smulField`/`addXYZ_smulField`, and the field-level corollary `WeierstrassCurve.zsmul_eq_smulEval`.
Because the same code is duplicated in HasseWeil, the upstream should be a **shared** mathlib home that both projects
then import and delete their forks of (NagellLutz `ZSMul.lean:424` and HasseWeil `DivisionPolynomial.lean:490`).

Pre-PR checklist before opening:
- [ ] First land `ωₙ` in `DivisionPolynomial/Basic.lean` (closes its own TODO) — hard prerequisite (the middle coordinate).
- [ ] De-duplicate: reconcile the NagellLutz (`ZSMul.lean:424`) and HasseWeil (`DivisionPolynomial.lean:490`) copies
      into the single upstreamed version (they are byte-identical statements; verify the proofs/contexts match).
- [ ] `/generalise WeierstrassCurve.Universal.Jacobian.zsmul_point_eq_smulField` — confirm no further weakening
      (expected: none; it is already the universal homogeneous root, unconditional in `n`).
- [ ] `/cleanup projects/NagellLutz/LutzNagell/ZSMul.lean WeierstrassCurve.Universal.Jacobian.zsmul_point_eq_smulField`
      — full audit (e.g. the `change` at line 430 and the `Quotient.sound`/`fin_cases` block may want tidying for mathlib).
- [ ] Coordinate with Junyan Xu (original author / mathlib division-polynomial maintainer) and pick a reviewer from
      recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits.

---

## Next step

Land the development as a grouped mathlib PR series (prereq: upstream `ωₙ` to close the existing
`DivisionPolynomial/Basic.lean` TODO; then the universal-curve machinery; then this Jacobian multiplication formula +
its affine sibling + the field-level corollary `zsmul_eq_smulEval`). De-duplicate the NagellLutz and HasseWeil copies
into the single upstream home. Run `/generalise` then `/cleanup` on the decl, and coordinate with Junyan Xu as
author/reviewer.
