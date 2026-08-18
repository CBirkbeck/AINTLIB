# /mathlibable report — `WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); decl elaborates per source.
- decl `WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:344`
- namespace nesting:        `namespace WeierstrassCurve` (76) → `namespace Universal` (86) → `namespace Affine` (157)
                            ⇒ qualified name **`WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY`** (matches the
                            module-docstring reference at line 59).
- kind:                     theorem
- has sorry:                no
- module docstring summary: "Integer multiples of a rational point on an elliptic curve in terms of division
                            polynomials" — proves `WeierstrassCurve.zsmul_eq_smulEval` (`[n]P` in division-polynomial
                            coordinates). Copyright (c) 2024 **Junyan Xu** (author of mathlib's division-polynomial files).

---

### Statement (Phase 1)

`zsmul_point_eq_smulX_smulY` is the **affine multiplication-by-`n` formula on the universal Weierstrass
curve**, stated for its distinguished generic point.

Let `Universal.Field = Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y] / ⟨Weierstrass polynomial⟩)` be the universal field, and let
`point = (X, Y)` be the distinguished (generic) point on `curveField = curve.baseChange Universal.Field`. Write
`ψᵤ n = polyToField (curve.ψ n)`, `smulX n = polyToField (curve.φ n) / ψᵤ n ²`, and
`smulY n = polyToField (curve.ω n) / ψᵤ n ³`. Then for every nonzero integer `n`, the scalar multiple `n • point`
is a nonsingular affine point whose coordinates are `(smulX n, smulY n)` — i.e.
`n • (X,Y) = (φₙ(X,Y)/ψₙ(X,Y)², ωₙ(X,Y)/ψₙ(X,Y)³)`.

Variables / typeclasses (Lean side):
- `n : ℤ` — the multiplier (the curve/field are fixed: the *universal* curve over the *universal* field).

Hypotheses (Lean side):
- `n ≠ 0` — required so `ψᵤ n ≠ 0` and the divisions are defined (and `n • point ≠ O`).

Conclusion (math): `n • point = (φₙ/ψₙ², ωₙ/ψₙ³)`, and this point is nonsingular.
Conclusion (Lean): `∃ h : Affine.Nonsingular _ (smulX n) (smulY n), n • Affine.point = .some _ _ h`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a named main result of the development (the universal-curve form of the multiplication-by-`n`
formula, Silverman III.3.7 / III.6.4(b)), explicitly listed in the module docstring as the affine engine of the
file, and is a theorem of a classical, literature-standard fact.

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → n/a. Proof body is a ~40-line even/odd + strong induction.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | elliptic curve mult-by-n: x = φₙ/ψₙ², y = ωₙ/ψₙ³                                                       | yes  | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`        | Multiple arXiv sources state exactly this; standard. |
|  2 | WebSearch (general form)         | mathlib EC division polynomials mult-by-n nsmul ω TODO                                                  | yes  | same; ψₙ²,ψ₂ₙ/y,φₙ ∈ K[x]        | Confirms form is canonical over a general field K. |
|  3 | WebSearch (named-after / source) | Silverman Arithmetic of Elliptic Curves Exercise III.3.7 / Cor III.6.4(b)                              | yes  | `y(nP)=ωₙ/ψₙ³` (Silverman)        | The canonical textbook reference; explicitly Exercise III.3.7. |
|  4 | ChatGPT MCP                      | standard form + generality + universal-curve route                                                     | n/a  | (MCP down — Codex exec failed)    | Recorded n/a; covered by #1–#3 + #9. |
|  5 | Local references                 | `.mathlib-quality/references/` for division polynomial / mult formula                                  | n/a  | (no references dir for project)   | dir absent. |
|  6 | nLab                             | elliptic curve / division polynomials                                                                  | no   | —                                 | nLab EC page omits division polys + universal-curve approach. |
|  7 | nCatLab (categorical)            | n/a                                                                                                    | n/a  | —                                 | Not a categorical concept. |
|  8 | Stacks Project (alg geom)        | n/a                                                                                                    | n/a  | —                                 | Stacks has no division-polynomial / mult-formula entry. |
|  9 | WebFetch Wikipedia               | "Division polynomials" — multiplication-by-n formula                                                    | yes  | `nP=(φₙ/ψₙ², ωₙ/ψₙ³)`            | Verbatim canonical form, "stated over a general field K". |
| 10 | recent arXiv (last 5 yrs)        | division polynomials / EDS recurrence / mult-by-n                                                       | yes  | same form                         | 1108.3051, 2102.07573, 1909.12654, etc. all use this form. |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (specific form, mathlib/general,
named-after Silverman); ChatGPT MCP attempted (down, recorded n/a); local refs checked (absent); nLab checked;
Stacks/nCatLab recorded n/a with reason; Wikipedia + arXiv consulted.

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` (a.k.a. division-polynomial / `[n]P`) coordinate formula** for
elliptic / Weierstrass curves — Silverman, *The Arithmetic of Elliptic Curves*, Exercise III.3.7 & Cor III.6.4(b).
Sources agree on the standard form: **yes** — `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` with `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`.
Most general standard form: the rational-function identity over a general field; the deepest underlying statement is
the *universal* one over the ring `ℤ[A₁,…,A₆,X,Y]` (generic point), from which every field case specializes.
Generality dimensions where the literature varies:
  - base field: short Weierstrass `y²=x³+Ax+B` (char ≠ 2,3) ↔ general Weierstrass over any field ↔ **universal curve
    over ℤ** (most general). The user's decl is the universal form — the maximally-general end.
Disagreement with the literature: none. The Lean form matches the canonical form exactly.

---

### Generality analysis — `zsmul_point_eq_smulX_smulY`

Literature-standard form (from Phase 3): `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; deepest form = the universal/generic-point
identity over `ℤ[A₁,…,A₆,X,Y]`.

| # | Parameter / hypothesis | Current Lean form                                  | Literature-standard form            | Weaker form exists? | Reason |
|---|------------------------|----------------------------------------------------|--------------------------------------|---------------------|--------|
| 1 | base field/ring        | the *universal field* `Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`    | any field; universal curve over ℤ    | NO                  | This *is* the universal (char-0, generic-coefficient) curve — the maximally general base from which all fields specialize. Cannot be weakened further; it is the root. |
| 2 | point                  | the distinguished generic point `(X,Y)`            | a general nonsingular point `(x,y)`  | n/a (by design)     | The generic point *is* the universal point; specialization (`ringEval`) recovers the formula for an arbitrary `(x,y)` over any field — done in this same file as `zsmul_eq_smulEval`. |
| 3 | `n ≠ 0`                | `n ≠ 0`                                            | `n ≠ 0` (so ψₙ ≠ 0)                  | NO                  | Genuinely needed: the divisions and `n•P ≠ O` require it. Standard hypothesis. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is the universal/generic-point root form; the general-field version
`zsmul_eq_smulEval` is *derived from this machinery* by specialization, and the module docstring at lines 67–71
explains the universal char-0 route is *required* to reach the characteristic-2 field case).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | "let X be a foo" → typeclasses? | no  | Already uses `WeierstrassCurve`/`Field`/`IsElliptic` instances; the universal curve is a `def`, the natural anchor. | — |
| 2 | sequences/metric → filters/topology? | no  | Purely algebraic identity; no limits. | — |
| 3 | construct → universal-property class? | no  | The universal curve already *is* the universal-property device here (generic point over ℤ[Aᵢ]). | — |
| 4 | set+closure → bundled substructure? | no  | n/a. | — |
| 5 | field/metric-specific → weaken typeclass? | no  | Stated over the universal field on purpose; the field-level corollary is the specialization, already present. | — |
| 6 | 1-categorical → higher-categorical? | no  | n/a. | — |
| 7 | concrete index → general algebraic? | no  | Index is `ℤ` (the multiplier of a group element); that is intrinsic. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is already the contemporary mathlib idiom (universal curve / generic point over
`ℤ[A₁,…,A₆,X,Y]`, EDS-based division polynomials) — indeed it *extends* mathlib's own current division-polynomial
formulation by the same author (Junyan Xu), supplying the `ωₙ` family that mathlib still lists as a TODO.

---

### Diamond / defeq risk — n/a (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or instance-search paths introduced.)

---

### Mathlib search-status: `zsmul_point_eq_smulX_smulY`

[A] Lean-Finder       (tool unavailable in env)                 n/a — index tool not loaded
[B] Loogle            (tool unavailable in env)                 n/a — index tool not loaded
[C] LeanSearch        (tool unavailable in env)                 n/a — index tool not loaded
[D] Grep mathlib src  `smulX/smulY/smulEval/zsmul_point/coord∘nsmul` over `.lake/.../Mathlib/`   → **no hits**
                      `nsmul/zsmul` in EC `Affine/Point.lean` + `Jacobian/Point.lean`  → only `nsmulBinRec`/`zsmulRec`
                      (abstract group-law recursion, NOT a coordinate formula)
                      `def ω / omega` in `Mathlib/.../DivisionPolynomial/`  → **no hits** (mathlib lacks `ωₙ`;
                      `DivisionPolynomial/Basic.lean:71` reads "TODO: the bivariate polynomials `ωₙ`")
[E] Name pattern      grep for `zsmul_point_eq_smulX_smulY` in mathlib  → **no hits** (only in this repo's two forks)

Searched for both:
  - user's current form (universal-curve `n • point = (smulX n, smulY n)`): not in mathlib.
  - literature-standard / general-field form (`[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`): not in mathlib — mathlib's EC `Point`
    `nsmul`/`zsmul` are defined by abstract recursion with **no division-polynomial coordinate formula**, and the
    `ωₙ` polynomial the y-coordinate needs is itself absent (an open TODO).

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard general form, plus the
prerequisite `ωₙ`). Mathlib has the *building blocks for the inputs* (ψₙ, φₙ, EDS) but neither `ωₙ` nor any
multiplication-by-`n` coordinate theorem.

---

### Call sites — `zsmul_point_eq_smulX_smulY`

Internal use count (NagellLutz, excluding declaring lines): **2** direct, both in the same file:
- `ZSMul.lean:386` — `nonsingular_smulX_smulY (hn) := (zsmul_point_eq_smulX_smulY hn).1`
- `ZSMul.lean:390` — `Affine.zsmul_point_ne_zero` (the generic point is non-torsion) → in turn feeds
  `Jacobian.zsmul_point_ne_zero` (402) → `Jacobian.zsmul_point_ne` (407, "distinct multiples are distinct").
- `ZSMul.lean:429` — `Affine.zsmul_point_eq_smulX_smulY hn` (further internal use).

External-to-file / cross-project: the **entire theorem is duplicated** in HasseWeil at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:415` (verbatim statement + proof), where it likewise
feeds `zsmul_point_ne_zero` (540) consumed across the Hasse–Weil development.

| Caller file:line                                        | Usage pattern |
|---------------------------------------------------------|---------------|
| NagellLutz/.../ZSMul.lean:386                           | `(zsmul_point_eq_smulX_smulY hn).1` (nonsingularity) |
| NagellLutz/.../ZSMul.lean:390, :429                     | non-torsion of the generic point |
| HasseWeil/.../Auxiliary/DivisionPolynomial.lean:415,459,495 | duplicated copy + its own consumers |

Inline-derivation grep: the *field-level* result `zsmul_eq_smulEval` (ZSMul.lean:590) is proved by an **independent**
even/odd induction in Jacobian coordinates (via `dblXYZ_smulEval`/`addXYZ_smulEval₁`), and `zsmul_eq_smulEval` is the
heavily-used downstream node (≥10 call sites across HasseWeil + NagellLutz `LutzNagellTheorem/*`). So
`zsmul_point_eq_smulX_smulY` is the *affine* sibling of that engine, not on its critical path — but it is the
canonical affine statement and is the one cited by name in the module docstring as the affine goal.

Signal reading: real API node (non-zero internal uses, feeds the non-torsion lemmas), **and duplicated across two
projects** — a textbook dedup/upstream candidate. Not dead code.

---

### Composition check (Phase 6)

Can `zsmul_point_eq_smulX_smulY` be derived from mathlib in ≤3 chained calls?

Attempt 1: any mathlib lemma giving coordinates of `n • P`?
  - Mathlib decls available: `WeierstrassCurve.Affine.Point` group structure with `nsmul := nsmulBinRec`,
    `zsmul := zsmulRec` (abstract recursion); division polynomials `ψ`, `φ` (no `ω`).
  - Result: **fails** — there is no mathlib lemma relating `n • P` to division-polynomial coordinates; the
    coordinate formula simply does not exist in mathlib, and `ωₙ` (needed for the y-coordinate) is absent.

Attempt 2: build it from EDS + addition formulas inline?
  - That is exactly the ~40-line even/odd-induction proof in this file (`smulX_add`, `smulY_add_sub_negY`,
    `Affine.addX_eq_addX_negY_sub`, …), several of which are themselves project-local lemmas building on the forked
    EDS/division-polynomial files. This is a genuine multi-lemma proof, not a 1–3-call composition.

Conclusion: **NOT-COMPOSABLE**. Deriving this requires the whole universal-curve + EDS + addition-formula apparatus,
most of which is not yet in mathlib (notably `ωₙ` and the universal generic-point machinery).

---

## Verdict: `WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): canonical multiplication-by-`n` formula `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` — Silverman
  III.3.7 / III.6.4(b); Wikipedia "Division polynomials"; multiple arXiv. Standard, named, undisputed form.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — this is the universal/generic-point root; the general-field
  result specializes from it (and the universal char-0 route is *required* to reach char 2). No modern-idiom move.
- Mathlib search (Phase 5): NOT in mathlib. No coordinate formula for `n • P`; the prerequisite `ωₙ` is an open
  mathlib TODO.
- Composition check (Phase 6): NOT-COMPOSABLE — needs the universal-curve + EDS + addition-formula apparatus.

**Rationale:**

This is a classical, named theorem (the affine multiplication-by-`n` formula on the universal Weierstrass curve —
Silverman III.3.7) in its maximally-general form, and mathlib does not have it in any form. Mathlib's elliptic-curve
`Point` defines `nsmul`/`zsmul` purely by abstract group-law recursion (`nsmulBinRec`/`zsmulRec`); there is no lemma
connecting `n • P` to division-polynomial coordinates, and the very polynomial the y-coordinate needs (`ωₙ`) is an
explicit open TODO in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71`. The whole NagellLutz
`Universal.lean`/`ZSMul.lean` development is Copyright (c) 2024 **Junyan Xu** — the author of mathlib's own
division-polynomial files — and reads as a mathlib-bound development that simply hasn't landed yet (it supplies `ωₙ`,
the universal generic-point, and this formula, all of which extend mathlib's current division-polynomial API).

The strongest single signal is **cross-project duplication**: the identical theorem (statement *and* proof) lives at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:415`, where both files openly describe themselves as
"a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`". Two independent NT developments in this
monorepo each had to re-fork the same machinery — precisely the redundancy mathlib inclusion eliminates. The decl is a
real API node (it powers the non-torsion-of-the-generic-point lemmas, and its Jacobian sibling `zsmul_eq_smulEval` has
≥10 downstream consumers). It is sorry-free, maximally general, and at the right level of abstraction.

WHY add it (refactor-actionable):
- **New content mathlib is missing:** the multiplication-by-`n` coordinate formula for elliptic curves — there is
  literally no `n • P = (…)` division-polynomial statement in `Mathlib/AlgebraicGeometry/EllipticCurve/`. It directly
  advances the named gap `DivisionPolynomial/Basic.lean:71` ("TODO: the bivariate polynomials `ωₙ`") and the
  implementation-notes TODO at line 83, since the formula's y-coordinate is the canonical *reason* to define `ωₙ`.
- **The named gap:** mathlib has ψₙ, φₙ, Ψₙ, Φₙ but not ωₙ and not the mult-formula; the universal-curve approach in
  this file is the idiomatic way (matching mathlib's existing EDS-based design) to supply both.
- **Composition with mathlib API:** once added, mathlib's `EllipticCurve.Point` group law gains an *explicit*
  coordinate description of `n • P`, unlocking division-polynomial-based torsion/reduction arguments (Nagell–Lutz,
  Hasse–Weil via `zsmul_eq_smulEval`) that currently each re-derive the apparatus.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Multiplication.lean` (a new
file in the existing `DivisionPolynomial/` directory), built on `DivisionPolynomial/Basic.lean` once `ωₙ` lands there.
The natural unit is the **whole development**, not this one theorem alone.

Proposed PR title: `feat(AlgebraicGeometry/EllipticCurve): multiplication-by-n formula via division polynomials`

PR grouping (REQUIRED — this decl is not a standalone PR): ship as one coherent series with the rest of the Junyan-Xu
universal-curve development it depends on / belongs with —
  - the `ωₙ` family + `ψc` + `invar` (`DivisionPolynomialOmega.lean`) — fills the mathlib `ωₙ` TODO;
  - the universal curve / generic point machinery (`Universal.lean`);
  - the field-level corollary `WeierstrassCurve.zsmul_eq_smulEval` (Jacobian form) and its affine sibling
    `zsmul_point_eq_smulX_smulY` (this decl), plus `nonsingular_smulX_smulY`, `zsmul_point_ne_zero`,
    `zsmul_point_ne`.
Because the same code is duplicated in HasseWeil, the upstream should be a **shared** mathlib home that both projects
then import and delete their forks of.

Pre-PR checklist before opening:
- [ ] First land `ωₙ` in `DivisionPolynomial/Basic.lean` (closes its own TODO) — prerequisite.
- [ ] De-duplicate: reconcile the NagellLutz and HasseWeil copies into the single upstreamed version.
- [ ] `/generalise WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY` — confirm no further weakening
      (expected: none; it is already the universal root).
- [ ] `/cleanup projects/NagellLutz/LutzNagell/ZSMul.lean WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY`
      — full audit (the `erw` usages at 354/363 and `change` at 304 may want tidying for mathlib).
- [ ] Coordinate with Junyan Xu (original author / mathlib division-polynomial maintainer) and pick a reviewer from
      recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits.

---

## Next step

Land the development as a grouped mathlib PR series (prereq: upstream `ωₙ` to close the existing
`DivisionPolynomial/Basic.lean` TODO; then the universal-curve machinery; then this multiplication formula + its
field-level corollary `zsmul_eq_smulEval`). De-duplicate the NagellLutz and HasseWeil copies into the single upstream
home. Run `/generalise` then `/cleanup` on the decl, and coordinate with Junyan Xu as author/reviewer.
