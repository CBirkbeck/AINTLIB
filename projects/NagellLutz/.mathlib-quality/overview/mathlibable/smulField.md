# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.smulField`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task; reasoning from source, as instructed)
- decl `WeierstrassCurve.Universal.Jacobian.smulField`:  ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:418`
- kind:                      `abbrev` (def-like; one substantive line)
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` in Jacobian coordinates for any integer `n` and nonsingular affine point `P` on a Weierstrass curve over a field, via the universal curve over `ℤ[a₁..a₆,X,Y]/⟨P⟩`.

Qualified name **verified from source**: namespaces nest `WeierstrassCurve` (line 76) → `Universal` (line 86) → `Jacobian` (line 395), decl `smulField` at line 418 ⇒ `WeierstrassCurve.Universal.Jacobian.smulField`. The parsed name in the task was correct.

---

### Statement (Phase 1)

```lean
/-- The three families of division polynomials as elements in the universal field. -/
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n
```
where (lines 414, 416, 418):
```lean
abbrev smulPoly  (n : ℤ) : Fin 3 → Poly           := ![curve.φ n, curve.ω n, curve.ψ n]
abbrev smulRing  (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n
```

`smulField n` is the length-3 coordinate vector `(φₙ, ωₙ, ψₙ)` of the universal division
polynomials of the **universal Weierstrass curve** `curve` (the curve over
`ℤ[A₁,A₂,A₃,A₄,A₆]`, with `φ`, `ω`, `ψ` living in `Poly = ℤ[A₁..A₆,X,Y]`), with every
entry mapped by the canonical ring hom `polyToField : Poly →+* Universal.Field` into the
fraction field `Universal.Field = Frac(ℤ[A₁..A₆,X,Y]/⟨Weierstrass poly⟩)`. It is the
Jacobian-coordinate representative used to state and prove that
`n • Jacobian.point = ⟦(φₙ : ωₙ : ψₙ)⟧` (the very next theorem,
`zsmul_point_eq_smulField`, line 424).

Variables / typeclasses involved (Lean side):
- `n : ℤ` — the multiplier.
- `Universal.Field` — a **fixed, project-specific** type (`Universal.lean:99`), the fraction
  field of the universal coordinate ring; not a type variable, not a mathlib object.
- `polyToField`, `smulPoly`, `curve.{φ,ω,ψ}` — all **project-specific** (`Universal.lean:108`,
  `ZSMul.lean:414`, and the forked `DivisionPolynomial*.lean`).

Hypotheses (Lean side): none — it is a plain definition.

Conclusion (math): the triple `(φₙ, ωₙ, ψₙ) ∈ F³` (`F` = universal field), i.e. the Jacobian
coordinates of `[n]·(X,Y)` on the universal curve.

Conclusion (Lean): n/a — definition; type is `Fin 3 → Universal.Field`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line bundling `abbrev` packaging three already-defined polynomials into a
`Fin 3` vector and post-composing a ring hom; not a named structure, not a `## Main results`
entry, not named after a person. The mathematical content lives in the *theorems about it*
(`zsmul_point_eq_smulField`, `dblXYZ_smulField`, …), not in this definition.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1** substantive line (`polyToField ∘ smulPoly n`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no  | It is an `abbrev` (reducible) — the opposite of a defeq barrier. Proofs throughout (`smulField_zero`, `dblXYZ_smulField`, line 462 `simp only [..., smulField, smulPoly, ...]`) freely unfold it; it is *meant* to unfold. |
| Avoid typeclass diamonds          | no  | No instance is keyed on it; `Fin 3 → Universal.Field` already has all instances from the codomain. |
| Mark semantic intent / API name   | partial | It does carry a docstring and is reused ~12× *inside this one file* — but every consumer is in `ZSMul.lean` (the file that proves the multiplication formula). It is file-local API, not a cross-project surface. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the partial "semantic intent" use is entirely
within the proving file; no external/cross-project consumer depends on the name).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "universal Weierstrass curve division polynomials Jacobian coordinates n-th multiple point formula" | yes | `nP = (αₙ(P) : βₙ(P) : γₙ(P))`, homogeneous `αₙ,βₙ,γₙ ∈ ℤ[a₁..a₆][x,y,z]`, deg `n²`; also affine `[n]P=(φ/ψ², ω/ψ³)` | arXiv 1303.4327 (homogeneous division polys over rings); MIT 18.783. The "universal" ring `ℤ[a₁..a₆,X,Y]` is exactly the project's `Universal.Ring`. |
| 2 | WebSearch (general form) | "elliptic curve multiplication-by-n map division polynomials (φ_n:ω_n:ψ_n) projective/Jacobian coordinates" | yes | `nP = (φₙ : ωₙ : ψₙ)` in Jacobian coords; `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`, `ωₙ` via `ψₙ₊₂ψₙ₋₁²−ψₙ₋₂ψₙ₊₁²` | MIT 18.783 Lec 6 confirms the *triple* `(φₙ:ωₙ:ψₙ)` is the canonical Jacobian-coordinate statement. The bundling is standard *notation*. |
| 3 | WebSearch (named-after / aliases) | "division polynomials elliptic curve triple phi omega psi Cassels Lang naming convention multiplication by n" | yes | φ/ψ/ω are individually named (Cassels 1949; Lang, *Elliptic Curves: Diophantine Analysis* 1978); Wikipedia "Division polynomials" | The three polynomials are standard *named* objects. The *vector packaging* of them is not itself a named object. |
| 4 | ChatGPT MCP | (asked: is the (φ,ω,ψ) bundling a named object; would a library want a named def for the Fin-3 division-poly vector) | n/a | — | Codex/MCP server errored (down, as the task flagged). Question answered from #1–#3 + nLab + source instead. |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` | n/a | — | Directory absent (only `overview/` exists under `.mathlib-quality/`). Recorded n/a. |
| 6 | nLab | "division polynomial" / "elliptic curve multiplication map" | partial | nLab treats division polynomials / torsion only via the individual `ψₙ`; no named "coordinate-triple" object | nLab has no entry bundling `(φ:ω:ψ)` as one object. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; it is a concrete coordinate vector of polynomials. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Stacks does not develop explicit Weierstrass division polynomials / their coordinate vectors. |
| 9 | MathOverflow / MSE | "Motivation for Jacobian coordinates (elliptic curves)" (surfaced under #2) | yes | confirms Jacobian coords `(X:Y:Z)`, `x=X/Z²,y=Y/Z³`; `[n]` convenient there | Supports that `(φ:ω:ψ)` is the natural Jacobian-coordinate triple; no named vector object. |
| 10 | recent arXiv (≤5 yr) | "Division polynomials in Mumford coordinates" (2412.10284); "homogeneous division polynomials" (1303.4327) | yes | Modern treatments still name `φ,ψ,ω`/`αₙ,βₙ,γₙ` individually; the triple is written inline as `(·:·:·)` | No source elevates the triple to a named definition. |

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` map of an elliptic curve in Jacobian
coordinates**, `[n]P = (φₙ : ωₙ : ψₙ)`, built from the classical division polynomials
`ψₙ` and the auxiliary `φₙ`, `ωₙ` (Cassels–Lang; Wikipedia; MIT 18.783; arXiv 1303.4327).
The polynomials live universally in `ℤ[a₁,…,a₆,X,Y]`.

Sources agree on the standard form: **yes** — the individual polynomials `φ,ψ,ω` are
standard named objects, and `(φₙ : ωₙ : ψₙ)` is the standard *way to write* `[n]P` in
Jacobian coordinates.

Most general standard form: the homogeneous triple `(αₙ : βₙ : γₙ)` over the universal ring,
valid for every Weierstrass curve over every ring (arXiv 1303.4327). The project realises
exactly this universal triple as `smulPoly`/`smulField`.

Generality dimensions where the literature varies:
  - **Coordinate model**: affine `(φ/ψ², ω/ψ³)` vs projective/Jacobian `(φ:ω:ψ)` — the project uses Jacobian, matching the homogeneous-triple literature.
  - **Base**: stated over a fixed field, a general ring, or the universal ring — the project uses the universal ring/field (maximal generality), then specialises.

Disagreement with the literature: **none on the math.** Crucial finding for the verdict:
**the *bundling* of `(φₙ, ωₙ, ψₙ)` into one length-3 vector is standard notation, not a named
mathematical object.** No source (Wikipedia, nLab, MIT notes, arXiv) gives the coordinate
*vector* its own definition/name; they name the three polynomials and write the triple inline.

---

### Generality analysis — `WeierstrassCurve.Universal.Jacobian.smulField`

Literature-standard form (Phase 3): the universal homogeneous triple `(φₙ : ωₙ : ψₙ)`,
specialisable to any Weierstrass curve over any commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/more-general form exists? | Reason |
|---|------------------------|-------------------|--------------------------|----------------------------------|--------|
| 1 | curve | the **fixed** universal curve `curve` over `ℤ[A₁..A₆]`; codomain `Universal.Field` hard-wired | the triple for an **arbitrary** `W : WeierstrassCurve R` | yes | The literature object is `(φₙ(W), ωₙ(W), ψₙ(W))` for general `W` over general `R`. `smulField` fixes `W = curve` and the field, so it is the universal *instance* of the general object, not the general object. A mathlib-grade definition would read `def divisionPolynomialTriple (W : WeierstrassCurve R) (n : ℤ) : Fin 3 → R[X][Y] := ![W.φ n, W.ω n, W.ψ n]`. |
| 2 | codomain | `Universal.Field` (one fixed fraction field) | `R[X][Y]` (or any base after a ring map) | yes | `polyToField ∘` bakes in one specific specialisation; the general object lives in the polynomial ring and is transported by *any* ring hom. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (specialised to one fixed
universal curve + one fixed field).
Number of weakening opportunities found: **2** (general curve `W`/ring `R`; general codomain).

Proposed restatement (the only mathlib-shippable form would be the general one):
```lean
namespace WeierstrassCurve
/-- The Jacobian-coordinate triple `(φₙ, ωₙ, ψₙ)` of division polynomials of `W`. -/
noncomputable def divisionPolynomialTriple (W : WeierstrassCurve R) (n : ℤ) :
    Fin 3 → R[X][Y] := ![W.φ n, W.ω n, W.ψ n]
```
Cost of restatement: **CHEAP** as a *definition*, but see Phase 7 — the definition is not
the asset; it is a one-line `![…]` whose only value is the *theorem* `[n]P = ⟦triple⟧`. And
that theorem requires `ω` (not yet in mathlib) plus the whole multiplication-formula proof.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | "let X be a foo" → typeclasses? | no | — | No bundled hypotheses; it is a bare `def`. |
| 2 | sequences/metric → filters/topology? | no | — | Purely algebraic; no limits. |
| 3 | construct an object → universal-property class? | no (subtle) | — | The *curve* is "universal" in the representable-functor sense, but `smulField` is a coordinate vector, not a universal-property carrier; classifying it as a UP class is not a real move. |
| 4 | set+closure-predicate → bundled substructure? | no | — | Not a substructure. |
| 5 | field/metric-specific → weaken typeclass? | yes | state over `R[X][Y]` for `[CommRing R]`, not `Universal.Field` | This is the same generalisation as Phase 4b row 2; it is the literature generalisation, not a separate "modern idiom". |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index → general monoid? | no | — | `n : ℤ` is intrinsic (the EDS index); `ℤ` is correct. |

Modern idiom available: **no** (the only improvement is the literature generalisation already
captured in 4b — there is no distinct Bourbaki-2.0 reformulation that makes a `Fin 3 → R[X][Y]`
vector compose better; it is already a plain vector).

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.Jacobian.smulField`

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | No instance keyed on it; all instances come from the codomain `Fin 3 → Universal.Field`. |
| 2 | Reducibility leak | low | It is `abbrev` (reducible), so its body *is* exposed to defeq everywhere — but that is intentional here (proofs unfold it constantly) and the body is a trivial `![…]∘`. As an `abbrev` it would not even ship to mathlib in this form (mathlib would use `def` + simp lemmas). |
| 3 | Non-canonical unfolding | low | `simp`/`rfl` do unfold it (by design); no surprising rewrite — it just exposes `polyToField (φ/ω/ψ)`. |
| 4 | Instance priority collision | n/a | Not an `instance`. |
| 5 | Universe issues | none | Everything is in `Type`; no universe polymorphism. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (reducibility-exposure only; irrelevant since the decl would not ship
as an `abbrev` and would not ship in its fixed-curve form at all).

---

### Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.smulField`

[A] Lean-Finder       — (mathlib index search) — no decl bundling division polynomials into a Fin 3 vector
[B] Loogle            `Fin 3 → ?`, `_ ∘ ![_, _, _]` over `WeierstrassCurve` — no hits for a division-polynomial coordinate triple
[C] LeanSearch        "division polynomials as a vector / triple in Jacobian coordinates", "n times point equals division polynomial triple" — no hits
[D] Grep mathlib src  `grep -rn "smulField|smulPoly|smulRing"` over `.lake/packages/mathlib/Mathlib` → **0 hits**; `grep "namespace Universal"` in `EllipticCurve` → **0 hits** (no `WeierstrassCurve.Universal` in mathlib at all); `DivisionPolynomial/{Basic,Degree}.lean` define `preΨ, Ψ, ΨSq, Φ` individually and **no `ω`** and **no coordinate vector**
[E] Name pattern      `smulField`, `smulPoly`, `divisionPolynomialTriple`, `jacobianCoordinates` over mathlib → no match

Searched for both:
  - user's current form (`smulField` over the fixed universal curve) — **not in mathlib**
  - literature-standard form (general `(φₙ:ωₙ:ψₙ)` triple for any `W`) — **not in mathlib**

Concluded: **not in mathlib (all 5 methods exhausted, plus the literature-standard form).**
Mathlib lacks even the prerequisites: there is no `WeierstrassCurve.Universal` construction,
no `polyToField`, and crucially **no `W.ω`** (the second division polynomial) — that is added
by this project in `DivisionPolynomialOmega.lean`. Mathlib has only the individual `Ψ`/`Φ`.

---

### Call sites — `WeierstrassCurve.Universal.Jacobian.smulField`

Internal use count (this project, excluding the declaring file): **0**.
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none outside `ZSMul.lean`) | — |

All ~12 uses of `smulField` are **inside `ZSMul.lean` itself** (lines 420, 424–528: the
`zsmul_point_eq_smulField`, `nonsingular_smulField`, `smulField_neg/zero`,
`dblXYZ_smulField`, `addXYZ_smulField(₁)` cluster). The HasseWeil project has its **own
independent copy** (`HasseWeil/Auxiliary/DivisionPolynomial.lean:484`) — it does *not* import
this one (confirming both are file-local helpers, duplicated rather than shared).

Inline-derivation grep: the equivalent `![curve.φ n, curve.ω n, curve.ψ n]` packaging is
re-created in HasseWeil's fork rather than imported — i.e. consumers re-derive it locally.

Call-sites signal (per the Phase-6 table): **K = 0 external + same statement re-derived in
another project ⇒ NO-composable** leaning: it is a file-local bundling that other developments
bypass.

---

### Composition check (Phase 6)

Can `smulField n` be produced from mathlib in ≤3 calls? The *definition* is literally a
3-call composition already:
```lean
-- given W.φ, W.ω, W.ψ in scope:
fun n => polyToField ∘ ![curve.φ n, curve.ω n, curve.ψ n]
```
Attempt 1: `polyToField ∘ ![curve.φ n, curve.ω n, curve.ψ n]`
  - Building blocks used: `Matrix.of`/`![·,·,·]` (mathlib), `Function.comp` (core), plus the
    *project* objects `curve.φ/ω/ψ` and `polyToField`.
  - Result: **succeeds trivially** — it is the body verbatim. The only non-mathlib pieces are
    `curve.{φ,ω,ψ}` and `polyToField`, which are this project's own definitions (and `ω` is a
    project addition not in mathlib).
  - Notes: there is nothing to *prove*; it is a notation-level packaging.

Conclusion: **COMPOSABLE** (the definition is a 1-line `![…]` + `∘`; no lemma content).

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.smulField`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the bundling `(φₙ,ωₙ,ψₙ)` is *standard notation*, never a named
  object; the named objects are the individual `φ,ψ,ω` (Cassels–Lang, Wikipedia, MIT 18.783).
- Generality analysis (Phase 4): **STRICTLY NARROWER** — fixed to one universal curve + one
  fixed field; the only mathlib-grade form would be a general `divisionPolynomialTriple W n`.
- Mathlib search (Phase 5): **not in mathlib** in any form; mathlib lacks even `W.ω` and the
  whole `Universal` construction.
- Composition check (Phase 6): **COMPOSABLE** — the body is a trivial `![…] ∘`.

**Rationale:**

`smulField` is a one-line, reducible `abbrev` that packages three objects (`curve.φ n`,
`curve.ω n`, `curve.ψ n`) into a `Fin 3` vector and post-composes the ring map `polyToField`.
It is defined only for the single fixed *universal* curve and the single fixed field
`Universal.Field`, and every one of its ~12 uses is inside the very file that proves the
multiplication-by-`n` formula; no other file in the project (and not even the sibling HasseWeil
copy) imports it. The literature is unambiguous that while `[n]P = (φₙ:ωₙ:ψₙ)` is the standard
Jacobian-coordinate statement, the coordinate *vector itself* is notation — no source gives it a
name or a definition. So there is no "right general object" hiding here that mathlib is missing:
the genuinely-standard objects are the individual division polynomials (`Φ`, `Ψ` already in
mathlib's `DivisionPolynomial/Basic.lean`; `ω` is the real project contribution, assessed
separately) and the *theorem* `zsmul_point_eq_smulField`. `smulField` is the throwaway local
glue between them.

It lands in **NO-composable-from-mathlib** rather than NO-mathlib-has-it (mathlib has no
`smulField`, no `Universal`, no `ω`) and rather than any YES bucket (it is a one-liner with no
Phase-2b exemption, `K=0` external call sites, STRICTLY-NARROWER generality, and — fatally — it
is built from project-local objects, so mathlib literally cannot host *this* decl; the only
mathlib-eligible thing in its vicinity is a general `divisionPolynomialTriple`, which is itself a
trivial `![W.φ n, W.ω n, W.ψ n]` whose worth is entirely parasitic on the `ω`-development and the
multiplication theorem that are tracked as their own decls).

**WHY not (refactor-actionable):**
- Mathlib has the *building blocks* for the only sensible general version: `![·,·,·]`
  (`Matrix.cons`/`!`-notation), `Function.comp`, and the individual division polynomials
  `WeierstrassCurve.Φ` / `WeierstrassCurve.Ψ` in
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`. It does **not** have
  `W.ω`, `WeierstrassCurve.Universal`, or `polyToField` — all project-local. So `smulField` is
  not a missing mathlib lemma; it is one-line project glue.
- Mathlib building blocks: `Matrix.cons` / `![…]` notation, `Function.comp`,
  `WeierstrassCurve.Φ`, `WeierstrassCurve.Ψ` (all in `DivisionPolynomial/Basic.lean`).
- Composition sketch (≤3 lines): the body itself —
  ```lean
  fun n => polyToField ∘ ![curve.φ n, curve.ω n, curve.ψ n]
  ```
- Call sites in this project (Phase 6.0): **K = 0** outside the declaring file.
- Refactor plan: keep `smulField` exactly as is — it is correct, harmless file-local glue and
  there is nothing to inline at call sites (the call sites are all in `ZSMul.lean`). The action
  for **mathlib** is: do **not** upstream `smulField`. If/when the multiplication-by-`n`
  Jacobian-coordinate formula and `W.ω` are upstreamed (those are the real contributions), state
  them with a general `WeierstrassCurve.divisionPolynomialTriple W n := ![W.φ n, W.ω n, W.ψ n]`
  defined for an arbitrary `W : WeierstrassCurve R`, declared `private`/local unless a downstream
  mathlib lemma actually reuses the vector. The fixed-universal-curve `smulField` should stay in
  the project.

**Next action:** Do not upstream `smulField`. It stays in `ZSMul.lean` as local glue. Route any
mathlib effort to (a) `W.ω` (`DivisionPolynomialOmega.lean`) and (b) the multiplication-by-`n`
theorem `zsmul_point_eq_smulField`; if those go up, introduce the general
`divisionPolynomialTriple` there (not this fixed specialisation).

---

## Next step

Do not upstream `smulField`. It stays in `ZSMul.lean` as file-local glue (it is correct and
used only internally). Direct mathlib effort instead at the real contributions in its vicinity —
the omega division polynomial `W.ω` and the multiplication-by-`n` Jacobian formula
`zsmul_point_eq_smulField` — and, only there, state the coordinate vector in its general form
`divisionPolynomialTriple W n := ![W.φ n, W.ω n, W.ψ n]` for arbitrary `W`.
