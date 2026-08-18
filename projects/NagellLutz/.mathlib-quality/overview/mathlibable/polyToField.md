# /mathlibable report — `WeierstrassCurve.Universal.polyToField`

## Verdict: **NO-composable-from-mathlib**

> `polyToField` is a 2-call composition of mathlib primitives
> (`algebraMap _ _ ∘ CoordinateRing.mk`), specialised to the project-local
> `Universal.curve`. Mathlib already has both building blocks and the function
> field `curve.FunctionField = FractionRing curve.CoordinateRing` (defeq to
> `Universal.Field`). No new mathlib lemma is justified — but the *consumer-side*
> convenience anchor is real, so this is a borderline NO (see Phase 7 note).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source + mathlib tree.
- decl `WeierstrassCurve.Universal.polyToField`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:108`
- kind:                      `def` (noncomputable section)
- has sorry:                 no
- module docstring summary:  Additions to `Affine.Point` + the **universal elliptic curve** over `ℤ[A₁..A₆]`; sets up `Universal.Ring/Field`, the distinguished point `(X,Y)`, and the cusp-curve specialisation used to prove `ψₙ(1,1)=n`.

### Statement (Phase 1)

`polyToField` is the **obvious ring homomorphism from the 7-variable polynomial
ring to the universal field**:
```
polyToField : Poly →+* Universal.Field
polyToField := (algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)
```
where
- `Poly = (MvPolynomial Coeff ℤ)[X][Y] = ℤ[A₁,A₂,A₃,A₄,A₆][X][Y]`,
- `Universal.Ring = curve.CoordinateRing = AdjoinRoot curve.polynomial`
  (`= ℤ[A₁..A₆,X,Y]/⟨P⟩`, `P` the Weierstrass polynomial),
- `Universal.Field = FractionRing Universal.Ring`.

Mathematically: send a 2-variable polynomial over `ℤ[A₁..A₆]` first to its class
in the coordinate ring of the universal Weierstrass curve (quotient by the
Weierstrass relation), then into the fraction field of that coordinate ring (the
**function field** of the universal curve). It is the composite
`quotient-then-localise` structure map `ℤ[A₁..A₆,X,Y] → 𝓞(curve) → Frac 𝓞(curve)`.

- Variables / typeclasses: none free — everything is the fixed project-local
  `Universal.curve : Affine (MvPolynomial Coeff ℤ)`.
- Hypotheses: none.
- Conclusion (math): n/a — definition (a `RingHom`).
- Conclusion (Lean): `Poly →+* Universal.Field`.

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line plumbing `def` — composite of two existing structure maps; not a
named mathematical concept, not a "Main result", not named after a person/place.
(The *surrounding* `Universal.curve` development is BIG infrastructure; this
particular `def` is a SMALL piece of it.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`(algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _`).
One-liner verdict: **ONE-LINER** (`def`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | Not sealed against unfolding — `polyToField_apply` (line 110) is proved by `rfl`, and downstream `simp [polyToField, …]` (lines 143, 146) deliberately unfolds it. So it is *not* a defeq barrier; it is meant to unfold. |
| Avoid typeclass diamonds          | no       | No competing `algebraMap`/instance path; it is a plain `RingHom`, not registered as an `Algebra`/`instance`. |
| Mark semantic intent / API name   | partial  | The *name* is a genuine local-ergonomics win — `ψᵤ`, `smulX/Y`, `smulField`, `point_point`, and ~30 EDS lemmas in `ZSMul.lean` read as `polyToField (curve.ψ n)`. But "convenient name" alone is not a mathlib-inclusion exemption; mathlib would just write the composite or use `CoordinateRing.mk`/`algebraMap`. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the API-name benefit is project-local ergonomics, not a mathlib structural need).

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve coordinate ring function field polynomial ring canonical map to fraction field universal Weierstrass" | yes  | `𝓞(X)=K[x,y]/⟨f⟩`, function field `K(X)=Frac 𝓞(X)`; regular fns `v(X)+Y·w(X)` | Milne *EC2*; Stanford/Purdue function-field notes. The map `poly → 𝓞 → Frac 𝓞` is standard structural plumbing, **unnamed**. |
|  2 | WebSearch (general form)         | "universal Weierstrass curve coordinate ring division polynomials function field ZSMul Junyan Xu mathlib" | partial | mathlib `DivisionPolynomial` describes the **universal ring** `ℤ[A₁..A₆][X,Y]` in prose | The "universal morphism `𝓡[X,Y]→R[X,Y]`" is documented as a *concept* in mathlib's `DivisionPolynomial/Basic.lean` docstring; no `polyToField` name in the literature. |
|  3 | WebSearch (named-after / aliases)| (folded into #1/#2) "function field of elliptic curve" / "structure map quotient localization" | yes  | "function field" / "field of rational functions on the curve" | The codomain is the standard *function field*; the map is the canonical `R[X][Y] → R(W)`. |
|  4 | ChatGPT MCP                      | n/a — MCP flagged down in task brief; substituted with extra WebSearch (#1–#3) + direct mathlib-source reading | n/a | — | Fallback per brief; the standard-form question is fully resolved by the mathlib source itself (it *defines* `FunctionField` and `CoordinateRing.mk`). |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                            | n/a  | (no references dir) | Directory absent. |
|  6 | nLab                             | "function field of a curve" / "coordinate ring"                                                | yes  | `k(C)=Frac(k[C])` | Confirms #1; nLab calls it the function field; the map is the localisation of the structure ring. Nothing named "polyToField". |
|  7 | nCatLab (categorical)            | n/a                                                                                            | n/a  | —                   | Not a categorical concept; it is a concrete ring map. |
|  8 | Stacks Project (alg geom)        | "function field" / "fraction field of coordinate ring"                                          | yes  | function field = `Frac` of the (domain) coordinate ring | Stacks treats it as the generic-point local ring / fraction field; standard, unnamed composite. |
|  9 | MathOverflow / Math.SE           | "function field elliptic curve coordinate ring fraction field"                                  | yes  | same as #1          | Routine background; no special name for the composite `poly→quotient→Frac`. |
| 10 | recent arXiv (last 5 yrs)        | "universal Weierstrass curve" / "elliptic divisibility sequence" + division polynomial          | partial | EDS / division-poly papers use the universal ring `ℤ[a_i][x,y]`; the field is `Frac` of its quotient | Standard tool; nobody names the structure map. |

### Literature summary (Phase 3)

Concept identified as: the **canonical map from the (bivariate) polynomial ring to
the function field of a Weierstrass curve** — i.e. `R[X][Y] → 𝓞(W) = R[X][Y]/⟨W⟩ →
Frac 𝓞(W) = R(W)`, specialised to the universal curve over `ℤ[A₁..A₆]`.
Sources agree on the standard form: **yes** — coordinate ring = quotient by the
Weierstrass polynomial; function field = its fraction field. The composite
quotient-then-localise map is universally used but **never given a proper name**;
it is structural plumbing.
Most general standard form: for any Weierstrass curve `W'` over a commutative ring
`R`, the composite `algebraMap W'.CoordinateRing (FractionRing W'.CoordinateRing) ∘
CoordinateRing.mk W' : R[X][Y] →+* W'.FunctionField`.
Generality dimensions where the literature varies: only the base (the universal
`ℤ[A₁..A₆]` vs a concrete field `K`) — the construction is identical.
Disagreement with the literature: none. The Lean form is the universal-curve
specialisation of the standard structural map.

### Generality analysis — `WeierstrassCurve.Universal.polyToField`

Literature-standard form: `algebraMap W'.CoordinateRing W'.FunctionField ∘
CoordinateRing.mk W'` for an arbitrary `[CommRing R]`, `W' : Affine R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | the curve              | the fixed `Universal.curve` over `MvPolynomial Coeff ℤ` | any `W' : Affine R` over any `[CommRing R]` | **yes** | the body `(algebraMap _ _).comp (AdjoinRoot.mk _)` never uses anything about `curve` — it works verbatim for every `W'`. The proof betrays the right form: `curve` appears 0 times in the body. |
| 2 | codomain               | `Universal.Field = FractionRing curve.CoordinateRing` | `W'.FunctionField = FractionRing W'.CoordinateRing` | n/a (defeq) | mathlib's `FunctionField` *is* this. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (hard-wired to the
universal curve) — *but the general form is a triviality, not a contribution*: it
is the bare composite `algebraMap ∘ CoordinateRing.mk`, both of which mathlib
already exports. Number of weakening opportunities: 1 (the base curve).
Cost of restatement: **CHEAP** (mechanical) — but see Phase 6: the general form is
exactly a 2-call composition, so the right move is *inline it*, not generalise-and-add.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
|  1 | "let X be a foo" → typeclass? | no  | already typeclass-driven (`CommRing R`). | — |
|  2 | sequences/metric → filters? | no  | no analysis here. | — |
|  3 | construct → universal-property class? | no  | this *is* a localisation structure map; `FractionRing`/`IsFractionRing` already carry the universal property in mathlib. | — |
|  4 | set+closure → bundled substructure? | no  | n/a. | — |
|  5 | field/metric-specific → weaken typeclass? | no  | already `CommRing`. | — |
|  6 | 1-categorical → higher? | no  | n/a. | — |
|  7 | concrete index → general algebraic structure? | partial | generalise `curve` → `W'` (Phase 4a row 1) — but this is the composition, not a modernisation. | — |

Modern idiom available: **no** — the modern idiom *already exists in mathlib* as
`CoordinateRing.mk` + `algebraMap`/`FunctionField`. There is nothing to modernise;
`polyToField` is a concrete re-spelling of the already-modern mathlib API.

### Diamond / defeq risk — `polyToField` (Phase 4.5)

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond            | none | plain `RingHom`; not an `instance`/`Algebra`. |
| 2 | Reducibility leak            | none | not `@[reducible]`; sealed `def`, body trivial. |
| 3 | Non-canonical unfolding      | low  | `polyToField_apply`/`simp [polyToField]` unfold it deliberately; intended. |
| 4 | Instance priority collision  | none | not an instance. |
| 5 | Universe issues              | none | monomorphic (`Type 0` throughout). |
| 6 | Coercion ambiguity           | none | no `CoeFun`/`CoeSort`. |

Risk verdict (Phase 4.5): **NONE**. (Not load-bearing here — the verdict is a NO bucket.)

### Mathlib search-status: `WeierstrassCurve.Universal.polyToField`

[A] Lean-Finder       n/a (offline index) — substituted with mathlib-tree grep ([D]).
[B] Loogle            type pattern `_[X][Y] →+* FractionRing _.CoordinateRing` / `RingHom.comp (algebraMap _ _) (AdjoinRoot.mk _)` — **no named decl** is this composite.
[C] LeanSearch        "polynomial ring to function field of Weierstrass curve" — building blocks only.
[D] Grep mathlib src  `.lake/packages/mathlib/Mathlib`: `polyToField` → **0 hits**; `Universal.curve|Universal.Ring|Universal.Field` → **0 hits** (only a *docstring* mention of the "universal ring" in `DivisionPolynomial/Basic.lean:36-38`); `CoordinateRing` → `Affine/Point.lean:90` (`= AdjoinRoot W'.polynomial`); `FunctionField` → `Affine/Point.lean:95` (`= FractionRing W'.CoordinateRing`); `CoordinateRing.mk` → `Affine/Point.lean:111` (`= AdjoinRoot.mk W'.polynomial`); composite `algebraMap … ∘ AdjoinRoot.mk` as a *named* map → **0 hits**.
[E] Name pattern      `polyToField` outside the two project forks → none in mathlib.

Searched both: the user's form (universal curve) **and** the general form
(arbitrary `W'`). Neither the named composite nor the `Universal.curve`
`def`-development is in mathlib.

Concluded: **found the building blocks** —
`WeierstrassCurve.Affine.CoordinateRing.mk` (`Affine/Point.lean:111`),
`algebraMap _.CoordinateRing _.FunctionField` /
`WeierstrassCurve.Affine.FunctionField` (`Affine/Point.lean:95`),
`AdjoinRoot.mk` (`RingTheory/AdjoinRoot.lean:94`),
`IsFractionRing`/`FractionRing` localisation API — **composition yields our form**.
The `Universal.curve` infrastructure itself is project-local (not in mathlib).

### Call sites — `WeierstrassCurve.Universal.polyToField`

Internal use count (NagellLutz, excluding the declaring file): **K = 25+**
External-to-file callers: `LutzNagell/ZSMul.lean` (the entire EDS / ℤ-scalar-mul track).
(Plus an *identical duplicate* `polyToField` in `HasseWeil/Auxiliary/Universal.lean:111`,
with its own ~25 call sites in `HasseWeil/.../DivisionPolynomial.lean` — confirming
this is shared "Universal curve" infra forked into two projects, authored by Junyan Xu.)

| Caller file:line | Usage pattern |
|------------------|---------------|
| ZSMul.lean:132 | `abbrev ψᵤ (n) := polyToField (curve.ψ n)` |
| ZSMul.lean:148 | `polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0` |
| ZSMul.lean:154 | `polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2` |
| ZSMul.lean:164 | `smulX := polyToField (curve.φ n) / (ψᵤ n)^2` |
| ZSMul.lean:168 | `smulY := polyToField (curve.ω n) / (ψᵤ n)^3` |
| ZSMul.lean:411 | `point_point : … = ⟦![polyToField (C X), polyToField Y, 1]⟧` |
| ZSMul.lean:418 | `smulField (n) := polyToField ∘ smulPoly n` |
| …(≈18 more in ZSMul.lean and Universal.lean's own `equation_point`, `pointedCurve_aᵢ`)… | |

Inline-derivation grep: the composite `algebraMap … ∘ AdjoinRoot.mk` is **not**
re-derived raw at call sites — they all go through the `polyToField` name. So `K`
is genuinely high and the name is load-bearing *for the projects*. (This is a
local-API signal, not a mathlib signal — mathlib consumers do not exist.)

### Composition check (Phase 6)

Can `polyToField` be obtained from mathlib in ≤3 chained calls? **Yes — 2 calls.**

`polyToField = (algebraMap Universal.Ring Universal.Field).comp (AdjoinRoot.mk _)`
and mathlib gives both factors directly, with `Universal.Ring = curve.CoordinateRing`,
`Universal.Field = FractionRing curve.CoordinateRing = curve.FunctionField` (defeq):

```lean
-- the whole definition, from mathlib primitives, specialised to `W' := curve`:
example : Poly →+* Universal.Field :=
  (algebraMap curve.CoordinateRing curve.FunctionField).comp (CoordinateRing.mk curve)
-- (CoordinateRing.mk curve  is mathlib's  AdjoinRoot.mk curve.polynomial)
```

- Mathlib decls used: `WeierstrassCurve.Affine.CoordinateRing.mk`,
  `algebraMap`, `WeierstrassCurve.Affine.FunctionField` (= `FractionRing _.CoordinateRing`).
- Result: **succeeds** — `RingHom.comp` of two existing maps; 2 calls, ≤3.
- This matches Phase 6b row "`Foo.bar (Bar.baz hx)` / `.comp` chain" = composable.

Conclusion: **COMPOSABLE**.

---

## Verdict: `WeierstrassCurve.Universal.polyToField`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature (Phase 3): the composite `R[X][Y] → 𝓞(W) → Frac 𝓞(W)` is the standard
  but **unnamed** quotient-then-localise structure map; no "polyToField" concept exists.
- Generality (Phase 4): STRICTLY NARROWER (hard-wired to `Universal.curve`), but the
  general form is itself the trivial 2-map composite — generalising would only
  reproduce mathlib's existing `CoordinateRing.mk` + `algebraMap`.
- Mathlib search (Phase 5): not present as a named map; **building blocks found**
  (`CoordinateRing.mk`, `algebraMap`, `FunctionField`/`FractionRing`).
- Composition (Phase 6): **COMPOSABLE** in 2 mathlib calls.

**Rationale.**
`polyToField` is not a theorem and not a new mathematical object — it is the bare
ring-hom composite `algebraMap _ _ ∘ AdjoinRoot.mk _`, specialised to the project's
fixed `Universal.curve`. Mathlib already exports every piece: the coordinate ring
`W'.CoordinateRing = AdjoinRoot W'.polynomial` with its canonical
`CoordinateRing.mk W' : R[X][Y] →+* W'.CoordinateRing`, the localisation map
`algebraMap`, and the function field `W'.FunctionField = FractionRing
W'.CoordinateRing` — into which `Universal.Field` is *definitionally equal*. The
definition's own body uses nothing about `curve`, so the "general" version is just
the 2-call composite, not a contribution. Mathlib has neither the *named* composite
(grep: 0 hits for `algebraMap … ∘ AdjoinRoot.mk` in `EllipticCurve/`) nor a reason
to want one — it would inline at the (handful of mathlib-internal) call sites.

The one honest tension: locally, the name is load-bearing — `K ≥ 25` uses across
`ZSMul.lean`, plus an identical fork in HasseWeil. But high *project-local* call
count is a local-ergonomics signal, not a mathlib-inclusion signal: mathlib has no
consumers of `polyToField`, and the Phase-2b "API name" exemption explicitly does
not apply to a bare composite that mathlib would just write out (or reach via
`CoordinateRing.mk`/`algebraMap`). This is therefore a *keep-it-local* NO, not a
mathlib gap. The larger `Universal.curve` development around it (which *is* sizeable
infrastructure, and genuinely absent from mathlib) is a separate upstreaming
question — `polyToField` itself rides along as plumbing, not as an independent decl.

**WHY not (refactor-actionable).**
Mathlib has the building blocks; `polyToField` is a 2-call composition. Inline it.

Mathlib building blocks:
- `WeierstrassCurve.Affine.CoordinateRing.mk`
  — `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:111`
  (`= AdjoinRoot.mk W'.polynomial`)
- `WeierstrassCurve.Affine.FunctionField`
  — `…/Affine/Point.lean:95` (`= FractionRing W'.CoordinateRing`; defeq to `Universal.Field`)
- `algebraMap` (the localisation map `_.CoordinateRing → _.FunctionField`)
- `AdjoinRoot.mk` — `.lake/packages/mathlib/Mathlib/RingTheory/AdjoinRoot.lean:94`

Composition sketch (≤3 lines):
```lean
-- equals the current `polyToField` (with curve.FunctionField defeq Universal.Field):
(algebraMap curve.CoordinateRing curve.FunctionField).comp (CoordinateRing.mk curve)
```

Call sites in our project: **K ≥ 25** (NagellLutz `ZSMul.lean` + `Universal.lean`;
a parallel ~25 in HasseWeil).

Refactor plan (judgment-gated — see "Recommendation"): *if* upstreaming, at each of
the K sites replace `polyToField p` with
`(algebraMap curve.CoordinateRing curve.FunctionField).comp (CoordinateRing.mk curve) p`,
or — much better — keep a **one-line project-local abbreviation** (exactly what
this is) and do **not** ship `polyToField` to mathlib. Because K is large and the
composite is verbose, the pragmatic action is: **leave `polyToField` as-is in the
project as local ergonomic sugar; do not add it to mathlib.** It is composable, so
mathlib does not need it; it is heavily used, so the project does.

**Next action:** Do **not** open a mathlib PR for `polyToField`. Keep it as a
project-local one-liner. (Separately, the project may consider switching its
spelling to mathlib's `CoordinateRing.mk curve` to reduce the fork's surface, and
defining `Universal.Field` as `curve.FunctionField` outright — but that is a local
dedup/cleanup task, not a mathlib contribution.) If the broader `Universal.curve`
infrastructure is ever upstreamed as a unit, `polyToField` travels with it as
plumbing — still not as a standalone mathlib decl.
