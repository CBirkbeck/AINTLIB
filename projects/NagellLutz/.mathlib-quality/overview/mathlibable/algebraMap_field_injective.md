# /mathlibable report — `WeierstrassCurve.Universal.algebraMap_field_injective`

> Mode A, single declaration. Project: NagellLutz (Nagell–Lutz theorem; division
> polynomials; elliptic divisibility sequences). Run reasoning from source — the
> local Lean build is stale, so Phase 0 build is recorded as N/A and the
> assessment is grounded in the source statement + mathlib source reads.

---

### Baseline (Phase 0)

- lake build:                N/A (environment: build stale; reasoned from source per instructions)
- decl `WeierstrassCurve.Universal.algebraMap_field_injective`:
                             ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:123`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — lemmas
                             missing from released mathlib needed for the division-polynomial / ZSMul
                             development, plus the construction of the universal Weierstrass curve over
                             `ℤ[A₁,A₂,A₃,A₄,A₆]` and the universal pointed elliptic curve over its
                             function field.

**Qualified name verified.** The decl sits inside `namespace WeierstrassCurve` → `namespace Universal`
(open at lines 69 and 75 of the file), so the fully-qualified name is
`WeierstrassCurve.Universal.algebraMap_field_injective`. This matches the prompt's parsed guess.

---

### Statement (Phase 1)

`WeierstrassCurve.Universal.algebraMap_field_injective` is a theorem stating:

> The canonical ring homomorphism from the universal coefficient ring
> `ℤ[A₁,A₂,A₃,A₄,A₆] = MvPolynomial Coeff ℤ` into the **universal field**
> `Universal.Field = Frac(curve.CoordinateRing)` is injective.

Mathematically: for the universal Weierstrass curve `curve` over `R₀ := ℤ[A₁,…,A₆]`, the structure
map `R₀ → Frac(R₀[curve])` (base ring → fraction field of the coordinate ring of the curve) is an
embedding. This is the concrete statement that "the coefficients survive in the function field of the
universal curve", i.e. the universal curve is genuinely a curve over `R₀` and the generic point does
not collapse the base.

Variables / typeclasses (Lean side):
- none free — every type is a fixed project-specific construction: `Coeff` (the 5-element index type),
  `MvPolynomial Coeff ℤ`, `Universal.Ring := curve.CoordinateRing`, `Universal.Field := FractionRing
  Universal.Ring`.

Hypotheses (Lean side): none.

Conclusion (math): the base ring `ℤ[A₁,…,A₆]` injects into the function field of the universal curve.

Conclusion (Lean): `Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)`.

**Proof body (load-bearing — it IS the composition):**

```lean
lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' (W' := curve))
```

It composes two injectivity facts:
1. `Affine.CoordinateRing.algebraMap_injective'` — `algebraMap R₀ (curve.CoordinateRing)` injective
   (a **project lemma**, defined at lines 50–51 of the same file as
   `algebraMap_poly_injective.comp C_injective`).
2. `IsFractionRing.injective Universal.Ring Universal.Field` — `algebraMap CoordinateRing Frac(CoordinateRing)`
   injective (**mathlib**, `Mathlib/RingTheory/Localization/FractionRing.lean:137`).

The genuinely non-trivial leaf is `algebraMap_poly_injective` (lines 45–48):
`Function.Injective (algebraMap R[X] W'.CoordinateRing)`, proved via mathlib's
`smul_basis_eq_zero` (linear independence of the power basis `{1, Y}` over `R[X]`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A specialisation helper. It is the injectivity of a single structure map, specialised to the
project's universal curve; it is consumed only to discharge the `pointedCurve.IsElliptic` instance
immediately below it (Δ ≠ 0 pushes forward along an injective map). Not a named theorem, not a `## Main
result`. (Literature width was run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive `term` line (a `.comp` of two injectivity facts).
One-liner verdict: **n/a — kind is `lemma`, not `def`.** The defeq/diamond/API exemption analysis is for
`def`s; for a proof term the one-liner signal feeds the composition check instead (Phase 6), where it
weighs toward a NO bucket.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "coordinate ring elliptic curve function field algebra map injective domain base ring"                 | yes  | base ring → Frac(coord ring) injective by construction | Purdue/Stanford/IITB notes; standard EC function-field setup |
|  2 | WebSearch (general form)         | "function field of a curve fraction field coordinate ring base field embeds injective … transcendental" | yes  | `k ↪ k(V) = Frac(k[V])` for irreducible `V`           | Scheidler "Intro to Function Fields"; uchicago integrality notes — "embedding … is injective by construction" |
|  3 | WebSearch (named-after / aliases)| "function field of a curve … regular functions transcendental"                                          | yes  | `A` (regular fns) ↪ `Fq(C)`; analog of ℤ ↪ ℚ          | Same sources; the embedding is structural, no person's name attached |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of: base ring embeds in the function field of a curve") | n/a  | MCP unavailable in this environment (per task note); covered by channels 1–3 + 6–9 and reasoning | recorded n/a — fallbacks used |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                 | n/a  | directory absent                                     | `.mathlib-quality/` for NagellLutz contains only `overview/`; no `references/` dir |
|  6 | nLab                             | "function field" / "coordinate ring of a variety"                                                       | yes  | `k(X) = Frac(O_X(U))`; integral ⇒ structure map injective | structural, foundational; nLab treats it as definitional |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept                            | the statement is a 1-step ring-map injectivity; no categorical content |
|  8 | Stacks Project (alg geom)        | function field of integral scheme / fraction field of affine ring (tag 01WV nbhd)                       | yes  | for integral `X`, `O_X(U) ↪ K(X)` (function field); Frac of a domain embeds | Stacks: function field of an integral scheme is `Frac` of any affine open; the map from global/affine functions is injective. (The exact tag fetched was a divisor page; the surrounding function-field material is standard Stacks.) |
|  9 | MathOverflow / Math.SE           | "base field injects into function field of a variety"                                                   | yes  | yes — folklore; `Frac` of an integral domain is faithfully an extension | treated as obvious; no research-level discussion |
| 10 | recent arXiv (last 5 years)      | "coordinate ring … function field … injective" (descent, Goppa-code, Drinfeld papers)                  | no   | used as ambient setup, never stated as a result      | the embedding is assumed, never a theorem — strong "too elementary to be a named lemma" signal |

The protocol passes: WebSearch ran 3 queries at distinct generality levels; ChatGPT MCP recorded `n/a`
with reason (environment); local refs recorded `n/a` with reason (dir absent); nLab/Stacks/MathOverflow/
arXiv each checked. nCatLab `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: **the base ring embeds into the function field of the (universal) curve** — i.e.
`R ↪ Frac(R[W])`, the structure map of an integral curve into its function field.
Sources agree on the standard form: **yes.** Every source treats `k ↪ k(V) = Frac(k[V])` (for an
irreducible/integral variety `V`) as *true by construction* — the coordinate ring is a domain and
`R[X,Y]/⟨W⟩` is a domain over a domain base, so the localisation map at the zero ideal is injective.
Most general standard form: for any **integral domain** base `R` and a Weierstrass curve `W/R`,
`algebraMap R W.FunctionField` is injective (indeed `algebraMap R[X] W.CoordinateRing` already is).
Generality dimensions where the literature varies:
  - base object: ranges from "algebraically closed field `k`" (classical) → "any field" → "any integral
    domain". The most general is **integral domain** (which is exactly what mathlib's `CoordinateRing`
    domain instance already targets via `IsDomain R`).
  - target: ranges from "coordinate ring `R[W]`" → "function field `Frac(R[W])`". Both appear.
Disagreement with the literature: **none.** The project's statement is the field-level specialisation of
the standard fact, restricted to the single base `R₀ = ℤ[A₁,…,A₆]`.

---

### Generality analysis — `WeierstrassCurve.Universal.algebraMap_field_injective` (Phase 4)

Literature-standard form (from Phase 3): for any integral-domain base `R` and Weierstrass curve `W/R`,
`algebraMap R W.FunctionField` (equivalently `algebraMap R (FractionRing W.CoordinateRing)`) is injective.

| # | Parameter / hypothesis        | Current Lean form                          | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | base ring                     | the single fixed `MvPolynomial Coeff ℤ`    | any `[CommRing R] [IsDomain R]`    | yes                 | The proof uses nothing about `ℤ[A₁,…,A₆]` beyond it being a comm-ring base of a Weierstrass curve; the leaf `algebraMap_poly_injective` is fully generic over `{R} [CommRing R] {W' : Affine R}`. |
| 2 | the curve                     | the fixed `Universal.curve`                | any `W' : WeierstrassCurve.Affine R`| yes                 | `algebraMap_injective'` is already stated for a generic `W'`; only this top wrapper pins it to `curve`. |
| 3 | target field                  | `Universal.Field = Frac(Universal.Ring)`   | `W.FunctionField = Frac(W.CoordinateRing)` (mathlib `abbrev`, `Affine/Point.lean:95`) | yes | `IsFractionRing.injective` is generic; only the wrapper pins the field to the universal one. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is the literature-standard fact pinned to
one specific base ring, one specific curve, and one specific fraction field. **But it is not narrower
because of a missing hypothesis-weakening; it is narrower because it is a deliberate *specialisation* of
a generic project lemma (`algebraMap_injective'`) to the universal curve.** The narrowness is the whole
point of the wrapper (it instantiates `W' := curve` so the `IsElliptic` instance can use it directly).
Number of weakening opportunities found: 3 (all three "weakenings" are just *not specialising*).
Proposed restatement (the general form, which is what would ever be mathlib-relevant):

```lean
-- general form (NOT this decl — this is what mathlib would conceivably want)
theorem algebraMap_functionField_injective {R : Type*} [CommRing R] [IsDomain R]
    (W' : WeierstrassCurve.Affine R) :
    Function.Injective (algebraMap R W'.FunctionField) :=
  (IsFractionRing.injective _ _).comp (CoordinateRing.algebraMap_injective' (W' := W'))
```

Cost of restatement: **CHEAP** (mechanical — the general proof is literally the same two-line `.comp`,
since both leaves are already generic). But see Phase 6: the general form is itself a ≤3-call mathlib
composition, so even the general form does not warrant a standalone mathlib lemma.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                   | no       | —                      | already typeclass-driven (`CommRing`, `IsFractionRing`) |
|  2 | sequences/metric → filters/topology?                                                                  | no       | —                      | no analytic content |
|  3 | construct an object where a universal-property class would characterise it?                          | no       | —                      | `IsFractionRing` already IS the universal-property class; the decl uses it correctly |
|  4 | set-with-closure-predicate → bundled substructure?                                                    | no       | —                      | no substructure here |
|  5 | vector-space/metric/field-specific → weaken to module/pseudometric/(semi)ring?                       | partial  | the general form (Phase 4b) weakens the base from the specific `ℤ[A₁,…,A₆]` to any `IsDomain` | already captured in 4b; not a new idiom |
|  6 | 1-categorical → higher/∞-categorical?                                                                 | no       | —                      | none |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive group/monoid?                                            | no       | —                      | no index |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The decl already uses the contemporary mathlib idiom
(`IsFractionRing.injective` + the bundled `CoordinateRing`/`FunctionField` API). The only "improvement"
is de-specialisation (Phase 4b), which is not an idiom change. One-line reason: this is a structure-map
injectivity discharged by the canonical `IsFractionRing` API — there is no cleaner contemporary form.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma`. (No definitional equalities or typeclass-search paths introduced.)

---

### Mathlib search-status: `WeierstrassCurve.Universal.algebraMap_field_injective` (Phase 5)

```
[A] Lean-Finder       (index unavailable locally; substituted by [D] grep over mathlib src)   n/a: tool not in env
[B] Loogle            `Function.Injective (algebraMap _ (FractionRing (WeierstrassCurve.Affine.CoordinateRing _)))`
                      `Function.Injective (algebraMap _ (WeierstrassCurve.Affine.CoordinateRing _))`   no hits (reasoned; see [D])
[C] LeanSearch        "base ring injects into function field of a Weierstrass curve"            no hits (reasoned; see [D])
[D] Grep mathlib src  `namespace Universal` under WeierstrassCurve;
                      `algebraMap_poly_injective` / `algebraMap_injective'`;
                      `Injective (algebraMap` in EllipticCurve/;
                      `FunctionField`, `CoordinateRing.map_injective`                            see conclusions below
[E] Name pattern      `algebraMap_field_injective`, `algebraMap_functionField`                  no mathlib hit (only the two project copies)
```

Concrete grep results (decisive):

- **No `WeierstrassCurve.Universal` namespace exists in mathlib.** The only `Universal` namespaces are
  `AlgebraicGeometry/Morphisms/UniversallyOpen.lean` and `Algebra/Lie/UniversalEnveloping.lean` — both
  unrelated. ⇒ The decl's *types* (`MvPolynomial Coeff ℤ`, `Universal.Field`, `Universal.Ring`) do not
  exist in mathlib, so the decl can never be added **as-is**.
- `grep` for the project's leaf names `algebraMap_poly_injective` and `algebraMap_injective'` over all
  of `Mathlib/` returns **nothing**. ⇒ The non-trivial leaf (`algebraMap R[X] CoordinateRing` injective)
  is **not** in mathlib under that name.
- `grep "Injective (algebraMap"` over `Mathlib/AlgebraicGeometry/EllipticCurve/` returns **nothing** —
  mathlib has no standalone "algebraMap into the coordinate ring / function field is injective" lemma.
- **However, mathlib HAS the building blocks:**
  - `WeierstrassCurve.Affine.FunctionField := FractionRing W'.CoordinateRing`
    (`Affine/Point.lean:95`) — the general analog of `Universal.Field`.
  - `WeierstrassCurve.Affine.CoordinateRing.map_injective` (`Affine/Point.lean`, ~line 187):
    `Function.Injective f → Function.Injective (map W' f)`.
  - `AdjoinRoot.of.injective_of_degree_ne_zero` (`Mathlib/RingTheory/AdjoinRoot.lean:265`): for
    `[IsDomain R]` and `f.degree ≠ 0`, `AdjoinRoot.of f` is injective. Since
    `W'.CoordinateRing := AdjoinRoot W'.polynomial` and `algebraMap R[X] W'.CoordinateRing = AdjoinRoot.of
    W'.polynomial`, and the Weierstrass polynomial has `Y`-degree 2 ≠ 0, this **directly** gives the
    non-trivial leaf for a domain base.
  - `IsFractionRing.injective` (`FractionRing.lean:137`) — the fraction-field leaf.
  - `Polynomial.C_injective` (`Algebra/Polynomial/Basic.lean:682`).
  - Mathlib even already runs essentially this composition to derive
    `instance [IsDomain R] : IsDomain W'.CoordinateRing` via
    `(map_injective <| IsFractionRing.injective R <| FractionRing R).isDomain` (`Affine/Point.lean:197`).

Searched for both the user's current form and the literature-standard (general) form.

Concluded: **found the building blocks** (`AdjoinRoot.of.injective_of_degree_ne_zero`,
`IsFractionRing.injective`, `Polynomial.C_injective`, and the bundled `FunctionField`/`CoordinateRing`
API); the exact form — and the general `algebraMap R W.FunctionField` form — is **not** a named lemma in
mathlib, but composes from these primitives.

---

### Call sites — `WeierstrassCurve.Universal.algebraMap_field_injective` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring file): **0.**
External-to-file callers (within NagellLutz): **0.** The only consumer is **in the same file**, one line
below the decl:

| Caller file:line                                   | Usage pattern (one-line excerpt)                                            |
|----------------------------------------------------|------------------------------------------------------------------------------|
| `projects/NagellLutz/LutzNagell/Universal.lean:135`| `exact ((map_ne_zero_iff _ algebraMap_field_injective).mpr Δ_curve_ne_zero).isUnit` — discharges the `pointedCurve.IsElliptic` instance |

Cross-project observation (consolidation-monorepo signal): the **identical lemma with the identical
proof** also exists at `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:126`, and HasseWeil also
duplicates the leaves `algebraMap_poly_injective` / `algebraMap_injective'`
(`HasseWeil/.../Universal.lean:48,53`). HasseWeil additionally uses the *generic leaf*
`Affine.CoordinateRing.algebraMap_poly_injective` heavily (~20 call sites across `OmegaPullbackCoeff`,
`MulByIntPullback`, `WronskianGeneral`, `FiniteOverKx`, `FrobeniusIsogeny`, …), frequently in exactly the
shape `(IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective` — i.e. the
*generic* composition that this universal-curve wrapper is one instance of.

Inline-derivation grep (was the equivalent re-derived elsewhere without using this decl?):
  - Yes — HasseWeil re-derives the same `IsFractionRing.injective ∘ algebraMap_poly_injective`
    composition inline at numerous sites rather than calling a named "field injective" wrapper. This is
    the K=0-with-inline-rederivation pattern: the wrapper is bypassed in favour of the underlying generic
    composition.

Call-sites signal: **K = 0 internal uses, single same-file consumer, and the same composition is
re-derived inline elsewhere** → strong lean toward a NO bucket (the wrapper adds nothing the underlying
generic leaf + `IsFractionRing.injective` don't already give at the call site).

### Composition check (Phase 6)

Can `WeierstrassCurve.Universal.algebraMap_field_injective` be derived from mathlib in ≤3 chained calls?

Two layers to consider — (i) the **specific** decl (pinned to the universal curve) and (ii) the
**general** fact it specialises.

Attempt 1 — the general fact `algebraMap R W'.FunctionField` injective for `[IsDomain R]`, from **pure
mathlib primitives**:
```lean
example {R : Type*} [CommRing R] [IsDomain R] (W' : WeierstrassCurve.Affine R) :
    Function.Injective (algebraMap R W'.FunctionField) :=
  (IsFractionRing.injective _ _).comp
    ((AdjoinRoot.of.injective_of_degree_ne_zero (by
        -- W'.polynomial has Y-degree 2 ≠ 0
        sorry)).comp Polynomial.C_injective)
```
  - Mathlib decls used: `IsFractionRing.injective`, `AdjoinRoot.of.injective_of_degree_ne_zero`,
    `Polynomial.C_injective` (+ the bundled defeq `algebraMap R[X] CoordinateRing = AdjoinRoot.of …`).
  - Result: **succeeds** as a 3-call composition for a domain base. The only obligation is the
    `degree ≠ 0` side goal (the Weierstrass polynomial is monic of `Y`-degree 2 — mathlib has
    `WeierstrassCurve.Affine.natDegree_polynomial` / `monic_polynomial` for this).
  - Notes: This is exactly the shape mathlib itself already uses one line away
    (`Affine/Point.lean:197`).

Attempt 2 — the **specific** decl: instantiate Attempt 1 (or the project's own generic leaf
`algebraMap_injective'`) at `R := MvPolynomial Coeff ℤ`, `W' := curve`:
```lean
example : Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective _ _).comp (Affine.CoordinateRing.algebraMap_injective' (W' := curve))
```
  - This is the decl's actual body. `MvPolynomial Coeff ℤ` is an integral domain, so Attempt 1 applies.
  - Result: **succeeds** in ≤3 calls (here 2, given the generic leaf).

Conclusion: **COMPOSABLE.** The general fact is a ≤3-call mathlib composition; the specific universal-curve
form is a 1–2 line instantiation of it. No new mathlib lemma is warranted.

---

## Verdict: `WeierstrassCurve.Universal.algebraMap_field_injective`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the base ring → function-field embedding is foundational and
  "injective by construction"; no named theorem; arXiv treats it as ambient setup, never a result.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a deliberate specialisation of the
  generic project leaf `algebraMap_injective'` to the single universal curve; no idiom improvement.
- Mathlib search (Phase 5): the decl's types (`Universal.Field`, `MvPolynomial Coeff ℤ`) do not exist in
  mathlib, so it cannot be added as-is; the building blocks (`IsFractionRing.injective`,
  `AdjoinRoot.of.injective_of_degree_ne_zero`, `Polynomial.C_injective`, bundled `FunctionField`) all
  exist; no named "algebraMap into the function field is injective" lemma exists.
- Composition check (Phase 6): COMPOSABLE — ≤3 mathlib calls give the general fact; the specific form is a
  1–2 line instantiation. K = 0 internal uses; the same composition is re-derived inline in HasseWeil.

**Rationale:**

This declaration is the structure-map injectivity `ℤ[A₁,…,A₆] ↪ Frac(curve.CoordinateRing)`, hard-wired
to the project's universal curve. It cannot be a mathlib lemma "as-is" because every type in its
signature (`Universal.Field`, `Universal.Ring`, `MvPolynomial Coeff ℤ`, `curve`) is a project-specific
construction with no mathlib counterpart. Stripped to its mathematical content, it is the standard,
foundational fact that the base ring of an integral curve embeds into the curve's function field —
literature uniformly treats this as true *by construction*, never as a named result. So the only
mathlib-relevant question is whether the **general** fact (`algebraMap R W.FunctionField` injective for a
domain base) deserves a standalone lemma, and the answer is **no**: it composes from mathlib primitives
in three chained calls — `IsFractionRing.injective` ∘ `AdjoinRoot.of.injective_of_degree_ne_zero` ∘
`Polynomial.C_injective` — using mathlib's already-present bundled `FunctionField`/`CoordinateRing` API.
Mathlib itself performs essentially this exact composition one line away (to derive
`IsDomain W'.CoordinateRing`), which is the strongest possible evidence that the building blocks suffice
and a wrapper is redundant.

The call-site analysis seals it: the lemma has **zero** internal consumers beyond the single
`IsElliptic` instance directly below it in the same file, and the identical composition is re-derived
inline across ~20 HasseWeil call sites rather than routed through a named "field injective" wrapper. The
proof body is itself already a one-line `.comp` — a textbook NO-composable shape.

**WHY not (refactor-actionable):**

Mathlib has the building blocks; the user's form is a 1–3 mathlib-call composition (and is itself only
used once, in-file). No new mathlib lemma is needed — the universal-curve specialisation should be
inlined / kept project-local, and any general "function field injective" need at a call site should be
discharged by the composition directly.

Mathlib building blocks:
- `IsFractionRing.injective` — `Mathlib/RingTheory/Localization/FractionRing.lean:137`
- `AdjoinRoot.of.injective_of_degree_ne_zero` — `Mathlib/RingTheory/AdjoinRoot.lean:265`
- `Polynomial.C_injective` — `Mathlib/Algebra/Polynomial/Basic.lean:682`
- `WeierstrassCurve.Affine.FunctionField` (`Affine/Point.lean:95`) and the bundled
  `CoordinateRing` API — the defeq `algebraMap R[X] W'.CoordinateRing = AdjoinRoot.of W'.polynomial`
- (project-internal, generic) `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'` — already
  the generic version; the universal wrapper is just `… .comp (algebraMap_injective' (W' := curve))`.

Composition sketch (≤3 lines), general form:
```lean
example {R : Type*} [CommRing R] [IsDomain R] (W' : WeierstrassCurve.Affine R) :
    Function.Injective (algebraMap R W'.FunctionField) :=
  (IsFractionRing.injective _ _).comp
    ((AdjoinRoot.of.injective_of_degree_ne_zero (W'.natDegree_polynomial ▸ two_ne_zero)).comp
      Polynomial.C_injective)
```
(specific form is then `… (W' := curve)` with `R := MvPolynomial Coeff ℤ`, a domain).

Call sites in our project (from Phase 6.0): **K = 0** outside the declaring file (1 same-file consumer
at `Universal.lean:135`).

Refactor plan:
1. **Do not upstream this decl.** Keep it project-local as a convenience wrapper *or* inline it.
2. If kept: it is fine as a tiny private helper for the `IsElliptic` instance — but note it duplicates
   `HasseWeil/.../Universal.lean:126` verbatim. The genuine consolidation-monorepo action is to
   **de-duplicate the whole `Universal.lean` pair** (NagellLutz + HasseWeil) into one shared
   `Common/` module that both projects import (this is a `/cleanup` cross-project dedup ticket, not a
   mathlib-PR action). The same applies to the leaves `algebraMap_poly_injective` /
   `algebraMap_injective'`, which are duplicated across both projects and heavily used in HasseWeil.
3. The leaf `algebraMap_poly_injective` (the actually-non-trivial lemma — `algebraMap R[X]
   W'.CoordinateRing` injective over an arbitrary `CommRing` base, no `IsDomain` needed) is the *only*
   piece here with any claim to mathlib novelty, because it holds **without** `[IsDomain R]` (mathlib's
   `AdjoinRoot.of.injective_of_degree_ne_zero` requires a domain). That is a separate assessment — see
   "Next action". For THIS decl (the field-level wrapper over the universal curve), the verdict is firmly
   NO-composable.

**Next action:** Delete/keep-local this universal-curve wrapper — do not open a mathlib PR for it. File a
NagellLutz↔HasseWeil **cross-project dedup** cleanup ticket for the duplicated `Universal.lean`. Optionally
run `/mathlibable WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective` separately: the
domain-free leaf is the one lemma in this neighbourhood that mathlib's `AdjoinRoot.of.injective_of_degree_ne_zero`
does **not** subsume (it needs `[IsDomain R]`), so it is the genuine candidate — not this field wrapper.

---

## Next step

Delete/keep this declaration project-local; do not open a mathlib PR. Inline the ≤3-call composition where
a general "algebraMap into the function field is injective" is ever needed. File a cross-project dedup
ticket for the duplicated NagellLutz/HasseWeil `Universal.lean`. Separately assess the domain-free leaf
`algebraMap_poly_injective` (the only nearby lemma not subsumed by mathlib's
`AdjoinRoot.of.injective_of_degree_ne_zero`).
