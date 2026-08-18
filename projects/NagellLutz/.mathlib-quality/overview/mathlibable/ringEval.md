# /mathlibable report — `WeierstrassCurve.Universal.ringEval`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration.
> Note: ChatGPT MCP (Codex) was DOWN this run; `lean_loogle`/`lean_leansearch`
> deferred tools were not exposed in this environment. Phase 5 methods [B]/[C]
> were covered via public LeanSearch-style WebSearch queries; methods [D]/[E]
> via authoritative direct grep of the pinned mathlib source tree
> (`.lake/packages/mathlib`, rev `09b373db6e24`, toolchain `v4.32.0-rc1`). The
> grep over the mathlib source is the authoritative existence check and is
> conclusive on its own.

---

### Baseline (Phase 0)
- lake build:               not run (build stale per task; reasoning from source — the decl elaborates as written and is used downstream across two projects)
- decl `WeierstrassCurve.Universal.ringEval`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:215`
- kind:                      `def` (takes a hypothesis `eqn : Affine.Equation W x y`)
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — defines the universal Weierstrass curve over ℤ[A₁..A₆], its coordinate ring `Universal.Ring`, and the specialization machinery `specialize`/`polyEval`/`ringEval`. Author: Junyan Xu (2024).

---

### Statement (Phase 1)

`WeierstrassCurve.Universal.ringEval` is a **definition**. Given a Weierstrass
curve `W` over a commutative ring `R` and an affine point `(x, y)` lying on it
(`eqn : W.Equation x y`), it produces the ring homomorphism

  `ringEval : Universal.Ring →+* R`

out of the **coordinate ring of the universal Weierstrass curve**
`Universal.Ring = curve.CoordinateRing = (ℤ[A₁,A₂,A₃,A₄,A₆])[X][Y] / ⟨P⟩`
(where `curve` is the universal curve whose five coefficients are the
indeterminates `A₁,…,A₆`, and `P` is its affine Weierstrass polynomial), into `R`.

Mathematically: this is the **realization of the universal property** of the
universal *pointed* Weierstrass curve. The pair (curve `W`, point `(x,y)`) is
classified by a unique ring map from the universal coordinate ring; `ringEval`
*is* that classifying map. It sends each indeterminate `Aᵢ` to the corresponding
coefficient `W.aᵢ`, and sends the adjoined coordinates `X ↦ x`, `Y ↦ y`. The
construction is `AdjoinRoot.lift` of the point-evaluation `eval₂RingHom W.specialize x`
at `y`, whose well-definedness obligation (`P ↦ 0`) is exactly the statement that
`(x,y)` lies on `W` (`map_specialize` + `Affine.map_polynomial`).

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — the target ring; mathematically the ring over which the concrete curve lives.
- `(W : WeierstrassCurve R)` — the concrete Weierstrass curve to specialize to.
- `(x y : R)` — coordinates of the concrete point.

Hypotheses (Lean side):
- `(eqn : Affine.Equation W x y)` — the point `(x,y)` lies on the affine curve. Used only to discharge the `AdjoinRoot.lift` side-condition `P.eval₂ … = 0`.

Conclusion (math): the unique specialization homomorphism from the universal pointed-curve coordinate ring to `R` classifying `(W, (x,y))`.

Conclusion (Lean): `Universal.Ring →+* R` (n/a — definition, no proposition).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a structural piece of the **universal Weierstrass curve** package —
the corepresentability map of a moduli-style functor. It introduces named
mathematical infrastructure (the classifying map of the universal pointed curve),
not a one-off helper. (Literature width is EXHAUSTIVE regardless; BIG/SMALL only
frames the report.)

### One-line check (Phase 2b)

Body line count: ~4 substantive lines (`AdjoinRoot.lift … <| by simp_rw …; rwa …`).
One-liner verdict: **MULTI-LINE** — the body is an `AdjoinRoot.lift` whose
well-definedness proof is itself a `by`-block (`simp_rw [...] ; rwa [...]`). The
2b exemption table is skipped (kind is a `def` but not a one-liner).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "universal Weierstrass curve coordinate ring specialization homomorphism point elliptic curve" | yes | curve over `ℤ[a₁..a₆]`; specialization map `A → R` sending `aᵢ ↦` coefficients | Sage `ell_generic`, Silverman-style; the specialization map is the standard "obvious ring morphism A → R" |
| 2 | WebSearch (general form) | "universal elliptic curve over polynomial ring a1..a6 division polynomials generic" | yes | "universal elliptic curve over Frac/closure of `ℤ[a₁..a₆]`"; "char-0 universal ring `ℤ[A₁..A₆][X,Y]`"; ψₙ = generic EDS | Wikipedia *Division polynomials*; arXiv 1303.4327. Confirms the exact `ℤ[A₁..A₆][X,Y]/(P)` ring as the standard universal object |
| 3 | WebSearch (named-after / aliases) | "elliptic curve point induces ring homomorphism coordinate ring evaluation AdjoinRoot universal property generic point" | partial | "map of curves induces ring hom of coordinate rings"; "generic point = Spec of integral domain"; Spec ⊣ Γ adjunction | Standard coordinate-ring functoriality + Spec–Γ adjunction is the abstract umbrella; no source names this exact specialize-at-a-point map as a standalone lemma |
| 4 | ChatGPT MCP | (asked: standard object? corepresentability? can it live in mathlib alone?) | **n/a** | — | Codex backend DOWN this run (errored on invocation, as the task warned). Compensated via channels 1–3 + nLab/Stacks + source reasoning |
| 5 | Local references | `ls projects/NagellLutz/.mathlib-quality/references/` | n/a | (directory absent) | No per-project references dir for NagellLutz |
| 6 | nLab | "Weierstrass curve / universal elliptic curve / moduli of elliptic curves" | yes (concept) | universal elliptic curve = tautological curve over the moduli stack 𝓜_{ell}; classifies families | nLab frames it stack-theoretically; the affine `ℤ[a₁..a₆]` presentation is the Weierstrass chart of 𝓜_{Weier}. Confirms it is a real, central object |
| 7 | nCatLab | (same as nLab) | yes | as above (moduli stack of elliptic curves; tmf literature) | The arithmetic of `ℤ[a₁..a₆]` underlies tmf (cf. arXiv 1212.3656 from channel-1 results) |
| 8 | Stacks Project | "generic point", "moduli of elliptic curves" | partial | generic point (tag 0BB7); moduli/representability language | Stacks has the representability/generic-point framework but no `ℤ[a₁..a₆]`-specific Weierstrass specialization lemma |
| 9 | MathOverflow / MSE | "universal Weierstrass curve specialization", coordinate-ring evaluation | partial | confirms the object is standard folklore; no canonical "lemma" name for the point-induced map | The construction is used freely, rarely isolated as a named result |
| 10 | recent arXiv (≤5y) | "homogeneous division polynomials Weierstrass" (1303.4327); "integral points / valuations of division polynomials" (1108.3051) | yes | uses the universal/generic curve over `ℤ[a₁..a₆]` to derive identities, then specializes | Exactly the proof technique this project formalizes (prove for ψₙ universally, specialize to the cusp / to `(x,y)`) |

The protocol passed: WebSearch ran 3 distinct queries at different generality
levels (specific specialization map / general universal-ring + division-polynomial
framing / named-after & abstract coordinate-ring functoriality); local refs
recorded `n/a` (absent); nLab, nCatLab, Stacks, MathOverflow, arXiv each checked.
ChatGPT MCP recorded `n/a` with reason (Codex backend down), compensated by the
other live channels and direct source reading.

### Literature summary (Phase 3)

Concept identified as: the **universal (generic) Weierstrass/elliptic curve over
`ℤ[A₁,A₂,A₃,A₄,A₆]`** and its **specialization homomorphism** — and `ringEval`
specifically is the **point-refined specialization out of the universal coordinate
ring** (the corepresentability / classifying map of the universal *pointed* curve).
Sources agree on the standard form: **yes** — the universal curve over `ℤ[a₁..a₆]`,
its function field/coordinate ring, and "the obvious ring morphism `A → R` sending
`aᵢ` to the coefficients" are standard (Silverman/Lang folklore; Sage's
`ell_generic`; the division-polynomial literature). The *point-induced* extension
to a map out of the coordinate ring (adjoining `X,Y`) is the natural next step but
is not isolated as a named lemma anywhere — it is used inline.
Most general standard form: for **any** commutative ring `R`, any Weierstrass curve
`W/R`, and any `R`-point `(x,y)` on `W`, the universal pointed coordinate ring maps
uniquely to `R`. This is exactly the Lean form here — already fully general
(arbitrary `CommRing R`).
Generality dimensions where the literature varies:
  - base ring: literature often works over a field / `Frac(ℤ[a₁..a₆])`; the project's `R : CommRing` form is **more** general (strictly), which is the right mathlib direction.
  - structure used: literature phrases it via Spec/morphisms of schemes; the project uses the concrete coordinate-ring / `AdjoinRoot` model mathlib already commits to.
Disagreement with the literature: none. The Lean form is the maximally general,
ring-theoretic shadow of the standard scheme-theoretic statement.

---

### Generality analysis — `WeierstrassCurve.Universal.ringEval`

Literature-standard form (from Phase 3): for any `CommRing R`, any `W/R`, any point
`(x,y)` on `W`, the unique specialization `Universal.Ring →+* R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]` | arbitrary commutative ring | often a field / `Frac(ℤ[a₁..a₆])` | NO (already maximal) | `CommRing` is the weakest sensible hypothesis; `AdjoinRoot.lift` + `eval₂RingHom` need no more. Already strictly more general than the literature's field default. |
| 2 | `(W : WeierstrassCurve R)` | arbitrary Weierstrass curve | smooth / elliptic curve | NO | the construction needs no nonsingularity/Δ-unit; works for any Weierstrass curve. Maximal. |
| 3 | `(eqn : Affine.Equation W x y)` | point on the affine curve | a point on the curve | NO | this is the minimal hypothesis: it is exactly the `AdjoinRoot.lift` side-condition. Cannot be dropped (without it the lift is ill-defined). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: 0
Cost of restatement: n/a — nothing to restate. The Lean form is already strictly
more general than the field-based statements common in the literature.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclass/instance? | no | — | the only hypothesis (`Equation W x y`) is genuinely data (a chosen point), not a typeclass; bundling it as an instance would be wrong (a curve has many points). |
| 2 | sequences/metric → filters/topology? | no | — | no limiting/metric content; purely algebraic. |
| 3 | construct object → universal-property class? | **borderline-yes (umbrella)** | a `WeierstrassCurve.IsUniversal`-style corepresentability class; `ringEval` would be the `lift` field | this is the *real* mathlib-idiomatic home — but it is an argument to ship the **whole universal-curve package** as a represented-functor, not to reshape `ringEval` alone. See Phase 7. |
| 4 | set+closure-predicate → bundled substructure? | no | — | not a substructure. |
| 5 | vector-space/field-specific → weaker typeclass? | no (already done) | — | already at `CommRing`; nothing to weaken. |
| 6 | 1-categorical → higher-categorical? | no | — | a single classifying ring map; no 2-categorical content at this granularity. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid/group? | no | — | no numeric index; the `ℤ`/`MvPolynomial Coeff ℤ` base is the *definition* of the universal object, not an artificial restriction. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for `ringEval` in isolation).
One-line reason: `ringEval` is already the maximally-general ring map; the only
"modernisation" is to package the *entire* universal-curve construction as a
represented/corepresented functor (a `IsUniversal` universal-property class) — that
is a property of the **whole package**, not a reformulation of this one `def`, and
mathlib has none of the package today. So this does not flip the verdict to
YES-but-generalise-first; it informs the YES rationale's framing instead.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.ringEval` (Phase 4.5)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | it is a plain `def` returning a `RingHom`, not an `instance`; introduces no new instance-search path. |
| 2 | Reducibility leak | none | not `@[reducible]`; body is an `AdjoinRoot.lift`, sealed. Downstream relies on the `ringEval_mk`/`ringEval_comp_*` API lemmas, not on unfolding. |
| 3 | Non-canonical unfolding | low | `simp` will not unfold it (no `@[simp]`); the project's `simp_rw [← ringEval_comp_smulRing …]` rewrites use lemmas, never the raw body. |
| 4 | Instance priority collision | none | not an `instance`. |
| 5 | Universe-polymorphism issues | none | all types live in `Type 0`-ish concrete rings; `R : Type*` is the only universe var and flows transparently through `RingHom`. |
| 6 | Coercion ambiguity | none | returns a bundled `→+*`; no new `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**
Top risks: none. (Were the universal-curve package ever upstreamed, the only care
needed is the usual one for `AdjoinRoot`-based defs: keep the API-lemma layer so
consumers never depend on the raw `lift` body — already the case here.)

---

### Mathlib search-status: `WeierstrassCurve.Universal.ringEval`

[A] Lean-Finder       n/a — deferred lean_* index tools not exposed this run; substituted by [D]/[E] direct source grep (authoritative).
[B] Loogle            type-pattern `WeierstrassCurve.CoordinateRing →+* _` and `Universal.Ring →+* _`  →  n/a tool; via grep [D]: the only `CoordinateRing →+*` in mathlib is `Affine.CoordinateRing.map` (into another coordinate ring), never into the base ring `R`.
[C] LeanSearch        NL queries (via WebSearch, results in Phase 3 channels 1–3): "universal Weierstrass curve specialization coordinate ring", "point induces ring hom out of coordinate ring"  →  no mathlib decl; only the docs for `CoordinateRing` functoriality surface.
[D] Grep mathlib src  `Universal`, `ringEval`, `polyEval`, `specialize` under `Mathlib/AlgebraicGeometry/EllipticCurve/`  →  **ZERO hits** for `Universal`/`ringEval`/`polyEval`/`specialize`. Also grepped `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (`universal`/`generic`/`specialize` → none). The closest map is `WeierstrassCurve.Affine.CoordinateRing.map` (`Affine/Point.lean:172`), `W'.CoordinateRing →+* (W'.map f).CoordinateRing`.
[E] Name pattern      grep `def ringEval`, `Universal.curve`, `protected abbrev Ring`  →  hits only in the project files (NagellLutz `Universal.lean`; the byte-near-identical HasseWeil fork). Nothing in mathlib.

Searched for both the user's current form (`Universal.Ring →+* R`) and the
literature-standard form (the universal-curve specialization). Mathlib has neither.

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard form). Mathlib has NO universal Weierstrass curve, no
`Universal.Ring`, no `specialize`, no point-evaluation out of a coordinate ring
into the base ring. It has only the *building block* `Affine.CoordinateRing.map`
(coefficient-transport functoriality into another coordinate ring).

---

### Call sites — `WeierstrassCurve.Universal.ringEval`

Internal use count (across the monorepo, excluding the declaring file): **many**
(≥ 15 distinct usages).
External-to-file callers: the same `Universal.lean` companion lemmas are excluded;
genuine downstream consumers span **3 files in 2 projects**:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:557` | `lemma ringEval_comp_smulRing (n) : ringEval eqn ∘ smulRing n = smulEval W x y n` |
| `projects/NagellLutz/LutzNagell/ZSMul.lean:564` | `ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n)` |
| `projects/NagellLutz/LutzNagell/ZSMul.lean:144,150` | `congr(ringEval cusp_equation_one_one $h)` (cusp specialization, ψₙ/φₙ nonvanishing) |
| `projects/NagellLutz/LutzNagell/ZSMul.lean:569,575,582,621` | `simp_rw [← ringEval_comp_smulRing eqn, …, curveRing_map_ringEval]` (group-law compatibility) |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:223,229,633,640,647,653,660,702` | same suite (this is the byte-near-identical fork of the same file) |
| `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:218…242` | the fork's own copy of `ringEval` + its companion lemmas |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `ringEval`?):
  - (none) — every consumer goes through `ringEval` and its API lemmas (`ringEval_mk`, `ringEval_comp_smulRing`, `curveRing_map_ringEval`, …). No site re-derives the specialization by hand.

Composability signal: **K ≥ 3 internal uses, no inline re-derivation** ⇒ real,
load-bearing API. (Caveat: this is a *forked* file living in two projects; the heavy
use is genuine, but it is project-internal infrastructure, not a public-library
surface — relevant to the consolidation, not to the mathlib verdict.)

---

### Composition check (Phase 6)

Can `ringEval` be derived from mathlib in ≤3 chained calls?

Attempt 1: `(eval-at-point) ∘ Affine.CoordinateRing.map W.specialize`.
  - `Affine.CoordinateRing.map (W.specialize) : curve.CoordinateRing →+* (curve.map W.specialize).CoordinateRing`. By `map_specialize`, `curve.map W.specialize = W`, so this is `Universal.Ring →+* W.CoordinateRing`.
  - Then we would need a mathlib map `W.CoordinateRing →+* R` that **evaluates at the point `(x,y)`**.
  - Mathlib decls used: `WeierstrassCurve.Affine.CoordinateRing.map`, `Universal.map_specialize` (— but `map_specialize` itself is **project-local**, not mathlib).
  - Result: **fails**. (i) `map_specialize` is not in mathlib. (ii) **Mathlib has no point-evaluation `W.CoordinateRing →+* R`** — grep [D] confirms the only `CoordinateRing →+*` map is `map` into another coordinate ring, never into the base ring. The missing second factor is itself a non-trivial new construction (another `AdjoinRoot.lift`).

Attempt 2: directly via `AdjoinRoot.lift` (mathlib primitive).
  - `ringEval = AdjoinRoot.lift (eval₂RingHom W.specialize x) y h` — this **is** the body. But it is not a *composition of existing mathlib decls*: it requires the project's `specialize` (project-local), and the side-condition `h` is discharged by `map_specialize`/`Affine.map_polynomial` (project-local lemmas). So this is "re-write the definition", not "compose mathlib calls".
  - Result: **fails** as a composition — it depends on `Universal.Ring`, `specialize`, `map_specialize`, all of which are absent from mathlib.

Conclusion: **NOT-COMPOSABLE**. The two prerequisites — (a) the universal curve /
`Universal.Ring` / `specialize` scaffold and (b) a point-evaluation map out of a
coordinate ring into the base ring — are both missing from mathlib. You cannot
inline `ringEval` at a call site from mathlib primitives in ≤3 calls; you would
first have to build the entire universal-curve package.

---

## Verdict: `WeierstrassCurve.Universal.ringEval`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): the universal Weierstrass curve over `ℤ[A₁..A₆]` and its specialization map are **standard** (Silverman/Lang folklore, Sage `ell_generic`, the division-polynomial literature arXiv 1303.4327 / Wikipedia); `ringEval` is the point-refined specialization out of the universal coordinate ring (the corepresentability map). Standard object, and the Lean form is the maximally general ring-theoretic shadow.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — arbitrary `CommRing R`, arbitrary `WeierstrassCurve`, minimal point hypothesis. Strictly more general than the field-based statements in the literature. Phase 4c found no `ringEval`-local modernisation (the only abstraction move — a represented-functor class — is a property of the whole package, not this def).
- Mathlib search (Phase 5): **not in mathlib** — zero hits for `Universal`/`ringEval`/`specialize` in the EllipticCurve tree; only the building-block `Affine.CoordinateRing.map` exists.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the universal-curve scaffold and a coordinate-ring point-evaluation map are both absent, so no ≤3-call mathlib inlining is possible.

**Rationale:**

This is the classifying map of the universal *pointed* Weierstrass curve: for any
curve `W/R` and any point `(x,y)` on it, `ringEval` is the unique ring homomorphism
`Universal.Ring →+* R` specializing the universal coordinate ring to `(W,(x,y))`.
The underlying object — the universal curve over `ℤ[A₁,…,A₆]` and its
specialization homomorphism — is genuinely standard in the literature (it is the
Weierstrass chart of the moduli of elliptic curves, and is exactly the device the
division-polynomial literature uses to prove identities "generically" and then
specialize). Mathlib commits to the `Affine.CoordinateRing`/`AdjoinRoot` model and
even builds *coordinate-ring functoriality* `Affine.CoordinateRing.map` with the
same `AdjoinRoot.lift` primitive — but it has **no universal curve at all**, hence
no map out of its coordinate ring, and no point-evaluation `W.CoordinateRing →+* R`.
The form here is already maximally general (any `CommRing`, any curve, minimal
point hypothesis), carries no diamond/defeq risk (a sealed `def` returning a bundled
`→+*`, fronted by a clean API-lemma layer), and is not a ≤3-call composition of
mathlib primitives. So it clears every YES gate.

The honest framing, though: `ringEval` should enter mathlib **as one piece of the
universal-Weierstrass-curve package**, not as an orphan. On its own it is
ill-typed-for-purpose — its entire domain `Universal.Ring`, plus `curve`,
`specialize`, `map_specialize`, `polyEval`, are all project-local and equally
absent. The PR grain is the package, with `ringEval` as the corepresentability
map. (See the PR-grouping note below.)

WHY add it (refactor-actionable):
  - **New mathematical content / the gap.** Mathlib's EllipticCurve library has a
    rich coordinate-ring + division-polynomial API (`EllipticCurve/DivisionPolynomial/*`,
    `NumberTheory/EllipticDivisibilitySequence`) but **no universal/generic curve**
    — the standard tool for proving division-polynomial identities once and
    specializing. The concrete gap: mathlib's `EllipticDivisibilitySequence` file
    proves the EDS *recurrences* abstractly, but to show e.g. `ψₙ ≠ 0` for the
    generic curve (needed for the order of points / Nagell–Lutz / Hasse–Weil
    developments) one needs precisely this specialize-and-evaluate machinery. There
    is no mathlib decl for "specialize the universal curve and its universal point
    to a concrete `(W, x, y)`"; `ringEval` is that missing canonical map.
  - **Composition with existing API.** Once present, `ringEval` lets mathlib's
    `WeierstrassCurve.map`/`baseChange` and `Affine.CoordinateRing.map` compose with
    point-evaluation: the key bridge lemma `curveRing.map (ringEval eqn) = W`
    (`Universal.lean:237`) connects the universal curve's base change to any concrete
    curve, so universal results transport along it. The `ringEval_comp_smulRing` /
    `ringEval_ψ` lemmas then carry universal division-polynomial facts to every
    concrete `(x,y)` — exactly the API the division-polynomial files lack today.
Proposed mathlib location:    `Mathlib/AlgebraicGeometry/EllipticCurve/Universal.lean` (new file)
Proposed PR title:            "feat(AlgebraicGeometry/EllipticCurve): the universal Weierstrass curve and its specialization maps"
PR grouping (REQUIRED — this is the right grain):
  Ship `ringEval` together with the rest of the package as ONE PR (or a short
  ordered series), since none of it exists in mathlib and `ringEval`'s domain is
  defined by the others:
    - `WeierstrassCurve.Coeff` (the 5-element coefficient index)
    - `WeierstrassCurve.Universal.curve`, `Δ_curve_ne_zero`
    - `WeierstrassCurve.Universal.Poly`, `Universal.Ring`, `Universal.Field`, `pointedCurve`
    - `WeierstrassCurve.specialize`, `map_specialize`
    - `WeierstrassCurve.Universal.polyEval` (+ `polyEval_apply`, `polyEval_comp_eq_specialize`)
    - `WeierstrassCurve.Universal.ringEval` (THIS decl) + `ringEval_mk`, `ringEval_comp_mk`, `ringEval_comp_eq_specialize`, `curveRing_map_ringEval`
  These move as a unit; splitting `ringEval` out is not possible (its type mentions
  `Universal.Ring`).
Pre-PR checklist before opening:
  - [ ] First land/de-duplicate: this file is **forked across NagellLutz and HasseWeil**
        (near-byte-identical `Universal.lean`). Consolidate to one copy in `Common/`
        before upstreaming — the AINTLIB cleanup fleet's dedup lane should own this.
  - [ ] `/generalise WeierstrassCurve.Universal.ringEval` — confirm no further weakening (expected: none; already at `CommRing`).
  - [ ] `/cleanup projects/.../Universal.lean WeierstrassCurve.Universal.ringEval` — full audit + diff gates on the whole package.
  - [ ] Consider whether the package should be phrased via a represented-functor
        / universal-property class (`IsUniversal`-style) per Phase 4c — a design
        question for the mathlib reviewer, not a blocker.
  - [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` committers (e.g. the DivisionPolynomial / Jacobian authors — David Kurniadi Angdinata, Junyan Xu, who is also the original author of this file).

---

## Next step

Upstream `ringEval` **as part of the universal-Weierstrass-curve package** (one PR
to `Mathlib/AlgebraicGeometry/EllipticCurve/Universal.lean`), not in isolation —
its domain `Universal.Ring` and the `specialize`/`polyEval`/`map_specialize`
scaffold are equally missing from mathlib. First deduplicate the
NagellLutz/HasseWeil fork into `Common/`, then run `/generalise` and `/cleanup` on
the consolidated copy before opening the PR. Flag the represented-functor framing
(Phase 4c) as an open design question for the mathlib reviewer.
