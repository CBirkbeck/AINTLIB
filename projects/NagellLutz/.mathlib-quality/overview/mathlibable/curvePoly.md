# /mathlibable report — `WeierstrassCurve.Universal.curvePoly`

### Baseline (Phase 0)
- lake build:               not run (env build stale — per task note; reasoning from source statement)
- decl `WeierstrassCurve.Universal.curvePoly`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:167`
- kind:                      `abbrev`
- has sorry:                 no
- module docstring summary:  Additions to `Affine.Point` plus the universal elliptic curve over `ℤ[A₁..A₆]` and the universal pointed elliptic curve over `Frac(ℤ[A₁..A₆,X,Y]/⟨P⟩)`, with specialization homomorphisms and the cusp curve `Y²=X³`.

Qualified name VERIFIED: nested `namespace WeierstrassCurve` → `namespace Universal`, so the full name is `WeierstrassCurve.Universal.curvePoly` (the parsed guess was correct).

---

### Statement (Phase 1)

```lean
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly
```

`curvePoly` is a **definition** (abbreviation). It is the universal Weierstrass curve
`curve` — the curve `y² + A₁xy + A₃y = x³ + A₂x² + A₄x + A₆` over the universal-coefficient
ring `MvPolynomial Coeff ℤ = ℤ[A₁,A₂,A₃,A₄,A₆]` — **base-changed** (via the structure
ring map `ℤ[A₁..A₆] → ℤ[A₁..A₆,X,Y]`) to the bivariate polynomial ring
`Poly := (MvPolynomial Coeff ℤ)[X][Y] = ℤ[A₁..A₆,X,Y]`. The result is the same Weierstrass
curve now viewed with coefficients in the larger ring `Poly`, which additionally contains the
two affine coordinate indeterminates `X`, `Y` (needed so that the Weierstrass polynomial `P`,
the division polynomials `ψₙ`, `φₙ`, `ωₙ`, and the Jacobian addition polynomials live in a
single ambient ring before passing to the coordinate-ring quotient `Poly/⟨P⟩` = `Universal.Ring`).

Variables / typeclasses involved (Lean side):
- none — `curvePoly` is a closed term; `curve : Affine (MvPolynomial Coeff ℤ)` and
  `Poly : Type` are both fixed project-internal objects, and `[Algebra (MvPolynomial Coeff ℤ) Poly]`
  is the canonical polynomial-ring algebra instance.

Hypotheses (Lean side): none.

Conclusion (math): the universal curve regarded over `ℤ[A₁..A₆,X,Y]`.
Conclusion (Lean): `WeierstrassCurve Poly` — n/a, this is a definition.

It is the first of a trio of sibling base-change abbreviations defined together
(lines 167–175):
```lean
abbrev curvePoly  : WeierstrassCurve Poly           := curve.baseChange Poly
abbrev curveRing  : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field
```
viewing `curve` over the three rings of the tower `Poly → Poly/⟨P⟩ = Ring → Frac(Ring) = Field`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a convenience `abbrev` that base-changes an already-defined curve along an already-defined
ring map; not a new mathematical structure, not a `## Main results` entry, not named after a
person/place. (The genuinely-substantive object here is `curve` / the universal curve, not this
particular base change of it.)

(Literature width was run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`curve.baseChange Poly`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | It is an `abbrev` (reducible) — the opposite of a sealing barrier. Call sites in `ZSMul.lean` and `HasseWeil` literally `unfold ... curvePoly` to expose the body (e.g. `ZSMul.lean:438`, `:481`), so the def is *meant* to unfold, not to block unfolding. |
| Avoid typeclass diamonds          | no       | No instance is anchored on it; the `[Algebra (MvPolynomial Coeff ℤ) Poly]` path is mathlib's standard polynomial-ring algebra instance, used directly. |
| Mark semantic intent / API name   | partial  | It does carry a name + docstring and 1 internal consumer reads it via `dblZ curvePoly (smulPoly n)`. But the name is purely local scaffolding ("the curve over `Poly`"), not a stable public-API surface; mathlib's own division-polynomial API never names such an intermediate (it threads `(W⁄A)` inline). |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the partial semantic-intent point is local convenience, not a mathlib-API anchor). Carried into Phase 7 — biases toward a NO bucket.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | universal Weierstrass curve over `ℤ[a1..a6]` universal coefficients                                      | yes  | The ring `A = ℤ[a₁,a₂,a₃,a₄,a₆]` parametrising Weierstrass curves; the **universal curve `𝓔 → Spec A`** | Cremona Ch.3, Sage `ell_generic`, arXiv 2003.08454, 1312.7394 (tmf). The *universal curve over `ℤ[a₁..a₆]`* is standard. None name the **further** base change to `ℤ[a₁..a₆,X,Y]`. |
|  2 | WebSearch (general form)         | "universal elliptic curve" base change Weierstrass division polynomial generic                           | yes  | Generic curve over `Frac(ℤ[a₁..a₆])` / its alg. closure; division polys `Ψₙ` defined there | arXiv 1303.4327, 1303.5002, 1108.3051. Literature passes from `ℤ[a₁..a₆]` straight to the function field; the bivariate poly ring `ℤ[a₁..a₆,X,Y]` is an unnamed intermediate. |
|  3 | WebSearch (named-after / aliases)| "generic Weierstrass curve" / universal curve coordinate ring affine                                     | yes  | "generic curve", "universal curve"; coordinate ring `ℤ[a₁..a₆,x,y]/⟨P⟩` | The quotient (= our `Universal.Ring`) is named (the affine coordinate ring); the *pre-quotient base-changed curve* (our `curvePoly`) is not a named object. |
|  4 | ChatGPT MCP                      | "Is `E_univ` base-changed to `ℤ[A₁..A₆,X,Y]` a named standard object, or unnamed scaffolding?"           | n/a  | — | **MCP down** in this env (Codex command failed; the task note warned of this). Fallback: WebSearch #1–3 + domain reasoning, which already answer the question (the bivariate base change is unnamed scaffolding). |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                  | n/a  | (no references dir) | Directory absent — recorded n/a. |
|  6 | nLab                             | "elliptic curve" universal / moduli stack of elliptic curves                                             | yes  | nLab "moduli stack of elliptic curves `M_ell`"; universal curve `𝓔 → M_ell` | nLab discusses the universal curve over the moduli stack / over `ℤ[a₁..a₆]`; it does not name a base change to a bivariate polynomial ring. |
|  7 | nCatLab (if categorical)         | — (same as nLab; concept is the universal curve over `M_ell`)                                            | n/a  | — | Not a distinct categorical concept beyond the universal curve already covered in #6. |
|  8 | Stacks Project (if alg geom)     | moduli of elliptic curves / Weierstrass equations (Tag 0CL0 area)                                        | yes  | Universal Weierstrass curve / Weierstrass data over `ℤ[a₁..a₆]` | Stacks frames it scheme-theoretically over `Spec ℤ[a₁..a₆]`; again the affine-ring intermediate is unnamed plumbing. |
|  9 | MathOverflow / Math.StackExchange| "universal elliptic curve" coordinate ring division polynomial                                           | yes  | Confirms #1–3; the working ring for division polynomials is `ℤ[a₁..a₆,x,y]` then its function field | No named status for the curve-over-`ℤ[a₁..a₆,x,y]` as a standalone object. |
| 10 | recent arXiv (last 5 years)      | universal / generic elliptic curve division polynomial base change (2020–2025)                           | yes  | 2003.08454 (homogeneous division polys), 1312.7394 (tmf level structure) | Use the universal curve and its base changes freely **inline**; none introduce a named symbol for `E_univ ⊗ ℤ[a₁..a₆,x,y]`. |

The protocol passes: WebSearch ran 3 distinct generality levels (#1 specific, #2 general/function-field, #3 aliases); ChatGPT MCP attempted (down — fallback used); local refs checked (n/a); nLab, Stacks, nCatLab, MathOverflow, arXiv all checked.

### Literature summary (Phase 3)

Concept identified as: the **universal (generic) Weierstrass curve** over `ℤ[a₁,a₂,a₃,a₄,a₆]`
(`curve` in this project) — a standard, well-named object. `curvePoly` is **not** that object;
it is the **base change of it to the bivariate polynomial ring `ℤ[a₁..a₆,X,Y]`**, an
**unnamed intermediate** in the literature.
Sources agree on the standard form: yes — for the universal curve over `ℤ[a₁..a₆]`. For the
specific bivariate base change there is no standard name; every source either works inline or
passes directly to the coordinate ring `ℤ[a₁..a₆,x,y]/⟨P⟩` (a named object — our `Universal.Ring`)
or the function field.
Most general standard form: the universal curve `𝓔 → Spec ℤ[a₁..a₆]`; base changes of it are
taken on demand, not named.
Generality dimensions where the literature varies:
  - base ring it's viewed over: `ℤ[a₁..a₆]` → its polynomial extensions → the coordinate ring `…/⟨P⟩` → the function field. `curvePoly` sits at the "`…[x,y]`, pre-quotient" rung — the rung literature treats as plumbing.
Disagreement with the literature: none — but the literature does **not** reify this particular base change as a named object.

---

### Generality analysis — `WeierstrassCurve.Universal.curvePoly`

Literature-standard form (from Phase 3): the universal curve is a curve over `ℤ[a₁..a₆]`; one
base-changes it to whatever ring is convenient, **inline**, using the generic base-change operation.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | target ring `Poly` (fixed) | the concrete `ℤ[a₁..a₆,X,Y]` | any `R`-algebra (base change is generic in the target) | yes — but that's exactly mathlib's already-general `baseChange`! | The genuinely general statement is *"a Weierstrass curve over `R` base-changes to any `R`-algebra `A`"*, which is precisely `WeierstrassCurve.baseChange` (Weierstrass.lean:236). `curvePoly` is the **specialisation** `A := Poly` of that general operation, applied to the specific curve `curve`. |
| 2 | source curve `curve` (fixed) | the universal curve over `ℤ[a₁..a₆]` | the universal curve (standard) | n/a | `curve` itself is the substantive object — but it is **not in mathlib** (see Phase 5), so a base change of it cannot be either. |

### Generality verdict (Phase 4b)

The current form is: **n/a — it is a fully-specialised instance of an already-maximally-general mathlib operation.**
Number of weakening opportunities found: 0 *as a standalone lemma* (generalising it just recovers
mathlib's `baseChange`, which already exists). `curvePoly` is the **opposite** of a generalisation
target: it is a point-specialisation `(curve, Poly)` of `WeierstrassCurve.baseChange`.
Proposed restatement: none — there is nothing to generalise; the general form already ships in mathlib.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | No bundled hypothesis here; it is a closed term. |
|  2 | sequences/metric → filters/topology? | no | — | No analytic content. |
|  3 | construction → universal-property class? | no | — | `baseChange` is already the canonical construction; `curvePoly` is just an evaluation of it. |
|  4 | set+closure-pred → bundled substructure? | no | — | No substructure. |
|  5 | vector-space/field-specific → weaken typeclass? | no | — | Already over a general `CommRing`/`Algebra`. |
|  6 | 1-categorical → higher-categorical? | no | — | The honest modern idiom is precisely the existing `baseChange` / the `⁄` notation; mathlib's own division-polynomial file uses `(W⁄A)` **inline** and never names such an intermediate (see `DivisionPolynomial/Basic.lean:553–566`, the `baseChange_*` lemmas). |
|  7 | concrete index → arbitrary structure? | no | — | The "index" (target ring `Poly`) generalising to "any algebra" is, once more, just `baseChange`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (in the sense of "a better named object to ship") — the idiomatic
mathlib move is the **opposite**: don't name this base change at all; write `curve⁄Poly`
(`baseChange curve Poly`) inline, exactly as mathlib's division-polynomial API threads `(W⁄A)`.
One-line reason: this is not a modernisation move; it is a convenience alias whose modern,
mathlib-idiomatic replacement is to inline the existing `baseChange` at each use.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.curvePoly`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | No instance is declared with `curvePoly` in its head; it is a plain `abbrev` of a term. The only instance in play, `[Algebra (MvPolynomial Coeff ℤ) Poly]`, is mathlib's standard polynomial algebra and is used identically with or without this alias. |
| 2 | Reducibility leak | low | As an `abbrev` it is `@[reducible]`, so its body `curve.baseChange Poly` is exposed to defeq everywhere. In-project this is *intended* (call sites `unfold curvePoly`). For mathlib it would be a (minor) reason to prefer inlining rather than shipping a reducible alias. |
| 3 | Non-canonical unfolding | none | Unfolding yields exactly `baseChange curve Poly`; no surprising `simp`/`rfl` behaviour beyond what `baseChange` already has. |
| 4 | Instance priority collision | n/a | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | Everything is at `Type 0` (concrete rings over `ℤ`); no universe variables. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort` introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (the single `low` is the reducibility of the `abbrev`, which is harmless
internally and merely reinforces "inline it" for mathlib).
Top risks: none HIGH.

---

### Mathlib search-status: `WeierstrassCurve.Universal.curvePoly`

[A] Lean-Finder       n/a — mathlib-index tool unavailable in this env.
[B] Loogle            n/a — mathlib-index tool unavailable in this env.
[C] LeanSearch        n/a — mathlib-index tool unavailable in this env.
[D] Grep mathlib src  `curvePoly`, `curve.baseChange`, `Universal.*WeierstrassCurve`, `WeierstrassCurve.Universal`, `MvPolynomial Coeff` over `.lake/packages/mathlib/`  →  **no hits** (zero). Also `abbrev/def … WeierstrassCurve … := … baseChange` over all of mathlib → **no hits**: mathlib never names a base-changed Weierstrass curve.
[E] Name pattern      grep mathlib EC tree for any `Universal`/`universal.*curve`/`five.*coeff` Weierstrass concept → **no hits**. `grep -ri Universal` in mathlib hits only ModelTheory/Padics/AG-morphisms — none is a universal elliptic curve.

Building blocks that DO exist in mathlib:
  - `WeierstrassCurve.baseChange` — `.lake/.../EllipticCurve/Weierstrass.lean:236`
    `def baseChange (A) [Algebra R A] : WeierstrassCurve A := W.map (algebraMap R A)`
  - `WeierstrassCurve.map` — `Weierstrass.lean:231`
  - scoped notation `W⁄A` for `baseChange W A` — `Weierstrass.lean:240`
  - the mathlib idiom `(W⁄A)` used inline throughout `DivisionPolynomial/Basic.lean` (e.g. `baseChange_ψ₂`, `:553–566`) — confirming mathlib does **not** name such intermediates.

Searched for both:
  - the user's current form (`curve.baseChange Poly`) — not in mathlib (neither `curve` nor `Poly` exist there).
  - the literature-standard "universal curve over `ℤ[a₁..a₆]`" — also **not in mathlib** (no `Universal` Weierstrass-curve concept at all). This is itself notable: the *base* object `curve` is a project original, so any base change of it is too.

Concluded: **"not in mathlib (all available methods exhausted, plus the literature-standard form); but the building block `WeierstrassCurve.baseChange` exists and `curvePoly` is a single application of it."**

---

### Call sites — `WeierstrassCurve.Universal.curvePoly`

Internal use count (NagellLutz, excluding declaring file `Universal.lean`): **K = 2 lemmas** —
all in `projects/NagellLutz/LutzNagell/ZSMul.lean`.
External-to-file callers: 1 file within the project (`ZSMul.lean`). (Note: `HasseWeil` carries
a byte-identical *fork* — `HasseWeil/Auxiliary/Universal.lean:170` defines its own `curvePoly`,
and `HasseWeil/Auxiliary/DivisionPolynomial.lean` uses it the same way. That is duplication of
the whole `Universal` scaffolding across two projects, not an external consumer of *this* decl.)

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ZSMul.lean:437   | `lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by` |
| ZSMul.lean:438   | `  unfold dblZ smulPoly WeierstrassCurve.Jacobian.negY curvePoly`  (unfolds it!) |
| ZSMul.lean:480   | `lemma ω_neg_eq_neg_negY : curve.ω (-n) = -negY curvePoly (smulPoly n) := by` |
| ZSMul.lean:481   | `  unfold smulPoly WeierstrassCurve.Jacobian.negY curvePoly`  (unfolds it!) |
| ZSMul.lean:487   | `lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by` |

Inline-derivation grep: the equivalent `curve.baseChange Poly` is the body itself; both call
sites that prove something immediately `unfold curvePoly` back to it — i.e. consumers treat it
as a name to be unfolded, not an opaque API. (none re-derived under a different name.)

Composability signal: K = 2 internal uses, both of which `unfold` the alias away → "could be
inlined" leaning (K small, and the def is used by being unfolded, the classic NO-composable tell).

---

### Composition check (Phase 6)

Can `WeierstrassCurve.Universal.curvePoly` be obtained from mathlib in ≤3 chained calls?

Attempt 1: `curvePoly := curve.baseChange Poly`  (≡ `WeierstrassCurve.baseChange curve Poly`, or in
notation `curve⁄Poly`).
  - Mathlib decls used: `WeierstrassCurve.baseChange` (1 call).
  - Result: **succeeds** — this *is* the definition; it is one application of a single mathlib
    primitive to the project-local `curve` and `Poly`.
  - Notes: the only non-mathlib ingredients are `curve` (the universal curve — a project
    original, not mathlib) and `Poly` (a project type abbreviation). So `curvePoly` adds **no
    new mathematics** on top of `baseChange`; it is a 1-call specialisation.

Conclusion: **COMPOSABLE** (1 mathlib call). The composition is `baseChange curve Poly`; mathlib's
own elliptic-curve code inlines exactly this kind of base change via the `⁄` notation rather than
naming it.

---

## Verdict: `WeierstrassCurve.Universal.curvePoly`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the *universal curve over `ℤ[a₁..a₆]`* is standard and named, but its base change to the bivariate ring `ℤ[a₁..a₆,X,Y]` is unnamed scaffolding everywhere (Cremona, Sage `ell_generic`, Stacks, nLab, arXiv 1303.4327 / 2003.08454).
- Generality analysis (Phase 4): not a generalisation target — generalising the fixed target `Poly` to "any algebra" just recovers mathlib's already-general `baseChange`; Phase 4c says the modern idiom is to inline it as `curve⁄Poly`.
- Mathlib search (Phase 5): not in mathlib (no `curvePoly`, no `Universal` Weierstrass curve), but the building block `WeierstrassCurve.baseChange` (Weierstrass.lean:236) exists.
- Composition check (Phase 6): COMPOSABLE — `baseChange curve Poly`, a single mathlib call.

**Rationale:**

`curvePoly` is a one-line, reducible `abbrev` equal to `curve.baseChange Poly` — a single
application of mathlib's existing `WeierstrassCurve.baseChange` to two project-local objects: the
universal curve `curve` (over `ℤ[a₁..a₆]`) and the bivariate polynomial ring `Poly = ℤ[a₁..a₆,X,Y]`.
It contributes **no new mathematical content** beyond `baseChange`; it merely fixes the target
algebra to `Poly`. The literature confirms that while the universal curve itself is a named,
standard object, the specific base change of it to the `[X,Y]`-adjoined polynomial ring is unnamed
plumbing — every source either works inline or passes straight to the coordinate ring `…/⟨P⟩` (which
*is* named — that is `Universal.Ring`) or the function field. Decisively, mathlib's **own**
division-polynomial development (`DivisionPolynomial/Basic.lean`, the `baseChange_*` lemmas at
lines 553–566) threads base-changed curves **inline** as `(W⁄A)` / `(W⁄B)` and never introduces a
named intermediate of this kind — so shipping `curvePoly` would cut against mathlib's established
idiom.

The one-liner has **no Phase-2b exemption** (it is reducible and is actively `unfold`ed at its call
sites, so it is neither a defeq barrier nor a diamond anchor; its name is local scaffolding, not a
stable API surface), and it has only K = 2 internal consumers, both of which immediately unfold it.
The Phase-4.5 risk is LOW (only the harmless reducibility of the `abbrev`). All signals point the
same way: this is a convenience alias, not a mathlib contribution. Note too that the *base* object
`curve` is itself a project original absent from mathlib, so even setting aside composability,
`curvePoly` could not be added without first adding the entire `Universal` curve apparatus — and the
right mathlib form of *that* is a separate, larger question about the universal Weierstrass curve, of
which this particular base change would still just be an inlined `baseChange`.

**WHY not (refactor-actionable):**
Mathlib already provides the building block `WeierstrassCurve.baseChange`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`) together with its `⁄` notation
(`:240`). `curvePoly` is the trivial composition `baseChange curve Poly`. No new lemma is warranted;
inline at the (few) call sites, matching mathlib's own inline-`(W⁄A)` division-polynomial style.

Mathlib building blocks:
  - `WeierstrassCurve.baseChange` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`
  - scoped notation `W⁄A` (= `baseChange W A`) — `…/Weierstrass.lean:240`

Composition sketch (1 mathlib call):
```lean
-- replace `curvePoly` everywhere with:
curve.baseChange Poly      -- equivalently, with the scoped notation:  curve⁄Poly
```

Call sites in this project (from Phase 6.0): **K = 2** (both in `ZSMul.lean`: `dblZ_smulPoly`
at :437–438, `ω_neg_eq_neg_negY` at :480–481; `smulPoly_neg` at :487 also references it).

Refactor plan:
  1. At `ZSMul.lean:437`, `:480`, `:487`, replace `curvePoly` with `curve.baseChange Poly`
     (or `curve⁄Poly` once `open scoped` brings the notation in scope).
  2. In the proofs at `:438` and `:481`, the lines currently read `unfold ... curvePoly`. After
     inlining, drop `curvePoly` from the `unfold` list (it is no longer a name); if the proof
     needed the unfolding, `unfold WeierstrassCurve.baseChange WeierstrassCurve.map` (or the
     relevant `baseChange`/`map` simp lemmas) reproduces the same exposed term. Re-run the proof
     to confirm `dblZ`/`negY`/`neg` still reduce identically (they will — `curvePoly` was defeq to
     the inlined term).
  3. Delete the `curvePoly` abbreviation from `Universal.lean:167`.
  4. **Cross-project note (not part of this decl's refactor, but flag for the fleet):** `HasseWeil`
     carries a duplicate `curvePoly` (`Auxiliary/Universal.lean:170`) with the same call pattern in
     `Auxiliary/DivisionPolynomial.lean`. The same inline-and-delete applies there; better, the
     whole duplicated `Universal` scaffolding across NagellLutz and HasseWeil is a dedup target for a
     `Common/` consolidation ticket.

**Caveat / lower-confidence note:** the mathlib-index search tools (Loogle / LeanSearch /
Lean-Finder) were unavailable in this environment and ChatGPT MCP was down; methods [A][B][C] are
n/a. The conclusion rests on direct grep of the mathlib source tree ([D]/[E], authoritative for
"does this name/concept exist") plus the literature sweep — and the verdict is robust because the
*base* object (`curve` / the universal curve) is demonstrably absent from mathlib, which by itself
precludes `NO-mathlib-has-it` and forces the question onto composability, where the answer is a clean
single `baseChange` call.

---

## Next step

Delete `WeierstrassCurve.Universal.curvePoly` from `Universal.lean:167` and inline the composition
`curve.baseChange Poly` (≡ `curve⁄Poly`) at its 2 call sites in `ZSMul.lean`, adjusting the two
`unfold` lines to unfold `WeierstrassCurve.baseChange`/`map` instead. Mirror in `HasseWeil`'s fork,
and consider a `Common/` consolidation ticket for the duplicated `Universal` scaffolding.
