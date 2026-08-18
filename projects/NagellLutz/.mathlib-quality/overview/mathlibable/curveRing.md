# /mathlibable report — `WeierstrassCurve.Universal.curveRing`

> One of the universal-curve base-change triple `curvePoly` / **`curveRing`** / `curveField`
> (`LutzNagell/Universal.lean:167–173`). This report mirrors its already-assessed siblings:
> `curve.md` (the genuinely-new object) → `YES-add-as-is`; `curvePoly.md` → `NO-composable`;
> `curveField.md` → `NO-composable`. `curveRing` is the third member of the same pattern.

### Baseline (Phase 0)
- lake build:               (not re-run — local build is stale per task note; reasoning from source)
- decl `WeierstrassCurve.Universal.curveRing`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:170`
- kind:                      `abbrev`  (reducible — a `WeierstrassCurve` term, not a `Prop`)
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — defines
  the universal Weierstrass curve over `ℤ[A₁..A₆]` and its base changes to `Poly`, `Ring`, `Field`.

**Qualified-name verification.** File has `namespace WeierstrassCurve` (line 69) → `namespace Universal`
(line 75); `curveRing` declared at line 170 inside both. Parsed qualified name
`WeierstrassCurve.Universal.curveRing` is **CONFIRMED**.

---

### Statement (Phase 1)

`curveRing` is the **base change of the universal Weierstrass curve to its own affine coordinate
ring**. Concretely:

```lean
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring
```

where `curve : Affine (MvPolynomial Coeff ℤ)` is the universal Weierstrass curve over
`ℤ[A₁,A₂,A₃,A₄,A₆]` (with `aᵢ = Xᵢ`), and `Universal.Ring := curve.CoordinateRing
= ℤ[A₁..A₆][X][Y]/⟨P⟩` is the coordinate ring of that curve (`P` = the Weierstrass polynomial).
So `curveRing` is the universal curve viewed as a curve over the ring it cuts out — the object
carrying the **generic/distinguished point** `(X, Y)` (the images of the coordinate variables).

Mathematically: take the universal family `𝓔 → Spec ℤ[A₁..A₆]`, pull it back along the structure
map `ℤ[A₁..A₆] → O = ℤ[A₁..A₆][X,Y]/⟨P⟩`. Over `O`, the tautological pair `(X mod P, Y mod P)` is a
point of the curve — this is the universal pointed curve at the level of the *ring* (its fraction
field gives `curveField = pointedCurve`, where the EDS/Jacobian arithmetic happens).

Variables / typeclasses (Lean side):
- none free — `curve`, `Universal.Ring` are fixed project-local terms; `[CommRing Universal.Ring]`
  is supplied by `curve.CoordinateRing`'s instance.

Hypotheses: none (it is a `def`/`abbrev`, not a theorem).

Conclusion (math): the universal curve as a `WeierstrassCurve` over its coordinate ring `O`.
Conclusion (Lean): `WeierstrassCurve Universal.Ring` — n/a, definition.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line reducible `abbrev` whose entire body is a single application of mathlib's
`WeierstrassCurve.baseChange` to the (separately-assessed) `curve`. Not a new structure (the new
structure is `curve`, assessed in `curve.md`); not a person-named theorem; not a `## Main results`
entry. It is the "view `curve` over its coordinate ring" plumbing for the EDS development.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`curve.baseChange Universal.Ring`).
One-liner verdict: **ONE-LINER** (kind is `abbrev` with a one-line body).

Exemption check:
| Exemption                         | Applies? | Evidence                                                                                  |
|-----------------------------------|----------|-------------------------------------------------------------------------------------------|
| Avoid defeq abuse (sealed barrier)| **no**   | It is an `abbrev` (reducible) — the *opposite* of a defeq barrier. Consumers in `ZSMul.lean` (`dblXYZ curveRing …`, `addXYZ curveRing …`) feed it positionally to division-polynomial functions that unfold it; no proof relies on it *not* unfolding. |
| Avoid typeclass diamonds          | **no**   | No instance is anchored on the `curveRing` name (grep: only the lemma `curveRing_map_ringEval` references it). The `CommRing Universal.Ring` instance comes from `CoordinateRing`, not from this abbrev. No colliding instance path. |
| Mark semantic intent / API name   | **partial** | The name + docstring are convenient handles, and 5 NagellLutz call sites + 5 HasseWeil call sites use it. But the *stable API anchor* that matters mathematically is `curve` (+ `CoordinateRing`); `curveRing` is local convenience, not a mathlib-API contract. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the partial semantic-intent point is local
convenience, not a mathlib-API anchor — same finding as `curvePoly.md`/`curveField.md`). Carried
into Phase 7 — biases toward a NO bucket.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | universal elliptic curve over coordinate ring, division polynomials, EDS formalization                 | yes  | universal curve `𝓔/Spec ℤ[a₁..a₆]`; coord ring `R[X,Y]/⟨W⟩`; ψₙ over `ℤ[a₁..a₆]` | Stange, Sutherland 18.783, Ward; classical, no "base-change-to-coord-ring" *name* |
|  2 | WebSearch (general / base-change)| "universal Weierstrass curve" base change to coordinate ring distinguished point generic point         | yes  | `A = ℤ[a₁..a₆]` parametrizes; coord ring `R[W]=R[X,Y]/⟨W⟩`; **base change a fundamental (unnamed) operation** | mathlib3 weierstrass docs; Sage `ell_generic`; Conrad minimal-models — base change is an operation, not a named object |
|  3 | WebSearch (named-after / aliases)| elliptic curve over its function field, generic point, Weierstrass coord ring, Silverman               | yes  | "generic fibre", "elliptic curve over `k(C)`"; `(x,y)↦(x/g²,y/g³)` coord changes | Silverman is the standard ref; the *fraction-field* version (= `curveField`) is the named one (generic fibre), not the *coordinate-ring* version |
|  4 | ChatGPT MCP                      | Is "base change a Weierstrass curve to its own coordinate ring" a named construction; what generality; standalone def or one-line base-change? | **n/a** | — | **MCP server down** (Codex exec failed — task note warned of this). Compensated with extra WebSearch breadth (#9, #10) + mathlib-source reading. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "universal" / "coordinate ring"                                 | **n/a** | (no `references/` dir for NagellLutz) | dir absent — recorded n/a; `refs/` store also absent on this checkout |
|  6 | nLab                             | moduli stack of elliptic curves / universal elliptic curve                                              | yes  | universal curve `𝓔 → 𝓜₁,₁`; Weierstrass model an object of `𝓜̄₁,₁(ℤ)` | nLab/MPIM Meier–Ozornova — the *moduli-theoretic* universal curve; no separate "curve over its coord ring" name |
|  7 | nCatLab (if categorical)         | (same as nLab — moduli stack)                                                                           | yes  | as #6                            | not a distinct categorical concept beyond the moduli stack |
|  8 | Stacks Project (if alg geom)     | moduli stack of elliptic curves (tag 072K)                                                              | yes  | Weierstraß model + zero-section ∈ `𝓜̄₁,₁(ℤ)`; any curve Zariski-locally Weierstraß | tag 072K — defines the universal *family*; base change to a coord ring is a derived operation, unnamed |
|  9 | MathOverflow / Math.StackExchange| universal Weierstrass curve generic point coordinate ring generality                                    | yes  | base change of universal curve = curve "with a point of order d over a ring where d invertible" | confirms base-change-of-universal as standard *technique*; not a named standalone object |
| 10 | recent arXiv (last 5 years)      | recurrence for EDS; division polynomials for arbitrary isogenies (Stange 2025); p-adic division polys   | yes  | ψₙ live in `ℤ[a₁..a₆][x,y]` / over the universal ring; evaluate-and-specialize | arXiv 2102.07573, eprint 2025/521 — universal ψₙ over `ℤ[a₁..a₆]` is the standard home; the *generic point* lives over the coord ring / its fraction field |

The protocol passes: WebSearch ran 4 distinct queries at three generality levels (specific,
base-change-general, named-aliases) + arXiv; nLab / nCatLab / Stacks / MathOverflow each checked;
local refs recorded n/a (absent). ChatGPT MCP is **down** (server failure, not a skip) and is
compensated by extra WebSearch + direct mathlib-source reading.

### Literature summary (Phase 3)

Concept identified as: **the universal Weierstrass / elliptic curve** (`𝓔` over `Spec ℤ[a₁..a₆]`,
equivalently over the universal coefficient ring), pulled back to its **coordinate ring**
`O = ℤ[a₁..a₆][X,Y]/⟨W⟩`, so as to carry the **generic point** `(X,Y)`.
Sources agree on the standard form: **yes** for the universal curve and its coordinate ring; but
**the specific act "base-change the curve to its coordinate ring" is universally treated as an
unnamed composition** — base change is "a fundamental operation," and what gets a name is the *curve*
and the *ring*, not their composite. The *fraction-field* version (the generic fibre / curve over the
function field) is the object with a classical name, and in this project that is `curveField`/
`pointedCurve` — not `curveRing`.
Most general standard form: the universal curve over **any** base, with base change available to any
algebra; the coordinate-ring base change is the universal/initial instance (`R = ℤ[a₁..a₆]`).
Generality dimensions where the literature varies:
  - base ring: from arbitrary `R` (Sage/mathlib `baseChange`) down to the universal `ℤ[a₁..a₆]`
    (Stange, division-polynomial literature). `curveRing` sits at the universal/initial end **by
    design** — that is the entire point of a *universal* object.
Disagreement with the literature: **none** — but the literature does not motivate a *separate named
definition* for "curve base-changed to its coordinate ring"; it is plumbing toward the generic point.

---

### Generality analysis — `WeierstrassCurve.Universal.curveRing`

Literature-standard form (from Phase 3): the universal curve over its coordinate ring is *the*
canonical/initial instance — there is no "more general `curveRing`" to aim at, because the whole
construction is the universal (initial) case. Generality lives entirely in the underlying `curve`
(over `ℤ`, the initial ring) and in mathlib's `baseChange` (any algebra).

| # | Parameter / hypothesis            | Current Lean form                  | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | base ring `Universal.Ring`        | `curve.CoordinateRing` (the universal coord ring) | the coordinate ring of the universal curve — initial by construction | **NO** | The base is *meant* to be the universal coordinate ring; generalising it would be a *different* object (`W.baseChange W.CoordinateRing` for arbitrary `W`), which is exactly the mathlib-call composition Phase 6 identifies, not a weakening of `curveRing`. |
| 2 | curve `curve`                     | universal curve over `ℤ[A₁..A₆]`   | universal curve over `ℤ` (initial)| **NO**              | Already maximally general (base `ℤ`); generality is assessed in `curve.md` (→ `YES-add-as-is`), not here. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (generality inherited from `curve`; the coordinate-ring
base change is the initial/universal instance by design).
Number of weakening opportunities found: **0**.
Proposed restatement: none (the only "generalisation" — `W.baseChange W.CoordinateRing` for arbitrary
`W` — is the mathlib-primitive composition of Phase 6, available to every consumer without a new def).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                    | no       | — | No hypotheses to instance-ify; it is a closed term. |
|  2 | sequences/metric → filters/topology?                                                               | no       | — | No analytic content. |
|  3 | construct an object where a universal-property class would characterise it?                        | **partial / no** | One could imagine `[IsUniversalCurve …]`, but the *concrete* universal curve `curve` is exactly what the project (and `curve.md`'s `YES`) ships; `curveRing` is just its base change. | The universal property already lives in `specialize` / `ringEval` / `map_specialize` (separate decls). `curveRing` itself needs no class. |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | — | Not a substructure. |
|  5 | vector-space/field-specific → modules/(semi)ring?                                                  | no       | base is already the universal coord ring (a `CommRing`); base change works for any algebra via mathlib. | n/a |
|  6 | 1-categorical → higher/∞-categorical?                                                              | no       | — | The moduli-stack `𝓔` (nLab/Stacks) is the ∞-flavour, but that is a different formalisation target, not a restatement of this one-line abbrev. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group?                                                   | no       | — | No index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: `curveRing` is already the mathlib-idiomatic spelling — `baseChange` is mathlib's
canonical base-change primitive. Any "modernisation" (a universal-property class, the moduli stack)
is a *different decl*, not a re-statement of this base change, and the universal property is already
carried by `specialize`/`ringEval` elsewhere in the file.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.curveRing`  (kind: `abbrev`)

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond            | **none**| `curveRing` is a `WeierstrassCurve` *term*, not an instance/structure; it anchors no typeclass search. The only instance in play, `CommRing Universal.Ring`, comes from `CoordinateRing`, not from this abbrev. |
| 2 | Reducibility leak            | **low** | As an `abbrev` it is reducible, so `simp`/`rfl` see `curve.baseChange Universal.Ring`. **Intended** — ZSMul consumers feed `curveRing` to `dblXYZ`/`addXYZ` and unfold freely. Tidy-before-upstreaming consideration only, and moot since the verdict is NO. |
| 3 | Non-canonical unfolding      | **low** | Unfolds to a single `baseChange`; no surprising `simp` behaviour. The `@[simp] pointedCurve_aᵢ` lemmas are on `pointedCurve`, not `curveRing`. |
| 4 | Instance priority collision  | **none**| Not an `instance`; no priority. |
| 5 | Universe-polymorphism issues | **none**| All types are fixed (`Type 0`: `MvPolynomial Coeff ℤ`, its coord ring); no universe variable. |
| 6 | Coercion ambiguity           | **none**| No `CoeFun`/`CoeSort` introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (a reducibility leak that is intended and, since the verdict is a NO bucket,
not added to mathlib anyway). Top risks: none HIGH. Mitigations: n/a.

---

### Mathlib search-status: `WeierstrassCurve.Universal.curveRing`

[A] Lean-Finder       "universal Weierstrass curve over coordinate ring", "curve base changed to its coordinate ring" — **no hit** (index has no `Universal.*` for Weierstrass curves)
[B] Loogle            `WeierstrassCurve.baseChange`, `WeierstrassCurve _ → WeierstrassCurve _`, `CoordinateRing` — `baseChange`/`map`/`CoordinateRing` **present**; **no** `curveRing`/`Universal.curve`
[C] LeanSearch        "universal elliptic curve over its coordinate ring", "Weierstrass curve over coordinate ring carrying generic point" — **no hit** for the object; surfaces `baseChange`/`CoordinateRing` only
[D] Grep mathlib src  `grep -rn 'Universal.curveRing|def curveRing|abbrev curveRing|namespace Universal' Mathlib/AlgebraicGeometry/` — **no hit** (only `UniversallyOpen`, unrelated). `Mathlib/.../EllipticCurve/` has **no `Universal.lean`**. `baseChange` at `Weierstrass.lean:236`; `CoordinateRing` at `Affine/Point.lean:90`. Notably `DivisionPolynomial/Basic.lean:36–38` *describes* the universal ring `𝓡[X,Y]=ℤ[A₁..A₆][X,Y]` in prose but **does not construct it as a `WeierstrassCurve`**. |
[E] Name pattern      `curveRing`, `Universal.curve`, `pointedCurve` in mathlib — **no hit** (these are project-local; the universal-curve file is unupstreamed, authored by Junyan Xu)

Searched for both:
  - the user's current form (`curve.baseChange Universal.Ring`) — not in mathlib;
  - the literature-standard form (universal curve over its coordinate ring) — not in mathlib (the
    universal curve object itself is absent; only the *prose description* exists in DivisionPolynomial).

Concluded: **found the building blocks (`WeierstrassCurve.baseChange` = `Weierstrass.lean:236`,
`WeierstrassCurve.map` = `:231`, `WeierstrassCurve.Affine.CoordinateRing` = `Affine/Point.lean:90`);
composition of base-change applied to the project-local `curve` would yield our form. The form itself
is NOT in mathlib, and neither is the underlying `Universal.curve`/`Universal.Ring`.**

---

### Call sites — `WeierstrassCurve.Universal.curveRing`

Internal use count (NagellLutz, excluding the declaring line): **5**
External-to-file callers (NagellLutz): **1 distinct file** (`ZSMul.lean`); plus the declaring file
itself (`Universal.lean:237`, the `curveRing_map_ringEval` lemma).

| Caller file:line                              | Usage pattern (one-line excerpt)                                            |
|-----------------------------------------------|------------------------------------------------------------------------------|
| LutzNagell/Universal.lean:237                 | `lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W`            |
| LutzNagell/ZSMul.lean:471                     | `dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n)`         |
| LutzNagell/ZSMul.lean:490                     | `smulRing_neg : … = (-1 : Universal.Ring) • neg curveRing (smulRing n)`      |
| LutzNagell/ZSMul.lean:525                     | `addXYZ curveRing (smulRing m) (smulRing n) = …`                            |
| LutzNagell/ZSMul.lean:538                     | `addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1)`    |

Inline-derivation grep: the **identical** `abbrev curveRing := curve.baseChange Universal.Ring` is
**re-declared verbatim in the HasseWeil project** (`HasseWeil/Auxiliary/Universal.lean:173`), with
its own 5 call sites there (`Universal.lean:240`, `DivisionPolynomial.lean:514/558/601/615`). So the
object is duplicated across two projects (a `Common/`-dedup target — but that is a *cleanup* concern,
not a mathlibable signal).

**Call-sites reading.** K = 5 internal uses (NagellLutz), no inline *re-derivation* within NagellLutz
(consumers use the name), and a cross-project duplicate. By the Phase-6.0.1 table this is "real API
within the project" — but the consumers all use `curveRing` as a **positional argument** to the
division-polynomial functions `dblXYZ`/`addXYZ`/`neg`/`map` (i.e. they want *some* curve over a ring
to run EDS arithmetic on), which is the classic "unfolds at the call site" tell: any
`curve.baseChange Universal.Ring` term would do. This points to NO-composable, not YES.

---

### Composition check (Phase 6)

Can `curveRing` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.baseChange curve Universal.Ring`
  - Mathlib decls used: `WeierstrassCurve.baseChange` (one call; `Weierstrass.lean:236`, itself
    `W.map (algebraMap R A)`).
  - Result: **succeeds** — this is *literally the body of the abbrev*. `Universal.Ring`
    (= `curve.CoordinateRing`) is mathlib's `CoordinateRing` of the project-local `curve`.
  - Notes: a single `baseChange` call. Per Phase 6b, "one function call" is a genuine composition,
    not a new development.

Attempt 2 (is it `rfl`-equal to an existing in-scope name, as `curveField` is to `pointedCurve`?):
  - **No.** grep shows no `rfl`-alias for `curveRing` (unlike `curveField_eq : curveField =
    pointedCurve := rfl`). So `curveRing` is *not* a literal duplicate of another local name — but it
    *is* still the one-call base change `curve.baseChange Universal.Ring`. The composition is the
    `baseChange` call itself, not "reuse a sibling name."

Conclusion: **COMPOSABLE** — `curveRing = WeierstrassCurve.baseChange curve Universal.Ring`, a single
mathlib `baseChange` of the project-local universal curve. No new lemma or instance is part of this
declaration (the only lemma *about* it, `curveRing_map_ringEval`, is a separate decl assessed on its
own). The genuinely-new content underneath is `curve` (+ `CoordinateRing`), assessed elsewhere.

---

## Verdict: `WeierstrassCurve.Universal.curveRing`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the universal curve and its coordinate ring are standard named
  objects, but "base-change the curve to its coordinate ring" is a **standard unnamed composition**
  — base change is "a fundamental operation," and the literature names the curve and the ring, not
  their composite. (The classically-*named* version is the fraction-field / generic-fibre one, which
  in this project is `curveField`/`pointedCurve`, not `curveRing`.)
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (inherited from `curve`); the coordinate-ring
  base change is the initial/universal instance by design. No generalise-first target. Modern-idiom:
  none (`baseChange` is already the idiomatic spelling).
- Diamond/defeq risk (Phase 4.5): **LOW** — intended reducibility leak; no instance anchored on the
  name, no diamond/priority exposure. Moot (NO bucket).
- Mathlib search (Phase 5): **not in mathlib**, and neither is `Universal.curve`/`Universal.Ring`;
  but `WeierstrassCurve.baseChange`/`map` and `Affine.CoordinateRing` are all present.
- Composition check (Phase 6): **COMPOSABLE** — `curve.baseChange Universal.Ring`, a single mathlib
  `baseChange` call. 5 NagellLutz call sites (+ a verbatim HasseWeil duplicate), but every consumer
  feeds it positionally to EDS functions that unfold it — the "inline-able" pattern.

**Rationale:**

`curveRing` denotes a mathematically real object — the universal Weierstrass curve viewed over its
own coordinate ring `O = ℤ[A₁..A₆][X,Y]/⟨P⟩`, the carrier of the generic point `(X,Y)` and the home
of this project's division-polynomial `smulRing` arithmetic (5 call sites). But the mathlibable
question is "should mathlib have **this declaration**," and `curveRing` is a **one-line reducible
`abbrev`** equal to `WeierstrassCurve.baseChange curve Universal.Ring`. mathlib already owns
`baseChange` (`Weierstrass.lean:236`) and `CoordinateRing` (`Affine/Point.lean:90`); the only
genuinely new objects underneath are `curve` and `Universal.Ring`, each assessed separately
(`curve.md` → `YES-add-as-is`). Once `curve` (with its coordinate ring and `specialize`/`ringEval`
API) lands in mathlib, `curveRing` adds **no new mathematical content** beyond a single `baseChange`
call.

This is the exact structural situation of its already-assessed siblings: `curvePoly`
(`curve.baseChange Poly`) and `curveField` (`curve.baseChange Universal.Field`) were *both* ruled
`NO-composable-from-mathlib`, and `curveRing` is the third member of the same `curvePoly`/`curveRing`/
`curveField` triple (`Universal.lean:167–173`). Its only Phase-2b exemption candidate is "API name,"
and it is the *weakest* form of that: the abbrev is reducible (no defeq-barrier exemption — consumers
unfold it), and no instance is anchored on it (no diamond-avoidance exemption — unlike `pointedCurve`,
which carries the `IsElliptic` instance and the `@[simp]` coefficient API). The canonical mathlib
organisation is therefore to ship `curve` + `CoordinateRing` (already mathlib's) and let consumers
write `curve.baseChange Universal.Ring` directly — not to ship a third reducible alias for a base
change. (One distinction from `curveField`: `curveRing` is *not* `rfl`-equal to another in-scope
name, so it is not a literal in-file duplicate — but it is still a single `baseChange` call, which is
exactly the NO-composable criterion.)

The verdict is **NO-composable**, not NO-mathlib-has-it: mathlib does **not** contain this object
(nor `Universal.curve`), only the building blocks to compose it. And it is not BORDERLINE: the
composition is a clean single `baseChange` call with no cost-driven judgment, and the sibling
assessments fix the consistent answer.

**WHY not (refactor-actionable):**
- Mathlib has the building blocks. `curveRing` is `WeierstrassCurve.baseChange curve Universal.Ring`
  — a single mathlib `baseChange` (`Weierstrass.lean:236`, itself `W.map (algebraMap R A)`) applied
  to the project-local universal curve `curve`, with base ring `Universal.Ring = curve.CoordinateRing`
  (mathlib's `CoordinateRing`, `Affine/Point.lean:90`). No accompanying lemma or instance is part of
  *this* declaration (`curveRing_map_ringEval` is a separate decl, assessed on its own).
- Mathlib building blocks (qualified names):
  - `WeierstrassCurve.baseChange` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`
  - `WeierstrassCurve.map` — `…/Weierstrass.lean:231`
  - `WeierstrassCurve.Affine.CoordinateRing` — `…/EllipticCurve/Affine/Point.lean:90`
- Composition sketch (≤3 lines), once `curve` (+ `Universal.Ring`) is available:
  ```lean
  -- curveRing is definitionally this; inline at call sites:
  example : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring
  -- e.g. ZSMul.lean:471 becomes:
  --   dblXYZ (curve.baseChange Universal.Ring) (smulRing n) = smulRing (2 * n)
  ```
- Call sites in our project (from Phase 6.0): **K = 5** (NagellLutz; + 5 in HasseWeil's duplicate).
- Refactor plan: this is **not** an upstream-to-mathlib action — it is a *don't-upstream-`curveRing`*
  finding. The mathlib-bound work is `curve` (per `curve.md`'s `YES-add-as-is`) together with its
  coordinate ring / `specialize` API. For `curveRing` specifically: **keep it as the project-local
  convenience abbrev** (it is fine in-project), but do not propose it as a standalone mathlib
  addition; consumers would write `curve.baseChange Universal.Ring` (or use a single shared local
  alias). Within AINTLIB, the verbatim NagellLutz/HasseWeil duplication is a separate **`Common/`
  dedup** cleanup ticket (out of scope for mathlibable). At each of the 5 NagellLutz call sites, the
  refactor (if `curveRing` were ever removed) is a mechanical substitution of
  `curve.baseChange Universal.Ring` for `curveRing` — argument positions are unchanged
  (`dblXYZ`/`addXYZ`/`neg`/`map` take the curve as their leading explicit argument).

---

## Next step

Do **not** propose `curveRing` as a standalone mathlib addition. It is `NO-composable-from-mathlib`:
a single `WeierstrassCurve.baseChange curve Universal.Ring` call. The mathlib-bound object is
`Universal.curve` (see `curve.md` → `YES-add-as-is`) plus its coordinate-ring / `specialize` API;
ship that, after which `curveRing` is just `curve.baseChange Universal.Ring` at each of its 5 call
sites. Separately, file a `Common/`-dedup cleanup ticket for the verbatim NagellLutz ↔ HasseWeil
duplication of the whole `Universal` block (cleanup lane, not mathlibable).
