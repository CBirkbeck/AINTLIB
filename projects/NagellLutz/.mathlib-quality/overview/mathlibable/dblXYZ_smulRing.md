# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulRing`

> The universal-ring form of the **doubling formula on division-polynomial triples**: applying
> mathlib's Jacobian doubling map `dblXYZ` to the universal `(φₙ, ωₙ, ψₙ)` reproduces `(φ₂ₙ, ω₂ₙ, ψ₂ₙ)`
> as an identity in the universal coordinate ring `Universal.Ring`. It is one **internal reduction
> step** in this file's proof of the scalar-multiplication formula `WeierstrassCurve.zsmul_eq_smulEval`
> (`ZSMul.lean`). Sibling triple: `dblXYZ_smulField` (field-level, the substantive identity, line 460)
> → **`dblXYZ_smulRing`** (this, the ring-level transfer, line 471) → `dblXYZ_smulEval` (concrete-curve,
> line 568). Field/Poly twins not yet separately assessed; the `curveRing`/`smulRing`/`smulPoly`
> *object* reports → `NO-composable`/internal.

### Baseline (Phase 0)
- lake build:               (not re-run — local build is stale per task note; reasoning from source)
- decl `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulRing`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:471`
- kind:                      `lemma` (a `Prop` — an equation of `Fin 3 → Universal.Ring`)
- has sorry:                 no
- module docstring summary:  "Integer multiples of a rational point on an elliptic curve in terms of
  division polynomials" — proves `WeierstrassCurve.zsmul_eq_smulEval`
  (`n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coords). Lines 24–29 explicitly frame `dblXYZ_smulRing` /
  `addXYZ_smulRing` as the **universal polynomial-identity reduction step** of that proof.

**Qualified-name verification.** `ZSMul.lean` opens `namespace WeierstrassCurve` (line 76) →
`namespace Universal` (line 86) → `namespace Jacobian` (line 395, closed at 544). `dblXYZ_smulRing` is
declared at line 471, inside all three. Parsed qualified name
`WeierstrassCurve.Universal.Jacobian.dblXYZ_smulRing` is **CONFIRMED**.

---

### Statement (Phase 1)

```lean
lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ Universal.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField
```

Implicit context (from the surrounding `variable`s / `noncomputable section`):
- `{n : ℤ}` — the index (set in the `Universal` block, `ZSMul.lean:97`).
- `smulPoly n := ![curve.φ n, curve.ω n, curve.ψ n] : Fin 3 → Poly` (line 414) — the three universal
  division polynomials packed as a Jacobian coordinate triple.
- `smulRing n := AdjoinRoot.mk _ ∘ smulPoly n : Fin 3 → Universal.Ring` (line 416) — those polynomials
  pushed into `Universal.Ring := curve.CoordinateRing = ℤ[A₁..A₆][X][Y]/⟨W⟩` (`Universal.lean:96`).
- `curveRing := curve.baseChange Universal.Ring : WeierstrassCurve Universal.Ring` (`Universal.lean:170`).
- `dblXYZ` — **mathlib's** Jacobian doubling map (`Jacobian/Formula.lean:349`), the coordinate-level
  formula for `2 • P` in Jacobian `(X : Y : Z)` coordinates.

**Math content.** Over the universal coordinate ring `O = ℤ[A₁..A₆][X,Y]/⟨W⟩` (the home of the generic
point `(X, Y)`), the Jacobian doubling formula applied to the division-polynomial triple `(φₙ, ωₙ, ψₙ)`
equals the doubling-index triple `(φ₂ₙ, ω₂ₙ, ψ₂ₙ)`:
$$ \mathrm{dblXYZ}\big(\varphi_n,\ \omega_n,\ \psi_n\big) \;=\; \big(\varphi_{2n},\ \omega_{2n},\ \psi_{2n}\big) \quad\text{in } O . $$
This is the Jacobian-coordinate packaging of the classical division-polynomial **doubling recursions**
(`ψ₂ₙ = ψₙ(ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)/ψ₂`, with the matching `φ₂ₙ`, `ω₂ₙ`), which encode
`2 • (n • (X,Y)) = (2n) • (X,Y)` at the level of the universal generic point. The equality holds
*modulo the Weierstrass polynomial* (i.e. in the quotient `O`, not in the free polynomial ring `Poly`).

Hypotheses: none beyond `n : ℤ` (no nonvanishing or characteristic hypothesis — that is what makes the
universal-ring statement clean; the field twin handles `n = 0` and the `ψₙ ≠ 0` quotient argument).

Conclusion (Lean): `dblXYZ curveRing (smulRing n) = smulRing (2 * n)`, an equation in `Fin 3 → Universal.Ring`.

**Proof (one line, a transfer).** Pass to the fraction field `Universal.Field = FractionRing Universal.Ring`.
`IsFractionRing.injective _ Universal.Field` is the injectivity of `algebraMap Universal.Ring Universal.Field`
(mathlib, `FractionRing.lean:137`); `.comp_left` (`Function.Injective.comp_left`, `Function/Basic.lean:231`)
lifts it to injectivity of post-composition on `Fin 3 → -`, so it suffices to prove the equation after
applying `algebraMap` coordinatewise. Then `map_dblXYZ` (mathlib, `Jacobian/Formula.lean:742`:
`(W.map f).dblXYZ (f ∘ P) = f ∘ dblXYZ W P`) moves the algebra map past `dblXYZ`, and the goal becomes
exactly the **field twin** `dblXYZ_smulField` (line 460) — which is the genuinely substantive lemma
(`equiv_iff_eq_of_Z_eq` + the universal `zsmul_point_eq_smulField`, the `ψₙ ≠ 0` quotient argument).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `lemma` whose proof is a 2-step transfer of an already-proved sibling
(`dblXYZ_smulField`) across the localization map `Universal.Ring ↪ Universal.Field`. It is **not** a
`## Main results` headline (the file's headline is `zsmul_eq_smulEval`), not a person-named theorem, and
introduces no new object. It is an internal reduction lemma in the multiplication-formula proof.

(Literature width: this report runs the wider sweep anyway, to fix the family verdict.)

### One-line check (Phase 2b)

Body: a single term-mode `:=` with a one-line `by` block (`simp_rw [← map_dblXYZ]; exact dblXYZ_smulField`).
One-liner verdict: **ONE-LINER PROOF** — but the relevant Phase-2b exemptions are about *definitions*
(defeq barriers / diamonds / API names); this is a **`Prop`**, so those exemptions do not apply. What
matters here is instead the *role* of the lemma (internal scaffolding vs. standalone API), handled in the
call-site and composition phases below.

---

### Literature search table

| #  | Channel                          | Query                                                                                                                | Hit? | Standard form found              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomials doubling formula Jacobian coordinates universal coordinate ring elliptic curve psi phi omega     | yes  | `[n]P = (φ/ψ², ω/ψ³)`; Jacobian `(X:Y:Z) ↔ (X/Z², Y/Z³)` | arXiv 2412.10284, Moody (NIST/eprint 2010/630), Sage `jacobian.py` — the *scalar-mult formula* and Jacobian doubling are standard; no separate name for "dblXYZ on the universal `(φₙ,ωₙ,ψₙ)` triple" |
|  2 | WebSearch (general / recursion)  | "division polynomial" doubling "2n" identity phi psi omega elliptic curve scalar multiplication formula Silverman      | yes  | `ψ₂ₙ = (ψₙ/2y)(ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)`; `φₙ = xψₙ² − ψₙ₋₁ψₙ₊₁`; `ωₙ = …/(4y)`; doubling `2(x,y)=(…)` | Wikipedia "Division polynomials", Sutherland 18.783 L#6, arXiv 1103.4560 — the **doubling recursions** are the classical, named identities; the Jacobian-triple repackaging is a *formalization device*, not a textbook-named theorem |
|  3 | Local references                 | grep `.mathlib-quality/references/` (NagellLutz)                                                                       | n/a  | (no `references/` dir for NagellLutz) | dir absent on this checkout; `refs/` store also absent — recorded n/a |
|  4 | ChatGPT MCP                      | second opinion on standing/name of the universal-ring doubling-triple identity                                        | n/a  | —                                | MCP down per task note; compensated by WebSearch breadth (#1,#2) + direct mathlib-source reading of `dblXYZ`/`map_dblXYZ`/`ψ`/`φ` |

The classical, *named* objects in the literature are (a) the **scalar-multiplication formula**
`[n]P = (φₙ : ωₙ : ψₙ)` (the citable end-product, = this file's `zsmul_eq_smulEval`) and (b) the
**division-polynomial recursions** for `ψ₂ₙ`, `ψ₂ₙ₊₁` (mathlib's `normEDS` / the project's EDS). The
statement "`dblXYZ` of the universal `(φₙ,ωₙ,ψₙ)` equals `(φ₂ₙ,ω₂ₙ,ψ₂ₙ)` **in the coordinate ring**" is
the *internal mechanism* by which one proves (a); the literature does not catalog it as a standalone result.

### Literature summary (Phase 3)

Concept identified as: the **Jacobian-coordinate doubling step of the division-polynomial
multiplication formula**, stated at the *universal coordinate-ring* level. The math is entirely classical
(Silverman; Sutherland 18.783; Wikipedia) and is the engine behind `[n]P = (φₙ : ωₙ : ψₙ)`. No source
gives this universal-ring transfer a name of its own — it is an intermediate identity, not a headline.
Most general standard form: the multiplication formula itself, valid over any base, specialized from the
universal case (exactly this file's architecture). Disagreement with literature: none.

---

### Generality analysis

Literature-standard target: the **multiplication formula** `n • P = (φₙ : ωₙ : ψₙ)` for any nonsingular
`P` over any base, obtained by *specializing* the universal identity. `dblXYZ_smulRing` is already the
universal (initial) instance of the doubling step — its generality is maximal *for its role*, and the file
already performs the specialization (`dblXYZ_smulEval`, via `ringEval`/`curveRing_map_ringEval`).

| # | Parameter / hypothesis        | Current Lean form                          | Literature-standard form                  | Weaker form? | Reason |
|---|-------------------------------|--------------------------------------------|-------------------------------------------|--------------|--------|
| 1 | base ring `Universal.Ring`    | `curve.CoordinateRing` (universal coord ring) | the universal coord ring (initial)      | **NO** | Universal/initial **by design** — this is the whole point of proving it *once* over `O` and specializing. Generalising the base would just be the `ringEval`-specialization that `dblXYZ_smulEval` already does. |
| 2 | index `n`                     | arbitrary `n : ℤ`                          | arbitrary `n ∈ ℤ`                          | **NO** | Already fully general in `n`; no hypothesis to weaken (the ring statement needs no `ψₙ ≠ 0`). |

### Generality verdict (Phase 4b)

Current form is: **MAXIMALLY GENERAL for its role** (the universal/initial doubling step). Weakening
opportunities: **0**. The "more general" object is not a weaker `dblXYZ_smulRing` but the *specialized*
`dblXYZ_smulEval` / the end-formula `zsmul_eq_smulEval`, both already present.

### Modern-idiom check (Phase 4c)

Not applicable in substance: this is a concrete polynomial identity, not a "let X be a foo" definition.
The idiomatic mathlib spelling is already used — `dblXYZ` is mathlib's Jacobian doubling primitive, the
transfer uses mathlib's `IsFractionRing.injective` + `map_dblXYZ`, and the EDS lives in mathlib's
`normEDS` vocabulary. No modern-idiom restatement applies. Modern idiom available: **no**.

---

### Diamond / defeq risk (Phase 4.5)

Kind is `lemma` (a `Prop`): no typeclass diamond, no reducibility leak, no instance priority, no
coercion or universe exposure. It anchors no instance and defines no notation. Overall risk: **NONE**
(propositional). Not a factor in the verdict.

---

### Mathlib search-status

[A] Lean-Finder  "division polynomial doubling formula universal ring", "dblXYZ of (φₙ,ωₙ,ψₙ)" — **no hit**
   (the mathlib index has no `Universal.*` for Weierstrass curves, and no scalar-multiplication-by-`n`
   division-polynomial formula at all).
[B] Loogle       `WeierstrassCurve.Jacobian.dblXYZ`, `dblXYZ _ _ = _`, `_ • _ = (_ , _ , _)` — `dblXYZ`,
   `map_dblXYZ` **present** (`Jacobian/Formula.lean`); **no** lemma equating `dblXYZ (φₙ,ωₙ,ψₙ)` to the
   `2n` triple; no `smulRing`/`smulPoly`/`Universal`.
[C] LeanSearch   "doubling formula for division polynomials in the coordinate ring", "n times a point as
   division polynomials Jacobian" — surfaces `dblXYZ`/`normEDS` building blocks only; **no** end-formula.
[D] Grep mathlib src  over `09b373db6e24` (toolchain v4.32.0-rc1):
   - `dblXYZ` ✓ `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:349`
   - `map_dblXYZ` ✓ `…/Jacobian/Formula.lean:742`
   - `ψ` (`WeierstrassCurve.ψ`) ✓ and `φ` ✓ `…/DivisionPolynomial/Basic.lean:401, :448`
   - **`ω` (the y-coordinate division polynomial): ABSENT from mathlib** — `grep 'def ω'` over
     `DivisionPolynomial/*.lean` returns nothing; `curve.ω` is **project-defined**
     (`DivisionPolynomialOmega.lean:74`, the entire purpose of that file).
   - `Universal` namespace / `Universal.Ring` / `smulPoly` / `smulRing` / any `dblXYZ … = … 2 * n`
     identity: **ABSENT** (`grep` over `Mathlib/AlgebraicGeometry/EllipticCurve/` and
     `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — no hit). The universal-curve machinery
     (`Universal.curve`, `CoordinateRing` base change, `ringEval`) is unupstreamed (authored by Junyan Xu).
[E] Name pattern  `dblXYZ_smulRing`, `smulRing`, `Universal.Jacobian` in mathlib — **no hit** (project-local).

Searched for both the current form and the literature target (the multiplication formula); **neither is in
mathlib**, and the statement is **not even expressible** in current mathlib — it requires `Universal.Ring`,
the project's `ω`, and `smulRing`, none of which mathlib has.

Concluded: **NOT in mathlib**, and unlike a typical NO-composable plumbing decl, its *statement* cannot be
written down in mathlib today (missing `ω`, `Universal.Ring`, `smulRing`).

---

### Call sites

Internal use count (NagellLutz, excluding the declaring line): **1** substantive proof use.

| Caller file:line                 | Usage pattern (one-line excerpt)                                                                  |
|----------------------------------|---------------------------------------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:569        | `dblXYZ_smulEval : … := by simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]` |
| LutzNagell/ZSMul.lean:26 (doc)   | module docstring: names it as the universal polynomial-identity reduction step                     |

**Call-sites reading.** `dblXYZ_smulRing` is consumed by **exactly one** lemma, `dblXYZ_smulEval`
(line 568), which specializes it from the universal curve to an arbitrary curve `W` via `ringEval` and
`curveRing_map_ringEval`. `dblXYZ_smulEval` in turn feeds the even-odd induction that proves the file's
deliverable `zsmul_eq_smulEval`. So this lemma is a **single-purpose internal node** in one proof chain:
`dblXYZ_smulField` (the real identity) → **`dblXYZ_smulRing`** (transfer to `O`) → `dblXYZ_smulEval`
(specialize to `W`) → `zsmul_eq_smulEval` (the citable formula). It is scaffolding, not standalone API.

---

### Composition check (Phase 6)

Can `dblXYZ_smulRing` be derived from **mathlib** in ≤3 chained calls? **No.**

Attempt 1 — transfer from the field twin (what the proof actually does):
`(IsFractionRing.injective _ _).comp_left <| by simp_rw [← map_dblXYZ]; exact dblXYZ_smulField`.
- Mathlib decls used: `IsFractionRing.injective` (`FractionRing.lean:137`),
  `Function.Injective.comp_left` (`Function/Basic.lean:231`), `map_dblXYZ` (`Jacobian/Formula.lean:742`).
- **Load-bearing input is `dblXYZ_smulField` — a PROJECT lemma, not mathlib.** The three mathlib calls do
  only the *ring ← field* transfer; they cannot produce the equation from mathlib alone. And
  `dblXYZ_smulField` is itself a genuine ~8-line proof (`equiv_iff_eq_of_Z_eq`, the universal point's
  `zsmul_point_eq_smulField`, `ψᵤ_ne_zero`, the `n = 0` case) over project-local `curveField`/`smulField`.
- Result: **fails as a mathlib-only composition** — it is a composition over *project* infrastructure.

Attempt 2 — direct from mathlib's `normEDS`/`dblXYZ` without the field twin: would require re-deriving the
doubling recursions for the universal `(φₙ,ωₙ,ψₙ)` modulo `⟨W⟩` from scratch — a substantial development,
not ≤3 calls, and still needs the project's `ω` (absent from mathlib).

Conclusion: **NOT COMPOSABLE FROM MATHLIB.** The only short derivation is from `dblXYZ_smulField`, which is
project-internal; mathlib's primitives supply the transfer machinery but not the mathematical content,
and the statement itself needs the project's unupstreamed `Universal.Ring`/`ω`/`smulRing`.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulRing`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- **Not in mathlib, and not even statable in mathlib (Phase 5).** mathlib has `ψ`, `φ`, `dblXYZ`,
  `map_dblXYZ`, but **no `ω`** (project-defined, `DivisionPolynomialOmega.lean:74`), **no `Universal`
  ring/field**, **no `smulRing`**, and **no scalar-multiplication-by-`n` division-polynomial formula**.
  So this rules out `NO-mathlib-has-it` *and* means the statement cannot be written in current mathlib.
- **Not composable from mathlib (Phase 6).** The one short proof is a transfer of the *project* lemma
  `dblXYZ_smulField` across `IsFractionRing.injective` + `map_dblXYZ`; mathlib's three calls do only the
  ring←field move, and the mathematical content lives in the project's field twin (itself a real proof).
  So this rules out `NO-composable-from-mathlib`.
- **Not a standalone YES, but also not a clean YES-but-generalise (Phase 1–4, call sites).** It is a
  **single-purpose internal reduction step** (1 consumer, `dblXYZ_smulEval` at line 569) inside this
  file's proof of the citable end-product `zsmul_eq_smulEval`. The literature (Silverman; Sutherland
  18.783; Wikipedia "Division polynomials") names the *multiplication formula* `[n]P = (φₙ:ωₙ:ψₙ)` and the
  *EDS recursions*, **not** this universal-ring doubling-triple transfer. Its generality is already
  maximal-for-its-role (universal/initial), so there is no generalise-first action.

**Rationale (why BORDERLINE, not one of the decisive buckets):**

`dblXYZ_smulRing` states real, classical mathematics — the Jacobian-coordinate doubling step of the
division-polynomial multiplication formula, over the universal coordinate ring. But its **disposition is a
packaging decision a human must make**, not a mechanical one, because three things are simultaneously true:

1. It is genuinely absent from mathlib (so not `NO-mathlib-has-it`), and its *statement* depends on
   unupstreamed project infrastructure — `Universal.curve`/`Universal.Ring`, the y-coordinate division
   polynomial `ω`, and the `smulRing` packaging. **Whether this lemma can go to mathlib at all is
   contingent on first upstreaming that infrastructure** (`Universal.curve` is the `YES-add-as-is` object
   in `curve.md`; `ω` is a real missing mathlib definition; `smulRing`/`curveRing` are `NO-composable`
   plumbing). That is a multi-decl package decision, not a per-lemma call.
2. It is not composable from mathlib (so not `NO-composable-from-mathlib`): the short proof's content is a
   *project* lemma (`dblXYZ_smulField`), and mathlib supplies only the localization-transfer wrapper.
3. It is not a standalone result mathlib would catalog on its own (so not a clean `YES-add-as-is`): it is
   one of a **family of internal intermediates** — `dblZ_smulPoly`, `dblXYZ_smulField`,
   **`dblXYZ_smulRing`**, `dblXYZ_smulEval`, and the `addXYZ_*` analogues — whose sole purpose is to
   assemble `zsmul_eq_smulEval`. When this development is upstreamed, a human/maintainer must decide
   whether such universal-ring intermediates ship as `private`/internal lemmas, get inlined, or are kept
   as a small public API — exactly the judgment the BORDERLINE bucket is for.

In short: the lemma **travels to mathlib with the `zsmul_eq_smulEval` development**, but only as part of
that package and only after the missing infrastructure (`Universal.curve`, `ω`) lands; as a *standalone*
decl assessed in isolation it is neither "add as-is" nor a NO. The right answer is to flag it for the
human deciding the scope and internal/public boundary of the upstream package.

**What a human needs to decide (actionable):**
- **Scope of the upstream package.** Is the AINTLIB plan to upstream the whole multiplication-formula
  development (`Universal.curve` + `ω` + the `smulPoly`/`smulRing`/`smulField` machinery +
  `zsmul_eq_smulEval`) to mathlib? If **yes**, `dblXYZ_smulRing` goes up *as part of it* — most likely as
  an **internal/`private`** lemma (1 consumer, pure transfer), since the public-facing results are
  `zsmul_eq_smulEval` and the `ω`/`Universal.curve` API. If **no** (kept project-local), this lemma stays
  local with everything it depends on.
- **Prerequisites that must land first** (each its own mathlibable decision):
  - `WeierstrassCurve.Universal.curve` (+ `CoordinateRing` / `specialize` / `ringEval` API) — see
    `curve.md` → `YES-add-as-is`.
  - `WeierstrassCurve.ω` — the y-coordinate (companion) division polynomial; **genuinely missing from
    mathlib** (mathlib has only `ψ`/`φ`). Needs its own assessment; likely `YES-add-as-is`.
- **Internal-vs-public boundary.** If upstreamed, recommend `private` (or omit, inlining into
  `dblXYZ_smulEval`): it has a single consumer and is a localization-transfer of the field twin
  `dblXYZ_smulField`, not an independently useful API surface.
- **Reference for the maintainer:** the named, citable target is the multiplication formula
  `[n]P = (φₙ : ωₙ : ψₙ)` (Silverman; Sutherland 18.783 Lecture #6) and the division-polynomial doubling
  recursions (Wikipedia "Division polynomials"); `dblXYZ_smulRing` is the Jacobian-ring intermediate that
  proves it, with no independent name in the literature.

**Mathlib building blocks present (for the transfer, not the content):**
- `WeierstrassCurve.Jacobian.dblXYZ` — `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:349`
- `WeierstrassCurve.Jacobian.map_dblXYZ` — `…/Jacobian/Formula.lean:742`
- `IsFractionRing.injective` — `Mathlib/RingTheory/Localization/FractionRing.lean:137`
- `Function.Injective.comp_left` — `Mathlib/Logic/Function/Basic.lean:231`
- `WeierstrassCurve.ψ`, `WeierstrassCurve.φ` — `…/DivisionPolynomial/Basic.lean:401, :448`
  (but **`ω` is absent** — the key missing piece).

---

## Next step

Do **not** treat `dblXYZ_smulRing` as an independent add/skip decision. Route it to a **human** as part of
the **`zsmul_eq_smulEval` upstreaming package**: decide (a) whether that whole development goes to mathlib,
and if so (b) upstream its prerequisites first — `Universal.curve` (`curve.md` → `YES`) and the missing
y-coordinate division polynomial `ω` (file its own mathlibable; likely `YES`) — then ship `dblXYZ_smulRing`
**as an internal/`private`** lemma (single consumer `dblXYZ_smulEval`, a pure ring←field transfer of
`dblXYZ_smulField`). It is `BORDERLINE-needs-human`: absent from mathlib, not composable from mathlib
primitives, not statable in current mathlib, and not a standalone catalog-worthy result — a packaging /
internal-boundary judgment, not a mechanical verdict.
