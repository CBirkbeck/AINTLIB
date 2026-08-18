# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.nonsingular_smulField`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves; division
> polynomials; elliptic divisibility sequences). One declaration, full workflow.
> Local Lean build is stale; mathlib **source tree is present** at
> `.lake/packages/mathlib/Mathlib/` and was grepped directly. Reasoned from the source statement
> + mathlib source + literature.

---

### Baseline (Phase 0)

- lake build:               not run (stale, per task) — reasoned from source; mathlib source tree present and grepped
- decl `WeierstrassCurve.Universal.Jacobian.nonsingular_smulField`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:445`
- kind:                      `lemma` (theorem-like; not a `def`)
- has sorry:                 no
- module docstring summary:  proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` in Jacobian coordinates, for any `n : ℤ` and nonsingular affine `P : W.Point` over a field — via a *universal* division-polynomial argument.

**Qualified-name verification.** Namespace stack in the file: `namespace WeierstrassCurve` (L76) →
`namespace Universal` (L86) → `namespace Jacobian` (L395). Inside, `open WeierstrassCurve.Jacobian`
(L399). The lemma `nonsingular_smulField` (L445) therefore has full name
**`WeierstrassCurve.Universal.Jacobian.nonsingular_smulField`** — matches the parsed name. ✓

---

### Statement (Phase 1)

```lean
variable (n : ℤ)   -- section variable

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  rw [← nonsingularLift_iff]
  simpa only [zsmul_point_eq_smulField] using (n • Jacobian.point).nonsingular
```

`nonsingular_smulField` is a **lemma** stating:

> On the *universal* Weierstrass curve — base-changed to the universal fraction field
> `Universal.Field = FractionRing (curve.CoordinateRing)` — the length-3 Jacobian coordinate tuple
> `smulField n = (φₙ : ωₙ : ψₙ)` (the universal division polynomials, mapped into the field)
> satisfies the Jacobian **`Nonsingular`** predicate, for every integer `n`.

In ordinary mathematics this is the (well-known) statement that the homogeneous triple
`(φₙ, ωₙ, ψₙ)` representing `[n]·(X,Y)` is a *bona fide* point of the curve in Jacobian
coordinates — i.e. it lies on the curve and is nonsingular — applied to the **generic point**
`(X,Y)` of the universal curve over `ℤ[A₁,…,A₆,X,Y]`.

Variables / typeclasses (Lean side):
- `n : ℤ` — the multiplier (section variable).
- Implicit: `curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field`
  — the universal curve over its universal coordinate **field** (`Universal.lean:173`).
- `smulField n : Fin 3 → Universal.Field := polyToField ∘ ![curve.φ n, curve.ω n, curve.ψ n]`
  (`ZSMul.lean:418`) — the three division-polynomial families as field elements.

Hypotheses (Lean side): none (universally quantified over `n : ℤ`; no `n ≠ 0` needed — the `n=0`
case gives `(1:1:0)`, the point at infinity, which is nonsingular).

Conclusion (math): the division-polynomial coordinate triple for `[n]` is a nonsingular Jacobian
point of the universal curve.

Conclusion (Lean): `WeierstrassCurve.Jacobian.Nonsingular curveField (smulField n)` — a `Prop`.

**How the proof works (load-bearing for the verdict).** Two steps:
1. `rw [← nonsingularLift_iff]` reduces the goal `Nonsingular curveField (smulField n)` to
   `NonsingularLift curveField ⟦smulField n⟧` — mathlib's
   `WeierstrassCurve.Jacobian.nonsingularLift_iff : W.NonsingularLift ⟦P⟧ ↔ W.Nonsingular P`
   (`.lake/.../Jacobian/Basic.lean:495`).
2. The term `(n • Jacobian.point).nonsingular` is the **structure projection** `.nonsingular` of the
   actual Jacobian point `n • Jacobian.point` — every `WeierstrassCurve.Jacobian.Point` *bundles*
   its nonsingularity proof:
   ```
   structure Point where (point : PointClass R) (nonsingular : W'.NonsingularLift point)
   ```
   (`.lake/.../Jacobian/Point.lean:372–376`). That proof has type `NonsingularLift ((n • Jacobian.point).point)`,
   and `simpa only [zsmul_point_eq_smulField]` rewrites `(n • Jacobian.point).point` to `⟦smulField n⟧`
   using the **project-local** theorem `zsmul_point_eq_smulField` (`ZSMul.lean:424`), closing the goal.

So the mathematical content reduces to: *the coordinate-formula theorem `zsmul_point_eq_smulField`
holds* (that is the deep part — the universal multiplication-by-`n` formula), and *every point of a
`Jacobian.Point` is nonsingular by construction* (trivial). This lemma is the thin bridge between the
two.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an internal helper lemma in the spine of the `Universal` division-polynomial development —
not itself a named/main theorem. (Literature width run EXHAUSTIVE regardless.) The *parent* result
`zsmul_eq_smulEval` it ultimately serves is BIG; this rung is small.

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner gate does **not** apply.
(For the record the proof body is 2 lines, but Phase 2b is about *definitions*; n/a here.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "division polynomial point elliptic curve nonsingular psi phi omega multiplication-by-n coordinates" | yes | `[n](x,y) = (φₙ/ψₙ², ωₙ/ψₙ³)` for `(x,y) ∈ E(K)ⁿˢ` | Sutherland MIT 18.783 Lec 6; Silverman *AEC*. The *formula* is standard; "the triple is a nonsingular point" is implicit, never a named lemma. |
| 2 | WebSearch (general/idiom) | "mathlib WeierstrassCurve division polynomial multiplication formula Jacobian coordinates Junyan Xu Angdinata" | partial | mathlib has `Ψ,Φ,ψ,φ` as polynomials; `dblXYZ`/`addXYZ` homogeneous degree-4 in Jacobian/Projective | mathlib4 docs DivisionPolynomial.Basic + Jacobian/Projective Formula. Confirms the *polynomials* are in mathlib; the *point formula* is not. |
| 3 | WebSearch (PR/upstream status) | "mathlib pull request elliptic curve zsmul_eq_smulEval / division polynomial multiplication formula 2024 2025" | no | — | No public PR found by name. mathlib4 docs reiterate `[n]P=(φ/ψ²,ω/ψ³)` only as motivating prose. |
| 4 | ChatGPT MCP | (math second opinion) | n/a | — | MCP down per task; substituted with extra WebSearch (#1–#3) + direct mathlib-source reading (Phase 5), which is stronger evidence for *this* question (a mathlib-internal API question). |
| 5 | Local references | `refs/NagellLutz/`, `.mathlib-quality/references/` | n/a | — | No references dir present for this project; symlinked `refs/` store is gitignored/local-only and not available in this checkout. Recorded n/a. |
| 6 | nLab | "division polynomial" / "elliptic curve" | n/a | — | nLab has no division-polynomial page at the granularity of "coordinate triple is nonsingular"; not a categorical concept. |
| 7 | nCatLab | — | n/a | — | Not a categorical statement (concrete coordinate computation). |
| 8 | Stacks Project | "division polynomial", "Weierstrass" | n/a | — | Stacks does not cover explicit division-polynomial multiplication formulas; not the right corpus. |
| 9 | MathOverflow / MSE | "division polynomials [n]P coordinates nonsingular" | yes (background) | same formula as #1 | Standard textbook fact; no distinct "nonsingularity of the triple" named result surfaced. |
| 10 | recent arXiv (≤5 yr) | "division polynomials arbitrary isogenies" (Stange 2025), "homogeneous division polynomials Weierstrass" | yes | confirms `φ,ψ,ω` triple and `[n]P` formula; homogeneous/Jacobian variants studied | arXiv 2503.15428, 1303.4327. Modern refs use exactly this triple; none isolate the Lean-style "the universal triple satisfies `Nonsingular`" lemma. |

**Protocol satisfied:** WebSearch ran ≥3 distinct queries at different levels (specific formula / mathlib-idiom / upstream-PR-status); ChatGPT MCP recorded n/a-with-reason (down) and substituted with direct mathlib-source reading; local refs checked (absent → n/a); nLab/nCatLab/Stacks each checked + n/a-with-reason; MathOverflow + arXiv hit.

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` formula via division polynomials**,
`[n](x,y) = (φₙ(x,y)/ψₙ(x,y)², ωₙ(x,y)/ψₙ(x,y)³)`, equivalently the homogeneous Jacobian triple
`(φₙ : ωₙ : ψₙ)`. The specific assertion here — *that triple is a nonsingular Jacobian point* — is a
**formalization-internal lemma**, not a named theorem in the mathematical literature.

Sources agree on the standard form: yes (Silverman AEC; Sutherland 18.783; arXiv 2503.15428,
1303.4327). The formula is classical and uniform.

Most general standard form: the formula holds for any `(x,y)` a nonsingular point of `E` over any
field (indeed over the universal/generic point, which is the strongest possible — it specialises to
every field by base change). The project states it in exactly that maximally-general *universal* form.

Generality dimensions where the literature varies: only the *coordinate model* (affine `φ/ψ²`,
`ω/ψ³` vs. homogeneous Jacobian `(φ:ω:ψ)`) and whether stated pointwise or generically. The project's
universal/generic formulation is the most general of these.

Disagreement with the literature: none. The Lean statement is a faithful (in fact maximally strong,
generic) rendering of a standard fact.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): the triple `(φₙ:ωₙ:ψₙ)` represents `[n]P` and is a nonsingular
point, for `P` a nonsingular point over any field — captured generically over the universal ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | base object | `curveField` = universal curve over `FractionRing curve.CoordinateRing` | the generic point of the universal curve | **NO** | Already the *universal/generic* curve — this is the maximally-general base; specialises to every field via `map`. Cannot be weakened further. |
| 2 | `n : ℤ` | arbitrary integer | arbitrary integer (incl. negative; `n=0` → ∞) | **NO** | Already fully general in `n`; no positivity hypothesis. |
| 3 | nonsingularity hyp on `P` | none (generic point `(X,Y)` is nonsingular for free, via `Jacobian.point`) | `(x,y) ∈ E(K)ⁿˢ` | **NO** | The universal point is built nonsingular; specialisations inherit it. Strongest possible. |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is the *universal/generic* statement; every
field-level instance is a base-change specialisation). K = 0 weakening opportunities.
Cost of restatement: n/a.

#### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|-----------|
| 1 | bundled hyps → typeclasses/instances? | no | — | Statement has no bundled "let X be a foo" preamble; the universal point already carries its data. |
| 2 | sequences/metric → filters/topology? | no | — | Purely algebraic; no limiting notions. |
| 3 | construct object → universal-property class? | **partially already done** | — | The whole *point* of the `Universal` apparatus is the universal-property/generic-point idiom: prove once over `Universal.Field`, specialise by ring map. The lemma already lives inside that idiom. |
| 4 | set+closure → bundled substructure? | no | — | n/a. |
| 5 | field/metric-specific → weaken typeclass? | no | the *parent* `zsmul_point_eq_smulField` is field-specific by necessity (division by `ψₙ`); the Ring-level facts are already factored out as `smulRing`/`dblXYZ_smulRing` siblings | the project already provides Ring-level versions where possible; the field is genuinely needed here. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid? | no | `ℤ` is intrinsic (the multiplication-by-`n` map on an abelian group) | n/a. |

**Modern-idiom verdict:** modern idiom available = **no** (the contemporary mathlib idiom — prove
generically over the universal ring, specialise via `map` — is *already what the project does*; this
lemma is a node inside it). The statement is already in its right, maximally-general, idiomatic form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a `Prop`-valued proof; introduces no definitional equalities,
typeclass-search paths, coercions, or instances). Skipped.

---

### Mathlib search-status (Phase 5)

Five-method search. Mathlib **source tree is present** at `.lake/packages/mathlib/Mathlib/` and was
grepped directly (strongest possible evidence — not just an index).

```
[A] Lean-Finder       (server stale; substituted with direct source grep below)   n/a → see [D]
[B] Loogle            type pattern `Nonsingular _ (?f _)` over division polys       no hits — mathlib divpoly files contain NO `Nonsingular` statements (see [D])
[C] LeanSearch        "division polynomial coordinates nonsingular point"           n/a (index stale) → covered by [D] direct grep
[D] Grep mathlib src  exhaustive, see below                                         decisive — NOT in mathlib
[E] Name pattern      `smulField`, `nonsingular_smul*`, `Universal.Jacobian`        no hits in mathlib
```

Direct mathlib-source greps (`.lake/packages/mathlib/Mathlib/`):

1. `smulField` / `smulPoly` / `smulRing` anywhere in mathlib → **0 files**. Mathlib has **no**
   division-polynomial *coordinate-triple* API.
2. `Universal.Field` / `Universal.Ring` / `namespace Universal` / `Universal.Jacobian` in
   `AlgebraicGeometry/EllipticCurve/` → **0 files**. The entire *universal/generic-point*
   division-polynomial machinery is **absent** from mathlib.
3. `Nonsingular` / `nonsingular` in `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` → **0
   matches**. Mathlib's division-polynomial files (`Basic.lean`, `Degree.lean`) say **nothing** about
   point nonsingularity — they are purely about the polynomials `Ψ,Φ,ψ,φ`, their recurrences and
   degrees.
4. `nonsingular_smul` in mathlib EC is the **scaling-invariance** lemma
   (`Jacobian/Basic.lean:388`: `W.Nonsingular (u • P) ↔ W.Nonsingular P` for a unit `u`) — a
   *different* statement (Jacobian `u`-scaling), unrelated to multiplication-by-`n`. **False-friend
   name collision**, not a match.
5. `zsmul_eq_smulEval` / `zsmul_point_eq_smulField` / `smulEval` in mathlib EC → **0 matches**. The
   load-bearing parent theorem (the multiplication-by-`n`-in-Jacobian-coordinates formula) is **not in
   mathlib**.
6. **mathlib's own docstring confirms the gap.** `DivisionPolynomial/Basic.lean` "Main definitions"
   lists `preΨ, ΨSq, Ψ, Φ, ψ, φ` and then: **"TODO: the bivariate polynomials `ωₙ`."** The formula
   `[n]P = (φ/ψ², ω/ψ³)` appears only as *motivating prose*, never as a proven theorem. So mathlib
   doesn't yet have `ω`, let alone the point formula or its nonsingularity corollary.

**Searched for both** the user's form (`Nonsingular curveField (smulField n)`) and the
literature-standard / parent form (the multiplication formula). Neither is present.

Concluded: **not in mathlib** (all methods exhausted via direct source grep, plus the
literature-standard parent form). Mathlib has the division *polynomials* but not the *point* formula,
not the universal apparatus, not `ω`, and no nonsingularity statement about division-polynomial
coordinates.

---

### Composition check (+ call-sites) (Phase 6)

#### Call sites — `nonsingular_smulField`

Internal use count (NagellLutz, excluding the declaring line 445): **2**
External-to-file callers: also duplicated **verbatim in a second project** (HasseWeil).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:504` | `addXYZ_self nonsingular_smulField.1, …` (uses `.1`, the on-curve `Equation` component) |
| `projects/NagellLutz/LutzNagell/ZSMul.lean:510` | `addXYZ_neg nonsingular_smulField.1, …` |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:523` | **duplicate declaration** (also `private lemma nonsingular_smulField : …`) |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:578, 584` | same `.1` uses as ZSMul L504/510 |

Inline-derivation grep: the lemma is **duplicated** across NagellLutz and HasseWeil (an AINTLIB
cross-project dedup signal — consolidation candidate), and is used as `.1` to feed `addXYZ_self` /
`addXYZ_neg` in the proof of `addXYZ_smulField` (`ZSMul.lean:499`), which feeds `zsmul_eq_smulEval`.

**Signal:** K = 2 internal uses + a second-project clone, no bypass re-derivation → **real API node**
inside the division-polynomial spine. (Per the Phase-6 table: "K ≥ 2 internal, no inline
re-derivation" leans YES-*; the cross-project duplication independently confirms it is load-bearing,
not dead code.)

#### Composition attempt

Can `nonsingular_smulField` be derived in ≤3 chained calls **from mathlib primitives**?

Attempt 1: `(nonsingularLift_iff _).mp (zsmul_point_eq_smulField ▸ (n • Jacobian.point).nonsingular)`
- Decls used: `Jacobian.nonsingularLift_iff` (mathlib ✓), `Jacobian.Point.nonsingular` projection
  (mathlib ✓), **`zsmul_point_eq_smulField`** (PROJECT-LOCAL ✗ — `ZSMul.lean:424`), `Jacobian.point`
  (PROJECT-LOCAL ✗ — `Universal.lean:155`).
- Result: succeeds **as written in the project**, but **fails the NO-composable bar**: two of the
  inputs are not mathlib primitives. `zsmul_point_eq_smulField` is itself the deep, unmerged
  multiplication-by-`n` theorem, and `Jacobian.point` is the project's universal generic point —
  neither exists in mathlib.

Conclusion: **NOT-COMPOSABLE from mathlib.** It *is* a 2-call composition, but over **project-local**
lemmas, not mathlib lemmas. The `NO-composable-from-mathlib` bucket explicitly requires the building
blocks to be *in mathlib* (so the form can be inlined at call sites using mathlib alone) — that
condition fails. The composition is trivial only *given* the surrounding `Universal` development.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.nonsingular_smulField`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the multiplication-by-`n` formula `[n]P=(φ/ψ²,ω/ψ³)` is standard
  (Silverman, Sutherland), but "the universal coordinate triple is a nonsingular Jacobian point" is a
  formalization-internal lemma, not a named literature theorem.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (stated over the universal/generic point;
  specialises to every field). Modern-idiom = no (it already lives inside the universal-ring idiom).
- Mathlib search (Phase 5): **not in mathlib** (direct source grep). Mathlib has the division
  *polynomials* but NOT the point formula, NOT the `Universal` apparatus, and `ω` is an explicit
  mathlib `TODO`. `nonsingular_smul` is a same-name false friend (scaling, not `[n]`).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the 2-line proof depends on the
  project-local `zsmul_point_eq_smulField` + `Jacobian.point`, neither in mathlib. Real API node
  (K=2 internal uses + duplicated in HasseWeil).

**Rationale.**

The mathematical *content* of this lemma — that the division-polynomial triple `(φₙ:ωₙ:ψₙ)` is a
genuine (nonsingular) Jacobian point representing `[n]P` — is exactly the kind of result mathlib
*wants*, and it fills a concrete, **named** gap: mathlib's `DivisionPolynomial/Basic.lean` defines the
polynomials but its docstring flags `ω` as a `TODO` and only states `[n]P=(φ/ψ²,ω/ψ³)` as motivating
prose, never as a theorem. There is no `Nonsingular` statement anywhere in mathlib's division-polynomial
files. So this is not redundant, and it is not composable from mathlib primitives (the load-bearing
input, the universal multiplication formula `zsmul_point_eq_smulField`, is itself missing upstream).

But it is **not a standalone-shippable result**, and that is what makes the verdict a judgment call
rather than a clean YES. `nonsingular_smulField` is one interior rung of a larger, self-contained
development — the `Universal` generic-point apparatus (`Universal.lean` + `ZSMul.lean`, copyright
**Junyan Xu / David Kurniadi Angdinata**, the actual mathlib elliptic-curve authors) whose headline
output is `WeierstrassCurve.zsmul_eq_smulEval`. The lemma only makes sense relative to
`Universal.Field`, `smulField`, `Jacobian.point`, and `zsmul_point_eq_smulField`, **none** of which
are in mathlib. Whether to upstream *this lemma* is therefore inseparable from whether/how to upstream
the **whole `Universal` development** — and in what form mathlib wants it (the `Universal` generic-point
device is a deliberate design choice that the mathlib maintainers would need to sign off on, and the
final public-facing statement would likely be the *field-level* `zsmul_eq_smulEval`, with
`nonsingular_smulField` either a `private`/internal step or folded into the `ωₙ`-TODO work). That, plus
the AINTLIB-internal fact that the lemma is **duplicated verbatim in HasseWeil** (a cross-project dedup
question that should be resolved *before* any upstreaming), are decisions the skill cannot make alone.

The honest classification is: a genuine contribution, maximally general, not in mathlib, not
mathlib-composable — but as a dependent node of an unmerged larger development, its upstreaming
grouping/naming/visibility is a human call. Hence BORDERLINE, not a bare YES-add-as-is (it would fail
the YES gate's "name the standalone PR" expectation — the right PR is the parent development, not this
lemma) and not NO-composable (the blocks are project-local, not mathlib).

**Numbered questions (≤5):**

1. Is the plan to upstream the **entire `Universal` division-polynomial development**
   (`zsmul_eq_smulEval` and supporting `Universal.lean`/`ZSMul.lean`) to mathlib — i.e. finish
   mathlib's `ωₙ` `TODO` and the multiplication-by-`n` point formula? If **yes**, `nonsingular_smulField`
   ships *inside that PR* (likely as an internal/`private` step), not as its own contribution.
2. If that upstreaming is **not** planned, do you still want the *standalone* statement "the
   division-polynomial coordinate triple is a nonsingular Jacobian point" in mathlib? It would need to
   be re-stated **field-generically over an arbitrary `WeierstrassCurve` and a nonsingular point**
   (not over the project's bespoke `Universal.Field`), since the `Universal` apparatus itself is the
   thing mathlib lacks.
3. The lemma is **duplicated verbatim in HasseWeil** (`Auxiliary/DivisionPolynomial.lean:523`). Should
   this first be **deduplicated into AINTLIB `Common/`** (a cleanup-lane task) before any mathlibability
   decision? (Strongly recommended — resolve the clone first.)
4. Mathlib already defines `ψ, φ` and lists `ω` as a `TODO`. Is anyone (Angdinata/Xu) already carrying
   a mathlib PR for the `ωₙ` + multiplication-formula work? If so, this should be **coordinated with /
   deferred to** that PR rather than opened independently.

**Next action:** answer the questions (especially #1 and #3). If #1 = yes → defer; track as part of
the parent `zsmul_eq_smulEval` upstreaming, not as a separate decl. If #1 = no but #2 = yes → re-run
`/mathlibable` on a *field-generic* restatement (not the `Universal.Field` form). In all cases, first
file a cleanup ticket to deduplicate the HasseWeil/NagellLutz clone (#3).

---

## Next step

Answer questions #1–#4 above. The likely resolution: this lemma is **not** a standalone mathlib
contribution — it is an internal step of the unmerged `Universal`/`zsmul_eq_smulEval` development
(mathlib's own `ωₙ` `TODO`), and it is currently duplicated across two AINTLIB projects. Resolve the
duplication (AINTLIB `Common/` dedup) and coordinate with the parent division-polynomial upstreaming
before treating `nonsingular_smulField` as independently mathlibable.
