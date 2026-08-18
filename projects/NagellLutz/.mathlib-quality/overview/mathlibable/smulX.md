# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX`

## Verdict: **BORDERLINE-needs-human**

One-line rationale: a one-line *intermediate* `def` for the universal n•P
x-coordinate; the math (universal-curve division-polynomial formula) is missing
from mathlib, but whether to ship *this exact helper* is a packaging call.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — task-sanctioned)
- decl `WeierstrassCurve.Universal.Affine.smulX`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:164`
- kind:                      `def` (noncomputable, in `noncomputable section`)
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ : ψₙ)`
  (Jacobian) / `(φₙ/ψₙ², ωₙ/ψₙ³)` (affine) for any integer `n` and nonsingular affine point `P` on a Weierstrass curve over a field.

Qualified name verified from source: namespaces `WeierstrassCurve` (line 76) →
`Universal` (line 86) → `Affine` (line 157); `def smulX` at line 164. The
parsed name `WeierstrassCurve.Universal.Affine.smulX` is correct.

---

### Statement (Phase 1)

`smulX n` is **the rational function `φₙ / ψₙ²` evaluated in the universal
function field**. Concretely: over the universal Weierstrass curve
`W_univ` defined over `R₀ = ℤ[A₁,A₂,A₃,A₄,A₆]` (a `MvPolynomial Coeff ℤ`), with
universal coordinate ring `Universal.Ring = R₀[X,Y]/⟨W_univ⟩` and universal field
`Universal.Field = Frac(Universal.Ring)`, define

  `smulX n := polyToField (φₙ) / (ψᵤ n)^2`

where `φₙ` and `ψₙ` are the (n-th) division polynomials of the universal curve,
`polyToField` is the ring map `R₀[X,Y] → Universal.Field`, and
`ψᵤ n = polyToField (ψₙ)`. Mathematically this is the candidate for the
**x-coordinate of `n • (X, Y)`**, where `(X, Y)` is the generic/universal point
on `W_univ`. The file later proves exactly that
(`Universal.Affine.zsmul_point_eq_smulX_smulY`), and specializes it to obtain the
n•P coordinate formula over an arbitrary field.

Variables / typeclasses (Lean side):
- `(n : ℤ)` — the scalar multiplier (the EDS index).
- No typeclass parameters of its own: everything is fixed by the ambient
  `Universal` namespace (`curve`, `Universal.Field`, `polyToField`, `ψᵤ`). The
  universal ring `ℤ[A₁..A₆,X,Y]/⟨W⟩` is the *single most general* base — every
  Weierstrass curve over every commutative ring is a quotient/specialization of it.

Hypotheses (Lean side): none on the def itself. (The lemmas about it carry
`n ≠ 0` where division by `ψₙ` must be justified.)

Conclusion (math): the element `φₙ/ψₙ² ∈ Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`.
Conclusion (Lean): n/a — definition; type is `Universal.Field`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (as a member of a BIG development).
Reason: `smulX` itself is a small helper `def`, but it is a load-bearing
component of a *main result* (`zsmul_eq_smulEval`, named in the module
docstring's `## …` summary and the project plan) and sits on top of a
**new mathematical structure** — the universal Weierstrass curve and its
function field, which mathlib does not have. The literature width is
EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`polyToField (curve.φ n) / (ψᵤ n) ^ 2`).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | yes      | The ~30 downstream lemmas (`smulX_eq`, `smulX_sub_smulX`, `smulX_neg`, `smulX_ne_zero`, …) drive proofs by `rw [smulX, …]` / `simp [smulX, …]`, i.e. controlled, explicit unfolding. `smulX` is sealed (not `@[reducible]`) so unification does not silently expand `φₙ/ψₙ²` everywhere. |
| Avoid typeclass diamonds          | no       | No instance is attached; pure data in a fixed field. |
| Mark semantic intent / API name   | yes      | The name + docstring ("the x-coordinate of `n•(X,Y)`") *is* the API surface for a 30-lemma block and for the downstream `zsmul_point_eq_smulX_smulY`. The HasseWeil project depends on the analogous name (`Affine.zsmul_point_eq_smulX_smulY`, referenced in `GenericPointZsmul.lean:31`). |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent + defeq-barrier).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "x-coordinate of nP division polynomials φₙ/ψₙ² formula" | yes | `x(nP) = φₙ(x)/ψₙ(x)²`, with `φₙ = xψₙ² − ψₙ₋₁ψₙ₊₁` | Wikipedia "Division polynomials"; Silverman AEC Ex 3.7; Washington §3.2 — fully standard |
| 2 | WebSearch (general form) | "mathlib elliptic curve division polynomial multiplication formula nP universal curve Junyan Xu" | partial | same coordinate formula; no universal-curve formalization named | confirms the *classical* form; no source names the Lean "universal" construction |
| 3 | WebSearch (named-after / aliases) | "mathlib4 WeierstrassCurve Universal Ring Field FractionRing CoordinateRing zsmul_eq division polynomial PR" | partial | mathlib `FunctionField = FractionRing CoordinateRing` for a *fixed* curve | the *universal* (over ℤ) version and the zsmul formula are NOT in the docs |
| 4 | ChatGPT MCP | (MCP down per task; substituted by channels 1–3 + 10 + WebFetch of mathlib docs) | n/a | — | task notes ChatGPT MCP may be down; used WebSearch×3 + arXiv + doc-fetch as fallback |
| 5 | Local references | `.mathlib-quality/references/` for NagellLutz | n/a | (no references dir; only `overview/` present) | dir absent — recorded n/a |
| 6 | nLab | "division polynomial" / "elliptic curve" | no | nLab has no division-polynomial / n•P-coordinate page | not a categorical concept |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | "division polynomial", "elliptic curve multiplication" | no | Stacks covers elliptic curves abstractly, not explicit division-polynomial coordinate formulas | explicit-formula material out of Stacks' scope |
| 9 | MathOverflow / MSE | "x-coordinate of nP division polynomial" generality | yes | confirms `φₙ/ψₙ²` is the universal/standard formula; the "universal curve over ℤ[a_i]" trick is folklore (used to prove the identities once and specialize) | the universal-ring trick is explicitly the standard way to prove these are polynomial identities |
| 10 | recent arXiv (≤5y) | EDS / division-polynomial recurrences | yes (1103.4560, 2102.07573, 2203.02015) | same coordinate formula + EDS recurrences | confirms `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`, ψ EDS recurrences |

### Literature summary (Phase 3)

Concept identified as: **the x-coordinate of `n·P` on a Weierstrass curve,
expressed via division polynomials as `φₙ/ψₙ²`**, instantiated **on the universal
curve over `ℤ[A₁,…,A₆]`** (the "generic point" of the universal Weierstrass
family).

Sources agree on the standard form: **yes** — `x([n]P) = φₙ/ψₙ²` is in Silverman,
Washington, and Wikipedia verbatim. The *universal-curve-over-ℤ* device (prove
the identity once for the generic point, then specialize by a ring hom to any
curve over any base) is standard folklore and is even cited as motivation in
mathlib's own `DivisionPolynomial/Basic.lean` docstring ("the characteristic-0
universal ring `𝓡[X, Y]`").

Most general standard form: the identity holds **as an equation of rational
functions in the universal field `Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`**, from which every
specialization follows. `smulX` is precisely the LHS element in that universal
field — i.e. it is already at the literature's maximal generality.

Generality dimensions where the literature varies:
  - base ring: from a fixed field (textbook) up to the universal ring over ℤ
    (most general; what this project uses). `smulX` is at the top.
  - object: some authors keep `x(nP)` as a function of `x` only; here it is the
    full universal-field element (carries `Y` too) — strictly the richer object.

Disagreement with the literature: none. `smulX`'s definition matches the
standard `φₙ/ψₙ²` exactly.

---

### Generality analysis — `WeierstrassCurve.Universal.Affine.smulX`

Literature-standard form: the universal-field element `φₙ/ψₙ²` over
`ℤ[A₁..A₆,X,Y]/⟨W⟩` — the maximal base.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | base ring (implicit, fixed by `Universal`) | universal ring `ℤ[A₁..A₆,X,Y]/⟨W⟩`, i.e. `Universal.Field` | same (universal ring over ℤ) | **NO** | this is already the initial object of the Weierstrass-curve category; nothing is more general. Specializing to any `W/R` is a ring hom *out* of it. |
| 2 | `(n : ℤ)` | integer index | integer index (EDS are ℤ-indexed) | NO | division polynomials / EDS are intrinsically ℤ-indexed; no monoid generalization is meaningful here. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0.
Cost of restatement: n/a (nothing to restate).

The universal curve is *the* maximally-general base by construction; `smulX`'s
job is to be specialized down, not generalized up.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | "let X be a foo" → typeclass/instance? | no | the def has no bundled hypotheses to declassify | — |
| 2 | sequences/metric → filters/topology? | no | purely algebraic (rational function); no topology | — |
| 3 | construct an object → universal-property class? | **maybe** | the *whole universal-curve layer* (`Universal.Ring/Field/curve`) is itself a universal-property construction; one could ask whether `smulX` should be a field of a bundled "scalar-multiplication map on the generic point" rather than a free-standing def | this is the packaging question that drives the BORDERLINE verdict — see Phase 7 |
| 4 | set+closure-pred → bundled substructure? | no | not a substructure | — |
| 5 | field-specific → module/(semi)ring weakening? | no | already over the universal *ring*; the field is `Frac` of it, needed for the division | — |
| 6 | 1-categorical → higher-categorical? | no | explicit-formula content; no categorification target | — |
| 7 | concrete index ℤ → monoid/group? | no | EDS are ℤ-indexed by nature | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** for `smulX` *as a standalone element* (it is
already the right object at the right generality). The only "modernisation"
question is organizational — whether the universal x/y-coordinate maps should be
bundled (row 3) — and that is a *packaging* decision about the surrounding
development, not a weakening of `smulX` itself. It feeds Phase 7 as a human
judgment call, not an auto-flip to YES-but-generalise.

One-line reason it is not a clean modernisation move: there is no redundancy to
eliminate and no blocked mathlib API; the def already composes with the project's
EDS / division-polynomial / group-law layers.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.Affine.smulX`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | no instance declared; pure element of a fixed `Field`. |
| 2 | Reducibility leak | low | not `@[reducible]`; body is a division `φₙ/ψₙ²`. Sealed-ness is *intended* (the API unfolds explicitly via `rw [smulX]`). No leak. |
| 3 | Non-canonical unfolding | low | `simp [smulX]` is used deliberately in its own lemmas; outside those it stays folded. No surprise unfolds. |
| 4 | Instance priority collision | none | not an instance. |
| 5 | Universe issues | none | lives in `Universal.Field : Type` (monomorphic). |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**. Top risks: none. No mitigations required.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulX`

[A] Lean-Finder       (index unavailable locally; substituted by grep over vendored mathlib + doc-fetch) — n/a
[B] Loogle            type pattern `WeierstrassCurve.Universal.Field` / `_ / (_)^2` over division polys — no such universal field type exists in mathlib → no hits
[C] LeanSearch        "x-coordinate of n times P elliptic curve division polynomial" — mathlib has division polynomials (`WeierstrassCurve.φ`, `.ψ`) but NO n•P coordinate formula → no hit on the formula
[D] Grep mathlib src  `grep -rn "smulX|smulEval|smulField|Universal\.(Field|Ring|curve)|zsmul_eq_smul" .lake/packages/mathlib/Mathlib/` — only hit is unrelated `MvPolynomial.sumSMulX` (linear poly Σcᵢxᵢ for irreducibility). NO `Universal` EC namespace, NO `smulX`. → no hit
[E] Name pattern      grep for `WeierstrassCurve.Universal.*` decls in mathlib — none exist → no hit

Searched for both:
  - current form (`smulX` = `φₙ/ψₙ²` in `Universal.Field`) — absent.
  - literature-standard form (universal `x(nP)` element, and the n•P coordinate
    theorem `zsmul_eq …`) — absent. Mathlib has the *ingredients*
    (`WeierstrassCurve.φ/ψ/ω`, `Affine.CoordinateRing`,
    `Affine.FunctionField = FractionRing CoordinateRing`, `Affine.CoordinateRing.mk_φ/mk_ψ`)
    but NOT the universal curve over ℤ, NOT `smulX`, NOT the zsmul formula. The
    mathlib `DivisionPolynomial/Basic.lean` docstring *mentions* the universal
    ring only as mathematical motivation; it is not implemented.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard
form). Mathlib has the building blocks for a *fixed* curve but neither the
universal-curve layer nor any scalar-multiplication coordinate formula.

---

### Call sites — `WeierstrassCurve.Universal.Affine.smulX`

Internal use count (NagellLutz, excluding the declaring `ZSMul.lean`): the def is
used **only inside `ZSMul.lean`** within NagellLutz (71 `smulX` occurrences in
that file, building its ~30-lemma API and the proof of
`Universal.Affine.zsmul_point_eq_smulX_smulY` → `zsmul_eq_smulEval`). No *other*
NagellLutz file imports it directly.

External-to-file callers: **the HasseWeil project carries a duplicate** of the
entire block —

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:240` | `def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2` (verbatim duplicate of this def) |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:246–374` | the full duplicated `smulX_*` API (`smulX_eq`, `smulX_sub_smulX`, `smulX_add`, …) |
| `projects/HasseWeil/HasseWeil/EC/GenericPointZsmul.lean:31` | references `Affine.zsmul_point_eq_smulX_smulY` (the theorem `smulX` exists to prove) |

Inline-derivation grep (was `φₙ/ψₙ²` re-derived without `smulX`?): none found —
where the coordinate is needed, it goes through `smulX`.

Composability signal: **K ≥ 3 internal uses, no inline re-derivation, plus a
second project depends on the same construction** → genuine API, leans YES-*.
The HasseWeil duplicate is itself evidence both that the construction is reusable
*and* that it is currently fork/duplicate code (a dedup/consolidation concern,
and a reason it would be valuable upstream).

---

### Composition check (Phase 6)

Can `smulX` be derived from mathlib in ≤3 chained calls?

Attempt 1: `polyToField (W.φ n) / (polyToField (W.ψ n))^2` directly.
  - Mathlib decls used: `WeierstrassCurve.φ`, `WeierstrassCurve.ψ`, and a map
    `R₀[X,Y] → Frac(…)`.
  - Result: **fails** — there is no `polyToField` / no `Universal.Field` in
    mathlib to even state this in. The *target type* doesn't exist upstream.
  - Notes: even granting the type, `smulX` is a *definition*, not a derivable
    proposition; "composition" is about deriving a *statement* from mathlib
    primitives, which doesn't apply to a new `def` whose ambient objects are
    themselves new.

Attempt 2: build the universal field from mathlib `FractionRing` +
`AdjoinRoot` + `MvPolynomial`.
  - This *constructs the entire `Universal` layer* (≫ 3 calls; it is `Universal.lean`'s job)
    before `smulX` can even be written. Not a ≤3-call composition.

Conclusion: **NOT-COMPOSABLE**. `smulX` presupposes the universal-curve
infrastructure that mathlib lacks; it is the anchor of a bespoke development
(the strong-induction proof of the n•P formula), not a short composition of
existing mathlib lemmas.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulX`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): `x(nP) = φₙ/ψₙ²` is fully standard (Silverman,
  Washington, Wikipedia); the universal-curve-over-ℤ device is standard folklore
  and even cited as motivation in mathlib's own division-polynomial docstring —
  but not implemented there.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (universal ring over ℤ is
  the initial base; nothing to weaken). Modern-idiom check surfaced only a
  *packaging* question (bundle the coordinate maps?), not a weakening.
- Mathlib search (Phase 5): **not in mathlib** — no `Universal` EC namespace, no
  `Universal.Field`, no `smulX`, no zsmul coordinate formula; only the
  fixed-curve ingredients exist.
- Composition check (Phase 6): **NOT-COMPOSABLE** — presupposes the
  missing universal-curve layer; it is a `def`, not a ≤3-call derivation.

**Rationale:**

The *mathematical content* this def participates in — the universal
division-polynomial formula for `n • P` and the universal-curve infrastructure
(`Universal.Ring`, `Universal.Field`, `polyToField`, `ψᵤ`, `smulX`, `smulY`) —
is clearly mathlib-worthy and **genuinely missing**: mathlib has division
polynomials and the fixed-curve function field, and its docstring explicitly
points at the universal ring as the right tool, yet the universal curve and the
n•P coordinate formula are not there. The HasseWeil duplicate confirms the
construction is reusable across projects (and is currently fork/duplicate code,
which is itself an argument for upstreaming).

What pushes this to BORDERLINE rather than a clean YES is that `smulX` is a
**one-line intermediate `def`** whose value is entirely *internal* to the
project's chosen proof architecture (the affine strong-induction route to
`zsmul_eq_smulEval`). It is correct, maximally general, and well-supported by a
~30-lemma API — but whether mathlib wants *this specific helper, with this name,
as a free-standing def* is exactly the kind of API-packaging judgment a mathlib
reviewer makes when the surrounding development is upstreamed. Plausible mathlib
outcomes include: (a) take `smulX`/`smulY` essentially as-is as the named
universal coordinate functions; (b) bundle them into a single
"scalar-multiplication on the generic point" map and demote `smulX` to a
projection/`simp`-lemma; or (c) reorganize the whole universal layer so the
intermediate is spelled differently. The def cannot be assessed in isolation
from that decision, and the decision is not one the skill should make alone.

The correct unit of upstreaming is **the whole universal-curve + n•P-formula
development**, not this single def — so the actionable recommendation is to route
the *file/development* to a human + mathlib reviewer, with `smulX` flagged as
"belongs, modulo packaging".

**Numbered questions (for the user / a mathlib reviewer):**

1. Should the **entire `Universal` Weierstrass-curve layer** (`Universal.Ring`,
   `Universal.Field`, `curve`, `polyToField`, `ψᵤ`, `smulX`, `smulY`, and the
   n•P formula `zsmul_eq_smulEval`) be upstreamed to mathlib as one development?
   (If yes, this becomes a multi-file PR effort and `smulX` rides along.)
2. If yes to (1): keep `smulX`/`smulY` as **free-standing named coordinate
   defs** (current form), or **bundle** them into one
   "generic-point scalar-multiplication" object with `smulX` as a projection?
   (This is the Phase-4c packaging question.)
3. Is mathlib's maintainer (the elliptic-curve / `WeierstrassCurve` owner —
   likely the original division-polynomial author) already preparing this
   upstreaming? The NagellLutz↔HasseWeil duplicate suggests in-flight work;
   if a mathlib PR exists, this is **NO-mathlib-has-it (pending)** and the
   project should track that PR rather than re-upstream.
4. Independent of mathlib: the **verbatim duplication** between
   `NagellLutz/…/ZSMul.lean` and `HasseWeil/…/Auxiliary/DivisionPolynomial.lean`
   should be consolidated into AINTLIB `Common/` regardless of the mathlib
   decision — should a dedup ticket be filed now?

**Next action:** user answers Q1–Q4 (especially Q3 — check whether the
universal-curve / n•P formula is already an open mathlib PR by Junyan Xu, since
this is clearly upstreaming-track code). If upstreaming is desired, treat the
*whole universal-curve development* as the PR unit and run `/generalise` /
`/cleanup` on the file, not on `smulX` alone. Independently, file an AINTLIB
dedup ticket for the NagellLutz↔HasseWeil duplicate.
