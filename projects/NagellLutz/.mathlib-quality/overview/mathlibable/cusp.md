# /mathlibable report — `WeierstrassCurve.cusp`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> Qualified name **verified from source**: the `def cusp` at `Universal.lean:180`
> sits inside `namespace WeierstrassCurve` (opened line 69, closed line 243) but
> *outside* `namespace Universal` (which ends at line 177). So the full name is
> **`WeierstrassCurve.cusp`** — the parsed name is correct.

---

### Baseline (Phase 0)
- lake build:               not re-run (env: local build stale per task brief); reasoning from source statement as instructed.
- decl `WeierstrassCurve.cusp`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:180`
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — missing-from-mathlib lemmas for the division-polynomial / ZSMul development, the universal Weierstrass curve, and the cusp curve `Y²=X³` (with rational point `(1,1)`, `ψₙ(1,1)=n`) used to prove nonvanishing of the universal `ψₙ`.

---

### Statement (Phase 1)

`WeierstrassCurve.cusp` is **a definition** of the *cuspidal cubic*
`Y² = X³` realised as a Weierstrass curve over `ℤ`:

```lean
/-- The cusp curve $Y^2 = X^3$ over ℤ. -/
def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }
```

In standard notation: the Weierstrass curve with all coefficients
`a₁ = a₂ = a₃ = a₄ = a₆ = 0`, whose affine equation
`Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` collapses to `Y² = X³`. This is the
canonical **cuspidal cubic** — the standard singular Weierstrass curve with a
cusp at the origin, discriminant `Δ = 0`, and additive (G_a) reduction. In this
project it is the specialisation target that makes the universal division
polynomial `ψₙ` easy to evaluate: `ψₙ(1,1) = n` on the cusp (`polyEval_cusp_ψ`).

Variables / typeclasses involved (Lean side):
- none — `Affine ℤ` is `WeierstrassCurve.Affine ℤ`, a mathlib `abbrev` for
  `WeierstrassCurve ℤ` (the base ring is hard-wired to `ℤ`).

Hypotheses (Lean side):
- none (it is a `def`, an anonymous-constructor record literal).

Conclusion (math): the cuspidal cubic `Y² = X³` as a Weierstrass curve.
Conclusion (Lean): n/a — definition; value has type `WeierstrassCurve.Affine ℤ`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (leaning BIG-adjacent for *placement*).
Reason: It is a one-line record literal, not a new structure or a named theorem.
But it *is* a named mathematical object (the cuspidal cubic) — the singular
sibling of mathlib's `ofJ0` / `ofJ1728` example curves — so it has more
standing than an ad-hoc helper. Literature width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`{ a₁ := 0, …, a₆ := 0 }`).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | Downstream proofs (`cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`, `polyEval_cusp_*`) *unfold* `cusp` via `simp [cusp, …]`; the def is not sealed against unfolding, it is meant to be unfolded. No defeq barrier role. |
| Avoid typeclass diamonds         | no       | No instance-search path hinges on the name; `cusp` carries no instances and competes with none. |
| Mark semantic intent / API name  | **yes**  | The name + docstring ("The cusp curve `Y²=X³`") *is* the API surface. ≥7 companion lemmas are named after it (`cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`, `cusp_equation_one_one`, `polyEval_cusp_ψ/φ/ψc/ω`). This is exactly the `ModelsWithJ` pattern: a named curve def anchoring a small lemma family. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name).
This is the *same* exemption mathlib itself relies on for `ofJ0`/`ofJ1728` —
both are one-line `⟨…⟩` literals with `_c₄`/`_Δ` companion lemmas. The one-liner
status is therefore not a NO signal here; it matches mathlib's own house style
for named model curves.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | cuspidal cubic Weierstrass curve `Y²=X³` singular point additive group                  | yes  | `C_cusp = {y²−x³=0}`, cusp at `(0,0)`, smooth locus ≅ G_a via `t↦[t:1:t³]` | Standard across ECC notes (Smith SAC), Harvard M223, Chalmers AG6 |
|  2 | WebSearch (general / role form)  | division polynomials cusp curve `Y²=X³`, `ψₙ` and elliptic divisibility sequences        | yes  | `ψₙ` evaluated at a point gives an EDS; multiplication on nonsingular points of a singular cubic via division polynomials | confirms the project's exact use of `cusp` to compute `ψₙ` |
|  3 | WebSearch (named-after / aliases)| nodal/cuspidal cubic, generalized elliptic curve, additive reduction, standard model    | yes  | cuspidal cubic ⇔ **additive reduction**; nodal ⇔ multiplicative; both are the two singular Weierstrass degenerations | LMFDB reduction-type KB, nLab "nodal curve", Purdue notes |
|  4 | ChatGPT MCP                      | (per task brief, ChatGPT MCP may be down) — substituted with channel #5 Silverman search | n/a  | —                                                     | MCP unavailable in this env; compensated by direct Silverman/EOM lookups (#5, #8) |
|  5 | WebSearch (textbook standard)    | Silverman *Arithmetic of Elliptic Curves*, singular Weierstrass eqn, `Eₙₛ`, additive group | yes  | singular Weierstrass ⇔ `Δ=0`; `Eₙₛ(K)` is a group; cusp case `Eₙₛ ≅ Gₐ` (Silverman III.2.5, exercise 3.5) | the canonical reference; matches mathlib's own `silverman2009` citation style |
|  6 | nLab                             | nodal curve / cuspidal cubic                                                            | yes  | nLab "nodal curve" page treats the singular cubic degenerations; cusp is the `Y²=X³` arithmetic-genus-1 singular curve | abstract treatment confirms naming |
|  7 | nCatLab (categorical)            | —                                                                                      | n/a  | not a categorical concept (a specific curve, not a universal construction) | recorded n/a with reason |
|  8 | Stacks Project (alg geom)        | cuspidal cubic / `Y²=X³`                                                                | n/a  | Stacks discusses cusp/node singularities of curves but has no named "cusp curve" decl to match against | concept present, no named object — recorded n/a (no competing canonical name) |
|  9 | MathOverflow / Math.SE           | cuspidal cubic smooth locus additive group                                             | yes  | standard Q&A: `Y²=X³` smooth locus `≅ Gₐ`, the textbook degenerate elliptic curve | corroborates #1 |
| 10 | recent arXiv (last 5 yr)         | algebraic divisibility sequences / EDS over function fields; `j=1728` primitive divisors | yes  | EDS literature (arXiv 1105.5633, 2102.07573, 2001.09634) uses singular-curve specialisation; `ψₙ` as EDS is current | confirms the `cusp`-as-specialisation technique is live research practice |

Protocol pass check:
- WebSearch ran **5 distinct queries** at three generality levels (specific
  `Y²=X³`, role-in-division-polynomials, named-after/reduction-type) ✓ (≥3).
- ChatGPT MCP: **unavailable in this environment** (task brief flagged it down);
  compensated by two extra textbook/encyclopaedia channels (#5 Silverman, #6
  nLab) that answer the same "standard form + generality" question. Recorded
  honestly rather than faked.
- Local references: **n/a** — no `.mathlib-quality/references/` dir and no
  `refs/NagellLutz/` PDFs exist (both checked, both absent).
- nLab ✓; Stacks checked (n/a, no named object); nCatLab n/a (not categorical);
  MathOverflow ✓; arXiv ✓.

### Literature summary (Phase 3)

Concept identified as: **the cuspidal cubic** `Y² = X³` (a.k.a. "the cusp curve",
the additive-reduction singular Weierstrass curve, the degenerate elliptic curve
with `Δ = 0` whose smooth locus is `≅ 𝔾ₐ`).
Sources agree on the standard form: **yes** — universally `Y² = X³`, cusp at the
origin; the unique cuspidal Weierstrass degeneration (the nodal cubic `Y²=X³+X²`
is its multiplicative-reduction sibling).
Most general standard form: the curve is defined **over any base** — Silverman
and the EDS literature state the singular Weierstrass equation over an arbitrary
field/ring; the object `⟨0,0,0,0,0⟩` makes sense over **any `CommRing R`**, not
just `ℤ`. The `ℤ`-form is the universal/initial instance (specialises to every
base by `map`/`baseChange`).
Generality dimensions where the literature varies:
  - base ring: literature ranges from a fixed field up to **arbitrary commutative
    ring**; the most general (and the mathlib-idiomatic) form is over `R` with
    `[CommRing R]`, exactly as `ofJ0`/`ofJ1728` are stated.
Disagreement with the literature: **none** on the math; the only gap is that the
project pins the base to `ℤ` whereas the standard/mathlib form is base-general.

---

### Generality analysis — `WeierstrassCurve.cusp`

Literature-standard form (Phase 3): the cuspidal cubic `Y²=X³` over **any**
commutative ring `R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring             | hard-wired `ℤ` (`Affine ℤ`) | arbitrary `[CommRing R]` (`Affine R`) | **yes** | the literal `⟨0,0,0,0,0⟩` needs no ring structure beyond `CommRing`; mathlib's sibling `ofJ0 : WeierstrassCurve R` is already stated this way. Generalising costs nothing — it is `(R) [CommRing R]` + the same body. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (base pinned to `ℤ`).
Number of weakening opportunities found: **1** (base-ring generalisation).
Proposed restatement:

```lean
variable (R : Type*) [CommRing R]

/-- The cusp curve `Y² = X³`. -/
def cusp : WeierstrassCurve R := ⟨0, 0, 0, 0, 0⟩
```

Cost of restatement: **CHEAP** — mechanical. The project's `ℤ`-uses recover as
`cusp ℤ` (or stay implicit). The companion lemmas `cusp_ψ₂`/`cusp_Ψ₃`/`cusp_preΨ₄`
are stated over the universal `Poly` ring and would be re-derived for the general
`cusp R` or kept as the `ℤ`-specialisation; either way the proofs (`simp [cusp, …]`)
are base-agnostic.

> Note: the project (a `dev/` producer) is **correct** to pin `ℤ` — it only ever
> needs the `ℤ` cusp, and CLAUDE.md tells producers not to generalise. The
> generalisation is a *mathlib-upstreaming* concern, not a project defect.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | it is a concrete curve, no bundled-hypothesis preamble to convert |
|  2 | sequences/metric → filters/topology? | no | — | no analytic content |
|  3 | construct object → universal-property class? | no | — | `cusp` *is* a concrete construction; no universal property to characterise it (it is one specific curve, like `ofJ0`) |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | not a substructure |
|  5 | field/metric-specific → weaken typeclass to ring? | **yes** | `cusp : WeierstrassCurve R` over `[CommRing R]` (Phase 4b) | matches the `ModelsWithJ` API; lets `cusp` base-change/`map` to any ring and reuse the existing `Δ`/`c₄`/equation lemmas generically |
|  6 | 1-categorical → higher-categorical? | no | — | no categorification axis |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary algebraic structure? | **yes** (same as #5) | base ring `ℤ → R` | unifies with mathlib's base-general model curves and with `baseChange`/`map` API |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (rows 5/7 — base-ring generalisation; this is the
same axis as Phase 4b, not an independent reformulation).
- Proposed mathlib-idiomatic restatement: `def cusp (R) [CommRing R] : WeierstrassCurve R := ⟨0,0,0,0,0⟩` (mirrors `ofJ0`/`ofJ1728`).
- Cost: **CHEAP**.
- Mathlib downstream this enables: a base-general cuspidal cubic composes with
  `WeierstrassCurve.map` / `baseChange`, the existing `Δ`/`c₄`/`b₂…b₈` lemmas, and
  the `Affine.Equation`/`Nonsingular` API at any base — so the `Δ = 0` /
  singular-point facts can be stated once over `R` instead of re-proved per base.
- Real mathematical improvement: yes — it makes `cusp` a *peer* of mathlib's
  named model curves rather than an `ℤ`-only one-off, which is precisely how the
  cuspidal cubic is used (specialise to whatever base the EDS argument needs).

> The modern-idiom axis coincides with the literature-weakening axis (base ring).
> There is **no** deeper restructuring (no typeclass/filter/universal-property
> move) — `cusp` is genuinely just a record literal naming a specific curve.

---

### Diamond / defeq risk — `WeierstrassCurve.cusp`  (Phase 4.5; kind = `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | `cusp` is a `WeierstrassCurve` *value*, not an instance; it introduces no instance-search path, so no two paths can collide. |
| 2 | Reducibility leak | none | Not `@[reducible]`. It is a plain `def`; downstream code unfolds it explicitly via `simp [cusp]`. Body is five literal `0`s — no non-trivial computation to leak. |
| 3 | Non-canonical unfolding | low | `simp [cusp]` unfolds to the all-zero record as intended; the companions rely on this. No surprising `rfl`/`simp` behaviour beyond the obvious. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | `WeierstrassCurve` lives in a fixed universe; `ℤ` (and a general `R : Type*` after generalisation) pose no universe constraint that breaks callers. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`; `Affine R` is a transparent `abbrev` for `WeierstrassCurve R`, already mathlib's own convention. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**.
Top risks: none.
Mitigations: n/a. (This is mechanically the same risk profile as `ofJ0`/`ofJ1728`,
which mathlib already ships without issue.)

---

### Mathlib search-status: `WeierstrassCurve.cusp`

[A] Lean-Finder       — index tool unavailable in this env; substituted with [D]/[E] over the local mathlib tree.
[B] Loogle            (concept is a nullary `def` of a record literal — no useful type-pattern signature to Loogle; `WeierstrassCurve ℤ` would match every curve). n/a — no discriminating type pattern.
[C] LeanSearch        natural-language "cusp curve / cuspidal cubic Weierstrass" → only modular-forms `cuspFunction` family surfaces (different concept). no hit for the curve.
[D] Grep mathlib src  `def cusp`, `WeierstrassCurve.cusp`, `Y²=X³`, `⟨0,0,0,0,0⟩`, `cuspidal`, `singular cubic` over `.lake/packages/mathlib/Mathlib/` → **no hit** for a singular/cusp Weierstrass curve. Only `cusp*` hits are `cuspFunction*` in `Analysis/Complex/Periodic.lean` + the `ModularForms/Cusps.lean` family (cusps of modular curves — unrelated).
[E] Name pattern      `(def|abbrev|lemma) …[Cc]usp` across mathlib, modular-forms excluded → **no hit**. The named model-curve file `AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean` has `ofJ0 ⟨0,0,1,0,0⟩`, `ofJ1728 ⟨0,0,0,1,0⟩`, `ofJNe0Or1728`, `ofJ` — but **no `cusp`** (it only houses *elliptic*, i.e. nonsingular, models).

Searched for both:
  - the user's current form (`cusp` over `ℤ`) — not in mathlib.
  - the literature-standard form (cuspidal cubic over any `R`) — not in mathlib.

Concluded: **not in mathlib** (all methods exhausted, plus the general form). The
closest mathlib artifact is the *family* of named model curves in `ModelsWithJ.lean`
(`ofJ0`/`ofJ1728`/`ofJNe0Or1728`/`ofJ`), which deliberately contains only the
**nonsingular** (elliptic) models — the singular cuspidal cubic is the missing
sibling.

---

### Call sites — `WeierstrassCurve.cusp`

Internal use count: **≥10** (within NagellLutz, excluding the declaring file
`Universal.lean`'s own `cusp_equation_one_one`).
External-to-file callers: **1 file** (`ZSMul.lean`); plus `cusp_equation_one_one`
in the declaring file.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| Universal.lean:182 | `lemma cusp_equation_one_one : cusp.Equation 1 1` (declaring file; dot-notation) |
| ZSMul.lean:110 | `lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by simp [cusp, …]` |
| ZSMul.lean:111 | `lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, …]` |
| ZSMul.lean:112 | `lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, …]` |
| ZSMul.lean:114 | `lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n` |
| ZSMul.lean:118 | `lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1` |
| ZSMul.lean:122 | `lemma polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2` |
| ZSMul.lean:126/127/129 | `polyEval_cusp_ω` proof: `congr(polyEval cusp 1 1 …)`, `simpa [cusp, …]` |

Inline-derivation grep (was the all-zero curve `⟨0,0,0,0,0⟩` re-built inline
elsewhere without `cusp`?): **none found** — every use goes through the named
`cusp`. No bypassing.

Call-sites signal: **K ≥ 3 internal uses, no inline re-derivation → real API**
(the K≥3 row of the Phase-6.0 table → YES-* leaning). This is a working
definition with a genuine consumer family, not dead code.

---

### Composition check (Phase 6)

Can `WeierstrassCurve.cusp` be derived from mathlib in ≤3 chained calls?

This is a **definition**, not a proposition, so "composition" means: is there an
existing mathlib term that already *is* this curve (so `cusp` would just alias it)?

Attempt 1: `cusp := ofJ1728 ℤ`? — **fails.** `ofJ1728 = ⟨0,0,0,1,0⟩` is `Y²=X³+X`
(`a₄=1`), the j=1728 *elliptic* curve, not `Y²=X³`.
Attempt 2: `cusp := ofJ0 ℤ`? — **fails.** `ofJ0 = ⟨0,0,1,0,0⟩` is `Y²+Y=X³`
(`a₃=1`), the j=0 elliptic curve, not the cusp.
Attempt 3: any `ofJ j`? — **fails.** `ofJ` only produces *elliptic* (nonsingular)
curves; the cuspidal cubic has `Δ=0` and is excluded from every mathlib model
constructor by design.

Conclusion: **NOT-COMPOSABLE** from existing mathlib named curves. Writing
`⟨0,0,0,0,0⟩` directly is not a "composition" — there is no mathlib primitive that
yields the all-zero Weierstrass curve; it is a new (small) named object. (One
*could* inline `⟨0,0,0,0,0⟩` at each call site, but that loses the name + docstring
+ the `cusp_*` lemma family's anchor — i.e. it defeats the Phase-2b API-name
exemption — and mathlib's own `ModelsWithJ` precedent is precisely *not* to inline
such literals.)

---

## Verdict: `WeierstrassCurve.cusp`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the cuspidal cubic `Y²=X³` is a standard named
  object (additive-reduction singular Weierstrass curve, smooth locus `≅ 𝔾ₐ`);
  Silverman/EOM/nLab/LMFDB all agree; standard generality is **over any base ring**.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — base pinned
  to `ℤ`; the standard / mathlib-idiomatic form is `def cusp (R) [CommRing R]`,
  matching the sibling `ofJ0`/`ofJ1728`.
- Mathlib search (Phase 5): **not in mathlib** (both forms); closest is
  `ModelsWithJ.lean`, which holds only the nonsingular model curves.
- Composition check (Phase 6): **NOT-COMPOSABLE** — no mathlib primitive yields
  the all-zero curve; the elliptic model constructors exclude `Δ=0`.

**Rationale:**

The cuspidal cubic is a textbook-standard named curve and mathlib visibly *wants*
it: `Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean` already collects the
named Weierstrass models (`ofJ0 = ⟨0,0,1,0,0⟩`, `ofJ1728 = ⟨0,0,0,1,0⟩`,
`ofJNe0Or1728`, `ofJ`) as one-line anonymous-constructor `def`s with `_c₄`/`_Δ`
companion lemmas — but it contains **only the nonsingular (elliptic) models**. The
*singular* member of that family — the cuspidal cubic `⟨0,0,0,0,0⟩` (`Y²=X³`) — is
the obvious gap, and is exactly what `cusp` supplies. It is structurally identical
to its `ModelsWithJ` siblings (one-line literal, docstring, small named lemma
family `cusp_ψ₂`/`cusp_Ψ₃`/`cusp_preΨ₄`/`cusp_equation_one_one`/`polyEval_cusp_*`),
shares their one-liner API-name exemption (Phase 2b), and has identical (zero)
diamond/defeq risk (Phase 4.5). So this is a genuine YES — mathlib should have it.

It is **not** `YES-add-as-is` only because the project pins the base ring to `ℤ`,
whereas every sibling in `ModelsWithJ.lean` is stated over a general `[CommRing R]`
and the literature's standard form is base-general (Phase 4b found exactly one,
CHEAP weakening). Shipping the `ℤ`-only form would be an inconsistent, strictly
narrower addition next to `ofJ0 : WeierstrassCurve R`. The fix is mechanical:
re-state as `def cusp (R) [CommRing R] : WeierstrassCurve R := ⟨0,0,0,0,0⟩`. The
project itself is right to keep `ℤ` (it is a `dev/` producer and only needs the
`ℤ` cusp); the generalisation is an upstreaming step, not a project defect.

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b found the user's `ℤ`-fixed form strictly
    narrower than the base-general literature standard.
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c rows 5/7 — the mathlib-idiomatic form is
    base-general, matching the `ModelsWithJ` siblings so `cusp` composes with
    `map`/`baseChange` and the generic `Δ`/`c₄`/equation API.

**Proposed restatement:**
```lean
namespace WeierstrassCurve
variable (R : Type*) [CommRing R]

/-- The cuspidal cubic `Y² = X³`, the singular Weierstrass curve with a cusp at
the origin (additive reduction; its smooth locus is `𝔾ₐ`). -/
def cusp : WeierstrassCurve R := ⟨0, 0, 0, 0, 0⟩

@[simp] lemma cusp_a₁ : (cusp R).a₁ = 0 := rfl
-- …a₂ a₃ a₄ a₆ analogues…
lemma cusp_Δ : (cusp R).Δ = 0 := by rw [cusp, Δ, b₂, b₄, b₆, b₈]; ring   -- singular: Δ = 0
```
Estimated cost of regeneralisation: **CHEAP** (mechanical; the project's uses
become `cusp ℤ`, and the `simp [cusp, …]` proofs are base-agnostic).

Mathlib downstream this enables (MODERN-IDIOM):
  - `cusp` becomes a peer of `ofJ0`/`ofJ1728` in `ModelsWithJ.lean`, so the named
    model-curve API is *complete* (all three reduction types: good via `ofJ*`,
    cuspidal/additive via `cusp`; nodal/multiplicative is the natural follow-up).
  - composes with `WeierstrassCurve.map` / `baseChange` to specialise to any base
    (the project's own `polyEval cusp …` specialisation generalises for free).
  - the singular-point / `Δ = 0` / `Eₙₛ ≅ 𝔾ₐ` facts can be stated once over `R`
    and reused, rather than re-proved per base — useful for any future
    bad-reduction / Tate-curve development.

**Proposed mathlib location:** `Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean`
(directly alongside `ofJ0`/`ofJ1728`; or a sibling `…/SingularModels.lean` if the
maintainers prefer to separate singular from elliptic models — a reviewer call).
Naming note: confirm `cusp` vs. a more explicit `cuspidalCubic` / `ofCusp` with the
EllipticCurve maintainers (consistency with the `ofJ*` naming scheme may favour a
`cuspidal…`-style name).

**Next action:** run `/generalise WeierstrassCurve.cusp` (it will tension the
`ℤ`-form against the base-general literature/`ModelsWithJ` target from Phases 4b/4c)
to produce the re-stated `def cusp (R) [CommRing R]` + its `_a*`/`_Δ` companion
lemmas, then open a `feat(AlgebraicGeometry): add the cuspidal cubic
WeierstrassCurve.cusp` PR grouped with a `cusp_Δ` (`Δ = 0`) lemma. Optionally
ship the nodal cubic in the same PR to complete the singular-model pair.

---

## Next step

Run `/generalise WeierstrassCurve.cusp` to weaken the base ring from `ℤ` to a
general `[CommRing R]` (matching mathlib's `ofJ0`/`ofJ1728` in `ModelsWithJ.lean`),
then open a `feat(AlgebraicGeometry): add WeierstrassCurve.cusp (the cuspidal
cubic)` PR.
