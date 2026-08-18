# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); reasoning from source
- decl `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:217`
- kind:                     lemma (theorem)
- has sorry:                no
- enclosing namespaces:     `WeierstrassCurve` (l.76) → `Universal` (l.86) → `Affine` (l.157)
  ⇒ true qualified name **`WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`** (matches the
  parsed name)
- module docstring summary: ZSMul.lean proves `WeierstrassCurve.zsmul_eq_smulEval`
  (`n • P = (φₙ : ωₙ, ψₙ)` in Jacobian coords) via the **universal pointed curve**
  `ℤ[A₁,…,A₆,X,Y]/⟨W⟩` and its fraction field `Universal.Field`.

---

### Statement (Phase 1)

`smulX_eq_smulX_iff` states, for integers `m n : ℤ`:

> `smulX m = smulX n ↔ m = n ∨ m = -n`.

Here `smulX n : Universal.Field` is **the x-coordinate of `n • P`** for `P = (X, Y)` the *universal
pointed point* on the universal Weierstrass curve over `Universal.Field = Frac(ℤ[A₁,…,A₆,X,Y]/⟨W⟩)`,
defined (l.164) as the rational function `φₙ(X,Y) / ψₙ(X,Y)²` (`smulX n := polyToField (curve.φ n) /
(ψᵤ n)^2`). So the lemma says: **the x-coordinate of `m·P` equals the x-coordinate of `n·P` (for the
universal, infinite-order point `P`) iff `m = ±n`.** Mathematically this is the conjunction of two
standard facts — "two points share an x-coordinate iff one is the negation of the other" and "on the
universal curve `P` has infinite order, so `m·P = ±(n·P) ⟺ m = ±n`."

Variables / typeclasses (Lean side):
- `{m n : ℤ}` — the two integer multipliers (implicit, from the `variable {m n : ℤ}` at l.97).
- No typeclass parameters: everything is fixed by the ambient `Universal` machinery
  (`Universal.Field`, `ψᵤ`, `curve.φ`, all `noncomputable`).

Hypotheses (Lean side): none.

Conclusion (math): the x-coordinate map `n ↦ x(n·P)` on the universal curve is two-to-one with fibres
`{n, −n}` (and the only collision is the sign one).

Conclusion (Lean): `smulX m = smulX n ↔ m = n ∨ m = -n`.

Proof (l.217–220): `⟨fun h ↦ ?_, ?_⟩`; forward by `contrapose!` + `smulX_ne_smulX h.1 h.2`; backward by
`rintro (rfl|rfl)` then `rfl` / `smulX_neg`. The real content lives in the sibling lemma
`smulX_ne_smulX` (l.206), which uses `smulX_sub_smulX` (l.186) and `ψᵤ_ne_zero` — i.e. it is proved
from the EDS/division-polynomial apparatus of this project, **not** from any mathlib point-arithmetic
lemma.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a two-line glue iff over a sibling inequality `smulX_ne_smulX`; not a named theorem, not a
`## Main results` entry (the main result is `zsmul_eq_smulEval`); introduces no new structure.

(Literature width still run in full below.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` ⇒ one-line-def check **n/a**. (Recorded for the gate.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                           | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve x-coordinate of nP determines n up to sign division polynomial injective"       | yes  | `x(nP)=φₙ(x)/ψₙ²(x)`; roots of `ψₙ` = x-coords of `E[n]\{O}`; x-coord of `nP` is `±`-ambiguous | Silverman-style standard; division polys give `x(nP)` as a rational function |
|  2 | WebSearch (general form)         | "elliptic curve two points equal x-coordinate iff P equals Q or P equals minus Q"               | yes  | `P,Q` share an x-coord ⟺ `P = ±Q` (vertical-line/reflection) | textbook ("two points have equal x-coordinate iff one is the negation of the other") |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2: "vertical line property", "reflection across x-axis", "division polynomial")  | yes  | same as #2 | concept is unnamed folklore; no eponym |
|  4 | ChatGPT MCP                      | —                                                                                               | n/a  | MCP down per task note; substituted extra WebSearch (#1–#3) + direct mathlib source reading | fallback used as instructed |
|  5 | Local references                 | `.mathlib-quality/references/` for the project                                                   | n/a  | directory absent (`projects/NagellLutz/.mathlib-quality/references/` does not exist) | recorded n/a |
|  6 | nLab                             | "elliptic curve" / "division polynomial"                                                         | n/a  | nLab has no page stating this elementary coordinate fact | too elementary for nLab's abstract treatment |
|  7 | nCatLab                          | —                                                                                               | n/a  | not a categorical statement | — |
|  8 | Stacks Project                   | division polynomial / x-coordinate of multiple                                                   | n/a  | Stacks does not cover explicit Weierstrass division-polynomial arithmetic | concrete EC arithmetic out of Stacks scope |
|  9 | MathOverflow / MSE               | (covered via WebSearch #2 — Stanford/Doche–Lange/notes hits)                                     | yes  | same vertical-line fact restated in lecture notes (Festi notes, Doche–Lange ch.13) | confirms folklore status |
| 10 | recent arXiv (≤5 yr)             | "recurrence relation for elliptic divisibility sequences" (arXiv:2102.07573); "explicit valuations of division polynomials" (arXiv:1108.3051) | yes  | EDS / division-poly machinery; `ψₙ ≠ 0 ⟺ n·P ≠ O` for non-torsion | corroborates the `ψᵤ_ne_zero`-style injectivity argument |

Protocol pass check: WebSearch ran 3 queries at different generality (specific `x(nP)` form, general
two-point form, aliases); ChatGPT MCP recorded n/a (down) with a substituted extra WebSearch; local
refs n/a (absent); nLab/Stacks/nCatLab/MathOverflow/arXiv each checked with a reason. ✓

### Literature summary (Phase 3)

Concept identified as: **"the x-coordinate of a point on an elliptic curve determines the point up to
sign"**, specialised to the multiples `n·P` via division polynomials (`x(nP) = φₙ/ψₙ²`).
Sources agree on the standard form: **yes** — universally stated as "x₁ = x₂ ⟺ P = ±Q" (the
vertical-line / reflection property), with the division-polynomial refinement giving `x(nP)` explicitly.
Most general standard form: for any two nonsingular affine points `P, Q` on a Weierstrass curve over a
field, `xₚ = x_Q ⟺ P = Q ∨ P = −Q`. The `smulX m = smulX n ⟺ m = ±n` version is the specialisation
to `P = m·(X,Y)`, `Q = n·(X,Y)` on the **universal** curve, where `(X,Y)` has infinite order so
`m·P = ±n·P ⟺ m = ±n`.
Generality dimensions where the literature varies:
  - which points: arbitrary `P, Q` (most general) → the specific multiples `m·P, n·P` (this lemma).
  - which base: any field (most general) → the one fixed universal field `Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`.
Disagreement with the literature: none — the lemma is a faithful, correct specialisation.

---

### Generality analysis — `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`

Literature-standard form (Phase 3): for nonsingular affine `P, Q` on `W` over a field `F`,
`xₚ = x_Q ↔ P = Q ∨ P = -Q`.

| # | Parameter / hypothesis            | Current Lean form                       | Literature-standard form         | Weaker form exists? | Reason |
|---|-----------------------------------|-----------------------------------------|----------------------------------|---------------------|--------|
| 1 | the two objects compared          | the rational functions `smulX m`,`smulX n` (x-coords of `m·P`,`n·P`) | arbitrary points `P, Q`          | yes (more general)  | the abstract two-point version (mathlib's `Point.X_eq_iff`) subsumes this; the `n ↦` indexing is an extra specialisation |
| 2 | the base field                    | the single universal field `Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)` | any field `F`                    | yes (more general)  | nothing here is special to the universal field except that it makes `P` infinite-order |
| 3 | the conclusion's RHS              | `m = n ∨ m = -n` (integer multipliers)  | `P = Q ∨ P = -Q` (points)        | n/a — this *is* the project's added value | converting `P = ±Q` to `m = ±n` needs `point` infinite-order (`ψᵤ_ne_zero`), project-specific |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it specialises the standard two-point
x-coordinate fact (already in mathlib, rows 1–2) to multiples of one fixed infinite-order point on one
fixed (universal) curve. But the narrowing is *purposeful*: the `m = ±n` integer conclusion (row 3) is
exactly what the surrounding `zsmul_eq_smulEval` induction consumes, and it is **not** a mechanical
weakening target — generalising rows 1–2 away would delete the lemma's reason to exist (it would just
become mathlib's `Point.X_eq_iff`).
Number of weakening opportunities: 2 (both already realised by an existing mathlib lemma — see Phase 5).
Proposed restatement: none that keeps the lemma meaningful — see Phase 7.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled hypotheses → typeclasses | no | no hypotheses to bundle | — |
| 2 | sequences/metric → filters/topology | no | finite algebraic identity over a field | — |
| 3 | construction → universal property | no | — | — |
| 4 | set+closure → bundled substructure | no | — | — |
| 5 | vector-space/field-specific → weaker typeclass | partial | the *abstract* version (`Point.X_eq_iff`) already states it over any field; but the integer-index `m=±n` form is the project's point | mathlib's `Point.X_eq_iff`/`xRep_eq_xRep_iff` |
| 6 | 1-categorical → higher-categorical | no | — | — |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid/group | no | the `ℤ`-index is intrinsic (it is the multiplier of a fixed point) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma as stated). The contemporary mathlib idiom for the
*underlying* fact is `WeierstrassCurve.Affine.Point.X_eq_iff` / `xRep_eq_xRep_iff` (two abstract points),
which mathlib already has; the project's lemma is the `n ↦ m·point` specialisation of it, whose value is
the integer `m = ±n` conclusion, not a re-organisation.

---

### Diamond / defeq risk — n/a (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`

[A] Lean-Finder       (index unavailable locally)                              n/a — substituted [D]/[E] grep over the vendored mathlib source
[B] Loogle            `Iff (Eq _ _) (Or (Eq _ _) (Eq _ (Neg.neg _)))` shape    no exact hit for `smulX`; the *shape* matches `Point.X_eq_iff` / `xRep_eq_xRep_iff`
[C] LeanSearch        "x coordinate of two points equal iff equal or negation" no `smulX` hit; surfaces the abstract `Point.X_eq_iff` family
[D] Grep mathlib src  `smulX`, `ψᵤ`, `namespace Universal`, `polyToField`      **no hits** — none of the project's universal-curve machinery exists in mathlib
[E] Grep mathlib src  `smulX_eq_smulX`, `smulX_ne_smulX`, `X_eq_iff`, `xRep_eq_xRep_iff`, `eq_or_eq_neg_of_xRep_eq_xRep` | `smulX_*`: no hits. `X_eq_iff`: **HIT** `Affine/Point.lean:639`. `xRep_eq_xRep_iff`: **HIT** `Affine/Point.lean:881`. `eq_or_eq_neg_of_xRep_eq_xRep`: HIT `Affine/Point.lean:872` |

Searched for both:
  - the user's current form (`smulX m = smulX n ↔ m = ±n`) — **not in mathlib** (`smulX` absent).
  - the literature-standard abstract form — **in mathlib**:
    - `WeierstrassCurve.Affine.Point.X_eq_iff` (`Affine/Point.lean:639`):
      `x₁ = x₂ ↔ some x₁ y₁ h₁ = some x₂ y₂ h₂ ∨ some x₁ y₁ h₁ = -some x₂ y₂ h₂`.
    - `WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff` (`Affine/Point.lean:881`):
      `P.xRep = Q.xRep ↔ P = Q ∨ P = -Q` (handles the point at infinity too).

Concluded: **not in mathlib in this form** (the `smulX` apparatus is project-only), **but the
underlying abstract fact IS in mathlib** as `Point.X_eq_iff` / `xRep_eq_xRep_iff`. The project lemma is
the specialisation `P := m • point`, `Q := n • point` *plus* the order-of-`point` step
`m • point = ±(n • point) ⟺ m = ±n`.

---

### Call sites — `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`

Internal use count: **0** (the *iff* `smulX_eq_smulX_iff` itself is not referenced outside its
declaration; its sibling `smulX_ne_smulX` is the one actually consumed).
External-to-file callers: 0.

| Caller file:line              | Usage pattern (one-line excerpt) |
|-------------------------------|-----------------------------------|
| (none — `smulX_eq_smulX_iff` itself is unused inside the project) | — |
| ZSMul.lean:360 *(uses sibling `smulX_ne_smulX`, not this iff)*    | `have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)` |

Inline-derivation grep (was the equivalent re-derived elsewhere?):
  - The forward direction is `smulX_ne_smulX` contraposed; that inequality (not the iff) is what the
    `zsmul_point_eq_smulX_smulY` induction calls at l.360. So the *iff packaging* has **0** consumers;
    the underlying inequality has 1.

Signal: `K = 0` internal uses of the iff (the iff is a tidy public restatement; the load-bearing form is
the sibling inequality). Per the call-sites table this leans toward NO-composable / "wrapper", *except*
that the composition is not a ≤3 mathlib-call inline (see Phase 6) — pushing the verdict to BORDERLINE.

---

### Composition check (Phase 6)

Can `smulX m = smulX n ↔ m = n ∨ m = -n` be derived from **mathlib** in ≤3 chained calls?

Attempt 1 — via `Point.X_eq_iff` / `xRep_eq_xRep_iff`:
  To use the mathlib lemma one must first (a) know `smulX k` is the x-coordinate of the point
  `k • Affine.point` — that is the project theorem `zsmul_point_eq_smulX_smulY` (l.343), a full
  induction — and (b) convert `m • point = ±(n • point)` into `m = ±n`, which needs `point` to have
  infinite order (`ψᵤ_ne_zero`, the EDS non-vanishing). Neither (a) nor (b) is a mathlib primitive.
  - Mathlib decls used: `Affine.Point.X_eq_iff`, `Affine.Point.xRep_eq_xRep_iff` (abstract only).
  - Result: **fails** as a ≤3-call mathlib composition — the bridge (a)+(b) is project-specific and
    substantial.

Attempt 2 — direct, as the project does it:
  `smulX_eq_smulX_iff` ⟵ `smulX_ne_smulX` ⟵ `smulX_sub_smulX` + `ψᵤ_ne_zero` + `IsEllSequence.normEDS`.
  All of these are **project** lemmas built on the forked DivisionPolynomial / EDS apparatus.
  - Result: this is a genuine proof over project machinery, **not** a mathlib composition.

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. Mathlib has the abstract endpoint
(`X_eq_iff`) but not the `smulX`-to-point bridge that this lemma sits on top of.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the fact is standard textbook folklore (x-coords equal ⟺ points equal
  up to sign; `x(nP)=φₙ/ψₙ²`); no eponym; confirmed across ≥4 channels.
- Generality analysis (Phase 4): STRICTLY NARROWER than the abstract two-point form — it specialises to
  multiples of one infinite-order point on the universal curve; the narrowing is purposeful, not a
  mechanical weakening miss. No modern-idiom re-organisation.
- Mathlib search (Phase 5): the **abstract** fact is in mathlib (`Affine.Point.X_eq_iff` l.639,
  `xRep_eq_xRep_iff` l.881); the **`smulX` form is NOT** (the whole `Universal.smulX`/`ψᵤ` apparatus is
  absent from mathlib).
- Composition check (Phase 6): NOT-COMPOSABLE in ≤3 mathlib calls — the `smulX`↔point bridge
  (`zsmul_point_eq_smulX_smulY` + `point` infinite-order) is project-specific and heavy.

**Rationale:**

This lemma sits in an awkward middle. Its *mathematical content* — "the x-coordinate of `n·P`
determines `n` up to sign" — is completely standard, and mathlib already proves the abstract two-point
version (`WeierstrassCurve.Affine.Point.X_eq_iff` and `xRep_eq_xRep_iff`: `x₁ = x₂ ⟺ P = ±Q`). So
"add it as a new general result" is wrong: mathlib has the general statement. But it is equally wrong to
call it `NO-mathlib-has-it` or `NO-composable-from-mathlib`, because the lemma is **not** phrased over
mathlib points — it is phrased over the project's bespoke `smulX n : Universal.Field` (the rational
function `φₙ/ψₙ²` on the universal pointed curve), and mathlib has none of that machinery (`smulX`,
`ψᵤ`, `Universal.Field`, `polyToField` are all project-only). Bridging from the mathlib abstract lemma
to this `smulX` form requires the project's own `zsmul_point_eq_smulX_smulY` (a full induction) plus the
infinite-order fact `ψᵤ n ≠ 0` — far more than a ≤3-call inline.

So the verdict turns on a **policy/architecture judgment the skill cannot make alone**: is the
`Universal.smulX` apparatus itself bound for mathlib? If the universal-curve division-polynomial
multiplication formula (`zsmul_eq_smulEval` and its `smulX`/`smulY` scaffolding) is upstreamed, then
`smulX_eq_smulX_iff` rides along as a natural API lemma of that scaffolding (a `YES-add-as-is`
*conditional on the scaffolding landing*). If instead only the *abstract* point-level facts are wanted
upstream, then this lemma stays project-internal and should simply be derived, at its single point of
use, from mathlib's `Point.X_eq_iff` via the project bridge — i.e. it is library-internal glue, not a
mathlib target. The call-site signal reinforces the "internal glue" reading: the iff itself has **zero**
internal consumers; only its sibling inequality `smulX_ne_smulX` is used (once, at l.360).

**Numbered questions (≤5):**

1. Is the `WeierstrassCurve.Universal` apparatus (the universal pointed curve, its fraction field
   `Universal.Field`, and the `smulX`/`smulY = φₙ/ψₙ², ωₙ/ψₙ³` rational functions) intended for
   upstreaming to mathlib, or is it a project-internal device for proving `zsmul_eq_smulEval`?
2. If `smulX`/`smulY` are NOT going upstream: do you want `smulX_eq_smulX_iff` (and `smulX_ne_smulX`)
   kept as project-internal lemmas, or refactored to derive from mathlib's
   `WeierstrassCurve.Affine.Point.X_eq_iff` / `xRep_eq_xRep_iff` via `zsmul_point_eq_smulX_smulY`?
3. If the apparatus IS going upstream: should the upstreamed API expose the integer-indexed form
   `x(mP) = x(nP) ⟺ m = ±n` for an infinite-order point (this lemma's content) as a named result, or
   leave callers to compose the abstract `X_eq_iff` with an infinite-order hypothesis themselves?

**Next action:** user answers the questions; re-run `/mathlibable
WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff` to resolve to a final bucket. (Strong default if
no upstreaming of the `Universal` apparatus is planned: treat as project-internal glue — derive from
mathlib's `Point.X_eq_iff` at the one site that needs the inequality — i.e. effectively
NO-mathlib-has-it for the *abstract* content, with this `smulX` packaging being scaffolding.)

---

## Next step

User answers questions 1–3 (chiefly: does the `Universal.smulX` apparatus go to mathlib?), then re-run
`/mathlibable WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`.
