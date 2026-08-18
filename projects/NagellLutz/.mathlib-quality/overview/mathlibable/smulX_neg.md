# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX_neg`

## Baseline (Phase 0)

- lake build:               ⚠ stale locally (per task brief); reasoning done from source + mathlib `.lake` tree, not a fresh elaboration
- decl `WeierstrassCurve.Universal.Affine.smulX_neg`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:201`
- kind:                      `lemma` (theorem)
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ, ψₙ)` in Jacobian coords for `n : ℤ` and a nonsingular affine point `P = (x,y)`, via the *universal* Weierstrass curve over `ℤ[A₁…A₆,X,Y]/⟨P⟩` and its fraction field.

True qualified name **VERIFIED**: the prompt's guess `WeierstrassCurve.Universal.Affine.smulX_neg` is exactly correct. Namespace stack at line 201: `WeierstrassCurve` (line 76) → `Universal` (line 86) → `Affine` (line 157). The lemma reads:

```lean
lemma smulX_neg : smulX (-n) = smulX n := by
  simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]
```

with `{n : ℤ}` an implicit variable in scope.

---

## Statement (Phase 1)

`smulX_neg` states that the universal-field X-coordinate function of `n • (X,Y)` is **even in `n`**: `smulX (-n) = smulX n`.

Here `smulX n : Universal.Field` is the rational function `polyToField (curve.φ n) / (ψᵤ n) ^ 2` (ZSMul.lean:164) — i.e. `φₙ / ψₙ²` interpreted in `Universal.Field = Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨W⟩)`. It is the candidate X-coordinate of the point `n • (X,Y)` on the *universal* Weierstrass curve, later proved equal to the actual group-law X-coordinate (`zsmul_point_eq_smulX_smulY`).

Mathematically this is the universal-field instance of the elementary classical fact

  x([−n]·P) = x([n]·P)

which holds because `[−n]·P = −([n]·P)` and the negation map on a Weierstrass curve fixes the X-coordinate (`(x,y) ↦ (x, −y − a₁x − a₃)`). In division-polynomial terms: `φ` is even (`φ₋ₙ = φₙ`), `ψ` is odd (`ψ₋ₙ = −ψₙ`), and `ψ` enters `smulX` squared, so the sign cancels.

Variables / typeclasses (Lean side):
- `{n : ℤ}` — the multiplier; ranges over **all integers** (the construction is already at full `ℤ` generality).
- No typeclass parameters on the lemma itself: `Universal.Field` / `curve` / `ψᵤ` are fixed global objects of this development (the universal curve over `ℤ`).

Hypotheses (Lean side): none.

Conclusion (math): the X-coordinate rational function of `n·(X,Y)` is invariant under `n ↦ −n`.
Conclusion (Lean): `smulX (-n) = smulX n` (an equation in `Universal.Field`).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a 2-line glue lemma (`simp_rw` only) stating a parity property of a project-defined rational function; not a named theorem, not a project main result, introduces no new structure.

(Literature width was run EXHAUSTIVE regardless.)

---

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner-definition check is **n/a**. (Recorded note: the *proof* is effectively a single `simp_rw`, which reinforces the SMALL classification but is not the Phase-2b def check.)

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve division polynomials multiplication by n x-coordinate φₙ/ψₙ² even function negation"    | yes  | x([n]P) = φₙ(x)/ψₙ²(x); ψₙ² is a function of x alone   | arXiv 1103.4560, 1108.3051; confirms ψₙ² ∈ ℤ[x,a₁…a₆] (even in y) |
|  2 | WebSearch (general / parity)     | "division polynomial ψₙ odd φₙ even parity elliptic curve Silverman III.4"                              | yes  | ψ₋ₙ = −ψₙ (ψ odd); φₙ = xψₙ² − ψₙ₋₁ψₙ₊₁ ∈ ℤ[x,a,b]     | Wikipedia "Division polynomials"; jtnb.881; cites Silverman GTM 106 |
|  3 | WebSearch (named / negation)     | "Weierstrass curve negation −P same x-coordinate x(−P)=x(P) … multiplication by minus n"                | yes  | −P = (x, σₓ(y)); x(−P)=x(P)                            | Wikipedia "EC point multiplication"; arXiv 2302.10640 (formal group law) |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to channels 1–3 + 6–10)                                             | n/a  | —                                                    | recorded n/a: server unavailable in this environment; covered by 3 distinct WebSearch generality levels + nLab |
|  5 | Local references                 | `.mathlib-quality/references/` for NagellLutz                                                           | n/a  | (directory absent)                                   | only `.mathlib-quality/overview/` exists; no refs PDFs present |
|  6 | nLab                             | "elliptic curve" / "division polynomial" / negation fixes x                                             | partial | negation/inversion is the elliptic involution fixing x | nLab has elliptic-curve group law; the x(−P)=x(P) fact is folklore, not a named nLab entry |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                                    | not a categorical concept |
|  8 | Stacks Project (alg geom)        | division polynomial / multiplication-by-n on Weierstrass model                                          | n/a  | —                                                    | Stacks treats abelian schemes abstractly; no explicit division-polynomial X-coordinate formula |
|  9 | MathOverflow / Math.SE           | x-coordinate of −P, evenness of φₙ/ψₙ²                                                                  | yes  | x(−P)=x(P) is textbook; ψ odd, φ even is standard      | recurring as routine exercise, not a citable named result |
| 10 | recent arXiv (≤5 yr)             | EDS recurrence / division polynomials negation                                                          | yes  | preNormEDS/normEDS negation = mathlib's own source     | arXiv 2102.07573 (EDS recurrence); matches mathlib `normEDS_neg` |

The protocol passes: WebSearch ran 3 distinct generality levels (specific φ/ψ formula, general parity, named negation fact); local refs checked (absent → n/a); nLab/Stacks/MathOverflow/arXiv each checked with reasons; ChatGPT MCP recorded n/a (down) with the gap covered by the breadth of the other channels.

### Literature summary (Phase 3)

Concept identified as: **evenness of the X-coordinate of `[n]P` under `n ↦ −n`** — equivalently the conjunction of "ψ is an odd EDS" (`ψ₋ₙ = −ψₙ`) and "φ is even" (`φ₋ₙ = φₙ`), with ψ entering the X-coordinate squared.
Sources agree on the standard form: **yes**. x([n]P) = φₙ/ψₙ²; ψ odd; φ even; x(−Q) = x(Q). All textbook (Silverman GTM 106 §III.4 / exercise 3.7; Washington, *Elliptic Curves* §3.2; Wikipedia).
Most general standard form: holds for any Weierstrass curve over any commutative ring (the polynomial identities `φ₋ₙ = φₙ`, `ψ₋ₙ = −ψₙ` are integral). The project already works at this maximal generality via the *universal* curve over `ℤ`.
Generality dimensions where the literature varies:
  - base: short Weierstrass `y²=x³+ax+b` (textbook) vs. general Weierstrass `a₁…a₆` (mathlib/this project — strictly more general).
  - index: always `ℤ` (the natural home of EDS parity); no further generalisation.
Disagreement with the literature: **none**. The Lean form is the universal/most-general instance of the textbook fact.

---

## Generality analysis — `smulX_neg`

Literature-standard form (from Phase 3): `x([−n]P) = x([n]P)` for a Weierstrass curve over any commutative ring, all `n : ℤ`.

| # | Parameter / hypothesis | Current Lean form                  | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|------------------------------------|---------------------------------|---------------------|---------------------------------|
| 1 | base ring / curve      | the *universal* curve over `ℤ` (`curve`, `Universal.Field`) | general Weierstrass over any comm. ring | NO  | Already maximal: the universal curve is the **terminal/most-general** Weierstrass curve; any ring-curve instance is a specialisation via `ringEval`/`map`. Can't be weaker. |
| 2 | multiplier `n`         | `n : ℤ` (all integers)             | `n : ℤ`                          | NO                  | `ℤ` is the right and only index for EDS parity. |
| 3 | torsion side-condition | none (statement is an identity of rational functions, vacuously fine where ψₙ=0) | textbook needs `P` not `n`-torsion to *evaluate*; the universal identity needs nothing | NO | The universal-field form is cleaner than the textbook conditional form. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: 0
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream |
|----|-----------------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                  | no       | —                      | The lemma already has no bundled hypotheses; `Universal.Field` is a fixed object. |
|  2 | sequences/metric → filters/topology?                                                                 | no       | —                      | Purely algebraic identity; no limit content. |
|  3 | construct an object → universal-property class?                                                      | no       | —                      | `smulX` is already *the* universal construction (its whole point); `smulX_neg` is a property of it. |
|  4 | set-with-closure-predicate → bundled substructure?                                                   | no       | —                      | No subobject involved. |
|  5 | vector-space/field-specific → weaken typeclasses (modules/(semi)ring)?                               | no       | —                      | Already over the universal `ℤ`-curve; `φ_neg`/`ψ_neg` hold over any comm. ring. |
|  6 | 1-categorical → higher-categorical?                                                                  | no       | —                      | n/a. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                                       | no       | —                      | Index is `ℤ`; EDS parity is intrinsically `ℤ`-indexed. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already an algebraic identity over the most-general (universal) curve at the natural `ℤ` index; there is no contemporary reformulation that improves organisation. The decl is maximally general but **not standalone-mathlib-shaped** (see Phase 5/6): its subject `smulX` is a private apparatus.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `smulX_neg`

[A] Lean-Finder       "x coordinate of n•P is even", "smulX negation"   no hits (no `smulX`/`Universal.Field` notion in mathlib)
[B] Loogle            `smulX (-_) = smulX _`-shaped; `?f (-_) = ?f _` over EC X-coord  no hits — `smulX` / `Universal.Affine` do not exist in mathlib
[C] LeanSearch        "x-coordinate of negative multiple equals x-coordinate of multiple, division polynomials"  no direct hit; nearest is negation fixing X-coord, not the n•P rational function
[D] Grep mathlib src  `.lake/.../Mathlib`: `namespace Universal`, `Universal.Field`, `def smulX`, `def smulY`, `polyToField`, `ψᵤ`, `smulEval`, `zsmul_eq_smulEval`, `zsmul_point_eq`  **ALL zero hits** — the entire universal-curve / multiplication-by-n-via-division-polynomial apparatus is NOT in mathlib
[E] Name pattern      `smulX_neg`, `smulX` in `.lake/.../Mathlib`  zero hits

Searched for both:
  - the user's current form (`smulX (-n) = smulX n`) — absent (no `smulX`).
  - the literature-standard form. Mathlib **does** have the underlying parity primitives the proof reduces to:
    * `WeierstrassCurve.ψ_neg : W.ψ (-n) = -W.ψ n` — **in mathlib**, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (proved by `normEDS_neg`).
    * `WeierstrassCurve.φ_neg : W.φ (-n) = W.φ n` — **in mathlib**, same file.
    * `normEDS_neg`, `preNormEDS_neg`, `complEDS_neg`, `complEDS₂_neg` — **in mathlib**, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:318,206,445,272`.
  - The X-coordinate of `[n]P`-as-a-formula and the parity statement `smulX_neg` about it: **not in mathlib** (all 5 methods exhausted).

Important context: the project's own `φ_neg`/`ψ_neg` (DivisionPolynomial.lean:401,350) are **forked copies** of these mathlib lemmas (this is the documented fork of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and `Mathlib.NumberTheory.EllipticDivisibilitySequence`). They are byte-for-byte equivalent to mathlib and defer to `normEDS_neg`. So the *building blocks* of `smulX_neg` are 100% already in mathlib; what is missing is only the `smulX` rational-function apparatus that `smulX_neg` is phrased over.

Concluded: **not in mathlib** — `smulX` and the multiplication-by-n formula apparatus are project-only; mathlib has the parity *building blocks* (`φ_neg`, `ψ_neg`, `normEDS_neg`) but not this lemma or its subject.

---

## Call sites — `smulX_neg`

Internal use count: **2** (within NagellLutz, excluding the declaring line 201).
External-to-file callers: 0 files outside `ZSMul.lean` in NagellLutz (both uses are in the same file).

| Caller file:line   | Usage pattern (one-line excerpt)                                              |
|--------------------|------------------------------------------------------------------------------|
| ZSMul.lean:220     | `· rintro (rfl|rfl); exacts [rfl, smulX_neg]` — discharges the `m = −n` case of `smulX_eq_smulX_iff` |
| ZSMul.lean:382     | `simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]` — the `(−n)•P` step of `zsmul_point_eq_smulX_smulY` |

Inline-derivation grep (re-derived elsewhere without `smulX_neg`?):
  - In the **HasseWeil** project, `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:258` defines an **independent copy** `smulX_neg` over its own copy of `smulX` (line 240), used at line 454. This is the duplicated General*/PID* track the project context warned about — confirming the lemma is genuinely useful within the EC-multiplication development, but also that it is internal apparatus duplicated across two AINTLIB projects rather than a mathlib-facing result.

Call-site signal: K = 2 internal uses, no inline re-derivation that bypasses it; it is real glue API *for the `smulX` development*. Per the Phase 6.0.1 table this leans toward "real API," but the API in question is the project-private `smulX` apparatus, not a mathlib-shaped standalone.

---

## Composition check (Phase 6)

Can `smulX_neg` be derived from mathlib in ≤3 chained calls?

Strictly speaking the question is ill-posed because **mathlib has no `smulX`** to even state the goal. Re-reading the *proof* as a composition over the building blocks (which mathlib does have, modulo the trivial `polyToField` wrapper that is itself project-only):

Attempt 1 (the actual proof): `by simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]`
  - Mathlib decls used: `WeierstrassCurve.φ_neg`, `WeierstrassCurve.ψ_neg` (both in mathlib), `neg_sq`, `map_pow`.
  - Project-only glue: unfolding `smulX`, `ψᵤ` (and `polyToField`, the universal-field embedding — project-only).
  - Result: **succeeds**. The mathematical core is exactly `φ even ∧ ψ odd ∧ ψ squared ⇒ φ/ψ² even`; once `smulX` is unfolded, it is a 3-rewrite identity over mathlib's `φ_neg`/`ψ_neg` + `neg_sq`.
  - Notes: the only non-mathlib ingredients are the *names* `smulX`/`ψᵤ`/`polyToField` — the universal-field apparatus.

Conclusion: **COMPOSABLE** — over mathlib's parity primitives plus the project's own `smulX` unfolding, in ≤3 rewrites. It is glue, not new mathematics. It is *not* independently composable in mathlib only because mathlib lacks the `smulX` subject; it would become a one-line glue lemma the moment that apparatus is upstreamed.

---

## Verdict: `smulX_neg`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): `x([−n]P)=x([n]P)` / `ψ` odd / `φ` even is textbook (Silverman §III.4, Washington §3.2); maximally-general form already used.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom improvement available.
- Mathlib search (Phase 5): subject `smulX` and the whole multiplication-by-n-via-division-polynomial apparatus are **not in mathlib**; the parity *building blocks* `WeierstrassCurve.φ_neg`, `WeierstrassCurve.ψ_neg`, `normEDS_neg` **are** in mathlib.
- Composition check (Phase 6): COMPOSABLE — a 3-rewrite glue lemma over `φ_neg`/`ψ_neg`/`neg_sq` once `smulX` is unfolded.

**Rationale:**

`smulX_neg` is a 2-line glue lemma asserting that the universal-field X-coordinate function `smulX n = φₙ/ψₙ²` is even in `n`. Its entire mathematical content is the classical, elementary fact that `x([−n]P) = x([n]P)` — true because `[−n]P = −([n]P)` and negation on a Weierstrass curve fixes `x`. The proof unfolds `smulX` and applies mathlib's `φ_neg` (φ even), `ψ_neg` (ψ odd), and `neg_sq` (ψ appears squared, so the sign cancels). Mathlib already owns every reusable ingredient: `WeierstrassCurve.φ_neg` and `WeierstrassCurve.ψ_neg` are *in mathlib*, and the project's local copies of them are explicit forks that just call mathlib's `normEDS_neg`. What is missing from mathlib is only the `smulX` rational-function apparatus (`Universal.Field`, `polyToField`, `ψᵤ`, `smulX`) over which the lemma is phrased — and that apparatus is project-internal scaffolding for proving the `n•P` coordinate formula, duplicated across NagellLutz and HasseWeil.

Therefore `smulX_neg` is not a standalone mathlib contribution. It belongs to the `smulX`/multiplication-by-n development as glue and would only ever reach mathlib *as part of upstreaming that whole apparatus* — at which point it is a trivial one-liner shipped alongside `smulX`, not a lemma worth a PR on its own. Adding it to mathlib in isolation is impossible (no `smulX` to talk about); extracting it as a general lemma is pointless (the general lemma is just `φ_neg`+`ψ_neg`+`neg_sq`, all already present). This is the textbook `NO-composable-from-mathlib` shape: mathlib has the building blocks; the result is a ≤3-call composition; nothing new is needed.

**WHY not (refactor-actionable):**

Mathlib has the parity building blocks; `smulX_neg` is a ≤3-rewrite composition over them plus the project-private `smulX` unfolding. No mathlib lemma is missing.

Mathlib building blocks:
- `WeierstrassCurve.φ_neg` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (`W.φ (-n) = W.φ n`)
- `WeierstrassCurve.ψ_neg` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (`W.ψ (-n) = -W.ψ n`, via `normEDS_neg`)
- `normEDS_neg` — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:318`
- `neg_sq`, `map_pow` — mathlib core

Composition sketch (the actual proof, ≤3 substantive rewrites):
```lean
-- over the project's own `smulX`/`ψᵤ`/`polyToField`:
lemma smulX_neg : smulX (-n) = smulX n := by
  simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]
```

Call sites in our project (from Phase 6.0): K = 2 (ZSMul.lean:220, 382), plus 1 independent duplicate in HasseWeil (Auxiliary/DivisionPolynomial.lean).

Refactor plan: **keep `smulX_neg` as a local glue lemma in the project** — it is the right size and is used. No mathlib action. Because mathlib has no `smulX`, there is nothing to inline *to mathlib* at the 2 call sites; the lemma must stay wherever `smulX` lives. The only cross-project cleanup worth noting (an AINTLIB dedup ticket, NOT a mathlib action): NagellLutz `ZSMul.smulX_neg` and HasseWeil `Auxiliary/DivisionPolynomial.smulX_neg` are duplicates over duplicated `smulX` definitions; if the universal multiplication-by-n apparatus is ever consolidated into a shared `Common/` module (or upstreamed to mathlib wholesale), this lemma collapses to a single one-liner and the duplicate is deleted.

Next action: no mathlib PR. Leave `smulX_neg` in place as project glue. If/when the `Universal.Affine.smulX` multiplication-by-n development is consolidated or upstreamed as a unit, `smulX_neg` rides along as a trivial `simp_rw` lemma — it is never a standalone contribution.

---

## Next step

No mathlib PR. `smulX_neg` is a ≤3-rewrite glue lemma over mathlib's existing `φ_neg`/`ψ_neg`/`neg_sq`, phrased over the project-private `smulX` apparatus; keep it local. Only revisit if the entire `Universal.Affine` multiplication-by-n development is upstreamed, in which case this ships with it as a one-liner. Optional AINTLIB-internal dedup: unify the NagellLutz and HasseWeil copies.
