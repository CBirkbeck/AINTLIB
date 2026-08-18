# Mathlibable assessment — `WeierstrassCurve.Universal.Jacobian.smulPoly_neg`

**Verdict bucket: `BORDERLINE-needs-human`**

> Correct, textbook fact (the Jacobian-coordinate packaging of `(-n)·P = -(n·P)`), but stated
> entirely in *project-only* vocabulary (`smulPoly`, the `ω` division polynomial, the universal
> curve) and resting on the project-new `ω`-family negation law. It is an internal stepping-stone
> in an in-flight upstream development (Junyan Xu / D. K. Angdinata's `zsmul_eq_smulEval`). Whether
> this specific helper lands as a public mathlib lemma is a packaging call for the maintainers.

---

## 0. Baseline (Phase 0)

- **lake build:** ⚠ stale locally (per task brief). Reasoning is from source + the pinned mathlib
  `.lake` tree (`…/aintlib-decompose/.lake/packages/mathlib`), not a fresh elaboration. The decl
  elaborates in the committed file (no `sorry`).
- **decl `WeierstrassCurve.Universal.Jacobian.smulPoly_neg`:** ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:487`.
- **Qualified name VERIFIED.** Namespace stack: `WeierstrassCurve` (L76) → `Universal` (L86) →
  `Jacobian` (L395, closed L544). Line 487 sits inside all three, so the prompt's parsed guess
  **`WeierstrassCurve.Universal.Jacobian.smulPoly_neg` is exactly correct**.
- **kind:** `lemma` (theorem-kind; Phase 4.5 diamond/defeq is n/a).
- **has sorry:** no — a one-line `simp` proof.
- **module docstring summary:** proves `WeierstrassCurve.zsmul_eq_smulEval`:
  `n • P = (φₙ : ωₙ, ψₙ)` in Jacobian coordinates for `n : ℤ` and a nonsingular affine point
  `P = (x,y)`, via the *universal* Weierstrass curve over `ℤ[A₁…A₆,X,Y]/⟨P⟩` and its fraction field.

```lean
lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp [smulPoly, ω_neg_eq_neg_negY, neg, smul_fin3, (show Odd 3 by decide).neg_pow]
```

with `{n : ℤ}` an implicit section variable in scope, and the immediately-preceding helper

```lean
lemma ω_neg_eq_neg_negY : curve.ω (-n) = -negY curvePoly (smulPoly n) := by …   -- ZSMul.lean:480
```

**Duplication note (cross-project).** A verbatim copy
`lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by …`
lives at `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:509` (same statement, same
proof). This is the duplicated General*/PID* track the project context warned about — a dedup signal
for the on-`main` cleanup fleet, independent of the mathlib question.

---

## 1. Statement (Phase 1)

`smulPoly_neg` is the **Jacobian-coordinate negation-of-multiplier identity** for the universal
division-polynomial triples.

Here `smulPoly k = ![curve.φ k, curve.ω k, curve.ψ k] : Fin 3 → Poly` (ZSMul.lean:414) is the
triple `(φ_k, ω_k, ψ_k)` of division polynomials living in `Poly = ℤ[a₁..a₆][X][Y]` (the universal
coefficient ring, before passing to any fraction field). These are the polynomials giving the
multiplication-by-`k` map in Jacobian coordinates: `k • (X,Y) = ⟦(φ_k, ω_k, ψ_k)⟧` on the universal
curve. `neg curvePoly` is **mathlib's** `WeierstrassCurve.Jacobian.neg` — the Jacobian negation
acting on a `Fin 3 → R` tuple, `(x,y,z) ↦ (x, negY x y z, z)` where
`negY x y z = -y - a₁ x z - a₃ z³`. The scalar action `(-1 : Poly) • -` is mathlib's Jacobian
`smul_fin3`, `u • P = ![u²·Px, u³·Py, u·Pz]`.

The lemma states:

> `(φ₋ₙ, ω₋ₙ, ψ₋ₙ) = (-1) • neg (φₙ, ωₙ, ψₙ)`.

Component-by-component this unpacks to the three classical facts:
- **X:** `φ₋ₙ = (-1)² · φₙ = φₙ` — `φ` is **even** (negation fixes the X-coordinate).
- **Y:** `ω₋ₙ = (-1)³ · negY(φₙ, ωₙ, ψₙ)` — the Y-coordinate of `(-n)·P` is `negY` of the
  Y-coordinate of `n·P`. This is exactly the content of the preceding lemma `ω_neg_eq_neg_negY`,
  which is itself the `ω`-family negation law `ω_neg`
  (`ω₋ₙ = ωₙ + a₁ φₙ ψₙ + a₃ ψₙ³`, `DivisionPolynomialOmega.lean:122`) rewritten through `negY`.
- **Z:** `ψ₋ₙ = (-1)¹ · ψₙ = -ψₙ` — `ψ` is **odd**.

So `smulPoly_neg` is precisely the **Jacobian-coordinate, universal-polynomial-ring packaging of
`(-n)·P = -(n·P)`** — the affine-coordinate version of which is the pair
`smulX_neg`/`smulY_neg`. The `(Odd 3).neg_pow` in the proof produces the `(-1)³ = -1` on the Y/Z
weights; `smul_fin3` distributes the `(-1)` powers across the three components.

Variables / typeclasses (Lean side):
- `{n : ℤ}` — the multiplier, ranging over **all integers** (already full `ℤ` generality).
- No bundled hypotheses. `curve`/`curvePoly`/`Poly` are fixed global objects of this development
  (the universal curve over `ℤ`); `neg`, `smul_fin3` come from mathlib's Jacobian API.

Hypotheses: none. Conclusion: an equation of `Fin 3 → Poly`.

---

## 2. Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line (`simp`) glue lemma stating a parity/negation property of a project-defined
polynomial triple; not a `def`/`class`/`structure`, not a person-named theorem, not a
`## Main results` entry (the headline result is `zsmul_eq_smulEval`). It is an internal bridge in the
even/odd-induction proof.

(Literature width was run EXHAUSTIVE regardless, per protocol for EC/division-polynomial decls.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner-definition check is **n/a**. (The
*proof* is a single `simp`, which reinforces SMALL but is not the Phase-2b def gate.)

---

## 3. Literature search — EXHAUSTIVE protocol

| #  | Channel                     | Query                                                                                                   | Hit? | Standard form found                                              | Notes |
|----|-----------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)   | "division polynomial omega negation `[-n]P = -[n]P` Jacobian coordinates φ ω ψ formula"                  | yes  | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; Jacobian `nP = [φₙψₙ : ωₙ : ψₙ³]`       | MIT 18.783 L6; arXiv 1103.4560, 1108.3051, 2102.07573; the *form* is textbook |
|  2 | WebSearch (ω / Y-coord neg) | "division polynomial ωₙ Y-coordinate multiplication-by-n negation ω₋ₙ negY Weierstrass"                  | partial | `4y·ωₙ = ψₙ₋₁²ψₙ₊₂ − ψₙ₋₂ψₙ₊₁²`; `ωₙ` weight `3n²` homogeneous     | arXiv 1303.4327 (homogeneous div polys), eprint 2010/630; **`ω₋ₙ` is NOT a named result** — follows from the explicit ω formula |
|  3 | WebSearch (parity / named)  | "ψ odd φ even Silverman III.4 negation `−P=(x,negY)` x(−P)=x(P)"                                          | yes  | `ψ₋ₙ=−ψₙ` (odd), `φ₋ₙ=φₙ` (even), `−P=(x, −y−a₁x−a₃)`              | Silverman GTM 106 §III.4 / Ex 3.7; Washington §3.2; Wikipedia "Division polynomials" |
|  4 | ChatGPT MCP                 | (MCP down per task brief — fallback to channels 1–3, 6, 9, 10)                                           | n/a  | —                                                                | recorded n/a: server unavailable; gap covered by 3 distinct WebSearch generality levels + nLab/MO/arXiv |
|  5 | Local references            | `projects/NagellLutz/.mathlib-quality/references/`                                                       | n/a  | (directory absent)                                               | only `.mathlib-quality/overview/` exists; no refs PDFs present |
|  6 | nLab                        | elliptic curve / division polynomial / negation = elliptic involution                                   | partial | inversion is the elliptic involution fixing x                    | the `(-n)P=-(nP)` fact is the group-inverse law; folklore, not a named nLab entry |
|  7 | nCatLab (categorical)       | —                                                                                                       | n/a  | —                                                                | not a categorical concept |
|  8 | Stacks Project (alg geom)   | division polynomial / multiplication-by-n on Weierstrass model                                          | n/a  | —                                                                | Stacks treats abelian schemes abstractly; no explicit division-polynomial coordinate formulas |
|  9 | MathOverflow / Math.SE      | ω₋ₙ negation, `[-n]P=-[n]P` in division-polynomial coordinates                                          | yes  | `[-n]P=-[n]P` & `−P=(x,negY)` are textbook; ψ odd / φ even standard | recurring as routine exercise, not a citable *named* result for ω |
| 10 | recent arXiv (≤5 yr)        | EDS / division-polynomial recurrence; homogeneous (Jacobian) division polynomials over comm. rings      | yes  | arXiv 1303.4327 (homogeneous div polys), 2102.07573 (EDS recur.); matches mathlib `normEDS`/`φ`/`ψ` | the `ω` (Y-coord) family + its negation law is exactly what mathlib still lacks |

Protocol status: WebSearch ran 3 distinct generality levels (specific φ/ω/ψ Jacobian formula;
ω-specific negation; general ψ-odd/φ-even parity) ✓; local refs checked (absent → n/a) ✓;
nLab/Stacks/MathOverflow/arXiv each checked with a reason ✓; ChatGPT MCP recorded n/a (down) with
the gap covered by the breadth of the other channels ✓.

### Literature summary (Phase 3)

Concept identified as: the **Jacobian-coordinate negation law** `(-n)·P = -(n·P)`, i.e. the
conjunction of "φ even" (`φ₋ₙ = φₙ`), "ω transforms by `negY`" (`ω₋ₙ = ωₙ + a₁φₙψₙ + a₃ψₙ³`), and
"ψ odd" (`ψ₋ₙ = -ψₙ`), packaged as one equation of the triple `(φ, ω, ψ)`.

Sources agree on the standard form: **yes** for the *coordinate formula* `[n]P=(φ/ψ²,ω/ψ³)` and the
*parity* statements (`ψ` odd, `φ` even, negation fixes x) — these are textbook (Silverman §III.4;
Washington §3.2; MIT 18.783; arXiv 1303.4327 for the homogeneous/Jacobian packaging). They hold as
**universal polynomial identities over any commutative ring**, which is precisely the generality the
project works at (the universal curve over `ℤ`).

Most general standard form: any Weierstrass curve over any commutative ring, all `n : ℤ`.

Disagreement with the literature: **none**. The Lean statement is the universal/most-general instance
of the textbook fact. The one nuance the searches surface: the **ω-component negation `ω₋ₙ` is not a
*named* result** in the literature — it follows mechanically from the explicit `ωₙ` formula. In this
project it is the lemma `ω_neg` (and its `negY`-wrapped form `ω_neg_eq_neg_negY`), which is exactly
the new-to-mathlib ingredient that makes `smulPoly_neg` more than a `φ_neg`/`ψ_neg` corollary.

---

## 4. Generality analysis — `smulPoly_neg`

Literature-standard form (Phase 3): `(-n)·P = -(n·P)` in Jacobian division-polynomial coordinates,
for a Weierstrass curve over any commutative ring, all `n : ℤ`.

| # | Parameter / hypothesis | Current Lean form                                   | Literature-standard form               | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-----------------------------------------------------|----------------------------------------|---------------------|---------------------------------|
| 1 | base ring / curve      | the **fixed universal** curve over `ℤ` (`curvePoly`, `Poly = ℤ[a₁..a₆][X][Y]`) | any `W : WeierstrassCurve R`, any `[CommRing R]` | yes (in principle) | The identity is a universal polynomial identity → it specialises to every `W`/`R` via `map_φ`/`map_ω`/`map_ψ` + `map_neg`. But this lemma is *deliberately* on the universal curve: the file's strategy is "prove once universally (`smulPoly`), then specialise to `smulRing`/`smulField` via `comp_smul`/`map_neg`" — which is exactly what `smulRing_neg` (L490) and `smulField_neg` (L493) do. |
| 2 | multiplier `n`         | `n : ℤ` (all integers)                              | `n : ℤ`                                | NO                  | `ℤ` is the right and only index for division-polynomial parity. |
| 3 | side conditions        | none (a genuine polynomial identity in `Poly`)       | none for the universal form             | NO                  | The universal-polynomial form is cleaner than any conditional/affine textbook form (no `ψₙ ≠ 0` needed — this is in the polynomial ring, not the fraction field). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** along dimension #1 (on the one fixed
universal curve, not a general `W : WeierstrassCurve R`). This narrowness is **structural, not
accidental**: the universal curve is the device by which a single proof yields the result for all
curves, and the very next two lemmas push `smulPoly_neg` down to `Universal.Ring`/`Universal.Field`
by functoriality. A "more general" `smulPoly_neg` over arbitrary `W` would be a **different lemma**
(`W.smulPoly (-n) = (-1) • Jacobian.neg W.curve (W.smulPoly n)`), provable from this one by
`map_neg` + `map_φ`/`map_ω`/`map_ψ`. If upstreamed, the user-facing form is almost certainly the
general-`W` version (the universal one is the engine).

Number of weakening opportunities: 1 (curve → arbitrary `W`/`R`).
Cost of restatement: **CHEAP** (mechanical — image under `map_*`). Does not change the bucket.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                        | no       | —                      | no bundled hypotheses; `Poly`/`curvePoly` are fixed objects |
|  2 | sequences/metric → filters/topology?                                       | no       | —                      | purely algebraic identity, no limit content |
|  3 | construct an object → universal-property class?                            | no       | —                      | `smulPoly` is itself the universal construction; this is a property of it |
|  4 | set-with-closure-predicate → bundled substructure?                         | no       | —                      | no subobject |
|  5 | vector-space/field-specific → weaken typeclasses (module/(semi)ring)?      | partial  | state over arbitrary `[CommRing R]` (Phase 4b row 1) | already maximally weak once de-universalised |
|  6 | 1-categorical → higher-categorical?                                        | no       | —                      | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                             | no       | `ℤ` is the intrinsic, correct index | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (beyond the de-universalisation already captured in 4b). A finite
algebraic identity; no filter-/category-/universal-property reformulation improves its organisation.
The decl is essentially maximally general but **not standalone-mathlib-shaped**: its subject
(`smulPoly`, `ω`, the universal curve) is project apparatus.

---

## 5. Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## 6. Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.smulPoly_neg`

Searched the pinned mathlib at `…/aintlib-decompose/.lake/packages/mathlib/Mathlib`.

[A] Lean-Finder / [B] Loogle / [C] LeanSearch — index tools target mathlib only; the subject
`smulPoly` / `Universal.Jacobian` does not exist there, so these return no hits by construction.
Covered authoritatively by direct source grep (D/E) over the pinned mathlib.

[D] **Grep mathlib src.**
- `smulPoly`, `smulRing`, `smulField`, `Universal.{Ring,Field,Jacobian}`, `zsmul_eq_smul`,
  `smulEval`, `zsmul_point_eq` → **0 hits** in `Mathlib/`. The entire universal-curve /
  multiplication-by-`n`-via-division-polynomial apparatus is **not in mathlib**.
- `WeierstrassCurve.ω` — the **Y-coordinate division polynomial** family (`protected def ω`) →
  **0 hits**. Mathlib has `φ`/`ψ`/`preΨ`/`Ψ` (DivisionPolynomial), but **not the `ω` family**.
  (The project file `DivisionPolynomialOmega.lean` docstring says verbatim: it *"extends the
  division polynomial development **from mathlib** with the `ω` family"* — authors Junyan Xu,
  David Kurniadi Angdinata, the mathlib EC-division-polynomial authors.)
- No `ω_neg`, no neg-of-`nP` division-polynomial statement anywhere in `Mathlib/`.

[E] **Name pattern.** `smulPoly_neg`, `*_smulPoly`, `ω_neg`, `smulPoly` → **0 hits** in `Mathlib/`.

**What mathlib DOES have** (the ambient operations + the φ/ψ parity primitives):
- `WeierstrassCurve.Jacobian.neg : (Fin 3 → R) → Fin 3 → R` —
  `…/Jacobian/Point.lean:91` (the `neg` used here).
- `WeierstrassCurve.Jacobian.smul_fin3` — `…/Jacobian/Basic.lean:140`.
- `WeierstrassCurve.Jacobian.negY_smul`, `map_negY` — `…/Jacobian/Formula.lean:95,712` (generic
  negation plumbing — **no division-polynomial content**).
- `WeierstrassCurve.φ_neg` (φ even), `WeierstrassCurve.ψ_neg` (ψ odd) —
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (via `normEDS_neg`).
- `normEDS_neg`, `preNormEDS_neg`, `complEDS_neg`, `compl₂EDS_neg` —
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

So mathlib owns the X-component (`φ_neg`) and Z-component (`ψ_neg`) parity, plus the generic
Jacobian `neg`/`smul_fin3`. What is **missing** is (i) the entire `smulPoly`/universal-curve
multiplication apparatus this lemma is phrased over, and decisively (ii) the **`ω` family and its
negation law `ω_neg`** that supplies the Y-component — the crux of the statement.

Concluded: **not in mathlib.** Neither the subject nor the load-bearing `ω`-negation ingredient
exists upstream. This is genuinely-new content (the `ω` family is in-flight upstream work).

---

## 7. Call sites — `WeierstrassCurve.Universal.Jacobian.smulPoly_neg`

Internal use count (NagellLutz, excluding the declaring line 487): **2**.
External-to-file callers: 0 files outside `ZSMul.lean` in NagellLutz.

| Caller file:line   | Usage pattern (one-line excerpt)                                                                  |
|--------------------|---------------------------------------------------------------------------------------------------|
| ZSMul.lean:491     | `simp_rw [smulRing, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl` — proves `smulRing_neg` (same identity in `Universal.Ring`) |
| ZSMul.lean:494     | `simp_rw [smulField, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl` — proves `smulField_neg` (same identity in `Universal.Field`) |

Inline-derivation grep (re-derived elsewhere without `smulPoly_neg`?):
- `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:509` — a **verbatim duplicate**
  `lemma smulPoly_neg` with identical statement and proof, consumed the same way at `:513`/`:568`
  (`smulRing_neg`/`smulField_neg` analogues). Cross-project fork duplication, not an inline bypass.

**What the pattern tells you.** K = 2 internal uses, both `← rewrite`s that lift the polynomial-ring
identity to the ring/field via functoriality (`comp_smul` + `map_neg`); no external/downstream
consumers. This is a **single-purpose bridge lemma**: it exists to prove the polynomial-ring base
case once so that `smulRing_neg`/`smulField_neg` follow by `map_*`. Exactly the granularity of an
internal helper inside a larger upstreaming-grade development (the file mirrors mathlib's EC layout
verbatim and is clearly written to be upstreamed). The call-site signal is weak evidence, consistent
with "internal helper of a coherent development," not "standalone API."

---

## 8. Composition check (Phase 6)

Can `smulPoly_neg` be derived from **existing mathlib** in ≤3 chained calls?

Strictly, the question is partly ill-posed: **mathlib has no `smulPoly`** (nor the `ω` family) to
even *state* the goal. Reading the *proof* as a composition over mathlib primitives:

Attempt 1 (the actual proof): `by simp [smulPoly, ω_neg_eq_neg_negY, neg, smul_fin3, (Odd 3).neg_pow]`
- Mathlib decls used: `WeierstrassCurve.Jacobian.neg`, `Jacobian.smul_fin3`, `Odd.neg_pow` — all
  in mathlib. The X-component reduces to `φ_neg` (even) and the Z-component to `ψ_neg` (odd), both
  in mathlib.
- **Project-only ingredients (decisive):**
  - unfolding `smulPoly` and `curvePoly` (the universal-curve apparatus) — not in mathlib;
  - **`ω_neg_eq_neg_negY`** (ZSMul.lean:480), which is the `ω`-family negation law `ω_neg`
    (`DivisionPolynomialOmega.lean:122`) wrapped through `negY`. **`ω` and `ω_neg` are not in
    mathlib.** This is *not* a generic algebra lemma — it is the substantive, new-to-mathlib
    Y-coordinate negation identity, and it is what the proof's middle component genuinely rests on.
- Result: **fails as a pure-mathlib composition.** Unlike its sibling `smulX_neg` (which *is* a
  ≤3-rewrite consequence of mathlib's `φ_neg`/`ψ_neg`/`neg_sq` once `smulX` is unfolded, because the
  X-coordinate only needs ψ-squared evenness), `smulPoly_neg` carries the **ω/Y-component**, whose
  negation law is project-new. You cannot reconstruct it from ≤3 existing mathlib lemmas: the
  Y-component ingredient `ω_neg` is itself absent upstream.

Conclusion: **NOT-COMPOSABLE** from current mathlib — its prerequisites (`smulPoly`, the universal
curve, and crucially `ω`/`ω_neg`) are not in mathlib. It *is* a one-line consequence **inside the
project**, given that apparatus.

(This is the precise point that separates `smulPoly_neg` from `smulX_neg`. `smulX_neg` →
`NO-composable-from-mathlib` because the X-coordinate negation needs only `φ_neg`+`ψ_neg`+`neg_sq`,
all in mathlib. `smulPoly_neg` includes the Y-coordinate, forcing a dependency on the not-yet-upstream
`ω_neg` — so it is genuinely-new content, matching the `smulY_neg`/`addZ_smulPoly` BORDERLINE
template, not the `smulX_neg` composable template.)

---

## 9. Verdict: `WeierstrassCurve.Universal.Jacobian.smulPoly_neg`

**Category: `BORDERLINE-needs-human`**

**Evidence:**
- **Literature (Phase 3):** the math is the textbook Jacobian negation law `(-n)·P = -(n·P)` —
  `φ` even, `ψ` odd (Silverman §III.4; Washington §3.2; MIT 18.783), `ω` transforming by `negY`.
  The φ/ψ-coordinate formula and its parity are standard; the **ω-component negation `ω₋ₙ` is not a
  named result** (follows from the explicit `ωₙ` formula). Maximally-general (universal) form used.
- **Generality (Phase 4):** STRICTLY NARROWER (fixed universal curve) — but that narrowness is the
  proof device; the user-facing upstream form is the general-`W` version (cheap to restate). No
  modern-idiom improvement.
- **Mathlib search (Phase 5):** **not in mathlib** — neither the subject (`smulPoly`,
  `Universal.{Jacobian,Ring,Field}`, `zsmul_eq_smulEval`) nor the load-bearing **`ω` family / its
  negation law `ω_neg`**. Mathlib has the ambient `Jacobian.neg`/`smul_fin3` and the φ/ψ parity
  primitives (`φ_neg`, `ψ_neg`, `normEDS_neg`), but not this lemma.
- **Composition (Phase 6):** NOT-COMPOSABLE from current mathlib — the Y-component depends on the
  not-yet-upstream `ω_neg`; a one-line consequence only *inside* the project. (Contrast `smulX_neg`,
  which is composable and was bucketed `NO-composable-from-mathlib`.)

**Rationale:**

`smulPoly_neg` is mathematically the well-known statement that negating the multiplier negates the
point, `(-n)·P = -(n·P)`, written in Jacobian coordinates at the level of the universal
division-polynomial triples: `(φ₋ₙ, ω₋ₙ, ψ₋ₙ) = (-1) • neg (φₙ, ωₙ, ψₙ)`. Its three components are
the textbook facts "φ even", "ω transforms by `negY`", "ψ odd". The X- and Z-components are pure
mathlib (`φ_neg`, `ψ_neg`); the Y-component rests on the project's `ω`-family negation law
`ω_neg`/`ω_neg_eq_neg_negY`, and that `ω` family is exactly the piece the file
(`DivisionPolynomialOmega.lean`) advertises as *extending mathlib's division-polynomial development*.
Mathlib today has neither the `ω` polynomials nor the universal-curve `smulPoly` apparatus, so the
lemma can be neither stated nor composed in mathlib as it stands — it is genuinely-new content.

The reason this is BORDERLINE rather than a clean YES is granularity: the decl in isolation is a
single-purpose (K = 2), `simp`-sized bridge lemma stated on the fixed universal curve, whose only job
is to seed `smulRing_neg`/`smulField_neg` by functoriality. The mathlib-worthy object is the **whole
development** — Junyan Xu / D. K. Angdinata's universal-curve track culminating in
`zsmul_eq_smulEval`, which mirrors mathlib's file layout verbatim and is plainly written to be
upstreamed. `smulPoly_neg` would ride into that PR as an internal lemma, most likely restated for a
general `W : WeierstrassCurve R` (Phase 4b) rather than only the universal curve, and quite possibly
kept `private`. Whether to (a) treat it as part of that larger upstreaming unit, (b) restate it
general-`W` and ship it as a named public lemma, or (c) keep it internal — is a packaging/taste call
tied to how the maintainers want to land the `ω`-family + multiplication-formula development. The
verbatim `private`-style duplicate in HasseWeil shows the project itself treats it as an internal
helper. That packaging decision is the human call.

**Numbered questions (≤5):**
1. Is the `WeierstrassCurve.Universal` + `ω`-family + `zsmul_eq_smulEval` development being
   upstreamed to mathlib as a unit (it appears to be Junyan Xu / D. K. Angdinata's work, mirroring
   mathlib structure and authored by mathlib's EC-division-polynomial authors)? If yes,
   `smulPoly_neg` ships *inside* that PR and needs no standalone verdict.
2. In that PR, should `smulPoly_neg` be a **public** lemma restated for a general
   `W : WeierstrassCurve R` (Phase 4b form), or remain a `private`/internal helper on the universal
   curve (as it is now, and as the HasseWeil duplicate is)?
3. The companion `ω` family and its negation law `ω_neg` are the genuinely-new content this lemma
   depends on. Is the upstreaming plan to add the `ω` division polynomials to
   `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` first? (Without `ω`/`ω_neg`,
   `smulPoly_neg` cannot exist upstream.)
4. The lemma is fork-duplicated in HasseWeil (`Auxiliary/DivisionPolynomial.lean:509`). Should the
   AINTLIB cleanup fleet dedup the two copies into one shared `Common/` lemma, independently of the
   mathlib question?

**Next action:** answer Q1–Q4. If the `ω`-family / `zsmul_eq_smulEval` development is being
upstreamed as a unit (Q1 = yes), record `smulPoly_neg` as "ships inside that PR" and assess the
*public* general-`W` form instead (likely YES-add-as-is once `ω`/`ω_neg` are upstream). Otherwise, if
a standalone decision is wanted, the prerequisite is upstreaming the `ω` family first; only then can
`smulPoly_neg` be restated general-`W` and re-run through `/mathlibable`. Separately, file an AINTLIB
dedup cleanup ticket for the NagellLutz/HasseWeil duplication.

---

## 10. Next step

Answer the four numbered questions (chiefly: is this part of the in-flight universal-curve + `ω`-family
upstreaming, and is the public target the general-`W` restatement?). The math is genuinely new to
mathlib — decisively because of the `ω`-component negation law `ω_neg`, which is *not* in mathlib and
is *not* composable from existing primitives (unlike the X-only sibling `smulX_neg`). The only open
question is the packaging grain, which is a maintainer call.

---

### Sources

- MIT 18.783 Elliptic Curves, Lecture #6 (Sutherland): https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf
- Homogeneous division polynomials for Weierstrass elliptic curves (arXiv:1303.4327): https://arxiv.org/abs/1303.4327
- Integral points on elliptic curves and explicit valuations of division polynomials (arXiv:1108.3051): https://arxiv.org/pdf/1108.3051
- A recurrence relation for elliptic divisibility sequences (arXiv:2102.07573): https://arxiv.org/pdf/2102.07573
- Division Polynomials for Alternate Models of Elliptic Curves (eprint 2010/630): https://eprint.iacr.org/2010/630.pdf
