# /mathlibable report — `LutzNagell.PID.curveK_equation_iff`

> Step-9 mathlibable assessment, single declaration. Repo: AINTLIB / NagellLutz.
> Source: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:35`.
> Project context: this project forks parts of mathlib's elliptic-curve / division-polynomial
> stack and maintains **duplicated `General*` (`ℤ/ℚ`) and `PID*` (`R/K`) tracks**, so the prior
> expectation was that this decl may already live in mathlib. **That expectation is confirmed.**
> This is the **PID-track twin** of `curveQ_equation_iff` (already classified `NO-mathlib-has-it`);
> see `analysis/05-duplications.md:52` which lists the pair explicitly ("special-case of PID").

---

## Baseline (Phase 0)

- lake build:               not re-run (environment build stale, per task note); reasoning from source + mathlib source on pin
- decl `LutzNagell.PID.curveK_equation_iff`: ✓ resolved at `PIDCurve.lean:35`
- qualified name:           **`LutzNagell.PID.curveK_equation_iff`** (namespaces `LutzNagell` ▸ `PID`, lines 17–18). The prompt's parsed guess `LutzNagell.PID.curveK_equation_iff` is **correct** (VERIFIED from source).
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: "General Weierstrass model over a PID and its fraction field" — sets up `W : WeierstrassCurve R` for a PID `R` with fraction field `K`, its base change `curveK R K W := W.map (algebraMap R K)`, and basic rewriting lemmas (equation, coefficients). The header states it "generalizes `GeneralCurve.lean` from `ℤ/ℚ` to an arbitrary PID `R` with fraction field `K`."

Exact source:

```lean
variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- The base change of `W` to the fraction field `K`. -/
abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)

lemma curveK_equation_iff (x y : K) :
    (curveK R K W).toAffine.Equation x y ↔
      y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x +
        algebraMap R K W.a₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveK]
```

(Note: although the file/abbrev are *named* with a PID/fraction-field intent, the `variable` block
only requires `[CommRing R] [Field K] [Algebra R K]`. The `[IsFractionRing R K]` / PID hypotheses are
**not** used in this particular lemma — it holds for any `R`-algebra `K`. This makes the
specialisation gap to mathlib's `equation_iff` even wider than in the ℚ case.)

---

## Statement (Phase 1)

`curveK_equation_iff` states the following:

> Let `R` be a commutative ring, `K` an `R`-algebra (intended: the fraction field of a PID `R`), and
> let `W` be a Weierstrass curve over `R`. Write `curveK R K W = W.map (algebraMap R K)` for the base
> change of `W` to `K`. For `x, y : K`, the affine point `(x, y)` lies on `curveK R K W` if and only
> if `y² + a₁ x y + a₃ y = x³ + a₂ x² + a₄ x + a₆`, where each `aᵢ` is the coefficient of `W` pushed
> into `K` via `algebraMap R K`.

It is the standard affine (long) Weierstrass equation, written out explicitly, for the specific curve
obtained by base-changing a curve over `R` to `K` — with the coefficients already pushed across the
algebra map and presented as `algebraMap R K W.aᵢ`.

Variables / typeclasses involved (Lean side):
- `R : Type*` `[CommRing R]` — base ring (intended PID).
- `K : Type*` `[Field K] [Algebra R K]` — the `R`-algebra (intended fraction field of `R`).
- `W : WeierstrassCurve R` — a Weierstrass curve over `R`.
- `x y : K` — affine coordinates over `K`.

Hypotheses (Lean side): none (no `IsFractionRing`, no PID assumption is invoked by *this* lemma).

Conclusion (math): membership of `(x,y)` on the base-changed curve ⇔ the explicit Weierstrass
polynomial relation with the coefficients mapped into `K`.

Conclusion (Lean):
`(curveK R K W).toAffine.Equation x y ↔ y^2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y = x^3 + algebraMap R K W.a₂ * x^2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆`

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `rw` + `simp` rewriting lemma that unfolds the `Equation` predicate for a fixed
base-changed curve; not a named theorem, not a new structure, not a `## Main results` entry. It is
plumbing for the `PID*` track (the verbatim analogue of `GeneralCurve`'s `curveQ_equation_iff`).
(Literature width is EXHAUSTIVE regardless — elliptic curves / Weierstrass theory.)

## One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner-definition check does not apply.
(For completeness: the *proof* is two tactic lines, `rw [...]; simp [...]`; that is the composition
signal flagged in Phase 6, not a Phase-2b concern.)
One-liner verdict: n/a (kind is lemma).

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                           | Query                                                                                          | Hit? | Standard form found                                                                 | Notes |
|----|-----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)         | general Weierstrass equation affine `y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆` over a field / base change PID fraction field | yes  | $`y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6`$ — exactly, `aᵢ ∈ k`                          | Stanford crypto notes; Wikipedia "Elliptic curve"; Fiveable EC notes; Lange ECC slides — all give exactly this long Weierstrass form over a field |
|  2 | WebSearch (general form)          | same relation over an arbitrary base ring / field; existence over the field of definition       | yes  | identical relation; "any elliptic curve over a field `K` admits this affine form with `aᵢ ∈ K`" | Wikipedia; the relation is ring-agnostic — `K` (a field) is one instance, the most general is an arbitrary commutative ring |
|  3 | WebSearch (named-after / aliases) | "(long / generalized) Weierstrass equation", "Weierstrass model", PID / global-minimal-model    | yes  | same relation; over a PID `R` a **global minimal Weierstrass equation** exists, and base change to `Frac R` is functorial | Harvard "Nagell–Lutz, quickly" (Alpoge); UCSB ch.2; the PID/fraction-field setting is exactly the classical Nagell–Lutz integral-model context — base change is coefficientwise |
|  4 | ChatGPT MCP                       | n/a — MCP reported down for this environment (task note); substituted by extra WebSearch strands #2,#3 and direct mathlib-source reading (Phase 5) | n/a  | (covered by #1–#3 + mathlib source)                                                 | The "standard form + generality + historical evolution" question is fully answered: the long Weierstrass equation is classical, stated over an arbitrary base ring; the base-change-to-`K` specialisation is a one-line functoriality remark, not a distinct literature object |
|  5 | Local references                  | `projects/NagellLutz/.mathlib-quality/references/` and `refs/`                                  | n/a  | both directories absent in this checkout                                            | recorded n/a (refs are LOCAL-ONLY per AINTLIB rules and not present here) |
|  6 | nLab                              | "Weierstrass elliptic curve" affine equation                                                    | n/a  | nLab treats the moduli/stacky side, not the bare affine equation                    | the explicit affine relation is below nLab's abstraction level; no distinct standard form there |
|  7 | nCatLab                           | —                                                                                               | n/a  | not a categorical concept                                                            | this is a polynomial-membership predicate, not a categorical construction |
|  8 | Stacks Project                    | Weierstrass equation / elliptic-curve chapter                                                    | n/a  | Stacks states the long Weierstrass equation identically; base change is functorial   | confirms the relation is standard over any ring; the `K`-specialisation is not a separate Stacks object |
|  9 | MathOverflow / Math.StackExchange | base change of a Weierstrass equation to the fraction field; integral vs. fraction-field model   | n/a  | routine; "apply the ring hom to each coefficient" (folklore)                         | no thread needed — `map` of a Weierstrass curve applies the ring hom coefficientwise (mathlib's `def map`) |
| 10 | recent arXiv (last 5 years)       | Nagell–Lutz / Weierstrass model base change over number fields & PIDs                            | yes  | arXiv:2509.07524 (Nagell–Lutz for imaginary quadratic fields), arXiv:2310.11768 (Weierstrass curves over `ℤ_n`), arXiv:1812.10415 (Selmer/Mordell–Weil) — all use the identical affine relation, base-changed | confirms the form is the contemporary standard; the integral-curve-over-`R` → equation-over-`K = Frac R` pattern is exactly the Nagell–Lutz working setup; no newer/more-general affine relation exists |

**Protocol pass check:** WebSearch ran ≥3 distinct queries at different generality levels (#1 specific,
#2 general/over-a-field, #3 named-after + PID/global-minimal-model). ChatGPT MCP recorded n/a with
reason (down in this env) and explicitly substituted by additional WebSearch strands + direct
mathlib-source reading, which fully cover the "standard form + generality" question. Local refs
checked (absent → n/a). nLab / Stacks / MathOverflow / arXiv each checked with a one-line reason.

### Literature summary (Phase 3)

Concept identified as: the **(long / generalized) affine Weierstrass equation** of an elliptic curve,
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.
Sources agree on the standard form: **yes** — Stanford, Wikipedia, Fiveable, Lange, UCSB, Stacks all
state exactly this relation.
Most general standard form: the relation holds over **any commutative base ring** with `aᵢ` in that
ring; base change is the coefficientwise application of a ring homomorphism (here `algebraMap R K`).
The PID/fraction-field instance is the classical Nagell–Lutz setup (integral model over `R`, equation
read over `K = Frac R`) and is treated in the literature as a routine functoriality step.
Generality dimensions where the literature varies:
  - base ring: from a specific field/ring (`K`) up to an arbitrary commutative ring — the most
    general is "arbitrary commutative ring", and the literature default is exactly that.
  - source of the coefficients: a curve given directly over the base, vs. a curve base-changed from a
    sub-ring (`R ↪ K`) — the literature treats the latter as a one-line functoriality remark.
Disagreement with the literature: **none.** The user's form is the literature form, fixed to
`base ring = K (a field, intended Frac R)` and `curve = map of an R-curve`.

---

## Generality analysis — `curveK_equation_iff`

Literature-standard form (from Phase 3): the affine Weierstrass equation over an **arbitrary
commutative ring**, i.e. mathlib's `WeierstrassCurve.Affine.equation_iff`.

| # | Parameter / hypothesis              | Current Lean form                          | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|--------------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | base ring of the curve              | `K` (the curve `curveK R K W : WeierstrassCurve K`, with `[Field K]`) | arbitrary `[CommRing R']`             | **yes**             | `equation_iff` holds verbatim over any commutative ring; the `[Field K]` instance is an arbitrary specialisation. Mathlib already states the fully general form. |
| 2 | the curve itself                    | `curveK R K W = W.map (algebraMap R K)` — a base change of an `R`-curve | an arbitrary curve over the base ring | **yes**             | nothing in the statement needs the `K`-curve to be `map`ped from `R`; mathlib's `equation_iff` takes any `W' : WeierstrassCurve K`. The `map` here only serves to rewrite `(curveK R K W).aᵢ` to `algebraMap R K W.aᵢ` (cosmetic coefficient presentation). |
| 3 | coefficient presentation            | `algebraMap R K W.aᵢ`                       | `(curveK R K W).aᵢ` (curve's own coeffs)| n/a (cosmetic)      | the mapped form is purely a display choice; `WeierstrassCurve.map_aᵢ` (auto-`@[simp]` from `@[simps] def map`) and the project's own `curveK_aᵢ` simp lemmas (PIDCurve.lean:29–33) bridge `(curveK R K W).aᵢ = algebraMap R K W.aᵢ` in one `simp`. |
| 4 | PID / fraction-field hypotheses     | `[Field K] [Algebra R K]` (intended `IsFractionRing R K`, `R` a PID) | none needed for the equation itself  | **yes** (already absent) | the lemma does **not** use any PID or `IsFractionRing` hypothesis; it would hold even for `K` a non-field `R`-algebra. So even the file's nominal generality framing is unused here. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (two specialisation axes: base ring fixed to
a field `K`, curve fixed to an `R→K` base change; plus an *unused* `[Field K]` constraint).
Number of weakening opportunities found: 2 substantive (axes 1 and 2), + 1 vacuous (axis 4: a
constraint present in the framing but not used).
Proposed restatement (if STRICTLY NARROWER): the maximally general form is **already in mathlib** as
`WeierstrassCurve.Affine.equation_iff (W : WeierstrassCurve R) (x y : R)`. There is nothing to restate
into the project — the general statement exists upstream. Hence this is a `NO-mathlib-has-it` case
(mathlib has the strictly-more-general form), **not** a `YES-but-generalise-first`.
Cost of restatement: n/a — no new declaration; the consumer should call the existing mathlib lemma
(plus the coefficient simp lemmas) directly.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                    | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                              | no       | —                      | the base ring is already a typeclass parameter in mathlib's `equation_iff` |
|  2 | sequences/metric → filters/topological?                                                                      | no       | —                      | purely algebraic; no topology |
|  3 | construct an object → universal-property class?                                                             | no       | —                      | this is a membership predicate, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                          | no       | —                      | no substructure here |
|  5 | vector-space/field-specific → module/ring typeclass weakening?                                              | **yes**  | state over `[CommRing R']` rather than `[Field K]` — but mathlib's `equation_iff` already does exactly this | the general lemma composes with every base ring, including the `R`-curve and any base change |
|  6 | 1-categorical → higher/∞-categorical?                                                                       | no       | —                      | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                                                            | no (re: index); the analogous "specific base ring → arbitrary ring" point is row 5 | —          | covered by row 5 |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, but it is **already realised in mathlib** — the contemporary
mathlib-idiomatic form is `WeierstrassCurve.Affine.equation_iff` over `[CommRing R]`. The project
lemma is the un-idiomatic specialisation (fixed field `K`, fixed `map`). Because the modern form is
the existing upstream lemma, this does **not** push the verdict toward `YES-but-generalise-first`
(there is no new general lemma to ship); it reinforces `NO-mathlib-has-it`.
Real mathematical improvement: none beyond what mathlib already provides.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `curveK_equation_iff`

[A] Lean-Finder       n/a (index/MCP queries not available in this env) — superseded by direct mathlib-source reading below
[B] Loogle            type-pattern `WeierstrassCurve.Affine.Equation _ _ ↔ _` / `_ .Equation _ _ ↔ _ = _`  →  expected hits: `equation_iff`, `equation_iff'` (matches the project proof's own `rw`)
[C] LeanSearch        natural-language "Weierstrass curve affine equation iff polynomial" → expected hit: `WeierstrassCurve.Affine.equation_iff`
[D] Grep mathlib src  `equation_iff`, `Equation.map`, `map_equation`, `baseChange_equation`, `map_a₁`, `@[simps] def map`, `curveK` over `.lake/packages/mathlib/` → see below (ran; authoritative)
[E] Name pattern      `curveK` / `curveK_equation_iff` over mathlib src → **no hits** (project-only name, as expected)

Direct mathlib-source findings (the load-bearing evidence — grepped on the pinned mathlib):

- **`WeierstrassCurve.Affine.equation_iff`** — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`:
  ```lean
  lemma equation_iff (x y : R) : W.Equation x y ↔
      y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    rw [equation_iff', sub_eq_zero]
  ```
  General over any `[CommRing R]`. This is **exactly** the project statement with `R := K`,
  `W := curveK R K W`, before the cosmetic coefficient rewrite. (The project proof literally opens by
  calling it: `rw [WeierstrassCurve.Affine.equation_iff]`.)
- **`WeierstrassCurve.map_a₁ … map_a₆`** — auto-generated `@[simp]` lemmas from `@[simps] def map`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230–231`): `(W.map f).aᵢ = f (W.aᵢ)`.
  With `f = algebraMap R K` these turn `(curveK R K W).aᵢ` into `algebraMap R K W.aᵢ` — exactly what
  the project's `simp [curveK]` does, and what the in-file `curveK_aᵢ` lemmas (PIDCurve.lean:29–33)
  restate.
- **`WeierstrassCurve.Affine.map_equation` / `Equation.map`** — `Affine/Basic.lean:275–281`: the
  base-change interaction `(W.map f).Equation (f x) (f y) ↔ W.Equation x y` for injective `f`
  (a *different*, complementary fact: it relates the equation over `R` to the equation over `K` at
  *mapped* points, whereas `curveK_equation_iff` characterises the equation over `K` at *arbitrary*
  `K`-points). Note: mathlib also has `baseChange_equation` (`Affine/Basic.lean:312`).
- **`curveK` / `curveK_equation_iff`** — `[E]` name search over mathlib: **no hits** (confirmed
  project-only; the prompt's "may already be in mathlib" warning refers to the *general* form, which
  is `equation_iff`, not to this exact name).

Searched for both:
  - the user's current form (`curveK`-specialised, field `K`, mapped coefficients) → not present
    verbatim (it is a project specialisation);
  - the literature-standard form (general ring) → **present as `WeierstrassCurve.Affine.equation_iff`**.

Concluded: **found in mathlib as `WeierstrassCurve.Affine.equation_iff`; strictly more general form**
(our lemma is the `R := K`, `W := W.map (algebraMap R K)` specialisation, with coefficients rewritten
by the existing `map_aᵢ` simp lemmas).

---

## Call sites — `curveK_equation_iff`

Internal use count: **6** (within NagellLutz, excluding the declaring file `PIDCurve.lean`).
External-to-file callers: **3 distinct files** (`PIDPrimeOrder.lean`, `PIDIntegralMultiple.lean`,
`PIDMain.lean`).

| Caller file:line                                   | Usage pattern (one-line excerpt)                                       |
|----------------------------------------------------|------------------------------------------------------------------------|
| `LutzNagellTheorem/PIDMain.lean:257`               | `have hQ := (curveK_equation_iff R K W x y).mp hpt.left`               |
| `LutzNagellTheorem/PIDPrimeOrder.lean:132`         | `((curveK_equation_iff R K W x y).mp hns.left) hψ hsf_lc`              |
| `LutzNagellTheorem/PIDPrimeOrder.lean:168`         | `((curveK_equation_iff R K W x y).mp hns.left) hpreΨ hsf_lc`          |
| `LutzNagellTheorem/PIDPrimeOrder.lean:171`         | `((curveK_equation_iff R K W x y).mp hns.left) hx₀⟩`                  |
| `LutzNagellTheorem/PIDPrimeOrder.lean:211`         | `((curveK_equation_iff R K W x y).mp hns.left) hx₀⟩`                  |
| `LutzNagellTheorem/PIDIntegralMultiple.lean:90`    | `((curveK_equation_iff R K W x y).mp hns.left) hx₀⟩`                  |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?):
  - (none found) — every consumer goes through `curveK_equation_iff`; the `.mp` direction is always used.

Signal reading: `K = 6` internal uses across 3 files is a genuine in-project API (would normally lean
YES). But the parent (`equation_iff`) is in mathlib in a strictly more general form, so the re-aim
rule applies: this is a thin, `K`-specialised convenience wrapper, and the consumers should call the
mathlib lemma plus the coefficient simp lemmas instead. The 6 call sites are the refactor surface.
(Exactly mirrors `curveQ_equation_iff`'s K = 5, same disposition.)

---

## Composition check (Phase 6)

Can `curveK_equation_iff` be derived from mathlib in ≤3 chained calls? **Yes — it already is.**

Attempt 1 (the actual project proof, verbatim):
```lean
rw [WeierstrassCurve.Affine.equation_iff]   -- general-ring iff, instantiated at R := K, W := curveK R K W
simp [curveK]                               -- fires map_a₁..map_a₆ (and curveK_aᵢ) to push coefficients through algebraMap
```
  - Mathlib decls used: `WeierstrassCurve.Affine.equation_iff`, `WeierstrassCurve.map_a₁..map_a₆`
    (auto-`@[simp]`), plus generic `algebraMap`/`map` simp facts.
  - Result: **succeeds** (this is the existing proof; 2 tactic steps).
  - Notes: the entire content of the lemma is "`equation_iff` specialised + coefficients pushed
    through `map`". No new mathematics.

Conclusion: **COMPOSABLE** — and, more strongly, it is a direct specialisation of a single mathlib
lemma (`equation_iff`) with a cosmetic `simp`. Because mathlib has the *general statement itself*
(not merely building blocks), the primary bucket is `NO-mathlib-has-it`; the composition sketch is
the refactor recipe for inlining at the 6 call sites.

---

## Verdict: `LutzNagell.PID.curveK_equation_iff`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the long Weierstrass equation `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆` is the
  universal standard form (Stanford, Wikipedia, Fiveable, Lange, UCSB, Stacks), stated over an
  arbitrary base ring; the base-change-to-`K = Frac R` instance is the classical Nagell–Lutz integral
  -model setup (Alpoge; arXiv:2509.07524; arXiv:2310.11768) and is not a distinct literature object.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — two specialisation axes (base
  ring fixed to a field `K`; curve fixed to an `R→K` `map`), plus an unused `[Field K]`/PID framing.
  The general form is the upstream lemma.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.Affine.equation_iff`** (general
  ring); the project lemma is its `R:=K`, `W:=curveK R K W` specialisation, coefficients rewritten by
  the existing `WeierstrassCurve.map_aᵢ` `@[simp]` lemmas.
- Composition check (Phase 6): **COMPOSABLE** (≤2 lines; it is literally the existing proof).

**Rationale:**

Mathlib already contains this result in strictly greater generality.
`WeierstrassCurve.Affine.equation_iff` (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`)
states, for any `[CommRing R]` and any `W : WeierstrassCurve R`, exactly
`W.Equation x y ↔ y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. The project lemma is that statement
specialised to base ring `K` and curve `curveK R K W = W.map (algebraMap R K)`, with the only extra
content being that the coefficients `(curveK R K W).aᵢ` are displayed as `algebraMap R K W.aᵢ` — a
rewrite the auto-generated `@[simps]` lemmas `WeierstrassCurve.map_aᵢ` (and the in-file `curveK_aᵢ`)
discharge in a single `simp`. The proof body *is* the proof of this fact:
`rw [WeierstrassCurve.Affine.equation_iff]; simp [curveK]`. There is no new mathematics, and the
specialisation does not even need its own name. This is the PID-track analogue of `curveQ_equation_iff`
(already `NO-mathlib-has-it`); if anything the case is **stronger** here, because the base ring `K` is
already an arbitrary field (closer to mathlib's `[CommRing R]` than `ℚ` was) and the lemma does not
use any PID/`IsFractionRing` hypothesis at all. This is precisely the "duplicated General/PID tracks
fork mathlib" situation the project context flagged: the PID-track `curveK` plumbing re-expresses an
existing mathlib lemma at a fixed base ring.

**WHY not (refactor-actionable):**
Mathlib already has it. The exact decl is **`WeierstrassCurve.Affine.equation_iff`**, located at
**`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`**. Our form follows in ≤2 lines
(modulo the cosmetic coefficient map, handled by `simp`):

```lean
-- our statement, derived directly:
example (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]
    (W : WeierstrassCurve R) (x y : K) :
    (curveK R K W).toAffine.Equation x y ↔
      y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]; simp [curveK]
```

Existing mathlib decl:  `WeierstrassCurve.Affine.equation_iff`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`
Supporting mathlib decls (for the coefficient rewrite): `WeierstrassCurve.map_a₁ … map_a₆`
                        (auto-`@[simp]` from `@[simps] def map`, `Mathlib/.../Weierstrass.lean:230`).

Call sites in our project (from Phase 6.0): **K = 6** (1 in `PIDMain.lean`, 4 in `PIDPrimeOrder.lean`,
1 in `PIDIntegralMultiple.lean`).

Refactor plan: this lemma is **owned by the NagellLutz producer** and lives on the `PID*` track; the
cleanest disposition is one of:
  1. **Inline + delete.** At each of the 6 call sites, replace `(curveK_equation_iff R K W x y).mp h`
     with `((WeierstrassCurve.Affine.equation_iff x y).mp h)` after a local `simp [curveK]` (or
     `simp only [curveK_a₁, curveK_a₃, …]`) to normalise `(curveK R K W).aᵢ` to `algebraMap R K W.aᵢ`.
     Note the argument-order difference: the mathlib lemma is `W.equation_iff x y` (curve via dot
     notation, coordinates positional), whereas the wrapper threads `R K W` explicitly.
  2. **Keep as a one-line local convenience but mark it as such** (acceptable under AINTLIB's
     WIP-tolerant `main`, but it must NOT be proposed to mathlib): the 6 consumers all use the `.mp`
     direction with the mapped-coefficient RHS, so a private/`local` helper is defensible for
     ergonomics. This is a project-policy call, not a mathlib contribution.
Either way: **do not** open a mathlib PR for `curveK_equation_iff` — mathlib has the general lemma.
(Coordinate this with `curveQ_equation_iff`: they are the same wrapper at two base rings; if the
project keeps one local convenience it may want to keep/drop both consistently, or collapse both onto
`equation_iff` directly.)

Next action: do **not** submit to mathlib. On the dev branch, optionally inline the 6 call sites onto
`WeierstrassCurve.Affine.equation_iff` (+ `simp [curveK]`) and delete the wrapper; or retain it as an
explicitly-local convenience. No upstreaming.

---

## Next step

Do not submit `curveK_equation_iff` to mathlib: it is the `R := K`, `W := W.map (algebraMap R K)`
specialisation of the existing `WeierstrassCurve.Affine.equation_iff`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`), with coefficients rewritten by the
existing `WeierstrassCurve.map_aᵢ` simp lemmas. Inline at the 6 call sites
(`PIDMain.lean:257`; `PIDPrimeOrder.lean:132,168,171,211`; `PIDIntegralMultiple.lean:90`) via
`rw [WeierstrassCurve.Affine.equation_iff]; simp [curveK]` and delete, or keep it as an explicitly
project-local convenience — but not as a mathlib contribution. Mirrors the `curveQ_equation_iff`
disposition exactly (same wrapper, base ring `K` instead of `ℚ`).

---

### Sources (Phase 3 literature)
- [Elliptic Curves — The Weierstrass Form (Stanford)](https://crypto.stanford.edu/pbc/notes/elliptic/weier.html)
- [Elliptic curve — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_curve)
- [Weierstrass equations — Elliptic Curves class notes (Fiveable)](https://fiveable.me/elliptic-curves/unit-1/weierstrass-equations/study-guide/K4io7LyS88PG9nEF)
- [Elliptic-curve cryptography V: Weierstrass curves (Lange)](https://hyperelliptic.org/tanja/teaching/crypto21/ecc-5.pdf)
- [The Basic Theory — Weierstrass Equations (UCSB ch.2)](http://koclab.cs.ucsb.edu/teaching/ccs130h/2013/chap2.pdf)
- [Nagell–Lutz, quickly (Alpoge, Harvard)](https://people.math.harvard.edu/~alpoge/papers/nagell-lutz,%20quickly.pdf)
- [Nagell–Lutz Theorem for Imaginary Quadratic Fields (arXiv:2509.07524)](https://arxiv.org/pdf/2509.07524)
- [On the Classification of Weierstrass Elliptic Curves over ℤ_n (arXiv:2310.11768)](https://arxiv.org/pdf/2310.11768)
- [Using Selmer Groups to compute Mordell–Weil Groups (arXiv:1812.10415)](https://arxiv.org/pdf/1812.10415)
