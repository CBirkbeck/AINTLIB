# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.smulPoly`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration.

## Baseline (Phase 0)

- lake build:               ⚠ NOT RUN — local build is stale (per task brief). Assessment
                            reasons from source + grep over the vendored mathlib
                            (`.lake/packages/mathlib`, pin `rev 09b373db6e24`, toolchain
                            `v4.32.0-rc1`). The decl is a 1-line `abbrev`, so its elaborated
                            type is unambiguous from source.
- decl `WeierstrassCurve.Universal.Jacobian.smulPoly`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:414`
- qualified name:           ✓ VERIFIED. Namespace nesting in the file is
                            `WeierstrassCurve` (76) → `Universal` (86) → `Jacobian` (395);
                            decl at 414 is inside all three.
                            ⇒ `WeierstrassCurve.Universal.Jacobian.smulPoly` (matches the
                            parsed name in the brief).
- kind:                     `abbrev` (a one-line definition)
- has sorry:                no
- module docstring summary: `ZSMul.lean` proves `WeierstrassCurve.zsmul_eq_smulEval`:
                            `n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coordinates for any integer
                            `n` and nonsingular affine point `P = (x,y)` on a Weierstrass
                            curve over a field. Strategy: reduce to a *universal* polynomial
                            identity over `ℤ[A₁..A₆][X][Y]`, then specialise.

### Project-fork context (load-bearing)

This project (and `HasseWeil`) **fork** mathlib's division-polynomial stack:

- `LutzNagell/DivisionPolynomial.lean` is, per its own header, *"a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
  `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name
  conflicts (both define `normEDS`, `complEDS`, etc.)."* The project's `φ`, `ψ` are byte-for-byte
  mathlib's (verified: `φ := C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)` in both).
- `LutzNagell/DivisionPolynomialOmega.lean` defines `WeierstrassCurve.ω` — **which mathlib does
  not have** (mathlib `DivisionPolynomial/Basic.lean` lists it under "Main definitions" as
  `* TODO: the bivariate polynomials ωₙ.` and again `TODO: implementation notes for ωₙ`).

So `smulPoly` sits on top of one component (`ω`) that is *not in mathlib*.

---

## Statement (Phase 1)

`smulPoly` is the definition:

```lean
/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
```

In words: for an integer `n`, `smulPoly n` is the ordered triple `(φₙ, ωₙ, ψₙ)` of division
polynomials **of the universal Weierstrass curve** `curve`, packaged as a `Fin 3 → Poly` vector.
These three polynomials are exactly the **Jacobian (weighted-projective, weights 2/3/1)
coordinates of `n • P`**: classically `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` in affine coordinates, i.e.
`[n]P = ⟦(φₙ, ωₙ, ψₙ)⟧` in Jacobian coordinates `[X : Y : Z]`. `smulPoly n` is the polynomial-ring
representative of that Jacobian point on the *universal* curve.

Here:
- `curve : Affine (MvPolynomial Coeff ℤ)` — the **universal Weierstrass curve** over
  `ℤ[A₁,A₂,A₃,A₄,A₆]` (`Universal.lean:84`).
- `Poly := (MvPolynomial Coeff ℤ)[X][Y]` — the universal bivariate polynomial ring
  `ℤ[A₁..A₆][X][Y]` (`Universal.lean:94`).
- `curve.φ`, `curve.ω`, `curve.ψ : ℤ → Poly` — the division-polynomial families of `curve`.
- `Fin 3 → _` is mathlib's representation of Jacobian points (`Mathlib/.../Jacobian/Point.lean`
  uses `Fin 3 → R` with `x = 0`, `y = 1`, `z = 2`).

Variables / typeclasses (Lean side):
- `n : ℤ` — the multiplier (explicit argument). No typeclass arguments; the curve and ring are
  fixed to the universal ones.

Hypotheses: none.

Conclusion (math): the Jacobian-coordinate triple `(φₙ, ωₙ, ψₙ)` of `n • P` on the universal curve.

Conclusion (Lean): `Fin 3 → Poly` (a definition; no proof obligation).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a 1-line `abbrev` bundling three already-named objects into a tuple. Not a new
mathematical structure, not a named-after-a-person theorem, not a `## Main results` entry (the
file's main result is `zsmul_eq_smulEval`; `smulPoly` is plumbing toward it). It is genuine API
*support* but it is not itself a headline object.

(Literature width was run EXHAUSTIVE regardless — see Phase 3.)

## One-line check (Phase 2b)

Body line count: **1 substantive line** (`![curve.φ n, curve.ω n, curve.ψ n]`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

Exemption check:

| Exemption                        | Applies? | Evidence                                                                                   |
|----------------------------------|----------|--------------------------------------------------------------------------------------------|
| Avoid defeq abuse                | no       | It is an `abbrev` (semireducible/reducible-ish) and is *routinely unfolded* by callers — `dblZ_smulPoly`, `addZ_smulPoly`, `smulPoly_neg`, `zsmul_point_eq_smulField` all `unfold smulPoly` / `simp [smulPoly]`. It is a notation convenience, not a defeq barrier (a barrier would be a sealed `def`). |
| Avoid typeclass diamonds         | no       | No instance resolution rides on it; it is a plain data tuple in a fixed ring.              |
| Mark semantic intent / API name  | partial  | It *does* carry a docstring and a meaningful name, and downstream defs (`smulRing`, `smulField`) are literally `… ∘ smulPoly n`. But the name is **project-internal**: it is never imported by another file (see Phase 6.0), so the "stable API anchor for consumers" rationale is weak — its only consumers are 15 lines in the same file. |

Conclusion: **ONE-LINER WITH (weak) PARTIAL EXEMPTION** — carried into Phase 7. Because the
def's content depends on `ω` (a mathlib gap), the one-liner question is *secondary*: even with a
strong exemption, `smulPoly` cannot ship to mathlib ahead of `ω`. The one-liner status reinforces
that, *on its own merits*, `smulPoly` is a thin convenience that would naturally ride along with
the `ω`/multiplication-formula contribution rather than stand alone.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomials φ ω ψ, Jacobian coords, `[n]P` multiplication-by-n formula                          | yes  | `[n]P = [φₙψₙ : ωₙ : ψₙ³]` (Jacobian); affine `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` | MIT 18.783 Sutherland Lec #6; arXiv 1103.4560, 1108.3051; eprint 2010/630 |
|  2 | WebSearch (general form)         | "division polynomial" elliptic curve omega psi phi projective coords scalar multiple Silverman          | yes  | same triple; Silverman *Arithmetic of Elliptic Curves* is the canonical reference | confirms `(φ, ω, ψ)` triple is *the* mult-by-n statement |
|  3 | WebSearch (named-after / aliases)| EDS / division polynomial triple "named" canonical object weighted projective Jacobian nLab             | yes  | `n·(x,y) = (φₙ/ψₙ², ωₙ/ψₙ³)`; **no special name for the tuple** | Wikipedia EDS; arXiv 2503.15428 (isogenies); the *triple itself* is unnamed |
|  4 | ChatGPT MCP                      | is `(φ,ω,ψ)` a named object? generality? merits its own Lean def?                                        | n/a  | —                                                     | **MCP/Codex down** in this env (errored, as brief warned). Compensated by extra WebSearch breadth (#1–3) + direct mathlib-source read. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                  | n/a  | —                                                     | directory absent; `refs/` store also absent. Recorded n/a. |
|  6 | nLab                             | division polynomial / EDS triple                                                                        | n/a  | no dedicated nLab page for the tuple                  | EDS/division polynomials are classical NT, not an nLab categorical topic; checked via #3, nothing. |
|  7 | nCatLab (categorical)            | —                                                                                                       | n/a  | —                                                     | not a categorical concept. |
|  8 | Stacks Project (alg geom)        | —                                                                                                       | n/a  | —                                                     | Stacks does not cover explicit division-polynomial formulas. |
|  9 | MathOverflow / MSE               | division polynomial omega / mult-by-n projective                                                        | yes  | reaffirms the affine/projective triple; no naming    | folded into #1–3 results. |
| 10 | recent arXiv (≤5 yr)             | division polynomials for arbitrary isogenies (2503.15428); EDS surveys                                  | yes  | uses `φ, ψ, ω` componentwise; triple still unnamed    | modern work still treats them as three separate families. |

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` map on an elliptic curve expressed via
division polynomials** — `[n]P = (φₙ(P)/ψₙ(P)², ωₙ(P)/ψₙ(P)³)` affine, equivalently the Jacobian
representative `(φₙ, ωₙ, ψₙ)`.

Sources agree on the standard form: **yes**. The triple `(φₙ, ωₙ, ψₙ)` is the universally-used
ingredient list for the multiplication-by-n formula (Silverman Ch. III/Ex.; Sutherland 18.783;
Washington; Lang).

Most general standard form: stated for a general Weierstrass curve / over the universal ring
`ℤ[a₁..a₆][X,Y]` (so that it specialises to every base). Mathlib's own `ω` TODO note literally
frames `ωₙ` via the *"characteristic-0 universal ring `𝓡[X,Y] := ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]`"* — i.e.
exactly this project's `Poly`.

Generality dimensions where the literature varies:
  - **Base form**: short Weierstrass `y²=x³+Ax+B` (most pedagogical sources) ↔ general Weierstrass
    `a₁..a₆` (Silverman, mathlib). The general form is standard and strictly more general.
  - **Component naming**: always three separately-named polynomials `ψₙ` (primary), `φₙ`, `ωₙ`
    (associates). The **bundled tuple is NOT a named object** in any source — it is the natural
    ad-hoc packaging of the three for the projective statement.

Disagreement with the literature: none on content. The only "gap" vs. literature is presentational:
the literature names the three polynomials, not the triple.

---

## Generality analysis — `smulPoly` (Phase 4)

Literature-standard form (from Phase 3): the division polynomials `φₙ, ωₙ, ψₙ` of a **general**
Weierstrass curve `W` (over any commutative ring), and the multiplication-by-n triple `(φₙ, ωₙ, ψₙ)`.

| # | Parameter / hypothesis      | Current Lean form                              | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|------------------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | the curve                   | hard-wired to `curve : Affine (MvPolynomial Coeff ℤ)` (the **universal** curve) | any `W : WeierstrassCurve R`, `[CommRing R]` | **yes** | `W.φ`, `W.ω`, `W.ψ` are *already* defined for arbitrary `W` (verified: `protected def ψ/φ/ω` take a general `W`). The universal restriction here is a *proof-technique* specialisation, not a content restriction. The mathlib-natural form is `W.smulPoly (n) : Fin 3 → R[X][Y] := ![W.φ n, W.ω n, W.ψ n]`. |
| 2 | the polynomial ring         | hard-wired `Poly = ℤ[A₁..A₆][X][Y]`           | `R[X][Y]` for the curve's base `R`     | yes (follows from #1) | purely a consequence of fixing the curve to universal. |
| 3 | the index `n`               | `n : ℤ`                                        | `n : ℤ`                                | NO                  | already the right index type (division polynomials are a ℤ-indexed family). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (specialised to the universal curve).
Number of weakening opportunities found: 1 (genuine; #2 is a corollary of #1).

Proposed restatement (the mathlib-natural form):

```lean
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The Jacobian coordinates `(φₙ, ωₙ, ψₙ)` of `n • P` via the division polynomials of `W`. -/
noncomputable def divisionPolynomialTriple (n : ℤ) : Fin 3 → R[X][Y] :=
  ![W.φ n, W.ω n, W.ψ n]
```

Cost of restatement: **CHEAP** — mechanical (the body is identical; only the curve becomes a
parameter). BUT this is moot until `W.ω` exists in mathlib (Phase 5).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Downstream |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let W be the universal curve" preamble → typeclass / parameter?                                  | yes      | parametrise over `W` (see 4b) | every Weierstrass curve gets the triple; the universal one is then `Universal.curve.divisionPolynomialTriple` | 
|  2 | sequences/metric → filters/topology?                                                              | no       | purely algebraic; no topology. |
|  3 | explicit construction → universal-property class?                                                 | no       | division polynomials are an explicit recursive construction; no UP to abstract. |
|  4 | set-with-closure-predicate → bundled substructure?                                                | no       | n/a. |
|  5 | vector-space/field-specific → weaken typeclass?                                                   | yes (already general) | `W.φ/ω/ψ` are over any `[CommRing R]`; the triple inherits that — *if* parametrised. |
|  6 | 1-categorical → higher-categorical?                                                               | no       | n/a. |
|  7 | concrete index ℕ/ℤ/ℝ → general monoid/group?                                                      | no       | `n : ℤ` is intrinsic (mult-by-n for `n ∈ ℤ`). |
|  8 | (concrete-via-abstract / proof betrays the right form) — is this a `def`, so n/a for proof-grep   | n/a      | it's a `def`; nothing to grep. |

Modern-idiom verdict (Phase 4c): a modern idiom **is** available, and it is the *same* move as 4b
(parametrise over `W` instead of hard-wiring the universal curve). Real improvement: the triple
then specialises to *every* Weierstrass curve over any commutative ring, matching how `W.φ/ω/ψ`
are already stated. Cost: CHEAP. Downstream: a general `W.divisionPolynomialTriple` is what the
mathlib multiplication-by-n formula (currently absent) would be phrased against.

**Caveat that dominates everything:** the generalised target still depends on `W.ω`, which mathlib
does not have (it's a TODO). So the "generalise first" target cannot be realised in mathlib without
*first* contributing `ω` and the multiplication-by-n machinery. This pushes the verdict away from a
clean YES-but-generalise toward a borderline/dependency call — see Phase 7.

---

## Diamond / defeq risk (Phase 4.5) — `def`/`abbrev`

| # | Risk                          | Verdict | Evidence / rationale                                                                              |
|---|-------------------------------|---------|---------------------------------------------------------------------------------------------------|
| 1 | Typeclass diamond            | none    | plain data (`Fin 3 → Poly`); no instances created or selected.                                    |
| 2 | Reducibility leak            | low     | it's an `abbrev` (reducible), so its body *is* exposed to defeq. In-project that's intended (callers unfold it). For mathlib one would likely make the general version a sealed `def`, not `abbrev`, to avoid surprising `simp`/`rfl` unfolds of a 3-vector. Minor, easily handled. |
| 3 | Non-canonical unfolding      | low     | `![…]` matrix-vector unfolding via `Matrix.cons_val_*` is routine; no surprise.                   |
| 4 | Instance priority collision  | n/a     | not an instance.                                                                                   |
| 5 | Universe-polymorphism issues | none    | fixed concrete types; the generalised form would be `R[X][Y]` over a single universe of `R`.      |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort`.                                                                             |

Risk verdict (Phase 4.5): **LOW** (only the `abbrev`-vs-`def` reducibility nuance; trivially
mitigated by shipping the general form as a sealed `def`). No HIGH rows.

---

## Mathlib search-status: `smulPoly` (Phase 5)

Mathlib pin grepped: `.lake/packages/mathlib` @ `rev 09b373db6e24`, toolchain `v4.32.0-rc1`.

```
[A] Lean-Finder       n/a — tool not exposed in this harness (only LSP available; build stale).
[B] Loogle            n/a — lean_loogle not exposed in this harness.
[C] LeanSearch        n/a — lean_leansearch not exposed in this harness.
[D] Grep mathlib src  RAN (authoritative): see findings below — this is the decisive method here.
[E] Name pattern      RAN via grep: `smulPoly`, `smulField`, `smulRing`, `smulEval`,
                      `zsmul_point`, `Fin 3 → …[X][Y]`, `ω`/`omega` in EllipticCurve/* — no hits
                      for the tuple, the mult-by-n formula, or `ω`.
```

Searched for **both** forms (universal `smulPoly` and the general `W.divisionPolynomialTriple`).

Findings from Method D (mathlib source, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`):

- **Building blocks present:** `WeierstrassCurve.ψ` (line 401), `WeierstrassCurve.φ` (line 448),
  plus `ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, preΨ, ΨSq, Ψ, Φ`. The "Main definitions" docstring lists exactly these.
- **`ω` is ABSENT — and explicitly flagged missing.** "Main definitions" ends with
  `* TODO: the bivariate polynomials ωₙ.` and Implementation notes add `TODO: implementation notes
  for the definition of ωₙ.` So one of `smulPoly`'s three components is a *known mathlib gap*.
- **No multiplication-by-n-via-division-polynomials formula in mathlib at all.** Grep for
  `zsmul_point` / `smulField` / `smul…ψ` / a Jacobian division-polynomial point returned nothing
  across `Mathlib/AlgebraicGeometry/EllipticCurve/`. The theorem `smulPoly` exists to support
  (`zsmul_point_eq_smulField`, ultimately `zsmul_eq_smulEval`) is itself not in mathlib.
- **No `Fin 3` division-polynomial tuple anywhere** in mathlib (`smul`+`φ` grep over all of mathlib
  hit only unrelated topology/germ lemmas).

Concluded: **not in mathlib** — neither `smulPoly` nor the general `W.divisionPolynomialTriple`,
and crucially neither its `ω` component nor the mult-by-n formula it serves. Mathlib has only the
`φ`/`ψ` building blocks; `ω` is an open TODO.

> Method-coverage note: A/B/C (the semantic indices) are unavailable in this harness, but Method D
> (direct source grep) **plus** mathlib's author-maintained "Main definitions / TODO" list is the
> strongest possible evidence for the "is this exact decl in mathlib" question — and it is
> unambiguous here. The unavailability does not weaken the conclusion.

---

## Composition check + call sites (Phase 6)

### 6.0 Call sites — `smulPoly`

Internal use count (NagellLutz, excluding the declaring line): **~15 uses, all within
`ZSMul.lean` itself.**
External-to-file callers **in NagellLutz**: **0 files** (it never escapes `ZSMul.lean`).

| Caller file:line                 | Usage pattern (one-line excerpt)                                              |
|----------------------------------|-------------------------------------------------------------------------------|
| ZSMul.lean:416                   | `abbrev smulRing (n) := AdjoinRoot.mk _ ∘ smulPoly n`                          |
| ZSMul.lean:418                   | `abbrev smulField (n) := polyToField ∘ smulPoly n`                            |
| ZSMul.lean:425                   | `rw [… , smulField, smulPoly]` (in `zsmul_point_eq_smulField`)                 |
| ZSMul.lean:437–438               | `lemma dblZ_smulPoly … unfold dblZ smulPoly …`                                |
| ZSMul.lean:462,467               | `simp only [… smulField, smulPoly …]`                                          |
| ZSMul.lean:475–476               | `lemma addZ_smulPoly … simp_rw [addZ, smulPoly, φ]`                           |
| ZSMul.lean:480–481,487–488,496   | `ω_neg_eq_neg_negY`, `smulPoly_neg`, `smulPoly_zero` (all unfold/`simp [smulPoly]`) |
| ZSMul.lean:559                   | `rw [… ← smulPoly, ← coe_evalEvalRingHom …]` (toward `zsmul_eq_smulEval`)      |

Inline-derivation grep (re-derived elsewhere without using `smulPoly`?):
  - **YES — duplicated verbatim in another project.**
    `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:480` defines an *identical*
    `abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]`, with the same
    satellite lemmas (`smulPoly_neg`, `dblZ_smulPoly`, `ω_neg_eq_neg_negY`, …). This is the
    "duplicated General*/PID* tracks" the brief flagged: the whole universal-curve
    division-polynomial file (Junyan Xu's) has been **copied** into two projects, not shared.

### 6.0.1 What the call-sites pattern says

`K ≥ 3` internal uses (heavy) **but** confined to one file, no external NagellLutz consumers, and
the *same def copied wholesale into a second project*. Signal: this is **genuinely reusable
infrastructure that is currently duplicated** rather than shared — a textbook case for hoisting to
a single canonical home. The natural canonical home is mathlib (next to `φ`/`ψ`/the `ω` TODO);
the second-best is an AINTLIB `Common/` module. It is *not* dead code, and *not* a one-off wrapper
that consumers bypass — its consumers just all live beside it (×2 projects).

### 6a. Composition attempt

Can `smulPoly` be derived from mathlib in ≤3 chained calls? **No** — not because it is deep, but
because it *names a value mathlib cannot express*: `curve.ω n` has no mathlib counterpart (`ω` is a
TODO). The body `![curve.φ n, curve.ω n, curve.ψ n]` would inline to `![curve.φ n, ⟨MISSING⟩, curve.ψ n]`.
So:

- Attempt 1: `![W.φ n, W.ω n, W.ψ n]` using mathlib `φ`/`ψ` + (missing) `ω`.
  - Mathlib decls used: `WeierstrassCurve.φ`, `WeierstrassCurve.ψ`. **`ω` unavailable.**
  - Result: **fails** — one of three components is absent from mathlib.

Conclusion: **NOT-COMPOSABLE** (blocked by the missing `ω`, not by proof depth). Once `ω` lands in
mathlib, the *tuple* would become a trivial `![W.φ n, W.ω n, W.ψ n]` — a candidate one-liner to
inline, OR a thin named convenience to ship alongside the mult-by-n formula.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.smulPoly`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the triple `(φₙ, ωₙ, ψₙ)` is the standard mult-by-n ingredient
  (Silverman, Sutherland 18.783), but is **not a named object** — the three components are named,
  the bundle is ad hoc.
- Generality analysis (Phase 4): **STRICTLY NARROWER** — hard-wired to the universal curve;
  natural mathlib form parametrises over a general `W` (CHEAP), but that target depends on `ω`.
- Mathlib search (Phase 5): **not in mathlib**; building blocks `φ`,`ψ` present, **`ω` is an
  explicit mathlib TODO**, and the whole mult-by-n formula is absent.
- Composition check (Phase 6): **NOT-COMPOSABLE** — blocked by the missing `ω`; heavy in-file use
  (~15×) and **duplicated verbatim in HasseWeil**, so it is reusable-but-duplicated infrastructure.

**Rationale:**

`smulPoly` is a 1-line `abbrev` that bundles `(φₙ, ωₙ, ψₙ)` — the Jacobian coordinates of `n • P`
— for the universal curve. On content it is squarely standard mathematics, and it is genuine API
(15 in-file uses; copied into a second project). But three facts make a clean verdict impossible
for the skill to pick alone, and all three are *judgment calls*, not search gaps:

1. **It is downstream of a mathlib gap.** Its `ω` component is a mathlib TODO. You cannot upstream
   `smulPoly` "as-is"; you would first upstream `ω` + the multiplication-by-n machinery
   (`zsmul_eq_smulEval` and its universal-ring proof — a substantial, genuinely-wanted contribution
   that mathlib's own TODOs invite). `smulPoly` only makes sense *as a rider on that larger PR*.
   Whether to treat this 1-liner as in-scope for that contribution is a packaging decision.

2. **The bundle is unnamed in the literature and is a one-liner.** Once `ω` exists, `![W.φ n,
   W.ω n, W.ψ n]` is a trivial inline tuple. Mathlib might want it as a named
   `divisionPolynomialTriple` (semantic anchor for the mult-by-n formula and the
   `addZ`/`dblZ`/`neg` satellite lemmas that are stated *about* it), or might prefer to inline it
   and keep only the satellite lemmas. That is exactly the "is a named one-liner worth it" taste
   call the skill must not make unilaterally — especially as the only current consumers are the
   author's own two copied files.

3. **The right home might be AINTLIB `Common/`, not mathlib (yet).** The decl is duplicated
   verbatim across NagellLutz and HasseWeil. The *immediate* correct refactor is to de-duplicate
   (one shared copy), independent of the slower mathlib question. The cleanup fleet can do that
   today; mathlib upstreaming waits on `ω`.

A cost factor is present (the general form's proof needs `ω`'s whole machinery), and per the
skill's own rule, "the general form is expensive because it needs new mathlib infrastructure" is a
BORDERLINE question to the user, not a self-resolving downgrade. Hence BORDERLINE.

**Numbered questions (≤5):**

1. **Packaging:** Do you intend to upstream `WeierstrassCurve.ω` + the multiplication-by-n formula
   (`zsmul_eq_smulEval`) to mathlib (mathlib lists `ωₙ` as an open TODO)? If **yes**, `smulPoly`
   should be re-assessed *as part of that PR* — likely shipped as a general
   `W.divisionPolynomialTriple` (or inlined). If **no**, `smulPoly` stays project-local and the
   only action is de-duplication (Q3).
2. **Named tuple vs. inline:** In the mathlib form, do you want the triple as a *named* def
   (`divisionPolynomialTriple`, a stable anchor for the `dblZ`/`addZ`/`neg`/`zero` satellite
   lemmas), or inlined as `![W.φ n, W.ω n, W.ψ n]` with only the satellite lemmas named? (This is
   the one-liner taste call.)
3. **De-duplication now:** NagellLutz and HasseWeil contain *identical* `smulPoly` (+ satellites).
   Should this be hoisted into a shared AINTLIB `Common/` module immediately (a pure dedup, no
   maths), regardless of the mathlib timeline?
4. **Generality:** If/when upstreamed, confirm the target is the general
   `W : WeierstrassCurve R` form (not the universal-curve specialisation) — the universal
   restriction here is only a proof device; `W.φ/ω/ψ` are already general.

**Next action:** answer Q1–Q4 and re-run `/mathlibable` (with the answers as Phase-1 input), OR —
the pragmatic path — (a) file an AINTLIB dev ticket to de-duplicate `smulPoly` across NagellLutz /
HasseWeil into `Common/` now (Q3), and (b) defer the mathlib question to whenever `ω` +
`zsmul_eq_smulEval` are upstreamed, at which point `smulPoly` rides along as a general
`divisionPolynomialTriple` or is inlined per Q2.

---

## Next step

File the de-dup dev ticket (NagellLutz + HasseWeil `smulPoly` → shared `Common/`) and answer
Q1–Q4 above. Mathlib upstreaming of `smulPoly` is gated on first contributing `WeierstrassCurve.ω`
(an explicit mathlib TODO) and the multiplication-by-n formula it supports; treat `smulPoly` as a
rider on that contribution, generalised to an arbitrary `W` or inlined.

Sources (Phase 3): MIT 18.783 (Sutherland) Lecture #6 division polynomials; Silverman, *The
Arithmetic of Elliptic Curves*; Wikipedia "Elliptic divisibility sequence"; arXiv 1103.4560,
1108.3051, 2503.15428; eprint 2010/630.
