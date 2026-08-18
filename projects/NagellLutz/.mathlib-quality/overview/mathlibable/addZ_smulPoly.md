# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.addZ_smulPoly`

**Verdict (one line):** BORDERLINE-needs-human — genuinely-new content (mathlib lacks the
`WeierstrassCurve.Universal` construction and the multiplication-by-`n` division-polynomial
formula), but `addZ_smulPoly` is an *internal bridge lemma* inside an in-flight upstreaming
track by the original mathlib author (Junyan Xu). It ships as part of that file, not as a
standalone PR; whether to carve it out is a human call.

---

### Baseline (Phase 0)
- lake build:               ⚠ not run — local build is stale per task instructions; reasoning is
                            from source. The decl elaborates in the committed file (no `sorry`).
- decl `WeierstrassCurve.Universal.Jacobian.addZ_smulPoly`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:475`
- qualified name:           VERIFIED — namespaces nest `WeierstrassCurve` (L76) → `Universal`
                            (L86) → `Jacobian` (L395); decl at L475 is inside all three.
- kind:                     `lemma` (theorem-kind; Phase 4.5 diamond/defeq is n/a)
- has sorry:                no (3-line tactic proof)
- module docstring summary: Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ:ωₙ:ψₙ)`
                            in Jacobian coordinates, via the universal Weierstrass curve.

**Duplication note (cross-project):** an identical `private lemma addZ_smulPoly` exists at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:560` (same statement, same proof).
This lemma is fork-duplicated across two AINTLIB projects — a dedup signal for the on-`main`
cleanup fleet, independent of the mathlib question.

---

### Statement (Phase 1)

`addZ_smulPoly` states the following polynomial identity in the universal coefficient ring
`Poly = ℤ[a₁..a₆][X][Y]` (here `curve` is the universal Weierstrass curve):

> For all integers `m, n`,
> `addZ (smulPoly m) (smulPoly n) = ψ_{n+m} · ψ_{n-m}`,
> where `smulPoly k = (φ_k, ω_k, ψ_k)` is the triple of division polynomials giving the
> multiplication-by-`k` map in Jacobian coordinates, and `addZ` is mathlib's generic
> Jacobian-group-law Z-coordinate, `addZ P Q := P_x · Q_z² − Q_x · P_z²`.

Unfolding: `addZ (smulPoly m)(smulPoly n) = φ_m·ψ_n² − φ_n·ψ_m²`. With the standard
`φ_k = X·ψ_k² − ψ_{k+1}·ψ_{k-1}`, the `X·ψ_m²ψ_n²` terms cancel, leaving
`ψ_{n+1}ψ_{n-1}ψ_m² − ψ_{m+1}ψ_{m-1}ψ_n²`, which the elliptic-sequence three-term recurrence
(with `r = 1`, using `ψ_1 = 1`) collapses to `ψ_{n+m}·ψ_{n-m}`. The proof is exactly this:
`simp_rw [addZ, smulPoly, φ]; convert (curve.isEllSequence_ψ n m 1).symm using 1` + two `ring`s.

Variables / typeclasses (Lean side):
- `curve : WeierstrassCurve Universal.Ring₀` — the *universal* Weierstrass curve over
  `ℤ[a₁,a₂,a₃,a₄,a₆]`. Not a generic `[CommRing R]` curve: this is one fixed object.
- `m n : ℤ` — the two multiplier indices.

Hypotheses: none.

Conclusion (math): the Jacobian addition Z-coordinate of the `m`- and `n`-multiplication
representatives equals `ψ_{n+m}ψ_{n-m}`.
Conclusion (Lean): `addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m)` in `Poly`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — a specific algebraic identity bridging mathlib's `addZ` to the
division-polynomial recurrence on one fixed (universal) curve. Not a `def`/`class`, not a
person-named theorem, not a `## Main results` entry (the main result is `zsmul_eq_smulEval`).

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line definition check is **n/a**.
(The proof body is 3 tactic lines; this is a theorem-kind decl, so 2b does not gate the verdict.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS recurrence ψ(n+m)ψ(n−m) division polynomial Jacobian Z-coordinate addition formula                 | yes  | `h_{m+n}h_{m-n}=h_{m+1}h_{m-1}h_n²−h_{n+1}h_{n-1}h_m²` | Ward's EDS recurrence; division-poly recurrence `ψ_{m+n}ψ_{m-n}=ψ_{m+1}ψ_{m-1}ψ_n²−ψ_{n+1}ψ_{n-1}ψ_m²` is textbook |
|  2 | WebSearch (φ-form / general)     | `ψ_{m+n}ψ_{m-n} = φ_m ψ_n² − φ_n ψ_m²` elliptic curve identity                                          | partial | recurrence + `φ_m = xψ_m²−ψ_{m+1}ψ_{m-1}` both standard | exact `φ_mψ_n²−φ_nψ_m²` packaging not a *named* identity; it is the recurrence rewritten with φ |
|  3 | WebSearch (named-after / EDS)    | nLab/Somos elliptic divisibility sequence division polynomial recurrence Ward                           | yes  | general `h_{m+n}h_{m-n}h_r²=h_{m+r}h_{m-r}h_n²−h_{n+r}h_{n-r}h_m²` | confirmed Ward; Somos-4 generalisation; arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" |
|  4 | ChatGPT MCP                      | self-contained Q on whether `addZ(smulPoly)` identity is named + most-general ring setting              | n/a  | —                                | MCP returned a Codex error (down, as task warned); fell back to channels 1–3,6,9,10 |
|  5 | Local references                 | `.mathlib-quality/references/`                                                                          | n/a  | (directory absent)               | no references dir under `projects/NagellLutz/.mathlib-quality/` |
|  6 | nLab                             | elliptic divisibility sequence / division polynomial                                                    | n/a  | (no dedicated nLab page surfaced)| EDS/division-poly recurrence is not an nLab-style categorical concept; recorded n/a-with-reason |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | Stacks has no division-polynomial / EDS material; not the right corpus |
|  9 | MathOverflow / Math.SE           | division polynomial recurrence generality commutative ring                                             | yes  | recurrence holds as polynomial identity over `ℤ[a_i][x,y]` | confirmed it is a universal polynomial identity, base-ring agnostic |
| 10 | recent arXiv (last 5y)           | division polynomials arbitrary isogenies; elliptic sequences over commutative rings                    | yes  | Stange 2025; arXiv 2604.05280, 2503.15428 | modern treatments keep the same recurrence; nothing changes the form |

Protocol status: WebSearch ran ≥3 queries at different generality levels ✓; local refs checked
(absent) ✓; nLab checked (n/a-reason) ✓; Stacks/MathOverflow/arXiv each checked ✓. ChatGPT MCP
attempted but the server errored — fallback channels cover the same ground (the standard form and
its generality were established independently).

### Literature summary (Phase 3)

Concept identified as: the **elliptic-(divisibility-)sequence three-term recurrence** for division
polynomials, `ψ_{m+n}ψ_{m-n}ψ_r² = ψ_{m+r}ψ_{m-r}ψ_n² − ψ_{n+r}ψ_{n-r}ψ_m²` (Ward), here used at
`r = 1`. `addZ_smulPoly` is this recurrence repackaged through `φ_k = Xψ_k² − ψ_{k+1}ψ_{k-1}` and
mathlib's Jacobian `addZ`.

Sources agree on the standard form: **yes** — the recurrence is textbook (Silverman; Ward;
multiple arXiv). It holds as a **universal polynomial identity over any commutative ring**, which
is precisely how mathlib already states it: `IsEllSequence` (`Mathlib/NumberTheory/
EllipticDivisibilitySequence.lean:82`) and `IsEllSequence.normEDS`.

Most general standard form: the recurrence over an arbitrary commutative base ring.

Disagreement with the literature: none. The lemma is mathematically the well-known recurrence;
the *novelty* is purely the bridge — phrasing one instance of it as a statement about mathlib's
`addZ` applied to the universal multiplication-formula triples `smulPoly k`. That bridge is an
artifact of *this formalisation's induction strategy* (prove `zsmul_eq_smulEval` by even-odd
induction; reduce the odd step to `addXYZ_smulField`; the Z-coordinate part is `addZ_smulPoly`).
It is **not** a named result in the mathematics literature.

---

### Generality analysis — `addZ_smulPoly`

Literature-standard form (Phase 3): the EDS recurrence over an arbitrary commutative ring,
already in mathlib as `IsEllSequence` / `IsEllSequence.normEDS`.

| # | Parameter / hypothesis        | Current Lean form                    | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `curve` (the base curve)      | the **fixed universal** curve over `ℤ[a₁..a₆]` | any `W : WeierstrassCurve R`, any `[CommRing R]` | yes (in principle) | The identity is a universal polynomial identity → it specialises to every `W`/`R` via `map_ψ`, `map_φ`, `map_addZ`. But this lemma is *deliberately* on the universal curve because the whole file's strategy is "prove it once universally, then specialise." |
| 2 | indices `m n`                 | `ℤ`                                  | `ℤ`                              | NO                  | already maximally general for the index |
| 3 | the recurrence `r`            | hard-wired `r = 1`                   | arbitrary `r` (general recurrence)| n/a here            | `addZ_smulPoly` is intrinsically the `r=1` slice (that is what `φ` packages); the general-`r` statement is just `isEllSequence_ψ` itself, which the project already has |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** along dimension #1 (it is on the one
fixed universal curve, not a general `W : WeierstrassCurve R`). However this narrowness is
*structural, not accidental*: the universal curve is the device by which a single proof yields
the result for all curves. A "more general" `addZ_smulPoly` over arbitrary `W` would be a
**different lemma** (`addZ (W.smulPoly m) (W.smulPoly n) = W.ψ(n+m)·W.ψ(n-m)`), provable from this
one by `map_addZ` + `map_ψ`. The right mathlib decl, if upstreamed, is almost certainly the
general-`W` version (the universal one is the engine, the general one is the user-facing result).

Number of weakening opportunities: 1 (curve → arbitrary `W`/`R`).
Proposed restatement (general-`W` form):
```lean
lemma WeierstrassCurve.addZ_smulPoly {R} [CommRing R] (W : WeierstrassCurve R) (m n : ℤ) :
    Jacobian.addZ (W.smulPoly m) (W.smulPoly n) = W.ψ (n + m) * W.ψ (n - m) := …
```
Cost of restatement: **CHEAP** (mechanical: it is the image of this identity under `map_*`; or a
1–2 line `convert (W.isEllSequence_ψ n m 1).symm` re-run). Cost does not change the verdict bucket.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclass/instance?                                                     | no       | — | already typeclass-driven (`[CommRing R]`) |
|  2 | sequences/metric → filters/topology?                                                       | no       | — | purely algebraic identity, no analysis |
|  3 | construction → universal-property class?                                                    | no       | — | `addZ`/`ψ` are concrete polynomials by design |
|  4 | set+closure-predicate → bundled substructure?                                              | no       | — | n/a |
|  5 | vector-space/field-specific → weaken to module/(semi)ring?                                 | partial  | state over arbitrary `[CommRing R]` (Phase 4b row 1) | already maximally weak in base-ring once de-universalised |
|  6 | 1-categorical → higher-categorical?                                                         | no       | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → general additive structure?                                       | no       | `ℤ` is the correct, intrinsic index for division polynomials | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (beyond the de-universalisation already captured in 4b). This is a
finite algebraic identity; there is no filter-/category-/universal-property reformulation that
improves its organisation. The only "generalisation" is base-ring weakening (curve → arbitrary
`W`), which is the literature-standard generality, not a Bourbaki-2.0 idiom shift.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (no definitional equalities or typeclass-search paths
introduced).

---

### Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.addZ_smulPoly`

[A] Lean-Finder       — index tool not loadable in this env (deferred tool absent)  → n/a (covered by D/E + docs)
[B] Loogle            — index tool not loadable in this env (deferred tool absent)  → n/a (covered by D/E + docs)
[C] LeanSearch        — index tool not loadable in this env (deferred tool absent)  → n/a (covered by WebSearch of mathlib4_docs)
[D] Grep mathlib src  `smulPoly`, `Universal.Ring/Field/Jacobian`, `addZ`+`normEDS/IsEllSequence`, `zsmul_eq_smulEval`  → **no hits** for the bridge:
      - `smulPoly` / `Universal.{Ring,Field,Jacobian}` : **0** hits in `Mathlib/`
      - `addZ` ∧ (`normEDS`|`IsEllSequence`|`ψ`) : only false-positive substring hits
        (`addZeroClass` etc. in `Order/Filter/Pointwise`, `Algebra/Group/Pointwise/*`);
        the only true elliptic-`addZ` files are `Jacobian/Formula.lean` + `Projective/Formula.lean`,
        whose `addZ` is the **generic** group-law Z-coord with **no** division-polynomial content.
      - `zsmul_eq_smulEval` / `smulEval` / `zsmul_point_eq` : **0** hits (the multiplication-by-`n`
        formula `n·P=(φₙ/ψₙ²,ωₙ/ψₙ³)` is **not** in mathlib).
[E] Name pattern      `addZ_smulPoly`, `dblZ_smulPoly`, `*_smulPoly`, `isEllSequence_ψ`  → **0** hits in `Mathlib/`.

Searched for both:
  - the user's current form (`addZ (smulPoly m)(smulPoly n) = …` on the universal curve) → absent
  - the literature-standard general form (EDS recurrence) → **present** as `IsEllSequence`
    (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:82`) and `IsEllSequence.normEDS`,
    BUT *not* the `addZ`-bridge / `φ`-packaged form, and *not* the curve-`ψ` specialisation
    `isEllSequence_ψ`.

Concluded: **not in mathlib.** Mathlib has (a) the generic Jacobian `addZ`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:425`) and (b) the abstract EDS
recurrence (`IsEllSequence`, `IsEllSequence.normEDS`), but neither the `WeierstrassCurve.Universal`
construction these `smulPoly`/`smulField` objects live in, nor any lemma tying `addZ` to division
polynomials, nor the multiplication-by-`n` formula this lemma serves. This is genuinely-new content.

---

### Call sites — `WeierstrassCurve.Universal.Jacobian.addZ_smulPoly`

Internal use count: **1** (within NagellLutz, excluding the declaring line)
External-to-file callers: 0 distinct files (the one use is in the **same** file)

| Caller file:line                          | Usage pattern (one-line excerpt)                                  |
|-------------------------------------------|-------------------------------------------------------------------|
| `LutzNagell/ZSMul.lean:516`               | `simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly, ← map_addZ]` (inside `addXYZ_smulField`) |

Inline-derivation grep (re-derived elsewhere without using `addZ_smulPoly`?):
  - `projects/HasseWeil/.../DivisionPolynomial.lean:560` — a **verbatim duplicate** `private lemma
    addZ_smulPoly` with the identical proof, used at `:590` the same way. This is a cross-project
    fork duplication, not an inline bypass; it reinforces that the lemma is a needed bridge in
    *both* forks, but consumed only internally in each.

**What the pattern tells you:** K = 1 internal use, no external/downstream consumers, and the one
use is a `← rewrite` in the odd-step (`addXYZ`) of the `zsmul_eq_smulEval` induction. This is a
single-use bridge lemma — exactly the kind of helper that exists only to factor one rewrite out of
a larger proof. On its own that leans toward NO-composable/inline; but here it is part of a
coherent upstreaming-grade development (mirrors mathlib structure exactly), so the call-site signal
is weak evidence, not decisive.

---

### Composition check (Phase 6)

Can `addZ_smulPoly` be derived from **existing mathlib** in ≤3 chained calls?

Attempt 1: `(curve.isEllSequence_ψ n m 1).symm` + algebra.
  - Mathlib decls used: `IsEllSequence` is in mathlib, but `curve.isEllSequence_ψ` (the *curve-ψ*
    instance) is **project-local** (`DivisionPolynomialOmega.lean:53`), itself resting on
    `IsEllSequence.normEDS` (mathlib) applied to `W.ψ₂, C W.Ψ₃, C W.preΨ₄`.
  - Also needs: the unfolding `addZ`, `smulPoly`, `φ` — `smulPoly` and the `Universal` curve are
    **project-local** definitions absent from mathlib.
  - Result: **fails as a pure-mathlib composition.** Two of the three ingredients (`smulPoly`,
    `isEllSequence_ψ` / the `Universal` curve) do not exist in mathlib. You cannot even *state*
    `addZ_smulPoly` in mathlib today, let alone compose it.
  - Notes: *Given the project's own definitions*, the proof is a 3-line composition
    (`simp_rw [addZ,smulPoly,φ]; convert (curve.isEllSequence_ψ n m 1).symm using 1; ring; ring`).
    So it is a trivial consequence **within the project**, but it is not a mathlib composition —
    the prerequisites must be upstreamed first.

Conclusion: **NOT-COMPOSABLE** from current mathlib (the building blocks `smulPoly` / the universal
curve / `isEllSequence_ψ` are themselves not in mathlib). It *is* a 3-line consequence of the
project's own (would-be-upstreamed) API.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.addZ_smulPoly`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the underlying math is Ward's EDS recurrence (textbook, holds over
  any commutative ring) used at `r=1`; the `addZ`-bridge packaging is **not** a named result.
- Generality analysis (Phase 4): STRICTLY NARROWER (on the fixed universal curve) — but that
  narrowness is the *proof device*; the user-facing upstream form is the general-`W` version.
- Mathlib search (Phase 5): **not in mathlib** — mathlib has generic `addZ` + abstract
  `IsEllSequence`/`normEDS`, but neither `WeierstrassCurve.Universal`, nor `smulPoly`, nor any
  `addZ`↔division-polynomial bridge, nor the `n·P=(φₙ/ψₙ²,ωₙ/ψₙ³)` multiplication formula.
- Composition check (Phase 6): NOT-COMPOSABLE from current mathlib (its prerequisites are not in
  mathlib); a 3-line consequence only *inside* the project.

**Rationale:**

This lemma is mathematically the well-known elliptic-sequence three-term recurrence (Ward;
`ψ_{m+n}ψ_{m-n}ψ_r² = ψ_{m+r}ψ_{m-r}ψ_n² − ψ_{n+r}ψ_{n-r}ψ_m²`), specialised to `r=1` and rewritten
through `φ_k = Xψ_k² − ψ_{k+1}ψ_{k-1}` so that the left side becomes mathlib's Jacobian
`addZ (smulPoly m)(smulPoly n)`. The abstract recurrence is already in mathlib (`IsEllSequence`,
`IsEllSequence.normEDS`). What is *not* in mathlib is the entire surrounding apparatus: the
`WeierstrassCurve.Universal` curve, the multiplication-formula triples `smulPoly k = (φ_k,ω_k,ψ_k)`,
the curve-specialised `isEllSequence_ψ`, and ultimately the multiplication-by-`n` formula
`zsmul_eq_smulEval : n•P = (φₙ:ωₙ:ψₙ)` that this file is built to prove. `addZ_smulPoly` is one
internal load-bearing step of that proof — the part that checks the Z-coordinates agree in the odd
(`addXYZ`) induction step.

The reason this is BORDERLINE rather than a clean YES is that the *decl in isolation* is a
single-use (K=1), `r=1`-hardcoded bridge lemma stated on the universal curve — the granularity of
an internal helper, not a standalone API result. The mathlib-worthy object is the **whole
development** (Junyan Xu's universal-curve track culminating in `zsmul_eq_smulEval`), which mirrors
mathlib's file layout verbatim and is clearly written to be upstreamed; `addZ_smulPoly` would ride
in as a `private`/internal lemma of that PR, very likely restated for a general `W : WeierstrassCurve R`
(Phase 4b) rather than only the universal curve. Whether to (a) treat it as part of that larger
upstreaming unit, (b) restate it general-`W` and ship it as a named public lemma, or (c) keep it
private/internal — is a packaging/taste judgment that depends on how the maintainers want to land
the multiplication-formula development. That is a human call, and the duplicate `private` copy in
HasseWeil shows the project itself treats it as an internal helper.

**Numbered questions (≤5):**
  1. Is the `WeierstrassCurve.Universal` / `zsmul_eq_smulEval` development being upstreamed to
     mathlib as a unit (it appears to be Junyan Xu's work, mirroring mathlib structure)? If yes,
     `addZ_smulPoly` ships *inside* that PR and needs no separate verdict.
  2. In that PR, should `addZ_smulPoly` be a **public** lemma restated for a general
     `W : WeierstrassCurve R` (Phase 4b form), or remain a `private`/internal helper on the
     universal curve (as it is now, and as the HasseWeil duplicate is)?
  3. Is the user-facing target the general-`W` statement
     `addZ (W.smulPoly m)(W.smulPoly n) = W.ψ(n+m)·W.ψ(n-m)`? If so the verdict on *that* lemma is
     YES-add-as-is (cheap to derive from this one via `map_addZ`/`map_ψ`).
  4. The lemma is fork-duplicated in HasseWeil (`DivisionPolynomial.lean:560`). Should the AINTLIB
     cleanup fleet dedup these two copies into one shared `Common/` lemma independently of the
     mathlib question?

**Next action:** answer Q1–Q4. If the development is being upstreamed as a unit (Q1=yes), record
`addZ_smulPoly` as "ships inside the `zsmul_eq_smulEval` PR" and assess the *public* general-`W`
form instead (likely YES-add-as-is). Otherwise, if a standalone decision is wanted, restate
general-`W` and re-run `/mathlibable` on that form. Separately, file an AINTLIB dedup cleanup
ticket for the NagellLutz/HasseWeil duplication.

---

## Next step

Answer the four numbered questions above (chiefly: is this part of the in-flight universal-curve
upstreaming, and is the public target the general-`W` restatement?). The math is genuinely new to
mathlib; the only open question is the packaging grain, which is a maintainer call.
