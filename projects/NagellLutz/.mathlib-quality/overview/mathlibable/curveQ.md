# /mathlibable report — `LutzNagell.LutzNagellTheorem.curveQ`

## Verdict: NO-mathlib-has-it

`curveQ W := W.map (algebraMap ℤ ℚ)` is definitionally **`WeierstrassCurve.baseChange W ℚ`**
(mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`, notation `W⁄ℚ`). It is
a reducible `abbrev` specialisation of an existing mathlib `def`. The very same project already
uses `WeierstrassCurve.baseChange` in its `Universal`/`ZSMul` track. The Lutz–Nagell `General*`
track simply re-spelled it under a private name.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoning from source — the decl is a 1-line `abbrev` that trivially elaborates and is used in 71 sites across 4 sibling files, so it certainly elaborates)
- decl `LutzNagell.LutzNagellTheorem.curveQ`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean:24`
- kind:                      `abbrev` (reducible def)
- has sorry:                 no
- module docstring summary:  "General Weierstrass model for the generalized Lutz-Nagell theorem" — sets up a general `W : WeierstrassCurve ℤ` and its base change to ℚ.

> Qualified-name note: the parsed handle in the task was `LutzNagell.LutzNagellTheorem.curveQ`,
> and the source confirms it exactly (`namespace LutzNagell` → `namespace LutzNagellTheorem` →
> `abbrev curveQ`). VERIFIED.

---

### Statement (Phase 1)

`curveQ` is a **definition**: given an integral Weierstrass curve `W : WeierstrassCurve ℤ`
(coefficients `a₁,a₂,a₃,a₄,a₆ ∈ ℤ`), it returns the rational Weierstrass curve obtained by
pushing every coefficient along the canonical ring map `ℤ → ℚ`. Mathematically this is the
**base change** (scalar extension) of the curve from ℤ to ℚ: `E/ℚ = E ×_{Spec ℤ} Spec ℚ`, the
generic fibre of the integral model.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — the integral Weierstrass curve.

Hypotheses: none.

Conclusion (math): the rational curve `W ⊗_ℤ ℚ` with `aᵢ ↦ (aᵢ : ℚ)`.
Conclusion (Lean): `WeierstrassCurve ℚ`, body `W.map (algebraMap ℤ ℚ)`.

The five companion simp lemmas `curveQ_a₁ … curveQ_a₆` just read off the coefficients
(`(curveQ W).aᵢ = (W.aᵢ : ℚ)`); `curveQ_equation_iff` rewrites the affine equation predicate
in terms of the integer coefficients cast to ℚ. (Those are out of scope for this single-decl
assessment but are noted because they are exactly mathlib's `map_aᵢ` / `Affine.equation_iff`
family — see Phase 5/6.)

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a reducible `abbrev` that specialises an existing structure-valued `def`
(`WeierstrassCurve.map` / `baseChange`) to fixed rings `ℤ → ℚ`. Not a new structure, not a
named theorem, not a `## Main results` entry.

(Literature width was still run EXHAUSTIVELY per the protocol.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`W.map (algebraMap ℤ ℚ)`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | It is declared `abbrev` (reducible) — the opposite of a sealing barrier. `simp [curveQ]` unfolds it freely throughout the project; nothing relies on it *not* unfolding. |
| Avoid typeclass diamonds         | no       | No instance is anchored on it; downstream `Jacobian.Point`/`Affine.Point` instances resolve through `WeierstrassCurve ℚ`, identical to what `baseChange` yields. |
| Mark semantic intent / API name  | no       | The intent ("base change to ℚ") is *already named in mathlib* as `baseChange`. A local alias adds no stable surface mathlib lacks. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** — biases strongly toward a NO bucket (confirmed
NO-mathlib-has-it below).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic curve base change scalar extension Weierstrass curve over Z to Q definition" | yes | `E/ℚ` from integral model; `aᵢ ↦ aᵢ` under the inclusion | Sage `base_extend`, Magma integral/minimal-model docs; entirely standard textbook operation (Silverman AEC III) |
| 2 | WebSearch (general form) | "mathlib WeierstrassCurve baseChange map elliptic curve Lean" | yes | `WeierstrassCurve.baseChange`, `WeierstrassCurve.map`, `map_baseChange`, `baseChange_Ψ`, `Affine.baseChange_polynomial` | mathlib4 docs confirm a full base-change API already exists, including division-polynomial transport |
| 3 | WebSearch (named-after / aliases) | "base change" / "base extension" / "scalar extension" elliptic curve over a ring | yes | same notion; alias "base extension" (Sage `.base_extend`) | name varies (base change / extension of scalars); concept identical |
| 4 | ChatGPT MCP | — | n/a | — | MCP reported down for this run (per task brief); compensated by an extra WebSearch generality level (#3) and direct mathlib source reading — the standard form is textbook-unambiguous, so the gap does not affect the verdict |
| 5 | Local references | grep `.mathlib-quality/references/` for "base change"/"curveQ" | n/a | — | NagellLutz references dir holds Lutz–Nagell sources, not a base-change definition; base change is assumed background, not a result to cite |
| 6 | nLab | "base change", "extension of scalars" | yes | base change = pullback along `Spec A → Spec R`; extension of scalars `M ↦ A ⊗_R M` | confirms the categorical content; mathlib's `baseChange` is the affine/coefficient-level instance |
| 7 | nCatLab | (same as nLab) | n/a | — | same source; nothing extra |
| 8 | Stacks Project | "base change of schemes" (tag 01JX area) | yes | base change of a scheme along a morphism of bases | the scheme-theoretic justification that `curveQ` = generic fibre; not a missing primitive |
| 9 | MathOverflow / MSE | "elliptic curve over Z base change to Q minimal/integral model" | yes | routine; generic fibre of a Weierstrass/Néron model | confirms ubiquity; no exotic generality |
| 10 | recent arXiv (≤5y) | "Weierstrass curve base change Lean formalization" | yes | the mathlib elliptic-curve formalization (Angdinata–Xu et al.) which *is* where `baseChange` lives | the formalized standard form is precisely mathlib's `baseChange` |

### Literature summary (Phase 3)

Concept identified as: **base change / extension of scalars of a Weierstrass curve** (here ℤ → ℚ;
the generic fibre of the integral model).
Sources agree on the standard form: **yes** — coefficient-wise image under the base ring map; the
only naming variation is "base change" vs "base extension".
Most general standard form: for any ring map `f : R →+* A`, map the curve coefficient-wise
(`WeierstrassCurve.map`); the algebra special case `baseChange A` uses `algebraMap R A`.
Generality dimensions where the literature varies:
  - base map: arbitrary ring hom (`map`) ⊇ algebra structure map (`baseChange`) ⊇ the fixed
    `ℤ → ℚ` used here. **The user's form sits at the most special end of this axis.**
Disagreement with the literature: none.

---

### Generality analysis — `curveQ`

Literature-standard form (Phase 3): coefficient-wise image of a Weierstrass curve along a ring
map `R →+* A` (mathlib `map`), or along `algebraMap R A` (mathlib `baseChange`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | source ring `ℤ` | fixed `ℤ` | arbitrary `CommRing R` | yes | nothing in the definition uses ℤ; `baseChange` already takes any `R` |
| 2 | target ring `ℚ` | fixed `ℚ` | arbitrary `CommRing A` with `[Algebra R A]` | yes | nothing uses ℚ; `baseChange` already takes any algebra `A` |
| 3 | the map | `algebraMap ℤ ℚ` | any `f : R →+* A` (`map`) or `algebraMap R A` (`baseChange`) | yes | mathlib's `map`/`baseChange` are strictly more general and already exist |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (and the strictly-more-general standard
form *already exists in mathlib*).
Number of weakening opportunities found: 3 (source ring, target ring, the map) — all collapse to
"use `WeierstrassCurve.baseChange` / `WeierstrassCurve.map`".
Proposed restatement: none needed for upstreaming — the general form is `WeierstrassCurve.baseChange`,
already in mathlib. Locally, replace `curveQ W` with `W.baseChange ℚ` (notation `W⁄ℚ`).
Cost of restatement: CHEAP — purely mechanical; the two terms are reducibly defeq.

Because the more-general form is **already present in mathlib**, this is NO-mathlib-has-it, not
YES-but-generalise-first (the latter is for forms mathlib lacks at *any* generality).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preamble → typeclass? | no | — | already structural |
| 2 | sequences/metric → filters/topology? | no | — | no analysis content |
| 3 | construct → universal-property class? | no | base change *is* a concrete construction in mathlib | — |
| 4 | set+closure → bundled substructure? | no | — | not a substructure |
| 5 | vector-space/field-specific → weaken typeclasses? | yes — but **already done by mathlib**: `baseChange` is stated for any `CommRing`/`Algebra` | `W.baseChange A` | the whole `map_aᵢ`, `map_Δ`, `baseChange_Ψ`, `Affine.baseChange_*` API |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | yes — but **already done**: `baseChange` is index-free over `(R, A)` | `W.baseChange A` | unifies with all base-change lemmas in mathlib |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it is mathlib's own `baseChange`.** The contemporary,
maximally-general mathlib formulation already exists. There is no *new* modernisation for us to
contribute; the move is simply to *use* `baseChange`. (So this does not flip the verdict to
YES-but-generalise-first: the better form is not ours to add, it is mathlib's to reuse.)

---

### Diamond / defeq risk — `curveQ` (Phase 4.5)

Kind is `abbrev` (a `def`), so the phase runs.

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Produces a plain `WeierstrassCurve ℚ` value; no instance is declared on it. Instance search on `(curveQ W).toAffine.Point` etc. is identical to that on `(W.baseChange ℚ).toAffine.Point`. |
| 2 | Reducibility leak | low | `abbrev` ⇒ `@[reducible]`; the body `W.map (algebraMap ℤ ℚ)` is exposed to defeq everywhere. Harmless here (it *should* unfold to `baseChange`), but it is the standard reason such a one-line alias is not worth a sealed mathlib def. |
| 3 | Non-canonical unfolding | none | `simp [curveQ]` unfolds to `map (algebraMap ℤ ℚ)` exactly as `baseChange` would; no surprise. |
| 4 | Instance priority collision | n/a | not an `instance`. |
| 5 | Universe issues | none | monomorphic (`ℤ`, `ℚ` in `Type 0`); no universe variables. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (single reducibility-leak row; benign). Not load-bearing for the verdict
since the bucket is a NO bucket (nothing is added to mathlib).

---

### Mathlib search-status: `curveQ`

[A] Lean-Finder       n/a (index tool unavailable this run) — compensated by direct source read of `Weierstrass.lean`
[B] Loogle            type pattern `WeierstrassCurve ℤ → WeierstrassCurve ℚ` via `map (algebraMap _ _)` — matches `WeierstrassCurve.baseChange` (general `R,A`)
[C] LeanSearch        "base change of a Weierstrass curve" / "map elliptic curve along ring hom" — `WeierstrassCurve.map`, `WeierstrassCurve.baseChange`
[D] Grep mathlib src  `def map` / `def baseChange` in `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` — **direct hits, lines 231 and 236**
[E] Name pattern      grep `baseChange`, `map (algebraMap ℤ ℚ)` across `Mathlib/` — `baseChange` is the canonical name; `W⁄A` notation at line 240

Searched for both:
  - the user's current form (`map (algebraMap ℤ ℚ)`) — equals `baseChange` specialised
  - the literature-standard form (base change along any algebra) — **`WeierstrassCurve.baseChange`**

Concluded: **found in mathlib as `WeierstrassCurve.baseChange`; more general form (the user's
`curveQ W` is the specialisation `W.baseChange ℚ`).** Definitionally `curveQ W = W.map (algebraMap ℤ ℚ)`
= `W.baseChange ℚ` (mathlib `baseChange` body, line 237, is literally `W.map <| algebraMap R A`).

Supporting facts:
- `@[simps] def map` (lines 230–232) auto-generates `map_a₁ … map_a₆`; mathlib also has `map_b*`,
  `map_c₄`, `map_c₆`, `map_Δ` (lines 242–275). These ARE the project's `curveQ_a₁ … curveQ_a₆`.
- The project's division-polynomial rewrites already call mathlib's `map_Φ`, `map_ΨSq`, `map_preΨ`
  (see `GeneralIntegralMultiple.lean:81-84`, `GeneralPrimeOrder.lean:92`) — i.e. the same
  `map`/`baseChange` family. The web search confirms `WeierstrassCurve.baseChange_Ψ`,
  `baseChange_ΨSq`, `Affine.baseChange_polynomial` exist in mathlib for the transported objects.
- `[Algebra ℤ ℚ]` is canonical in mathlib (ℚ is a ℤ-algebra), so `W.baseChange ℚ` is well-typed
  with no extra instance work.

---

### Call sites — `curveQ`

Internal use count: **71** (within NagellLutz, excluding the declaring file `GeneralCurve.lean`).
External-to-file callers: **4 distinct files**.

| Caller file:line (representative) | Usage pattern (one-line excerpt) |
|-----------------------------------|----------------------------------|
| GeneralIntegralMultiple.lean:28   | `(hns : (curveQ W).toAffine.Nonsingular x y)` |
| GeneralIntegralMultiple.lean:37   | `congrArg (Jacobian.Point.toAffineAddEquiv (curveQ W)).symm hnP` |
| GeneralMain.lean:33               | `congrArg (Jacobian.Point.toAffineAddEquiv (curveQ W)).symm h` |
| GeneralDiscriminant.lean:122      | `eval x ((curveQ W).Φ 2) = …` |
| GeneralPrimeOrder.lean:59         | `((curveQ W).ψ n).evalEval x y = 0` |

Files: `GeneralIntegralMultiple.lean`, `GeneralMain.lean`, `GeneralDiscriminant.lean`,
`GeneralPrimeOrder.lean`.

Inline-derivation grep (was `W.baseChange ℚ` used directly instead?):
  - **YES — the same project already uses `WeierstrassCurve.baseChange` in a parallel track:**
    - `LutzNagell/Universal.lean:130` `abbrev pointedCurve := baseChange curve Universal.Field`
    - `LutzNagell/Universal.lean:167` `abbrev curvePoly := curve.baseChange Poly`
    - `LutzNagell/Universal.lean:170` `abbrev curveRing := curve.baseChange Universal.Ring`
    - `LutzNagell/ZSMul.lean:341,439,486` `curve.baseChange Universal.Field`, `WeierstrassCurve.baseChange`
  - This confirms the prompt's "duplicated General*/PID* tracks" diagnosis: one track uses the
    mathlib primitive `baseChange`, the General/Lutz–Nagell track re-wrapped it as `curveQ`.

Composability signal: K = 71 internal uses is a *real local API* — but it is an API for the
**wrong abstraction**: every one of those 71 uses would work verbatim with `W.baseChange ℚ`
(reducibly defeq). So the high call count argues for a project-internal rename to the mathlib
primitive, not for upstreaming a duplicate.

---

### Composition check (Phase 6)

Can `curveQ` be obtained from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.baseChange W ℚ` (one call), or equivalently `W.baseChange ℚ`,
notation `W⁄ℚ`.
  - Mathlib decls used: `WeierstrassCurve.baseChange` (which is `W.map (algebraMap ℤ ℚ)`).
  - Result: **succeeds** — and not merely up to propositional equality: `curveQ W` and
    `W.baseChange ℚ` are **reducibly definitionally equal** (`abbrev` body = `baseChange` body).
  - Notes: this is the degenerate "composition" — it is the *same definition* already in mathlib,
    so the more precise bucket is NO-mathlib-has-it rather than NO-composable-from-mathlib.

Conclusion: the term *is* a single existing mathlib definition. → **NO-mathlib-has-it** (a strict
strengthening of "composable": no composition is even required).

---

## Verdict: `curveQ`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): "base change of a Weierstrass curve, ℤ → ℚ" — textbook-standard;
  mathlib4 docs and the formalization literature confirm `WeierstrassCurve.baseChange` exists.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — and the general form already
  ships in mathlib; no new contribution at any generality.
- Mathlib search (Phase 5): found as `WeierstrassCurve.baseChange`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`); the user's form is the
  `R=ℤ, A=ℚ` specialisation, reducibly defeq.
- Composition check (Phase 6): NO composition needed — it is the same definition.

**Rationale:**

`curveQ W := W.map (algebraMap ℤ ℚ)` is, verbatim, mathlib's `WeierstrassCurve.baseChange W ℚ`,
whose definition (`Weierstrass.lean:237`) is `W.map <| algebraMap R A`. Because `curveQ` is a
reducible `abbrev`, the two are not just propositionally equal but reducibly definitionally equal,
so every one of the 71 call sites would type-check unchanged after the substitution. The five
satellite lemmas `curveQ_a₁ … curveQ_a₆` are mathlib's `@[simps]`-generated `map_a₁ … map_a₆`
(lines 230–232 with the `b/c/Δ` companions at 242–275), and `curveQ_equation_iff` is
`WeierstrassCurve.Affine.equation_iff` after the trivial coefficient simp — nothing here is
absent from mathlib. The named gap mathlib has is *none*: it has the definition, the coefficient
simp set, the discriminant/`c`-invariant transport, the division-polynomial transport
(`baseChange_Ψ`, `baseChange_ΨSq`), and the affine-polynomial transport
(`Affine.baseChange_polynomial`). The decisive tell is that this very project already uses
`WeierstrassCurve.baseChange` in its `Universal`/`ZSMul` track (`baseChange curve Universal.Field`,
`curve.baseChange Poly`, `curve.baseChange Universal.Ring`); the Lutz–Nagell `General*` fork merely
re-spelled the same primitive under a local name — exactly the duplicated-fork pattern flagged in
the task brief.

**WHY not (refactor-actionable):**
Mathlib already has it. The existing decl is `WeierstrassCurve.baseChange` (general over any
`CommRing R` and `[Algebra R A]`); the project's `curveQ W` is its `R=ℤ, A=ℚ` instance and is
reducibly defeq to `W.baseChange ℚ`. The coefficient lemmas come for free from the `@[simps]` on
`WeierstrassCurve.map`, and `curveQ_equation_iff` follows from `Affine.equation_iff` plus the
`map_aᵢ` rewrites. No mathlib gap exists to fill.

  Existing mathlib decl:        `WeierstrassCurve.baseChange`
  Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`
                                (body line 237: `W.map <| algebraMap R A`; notation `W⁄A` at line 240)
  Our form follows immediately (reducibly defeq):
  ```lean
  example (W : WeierstrassCurve ℤ) : curveQ W = W.baseChange ℚ := rfl
  ```
  And the satellite lemmas (out of scope, noted for the refactor):
  ```lean
  example (W : WeierstrassCurve ℤ) : (W.baseChange ℚ).a₁ = (W.a₁ : ℚ) := by simp   -- WeierstrassCurve.map_a₁ via baseChange
  ```
  Call sites in our project (Phase 6.0): **71**, across 4 files
  (`GeneralIntegralMultiple.lean`, `GeneralMain.lean`, `GeneralDiscriminant.lean`,
  `GeneralPrimeOrder.lean`).

  **Refactor plan:**
  1. At each of the 71 sites, replace `curveQ W` with `W.baseChange ℚ` (or notation `W⁄ℚ`).
     The substitution is reducibly defeq, so no proof body needs to change — only the term spelling.
  2. Delete the satellite lemmas `curveQ_a₁ … curveQ_a₆`: replace their uses by the existing
     mathlib simp lemmas `WeierstrassCurve.map_a₁ … map_a₆` (these already fire on
     `(W.baseChange ℚ).aᵢ` after unfolding `baseChange`; in practice `simp` closes the same goals).
     Note: the project's own `simp only [curveQ_a₁, curveQ_a₃, …]` calls (e.g.
     `GeneralMain.lean:167`, `GeneralDiscriminant.lean:111`) become `simp only [map_a₁, map_a₃, …]`
     (or just `simp`), watching for the `baseChange`→`map` unfolding step.
  3. Replace `curveQ_equation_iff W x y` (used at `GeneralIntegralMultiple.lean:109`,
     `GeneralPrimeOrder.lean:111`, `GeneralDiscriminant.lean:95`) with
     `WeierstrassCurve.Affine.equation_iff` plus the `map_aᵢ` rewrites — or keep a *single*
     thin local lemma if it materially shortens those three call sites (a judgment call, but it is
     not a mathlib contribution either way).
  4. Delete `abbrev curveQ` from `GeneralCurve.lean`. Align the `General*` track with the
     `Universal`/`ZSMul` track, which already uses `baseChange`.

  Argument-order note: `curveQ W` (function form) ↦ `W.baseChange ℚ` (dot form, target ring
  explicit) ↦ or notation `W⁄ℚ`. `baseChange` takes the target type `A` as an explicit argument
  (`variable (A) in`), so write `W.baseChange ℚ`, not `W.baseChange`.

  Next action: delete `curveQ` (and its `_aᵢ` / `equation_iff` satellites) from the project;
  migrate the 71 call sites to `WeierstrassCurve.baseChange`. This is a **CLEANUP/dedup ticket on
  `main`**, not a mathlib PR — and it is the same dedup the project already half-did in its other
  track.

---

## Next step

Delete `curveQ` from `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean` and
replace its 71 uses (4 files) with mathlib's `WeierstrassCurve.baseChange W ℚ` (notation `W⁄ℚ`);
drop the `curveQ_a₁ … curveQ_a₆` lemmas in favour of mathlib's `map_a₁ … map_a₆`. File this as an
AINTLIB cleanup/dedup ticket on `main` (no mathlib PR — mathlib already has the definition).
