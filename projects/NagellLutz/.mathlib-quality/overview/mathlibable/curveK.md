# /mathlibable report — `LutzNagell.PID.curveK`

**Verdict: `NO-mathlib-has-it`** — `curveK` is definitionally identical to mathlib's
`WeierstrassCurve.baseChange`.

---

### Baseline (Phase 0)
- lake build:               not run (build is stale per task note; reasoned from source — the decl is a 1-line `abbrev`, no elaboration risk)
- decl `LutzNagell.PID.curveK`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:27`
- kind:                      `abbrev` (a `def` marked reducible)
- has sorry:                 no
- module docstring summary:  "General Weierstrass model over a PID and its fraction field" — sets up `W : WeierstrassCurve R` for a PID `R` with fraction field `K` and base-changes `W` to `K`. Generalises `GeneralCurve.lean` from `ℤ/ℚ` to an arbitrary PID `R`.

True qualified name (VERIFIED from source): **`LutzNagell.PID.curveK`** (namespaces `LutzNagell` → `PID`).

---

### Statement (Phase 1)

`LutzNagell.PID.curveK` is **a definition**: the base change of a Weierstrass curve along
a fixed algebra structure.

Given a commutative ring `R`, a field `K` with `[Algebra R K]`, and a Weierstrass curve
`W : WeierstrassCurve R`, `curveK R K W` is the Weierstrass curve over `K` obtained by
applying `algebraMap R K` to each of the five Weierstrass coefficients
`a₁, a₂, a₃, a₄, a₆`. Mathematically: extend the scalars of the Weierstrass model from
`R` up to `K`. (Despite the file's framing — `K` a fraction field of a PID `R` — the
definition itself requires only `[CommRing R] [Field K] [Algebra R K]`; the PID/fraction-field
hypotheses are imposed downstream, not here.)

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R]` — the base ring (mathematical role: ground ring of `W`).
- `K : Type*` `[Field K] [Algebra R K]` — the target field and its `R`-algebra structure.
- `W : WeierstrassCurve R` — the Weierstrass curve to be base-changed.

Hypotheses: none (it is a definition).

Conclusion (math): the curve `W ⊗_R K`, i.e. `W` with coefficients pushed along `R → K`.
Conclusion (Lean): `WeierstrassCurve K`, with body `W.map (algebraMap R K)`.

Accompanying API in the same file (NOT the target decl, but assessed together because they
are glue around `curveK`):
- `curveK_a₁ … curveK_a₆` — `@[simp]` coefficient projections, each `:= by simp [curveK]`.
- `curveK_equation_iff` — unfolds the affine Weierstrass equation over `K`; proof is
  `rw [Affine.equation_iff]; simp [curveK]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `abbrev` that renames an existing mathlib construction; not a new
structure, not a named theorem, not a `## Main results` entry. (It is *infrastructure* for
the project's main results, but is not itself one.)

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1** substantive line (`W.map (algebraMap R K)`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

Exemption check:
| Exemption                         | Applies? | Evidence                                                                                      |
|-----------------------------------|----------|------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                 | no       | It is an `abbrev` (reducible) — the opposite of a sealing barrier; it *exposes* the body to defeq. Several call sites (`PIDPrimeOrder.lean:145`, `PIDIntegralMultiple.lean:74`) deliberately `simp [curveK]`/`unfold` it, so consumers rely on it unfolding, not on it being opaque. |
| Avoid typeclass diamonds          | no       | No instance is anchored on it; it returns a bare `WeierstrassCurve K`. The `[Algebra R K]` it consumes is supplied by the caller, not pinned by this def. |
| Mark semantic intent / API name   | partial → no | It does carry a docstring and a short name reused ~40× — but that is exactly the duplication problem: the same role is already served by mathlib's named `WeierstrassCurve.baseChange` (which even has scoped notation `W⁄K`). A project-local synonym is not a *new* stable API surface; it shadows an existing one. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (biases the verdict toward a NO bucket — confirmed by Phases 5–6).

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "base change of a Weierstrass curve over a ring homomorphism elliptic curve coefficients"               | yes  | `W.map f = ⟨f a₁, f a₂, f a₃, f a₄, f a₆⟩`             | Top hit is the **mathlib4 docs** `…EllipticCurve.Weierstrass` page describing `map`/`baseChange` verbatim; also SageMath `weierstrass_morphism`. |
|  2 | WebSearch (general form)          | "elliptic curve base extension to fraction field Weierstrass equation Nagell-Lutz"                      | yes  | base-extend E/k along a field extension; coeffs relabel | Silverman-style; Wikipedia "Nagell–Lutz". Base extension to ℚ / number fields is treated as a routine relabeling, never a named lemma. |
|  3 | WebSearch (named-after / aliases) | `"WeierstrassCurve" mathlib "baseChange" map algebraMap`                                                | yes  | `W.baseChange A = W.map (algebraMap R A)`               | mathlib4 docs again; aliases: "base change", "base extension", "scalar extension". Confirms the exact identity to `curveK`. |
|  4 | ChatGPT MCP                       | self-contained: is base change a named construction; is it in mathlib; is equation_iff just unfolding?  | n/a  | (server down)                                          | Codex backend errored (matches task's "ChatGPT MCP may be down"). Fell back to channels 1–3 + source, which already settle every sub-question. |
|  5 | Local references                  | grep `.mathlib-quality/references/`                                                                     | n/a  | —                                                      | Directory absent for NagellLutz. Recorded n/a. |
|  6 | nLab                              | "elliptic curve" base change                                                                            | n/a  | —                                                      | nLab has no atomic "base change of a Weierstrass model" page; it is a special case of pullback of schemes / base change of affine schemes, far more general than this coefficient map. No tighter statement than mathlib's. |
|  7 | nCatLab (categorical)             | —                                                                                                      | n/a  | —                                                      | Not a categorical concept beyond "apply a ring map to a tuple of coefficients". |
|  8 | Stacks Project (alg geom)         | base change of Weierstrass equation                                                                     | n/a  | —                                                      | Stacks treats base change of schemes/morphisms abstractly (`02WE` etc.); the coefficient-level Weierstrass map is below its granularity. No competing named statement. |
|  9 | MathOverflow / Math.SE            | base change Weierstrass coefficients generality                                                         | n/a  | —                                                      | No canonical Q&A; the construction is considered elementary (relabel coefficients along R→K). |
| 10 | recent arXiv (last 5 yr)          | (covered by #1) arXiv 2302.10640 "Formal Proof of the Group Law on Weierstrass…"                        | yes  | uses mathlib's `WeierstrassCurve` + `map`/`baseChange` | The formalisation literature itself uses mathlib's `map`/`baseChange`, not a bespoke alias. |

Protocol pass: WebSearch ran 3 distinct queries at 3 generality levels (✓); ChatGPT MCP
attempted (server down, recorded n/a with reason ✓); local refs checked (absent, n/a ✓); nLab
checked (✓); Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason (✓).

### Literature summary (Phase 3)

Concept identified as: **base change (a.k.a. base extension / scalar extension) of a
Weierstrass curve** along a ring homomorphism / algebra map.
Sources agree on the standard form: **yes** — apply the ring map to each coefficient; over a
field this is the model `W ×_{Spec R} Spec K`.
Most general standard form: for *any* ring homomorphism `f : R →+* A` (no field, no
PID, no fraction-field hypothesis), `W.map f` with coefficients `f aᵢ`. The
algebra-map special case `W.map (algebraMap R A)` is exactly "base change to an `R`-algebra `A`".
Generality dimensions where the literature varies:
  - target object: arbitrary ring `A` (most general, via a `RingHom`) ⊇ `R`-algebra `A`
    (via `algebraMap`) ⊇ field `K` (curveK's stated case) ⊇ fraction field of a PID
    (the file's framing). The literature/mathlib standard sits at the **top** of this chain.
Disagreement with the literature: **none**. The literature/mathlib form is strictly more
general than `curveK`; `curveK` is a special case (`A := K` a field) wearing a local name.

---

### Generality analysis — `LutzNagell.PID.curveK` (Phase 4)

Literature-standard form (Phase 3): `WeierstrassCurve.map (f : R →+* A) : WeierstrassCurve A`,
specialised to algebras as `WeierstrassCurve.baseChange (A) [Algebra R A]`.

| # | Parameter / hypothesis      | Current Lean form            | Literature-standard form      | Weaker form exists? | Reason |
|---|-----------------------------|------------------------------|-------------------------------|---------------------|--------|
| 1 | `K : Type*` `[Field K]`     | target is a **field**        | target is an arbitrary **comm ring** `A` | **yes** | `map`/`baseChange` need only `[CommRing A]`; the `Field` hypothesis is unused by the construction. |
| 2 | `[Algebra R K]`             | algebra map `R → K`          | either an arbitrary `RingHom R →+* A` (`map`) or `[Algebra R A]` (`baseChange`) | yes | mathlib offers both: `map` for a bare ring hom, `baseChange` for the algebra-map case `curveK` uses. |
| 3 | `R` `[CommRing R]`          | comm ring                    | comm ring (same)              | no                  | already maximally weak. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (target needlessly restricted to a
field; mathlib's `baseChange`/`map` are over any comm ring / any ring hom).
Number of weakening opportunities: 2 (drop `Field K`; generalise target to any algebra/ring).
Proposed restatement: **none needed for the project to author** — the more general form
*already exists in mathlib* as `WeierstrassCurve.baseChange` (algebra case) and
`WeierstrassCurve.map` (ring-hom case). So this is not a "generalise-first" situation; it is a
"mathlib already has the general form" situation → drives the verdict to **NO-mathlib-has-it**,
not YES-but-generalise-first.
Cost of restatement: n/a (delete + reuse mathlib).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Reformulation                              | Downstream |
|----|--------------------------------------------------------------------------|----------|--------------------------------------------|------------|
|  1 | bundled hypotheses → typeclasses/instances?                              | no       | already typeclass-based (`[Algebra R K]`)  | — |
|  2 | sequences/metric → filters/topological?                                 | no       | no analytic content                        | — |
|  3 | construction → universal-property class?                                | no (already done by mathlib) | mathlib's `baseChange` is the canonical construction; `map` has `map_baseChange`, `map_map`, `map_injective` API | reuse mathlib's base-change API |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | n/a                                        | — |
|  5 | field/metric-specific → weaken to module/ring?                          | **yes**  | drop `Field K` → any `[CommRing A]` (= mathlib `baseChange`) | unlocks `map_a*, map_b*, map_c*, map_Δ, map_map, map_baseChange, map_injective` |
|  6 | 1-categorical → higher-categorical?                                     | no       | n/a                                        | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary structure?                          | n/a      | no numeric index                           | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, and mathlib already implements it.** The contemporary mathlib
form is `WeierstrassCurve.baseChange W K` (or `W.map (algebraMap R K)`, or the notation `W⁄K`).
Because the better form is *already in mathlib*, Phase 7 is **NO-mathlib-has-it**, not
YES-but-generalise-first (there is nothing for the project to newly contribute).

---

### Diamond / defeq risk — `LutzNagell.PID.curveK` (Phase 4.5)

Kind is `abbrev` (a `def`), so the phase runs.

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond            | none    | Returns a bare `WeierstrassCurve K`; defines no instance, anchors no search path.    |
| 2 | Reducibility leak            | low     | `abbrev` is `@[reducible]`, so the body `W.map (algebraMap R K)` is exposed to defeq everywhere — but the body is itself a trivial wrapper, so this is harmless. (Moot for mathlib: we are not adding it; we are *replacing* it with the sealed `baseChange`.) |
| 3 | Non-canonical unfolding      | low     | `simp [curveK]` unfolds to `W.map (algebraMap R K)`; predictable. |
| 4 | Instance priority collision  | none    | Not an instance. |
| 5 | Universe-polymorphism issues | none    | Inherits `WeierstrassCurve`'s universe handling; no forced annotation. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (and irrelevant to the verdict — the decl is not being added to mathlib).
Top risks: none HIGH. Mitigations: n/a.

---

### Mathlib search-status: `LutzNagell.PID.curveK` (Phase 5)

[A] Lean-Finder       "base change Weierstrass curve", "map curve ring hom"   → hit: `WeierstrassCurve.baseChange`, `WeierstrassCurve.map`
[B] Loogle            `WeierstrassCurve _ → (_ →+* _) → WeierstrassCurve _` / `WeierstrassCurve.map` / `WeierstrassCurve.baseChange`  → hit: `WeierstrassCurve.map`, `WeierstrassCurve.baseChange`
[C] LeanSearch        "Weierstrass curve base changed to an algebra"           → hit: `WeierstrassCurve.baseChange`
[D] Grep mathlib src  `def map`, `def baseChange` in `…/EllipticCurve/Weierstrass.lean`  → **hit, confirmed by direct file read**:
      - `Weierstrass.lean:231`  `@[simps] def map : WeierstrassCurve A := ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩`
      - `Weierstrass.lean:236`  `def baseChange [Algebra R A] : WeierstrassCurve A := W.map <| algebraMap R A`
      - `Weierstrass.lean:240`  scoped notation `W⁄A` for `baseChange W A`
      - `@[simps]` on `map` ⇒ auto-generated `WeierstrassCurve.map_a₁ … map_a₆` (used at lines 244–259)
      - companion API: `map_b₂/b₄/b₆/b₈`, `map_c₄/c₆`, `map_Δ`, `map_id`, `map_map`, `map_baseChange`, `map_injective`
[E] Name pattern      grep `curveK`/`baseChange`/`WeierstrassCurve.map` in project + mathlib  → only project-local `curveK`; mathlib owns `map`/`baseChange`

Searched both forms:
  - current form (`W.map (algebraMap R K)`, `K` a field) — IS `WeierstrassCurve.baseChange W K` by definition.
  - literature-standard / general form (`W.map f`, any ring hom) — `WeierstrassCurve.map`.

Concluded: **found in mathlib as `WeierstrassCurve.baseChange` — DEFINITIONALLY IDENTICAL
form** (mathlib's `baseChange` body is the literal right-hand side of `curveK`), and as
`WeierstrassCurve.map` for the more general ring-hom version. The five `curveK_aᵢ` lemmas are
mathlib's `@[simps]`-generated `WeierstrassCurve.map_aᵢ`; `curveK_equation_iff` is
`WeierstrassCurve.Affine.equation_iff` followed by those coefficient simp lemmas.

---

### Call sites — `LutzNagell.PID.curveK` (Phase 6.0)

Internal use count: **K ≈ 40** distinct uses (excluding the declaring file `PIDCurve.lean`).
External-to-file callers: **3 files** — `PIDMain.lean`, `PIDPrimeOrder.lean`,
`PIDIntegralMultiple.lean` (plus a prose mention in `GeneralIntegralMultiple.lean:23`).

| Caller file:line                | Usage pattern (one-line excerpt)                                   |
|---------------------------------|---------------------------------------------------------------------|
| PIDMain.lean:49                 | `(curveK R K W).toAffine.Nonsingular x y`                          |
| PIDMain.lean:277                | `simp only [curveK_a₁, curveK_a₃] at hψ₂`                          |
| PIDMain.lean:288                | `eval x ((curveK R K W).Φ 2) = …`                                  |
| PIDPrimeOrder.lean:66           | `((curveK R K W).ψ n).evalEval x y = 0`                            |
| PIDPrimeOrder.lean:145          | `simp only [WeierstrassCurve.Affine.negY, curveK]` (unfolds it)   |
| PIDIntegralMultiple.lean:44     | `x' * ((curveK R K W).ΨSq n).eval x = ((curveK R K W).Φ n).eval x` |
| PIDIntegralMultiple.lean:74     | `simp only [← hc, curveK, map_Φ, map_ΨSq, …]` (unfolds it)         |

Inline-derivation grep: several sites already `simp [curveK]` / `unfold curveK` down to
`W.map (algebraMap R K)` (e.g. `PIDPrimeOrder.lean:145`, `PIDIntegralMultiple.lean:74`), i.e.
they deliberately strip the alias to expose the underlying `map`. This confirms the alias is a
thin renaming layer over mathlib's `map`/`baseChange`, not load-bearing abstraction.

Signal (per the call-sites table): K ≥ 3 internal uses, but the statement is identical to an
existing mathlib decl AND is re-derived/unfolded inline at multiple sites → **NO-mathlib-has-it**
(mathlib has it; the K sites are a mechanical rename `curveK R K W` ⇝ `W.baseChange K` / `W⁄K`).

### Composition check (Phase 6)

Can `curveK` be obtained from mathlib in ≤3 calls? It is not even a composition — it is a
**single mathlib definition**:

Attempt 1: `curveK R K W` ≡ `WeierstrassCurve.baseChange W K` ≡ `W.map (algebraMap R K)`.
  - Mathlib decls used: `WeierstrassCurve.baseChange` (1 call) — equal **by `rfl`**.
  - Result: **succeeds** (definitional equality, zero rewriting).
  - The five `curveK_aᵢ` are `WeierstrassCurve.map_aᵢ`; `curveK_equation_iff` is
    `Affine.equation_iff` + `map_a₁..map_a₆` simp.

Conclusion: **NOT a composition — a verbatim existing definition.** (This is stronger than
NO-composable: it is NO-mathlib-has-it.)

---

## Verdict: `LutzNagell.PID.curveK`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the construction is "base change of a Weierstrass curve"; the
  mathlib4 docs (top WebSearch hit, twice) state `baseChange A = map (algebraMap R A)` —
  exactly `curveK`'s body. Nagell–Lutz literature treats base extension as routine relabeling.
- Generality analysis (Phase 4): STRICTLY NARROWER (target pinned to a `Field`), but the more
  general form already lives in mathlib (`baseChange` over any algebra, `map` over any ring hom).
- Mathlib search (Phase 5): found as `WeierstrassCurve.baseChange` (`Weierstrass.lean:236`),
  **definitionally identical**; general version `WeierstrassCurve.map` (`Weierstrass.lean:231`).
- Composition check (Phase 6): not a composition — a single existing definition, equal by `rfl`.

**Rationale:**

`curveK R K W := W.map (algebraMap R K)` is, character-for-character, the body of mathlib's
`WeierstrassCurve.baseChange W K` (whose definition is `W.map <| algebraMap R A`). They are
equal by `rfl`. Mathlib furthermore ships the more general `WeierstrassCurve.map (f : R →+* A)`
for an arbitrary ring homomorphism, of which `curveK` is the `f := algebraMap R K`, `A := K`
special case — and even provides the scoped notation `W⁄K` for `baseChange W K`. The project's
five `@[simp]` lemmas `curveK_a₁ … curveK_a₆` re-derive mathlib's `@[simps]`-generated
`WeierstrassCurve.map_a₁ … map_a₆`; the helper `curveK_equation_iff` is just
`WeierstrassCurve.Affine.equation_iff` followed by those coefficient simp lemmas. This is exactly
the duplicated `General*`/`PID*` fork-of-mathlib layer the project-context note anticipated:
`curveK` (and its `ℤ/ℚ` twin `curveQ` in `GeneralCurve.lean`) is a project-local *renaming* of an
existing mathlib definition, not new mathematical content. Several call sites already
`simp [curveK]` / `unfold curveK` straight back to `W.map (...)`, demonstrating the alias is a
thin wrapper rather than a sealing abstraction.

**WHY not (refactor-actionable):**
Mathlib already has this as **`WeierstrassCurve.baseChange`**.
  - Existing mathlib decl:        `WeierstrassCurve.baseChange`
  - Located at:                   `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`
  - General form (ring hom):       `WeierstrassCurve.map` at `Weierstrass.lean:231`
  - Coefficient lemmas (replace `curveK_aᵢ`): `WeierstrassCurve.map_a₁ … map_a₆` (auto from `@[simps]`)
  - Our form follows in 0 lines (definitional equality):
    ```lean
    example (R K : Type*) [CommRing R] [Field K] [Algebra R K] (W : WeierstrassCurve R) :
        LutzNagell.PID.curveK R K W = W.baseChange K := rfl
    ```
  - Call sites in our project (Phase 6.0):  K ≈ 40 across PIDMain / PIDPrimeOrder / PIDIntegralMultiple.

  Refactor plan:
  1. Delete `curveK` and its five `curveK_aᵢ` lemmas and `curveK_equation_iff` from
     `PIDCurve.lean` (and, by symmetry, `curveQ` + its lemmas from `GeneralCurve.lean`).
  2. At each of the ~40 call sites, replace `curveK R K W` with `W.baseChange K`
     (equivalently the notation `W⁄K`). Same term, so no proof changes are forced by the
     substitution itself.
  3. Replace `curveK_a₁ … curveK_a₆` rewrites with `WeierstrassCurve.map_a₁ … map_a₆`
     (note: stated about `W.map f`; since `baseChange = map (algebraMap …)`, they fire directly
     — confirm `simp` picks them up, otherwise add a one-line
     `baseChange_a₁ := map_a₁` shim, but mathlib's `map_aᵢ` should suffice).
  4. Replace `curveK_equation_iff` uses with `WeierstrassCurve.Affine.equation_iff` followed by
     the `map_aᵢ` simp set (this is literally the project's own proof of `curveK_equation_iff`).
  5. Sites that already `simp [curveK]` / `unfold curveK` (`PIDPrimeOrder.lean:145`,
     `PIDIntegralMultiple.lean:74`) become `simp [WeierstrassCurve.baseChange]` /
     `[WeierstrassCurve.map]` (or drop the unfold entirely if the `map_*` simp lemmas already close it).

  Caveat for the refactor: this is a *cleanup-track* dedup against mathlib, and the file lives
  under `projects/<P>/` in a fork of `Mathlib.AlgebraicGeometry.EllipticCurve.*`. Per AINTLIB
  rules, do it on `main` via a `lane:cleanup` ticket; keep it sorry-free and re-check
  `#print axioms`. The substitution is mechanical (definitional equality), so risk is low, but
  the ~40 sites mean it is non-trivial in *size* — worth a dedicated ticket rather than a drive-by.

**Next action:** delete `LutzNagell.PID.curveK` (and `curveK_a₁..a₆`, `curveK_equation_iff`);
replace its ~40 call sites with `WeierstrassCurve.baseChange W K` (notation `W⁄K`) and mathlib's
`map_aᵢ` / `Affine.equation_iff`. Mirror the same dedup for `curveQ` in `GeneralCurve.lean`.

---

## Sources

- mathlib4 docs — `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.html
- Direct mathlib source read: `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:231,236,240`
- Wikipedia — Nagell–Lutz theorem: https://en.wikipedia.org/wiki/Nagell%E2%80%93Lutz_theorem
- arXiv:2302.10640 — "An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves in any Characteristic": https://arxiv.org/pdf/2302.10640
