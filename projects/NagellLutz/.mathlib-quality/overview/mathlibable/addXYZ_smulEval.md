# /mathlibable report — `WeierstrassCurve.addXYZ_smulEval`

## Verdict: NO-composable-from-mathlib (tightly coupled project-internal bridge; see rationale)

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source.
- decl `WeierstrassCurve.addXYZ_smulEval`:  ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:572`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Proves `zsmul_eq_smulEval`: `n • P = ⟦φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y)⟧` in Jacobian coordinates for any integer `n` and nonsingular rational point `P` on a Weierstrass curve over a field.

True qualified name **confirmed from source**: `WeierstrassCurve.addXYZ_smulEval` (inside `namespace WeierstrassCurve`, opened line 76; lemma at line 572). The parsed name was correct.

---

### Statement (Phase 1)

`addXYZ_smulEval` is a **lemma** stating: applying mathlib's Jacobian addition-formula polynomials `addXYZ` to the *evaluated division-polynomial coordinate vectors* of `m • P` and `n • P` (for distinct multiples) returns the coordinate vector of `(n+m) • P`, scaled by the scalar `ψ_{n−m}(P)`:

> `addXYZ W (smulEval W x y m) (smulEval W x y n) = evalEval x y (W.ψ (n − m)) • smulEval W x y (n + m)`

Here `smulEval W x y k = (φ_k(x,y), ω_k(x,y), ψ_k(x,y)) ∈ Fin 3 → R` is the evaluation of the division polynomials `(W.φ k, W.ω k, W.ψ k)` at `(x,y)` (abbrev, line 551), and `addXYZ` is mathlib's un-normalized Jacobian point-addition coordinate map (`Mathlib/.../Jacobian/Formula.lean:661`).

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — base commutative ring.
- `W : WeierstrassCurve R` — the curve.
- `x y : R` — coordinates of an affine point.

Hypotheses (Lean side):
- `eqn : W.toAffine.Equation x y` (an `include`d section hypothesis, line 553) — `(x,y)` lies on the curve.

Conclusion (math): the Jacobian addition-formula output for the `mP` and `nP` coordinate vectors equals `ψ_{n−m}(P)` times the `(n+m)P` coordinate vector.

Conclusion (Lean): `addXYZ W (smulEval W x y m) (smulEval W x y n) = evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m)`.

Proof body (3 steps): `simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]; rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]; simp_rw [curveRing_map_ringEval]`. It transports the **universal-ring** identity `addXYZ_smulRing` down to the evaluated point via the specialization homomorphism `ringEval`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — the evaluated-point image of the universal-ring identity `addXYZ_smulRing`, used to assemble the named main result `zsmul_eq_smulEval`. Not itself a main result and not named after a person/place. (The *named* theorem of this file is `zsmul_eq_smulEval`.) Literature width run EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Body line count: 3 substantive lines. One-liner verdict: **MULTI-LINE** → exemption table skipped. Kind is `lemma`, not a `def`. Phase 4.5 (diamond/defeq) is **n/a**.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomials addition formula ψ_{m+n} ψ_{m−n} multiplication-by-n Jacobian coordinates          | yes  | `nP = [φₙψₙ : ωₙ : ψₙ³]`; recursions for ψ₂ₘ₊₁, ψ₂ₘ | Wikipedia "Division polynomials"; arXiv 1801.02664, eprint 2010/630. Gives the *coordinate* form of `nP`, NOT a vector addition identity with a ψ_{n−m} factor. |
|  2 | WebSearch (general / EDS form)   | EDS addition formula Ward division polynomial ψ recurrence Silverman                                     | yes  | `W_{n+m}W_{n−m} = W_{n+1}W_{n−1}W_m² − W_{m+1}W_{m−1}W_n²` | Ward 1948; EDS Wikipedia. This is the **scalar** (Z-coordinate) shadow of our lemma. |
|  3 | WebSearch (named-after / aliases)| "division polynomial" "n*P" coordinates φ_n ψ_n ω_n multiplication-by-n                                  | yes  | `nP = (φₙ/ψₙ², ωₙ/ψₙ³)`           | Wikipedia; arXiv 1710.05264, 2102.07573. Affine multiplication-by-n; standard. No vector-valued `addXYZ`-scaling identity surfaced. |
|  4 | ChatGPT MCP                      | "is `addXYZ(mP,nP)=ψ_{n−m}•(n+m)P` a named identity or an artifact of the un-normalized addition formula?" | n/a  | —                                | **MCP down** (Codex backend failed — task brief flagged this). Recorded n/a; literature channels are already conclusive. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                      | n/a  | —                                | **Directory absent** for NagellLutz (`.mathlib-quality/references/` does not exist). Recorded n/a. |
|  6 | nLab                             | division polynomial / elliptic divisibility sequence                                                    | n/a  | —                                | nLab has no dedicated division-polynomial / EDS coordinate-formula page; concept is classical-arithmetic, not categorical. |
|  7 | nCatLab (categorical)            | —                                                                                                       | n/a  | —                                | Not a categorical concept — explicit Jacobian-coordinate polynomial identity. |
|  8 | Stacks Project (alg geom)        | division polynomial / Weierstrass point multiplication                                                  | n/a  | —                                | Stacks does not develop explicit division-polynomial coordinate formulas for Weierstrass curves. |
|  9 | MathOverflow / Math.SE           | division polynomial addition formula vector identity scaling factor                                     | yes  | scalar EDS law only              | Discussions reproduce the affine `nP` formula and the scalar EDS recurrence; no "vector addition identity with ψ_{n−m} factor" as a named result. |
| 10 | recent arXiv (≤5 yr)             | elliptic nets addition formula; recurrence for EDS (2102.07573, 2512.09601)                              | yes  | elliptic-net / EDS recurrences   | Stange's elliptic nets generalise EDS; the addition structure appears as net recurrences (scalar), not as a `addXYZ`-coordinate vector identity. |

### Literature summary (Phase 3)

Concept identified as: the **division-polynomial multiplication-by-n coordinate formula** (`nP = ⟦φₙ : ωₙ : ψₙ³⟧` / affine `(φₙ/ψₙ², ωₙ/ψₙ³)`) together with the **elliptic divisibility sequence (Ward 1948) addition law**.
Sources agree on the standard form: **yes** for the two *standard* objects — (i) the coordinate formula for `nP`, and (ii) the scalar EDS relation `W_{n+m}W_{n−m} = W_{n+1}W_{n−1}W_m² − W_{m+1}W_{m−1}W_n²` (full form `W_{n+m}W_{n−m}W_r² = W_{n+r}W_{n−r}W_m² − W_{m+r}W_{m−r}W_n²`).
Most general standard form: the affine/projective `nP` coordinate formula (holds over any field where the curve is defined), plus the scalar EDS bilinear recurrence.
Generality dimensions where the literature varies: base field (ℚ → any field → universal ring, as the project does); normalisation of ω (factor 1/(4y) vs project's integral ω). 
**Disagreement / gap with the literature:** the *exact lemma* `addXYZ_smulEval` — a **vector** identity `addXYZ(mP,nP) = ψ_{n−m}(P) • (n+m)P` carrying the precise scaling factor `ψ_{n−m}` — is **not a named classical statement**. The classical content is the *scalar* EDS law and the *single-point* `nP` coordinate formula. The vector identity, with its specific `ψ_{n−m}` factor, is an **artifact of mathlib's particular un-normalized `addXYZ` polynomial map**: `ψ_{n−m}` is exactly the discrepancy between mathlib's unnormalized `addXYZ` output and the canonical Jacobian representative of `(n+m)P`. Different addition-formula normalisations would carry a different factor. It is the coordinate-level engine that *yields* the classical scalar law, not the classical law itself.

---

### Generality analysis — `WeierstrassCurve.addXYZ_smulEval`

Literature-standard form (from Phase 3): the multiplication-by-n coordinate formula over a field; the scalar EDS addition law.

| # | Parameter / hypothesis              | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|----------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `{R : Type*} [CommRing R]`          | arbitrary commutative ring       | usually a field                  | already general     | The lemma is **already stated over an arbitrary `CommRing`** — strictly more general than the classical field setting. The downstream `zsmul_eq_smulEval` then specialises to a field. No weakening available; this is maximal. |
| 2 | `eqn : W.toAffine.Equation x y`     | point lies on the curve          | point on the curve               | NO                  | The point-on-curve hypothesis is essential and minimal (`Nonsingular` is *not* required at this level — only `Equation`). Already optimal. |
| 3 | indices `m n : ℤ`                   | integer multiples                | `ℤ` (or `ℕ` then extended)       | already general     | Stated for all integer `m, n`. Maximal. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (already over an arbitrary `CommRing`, all integer indices, minimal `Equation` hypothesis).
Number of weakening opportunities found: 0.
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation | Mathlib downstream |
|----|-----------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | bundled hypotheses → typeclasses/instances?                                       | no       | `Equation x y` is already the idiomatic hypothesis | — |
|  2 | sequences/metric → filters/topological?                                           | no       | purely algebraic coordinate identity; no limits | — |
|  3 | construction → universal-property class?                                          | no       | this *is* the construction-level lemma feeding the universal `ringEval` argument | — |
|  4 | set-with-closure → bundled substructure?                                          | no       | no substructure here | — |
|  5 | field/metric-specific → weaken typeclasses?                                       | no       | already over arbitrary `CommRing` (weaker than the field literature) | — |
|  6 | 1-categorical → higher-categorical?                                               | no       | n/a | — |
|  7 | concrete index ℕ/ℤ/ℝ → general monoid/group?                                      | no       | indices are genuinely `ℤ` (point multiples); generalising the index has no meaning | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The lemma is already in the idiomatic mathlib form (arbitrary `CommRing`, `addXYZ`/`smulEval` framed on mathlib's existing Jacobian + division-polynomial API, minimal `Equation` hypothesis). No reorganisation improves it.

---

### Mathlib search-status: `WeierstrassCurve.addXYZ_smulEval`

[A] Lean-Finder       n/a (mathlib index unavailable offline; substituted with source grep over `.lake/packages/mathlib`).
[B] Loogle            type-pattern `WeierstrassCurve.addXYZ _ _ = _ • _` and `smulEval` — n/a offline; grep substitute below.
[C] LeanSearch        "division polynomial evaluation Jacobian coordinates scalar multiple of point" — n/a offline.
[D] Grep mathlib src  `smulEval`, `addXYZ_smulEval`, `smul_eq_divisionPolynomial`, `zsmul_eq`, `divisionPolynomial_eval`, `curveRing`, `smulRing`, `ringEval_comp_smulRing`, `addXYZ_smulRing`, `curveRing_map_ringEval`, `ringEval_ψ`  →  **ALL: no hits** in `Mathlib/`. The `DivisionPolynomial` files do **not import or even mention `Jacobian`** — confirmed there is **no link in mathlib between division polynomials and `Jacobian.Point` scaling**.
[E] Name pattern      grep `*smulEval*` / `*_smulRing*` over mathlib → no hits.

Searched for both:
  - the user's current form (`addXYZ_smulEval`) — **absent**.
  - the literature-standard forms — mathlib has **`addXYZ`, `dblXYZ`, `map_addXYZ`, `map_dblXYZ`, `Jacobian.comp_smul`, `equiv_iff_eq_of_Z_eq`, `add_of_not_equiv`, `addXYZ_self`** (the Jacobian addition/doubling primitives, `Mathlib/.../Jacobian/Formula.lean` + `Point.lean`) and the **division polynomials `φ_n, ω_n, ψ_n`** (`Mathlib/.../DivisionPolynomial/Basic.lean`), but **NOT** the bridge that ties them together (`smulEval`, `nP = ⟦φₙ:ωₙ:ψₙ⟧`, or any `addXYZ_smulEval`-shaped statement).

Concluded: **not in mathlib** (all methods + the literature-standard form exhausted). Mathlib has the *building blocks on each side* but **not** the connecting bridge — and critically, the connecting machinery this lemma is *stated in terms of* (`smulEval` over `Universal.Ring` via `ringEval`/`smulRing`/`addXYZ_smulRing`) does not exist in mathlib.

---

### Call sites — `WeierstrassCurve.addXYZ_smulEval`

Internal use count (NagellLutz, excluding declaring file `ZSMul.lean`): **0**
External-to-file callers: **0** distinct files within NagellLutz.
Cross-project: **1 literal duplicate** — `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:648` declares the identical `addXYZ_smulEval (m n : ℤ)` (same statement, same proof up to a `WeierstrassCurve.` prefix). That copy is also **not consumed** in HasseWeil's `zsmul_eq_smulEval`.

| Caller file:line | Usage pattern |
|------------------|----------------|
| (none within NagellLutz) | — |
| HasseWeil/.../DivisionPolynomial.lean:648 | duplicate *declaration*, not a call site |

Inline-derivation grep: the **specialised** sibling `addXYZ_smulEval₁ (n : ℤ)` (the consecutive `n, n+1` case) is what the main proof `zsmul_eq_smulEval` actually uses (`ZSMul.lean:616`), alongside `dblXYZ_smulEval` (`ZSMul.lean:602`). The general two-argument `addXYZ_smulEval (m n)` is the **general-form companion**: it is *proved* (it is the natural general statement and likely the source of `addXYZ_smulEval₁`) but **`addXYZ_smulEval₁` is stated independently** (via `addXYZ_smulRing₁`, not as a corollary of `addXYZ_smulEval`), so the general lemma currently has **K = 0** live consumers.

Composability signal: **K = 0 internal uses, no inline re-derivation that bypasses it** → matches the "brand-new general API companion / possibly-unused" row. Combined with the literature finding (not a named theorem) and the duplicate-across-projects fact, the case leans NO unless mathlib would want it as the general form behind `addXYZ_smulEval₁`.

---

### Composition check (Phase 6)

Can `addXYZ_smulEval` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: transport the mathlib-side `addXYZ` + `map_addXYZ` + `Jacobian.comp_smul` directly.
  - Mathlib decls available: `Jacobian.comp_smul`, `map_addXYZ`.
  - Result: **fails**. The proof's load-bearing steps are `← ringEval_comp_smulRing`, `← addXYZ_smulRing`, `← curveRing_map_ringEval`, `← ringEval_ψ` — **all four are project-local** (confirmed absent from mathlib). The identity is not "mathlib `addXYZ` lemmas composed"; it is "the **universal-ring** polynomial identity `addXYZ_smulRing` pushed through the specialization map `ringEval`". Neither `smulRing` (the universal `(φ,ω,ψ)` triple in `AdjoinRoot curve.polynomial`) nor `ringEval` nor `addXYZ_smulRing` exists in mathlib.

Attempt 2: derive it from the eventual main theorem `zsmul_eq_smulEval` (`mP, nP, (n+m)P` all equal their `smulEval`, then use mathlib's `add_of_not_equiv`).
  - Result: **circular / not a mathlib composition** — `zsmul_eq_smulEval` is itself the *project's* result (also not in mathlib) and is proved *using* `addXYZ_smulEval₁`/`dblXYZ_smulEval`, the siblings of this lemma. Cannot bootstrap from mathlib alone.

Conclusion: **NOT-COMPOSABLE from mathlib in isolation.** The ≤3-call composition exists only *within the project's own `smulRing`/`ringEval` API stack*, none of which is in mathlib.

---

## Verdict: `WeierstrassCurve.addXYZ_smulEval`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the classical objects are the *scalar* EDS addition law and the *single-point* `nP` coordinate formula; the **vector** `addXYZ`-scaling identity with factor `ψ_{n−m}` is **not a named classical theorem** — it is an artifact of mathlib's un-normalized `addXYZ`.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (arbitrary `CommRing`, all `m,n:ℤ`, minimal `Equation`); no modern-idiom improvement.
- Mathlib search (Phase 5): **not in mathlib**; mathlib has the per-side primitives (`addXYZ`, `φ/ω/ψ`) but neither the `smulEval` bridge nor the `smulRing`/`ringEval`/`addXYZ_smulRing` machinery this lemma is phrased in.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the ≤3-step proof composes *project-local* lemmas (`ringEval_comp_smulRing`, `addXYZ_smulRing`, `curveRing_map_ringEval`, `ringEval_ψ`), all absent upstream.

**Rationale:**

`addXYZ_smulEval` is a **project-internal coordinate-bookkeeping lemma**, not a standalone mathlib-worthy result. Mathematically it is the evaluated-point image of the universal-ring identity `addXYZ_smulRing`, transported via the specialization homomorphism `ringEval` — its only role in the file is to underwrite the named theorem `zsmul_eq_smulEval` (`n • P = division-polynomial coordinates`). The classical literature confirms the *content* it serves (Ward's EDS addition law, the multiplication-by-n coordinate formula) but does **not** contain this exact vector statement: the precise scaling factor `ψ_{n−m}` is the discrepancy between mathlib's specific un-normalized `addXYZ` output and the canonical Jacobian representative, so the identity is tied to mathlib's coordinate-formula *implementation*, not to a theorem mathematicians cite by name.

It is also strictly NOT composable from mathlib *in isolation*: although mathlib supplies `addXYZ`, `map_addXYZ`, and `Jacobian.comp_smul`, the actual proof runs through `addXYZ_smulRing` (a polynomial identity in `Universal.Ring`) and the `smulRing`/`ringEval`/`curveRing_map_ringEval` API — an entire sub-development (the universal division-polynomial ring, its `ringEval` specialization, the `smulRing` triple) that **does not exist in mathlib**. So the "composition" lives wholly inside the project's own forked-and-extended API, not mathlib's.

The honest framing: this lemma should NOT be a separate mathlib PR *on its own*. It belongs to the **`smulEval` → `zsmul_eq_smulEval` package** — the whole "integer multiples of a point are given by division polynomials in Jacobian coordinates" development (authored by Junyan Xu; the file reads as upstream-destined mathlib material). When that package is upstreamed, `addXYZ_smulEval` rides along as a **private/internal step** of it (very plausibly even folded into the proof of `addXYZ_smulEval₁`, which is the only variant `zsmul_eq_smulEval` consumes), not as an independently-stated public API lemma. Standalone, it is NO-composable-from-mathlib.

**WHY not (refactor-actionable):**
Mathlib has the building blocks **on each side** but not the bridge, and the bridge's prerequisites are absent, so this is "composable only within the project's own machinery" — i.e. NO-composable-from-mathlib (it should be inlined/internalised, not shipped as a public lemma).
- Mathlib building blocks (per side): `WeierstrassCurve.Jacobian.addXYZ` (`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:661`), `…Jacobian.map_addXYZ` (`Formula.lean:771`), `…Jacobian.comp_smul` (`Jacobian/Basic.lean:147`), and the division polynomials `WeierstrassCurve.ψ/φ/ω` (`Mathlib/.../DivisionPolynomial/Basic.lean`).
- **Missing upstream (why no clean mathlib composition):** `smulEval`, `smulRing`, `ringEval`, `addXYZ_smulRing`, `curveRing_map_ringEval`, `ringEval_ψ`, `ringEval_comp_smulRing` — all project-local (grep over `Mathlib/` returns NONE for each).
- Composition sketch (the actual ≤3 steps — **note they are project-local, not mathlib**):
  ```lean
  -- (project-internal; NOT a mathlib one-liner)
  example (eqn : W.toAffine.Equation x y) (m n : ℤ) :
      addXYZ W (smulEval W x y m) (smulEval W x y n)
        = evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
    simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
    rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]   -- comp_smul, map_addXYZ are mathlib; addXYZ_smulRing is project-local
    simp_rw [curveRing_map_ringEval]                              -- project-local
  ```
- Call sites in NagellLutz (from Phase 6.0): **K = 0** (plus 1 literal duplicate in HasseWeil, also unused).

**Refactor plan (project-internal, NOT a mathlib deletion):** This is fleet-cleanup guidance, not a mathlib action. (1) Because `addXYZ_smulEval` has **0 consumers** while its specialisation `addXYZ_smulEval₁` (proved independently via `addXYZ_smulRing₁`) is the one `zsmul_eq_smulEval` actually uses, consider either (a) **deriving `addXYZ_smulEval₁` from `addXYZ_smulEval`** (substitute `m := n`, `n := n+1`, then `ψ₁ = 1`) so the general lemma earns its keep, or (b) if `addXYZ_smulEval₁`'s direct proof is preferred, **down-scope `addXYZ_smulEval`** (it is currently dead general-form API). (2) **De-duplicate across projects**: the identical lemma in `HasseWeil/Auxiliary/DivisionPolynomial.lean:648` and this one should be refactored into one shared `Common/` location (this is an AINTLIB cross-project dedup ticket, exactly the kind CLAUDE.md calls out). (3) When the `smulEval`/`zsmul_eq_smulEval` package is upstreamed to mathlib, `addXYZ_smulEval` goes **as an internal step of that PR**, not as a standalone public lemma.

Next action: do **not** open a standalone mathlib PR for this lemma. File an AINTLIB **cleanup/dedup ticket** to merge the NagellLutz + HasseWeil copies (and decide whether `addXYZ_smulEval₁` should derive from it). If/when the surrounding `zsmul_eq_smulEval` development is proposed for mathlib, include `addXYZ_smulEval` as a private/internal lemma of that contribution (run `/mathlibable WeierstrassCurve.zsmul_eq_smulEval` and `/mathlibable WeierstrassCurve.smulEval` to assess the package as a whole — `smulEval` is the BIG anchor decl).

---

## Next step

Do not open a standalone mathlib PR. File an AINTLIB cross-project dedup ticket (NagellLutz `ZSMul.lean:572` ↔ HasseWeil `DivisionPolynomial.lean:648`) and revisit `addXYZ_smulEval` as an internal step when the `smulEval`/`zsmul_eq_smulEval` package is upstreamed; assess that package via `/mathlibable WeierstrassCurve.smulEval` (the BIG anchor).
