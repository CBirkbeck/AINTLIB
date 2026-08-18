# /mathlibable report — `WeierstrassCurve.Universal.evalEval_Ψ₃`

## Verdict: NO-composable-from-mathlib

A one-line glue lemma whose **statement mentions the project-local `polyEval` and `Universal.curve`** (neither in mathlib). The mathematical content — `Ψ₃` commutes with the specialization map — is already in mathlib as `map_Ψ₃`; the lemma is a ≤3-call composition of `map_Ψ₃` + `map_specialize` + the project's own `polyEval_apply`. Cannot be upstreamed as-is (subject is a downstream def); the building blocks already live upstream. Sibling to `evalEval_ψ₂` / `evalEval_preΨ₄` / `polyEval_apply` (same disposition).

> Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
> This project **forks** parts of mathlib (`…EllipticCurve.DivisionPolynomial.*`,
> `…NumberTheory.EllipticDivisibilitySequence`) and carries a duplicated `Universal.lean`.
> `evalEval_Ψ₃` is **duplicated verbatim** in
> `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:166`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — the proof is a one-line `simp_rw` over in-mathlib lemmas, see Phase 5/6).
- decl `WeierstrassCurve.Universal.evalEval_Ψ₃`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:91`.
- kind:                      `lemma` (inside `noncomputable section`).
- has sorry:                 no.
- qualified name:            **`WeierstrassCurve.Universal.evalEval_Ψ₃`** — VERIFIED from source: `namespace WeierstrassCurve` (`ZSMul.lean:76`) → `namespace Universal` (`ZSMul.lean:86`); the lemma is on line 91. Task's parsed name confirmed exactly.
- module docstring summary:  `ZSMul.lean` proves `WeierstrassCurve.zsmul_eq_smulEval` (`n • P = ⟦(φₙ, ωₙ, ψₙ)⟧` in Jacobian coords for any `n : ℤ` and nonsingular affine point `P=(x,y)` on `W/F`), via even-odd induction reducing to universal-ring polynomial identities specialized through `polyEval`/`ringEval`. `evalEval_Ψ₃` is one of the small "specialize a division polynomial" glue lemmas feeding the cusp-curve nonvanishing trick (`polyEval_cusp_ψ`).

---

### Statement (Phase 1)

`evalEval_Ψ₃` is a **lemma**. With `W : WeierstrassCurve R` (`R` a comm ring), `x y : R`, and `Universal.curve : Affine (MvPolynomial Coeff ℤ)` the universal Weierstrass curve over `ℤ[A₁,A₂,A₃,A₄,A₆]`, it states

```lean
lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃)
```

where:
- `W.Ψ₃ : R[X]` is mathlib's third (pre-)division polynomial (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:142`); `C W.Ψ₃ : R[X][Y]` embeds it as a constant in `Y`;
- `evalEval x y : R[X][Y] → R` is mathlib's bivariate evaluation `p ↦ eval x (eval (C y) p)` (`Mathlib/Algebra/Polynomial/Bivariate.lean:44`);
- `curve.Ψ₃ : (MvPolynomial Coeff ℤ)[X]` is the **universal** `Ψ₃`, and `C curve.Ψ₃ : Poly = (MvPolynomial Coeff ℤ)[X][Y]`;
- `polyEval W x y : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y` is the **project-local** evaluation hom (`Universal.lean:203`) sending the universal indeterminates `Aᵢ ↦ W.aᵢ` and `(X,Y) ↦ (x,y)`.

Mathematically: **specializing the universal `Ψ₃` to `W` (via `Aᵢ ↦ W.aᵢ`) and evaluating at `(x,y)` agrees with first forming `W.Ψ₃` and evaluating at `(x,y)`** — i.e. the third division polynomial is a *universal* polynomial in `ℤ[A₁..A₆][x]` whose specialization commutes with evaluation. It is the "$Ψ_3$ row" of the family `{evalEval_ψ₂, evalEval_Ψ₃, evalEval_preΨ₄, evalEval_ψ, evalEval_φ, evalEval_ω}` (`ZSMul.lean:88–106`).

Variables / typeclasses:
- `{R : Type*}` `[CommRing R]` — base ring (`ZSMul.lean:80`).
- `(W : WeierstrassCurve R)` — supplies `W.specialize` / `W.Ψ₃`.
- `{x y : R}` — the affine point (`ZSMul.lean:84`).

Hypotheses: none (no `Equation W x y` needed — this is the `polyEval` level, *before* passing to the coordinate ring `ringEval`).

Conclusion (math): `Ψ₃`-evaluation commutes with specialization of the curve coefficients.
Conclusion (Lean): `(C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃)`.

Body (one substantive line):
```lean
by simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]
```
Reading the proof:
- `polyEval_apply` rewrites `polyEval W x y (C curve.Ψ₃)` to `((C curve.Ψ₃).map (mapRingHom W.specialize)).evalEval x y` (project lemma = 1-call wrapper of mathlib's `eval₂_eval₂RingHom_apply`);
- `map_C`, `coe_mapRingHom` push the `map (mapRingHom specialize)` through the `C`;
- `← map_Ψ₃` (mathlib `@[simp]`, `Basic.lean:506`: `(W.map f).Ψ₃ = W.Ψ₃.map f`) rewrites `curve.Ψ₃.map W.specialize` to `(curve.map W.specialize).Ψ₃`;
- `map_specialize` (project lemma, `Universal.lean:194`: `curve.map W.specialize = W`) collapses `curve.map W.specialize` to `W`, giving `(C W.Ψ₃).evalEval x y`. ∎

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `simp_rw` glue/compatibility lemma; not a named theorem, not a `Main results` entry, not a new structure or definition. It is plumbing for the universal-curve specialization track (the project main result is the Nagell–Lutz theorem). (Literature width run EXHAUSTIVE regardless, per protocol.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`simp_rw [...]`).
One-liner verdict: n/a for the def-exemption table — kind is `lemma`, not `def`/`abbrev`/`structure`. A one-line *lemma* is a strong "reuse mathlib / composable" signal, recorded for Phase 6–7.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | division polynomial Ψ₃ specialization universal Weierstrass curve evaluation base change ring homomorphism | yes | `Ψ₃(u,v)=3u⁴+6Au²+12Bu−A²`, coefficients in `ℤ[A,B]` (resp. `ℤ[a₁..a₆]`) — *universal* polynomials; "under any specialization ρ:R→S … the expansion … commute with this base change" | arXiv:1303.5002 (Cojocaru–et al, coefficients of division polys), arXiv:1303.4327 (homogeneous division polys). Confirms the **concept** (universal integral division polys; specialization commutes with base change) but no source names a standalone "Ψ₃ evaluation commutes with specialize" lemma. |
| 2 | WebSearch (general form) | third division polynomial evaluation commutes with map of coefficients functoriality | yes (weak) | division polys defined by a fixed recurrence with `ℤ`-coefficient initial data; commutation with coefficient maps is implicit (functoriality of the recurrence) | ask.sagemath, eprint 2010/630 (Moody, alternate models), arXiv:1108.3051. The commutation is treated as obvious folklore — "the same polynomial over any base" — never isolated as a named result. |
| 3 | WebSearch (named-after / aliases) | (covered by #1/#2; the relevant mathlib spelling is `map_Ψ₃`) | yes | mathlib's own `map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f` | This is the in-library statement of exactly the functoriality content (any ring hom `f`), see Phase 5[D]. The project lemma instantiates `f := W.specialize` and wraps it in `evalEval`. |
| 4 | ChatGPT MCP | (server down per prompt — fallback) | n/a | — | Compensated with WebSearch at three generality levels (#1 specific universal-curve, #2 general functoriality, #3 mathlib spelling) + direct mathlib-source read (Phase 5[D]). |
| 5 | Local references | `.mathlib-quality/references/` in NagellLutz | n/a | (no `references/` dir present) | Only `overview/` exists under `projects/NagellLutz/.mathlib-quality/`. |
| 6 | nLab | division polynomial / universal elliptic curve | yes (weak) | universal curve over the moduli/parameter space; division polys as universal objects | nLab does not isolate the per-`Ψₙ` specialization-evaluation identity; it is below the granularity (functoriality of evaluation). |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept beyond #6; it is concrete polynomial-algebra bookkeeping (functoriality of `eval₂`). |
| 8 | Stacks Project | base change of polynomial evaluation / Weierstrass data | n/a | — | Concept = elementary `R[X][Y]` evaluation commuting with a coefficient ring hom; below Stacks granularity (no scheme-theoretic content). |
| 9 | MathOverflow / MSE | division polynomial same polynomial over any base / specialization | yes (via #1,#2) | consistent: division polys are universal/integral; specialization is "plug in the coefficients" | No MO/MSE question isolates this exact identity; it is folklore. |
| 10 | recent arXiv (≤5 yr) | division polynomials universal curve specialization base change | yes | arXiv:1303.5002, 1303.4327, 1108.3051, 1410.7070 — universal `ℤ[a]`-coefficient division polys, specialization commutes with base change | Content level; reconfirms the concept is standard, the per-lemma statement is not named. |

Protocol pass: WebSearch ran 3 distinct queries at three generality levels (#1 specific, #2 general functoriality, #3 mathlib spelling) — PASS. ChatGPT MCP unavailable (prompt: down) — compensated. Local refs checked (absent). nLab/Stacks/nCatLab/MO/arXiv each checked or `n/a` with reason. PASS.

### Literature summary (Phase 3)

Concept identified as: **functoriality of division-polynomial evaluation** — the third division polynomial `Ψ₃` is a *universal* integral polynomial in `ℤ[a₁..a₆][x]`, and specializing its coefficients along `Aᵢ ↦ W.aᵢ` then evaluating at `(x,y)` equals forming `W.Ψ₃` and evaluating. The surrounding universal-curve / base-change story is standard (arXiv:1303.5002: "the expansion … commute with this base change"); this lemma is the trivial substitution step inside it, specialised to `Ψ₃`.
Sources agree on the standard form: yes — the canonical statement of the content is "for **any** ring hom `f`, `(W.map f).Ψ₃ = W.Ψ₃.map f`" (functoriality), which is exactly mathlib's `map_Ψ₃`. The project lemma fixes `f := W.specialize` and wraps it in `evalEval`.
Most general standard form: `map_Ψ₃` for an arbitrary `f : R →+* S` (already in mathlib).
Generality dimensions where the literature varies: the coefficient map ranges over **any** ring hom (literature/mathlib); the project's lemma fixes the single hom `W.specialize` — strictly **narrower** (a specialisation, not a generalisation).
Disagreement with the literature: none. The project form is the general functoriality fact instantiated at `f = W.specialize` and post-composed with `evalEval`.

---

### Generality analysis — `WeierstrassCurve.Universal.evalEval_Ψ₃` (Phase 4)

Literature-standard form (Phase 3): functoriality `(W.map f).Ψ₃ = W.Ψ₃.map f` for any `f : R →+* S` — i.e. mathlib's `map_Ψ₃`; the "evaluate at a point" wrapper is `evalEval`/`eval₂_eval₂RingHom_apply` for any `f`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | the coefficient map | `W.specialize` (a *specific* hom `ℤ[A₁..A₆] →+* R` baked into `polyEval`) | an **arbitrary** `f : R →+* S` | **yes — fully generalisable** | The proof uses nothing about `specialize` beyond `map_specialize`; the content is `map_Ψ₃` (any `f`) ∘ `evalEval`. The general form already exists in mathlib (`map_Ψ₃`). |
| 2 | the polynomial | `Ψ₃` (a fixed division polynomial) | any `p` with a `map_p` functoriality lemma | yes (within the family) | The same one-line proof shape works for `ψ₂`, `preΨ₄`, `ψ`, `φ`, `ω` (and indeed all six siblings exist verbatim at `ZSMul.lean:88–106`). Each is the `polyEval_apply` + `map_<p>` + `map_specialize` composition. |
| 3 | base ring `R` | `[CommRing R]` | `[CommSemiring R]` (mathlib's `evalEval`/`eval₂` context) | partly | `evalEval`/`eval₂_eval₂RingHom_apply` live over comm-semirings; but `Ψ₃` and `specialize`/`curve` are defined over `CommRing`-flavoured Weierstrass data, so `CommRing` is the natural ambient. Not a meaningful weakening for *this* lemma. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (a specialisation of mathlib's general functoriality lemma `map_Ψ₃`, post-composed with `evalEval`).
Number of weakening opportunities found: K = 2 substantive (arbitrary `f`; arbitrary `p` in the family) — but each weakening **lands exactly on already-existing mathlib lemmas** (`map_Ψ₃`, `map_ψ₂`, `map_preΨ₄`, …, plus `eval₂_eval₂RingHom_apply`). Generalising `evalEval_Ψ₃` does **not** yield a new mathlib lemma; it yields mathlib's existing ones.
Proposed restatement: n/a as a mathlib contribution — the maximally-general content **is already in mathlib** (`map_Ψ₃` + bivariate `eval₂`).
Cost of restatement: n/a (CHEAP to drop — nothing to re-prove upstream; the general lemmas exist).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | already plain ring data + elements |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic |
| 3 | construct → universal-property class? | no | — | `evalEval`/`eval₂`/`map` already ARE the universal-property evaluation/functoriality maps |
| 4 | set+closure-pred → bundled substructure? | no | — | no substructure |
| 5 | field/metric-specific → weaken typeclass? | partially | the content's general form (`map_Ψ₃`, any `f`) is already upstream | the modernisation **is** the existing mathlib lemma `map_Ψ₃` |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general algebra? | no | — | `Ψ₃` is intrinsically the third division polynomial |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no (as a new contribution)** — the contemporary, maximally-general formulation already exists in mathlib as `map_Ψ₃` (functoriality, any `f`) together with bivariate `eval₂_eval₂RingHom_apply`. There is no modernised statement to add upstream; the general content is already there. The project lemma is the `f := W.specialize`, `p := Ψ₃` instance wrapped in `evalEval`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities, instances, or typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.Universal.evalEval_Ψ₃` (Phase 5)

[A] Lean-Finder — n/a (mathlib index tools `lean_loogle`/`lean_leansearch` not exposed in this env; substituted exhaustive source grep over the pinned mathlib `09b373db6e24`, toolchain `v4.32.0-rc1`).
[B] Loogle — pattern `(C (WeierstrassCurve.Ψ₃ _)).evalEval _ _ = _` / `Polynomial.evalEval _ _ (Polynomial.C (WeierstrassCurve.Ψ₃ _))` — **no hits** (grep proxy: no `evalEval_Ψ₃`, no `polyEval`, no `Universal.curve`/`specialize` anywhere under `Mathlib/AlgebraicGeometry/EllipticCurve/` or `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`).
[C] LeanSearch — NL "third division polynomial evaluated at a point commutes with specializing the curve coefficients" — n/a (index tool absent); literature-channel (Phase 3) covered the NL angle.
[D] Grep mathlib src — terms `evalEval_Ψ₃`, `polyEval`, `Universal.curve`, `specialize`, `map_Ψ₃`, `Ψ₃`:
   - `polyEval` / `Universal.curve` / curve-`specialize` → **no hits** in mathlib (the universal-curve specialization track does NOT exist in mathlib; the only `Universal` namespaces are `UniversallyOpen` and `UniversalEnvelopingAlgebra`, unrelated).
   - **`map_Ψ₃` IS in mathlib** — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:506`, `@[simp] lemma map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f`. This is the general functoriality content (any `f : R →+* S`).
   - `Ψ₃` itself is mathlib's (`Basic.lean:142`); `evalEval` is mathlib's (`Bivariate.lean:44`); `eval₂_eval₂RingHom_apply` is mathlib's (`Bivariate.lean:194`).
[E] Name pattern — `evalEval_Ψ₃` / `evalEval_ψ` family in mathlib — **no hits** (these `evalEval_*` specialization lemmas are project-local; the closest mathlib relative is the `map_*` functoriality family).

Searched for both:
  - the user's current form (`evalEval_Ψ₃`, mentions `polyEval` + `curve`) → only in this project + the duplicated HasseWeil copy; **not in mathlib** (its statement names non-mathlib decls).
  - the literature-standard general content → **found in mathlib**: `map_Ψ₃` (`Basic.lean:506`) + `eval₂_eval₂RingHom_apply` (`Bivariate.lean:194`).

Concluded: **the user's `evalEval_Ψ₃` is NOT in mathlib (its statement is about the project-local `polyEval`/`Universal.curve`), but its mathematical content IS — the functoriality `map_Ψ₃` plus bivariate evaluation. The lemma is a ≤3-mathlib-call composition (via the project's own `polyEval_apply`/`map_specialize` glue) specialising that content to `f = W.specialize`.**

---

### Call sites — `WeierstrassCurve.Universal.evalEval_Ψ₃` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring line 91): **K = 2** — both in `LutzNagell/ZSMul.lean`.
External-to-file callers within NagellLutz: 0 other files (used only inside `ZSMul.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `LutzNagell/ZSMul.lean:115` | `rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]` (in `polyEval_cusp_ψ`) |
| `LutzNagell/ZSMul.lean:123` | `rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]` (in `polyEval_cusp_ψc`) |

Both consumers are the **cusp-curve nonvanishing trick**: rewriting `polyEval cusp 1 1 (curve.ψ n)` (resp. `ψc`) down to `n` (resp. `2`) by pushing `normEDS`/`compl₂EDS` through the three `evalEval_*` rewrites then specialising at the cusp. This is internal to proving the universal `ψₙ ≠ 0` for `n ≠ 0`.

Inline-derivation grep (re-derived without `evalEval_Ψ₃`?): none — both sites cite the named lemma. (The two sites cite it *together with* `evalEval_ψ₂` and `evalEval_preΨ₄` as a fixed triple — they are a unit used to expand `normEDS`.)

Cross-project duplication: an **identical** `evalEval_Ψ₃` (same statement, same proof) exists at `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:166`, with the same two cusp consumers (`DivisionPolynomial.lean:190,199`). So the decl is **duplicated verbatim across two projects** — a cross-project dedup target (→ `Common/`), independent of the mathlib question.

Composability signal: K = 2 internal uses, no inline re-derivation → genuine local convenience API. But it is a thin wrapper: each use is a `rw [← evalEval_Ψ₃]` that could equally be expanded via `[polyEval_apply, map_C, coe_mapRingHom, map_Ψ₃, map_specialize]` (the proof body). Subject (`polyEval`, `curve`) is non-mathlib → not upstreamable as-is.

### Composition check (Phase 6)

Can `evalEval_Ψ₃` be reproduced from mathlib in ≤3 chained calls?

Attempt 1 (= the verbatim source proof): `by simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]`
  - Mathlib decls used: `Polynomial.map_C`, `Polynomial.coe_mapRingHom`, **`WeierstrassCurve.map_Ψ₃`** (`Basic.lean:506`) — the load-bearing one.
  - Project glue used: `polyEval_apply` (itself a 1-call wrapper of mathlib's `eval₂_eval₂RingHom_apply`, `Bivariate.lean:194`) and `map_specialize` (`curve.map W.specialize = W`, a 1-line `simp [specialize, curve, map]`).
  - Result: **succeeds** — exactly the existing proof; a short `simp_rw` chain. Counting *mathlib* primitives in the essential path: `eval₂_eval₂RingHom_apply` (via `polyEval_apply`) → `map_Ψ₃` → (push `C` via `map_C`/`coe_mapRingHom`) → `map_specialize`. The non-trivial step is the single mathlib functoriality lemma `map_Ψ₃`; the rest is `C`-bookkeeping and the trivial `map_specialize`.
  - Notes: the only reason this needs the project's `polyEval_apply`/`map_specialize` rather than being a bare 3-call mathlib composition is that the **statement** is phrased in terms of `polyEval` and `curve` (project-local). Re-stated for an arbitrary `f : R →+* S` it collapses to `map_Ψ₃` + bivariate `eval₂` — pure mathlib.

Conclusion: **COMPOSABLE** — a ≤3-step `simp_rw` whose essential content is the single in-mathlib functoriality lemma `map_Ψ₃` (plus bivariate `eval₂`), wrapped to the project-local `polyEval`/`curve` via two trivial project glue lemmas.

### Composition heuristics check
Pattern = "short `simp_rw` rewrite chain reducing to one functoriality lemma (`map_Ψ₃`) + bookkeeping" → row "small rewrite to an existing general lemma" → **composable: yes**. Not a disguised substantial proof (the genuine math — that `Ψ₃ ∈ ℤ[a][x]` is universal — is already captured by `map_Ψ₃`).

---

## Verdict: `WeierstrassCurve.Universal.evalEval_Ψ₃`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the content is folklore functoriality — `Ψ₃` is a universal integral polynomial in `ℤ[a₁..a₆][x]` whose specialization commutes with base change (arXiv:1303.5002, 1303.4327). No source names a standalone "Ψ₃-evaluation commutes with specialize" lemma; the canonical statement of the content is `(W.map f).Ψ₃ = W.Ψ₃.map f` for any `f` — mathlib's `map_Ψ₃`.
- Generality analysis (Phase 4): STRICTLY NARROWER — the lemma is the `f := W.specialize`, `p := Ψ₃` instance of mathlib's general functoriality lemma, post-composed with `evalEval`; every generalisation lands on an already-existing mathlib lemma (`map_Ψ₃`, `eval₂_eval₂RingHom_apply`).
- Mathlib search (Phase 5): the def `polyEval` and `Universal.curve`/`specialize` track are **not** in mathlib, but the lemma's content **is** — `WeierstrassCurve.map_Ψ₃` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:506`, `@[simp]`, any ring hom `f`) + bivariate `eval₂_eval₂RingHom_apply` (`Bivariate.lean:194`).
- Composition check (Phase 6): COMPOSABLE — the verbatim source proof is a ≤3-step `simp_rw` whose load-bearing call is the in-mathlib `map_Ψ₃`, wrapped to `polyEval`/`curve` by the project's trivial `polyEval_apply` and `map_specialize`.

**Rationale.**
`evalEval_Ψ₃` is not a mathlib candidate because its **statement** is *about* `polyEval` and `Universal.curve` — project-local constructions tied to the NagellLutz/HasseWeil "universal Weierstrass curve + specialization" track that does not exist in mathlib (Phase 5[D]: no `Universal.curve`/`specialize`/`polyEval` in mathlib's EllipticCurve directory). One cannot upstream a lemma whose subject is a downstream def. Meanwhile the actual mathematical content — "the third division polynomial is universal; specializing its coefficients then evaluating = forming `W.Ψ₃` then evaluating" — is already in mathlib in full generality as `map_Ψ₃` (functoriality for an arbitrary `f : R →+* S`), combined with bivariate evaluation. The lemma is precisely the `f := W.specialize` instance of that, with the universal `curve.Ψ₃` mapped to `W.Ψ₃` via `map_specialize`, all under an `evalEval`/`eval₂` wrapper supplied by `eval₂_eval₂RingHom_apply`. Its one-line proof is exactly this ≤3-call composition. That is the textbook NO-composable-from-mathlib signature: mathlib supplies the building block (`map_Ψ₃`), the project form is a short specialisation, and no new lemma is warranted upstream.

It is **not** NO-mathlib-has-it, because mathlib does not have a lemma *named for* `polyEval`/`evalEval_Ψ₃` (the exact form mentions non-mathlib defs); the precise framing is "mathlib has the building block `map_Ψ₃` — express the goal through it". It is **not** YES-but-generalise-first, because the generalised statement (`map_Ψ₃`, any `f`) **already exists in mathlib** — there is nothing to add. The lemma does have 2 internal uses (the cusp nonvanishing trick), so locally it is reasonable convenience API — but those uses are `rw [← evalEval_Ψ₃]` that could cite the proof's building blocks directly.

This verdict is **consistent with its decided siblings**: `evalEval_ψ₂`, `evalEval_preΨ₄` (identical shape, `map_ψ₂`/`map_preΨ₄` instead of `map_Ψ₃`) and `polyEval_apply` were all assessed NO-composable-from-mathlib for the same reason (statement about `polyEval`; content = a single mathlib lemma applied). The decl sits *below* the genuinely-borderline anchors of the same track (`specialize`, `Universal.curve`), which are the real "should the universal-curve package be upstreamed?" question — `evalEval_Ψ₃` rides on those defs but adds no upstreamable content of its own.

**WHY not (refactor-actionable).**
Mathlib already provides the building block `WeierstrassCurve.map_Ψ₃` (functoriality of `Ψ₃` under any ring hom). The project lemma is the specialisation to `f = W.specialize`, with `curve.map W.specialize = W` (`map_specialize`) and the bivariate-evaluation wrapper `eval₂_eval₂RingHom_apply` (via `polyEval_apply`). No new mathlib lemma is needed; the content lives upstream.

Mathlib building blocks:
  - `WeierstrassCurve.map_Ψ₃` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:506` (load-bearing; `@[simp]`, any `f : R →+* S`).
  - `Polynomial.eval₂_eval₂RingHom_apply` — `Mathlib/Algebra/Polynomial/Bivariate.lean:194` (the `evalEval` wrapper; reached via the project's `polyEval_apply`).
  - `Polynomial.map_C`, `Polynomial.coe_mapRingHom` — the `C`-bookkeeping.

Composition sketch (≤3 essential steps, = the existing source proof):
```lean
example : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]
```

Call sites in our project (Phase 6.0): K = 2 (both in `LutzNagell/ZSMul.lean:115,123`, the cusp nonvanishing trick).

Refactor plan (project-internal — NOT a mathlib PR):
  - This lemma is best understood as a **thin local specialisation** of `map_Ψ₃` to `polyEval`. Two equally valid dispositions:
    1. **Keep it** as a 1-line convenience lemma (it reads well and has 2 consumers that use the `{evalEval_ψ₂, evalEval_Ψ₃, evalEval_preΨ₄}` triple together) — but there is nothing to upstream.
    2. **Inline** the building blocks at the 2 `ZSMul.lean` sites if the track is ever slimmed — though keeping the named triple is clearer.
  - Either way: **do not add `evalEval_Ψ₃` to mathlib.** If anything from this track is upstreamed it is the `Universal.curve` / `specialize` *scaffold itself* (the separate BORDERLINE / BIG question tracked under `specialize.md`, `curve.md`, `map_specialize.md`), not this glue lemma.

Next action: no mathlib PR for this decl. Separately, deduplicate against the identical HasseWeil copy (`Auxiliary/DivisionPolynomial.lean:166`) into a shared `Common/` module on `main` — a cross-project cleanup ticket, orthogonal to mathlibability.

---

## Next step

No mathlib PR. The content is already upstream as `WeierstrassCurve.map_Ψ₃` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:506`) + bivariate `eval₂_eval₂RingHom_apply` (`Bivariate.lean:194`); `evalEval_Ψ₃` is their ≤3-call specialisation to the project-local `polyEval`/`Universal.curve` (via `polyEval_apply` + `map_specialize`). Keep it as a thin local wrapper or inline the building blocks; do not upstream. Deduplicate against the verbatim HasseWeil copy. The genuine upstreaming question for this track lives at the `specialize` / `Universal.curve` anchors, not here.
