# /mathlibable report — `WeierstrassCurve.addXYZ_smulEval₁`

## Verdict: BORDERLINE-needs-human

One-line: Genuine mathlib gap (no division-poly ↔ point-group bridge upstream), but
this is an intermediate rung of the `zsmul_eq_smulEval` tower; packaging/scaffolding
is a human call, and it must ship as a batch, not solo.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note; reasoned from source)
- decl `WeierstrassCurve.addXYZ_smulEval₁`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:580`
- kind:                     lemma (theorem)
- has sorry:                no
- module docstring summary: Proves `zsmul_eq_smulEval`: integer multiples of a
  nonsingular rational point on a Weierstrass curve, in Jacobian coordinates, are
  given by evaluating division polynomials (`smulEval`).

Qualified name verified: namespace `WeierstrassCurve` opens at line 76; the inner
`Universal` (86) and `Jacobian` (395) namespaces both **close** (`end Jacobian` 544,
`end Universal` 546) *before* the lemma at line 580. So the true qualified name is
`WeierstrassCurve.addXYZ_smulEval₁` — the parsed name in the prompt is correct.

---

### Statement (Phase 1)

`addXYZ_smulEval₁` states: for a Weierstrass curve `W` over a field `F`, a point `(x,y)`
satisfying the affine equation, and `n : ℤ`,

  addXYZ W (smulEval W x y n) (smulEval W x y (n+1)) = smulEval W x y (2n+1)

where `smulEval W x y n = evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]` is the triple of
division-polynomial evaluations giving the Jacobian coordinates of `n • (x,y)`, and
`addXYZ` is mathlib's Jacobian-coordinate point-addition formula.

Mathematically: **the Jacobian-coordinate sum of the `n`-th and `(n+1)`-th multiples of
a point equals the `(2n+1)`-th multiple** — the projective-coordinate incarnation of the
classical odd-index division-polynomial addition law `ψ₂ₙ₊₁ = ψₙ₊₂ψₙ³ − ψₙ₋₁ψₙ₊₁³`
(more precisely, the `m = n+1` specialisation of the general two-point addition law,
where the `ψ(n+1 − n) = ψ(1) = 1` factor drops out, so no scaling is needed).

Variables / typeclasses:
- `{F : Type*} [Field F]` — base field (set at line 584; field needed for the affine point group).
- `(W : WeierstrassCurve F)` — the curve.
- `{x y : F}`, `(eqn : W.toAffine.Equation x y)` — a point on the affine model (proof uses `eqn`).
- `(n : ℤ)` — the index.

Conclusion (Lean): an equality of `Fin 3 → F` (Jacobian coordinate triples).

---

### Size classification (Phase 2a)

Verdict: SMALL.
Reason: helper lemma — an intermediate step (one of the three reductions named in the
module docstring: `dblXYZ_smulEval` and `addXYZ_smulEval₁`) toward the main result
`zsmul_eq_smulEval`. Not itself a named theorem; it is the odd-step recursion rung.

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`. One-line check skipped (n/a). The 1-line *proof* body
(`simp_rw [...]`) is noted in Phase 6 — it is pure transport, but transport across
**project-only** infrastructure.

---

### Literature search (Phase 3)

| #  | Channel             | Query | Hit? | Standard form found | Notes |
|----|---------------------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | division polynomials Jacobian coords point multiplication ψ φ ω 2n+1 | partial | `[n]P` rational map via ψₙ; Jacobian (X,Y,Z)=(x,y) with x=X/Z², y=Y/Z³ | MIT 18.783 Lec 6; the Jacobian-projective add/double formulas are standard ECC material |
| 2 | WebSearch (general)  | EDS addition formula ψ(2n+1) doubling Nagell-Lutz division polynomial | yes | `ψ₂ₙ₊₁ = ψₙ₊₂ψₙ³ − ψₙ₋₁ψₙ₊₁³`; general `ψₘ₊ₙψₘ₋ₙψᵣ² = …`; `[n]P=((xψₙ²−ψₙ₋₁ψₙ₊₁)/ψₙ², …)` | Wikipedia "Division polynomials" / "Elliptic divisibility sequence"; arXiv 2102.07573 |
| 3 | WebSearch (aliases)  | (covered by #1/#2) — "scalar multiplication", "shift", "EDS" | yes | same law under EDS naming | name varies (division poly vs EDS) but identical content |
| 4 | ChatGPT MCP          | — | n/a | — | MCP down per task note; substituted by extra WebSearch + Silverman knowledge (AEC Ex. 3.7 / §III). The `[n]` map via division polynomials and its odd/even recursion is textbook-standard. |
| 5 | Local references     | grep `.mathlib-quality/references/` | n/a | — | no references dir under this project's `.mathlib-quality/`; the source PDF is the known unpublished "Lutz–Nagell" note this file formalises |
| 6 | nLab                 | "division polynomial" / "elliptic divisibility sequence" | n/a | — | not an nLab topic (concrete arithmetic, not categorical) |
| 7 | nCatLab              | — | n/a | — | not a categorical concept |
| 8 | Stacks Project       | division polynomial | n/a | — | Stacks does not cover explicit division-polynomial arithmetic |
| 9 | MathOverflow/MSE     | division polynomial Jacobian coordinate multiplication | partial | confirms ECC-standard | same content; cryptographic-implementation framing |
| 10 | arXiv (recent)      | division polynomials / EDS recurrence (2021–2025) | yes | arXiv 2102.07573, 2503.15428 | confirms the recurrence is actively used; no Lean/Jacobian-bridge statement |

### Literature summary (Phase 3)

Concept identified as: the **odd-index recursion of the elliptic-curve multiplication-by-`n`
map**, expressed in Jacobian (weighted-projective) coordinates — equivalently the odd
case of the elliptic-divisibility-sequence / division-polynomial addition law.

Sources agree on the standard form: yes — `ψ₂ₙ₊₁ = ψₙ₊₂ψₙ³ − ψₙ₋₁ψₙ₊₁³` and the
multiplication map `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` are universally stated (Silverman AEC III;
Wikipedia; MIT 18.783; arXiv).

Most general standard form: the **two-point** law `addXYZ(eval m, eval n) = ψ(n−m) • eval(n+m)`
(this is the project's `addXYZ_smulEval`, line 572). `addXYZ_smulEval₁` is its `m = n, →` the
`n, n+1` specialisation where `ψ(1)=1` removes the scaling.

Generality dimensions where the literature varies:
  - coefficient ring: the *polynomial identity* holds over the universal/any commutative
    ring (the project proves this as `addXYZ_smulRing₁` over `Universal.Ring`). The
    *evaluation-at-a-point* statement naturally lives over a field (point group).
  - index: stated for `ℤ`; here `ℤ`. No generalisation axis.

Disagreement with the literature: none — the Lean form is a faithful, slightly specialised
(`m = n+1`) Jacobian-coordinate rendering of the standard law.

---

### Generality analysis (Phase 4)

Literature-standard form: two-point addition law over a ring (poly identity) / field
(evaluation). This lemma is the `(n, n+1)` specialisation.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[Field F]` | base field | field (for point group) / ring (for poly identity) | NO (at this layer) | `smulEval`/`Affine.Equation` evaluation + the downstream consumer `zsmul_eq_smulEval` (which needs `Affine.Point`, field-only in mathlib) require a field. The *ring-level* generality is already captured separately by `addXYZ_smulRing₁` over `Universal.Ring`. |
| 2 | index `n : ℤ` | integer | integer | NO | indices are intrinsically `ℤ`. |
| 3 | specialisation `n,n+1` | odd-step | general `m,n` | (by design) | the general `m,n` form already exists as `addXYZ_smulEval` (line 572); this `₁` version is the form the induction in `zsmul_eq_smulEval` actually calls. |

#### Generality verdict (Phase 4b)
The current form is: MAXIMALLY GENERAL **for its layer** (field is intrinsic; the ring-level
maximal generality is the sibling `addXYZ_smulRing₁`). Weakening opportunities: 0.
Cost of any restatement: n/a.

#### Modern-idiom check (Phase 4c)
| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|-----------|
| 1 | bundled-hyp → typeclass? | no | `Equation x y` is genuinely a hypothesis, not a class | — |
| 2 | sequences→filters? | no | finite algebraic identity; no limits | — |
| 3 | construct→universal-property? | no | concrete coordinate identity | — |
| 4 | set+closure→bundled-substructure? | no | n/a | — |
| 5 | field/metric→weaker typeclass? | partial | the *ring* version already exists (`addXYZ_smulRing₁`); this field version is the evaluated specialisation, deliberately field-level | the two-layer (universal ring → evaluate via `ringEval`) design is *already* the modern, maximally-general mathlib idiom |
| 6 | 1-cat→higher-cat? | no | n/a | — |
| 7 | concrete index→general monoid? | no | `ℤ` intrinsic to point multiplication | — |

Modern idiom available: **no** — the project's universal-ring-then-specialise architecture
is already the idiomatic maximally-general approach. No reformulation improves organisation.

---

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma` (no definitional equalities or instance paths introduced).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a (mathlib index offline locally) — substituted by direct grep over `.lake/packages/mathlib`
[B] Loogle            type-pattern `addXYZ _ _ = _ • _` / `_ • _ = smulEval _` — no such index symbol in mathlib (`smulEval` absent)
[C] LeanSearch        "n-th multiple of point equals division polynomial evaluation" — no mathlib hit (concept not upstream)
[D] Grep mathlib src  `smulEval|smulRing|addXYZ_smulRing|zsmul_eq_smulEval|smul_eq_divisionPolynomial|ringEval_comp_smulRing` over all of `Mathlib/` → **ZERO hits**
[E] Name pattern      `addXYZ_smulEval`, `smulEval` over `Mathlib/` → ZERO hits

Searched for both the current form and the literature-standard two-point law. Mathlib HAS:
  - the Jacobian arithmetic primitives: `WeierstrassCurve.Jacobian.addXYZ`, `dblXYZ`,
    `addXYZ_smul`, `map_addXYZ`, `addXYZ_self`, … (`Jacobian/Formula.lean`).
  - the division polynomials `Ψ`/`Φ`/`ω`/`ψ`/`φ` (`DivisionPolynomial/Basic.lean`).
  - the abstract EDS API: `IsEllSequence`, `preNormEDS`, `normEDS`, `complEDS₂`, …
    (`NumberTheory/EllipticDivisibilitySequence.lean`).

Mathlib does **NOT** have: any lemma connecting `n • P` (in `Affine.Point` / the Jacobian
point group) to division-polynomial evaluation. `DivisionPolynomial/Basic.lean` contains
**no** reference to `Affine.Point`/`Jacobian.Point`/smul-of-a-point. The bridge is exactly
what this project builds.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form).
The building blocks (`addXYZ`, `map_addXYZ`, division polys) are upstream; the bridge lemma
and its entire `Universal.Ring`/`smulRing`/`ringEval` scaffolding are project-only.

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.addXYZ_smulEval₁`
Internal use count (excluding declaring file): 0 in NagellLutz outside `ZSMul.lean`.
Within `ZSMul.lean`: used once, at line 616, inside `zsmul_eq_smulEval` (the odd branch of
the strong induction).

| Caller file:line | Usage pattern |
|------------------|---------------|
| ZSMul.lean:616 | `rw [this, addXYZ_smulEval₁ h.1]` — the only consumer; the odd-index inductive step |

Inline-derivation grep: **DUPLICATED** — the identical lemma is independently present in a
sibling fork: `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:656` (def) and
:695 (use). This is the duplicated General*/PID* track the task flagged: two AINTLIB projects
carry the same forked ZSMul tower. (Cross-project dedup is a *cleanup* concern, not a mathlib
verdict driver, but it confirms the lemma is "real API" within AINTLIB.)

#### Composition attempt
Proof body is one line:
`simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]`

Ingredients: `ringEval_comp_smulRing` (project), `addXYZ_smulRing₁` (project),
`map_addXYZ` (**mathlib**), `curveRing_map_ringEval` (project).

Attempt 1 (compose from mathlib only): FAILS. Three of the four rewrite lemmas are
project-only, and they themselves rest on the whole tower: `addXYZ_smulRing₁` ← `addXYZ_smulRing`
← `addXYZ_smulField` (a real ~30-line proof using `add_point_of_ne_eq_addXYZ`, EDS
`isEllSequence_ψ`, fraction-field injectivity); `ringEval_comp_smulRing` ← `Universal.Ring`,
`AdjoinRoot`, `specialize`, `polyEval`. None of this exists in mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. The 1-line proof is genuine
*transport* across a substantial, project-only construction — not a mathlib composition.

---

## Verdict: `WeierstrassCurve.addXYZ_smulEval₁`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature (Phase 3): standard odd-index division-polynomial / EDS addition law; the
  Jacobian-coordinate rendering is faithful and standard.
- Generality (Phase 4): MAXIMALLY GENERAL for its (field-evaluation) layer; the ring-level
  maximal form is the sibling `addXYZ_smulRing₁`. No weakening; no modern-idiom flip.
- Mathlib search (Phase 5): not in mathlib; building blocks present but the
  division-poly ↔ point-group **bridge is entirely absent** upstream.
- Composition (Phase 6): NOT-COMPOSABLE from mathlib (needs the project's `smulRing` /
  `ringEval` / `addXYZ_smulRing₁` tower).

**Rationale:**

This is neither a redundancy nor a trivial composition. Mathlib has the Jacobian arithmetic
formulas (`addXYZ`, `map_addXYZ`) and the division polynomials/EDS API, but **nothing links
`n • P` to division-polynomial evaluation** — `DivisionPolynomial/Basic.lean` never mentions
the point group. The NagellLutz project builds exactly that missing bridge, culminating in
`zsmul_eq_smulEval`. So a NO verdict (mathlib-has-it / composable) is wrong: the result rests
on a large project-only construction and contributes content mathlib genuinely lacks.

Why not a clean YES, then? Because `addXYZ_smulEval₁` is an **intermediate rung**, not the
upstreamable unit. It is a SMALL helper (the odd inductive step) consumed exactly once, by
`zsmul_eq_smulEval`. What mathlib would want is the *bridge theorem* `zsmul_eq_smulEval`
(or a clean repackaging of it), shipped together with the supporting tower — `addXYZ_smulRing₁`,
`ringEval_comp_smulRing`, the `Universal.Ring` machinery, etc. Whether to upstream this exact
helper, what to rename, how much of the `Universal.Ring`/`smulRing` scaffolding mathlib accepts
vs. wants rebuilt on its existing `DivisionPolynomial`/`Ψ` API, and what the public-facing
statement should be (`Affine.Point` vs. Jacobian `⟦·⟧`) — these are packaging and taste calls
the skill cannot make alone. The decl should be assessed (and PR'd) as part of the whole ZSMul
batch, not as one isolated lemma. Hence BORDERLINE.

Note also: the lemma is **duplicated verbatim** in HasseWeil (`Auxiliary/DivisionPolynomial.lean`).
That cross-project duplication is an AINTLIB cleanup item, and it reinforces that the right
unit of action is the shared tower, not this single rung.

**Numbered questions for the human:**
1. Should mathlibability be assessed at the level of the **whole `ZSMul` bridge** (ending in
   `zsmul_eq_smulEval`) rather than this single helper? (If yes, re-target `/mathlibable` at
   `WeierstrassCurve.zsmul_eq_smulEval` and treat `addXYZ_smulEval₁` as supporting API that
   ships in the same PR batch.)
2. Should the upstream version be rebuilt on mathlib's existing `DivisionPolynomial`/`normEDS`/`Ψ`
   API instead of the project's `Universal.Ring` + `AdjoinRoot.mk` + `specialize` construction —
   i.e. is the universal-ring scaffolding itself wanted in mathlib, or only the final bridge?
3. The NagellLutz and HasseWeil forks carry this tower twice. Before any mathlib PR, should the
   shared `ZSMul`/`DivisionPolynomial` tower be deduplicated into `Common/` within AINTLIB first?

**Next action:** Answer Q1–Q3. Most likely path: re-run `/mathlibable WeierstrassCurve.zsmul_eq_smulEval`
to assess the bridge as a whole; if that is YES, this helper is upstreamed as part of that batch
(not separately), with the AINTLIB cross-project dedup done first.

---

## Next step

Re-target the assessment at the bridge theorem `WeierstrassCurve.zsmul_eq_smulEval` and decide
the scaffolding/packaging questions (Q1–Q3) before any mathlib PR; `addXYZ_smulEval₁` then ships
as supporting API within that batch rather than as an isolated lemma.
