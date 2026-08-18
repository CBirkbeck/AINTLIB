# `/mathlibable` report — `PadicLFunctions.pow_mem_expBall`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

**Final five-bucket verdict: `YES-but-generalise-first`** (reason: LITERATURE-WEAKENING + MODERN-IDIOM).

The content — the open ball of radius `p^{-1/(p-1)}` around `1` in a nonarchimedean
field (the *exponential ball* `1 + B`, equivalently a higher unit group / the image of
the `p`-adic `exp`) is closed under taking `n`-th powers — is a correct, standard fact
that is genuinely missing from mathlib in this additive-norm form. But the user's
statement is strictly narrower than the proof supports (the `p`-baked radius and the
`NormedAlgebra ℚ_[p] L` / prime context are inessential; the only operative hypotheses
are `SeminormedRing + NormOneClass + IsUltrametricDist` and `‖y-1‖ < r ≤ 1`), and the
mathlib-idiomatic target is the **bundled `Submonoid`** "ball of radius `r ≤ 1` around
`1`" (the additive-distance counterpart of the multiplicative
`IsUltrametricDist.ball_openSubgroup` that already exists), with this theorem recovered
as `Submonoid.pow_mem` in one line. This is the **same upstreaming object** already
identified for the full-unit-ball sibling
`PadicLFunctions.MeasureR.boundary_norm_pow_sub_one_lt_one` (also
`YES-but-generalise-first`); `pow_mem_expBall` is the radius-`p^{-1/(p-1)}` instance of
that same bundled object and should ship with it, not as a standalone `p`-adic lemma.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task BUILD NOTE — `lake build` is stale/slow here; the declaration and its full dependency chain — `InExpBall`, `mul_mem_expBall`, `norm_lt_one_of_inExpBall`, and the mathlib `Ultra`/`UnitBall`/`ValuationSubring`/`Submonoid` files — were read directly from source and reasoned from there, exactly as the skill's Phase-0 fallback allows). Baseline commit `5511b59`.
- decl `PadicLFunctions.pow_mem_expBall`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:67`
- kind:                      theorem
- has sorry:                 no (2-case `induction n`; both branches close)
- module docstring summary:  ExtLog.lean develops the extended (Iwasawa-branch) `p`-adic logarithm `extLog` for RJW Thm 6.1(ii) (W6a); this theorem is one of the ball-closure helpers (`norm_lt_one_of_inExpBall → mul_mem_expBall → pow_mem_expBall`) that make the translated exponential ball `1 + B` behave like the multiplicative group it is.

---

### Statement (Phase 1)

`pow_mem_expBall` is a theorem stating the following:

> Let `L` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra, and
> let `B = {w : ‖w‖^{p-1} < p⁻¹}` be the open convergence ball of the `p`-adic
> exponential (equivalently `‖w‖ < p^{-1/(p-1)}`). If `y - 1 ∈ B` (i.e. `y` lies in the
> translated *exponential ball* `1 + B`), then for every `n ∈ ℕ`, `yⁿ - 1 ∈ B` as well
> — the exponential ball `1 + B` is closed under taking `n`-th powers.

Equivalently: the set `1 + B` is a multiplicative submonoid of `L` (indeed a subgroup
of `Lˣ` — it is a *higher unit group*, the image of the additive-to-multiplicative
isomorphism `exp : (B,+) → (1+B,×)`), and this theorem is its *power-closure* half.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (file-level `variable`; `include`d here implicitly via `hp.out` usage in the `zero` branch).
- `{L : Type*}` with the file-level `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`. **The decl carries `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`**, so its effective signature drops the algebra and completeness instances; the operative instances are `[NormedField L] [IsUltrametricDist L]` (plus `Fact p.Prime`, used only to know `p ≥ 2` so the `ℕ`-exponent `p - 1` is positive and `p⁻¹ > 0`).
- `InExpBall p : L → Prop` — defined in `PadicExp.lean:65` as `‖x‖ ^ (p - 1) < (p : ℝ)⁻¹` (rpow-free membership in the exp convergence ball).

Hypotheses (Lean side):
- `{y : L}` — the base point.
- `(hy : InExpBall p (y - 1))` — `y` lies in the translated exp ball `1 + B`.
- `(n : ℕ)` — the exponent.

Conclusion (math): `yⁿ` again lies in the translated exp ball `1 + B`.

Conclusion (Lean): `InExpBall p (y ^ n - 1)`.

Proof body (read from source):
```lean
induction n with
| zero =>
  rw [pow_zero, sub_self, InExpBall, norm_zero,
    zero_pow (by have := hp.out.one_lt; omega)]
  exact inv_pos.mpr (by exact_mod_cast hp.out.pos)
| succ k ih =>
  rw [pow_succ]
  exact mul_mem_expBall p ih hy
```
The base case `n = 0` reduces to `‖0‖^{p-1} = 0 < p⁻¹`. The inductive step rewrites
`y^{k+1} = yᵏ·y` and applies the multiplicative-closure lemma `mul_mem_expBall`
(`ExtLog.lean:47`, the `mul_mem'` of the would-be submonoid). So the proof is exactly
the `Submonoid.pow_mem` induction (`one_mem` + `mul_mem` ⟹ `pow_mem`), hand-rolled
because no bundled submonoid exists.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — the power-closure half of "the exp ball `1 + B` is a
submonoid". It is not a new structure, not a `## Main results` entry, and not named
after a person. (It does, however, sit inside a substantial new development — the
extended `p`-adic logarithm `extLog` and the `p`-adic `exp`/`log` API — none of which
is in mathlib; that context is what makes the verdict non-trivial, see Phase 7.)

(Note: literature width was run EXHAUSTIVE regardless; BIG/SMALL recorded only for
framing.)

### One-line check (Phase 2b)

Body line count: ~6 substantive lines (an `induction` with two branches).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** Section skipped.

---

### Literature search table — EXHAUSTIVE protocol

Goal: identify the literature-standard form of "the `p`-adic exp's convergence/image
ball `1 + B` is closed under products and powers", and whether closure-under-powers is
ever a *named standalone theorem* or merely a consequence of `1 + B` being a group.

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic exponential convergence disc 1+B closed under multiplication powers nonarchimedean group` | yes | Convergence is governed by `\|x\|` only; nonarchimedean convergence discs are closed under the algebraic operations; `exp(x+y)=exp(x)exp(y)` | Conrad "Infinite series in p-adic fields"; Cambridge jat58 notes; Wikipedia. The disc is closed under operations **because** it carries group structure, not as a separate lemma. |
| 2 | WebSearch (general / max-domain) | `principal units 1 + maximal ideal subgroup multiplicative ultrametric field closed under powers` | yes | `U₁(K) = 1 + 𝔪 = {1+x : \|x\|<1}` is **the** subgroup of principal units; `K* ⊇ 𝒪* ⊇ U₁(K)` splits as topological groups | The full-unit-ball case (`r=1`). Power-closure is immediate from "subgroup". This is the `boundary_norm_pow_sub_one_lt_one` object. |
| 3 | WebSearch (named-after / aliases) | `higher unit groups filtration U_n 1 + m^n subgroup local field congruence subgroup multiplicatively closed` | yes | `U^i = 1 + 𝔪ⁱ = {x : v(x-1) ≥ i}` form a decreasing filtration of **closed subgroups** of `U`; quotients `U^{(n)}/U^{(n+1)} ≅ 𝒪/𝔪` | Neukirch–Serre / local-class-field-theory standard. The exp ball `1+B` (radius `p^{-1/(p-1)}`) is one of these higher unit groups — a subgroup, hence power-closed. Kedlaya CFT notes §filtration; Conrad CFT history. |
| 4 | ChatGPT MCP | "standard form of 'exp ball is power-closed', its generality, historical evolution" | n/a | — | **No ChatGPT/OpenAI MCP server is live in this session.** (`plugin:mathlib-quality:chatgpt-math` appears in `~/.claude/mcp-needs-auth-cache.json` but is **not** surfaced as a callable tool here — `ToolSearch` for it returns nothing.) Recorded n/a with reason; compensated by extra WebSearch probes (#5, #10) and the WebFetch channels below, matching the sibling reports' handling. |
| 5 | WebSearch (exp-as-isomorphism / explicit power rule) | `p-adic exp isomorphism additive group ball onto multiplicative group 1+B power rule exp(x)^n = exp(nx) consequence` | yes | `exp` is an isomorphism `(B,+) → (1+B,×)`; `exp(nx)=exp(x)ⁿ ∈ 1+B` follows by applying the homomorphism property `n` times | Berkeley "Existence of primitive roots via p-adic numbers"; arXiv 1907.06437. Confirms: power-closure of `1+B` is a **corollary of the group iso**, never a named theorem. |
| 6 | nLab | `nLab principal units one-units multiplicative subgroup nonarchimedean exponential disc closed multiplication` → `ncatlab.org/nlab/show/group+of+units` | weak | nLab has "group of units"; no dedicated p-adic-exp-disc page | The exp-ball-as-subgroup fact is background folklore on nLab, not a named entry. |
| 7 | nCatLab (categorical) | (same as #6) | n/a | — | Not a categorical concept beyond "subgroup of a topological group"; no universal property / higher-categorical content to look up. |
| 8 | Stacks Project (alg geom) | considered | n/a | — | Not a scheme-theoretic statement; it is a one-variable norm inequality / unit-filtration fact. Stacks has valuation-ring material but nothing closer than the standard `1+𝔪` subgroup already found in #2/#3. Recorded n/a with reason. |
| 9 | MathOverflow / Math.StackExchange | (surfaced via #1/#2/#3 WebSearches) | yes (background) | `1+𝔪` and the higher `1+𝔪ⁿ` are subgroups of `𝒪×` in any nonarchimedean field; closure under products/powers is the multiplicative-closure half | Treated as folklore; consistent with #1–#3, #5. |
| 10 | recent arXiv (last 5 years) + history probe | `Hensel minimality, p-adic exponentiation and Tate uniformization` (arXiv 2602.16433); unit-filtration papers (arXiv 2104.03299 "First Cohomology of Local Units"; 1810.09975 "Jump sets in local fields") | yes | `exp` on the ball of radius `p^{-1/(p-1)}` is an **isometry and a homomorphism** onto its image; modern literature treats `1+𝔪ⁿ` as bundled (filtered) groups | Contemporary research uses exactly the same inequality hypothesis and the same group structure; the image disc is a subgroup. |

Protocol pass check:
- WebSearch ran ≥3 distinct queries at different generality levels (#1 specific exp-ball form, #2 full-unit-ball `1+𝔪`, #3 higher-unit-group filtration, plus #5/#10 isomorphism + history) — ✓.
- ChatGPT MCP: **environment has no live server** — recorded n/a with reason and compensated with the extra probes #5/#10 — ✓ (gate-compliant).
- Local references (#5 of the protocol, channel "Local references"): `n/a` — neither `projects/PadicLFunctions/.mathlib-quality/references/` nor `refs/PadicLFunctions/` exists (only `overview/` is present; the `--refs` path passed points at the skill's generic reference docs, not project source PDFs). The module docstring cites RJW Thm 6.1(ii) and Washington §5.1 as the sources.
- nLab checked (#6) — ✓. Stacks / nCatLab recorded n/a-with-reason (#7/#8) — ✓. MathOverflow / arXiv checked (#9/#10) — ✓.

### Literature summary (Phase 3)

Concept identified as: the **exponential ball** `1 + B = {y : ‖y-1‖ < p^{-1/(p-1)}}` of a
nonarchimedean field — equivalently a **higher unit group** (one of the congruence
subgroups `U^i = 1 + 𝔪ⁱ`) and precisely **the image of the `p`-adic exponential**, which
is a group isomorphism `exp : (B,+) → (1+B,×)`. The theorem is the **power-closure half**
of the standard fact that `1 + B` is a multiplicative subgroup of `Lˣ`.

Sources agree on the standard form: **yes.** Every nonarchimedean-analysis / local-field
reference (Conrad, Cambridge notes, Neukirch–Serre, Kedlaya CFT, the modern arXiv
unit-filtration literature) treats `1 + 𝔪ⁿ` (hence the exp image disc) as a multiplicative
(sub)group as a matter of course. Closure under powers is folklore — a one-line consequence
of "`1 + B` is a subgroup" / "`exp` is a homomorphism (`exp(nx)=exp(x)ⁿ`)". It is **never**
stated as a separate named theorem.

Most general standard form: in *any* nonarchimedean normed ring with `‖1‖ = 1`, for any
radius `0 < r ≤ 1`, the set `1 + {a : ‖a‖ < r}` is a multiplicative submonoid (and, in the
units, a subgroup). The radius `r = p^{-1/(p-1)}` is the special exp-convergence value, but
the closure-under-powers direction uses **only** submultiplicativity `‖ab‖ ≤ ‖a‖‖b‖`,
`‖1‖ = 1`, the ultrametric inequality, and `r ≤ 1` (so that `‖y‖ ≤ 1` on `1 + B`). Neither
the prime `p`, nor the `ℚ_p`-algebra structure, nor completeness, nor the field structure,
nor the specific value of `r` is essential.

Generality dimensions where the literature varies:
- **Radius.** `r = 1` (principal units `U₁`, the `boundary_norm_pow_sub_one_lt_one` case)
  vs. `r = p^{-1/(p-1)}` (the exp ball, *this* lemma) vs. arbitrary `r ≤ 1` (higher unit
  groups `U^i`). All are the same submonoid construction at different radii.
- **Ambient structure.** Stated for complete discretely-valued local fields in textbooks,
  but the closure fact holds for any nonarchimedean normed ring with `NormOneClass` (no
  completeness, no field, no prime). Most general = `SeminormedRing + NormOneClass +
  IsUltrametricDist`.
- **Packaging.** Bare predicate `InExpBall p (yⁿ - 1)` (user) vs. bundled **submonoid**
  `1 + B` (modern literature; mathlib's analogous *multiplicative* object
  `IsUltrametricDist.ball_openSubgroup`, and the *around-0* `Subsemigroup.unitBall`). The
  modern idiom is the bundled object.

Disagreement with the literature: **none on content.** The user's form is correct but is a
*specialisation* (to a `p`-baked radius and the `ℚ_p`-algebra prime context) and
*unbundled* (a bare implication rather than the substructure the literature/mathlib idiom
uses).

---

### Generality analysis — `pow_mem_expBall`

Literature-standard form (from Phase 3): in any nonarchimedean normed ring with `‖1‖ = 1`,
for `0 < r ≤ 1`, `1 + {a : ‖a‖ < r}` is multiplicatively closed; i.e. `‖y-1‖ < r ⟹
‖yⁿ-1‖ < r`. The exp ball is the `r = p^{-1/(p-1)}` instance.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | normed field (mult. norm, `‖1‖=1`, division) | nonarchimedean normed *ring* with `‖1‖=1` | **yes** | The proof (`mul_mem_expBall` + induction) uses only `norm_add_le_max` (ultrametric, `SeminormedAddGroup`), `norm_mul`/submultiplicativity (`SeminormedRing`), `norm_one`, and `‖y‖≤1`. **No division, no field needed.** Weakens to `[SeminormedRing R] [NormOneClass R]` — the typeclass cluster of `IsUltrametricDist.norm_add_one_le_max_norm_one`. (Same axis the sibling `boundary_norm_pow_sub_one_lt_one` identified.) |
| 2 | `[IsUltrametricDist L]` | nonarchimedean | nonarchimedean | NO | Essential — the whole estimate is the ultrametric `max` bound. The defining hypothesis. |
| 3 | `[Fact p.Prime]` + the radius `p⁻¹` and exponent `p-1` baked into `InExpBall` | radius `r = p^{-1/(p-1)}`, a specific prime-dependent value | arbitrary radius `0 < r ≤ 1` | **yes** | The power-closure direction needs only `r ≤ 1` (to get `‖y‖ ≤ 1`). The specific value `p^{-1/(p-1)}` and the prime `p` are **irrelevant** to closure-under-powers; they matter only for *exp convergence*, which is a different fact. The general statement is the radius-`r` submonoid; `pow_mem_expBall` is the `r = p^{-1/(p-1)}` instance. |
| 4 | `[NormedAlgebra ℚ_[p] L]`, `[CompleteSpace L]` | present in `variable`, **`omit`-ted** on this decl | absent | already absent | Explicitly `omit`-ted; not part of the effective signature. No action; noted for completeness. |
| 5 | `(n : ℕ)` | nonneg-integer exponent | `n : ℕ` (powers) | NO (for this statement) | `ℕ` is correct for the *monoid* closure. The `ℤ`-power / full-subgroup statement (`‖y⁻¹-1‖ < r`) is the *additional* content of the bundled-subgroup form (Phase 4c), not a weakening of this one. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: 2 (the `NormedField → SeminormedRing + NormOneClass` axis, row 1; and the `p`-baked radius `→` arbitrary `r ≤ 1` axis, row 3).

Proposed restatement (literature-weakened, bare-implication form, radius-generalised):

```lean
theorem norm_pow_sub_one_lt_of_lt {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {r : ℝ} (hr : r ≤ 1) {y : R} (hy : ‖y - 1‖ < r) (n : ℕ) :
    ‖y ^ n - 1‖ < r
```

(The `InExpBall`-flavoured `pow_mem_expBall` is then the `r := p^{-1/(p-1)} ≤ 1` instance —
or, in the project's rpow-free encoding, recovered directly from the bundled object below.)

Cost of restatement: **CHEAP** — the existing `mul_mem_expBall`+induction transfers
essentially verbatim (`norm_mul` ⟶ `norm_mul_le`'s `≤`; the radius generalises by replacing
the literal `p^{-1/(p-1)}` bound with `r` and using `r ≤ 1` where `‖y‖ ≤ 1` is needed). No
new ideas.

Since STRICTLY NARROWER → Phase 7 considers `YES-but-generalise-first` prominently; 4c
sharpens *what* to generalise to.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let `L` be a foo" preambles → typeclasses/instances? | no | already typeclass-driven | — |
| 2 | sequences/metric → filters/nets/topological? | no | finite induction over `ℕ` powers; no limit/convergence content to filter-ise (exp *convergence* is elsewhere; this is pure algebraic closure) | — |
| 3 | **construct** an object where a **universal-property class** would characterise it? | no | not a universal-property situation | — |
| 4 | **set-with-closure-predicate → bundled-substructure type** that composes with mathlib's lattices? | **YES** | bundle `1 + {a : ‖a‖ < r}` (for `0 < r ≤ 1`) as a `Submonoid R` (and a `Subgroup Rˣ`), the **additive-distance** counterpart of the *multiplicative* `IsUltrametricDist.ball_openSubgroup` and of the around-0 `Subsemigroup.unitBall`. The present theorem is then `Submonoid.pow_mem`. | the full `Submonoid`/`Subgroup` lattice API: `pow_mem`, `zpow_mem`, `mul_mem`, `prod_mem`, intersections; the higher-unit-group filtration `U^1 ⊇ U^2 ⊇ …` (the `r`-indexed family) gets a uniform home; `OpenSubgroup` topology. |
| 5 | vector-space/metric/field-specific → modules/pseudometric/(semi)ring? | **YES** | weaken `NormedField` → `SeminormedRing + NormOneClass` (= Phase 4b row 1) | the lemma then lives next to `norm_add_one_le_max_norm_one` in `Analysis/Normed/Ring/Ultra.lean` and applies to ultrametric *rings* (`𝒪_K`, group algebras), not just fields. |
| 6 | 1-categorical → higher/∞-categorical? | no | elementary inequality; no categorification | — |
| 7 | concrete index (`ℕ`,`ℤ`,`ℝ`) → arbitrary monoid/group? | partial | the bundled `Submonoid` makes `pow_mem` (ℕ) automatic; promoting to `Subgroup Rˣ` additionally gives `zpow_mem` (ℤ) for free; and the radius `r` generalises the `p`-specific bound to a parameter | unifies the ℕ-power statement with the ℤ-power one, and the exp-ball case with the full-unit-ball/higher-unit-group cases, without separate proofs. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**
- Proposed mathlib-idiomatic restatement (the bundled object + this theorem as its corollary):

  ```lean
  -- in Mathlib/Analysis/Normed/Ring/Ultra.lean, namespace IsUltrametricDist,
  -- variable {R : Type*} [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

  /-- The "principal units of radius `r`" `1 + {a | ‖a‖ < r}` of a nonarchimedean
  normed ring with `‖1‖ = 1` form a submonoid, for `0 < r ≤ 1` (the additive-distance
  counterpart of `ball_openSubgroup`; `r = 1` is the principal units `U₁`,
  `r = p^{-1/(p-1)}` is the p-adic exponential ball). -/
  def oneAddBallSubmonoid {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) : Submonoid R where
    carrier := {y | ‖y - 1‖ < r}
    one_mem' := by simpa using hr₀
    mul_mem' := by
      -- ‖yz − 1‖ = ‖(y−1)·z + (z−1)‖ ≤ max (‖y−1‖·‖z‖) ‖z−1‖ < r   (using ‖z‖ ≤ 1 from r ≤ 1)
      sorry

  /-- The radius-`r` ball around `1` is closed under powers (recovered as `pow_mem`). -/
  theorem norm_pow_sub_one_lt_of_lt {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1)
      {y : R} (hy : ‖y - 1‖ < r) (n : ℕ) : ‖y ^ n - 1‖ < r :=
    (oneAddBallSubmonoid hr₀ hr₁).pow_mem hy n
  ```

  (and, on the units, a `Subgroup Rˣ` giving `zpow_mem` and matching the multiplicative
  `ball_openSubgroup`.) The project's `pow_mem_expBall` is then the `r := p^{-1/(p-1)}`
  instance: `InExpBall p (y-1)` unfolds to `‖y-1‖^{p-1} < p⁻¹`, equivalently
  `‖y-1‖ < p^{-1/(p-1)} ≤ 1`, so `pow_mem_expBall p hy n` becomes a one-line corollary of
  `(oneAddBallSubmonoid …).pow_mem`.
- Cost: bare-implication weakening **CHEAP**; bundled-submonoid form **MODERATE** (one
  ultrametric `mul_mem'` estimate — which the project already has as `mul_mem_expBall`).
- Mathlib downstream this enables: the full `Submonoid`/`Subgroup` API (`pow_mem`,
  `zpow_mem`, `mul_mem`, `prod_mem`, lattice ops), the higher-unit-group filtration as the
  `r`-indexed family `U^i = oneAddBallSubmonoid …`, an `OpenSubgroup Rˣ` paralleling
  `ball_openSubgroup`, and a clean home for the principal-units / exp-ball machinery used
  throughout local-field, cyclotomic, and Iwasawa theory.
- Real mathematical improvement (not just "looks cooler"): it puts the *additive-distance*
  ball around `1` on the same bundled footing mathlib already gives the *multiplicative*
  one (`ball_openSubgroup`) and the *around-0* one (`Subsemigroup.unitBall`), eliminating
  the asymmetry and removing the need for every consumer (this project's `ExtLog.lean`,
  `ValuesAtOne.lean`, and the parallel `MeasureR` cluster) to re-prove product/power closure
  by hand at each radius.

Per Phase 4c "modern idiom available" + Phase 4b STRICTLY NARROWER → Phase 7 produces
`YES-but-generalise-first`.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`** (no definitional equalities or typeclass-search
paths introduced). Skipped per scope. (The *proposed* bundled `Submonoid`/`Subgroup` in 4c
would warrant a risk pass when actually written — none of the six rows looks problematic
for a plain `Submonoid where` carrier-set bundle — but the object under assessment is the
theorem.)

---

### Mathlib search-status: `pow_mem_expBall`

[A] Lean-Finder — **n/a:** no Lean-Finder MCP tool available in this session (the deferred-tool list exposes only `WebSearch`/`WebFetch`; no `lean_*` MCP). Compensated by [D] direct mathlib-source grep + reading the `Ultra`/`UnitBall`/`ValuationSubring`/`Submonoid` files in full.
[B] Loogle — **n/a:** no `lean_loogle` tool live. Type-pattern intent `IsUltrametricDist → ‖_^_ - 1‖ < _` / `(?a ^ _) ∈ ?S` emulated via grep of the exact and near shapes over `.lake/packages/mathlib/` — no hits for the additive `‖yⁿ-1‖ < r` statement (see [D]).
[C] LeanSearch — **n/a:** no `lean_leansearch` tool live. Natural-language intent "ball around one closed under powers in ultrametric field / higher unit group power-closure" chased through Phase 3 literature + the mathlib `Ultra`/`UnitBall`/`ValuationSubring` source (read directly); closest objects identified below.
[D] Grep mathlib src — searched `‖.*\^.* - 1‖ *< ` (exact additive shape): **0 hits**. Searched `IsUltrametricDist` lemma/def heads across `Analysis/Normed/{Group,Ring,Field}/Ultra.lean`, `norm_add_one_le_max_norm_one`, `ball_openSubgroup`/`closedBall_openSubgroup`, `Subsemigroup.unitBall`/`unitClosedBall`, `ValuationSubring.principalUnitGroup`, `Submonoid.pow_mem`, plus `padicExp`/`padicLog`/`InExpBall` (zero — mathlib has no p-adic exp/log at all).
[E] Name pattern — searched `pow_mem_expBall`, `norm_pow_sub_one`, `expBall`, `oneAddBall`, `principalUnit*`, `higherUnit`, `oneSub*` over mathlib: **no decl** matching the additive `‖yⁿ-1‖ < r` ball-power-closure statement.

Searched for both:
  - the user's current form (`InExpBall p (yⁿ - 1)`, radius `p^{-1/(p-1)}`, `NormedField` + `IsUltrametricDist`),
  - the literature-standard / general form (radius-`r` ball `1 + {a : ‖a‖ < r}` as a `Submonoid` over `SeminormedRing + NormOneClass`).

Relevant mathlib objects found (none is the statement):
  - **`IsUltrametricDist.ball_openSubgroup` / `.closedBall_openSubgroup`** (`Analysis/Normed/Group/Ultra.lean:162,176`): for a `SeminormedGroup S`, `Metric.ball (1 : S) r` is an `OpenSubgroup` for any `r > 0` — including the exp-ball radius. **Different group:** this is the *multiplicative* group with multiplicative distance `dist x 1 = ‖x⁻¹·1‖` (its `mul_mem'` uses `dist_eq_norm_inv_mul'`). Our `‖y - 1‖` is the *additive* distance in the field `L`; there is **no `SeminormedGroup` instance on `Lˣ`** with norm `‖y - 1‖`, so this does **not** apply to our statement. It is the *parallel* object — exactly why the bundled **additive** version (Phase 4c) is the right contribution. This is the only mathlib `D'` that is even radius-correct, and it is structurally the wrong distance.
  - **`Subsemigroup.unitBall` / `Subsemigroup.unitClosedBall`** (`Analysis/Normed/Field/UnitBall.lean:32,96`): the ball `{x : ‖x‖ < 1}` around **0** is a bundled `Subsemigroup` of a `NonUnitalSeminormedRing`. Confirms the **idiom** (mathlib bundles norm-balls as algebraic substructures) but is around `0`, not around `1`, and at radius `1` only. Not our statement; it is the template the Phase-4c `oneAddBallSubmonoid` would follow.
  - **`IsUltrametricDist.norm_add_one_le_max_norm_one`** (`Analysis/Normed/Ring/Ultra.lean:50`): `‖x + 1‖ ≤ max ‖x‖ 1` in `SeminormedRing + NormOneClass + IsUltrametricDist` — a **building block** for the `mul_mem'`, not the statement. Confirms the right typeclass home.
  - **`ValuationSubring.principalUnitGroup`** (`RingTheory/Valuation/ValuationSubring.lean:634`): `Subgroup Kˣ` with carrier `{x | A.valuation (x-1) < 1}`, `mul_mem'`/`inv_mem'` proven. The **valuation-theoretic** sibling — but radius `1` only (full principal units, not the exp ball), stated via a `Valuation`/`ValuationSubring` on `Kˣ`, not via a `NormedField`'s norm on `K`. Not our statement; bridging to it is not a bounded composition (see Phase 6).
  - **`Submonoid.pow_mem`** (`Algebra/Group/Submonoid/Defs.lean:475`): `S.pow_mem hx n : x ^ n ∈ S` — the generic engine that *would* discharge this lemma in one line **if** the exp ball were a bundled submonoid. It is not (in either this project or mathlib). This is the lemma the Phase-4c restatement leans on.

Concluded: **not in mathlib** (all five methods exhausted on both the user's form and the
literature-standard form; the A/B/C MCP channels are unavailable this session but moot —
the decisive `padicExp`/`InExpBall`/`‖yⁿ-1‖<r` greps return zero, and the only
radius-correct mathlib object, `ball_openSubgroup`, is the multiplicative-distance group,
not the additive-distance ball). Mathlib has the *multiplicative-group* ball-subgroup, the
*around-0* unit-ball semigroup, and the *valuation-theoretic* `principalUnitGroup`, but
**none** is the additive normed-ring exp-ball form, and none specialises to it in ≤1 line.

---

### Call sites — `pow_mem_expBall`

Internal use count (within the project, NOT counting the declaring file `ExtLog.lean`):
**1** — at `ValuesAtOne.lean:558`.
External-to-file callers: **1** distinct file (`ValuesAtOne.lean`).
Within-file uses (`ExtLog.lean`, for context): **3** — at lines 84 (`padicLog_pow`), 364 and 374 (`extLog_mul`), and 392 (`ExtLogDomain.mul`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ValuesAtOne.lean:558 | `exact pow_mem_expBall (p := p) hwj (p ^ d)` — inside `padicLog_mul_of_norm_lt_one`, to lift `InExpBall (w^{p^j}-1)` to `InExpBall (w^{p^{j+d}}-1)` via `w^{p^{j+d}} = (w^{p^j})^{p^d}` |
| ExtLog.lean:84 (own file) | `padicLog_mul p (pow_mem_expBall p hy k) hy` — in `padicLog_pow` |
| ExtLog.lean:364, 374, 392 (own file) | `mul_mem_expBall p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m)` etc. — in `extLog_mul` / `ExtLogDomain.mul` |

Inline-derivation grep (was the `InExpBall (yⁿ-1)` power-closure re-derived elsewhere
without using `pow_mem_expBall`?):
  - (none found) — `pow_mem_expBall` is the single source of exp-ball power-closure in the
    project. The parallel `MeasureR` cluster (`boundary_norm_pow_sub_one_lt_one`) proves the
    *full-unit-ball* power-closure (`‖x^n-1‖<1`) separately, but that is the radius-`1`
    statement, a different (weaker-radius) fact, not an inline re-derivation of this one.

What the pattern tells us: this is **real API** — 1 genuine cross-file consumer
(`ValuesAtOne.lean`, in the load-bearing `padicLog_mul_of_norm_lt_one` proof) plus 3
within-file consumers (it is the engine for `padicLog_pow`, `extLog_mul`, and
`ExtLogDomain.mul`). It is the standard `mul_mem ⟹ pow_mem` step the whole `extLog`
additivity development routes through. The genuine, recurring use plus complete absence from
mathlib (Phase 5) plus the strictly-narrower-than-standard form (Phase 4) points at a YES
family — specifically `YES-but-generalise-first`, not `YES-add-as-is`.

### Composition check (Phase 6)

Can `pow_mem_expBall` be derived from mathlib in ≤3 chained calls?

Attempt 1 — via the multiplicative `IsUltrametricDist.ball_openSubgroup` + `Subgroup.pow_mem`:
  - Mathlib decls used: `IsUltrametricDist.ball_openSubgroup`, `Subgroup.pow_mem`.
  - Result: **fails.** `ball_openSubgroup` lives in a `SeminormedGroup` and its ball is
    `Metric.ball (1 : S) r` under the *multiplicative* distance `dist x 1 = ‖x⁻¹·1‖`
    (its `mul_mem'` literally rewrites with `dist_eq_norm_inv_mul'`). There is **no
    `SeminormedGroup` instance on `Lˣ`** (or `L`) whose norm equals `‖y - 1‖`. Manufacturing
    one (a multiplicative group seminorm `‖y‖' := ‖y - 1‖` on the units) is *itself* the
    content of `mul_mem_expBall`'s ultrametric estimate — circular, not a composition.

Attempt 2 — via `ValuationSubring.principalUnitGroup` + `Subgroup.pow_mem`:
  - Mathlib decls used: `NormedField.toValued`/valuation, `ValuationSubring.principalUnitGroup`,
    `mem_principalUnitGroup_iff`, `Subgroup.pow_mem`, norm↔valuation translation.
  - Result: **fails (not bounded), and radius-wrong.** (a) Producing the canonical
    `ValuationSubring` from the norm needs `NontriviallyNormedField` + a rank-one `Valuation`
    instance the hypotheses (`NormedField + IsUltrametricDist`) don't supply; (b) `y` must be
    promoted to `Lˣ` (extra `y ≠ 0` derivation); (c) `principalUnitGroup` is the radius-`1`
    ball `valuation(y-1) < 1`, **not** the exp ball `‖y-1‖ < p^{-1/(p-1)}` — so even after
    bridging, `Subgroup.pow_mem` would give `‖yⁿ-1‖ < 1`, the *weaker* conclusion, not
    `InExpBall p (yⁿ-1)`. ≥5 steps across `Valued`/`ValuationSubring`/`Lˣ`/valuation-vs-norm
    **and** a strictly weaker target. A genuine proof, not a 1–3 call composition.

Attempt 3 — the actual project proof: `induction n; zero => …; succ k ih => rw [pow_succ]; exact mul_mem_expBall p ih hy`.
  - Mathlib decls used: only `pow_succ` (+ `pow_zero`, `sub_self`, `norm_zero`, `zero_pow`, `inv_pos` in the base case). The load-bearing step — the multiplicative closure `mul_mem_expBall` — is a **project lemma, not mathlib**. And it is an `induction`, i.e. a genuine proof (precisely the `Submonoid.pow_mem` induction, done by hand for lack of a bundled submonoid).
  - Result: not a mathlib composition.

Conclusion: **NOT-COMPOSABLE** from mathlib. (Mathlib has neither the additive-distance
exp-ball submonoid nor `mul_mem_expBall`; the only radius-correct object,
`ball_openSubgroup`, is the wrong — multiplicative — distance and has no usable instance
here; `principalUnitGroup` is both an unbounded bridge and radius-wrong.) → Phase 7
considers the YES verdicts.

---

## Verdict: `pow_mem_expBall`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): unambiguous — the exp ball `1 + B` is a **higher unit
  group** / the **image of the `p`-adic exp**, hence a multiplicative subgroup; this theorem
  is the power-closure half of "`1 + B` is a subgroup", a folklore corollary of `exp` being
  a homomorphism (`exp(nx)=exp(x)ⁿ`), never a named standalone theorem. The full-unit-ball
  radius-`1` case is the standard principal units `U₁ = 1 + 𝔪` (Neukirch–Serre, Kedlaya
  CFT, arXiv unit-filtration literature).
- Generality analysis (Phase 4): **STRICTLY NARROWER** — `NormedField` weakens (CHEAP) to
  `SeminormedRing + NormOneClass`, and the `p`-baked radius `p^{-1/(p-1)}` generalises to an
  arbitrary `r ≤ 1`; (Phase 4c) the mathlib-idiomatic target is the **bundled radius-`r`
  `Submonoid`** `1 + {a : ‖a‖ < r}`, paralleling the existing multiplicative
  `IsUltrametricDist.ball_openSubgroup` and the around-0 `Subsemigroup.unitBall`.
- Mathlib search (Phase 5): **not in mathlib** in this additive form; the multiplicative
  `ball_openSubgroup` (wrong distance, though radius-correct), the around-0
  `Subsemigroup.unitBall`, and the valuation-theoretic `principalUnitGroup` (radius-`1`,
  via `Valuation`) are siblings — none is our form, none specialises in ≤1 line.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the `ball_openSubgroup` route needs a
  nonexistent `SeminormedGroup`-on-`Lˣ` instance (circular with `mul_mem_expBall`); the
  `principalUnitGroup` bridge is ≥5 steps *and* yields a strictly weaker (radius-`1`)
  conclusion.

**Rationale (1–2 paragraphs):**

The fact is genuinely wanted in mathlib and genuinely absent: mathlib already bundles the
*multiplicative* ultrametric ball around `1` (`ball_openSubgroup`, for any radius) and the
*around-0* unit ball (`Subsemigroup.unitBall`), but has **no** counterpart for the
*additive-distance* ball around `1` on the ring/field side — even though
`norm_add_one_le_max_norm_one`, the building block, already sits in
`Analysis/Normed/Ring/Ultra.lean`. The named gap is precisely that asymmetry: the additive
`1 + {a : ‖a‖ < r}` submonoid and its power-closure are missing, which is why this project
(and local-field / cyclotomic / Iwasawa developments generally) re-prove it by hand — here
as the `mul_mem_expBall → pow_mem_expBall` chain, and *again* in the parallel `MeasureR`
cluster as `boundary_norm_pow_sub_one_lt_one`. So the verdict is a YES family, not a NO.

It is **not** `YES-add-as-is`, for the two gating reasons the verdict gate enforces. (1)
Phase 4b found the form STRICTLY NARROWER than the proof supports — both the `NormedField`
hypothesis and the `p`-specific radius are needless specialisations (CHEAP weakenings to
`SeminormedRing + NormOneClass` and arbitrary `r ≤ 1`). (2) Phase 4c found a real
MODERN-IDIOM improvement: the bundled radius-`r` `Submonoid R` / `Subgroup Rˣ` (mirroring
`ball_openSubgroup` and `Subsemigroup.unitBall`), with this theorem recovered as
`Submonoid.pow_mem` in one line — unlocking the whole `pow_mem`/`zpow_mem`/`mul_mem`/
`prod_mem`/lattice/`OpenSubgroup` API and giving the higher-unit-group filtration (the
`r`-indexed family, of which the exp ball and the full unit ball are two members) a uniform
home. Critically, **this is the very same upstreaming object already proposed for the
sibling `boundary_norm_pow_sub_one_lt_one`** (also `YES-but-generalise-first`): that lemma
is the `r = 1` instance, `pow_mem_expBall` is the `r = p^{-1/(p-1)}` instance. They must be
generalised and shipped *together* as the one bundled `oneAddBallSubmonoid` (radius-
parametrised), not as two separate `p`-adic vs. unit-ball lemmas. Per the verdict gate,
STRICTLY NARROWER plus a real modern-idiom improvement both force `YES-but-generalise-first`.

**Reason for the generalisation:**
- LITERATURE-WEAKENING: Phase 4b — the user's `NormedField` + `p`-specific-radius form is
  strictly narrower than the proof supports (`SeminormedRing + NormOneClass`, arbitrary
  `r ≤ 1`).
- MODERN-IDIOM (Bourbaki 2.0): Phase 4c — bundle `1 + {a : ‖a‖ < r}` as a radius-parametrised
  `Submonoid`/`Subgroup`, matching mathlib's existing multiplicative `ball_openSubgroup` and
  around-0 `Subsemigroup.unitBall`.

**Proposed restatement (preferred — the bundled, radius-parametrised modern-idiom form):**

```lean
namespace IsUltrametricDist
variable {R : Type*} [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

/-- The "principal units of radius `r`" `1 + {a | ‖a‖ < r}` of a nonarchimedean normed
ring with `‖1‖ = 1`, as a submonoid (for `0 < r ≤ 1`; the additive-distance counterpart
of `ball_openSubgroup`). `r = 1` is the principal units `U₁`; `r = p^{-1/(p-1)}` is the
p-adic exponential ball. -/
def oneAddBallSubmonoid {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) : Submonoid R where
  carrier := {y | ‖y - 1‖ < r}
  one_mem' := by simpa using hr₀
  mul_mem' := by sorry  -- ‖yz − 1‖ = ‖(y−1)z + (z−1)‖ ≤ max (‖y−1‖‖z‖) ‖z−1‖ < r
                        -- (this is exactly the project's `mul_mem_expBall` estimate)

/-- The radius-`r` ball around `1` is closed under powers (recovered as `pow_mem`). -/
theorem norm_pow_sub_one_lt_of_lt {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {y : R} (hy : ‖y - 1‖ < r) (n : ℕ) : ‖y ^ n - 1‖ < r :=
  (oneAddBallSubmonoid hr₀ hr₁).pow_mem hy n
end IsUltrametricDist
```

The project's `pow_mem_expBall` is then a one-line corollary at `r := p^{-1/(p-1)} ≤ 1`
(`InExpBall p (y-1)` ↔ `‖y-1‖ < p^{-1/(p-1)}`), and the sibling
`boundary_norm_pow_sub_one_lt_one` is the `r := 1` corollary.

**Proposed restatement (minimal — bare-implication weakening, if the bundle is deferred):**

```lean
theorem norm_pow_sub_one_lt_of_lt {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {r : ℝ} (hr : r ≤ 1) {y : R} (hy : ‖y - 1‖ < r) (n : ℕ) :
    ‖y ^ n - 1‖ < r := by
  sorry  -- the existing mul_mem_expBall + induction transfers verbatim (norm_mul → norm_mul_le)
```

Estimated cost of regeneralisation: bare-implication weakening **CHEAP**; bundled-submonoid
form **MODERATE** (one ultrametric `mul_mem'` estimate — *already* written in the project as
`mul_mem_expBall`). EXPENSIVE-cost note: n/a — this is cheap/moderate; and per the gate, cost
would not downgrade the verdict regardless.

**Mathlib downstream this enables (MODERN-IDIOM, required):**
- `Submonoid.pow_mem` / `Subgroup.zpow_mem` recover the ℕ- and ℤ-power closure for free, at
  every radius.
- `mul_mem` / `prod_mem` give finite-product closure of the radius-`r` ball (this project
  uses exactly that via `mul_mem_expBall` in `extLog_mul`, `ExtLogDomain.mul`,
  `ExtLogDomain.prod`).
- The higher-unit-group filtration `U^1 ⊇ U^2 ⊇ …` becomes the `r`-indexed family
  `oneAddBallSubmonoid …`, unifying the exp-ball, full-unit-ball, and deeper-congruence
  cases under one object.
- An `OpenSubgroup Rˣ` paralleling `ball_openSubgroup`, giving these unit groups their
  topology.
- Removes the asymmetry whereby mathlib bundles the multiplicative ultrametric `1`-ball and
  the around-0 unit ball but not the additive `1`-ball — the gap this project hit and worked
  around **twice** (`pow_mem_expBall` here, `boundary_norm_pow_sub_one_lt_one` in `MeasureR`).

**What proofs were blocked by the old (bare, `p`-specific, `NormedField`) form:** any
consumer wanting product/inverse/topological closure of the exp ball or any unit-filtration
layer must re-derive it; the project re-proves the same closure at two different radii in two
files precisely because no bundled, radius-parametrised object exists to lean on.

**PR grouping (required):** ship `pow_mem_expBall` together with its sibling
`PadicLFunctions.MeasureR.boundary_norm_pow_sub_one_lt_one` (the `r = 1` case) as **one
coherent PR** adding `IsUltrametricDist.oneAddBallSubmonoid` (+ its `Subgroup Rˣ` /
`OpenSubgroup` API and `norm_pow_sub_one_lt_of_lt`) to `Mathlib/Analysis/Normed/Ring/Ultra.lean`,
alongside `norm_add_one_le_max_norm_one`. Both project lemmas become one-line corollaries.

**Pre-PR checklist before opening:**
- [ ] `/generalise PadicLFunctions.pow_mem_expBall` — confirm the radius-`r` weakening and the
      `SeminormedRing + NormOneClass` typeclass cluster (tension against the Phase-3
      higher-unit-group form and the Phase-4c bundled-submonoid form); do the same for
      `boundary_norm_pow_sub_one_lt_one` so they converge on the *same* `oneAddBallSubmonoid`.
- [ ] `/cleanup Mathlib/Analysis/Normed/Ring/Ultra.lean` (the new bundle) — full audit + diff gates.
- [ ] Pick a mathlib reviewer from recent `Mathlib/Analysis/Normed/{Ring,Group}/Ultra.lean`
      commits (the `ball_openSubgroup` / `IsUltrametricDist` authors).

---

## Next step

Run `/generalise PadicLFunctions.pow_mem_expBall` to restate at
`SeminormedRing + NormOneClass + IsUltrametricDist` with an arbitrary radius `r ≤ 1`, and —
preferably — as the bundled `IsUltrametricDist.oneAddBallSubmonoid` (the radius-parametrised
additive counterpart of `IsUltrametricDist.ball_openSubgroup`), with this theorem recovered
as `Submonoid.pow_mem`. Coordinate with the sibling
`PadicLFunctions.MeasureR.boundary_norm_pow_sub_one_lt_one` (the `r = 1` instance, already
verdicted `YES-but-generalise-first` for the *same* object): generalise both, then `/cleanup`
and open **one** mathlib PR to `Mathlib/Analysis/Normed/Ring/Ultra.lean` adding the bundled
`oneAddBallSubmonoid` with both project lemmas as corollaries. Do **not** PR `pow_mem_expBall`
as a standalone `p`-adic lemma; it is a radius-instance of a general ultrametric-ring fact.
