# `/mathlibable` report — `PadicLFunctions.MeasureR.boundary_norm_pow_sub_one_lt_one`

**Final verdict: `YES-but-generalise-first`** (reason: LITERATURE-WEAKENING + MODERN-IDIOM)

The content — the open unit norm-ball around `1` in an ultrametric field is closed
under (nonneg-integer) powers, i.e. the *principal units* `U₁ = 1 + 𝔪` are
multiplicatively closed — is genuinely missing from mathlib in this additive
norm form. But the user's `NormedField` form is strictly narrower than the proof
supports, and the mathlib-idiomatic target is the **bundled submonoid/subgroup**
(mirroring the multiplicative `IsUltrametricDist.ball_openSubgroup` that already
exists), stated at `SeminormedRing + NormOneClass + IsUltrametricDist`.

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (project oleans
  stale — `lean` reports `unknown module prefix 'PadicLFunctions'`; per the task's
  build note, read the declaration + its mathlib dependencies directly).
- decl `PadicLFunctions.MeasureR.boundary_norm_pow_sub_one_lt_one`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:453`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the file develops the `p`-adic value `L_p(θ,1)` (RJW
  §6.2, Thm 6.1(ii)); this theorem is a helper in the "boundary `p`-adic logarithm"
  block (T618 / Washington §5.1), supplying that powers of `x` with `‖x−1‖<1` stay
  in the open unit ball so the `padicLog` `p`-power law extends to the whole ball.

---

### Statement (Phase 1)

`boundary_norm_pow_sub_one_lt_one` is a theorem stating the following:

> In a field `K` with a non-archimedean (ultrametric) absolute value, if `x` lies in
> the open unit ball around `1` (i.e. `‖x − 1‖ < 1`), then every power `xⁿ` also lies
> in that ball (`‖xⁿ − 1‖ < 1`).

Equivalently: the set `1 + 𝔪 = {x : ‖x − 1‖ < 1}` — the **principal units** `U₁(K)`
of the non-archimedean field — is closed under taking nonnegative integer powers.

Variables / typeclasses involved (Lean side, after `omit`/auto-bound resolution):
- `K : Type*` — the ambient field.
- `[NormedField K]` — `K` carries a multiplicative absolute value (norm).
- `[IsUltrametricDist K]` — the norm is non-archimedean: `‖a + b‖ ≤ max ‖a‖ ‖b‖`.
- (`p`, `[Fact p.Prime]`, `[NormedAlgebra ℚ_[p] K]`, `[CompleteSpace K]`, `[CharZero K]`
  are in the `variable` block but **not used**: the decl carries
  `omit [CompleteSpace K] [CharZero K]`, does **not** `include hp`, and neither the
  statement nor the proof mentions `p` or the `ℚ_[p]`-algebra structure, so Lean's
  auto-bound-implicit machinery drops them. The **effective** signature is over
  `{K : Type*} [NormedField K] [IsUltrametricDist K]` only.)

Hypotheses (Lean side):
- `{x : K}` — the base point.
- `(hx : ‖x − 1‖ < 1)` — `x` is in the open unit ball around `1`.
- `(n : ℕ)` — the exponent.

Conclusion (math): `xⁿ` is again within distance `< 1` of `1`.

Conclusion (Lean): `‖x ^ n - 1‖ < 1`.

**Proof shape (induction on `n`):** base `n=0` gives `‖0‖ = 0 < 1`; step uses the
factorisation `xᵏ⁺¹ − 1 = (xᵏ − 1)·x + (x − 1)`, the ultrametric bound
`IsUltrametricDist.norm_add_le_max`, `‖x‖ ≤ 1` (itself from the ultrametric bound on
`(x−1)+1`), and `‖(xᵏ−1)·x‖ = ‖xᵏ−1‖·‖x‖ ≤ ‖xᵏ−1‖`, then `max_lt ih hx`. Three lines.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper lemma (the open-unit-ball-closed-under-powers fact), used to drive a
larger result (`padicLog_pow_p_of_norm_lt_one`); not a named theorem, not a new
structure, not a `## Main results` entry.

(Note: literature width was run EXHAUSTIVE regardless. SMALL is recorded for framing.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-line check is n/a (skipped).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "ultrametric field open unit ball around 1 closed under multiplication powers principal units" | yes | `U_n = 1 + 𝔪ⁿ = {u ∈ 𝒪× : v(u−1) ≥ n}`; `B_r` and `B̄_r` are subgroups of `(E,+)`; closed unit ball is the valuation ring | Multiple arXiv sources + Wikipedia "Unit disk"; the additive balls are additive subgroups, and `1 + 𝔪` is the multiplicative one |
| 2 | WebSearch (general form) | "non-archimedean valued field '1 + m' units one-units subgroup closed under powers norm less than one" | yes | `U₁(K) = 1 + 𝔪` = `{1 + a : |a| < 1}`; the principal units; `K* ⊇ 𝒪* ⊇ U₁(K) = 1 + 𝔪` splits as topological groups | ResearchGate "Summary on non-Archimedean valued fields", arXiv 1810.09975 "Jump sets in local fields" — `U₁` is a standard subgroup |
| 3 | WebSearch (named-after / aliases) | "local field higher unit groups U_n filtration 1 + m^n subgroup Neukirch Serre principal units multiplicative" | yes | `𝒰⁽ⁿ⁾ = 1 + 𝔪ⁿ`, `𝒰 = 𝒪× = 𝒰⁽⁰⁾`; quotients `𝒰/𝒰⁽ⁿ⁾ ≅ (𝒪/𝔪ⁿ)×`; cited to **Neukirch–Schmidt–Wingberg Ch. II §3.10, §5.3** and **Serre, Local Fields** | These are THE references; `U₁` being a subgroup (hence power-closed) is foundational, stated without fuss |
| 4 | ChatGPT MCP | — | n/a | — | ChatGPT MCP server not configured in this environment (`/setup-chatgpt` not run; no `mcp__*chatgpt*` tool present). Compensated with two extra WebSearch queries (#5, #10) and the nLab/MathOverflow channels below. |
| 5 | WebSearch (proof / explicit implication) | "'one-units' OR '1-units' multiplicatively closed power 'v(x-1)<1' implies 'v(x^n-1)<1' non-archimedean proof" | partial | concept confirmed; no source states the bare implication `v(x−1)<1 ⟹ v(xⁿ−1)<1` as a named result | It is a textbook *exercise* / immediate consequence of `U₁ ≤ K×` being a subgroup, not a separately-named theorem — exactly the signal that the *bundled* form (not the bare implication) is the right mathlib object |
| 6 | nLab | "valuation ring" / principal units (ncatlab.org/nlab/show/valuation+ring surfaced) | yes (weak) | nLab "valuation ring": `𝒪 = {x : v(x) ≥ 0}`, `𝔪 = {x : v(x) > 0}`; principal units `1 + 𝔪` referenced | nLab has the valuation-ring page; the principal-units subgroup is standard background, not a dedicated page |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept — this is an elementary inequality in a normed ring; no universal property / higher-categorical content to look up. |
| 8 | Stacks Project | (not queried in depth) | n/a | — | Not an algebraic-geometry / scheme-theoretic statement; it is a one-variable norm inequality. Stacks has valuation-ring material but nothing closer than the standard `1 + 𝔪` subgroup already found in channels 1–3. |
| 9 | MathOverflow / Math.StackExchange | principal units / `1 + 𝔪` subgroup generality (via WebSearch surfacing) | yes (background) | confirms `1 + 𝔪` is a subgroup of `𝒪×` in any non-archimedean field; the "closed under products/powers" fact is the multiplicative-closure half | Treated as folklore on these sites; consistent with channels 1–3 |
| 10 | recent arXiv (last 5 years) | "Jump sets in local fields" (arXiv 1810.09975), "First Cohomology of Local Units" (arXiv 2104.03299), "Filtration of the group of principal units…" | yes | the **group of principal units** `E₁ = 1 + 𝔪` and its filtration `Eₘ` are the central objects | Modern literature treats `1 + 𝔪` as a *group* (filtered module); strong evidence the mathlib-idiomatic target is the bundled subgroup, not a bare `‖xⁿ−1‖<1` implication |

The protocol passes: WebSearch ran ≥3 queries at distinct generality levels (specific
ball form, general principal-units form, named-after/Neukirch–Serre); ChatGPT MCP
recorded n/a with reason (server absent) and compensated; local references checked
(see summary); nLab checked; nCatLab/Stacks recorded n/a with reasons; MathOverflow
and recent arXiv checked.

### Literature summary (Phase 3)

Concept identified as: the **principal units** (a.k.a. *one-units* / *1-units*) of a
non-archimedean field, `U₁(K) = 1 + 𝔪 = {x ∈ 𝒪×_K : v(x − 1) > 0} = {x : ‖x − 1‖ < 1}`.
The theorem is the **multiplicative-closure (power) half** of the standard fact that
`U₁(K)` is a subgroup of `K×`.

Sources agree on the standard form: yes. Every local-field reference (Neukirch–Schmidt–
Wingberg ANT II.§3.10/§5.3, Serre *Local Fields*, and the modern arXiv literature on
unit filtrations) defines `1 + 𝔪ⁿ` and treats it as a multiplicative (sub)group as a
matter of course. The closure-under-powers statement is folklore — a one-line
consequence of `U₁ ≤ K×`.

Most general standard form: in *any* non-archimedean valued/normed ring with `‖1‖ = 1`,
the set `1 + {a : ‖a‖ < 1}` is a multiplicative submonoid (and, in the units, a
subgroup). The field/division structure is **not** essential to the closure-under-powers
direction — only submultiplicativity `‖ab‖ ≤ ‖a‖‖b‖`, `‖1‖ = 1`, and the ultrametric
inequality are used.

Generality dimensions where the literature varies:
- Ambient structure: stated for complete discretely-valued *local fields* in textbooks,
  but the closure fact holds for any **non-archimedean normed ring with `NormOneClass`**
  (no completeness, no discreteness, no field). Most general = `SeminormedRing` +
  `NormOneClass` + `IsUltrametricDist`.
- Packaging: bare predicate `‖x − 1‖ < 1` (user) vs. bundled **subgroup/submonoid**
  `1 + 𝔪` (modern literature; mathlib's analogous multiplicative object
  `IsUltrametricDist.ball_openSubgroup`). The modern idiom is the bundled object.

Disagreement with the literature: none on content. The user's form is correct but is a
*specialisation* (to `NormedField`) and *unbundled* (a bare implication rather than the
substructure the literature/mathlib idiom uses).

Project references: `n/a` — `projects/PadicLFunctions/.mathlib-quality/references/`
does not exist (only `overview/` is present); the `--refs` path passed points at the
skill's generic reference docs, not project source PDFs. Recorded n/a per protocol.

---

### Generality analysis — `boundary_norm_pow_sub_one_lt_one`

Literature-standard form (from Phase 3): in any non-archimedean normed ring with
`‖1‖ = 1`, `1 + {a : ‖a‖ < 1}` is multiplicatively closed; i.e. `‖x − 1‖ < 1` ⟹
`‖xⁿ − 1‖ < 1`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField K]` | normed field (mult. norm, `‖1‖=1`, division) | non-archimedean normed *ring* with `‖1‖=1` | **yes** | The proof uses only `norm_add_le_max` (ultrametric add, holds in `SeminormedAddGroup`), `norm_mul`/submultiplicativity (`‖ab‖≤‖a‖‖b‖`, holds in `SeminormedRing` via `norm_mul_le`), `norm_one`, and `‖x‖≤1`. **No division, no field, no `NormMulClass` equality is needed.** Weakens to `[SeminormedRing R] [NormOneClass R]`. This is exactly the typeclass cluster of mathlib's `IsUltrametricDist.norm_add_one_le_max_norm_one` (`Analysis/Normed/Ring/Ultra.lean`). |
| 2 | `[IsUltrametricDist K]` | non-archimedean | non-archimedean | NO | Essential — the whole proof is the ultrametric `max` bound; this is the defining hypothesis. |
| 3 | the four unused `p`-instances (`[NormedAlgebra ℚ_[p] K]`, `[CompleteSpace K]`, `[CharZero K]`, `[Fact p.Prime]`) | present in `variable` block | absent | already absent | Not part of the effective signature (auto-bound-implicit drops them; two are explicitly `omit`-ted). No action needed; just noted for completeness. |
| 4 | `(n : ℕ)` | nonneg-integer exponent | `n : ℕ` (powers) | NO (for this statement) | `ℕ` is correct for the *monoid*/submonoid closure. The `ℤ`-power / full-subgroup statement (`‖x⁻¹ − 1‖ < 1`) is the *additional* content of the bundled-subgroup form (Phase 4c), not a weakening of this one. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD
Number of weakening opportunities found: 1 (the `NormedField → SeminormedRing + NormOneClass` axis, row 1)

Proposed restatement (literature-weakened, bare-implication form):

```lean
theorem norm_pow_sub_one_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ < 1
```

Cost of restatement: **CHEAP** — the existing induction proof transfers essentially
verbatim (`norm_mul` becomes `norm_mul_le`'s `≤`; everything else is already
group/ring-level). No new ideas.

Since STRICTLY NARROWER → Phase 7 considers `YES-but-generalise-first` prominently.
4c (below) sharpens *what* to generalise to.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let `K` be a foo" preambles → typeclasses/instances? | no | already typeclass-driven (`[NormedField]`/`[IsUltrametricDist]`) | — |
| 2 | sequences/metric → filters/nets/topological? | no | finite induction over `ℕ` powers; no limit/convergence content to filter-ise | — |
| 3 | **construct** an object where a **universal-property class** would characterise it? | no | not a universal-property situation | — |
| 4 | **set-with-closure-predicate → bundled-substructure type** that composes with mathlib's lattices? | **YES** | bundle `1 + {a : ‖a‖ < 1}` as a `Submonoid R` (and a `Subgroup Rˣ`), exactly paralleling the *multiplicative* `IsUltrametricDist.ball_openSubgroup`/`closedBall_openSubgroup` already in `Analysis/Normed/Group/Ultra.lean`. The present theorem is then the `pow_mem`/`one_mem`-flavoured corollary of the bundled object. | the `Submonoid`/`Subgroup` lattice API: `pow_mem`, `mul_mem`, `prod_mem`, intersections, the `OpenSubgroup` topology, and a uniform statement of the principal-units filtration `U₁ ⊇ U₂ ⊇ …` |
| 5 | vector-space/metric/field-specific → modules/pseudometric/(semi)ring? | **YES** | weaken `NormedField` → `SeminormedRing + NormOneClass` (same as Phase 4b row 1) | the lemma then lives next to `norm_add_one_le_max_norm_one` and applies to ultrametric *rings* (e.g. `𝒪_K`, group algebras), not just fields |
| 6 | 1-categorical → higher/∞-categorical? | no | elementary inequality; no categorification | — |
| 7 | concrete index (`ℕ`,`ℤ`,`ℝ`) → arbitrary monoid/group? | partial | the bundled `Submonoid` makes `pow_mem` (ℕ) automatic; promoting to `Subgroup Rˣ` additionally gives `zpow_mem` (ℤ) for free | unifies the ℕ-power statement with the ℤ-power one without a second proof |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**
- Proposed mathlib-idiomatic restatement (the bundled object + this lemma as its corollary):

  ```lean
  -- in Mathlib/Analysis/Normed/Ring/Ultra.lean, namespace IsUltrametricDist,
  -- variable {R : Type*} [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

  /-- The principal units `1 + 𝔪 = {x | ‖x − 1‖ < 1}` form a submonoid of a
  non-archimedean normed ring with `‖1‖ = 1`. -/
  def oneAddBallSubmonoid : Submonoid R where
    carrier := {x | ‖x - 1‖ < 1}
    one_mem' := by simpa using zero_lt_one
    mul_mem' := by
      -- ‖xy − 1‖ = ‖(x−1)·y + (y−1)‖ ≤ max (‖x−1‖·‖y‖) ‖y−1‖ < 1
      sorry

  /-- The open unit ball around `1` is closed under powers (the present lemma,
  recovered as `Submonoid.pow_mem`). -/
  theorem norm_pow_sub_one_lt_one {x : R} (hx : ‖x - 1‖ < 1) (n : ℕ) :
      ‖x ^ n - 1‖ < 1 :=
    oneAddBallSubmonoid.pow_mem hx n
  ```

  (and, on the units, a `Subgroup Rˣ` giving `zpow_mem` and matching the
  multiplicative `ball_openSubgroup`.)
- Cost: **MODERATE** — bundling the submonoid is a small amount of new code (the
  `mul_mem'` is one ultrametric estimate); recovering the present lemma is then 1 line.
  The bare-implication weakening alone (Phase 4b) is CHEAP.
- Mathlib downstream this enables: the full `Submonoid`/`Subgroup` API (`pow_mem`,
  `zpow_mem`, `mul_mem`, `prod_mem`, lattice ops), an `OpenSubgroup` of `Rˣ`/`Kˣ`
  paralleling `ball_openSubgroup`, and a clean home for the principal-units filtration
  used throughout local-field / Iwasawa theory.
- Real mathematical improvement (not just "looks cooler"): it puts the *additive*
  principal-units object on the same bundled footing mathlib already gives the
  *multiplicative* one (`ball_openSubgroup`), eliminating the asymmetry and removing the
  need for every consumer (like this project) to re-prove power/product closure by hand.

Per Phase 4c "modern idiom available" + Phase 4b STRICTLY NARROWER → Phase 7 produces
`YES-but-generalise-first`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search
paths introduced). (The *proposed* bundled `Submonoid`/`Subgroup` in 4c would warrant a
risk pass when actually written, but the object under assessment is the theorem.)

---

### Mathlib search-status: `boundary_norm_pow_sub_one_lt_one`

[A] Lean-Finder — n/a: Lean-Finder MCP/tool not available in this environment. Compensated
    by [D] direct mathlib-source grep + [C]-style natural-language reasoning over the
    `Ultra` files, which were read in full.
[B] Loogle — type-pattern intent `‖_ ^ _ - 1‖ < 1` / `IsUltrametricDist → ‖_^_ - 1‖`:
    no `lean_loogle` tool live here; emulated via grep of the exact and near shapes
    over `.lake/packages/mathlib/` — no hits (see [D]).
[C] LeanSearch — natural-language intent "open unit ball around one closed under powers in
    ultrametric field / principal units closed under powers": no live `lean_leansearch`
    tool; the equivalent concepts were chased through Phase 3 literature + the mathlib
    `Ultra`/`ValuationSubring` source — closest objects identified (see Concluded).
[D] Grep mathlib src — searched `‖.*\^.* - 1‖ *< *1` (exact shape): **0 hits**.
    Searched `IsUltrametricDist` lemma heads across `Analysis/Normed/{Group,Ring,Field}/Ultra.lean`,
    `norm_add_one_le_max_norm_one`, `ball_openSubgroup`, `closedBall_openSubgroup`,
    `principalUnitGroup`, `pow_mem_closedBall`/`pow_mem_ball`, Padic `norm_sub_one`/`pow`.
[E] Name pattern — searched `boundary_`, `norm_pow_sub_one`, `norm_sub_one_*`, `principalUnit*`,
    `oneAdd*`, `one_unit*` over mathlib: no decl matching the additive
    `‖xⁿ − 1‖ < 1` statement.

Searched for both:
  - the user's current form (`NormedField` + `IsUltrametricDist`, `‖xⁿ − 1‖ < 1`),
  - the literature-standard / general form (`SeminormedRing + NormOneClass`, and the
    bundled `1 + 𝔪` submonoid/subgroup).

Relevant mathlib objects found (none is the statement):
  - `IsUltrametricDist.ball_openSubgroup` / `.closedBall_openSubgroup`
    (`Analysis/Normed/Group/Ultra.lean:162,176`): open/closed balls around `1` in a
    *`SeminormedGroup`* are open subgroups. **Different group:** this is the
    *multiplicative* group with multiplicative distance `dist x 1 = ‖x⁻¹·x'‖`. Our
    `‖x − 1‖` is the *additive* distance in the field; there is **no `SeminormedGroup`
    instance on `Kˣ`** with norm `‖x − 1‖`, so this lemma does **not** apply to our
    statement. It is the *parallel* object, which is exactly why the bundled additive
    version (Phase 4c) is the right contribution.
  - `IsUltrametricDist.norm_add_one_le_max_norm_one` (`Analysis/Normed/Ring/Ultra.lean:50`):
    `‖x + 1‖ ≤ max ‖x‖ 1` in `SeminormedRing + NormOneClass + IsUltrametricDist` — a
    **building block**, not the statement. Confirms the right typeclass home.
  - `ValuationSubring.principalUnitGroup` (`RingTheory/Valuation/ValuationSubring.lean:634`):
    `Subgroup Kˣ` with carrier `{x | A.valuation (x − 1) < 1}` and `mul_mem'`/`inv_mem'`
    proven. This is the **valuation-theoretic** sibling — same mathematics — but stated
    via a `Valuation`/`ValuationSubring` on `Kˣ`, not via a `NormedField`'s norm on `K`.
    Not our statement; see Phase 6 for why bridging to it is not a bounded composition.

Concluded: **not in mathlib** (all methods exhausted on both the user's form and the
literature-standard form). The exact additive statement `‖xⁿ − 1‖ < 1` is absent; mathlib
has the *multiplicative-group* ball-subgroup (`ball_openSubgroup`) and the
*valuation-theoretic* `principalUnitGroup`, but neither is the additive normed-field/ring
form, and neither specialises to it in ≤1 line (Phase 6).

---

### Call sites — `boundary_norm_pow_sub_one_lt_one`

Internal use count: 3 (all within the same project; **all in the declaring file**
`ValuesAtOne.lean`, none in any other file).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ValuesAtOne.lean:515 | `have hzp1 : ‖z ^ p - 1‖ < 1 := boundary_norm_pow_sub_one_lt_one hz p` |
| ValuesAtOne.lean:537 | `… (boundary_norm_pow_sub_one_lt_one hz (p ^ M)), ih, smul_smul, pow_succ, mul_comm]` |
| ValuesAtOne.lean:583 | `… (boundary_norm_pow_sub_one_lt_one hx k) hx, ih, succ_nsmul]` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none found) — the lemma is the single source of this fact in the project.

What the pattern tells us: 3 internal uses, no inline re-derivation. This is real
local API — consumers depend on it. The uses pass the exponent as `p`, `p^M`, `k`,
confirming the lemma's only relevant inputs are `hx : ‖x−1‖<1` and the exponent `n`,
i.e. `p` is incidental to the call context, not a dependency of the lemma. The 3-internal-use
pattern leans toward a YES-family verdict (the fact is genuinely needed and reusable), and
its complete absence from mathlib (Phase 5) plus its narrower-than-standard form (Phase 4)
points specifically at `YES-but-generalise-first` rather than `YES-add-as-is`.

### Composition check (Phase 6)

Can `boundary_norm_pow_sub_one_lt_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 — via the multiplicative `IsUltrametricDist.ball_openSubgroup`:
  - Mathlib decls used: `IsUltrametricDist.ball_openSubgroup`, `Subgroup.pow_mem`.
  - Result: **fails**. `ball_openSubgroup` lives in a `SeminormedGroup` and its ball is
    `Metric.ball (1 : S) r` under the *multiplicative* distance `dist x 1 = ‖x⁻¹·1‖`.
    There is no `SeminormedGroup` instance on `Kˣ` (or `K`) whose norm equals `‖x − 1‖`.
    Building one (a multiplicative group seminorm `‖x‖' := ‖x − 1‖` on the units) is
    *itself* the content of this lemma's `mul_mem'` estimate — circular, not a composition.

Attempt 2 — via `ValuationSubring.principalUnitGroup` + `Subgroup.pow_mem`:
  - Mathlib decls used: `NormedField.toValued` / `NormedField.valuation`,
    `ValuationSubring.principalUnitGroup`, `ValuationSubring.mem_principalUnitGroup_iff`,
    `Subgroup.pow_mem`, plus `Units.mk0` / norm↔valuation translation.
  - Result: **fails (not bounded)**. This route requires: (a) producing the canonical
    `ValuationSubring` from the norm — which goes through `NormedField.toValued`, needing
    `NontriviallyNormedField` + a rank-one `Valuation` instance that the lemma's actual
    hypotheses (`NormedField` + `IsUltrametricDist`) do **not** supply; (b) promoting `x`
    to `Kˣ` (needs `x ≠ 0`, an extra derivation); (c) rewriting `A.valuation (x−1) < 1`
    ↔ `‖x−1‖ < 1`; (d) `Subgroup.pow_mem`; (e) translating back to `‖xⁿ−1‖ < 1`. That is
    ≥5 steps across `Valued`/`ValuationSubring`/`Kˣ`/valuation-vs-norm with instance
    requirements beyond the hypotheses — a genuine proof, not a 1–3 call composition.

Conclusion: **NOT-COMPOSABLE** (in the bounded ≤3-call sense). The direct 3-line
ultrametric induction (the existing proof) is both simpler and strictly more general than
any mathlib-composition route. → Phase 7 considers the YES verdicts.

---

## Verdict: `boundary_norm_pow_sub_one_lt_one`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): unambiguous — the **principal units** `U₁ = 1 + 𝔪` of a
  non-archimedean field; this theorem is the power-closure half of "`U₁ ≤ K×`". Standard
  (Neukirch–Schmidt–Wingberg II.§3.10/§5.3, Serre *Local Fields*); modern arXiv literature
  treats `1 + 𝔪` as a bundled (filtered) group.
- Generality analysis (Phase 4): **STRICTLY NARROWER** — `NormedField` weakens (CHEAP) to
  `SeminormedRing + NormOneClass`; and (Phase 4c) the mathlib-idiomatic target is the
  **bundled `Submonoid`/`Subgroup`** `1 + 𝔪`, paralleling the existing multiplicative
  `IsUltrametricDist.ball_openSubgroup`.
- Mathlib search (Phase 5): **not in mathlib** in this additive form; the multiplicative
  `ball_openSubgroup` (wrong group structure) and the valuation-theoretic
  `principalUnitGroup` (on `Kˣ`, via `Valuation`) are siblings, neither directly our form.
- Composition check (Phase 6): **NOT-COMPOSABLE** (the `principalUnitGroup` bridge needs
  rank-one-valuation instances the hypotheses lack and is ≥5 steps).

**Rationale:**

The fact is genuinely wanted in mathlib: mathlib already bundles the *multiplicative*
ultrametric ball around `1` as `IsUltrametricDist.ball_openSubgroup`, but has **no**
counterpart for the *additive* principal-units ball `1 + 𝔪 = {x : ‖x − 1‖ < 1}` on the
ring/field side — even though `norm_add_one_le_max_norm_one` (the building block) already
sits in `Analysis/Normed/Ring/Ultra.lean`. The named gap is precisely that asymmetry: the
additive `1 + 𝔪` submonoid/subgroup, and its power-closure, is missing, which is why this
project (and the cyclotomic / local-field developments generally) re-prove it by hand. So
the verdict is a YES family, not a NO.

It is **not** `YES-add-as-is` for two gating reasons. (1) Phase 4b found the form STRICTLY
NARROWER than the proof supports — the `NormedField` hypothesis is a needless
specialisation of `SeminormedRing + NormOneClass` (a CHEAP weakening that lands the lemma
in its natural mathlib home). (2) Phase 4c found a real MODERN-IDIOM improvement: the
bundled `Submonoid R` / `Subgroup Rˣ` form (mirroring `ball_openSubgroup`) is the
mathlib-idiomatic object, with this theorem recovered as `Submonoid.pow_mem` in one line —
unlocking the whole `pow_mem`/`zpow_mem`/`mul_mem`/lattice/`OpenSubgroup` API and giving the
principal-units filtration a uniform home. Per the verdict gate, STRICTLY NARROWER and a
real modern-idiom improvement both force `YES-but-generalise-first`.

**Reason for the generalisation:**
- LITERATURE-WEAKENING: Phase 4b — the user's `NormedField` form is strictly narrower than
  the proof supports (`SeminormedRing + NormOneClass`).
- MODERN-IDIOM (Bourbaki 2.0): Phase 4c — bundle `1 + 𝔪` as a `Submonoid`/`Subgroup`,
  matching mathlib's existing multiplicative `ball_openSubgroup`.

**Proposed restatement (minimal — the bare-implication weakening):**

```lean
theorem norm_pow_sub_one_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ < 1 := by
  sorry  -- the existing 3-line induction transfers verbatim (norm_mul → norm_mul_le)
```

**Proposed restatement (preferred — the bundled modern-idiom form):**

```lean
namespace IsUltrametricDist
variable {R : Type*} [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

/-- The principal units `1 + 𝔪 = {x | ‖x − 1‖ < 1}` of a non-archimedean normed ring
with `‖1‖ = 1`, as a submonoid (the additive counterpart of `ball_openSubgroup`). -/
def oneAddBallSubmonoid : Submonoid R where
  carrier := {x | ‖x - 1‖ < 1}
  one_mem' := by simpa using zero_lt_one
  mul_mem' := by sorry  -- ‖xy − 1‖ = ‖(x−1)y + (y−1)‖ ≤ max (‖x−1‖‖y‖) ‖y−1‖ < 1

theorem norm_pow_sub_one_lt_one {x : R} (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ < 1 :=
  oneAddBallSubmonoid.pow_mem hx n
end IsUltrametricDist
```

Estimated cost of regeneralisation: bare-implication weakening **CHEAP**; bundled-submonoid
form **MODERATE** (one extra `mul_mem'` ultrametric estimate). EXPENSIVE-cost note: n/a —
this is cheap; and per the gate, cost would not downgrade the verdict regardless.

Mathlib downstream this enables (MODERN-IDIOM, required):
- `Submonoid.pow_mem` / `Subgroup.zpow_mem` recover the ℕ- and ℤ-power closure for free.
- `mul_mem` / `prod_mem` give finite-product closure of principal units (used in the
  cyclotomic `norm_pow_sub_one_*` family and in Iwasawa-theoretic unit computations).
- An `OpenSubgroup Rˣ` instance paralleling `ball_openSubgroup`, giving the principal units
  their topology + the filtration `U₁ ⊇ U₂ ⊇ …` a uniform statement.
- Removes the asymmetry whereby mathlib bundles the multiplicative ultrametric `1`-ball but
  not the additive principal-units `1`-ball — the gap this project hit and worked around.

What proofs were blocked by the old (bare, `NormedField`) form: any consumer wanting
product/inverse/topological closure of `1 + 𝔪` must currently re-derive it; the project's
own `ValuesAtOne.lean` uses the bare lemma three times precisely because no bundled object
exists to lean on.

Next action: run `/generalise PadicLFunctions.MeasureR.boundary_norm_pow_sub_one_lt_one`
(it will tension against both the literature-standard `SeminormedRing + NormOneClass` form
from Phase 3/4b and the bundled-submonoid modern-idiom form from Phase 4c), then `/cleanup`
the result and open a mathlib PR adding the bundled object to
`Mathlib/Analysis/Normed/Ring/Ultra.lean` alongside `norm_add_one_le_max_norm_one`, with the
power-closure lemma as its corollary. PR grouping: ship the `oneAddBallSubmonoid` (+ its
`Subgroup Rˣ` / `OpenSubgroup` API and `norm_pow_sub_one_lt_one`) as one coherent PR.

---

## Next step

Run `/generalise PadicLFunctions.MeasureR.boundary_norm_pow_sub_one_lt_one` to restate at
`SeminormedRing + NormOneClass + IsUltrametricDist` and, preferably, as the bundled
`IsUltrametricDist.oneAddBallSubmonoid` (the additive counterpart of the existing
`IsUltrametricDist.ball_openSubgroup`), with this theorem recovered as `Submonoid.pow_mem`.
Then `/cleanup` and open a mathlib PR to `Mathlib/Analysis/Normed/Ring/Ultra.lean`.
