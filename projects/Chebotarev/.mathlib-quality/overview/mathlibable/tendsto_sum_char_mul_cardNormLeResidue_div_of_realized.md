# /mathlibable report — `Chebotarev.tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`

## Baseline (Phase 0)
- lake build:               (stale local build — assessed from source per the standing
                              environment note; the decl elaborates as part of `CebotarevDensity`)
- decl:                     `Chebotarev.tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`
                              resolved at
                              `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean:3400`
- namespace:                `Chebotarev` (file closes with `end Chebotarev` at line 3437) — so the
                              parsed qualified name in the prompt is **confirmed**.
- kind:                     theorem (`public`, i.e. NOT `private` — unusually for this file, where
                              `cardNormLeResidue`, `exists_tendsto_cardNormLeResidue_div`,
                              `cardNormLeResidue_density_const_of_realized` are all `private`)
- has sorry:                no
- module docstring summary: "Effective counting of ideals by class and norm residue" — the
                              `O(N^{1-1/d})` refinement of mathlib's ideal-counting asymptotics,
                              additionally split by the residue of the ideal norm mod `c`. Arithmetic
                              engine of the Frobenius-fibre equidistribution (Gap B / L2).

---

## Statement (Phase 1)

`tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` is a theorem stating:

> Let `K` be a number field of degree `d`, `c` a positive modulus, and `S ≤ (ℤ/cℤ)ˣ` a subgroup
> **all of whose elements are realized as ideal-norm residues** — i.e. for each `a ∈ S` there is a
> nonzero integral ideal `𝔟` of `𝓞 K` with `N(𝔟) ≡ a (mod c)`. Then for every **nontrivial**
> character `χ : S → ℂˣ`, the `χ`-twisted average of norm-residue ideal counts tends to `0`:
> `(∑_{s ∈ S} χ(s) · #{I : N(I) ≤ N, N(I) ≡ s (mod c)}) / N → 0` as `N → ∞`.

The mechanism: by the per-class density tower the leading density
`κ_s = lim_N #{N(I) ≤ N, N(I) ≡ s}/N` is **constant in `s ∈ S`** (Lang VI §3 Thm 3, via the
per-class densities; the realizer hypothesis is what makes `κ` transferable across `S` by
`cardNormLeResidue_density_transfer`). The twisted average then converges to
`(∑_{s∈S} χ(s))·κ = 0·κ = 0` by character **row orthogonality** (`∑_{s∈S} χ(s) = 0` for `χ ≠ 1`).

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K] [NumberField K]` — the number field.
- `c : ℕ` `[NeZero c]` — the modulus.
- `S : Subgroup (ZMod c)ˣ` — the residue subgroup.
- `χ : S →* ℂˣ` — a multiplicative character of `S`.

Hypotheses (Lean side):
- `hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰, (Ideal.absNorm 𝔟 : ZMod c) = (a : ZMod c)` — every residue
  in `S` is an ideal-norm residue (the **realizer** hypothesis; built to dodge the ℚ(i) trap).
- `hχ : χ ≠ 1` — nontriviality of the character.

Conclusion (math): `(∑_{s∈S} χ(s)·#{N(I) ≤ N, N(I) ≡ s})/N → 0`.

Conclusion (Lean): `Filter.Tendsto (fun N : ℕ => (∑ s : S, (χ s : ℂ) * (Nat.card {I : (Ideal (𝓞 K))⁰
  // Ideal.absNorm I ≤ N ∧ (Ideal.absNorm I : ZMod c) = (s : ZMod c)} : ℂ)) / (N : ℂ))
  Filter.atTop (nhds 0)`.

---

## Size classification (Phase 2a)

Verdict: **SMALL** (leaning BIG-adjacent)
Reason: It is a named producer in the `## Architecture` section of the module docstring (the "`hF`
producer"), so it has main-result flavour *within the project*; but it is mathematically a Fourier-
orthogonality glue step (κ-constancy ⇒ twisted average → 0), not a named theorem. Not named after a
person/place. Literature width run EXHAUSTIVE regardless.

## One-line check (Phase 2b)

Kind is `theorem` — n/a (one-line check is for `def`/`abbrev`/`structure`). Skipped.

---

## Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | counting ideals in arithmetic progressions number field norm congruence density | yes | Weber/Landau `I_K(x)=κ_K x + O(x^{1-1/d})`; class-split `P_K(x,𝔠)=C_K x+O(...)` | Murty–Van Order; the *unsplit* and *class-split* counts are classical & in mathlib. Residue-split is the project's extension. |
| 2  | WebSearch (named source)         | Gun Ramaré Sivaraman "Counting ideals in ray classes" JNT 2023        | yes  | Tatuzawa (1973) asymptotic for ray-class counts, made fully explicit | JNT 243 (2023) 13–37. The cited source #1 in the file's docstring. Confirms the count-by-residue is a real, recent, named paper — but the *theorem* there is the count, not the χ-twist→0 corollary. |
| 3  | WebSearch (consequence / aliases)| density ideals norm residue class group independent character sum orthogonality vanishing | partial | character orthogonality decomposes ideal-class counting; twisted sums → 0 is the *mechanism* of equidistribution | The "twisted average → 0" appears only as an **intermediate orthogonality step** in equidistribution/Chebotarev proofs, never as a named standalone result. |
| 4  | ChatGPT MCP                      | (self-contained: is "twisted average → 0 for nontrivial χ" named? most general form? abstract home?) | n/a — **MCP DOWN** | Codex backend failed (matches the standing env warning) | Fallback: covered by channels 1–3 + 6 + 10. |
| 5  | Local references                 | grep `.mathlib-quality/references/` and `refs/Chebotarev/`             | n/a  | neither directory exists | recorded n/a (no refs dir on this checkout). |
| 6  | nLab                             | character orthogonality finite abelian group / equidistribution norms ideals | yes  | row+column orthogonality for finite abelian `G`: `∑_{g} χ(g) = |G|·[χ=1]`; `Ĝ = Hom(G,ℂˣ)`, `|Ĝ|=|G|` | nLab "group character". The orthogonality kernel is utterly standard; the number-field application is not an nLab page. |
| 7  | nCatLab (categorical)            | —                                                                     | n/a  | not a categorical concept | the statement is analytic NT + finite Fourier; no (higher-)categorical content. |
| 8  | Stacks Project (alg geom)        | —                                                                     | n/a  | not an algebraic-geometry concept | ideal-norm counting asymptotics are analytic NT, outside Stacks' scope. |
| 9  | MathOverflow / Math.SE           | (covered via channel 3 sweep: equidistribution of ideal norms, character sums) | partial | twisted-sum cancellation is folklore "orthogonality kills the non-principal part" | no canonical MO post elevating it to a named lemma. |
| 10 | recent arXiv (≤5 yr)             | equidistributed nilsequences summed over ideal norms twisted by Dirichlet characters of K | yes  | cancellation when mean-zero sequences are summed over ideal norms twisted by characters | arXiv work on ideal-norm character twists confirms this is a *technique*, recurring inside larger equidistribution arguments — not a packaged result. |

### Literature summary (Phase 3)

Concept identified as: two classical ingredients welded together —
  (a) **density of ideals by norm residue is constant over the realized-residue subgroup** (Lang,
      *Algebraic Number Theory* GTM 110, Ch VI §3 Thm 3; Gun–Ramaré–Sivaraman, JNT 243 (2023);
      Tatuzawa 1973); and
  (b) **finite-abelian character row orthogonality** `∑_{s∈S} χ(s) = 0` for `χ ≠ 1` (nLab; textbook).
Sources agree on the standard form of EACH ingredient: yes. The **composite statement** ("twisted
average of residue-counts → 0 for nontrivial χ over the realized subgroup") is **not a named or
standalone result** anywhere — it is an intermediate Fourier-orthogonality step on the way to
equidistribution of ideal norms / a fibre of Chebotarev.
Most general standard form: the κ-constancy holds for the **ray/ideal-class density** under realized
residues; orthogonality holds for any finite abelian group. The composite is bespoke: it packages
exactly the `hF` decay hypothesis that the project's uniform counter consumes.
Generality dimensions where the literature varies:
  - error term sharpness: from `O(x^{1-1/d})` (Weber) to explicit (GRS) — orthogonal to this decl.
  - residue structure: full `(ℤ/c)ˣ` vs the **realized subgroup** `S` — the project deliberately
    restricts to `S` (the ℚ(i)-trap avoidance); the literature κ-constancy is naturally stated on
    the realized subgroup too.
Disagreement with the literature: none. The decl is faithful; it is simply *more specific* (a glue
corollary) than anything the literature names.

---

## Generality analysis — `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` (Phase 4)

Literature-standard form (from Phase 3): there is no *named* literature statement to match; the
nearest reusable mathematical object is **"if a function `f : S → ℝ` on a finite abelian group has a
constant per-point density `κ` (equivalently every nontrivial character moment of the density
vanishes), then every nontrivial-character-twisted average → 0"**, instantiated at
`f = (residue-count)/N`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard / reusable form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|-------------------------------------|---------------------|----------------------------------|
| 1 | `S : Subgroup (ZMod c)ˣ` + the whole ideal-count payload | residue subgroup of a number field, counts = `Nat.card` of an ideal subtype | finite abelian group `G` + an arbitrary family of count functions `n_s(N)` with `n_s(N)/N → κ_s` and `κ_s` constant on `G` | **yes** | The proof body uses NOTHING ideal-specific beyond `exists_tendsto_cardNormLeResidue_div` (existence of the per-residue density) and `cardNormLeResidue_density_const_of_realized` (constancy). Strip those two project facts as a hypothesis `(hκ : ∀ s, Tendsto (n_s ·/N) atTop (𝓝 κ)) (hconst : ∀ s, κ_s = κ_{1})` and the theorem becomes a pure finite-Fourier statement over any `[CommGroup G] [Fintype G]`. |
| 2 | `χ : S →* ℂˣ`, `hχ : χ ≠ 1` | character of `S` | character of `G` | already general | the ℂˣ-valued character + nontriviality are exactly the row-orthogonality hypothesis; `sum_char_self_eq_zero_of_ne_one` already lives at `[CommGroup G] [Fintype G]`. |
| 3 | realizer `hS` | every `a ∈ S` is an ideal-norm residue | the *purpose* of `hS` is solely to feed `cardNormLeResidue_density_const_of_realized`, i.e. to GET `κ_s ≡ const` | **yes** | `hS` is not used directly; it is consumed only to prove `hconst : κf s = κf 1`. In the abstract restatement it disappears, replaced by the constancy hypothesis itself. |
| 4 | conclusion `Tendsto (∑ χ(s)·Nat.card{...}/N) (𝓝 0)` | bespoke ideal `Nat.card` subtype | `Tendsto (∑ χ(s)·n_s(N)/N) (𝓝 0)` | **yes** | the `Nat.card {...}` is definitionally `cardNormLeResidue K c s N` (the proof does `simp only [cardNormLeResidue]`); it is an opaque `ℕ`-valued count to the argument. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (welded to the number-field ideal count,
when the proof is a pure finite-abelian-Fourier argument).
Number of weakening opportunities found: 4 (collapsing to one structural move: replace the ideal
payload by an abstract count family + constant-density hypothesis).
Proposed restatement (abstract finite-Fourier kernel — the genuinely reusable lemma):

```lean
theorem tendsto_sum_char_mul_div_of_const_density
    {G : Type*} [CommGroup G] [Fintype G]
    (n : G → ℕ → ℝ) (κ : ℝ)
    (hκ : ∀ s : G, Filter.Tendsto (fun N : ℕ ↦ n s N / (N : ℝ)) Filter.atTop (nhds κ))
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    Filter.Tendsto
      (fun N : ℕ ↦ (∑ s : G, ((χ s : ℂˣ) : ℂ) * (n s N : ℂ)) / (N : ℂ))
      Filter.atTop (nhds 0) := by
  sorry  -- exactly the current proof: tendsto_finsetSum + sum_mul + sum_char_self_eq_zero_of_ne_one
```

Cost of restatement: **CHEAP** — mechanical. The current proof already factors through precisely
this: `hκf` gives `hκ`, `hconst` gives the common `κ = κf 1`, `hlim` is `tendsto_finsetSum`, and the
finish is `sum_char_self_eq_zero_of_ne_one`. The number-field theorem then becomes a ~4-line
corollary feeding `exists_tendsto_cardNormLeResidue_div` + `cardNormLeResidue_density_const_of_realized`
into the abstract lemma.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | "let X be a foo" preambles → typeclasses? | no | already typeclass-driven (`[CommGroup G] [Fintype G]`); the realizer is a genuine hypothesis, not a bundling | — |
| 2  | sequences/metric → filters/topological? | partial | the index `N : ℕ → atTop` could be a general filter `l` with `(N : ℂ) →_l ∞`, but `atTop` on ℕ is the natural counting index | minor; not a real improvement |
| 3  | construct → universal property? | no | nothing is constructed | — |
| 4  | set+closure-predicate → bundled substructure? | no | `S` is already a bundled `Subgroup` | — |
| 5  | vector-space/field-specific → weaken typeclass? | **yes** (this is the real move) | replace the ideal-count payload by `n : G → ℕ → ℝ` over any `[CommGroup G] [Fintype G]` — see 4b | the abstract lemma composes with ANY constant-density count family, not just ideals; it is the reusable Fourier kernel |
| 6  | 1-categorical → higher-categorical? | no | n/a | — |
| 7  | concrete index (ℕ/ℤ/ℝ) → general? | partial | `c : ℕ` modulus is intrinsic; `G = S` already abstract once payload is stripped | covered by 4b |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and it coincides with the 4b weakening: the genuinely mathlib-
worthy object is the **abstract finite-abelian-character / constant-density ⇒ twisted-average-→-0
kernel** (`tendsto_sum_char_mul_div_of_const_density` above), which is number-field-free.
  - Cost: CHEAP.
  - Mathlib downstream this enables: any equidistribution argument that twists a constant-leading-
    density count by characters of a finite abelian group (Chebotarev fibres, Dirichlet-progression
    counts, ray-class counts) gets the cancellation for free; it composes with mathlib's
    `Filter.Tendsto` API and (once added) a general finite-abelian row-orthogonality lemma.
  - Real mathematical improvement: it separates the **pure Fourier orthogonality** (reusable) from
    the **number-field density input** (project-specific), which is exactly the mathlib factoring
    discipline. The current decl fuses them.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. Skipped.

---

## Mathlib search-status: `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` (Phase 5)

[A] Lean-Finder       (index unavailable offline)                          n/a: offline; substituted by [D] grep of mathlib source + WebSearch over mathlib4_docs
[B] Loogle            `Filter.Tendsto (fun N => (∑ _, _ * Nat.card _)/_) _ (nhds 0)`; `Ideal.absNorm, ZMod, Filter.Tendsto` | no hits — no mathlib decl pairs ideal-norm `absNorm … : ZMod c` with a `Tendsto … (nhds 0)` twisted sum
[C] LeanSearch        "ideal norm residue mod c counting density character sum tends to zero" | no hits (matches via WebSearch over mathlib4_docs — only the unsplit/class-split asymptotics surface)
[D] Grep mathlib src  `grep "ZMod\|residue\|progression"` in `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean` → **0 matches**; the file's only theorems are `tendsto_norm_le_and_mk_eq_div_atTop`, `tendsto_norm_le_div_atTop₀`, `tendsto_norm_le_div_atTop` (NO residue split). Char orthogonality: only `Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean` (`sum_characters_eq_zero` — for `DirichletCharacter R n`, NOT general `CommGroup`). No general finite-abelian `∑_{g} χ g = 0` anywhere in mathlib.
[E] Name pattern      grep `tendsto.*residue`, `sum_char.*Tendsto`, `cardNormLeResidue` across mathlib | no hits (these names are project-only)

Searched for both:
  - the user's current form (ideal `Nat.card` twisted sum → 0): **not in mathlib**.
  - the literature-standard / reusable forms:
    * ideal counting asymptotics: mathlib has `NumberField.Ideal.tendsto_norm_le_div_atTop` and
      `tendsto_norm_le_and_mk_eq_div_atTop` — but **only unsplit and class-split**, never residue-
      split mod `c`. The project's effective per-residue count
      (`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, the GRS/Lang engine) is **NOT** in
      mathlib.
    * character row orthogonality: mathlib has it ONLY for `DirichletCharacter`
      (`DirichletCharacter.sum_characters_eq_zero`), not for an abstract `[CommGroup G] [Fintype G]`
      — which is precisely why the project ships its own `sum_char_self_eq_zero_of_ne_one`.

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard forms)** — and
moreover the chain it stands on (effective residue-split ideal count) is not in mathlib either, so it
cannot even be *re-derived* against mathlib today.

---

## Composition check (+ call-sites) (Phase 6)

### Call sites — `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`

Internal use count (excluding the declaring file): **1**
External-to-file callers: 1 distinct file (same project).

| Caller file:line          | Usage pattern (one-line excerpt) |
|---------------------------|-----------------------------------|
| `CebotarevDensity/ZetaProduct.lean:1265` | `(fun χ hχ ↦ tendsto_sum_char_mul_cardNormLeResidue_div_of_realized K m (hζ.autToPow K).range (realizes_autToPow_range K L m hζ) χ hχ)` — discharges the `hF` Fourier-decay hypothesis of `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform` inside `exists_kappa_uniform`. |

(Three further textual mentions — `ZetaProduct.lean:1005`, `:1065`, `:1253`, and
`IdealCongruenceCount.lean:51` — are docstring references, not call sites.)

Inline-derivation grep (re-derived elsewhere without the lemma?): (none).

Call-sites signal: **K = 1 internal use, no inline re-derivation.** Per the Phase-6 table this leans
toward "possibly the wrong grain — could be inlined", but here it is a deliberate `hF`-producer/
consumer split: the theorem packages exactly the hypothesis the uniform counter consumes one file
over. So it is a real (if thin) API boundary within the project, not dead code.

### Composition check (Phase 6a)

Can `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: feed mathlib's `tendsto_norm_le_and_mk_eq_div_atTop` (class-split count) + a residue
refinement + `DirichletCharacter.sum_characters_eq_zero`.
  - Result: **fails.** Mathlib's count is class-split, not residue-split; there is no mathlib bridge
    from "class density" to "norm-residue density mod `c`", and no mathlib residue-split count at
    all. The realizer→constancy step (`cardNormLeResidue_density_const_of_realized`) has no mathlib
    analogue, and `sum_characters_eq_zero` is for `DirichletCharacter`, not the abstract `S`-character
    used here.

Attempt 2: use only the project's own primitives.
  - The actual proof is: `choose κf hκf` (per-residue density existence,
    `exists_tendsto_cardNormLeResidue_div`) → `hconst` (constancy via
    `cardNormLeResidue_density_const_of_realized`) → `tendsto_finsetSum` (mathlib) +
    `Finset.sum_div`/`push_cast`/`ring` → `sum_char_self_eq_zero_of_ne_one` (project) → rewrite. That
    is **several `have`s with real reasoning between them**, and two of the inputs
    (`exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_const_of_realized`) are
    PRIVATE and rest on the project's effective ideal count, which is not in mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib. (It IS a short composition from the project's *own*
private tower — but that tower is not in mathlib, so this is not a "mathlib has the building blocks"
situation.)

---

## Verdict: `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): each ingredient is classical (Lang VI §3 Thm 3; GRS JNT 243 (2023);
  finite-abelian row orthogonality, nLab); the **composite** "twisted average → 0" is an unnamed
  intermediate Fourier-orthogonality step, never a standalone literature result.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the proof is a pure
  finite-abelian-Fourier argument welded to the number-field ideal count; 4 weakening opportunities
  collapse to one move (strip the ideal payload to an abstract constant-density count family). Phase
  4c independently flags the same abstract kernel as the real mathlib object (MODERN-IDIOM).
- Mathlib search (Phase 5): not in mathlib in any form; the residue-split ideal count it depends on
  is also not in mathlib; mathlib's char orthogonality is `DirichletCharacter`-only.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (composable only from the project's own
  private, not-yet-upstreamed tower).

**Rationale:**

The theorem is mathematically sound and rests on genuinely classical facts, but in its current form
it is the **public face of a private, project-specific tower** (`cardNormLeResidue`,
`exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_const_of_realized`, ultimately the
GRS/Lang effective residue-split ideal count `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`),
none of which is in mathlib. Its signature is welded to a bespoke `Nat.card`-of-ideal-subtype count,
its docstring is written entirely in the project's internal vocabulary ("the `hF` producer",
"consumed by `exists_card_...`", "the ℚ(i)-trap"), and it has a single internal call site. Shipping
it verbatim to mathlib is impossible today: the effective residue-split ideal count it stands on must
land first, and the statement as written carries project-glue intent rather than a reusable
mathematical interface.

But the proof body reveals a clean, number-field-free kernel that mathlib genuinely lacks: **over any
finite abelian group `G`, if a count family `n_s(N)` has a constant per-point density
`n_s(N)/N → κ`, then for every nontrivial character `χ : G → ℂˣ` the twisted average
`(∑_s χ(s)·n_s(N))/N → 0`.** That is the real contribution (Phase 4c MODERN-IDIOM), and it composes
with every character-twisted equidistribution argument, not just this one. It also exposes a *second*
gap the project already worked around: mathlib has finite-abelian character row orthogonality only
for `DirichletCharacter` (`DirichletCharacter.sum_characters_eq_zero`), not for an abstract
`[CommGroup G] [Fintype G]` — which is why the project wrote `sum_char_self_eq_zero_of_ne_one`. The
honest verdict is therefore generalise-first: lift the Fourier kernel out (and, separately, upstream
the general row-orthogonality lemma), leaving the number-field theorem as a thin corollary that stays
in the project until the effective ideal count is itself upstreamed.

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b found the current form strictly narrower than the natural reusable
    statement — the proof uses nothing ideal-specific.
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c found the contemporary mathlib formulation (the abstract
    constant-density / character-twist kernel) to be a real organisational improvement — it separates
    pure finite-Fourier orthogonality from the number-field density input.

**Proposed restatement** (the mathlib-worthy kernel):

```lean
/-- If a count family `n_s(N)` over a finite abelian group `G` has a common leading density
`n_s(N)/N → κ`, then every nontrivial-character-twisted average of the counts vanishes in the
limit. -/
theorem tendsto_sum_char_mul_div_of_const_density
    {G : Type*} [CommGroup G] [Fintype G]
    (n : G → ℕ → ℝ) (κ : ℝ)
    (hκ : ∀ s : G, Filter.Tendsto (fun N : ℕ ↦ n s N / (N : ℝ)) Filter.atTop (nhds κ))
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    Filter.Tendsto
      (fun N : ℕ ↦ (∑ s : G, ((χ s : ℂˣ) : ℂ) * (n s N : ℂ)) / (N : ℂ))
      Filter.atTop (nhds 0) := by
  sorry  -- current proof: tendsto_finsetSum + Finset.sum_div + sum_char_self_eq_zero_of_ne_one
```

Estimated cost of regeneralisation: **CHEAP** (the existing proof already factors through this; the
number-field theorem becomes a ~4-line corollary plugging
`exists_tendsto_cardNormLeResidue_div` + `cardNormLeResidue_density_const_of_realized` into it).

Mathlib downstream this enables:
  - every character-twisted equidistribution count (Chebotarev fibres, Dirichlet/ray-class
    progressions) reuses the cancellation;
  - it composes with mathlib `Filter.Tendsto` API and with a general finite-abelian row-orthogonality
    lemma (itself a worthwhile upstreaming: lift `sum_char_self_eq_zero_of_ne_one` from
    `CharacterOrthogonality.lean` — mathlib only has the `DirichletCharacter` special case today).

Note: this is **not** a verdict driven by regeneralisation cost (it is CHEAP); it is driven by the
fact that the current form fuses a reusable Fourier kernel with project-private number-field
machinery that is not yet in mathlib.

**Next action:** run `/generalise Chebotarev.tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`
to extract the abstract `tendsto_sum_char_mul_div_of_const_density` kernel (tensioning against the
finite-Fourier form above), keep the number-field theorem as a project-local corollary, and
separately consider upstreaming the general finite-abelian row-orthogonality lemma
`sum_char_self_eq_zero_of_ne_one` (mathlib presently has only `DirichletCharacter.sum_characters_eq_zero`).
Do not attempt to upstream the number-field theorem itself until the effective residue-split ideal
count (`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`) is in mathlib.

---

## Next step

Run `/generalise Chebotarev.tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`: extract the
abstract finite-abelian constant-density character-twist kernel (`tendsto_sum_char_mul_div_of_const_density`),
leave the number-field statement as a thin corollary, and flag the general row-orthogonality lemma
for separate upstreaming. The number-field theorem stays in-project pending upstreaming of the
effective residue-split ideal count it depends on.
