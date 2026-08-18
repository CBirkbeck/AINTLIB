# `/mathlibable` report — `PadicLFunctions.pow_norm_sum_le`

**Final verdict: `NO-composable-from-mathlib`**
(close to the `NO-mathlib-has-it` boundary — see Phase 7; the `m = 1` case *is* literally in mathlib.)

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (mathlib pinned at `rev = 005f0aa67b69`, toolchain `leanprover/lean4:v4.32.0-rc1`; `.lake/build/lib` empty — stale, per task note do not block on full build)
- decl `PadicLFunctions.pow_norm_sum_le`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:692`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The p-adic exponential and logarithm (RJW Lem 5.14): `exp`/`log` convergence and isometry on a nonarchimedean complete normed `ℚ_[p]`-algebra field; `pow_norm_sum_le` is an internal ultrametric power-bound helper in the coefficient-estimate chain (E-cluster, `norm_coeff_pow_le`).

The declaration sits under an `omit` line that drops `[NormedAlgebra ℚ_[p] L]` and `[CompleteSpace L]` from the section's variable block, so its effective context is:

```lean
variable {L : Type*} [NormedField L] [IsUltrametricDist L]

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- Ultrametric power bound: `‖∑ f i‖ᵐ ≤ C` whenever every term satisfies `‖f i‖ᵐ ≤ C`. -/
theorem pow_norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → L) {m : ℕ} (hm : 1 ≤ m)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i ∈ s, ‖f i‖ ^ m ≤ C) :
    ‖∑ i ∈ s, f i‖ ^ m ≤ C
```

---

### Statement (Phase 1)

`PadicLFunctions.pow_norm_sum_le` is **a theorem** stating:

> In a normed field `L` whose norm is ultrametric (nonarchimedean), let `s` be a finite index set and `f : ι → L`. If `m ≥ 1` and `C ≥ 0` and every term satisfies `‖f i‖^m ≤ C` for `i ∈ s`, then `‖∑_{i∈s} f i‖^m ≤ C`.

Mathematically this is the **strong (ultrametric) triangle inequality for finite sums**, `‖∑ f i‖ ≤ maxᵢ ‖f i‖`, repackaged by raising both sides to the fixed power `m` and bounding the per-term `m`-th powers by a common constant `C`. The `^m` form is bookkeeping for a downstream Legendre-type estimate where the natural quantity is `‖·‖^(p-1)`.

Variables / typeclasses involved (Lean side):

- `L` with `[NormedField L]` — the value field. (Field structure is *not used by the proof*; only the additive seminormed-group structure is.)
- `[IsUltrametricDist L]` — the norm is nonarchimedean: `‖x + y‖ ≤ max ‖x‖ ‖y‖`. This is the essential hypothesis.
- `{ι : Type*}` — arbitrary index type.
- `(s : Finset ι)` — the finite index set summed over.
- `(f : ι → L)` — the summands.
- `{m : ℕ}` — the exponent.

Hypotheses (Lean side):

- `(hm : 1 ≤ m)` — needed only so the empty-sum case `0^m = 0 ≤ C` holds (`m = 0` would give `‖∅-sum‖^0 = 1`, which need not be `≤ C`).
- `(hC : 0 ≤ C)` — nonnegativity of the bound, used both for the empty case and to lift to `ℝ≥0` internally.
- `(hf : ∀ i ∈ s, ‖f i‖ ^ m ≤ C)` — the per-term bound on `m`-th powers.

Conclusion (math): the `m`-th power of the norm of the finite sum is `≤ C`.

Conclusion (Lean): `‖∑ i ∈ s, f i‖ ^ m ≤ C` (a `Prop`, type `ℝ` inequality).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — no new structure, not a named theorem, not a `## Main results` entry. It is one rung in the coefficient-estimate ladder (`norm_coeff_prod_le` → `norm_coeff_pow_le` → `summable_prod_family`) supporting the genuine main result (`exp`/`log` convergence, RJW Lem 5.14).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~12 substantive lines (a `rcases` empty/nonempty split, an argmax `obtain`, and a `calc`).
One-liner verdict: **n/a — kind is theorem, not def.**

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | ultrametric norm "norm of sum" "max of norms" nonarchimedean finite sum | yes | `‖∑ aᵢ‖ ≤ maxᵢ ‖aᵢ‖` | Kedlaya 18.787 abs-values notes; standard nonarchimedean fact |
| 2 | WebSearch (general / named) | nonarchimedean absolute value `\|a_1+...+a_n\| ≤ max` ultrametric finite sum | yes | `\|a₁+…+aₙ\| ≤ max\|aᵢ\|` | Conrad/Stanford handouts, Berkeley FLT notes, MIT 18.785 Lec 8 — universal, unnamed |
| 3 | WebSearch (power variant) | "strong triangle inequality" power monotone `x^n` nonarchimedean norm bound sum p-adic | yes | base inequality only; Cauchy-criterion use `\|aₙ+…+aₙ₊ₘ\| ≤ maxᵢ\|aᵢ\|` | Cambridge p-adic notes, Thorne/Conrad, MathWorld "Strong Triangle Inequality" — **no power-of-sum variant named anywhere** |
| 4 | ChatGPT MCP | (intended: standard form + generality + historical evolution) | n/a | — | ChatGPT MCP server not installed in this environment (`/setup-chatgpt` not run); recorded n/a. Compensated by extra WebSearch generality passes (#1–#3) + nLab + Wikipedia + MathWorld. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` | n/a | (no references dir) | directory absent; `refs/` symlink also absent — recorded n/a |
| 6 | nLab | `ultrametric+space` (strong triangle inequality, finite-sum/power) | partial | `max(d(x,y),d(y,z)) ≥ d(x,z)` | nLab states the pairwise ultrametric inequality only; **no finite-sum or power version** |
| 7 | nCatLab / categorical | — | n/a | — | not a categorical concept — a real-analysis inequality; nothing to category-ify |
| 8 | Stacks Project | — | n/a | — | not an algebraic-geometry concept (elementary normed-field inequality) |
| 9 | MathOverflow / Math.SE | (covered transitively via #1–#3 result pages: Berkeley/MIT/Stanford lecture PDFs) | yes | same as #2 | finite-sum ultrametric bound is folklore; no MO thread treats the `^m` variant as a named result |
| 10 | recent arXiv (≤5y) | non-Archimedean norms / p-adic functional series (1411.4195, 2512.22692, 2508.16322) | partial | uses `\|∑\| ≤ max\|·\|` as a step | appears only as an inline proof step, never as a standalone "power of norm of sum" lemma |

#### Literature summary (Phase 3)

Concept identified as: **the ultrametric / strong triangle inequality, extended to finite sums** — `‖a₁ + … + aₙ‖ ≤ maxᵢ ‖aᵢ‖`. Equivalently `‖∑_{i∈s} f i‖ ≤ s.sup' (‖f ·‖)`.

Sources agree on the standard form: **yes** — Kedlaya, Conrad, Thorne, MIT 18.785, Wikipedia, MathWorld all state `‖x+y‖ ≤ max ‖x‖ ‖y‖` and use the finite-sum extension (often via the Cauchy criterion) without giving it a special name.

Most general standard form: for any nonarchimedean (ultrametric) seminormed additive group, `‖∑_{i∈s} f i‖ ≤ maxᵢ ‖f i‖` (i.e. bounded by `Finset.sup'` of the term-norms, or by any common upper bound `C` of the term-norms).

Generality dimensions where the literature varies:
  - underlying structure: stated for nonarchimedean *fields/absolute values* in number-theory texts, but the proof only needs an *additive group with an ultrametric norm* (this is how mathlib states it).
  - the **`^m` power wrapping is not a literature variant at all** — it is a monotone corollary (`a ≤ b ⇒ aᵐ ≤ bᵐ` for `a ≥ 0`). No source isolates it as a result.

Disagreement with the literature: **none on the base inequality.** The user's form differs only by the (non-standard) `^m` repackaging, which the literature treats as a trivial post-composition, not a theorem.

---

### Generality analysis — `PadicLFunctions.pow_norm_sum_le` (Phase 4)

Literature-standard form (from Phase 3): `‖∑_{i∈s} f i‖ ≤ maxᵢ ‖f i‖` for an ultrametric *seminormed additive group*.

| # | Parameter / hypothesis | Current Lean form | Literature-standard / mathlib form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|------------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]` | normed **field** | ultrametric **seminormed add. comm. group** | **yes** | proof never multiplies or inverts; only uses `‖·‖` of an additive group. Mathlib's `norm_sum_le_of_forall_le_of_nonneg` is stated for `[SeminormedAddCommGroup M]`. The `Field` is wholly unnecessary. |
| 2 | `[IsUltrametricDist L]` | ultrametric norm | ultrametric norm | NO | essential — without it the bound is false |
| 3 | `(hf : … ‖f i‖^m ≤ C)` + `^m` conclusion | bound on `m`-th powers | base form bounds `‖f i‖` directly | (n/a — not a *weakening*, see 4b/4c) | the `^m` is a specialisation by a monotone post-map, not a generality axis |
| 4 | `{C : ℝ} (hC : 0 ≤ C)` | explicit constant `C` | `Finset.sup'` of term-norms (sharp) | sharper form exists | mathlib also has the `sup'` form (`Finset.Nonempty.norm_sum_le_sup'_norm`); the `C`-bounded form is the convenience corollary `norm_sum_le_of_forall_le_of_nonneg` |

#### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (on the typeclass axis: `NormedField` where `SeminormedAddCommGroup` suffices) **AND simultaneously a non-standard specialisation** (the `^m` wrapper).
Number of weakening opportunities found: 1 substantive (`NormedField` → `SeminormedAddCommGroup`).

This does **not** push the verdict toward `YES-but-generalise-first`, because Phase 5 shows mathlib **already has the maximally-general base form** (`norm_sum_le_of_forall_le_of_nonneg`, stated for `SeminormedAddCommGroup` + `IsUltrametricDist`). There is nothing to contribute by generalising — the general form is upstream already. The user's lemma is a *field-specialised, `^m`-wrapped* restatement of an existing mathlib lemma plus one monotone step.

#### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | "Let L be a field" → typeclass instead of bundled hyp? | partial | already a typeclass; the move is to *weaken* it to `SeminormedAddCommGroup` (see 4a #1) | mathlib's `norm_sum_le_*` already lives at that generality |
| 2 | sequences/metric → filters/topological? | no | this is a finite-sum algebraic inequality; no limiting process to filter-ise | — |
| 3 | construct object → universal property? | no | it is a `Prop`, not a construction | — |
| 4 | set+closure predicate → bundled substructure? | no | no substructure involved | — |
| 5 | field/metric-specific → weaken typeclass to module/(semi)ring/group? | **yes** | `[NormedField L]` ⇒ `[SeminormedAddCommGroup M] [IsUltrametricDist M]` | exactly mathlib's existing `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` generality |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | index is already `ι : Type*` over a `Finset`; maximally general | — |

#### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no new idiom** — the only "modernisation" (row 5) is a typeclass weakening that mathlib has *already done* on the base lemma. It is therefore not a contribution; it is a reason this lemma is redundant. There is no contemporary reformulation that turns `pow_norm_sum_le` into something mathlib lacks.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.pow_norm_sum_le` (Phase 5)

Search method note: Loogle / LeanSearch / Lean-Finder MCP servers are not wired into this environment, so the type-pattern and NL searches were executed as equivalent `grep` queries over the pinned mathlib source tree (`.lake/packages/mathlib/Mathlib`), plus the `to_additive` source-lemma inspection. The base lemma was found directly and confirmed in active use.

```
[A] Lean-Finder       (server n/a)                              n/a: not wired; substituted by [D]+[E] over pinned source
[B] Loogle            ‖∑ _ ∈ _, _‖ ^ _ ≤ _                       no exact hit: 6 source hits for `‖∑…‖ ^ _`, all EQUALITIES
                                                                  (InnerProductSpace/Subspace, l2Space, lpSpace Parseval-type `^2`;
                                                                  ZLattice/Summable `^r`) — none is the ultrametric "≤ max" power form
[C] LeanSearch        "power of norm of finite sum at most C,    no exact hit (the base "norm of ultrametric sum ≤ C" maps to [D])
                       ultrametric / nonarchimedean"
[D] Grep mathlib src  norm_sum_le_of_forall_le_of_nonneg          HIT — IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
                      (+ to_additive twins of                     defined (multiplicatively) at
                       norm_prod_le_of_forall_le_of_nonneg)       Mathlib/Analysis/Normed/Group/Ultra.lean:256;
                                                                  additive twin used at Mathlib/NumberTheory/Padics/MahlerBasis.lean:126
[E] Name pattern      pow_norm_sum / norm_sum_pow / sum_norm_pow  no hit (only our project decl + unrelated
                                                                  GelfandFormula.pow_norm_pow_one_div_tendsto…)
```

Searched for **both**:
  - the user's current `^m` form — **not in mathlib** (all five methods; no power-of-norm-of-sum lemma exists)
  - the literature-standard / general base form — **in mathlib**, as:

```lean
-- Mathlib/Analysis/Normed/Group/Ultra.lean  (additive twin generated by `to_additive`)
-- [SeminormedAddCommGroup M] [IsUltrametricDist M]
theorem IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    {s : Finset ι} {f : ι → M} {C : ℝ}
    (h_nonneg : 0 ≤ C) (hC : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C
```

Companions also present in the same file:
  - `Finset.Nonempty.norm_sum_le_sup'_norm` (sharp `sup'` bound, `Ultra.lean:207` twin)
  - `exists_norm_finsetSum_le_of_nonempty : s.Nonempty → ∃ i ∈ s, ‖∑ j ∈ s, f j‖ ≤ ‖f i‖` (`Ultra.lean:267` twin) — the argmax extractor
  - `nnnorm_sum_le_of_forall_le`, `norm_sum_le_of_forall_le_of_nonempty`

Concluded: **found building blocks** — mathlib has the `m = 1` statement *verbatim and more general* (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, for any ultrametric seminormed additive group), plus the argmax extractor and the monotone power lemma `pow_le_pow_left₀`. The exact `‖∑‖^m ≤ C` form is **not** in mathlib, but it is a 1–2 step composition of these (see Phase 6).

---

### Call sites — `PadicLFunctions.pow_norm_sum_le` (Phase 6.0)

Internal use count: **1** (within `projects/PadicLFunctions/`, excluding the declaring lemma's own line)
External-to-file callers: **0** distinct files (the one caller is in the same file)

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:747 | `refine pow_norm_sum_le (L := ℚ_[p]) _ _ (by … omega) (by positivity) fun l hl => norm_coeff_prod_le …` — inside `norm_coeff_pow_le`, after `rw [coeff_pow]`, to lift the per-tuple bound `‖∏‖^(p-1) ≤ p^(k−n)` to the sum `‖[Xᵏ](Gⁿ)‖^(p−1) ≤ p^(k−n)` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `pow_norm_sum_le`?): **(none found)** — the only use of the `^(p-1)`-of-a-sum pattern routes through this lemma.

**What the call-sites pattern tells you:** `K = 1` internal use, no external callers. Per the Phase-6 signal table this leans **NO-composable** — a single call site for a lemma whose body is a short composition of existing mathlib API is the canonical "could be inlined / wrong abstraction" signature. It is genuinely used (not dead code), and the single use is well-motivated (the `m = p−1` exponent on a coefficient sum), but one consumer does not justify a standalone mathlib lemma when the consumer is a project-internal Legendre estimate.

#### Composition check (Phase 6)

Can `pow_norm_sum_le` be derived from mathlib in ≤3 chained calls?

**Attempt 1** (tightest, via the argmax extractor):
```lean
example {ι} (s : Finset ι) (f : ι → L) {m : ℕ} (hm : 1 ≤ m) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i ∈ s, ‖f i‖ ^ m ≤ C) : ‖∑ i ∈ s, f i‖ ^ m ≤ C := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa [zero_pow (Nat.one_le_iff_ne_zero.mp hm)] using hC          -- empty case
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
    exact (pow_le_pow_left₀ (norm_nonneg _) hle m).trans (hf i hi)     -- nonempty case
```
  - Mathlib decls used: `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`, `pow_le_pow_left₀`, `norm_nonneg`, `zero_pow`, `Nat.one_le_iff_ne_zero`.
  - Result: **succeeds**, but it is a 5–6 line proof with a *case split* and a `calc`/`.trans`, not a single ≤3-call expression. The empty-sum branch (where `1 ≤ m` makes `0^m = 0 ≤ C`) cannot be folded into the nonempty branch's chain.
  - Notes: the case split is irreducible because the argmax extractor requires `s.Nonempty`. This is a *small proof*, on the COMPOSABLE/NOT-COMPOSABLE boundary.

**Attempt 2** (avoid the case split via the `C`-bounded base lemma directly): not available cleanly — `norm_sum_le_of_forall_le_of_nonneg` wants `∀ i, ‖f i‖ ≤ C`, but the hypothesis bounds `‖f i‖^m`, not `‖f i‖`. Recovering `‖f i‖ ≤ C^(1/m)` introduces `Real.rpow` and is *worse* than Attempt 1. So Attempt 1 is the canonical inline form.

Conclusion: **COMPOSABLE** (in the practical sense: a 5–6 line inline derivation from named mathlib lemmas, no new mathematical idea, no `ring_nf`/`aesop` automation). It exceeds the literal "≤3 chained calls" by a case split, but every step is a direct mathlib-lemma application — this is exactly the "building blocks present, inline at the call site" situation that `NO-composable-from-mathlib` describes, with `NO-mathlib-has-it` applying outright to the `m = 1` slice.

---

## Verdict: `PadicLFunctions.pow_norm_sum_le`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the canonical fact is the ultrametric finite-sum bound `‖∑ aᵢ‖ ≤ max ‖aᵢ‖` (Kedlaya/Conrad/MIT 18.785/Wikipedia/MathWorld). The `^m` wrapper is **not** a named literature variant — it is a trivial monotone corollary.
- Generality analysis (Phase 4): STRICTLY NARROWER on the typeclass axis (`NormedField` where `SeminormedAddCommGroup` suffices) — but mathlib already holds the general form, so there is nothing to generalise *into mathlib*.
- Mathlib search (Phase 5): the `m = 1` statement is in mathlib **verbatim and strictly more general** — `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` (`Mathlib/Analysis/Normed/Group/Ultra.lean:256`, additive twin used at `MahlerBasis.lean:126`). The `^m` form is not present, but the argmax extractor `exists_norm_finsetSum_le_of_nonempty` and `pow_le_pow_left₀` are.
- Composition check (Phase 6): COMPOSABLE — a 5–6 line inline derivation from the three named mathlib lemmas; one internal call site, no external consumers.

**Rationale.** `pow_norm_sum_le` is not new mathematics for mathlib. Its `m = 1` case is *literally already in mathlib* and at greater generality (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, stated for any ultrametric `SeminormedAddCommGroup`, whereas the project lemma needlessly demands a `NormedField`). The only thing the project lemma adds over that mathlib lemma is raising the conclusion to a fixed power `m ≥ 1` and bounding the per-term `m`-th powers — a monotone post-composition (`pow_le_pow_left₀`) that the literature never isolates as a result and that mathlib justifiably omits. The lemma exists purely as bookkeeping for the project's Legendre estimate, where the natural exponent is `m = p − 1`; that motivation is project-internal, evidenced by the single in-file call site (`norm_coeff_pow_le`, line 747) and zero external consumers. This is the textbook `NO-composable-from-mathlib` profile: mathlib has the building blocks, the user's form is a short composition, and no standalone lemma is warranted. (The verdict sits a hair from `NO-mathlib-has-it`: if the `^m` packaging were dropped — i.e. for `m = 1` — it would be a flat `NO-mathlib-has-it` citing the same decl. It lands on `NO-composable` only because the literal stated form carries the extra power and so needs the one-step monotone composition rather than a zero-step alias.)

**Refactor-actionable bar.**

For NO-composable-from-mathlib:
  WHY not: Mathlib has the maximally-general ultrametric finite-sum bound `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` (the `m = 1` case, verbatim, for `SeminormedAddCommGroup` + `IsUltrametricDist`). The project's `‖∑‖^m ≤ C` form is that lemma's `m = 1` conclusion raised to a fixed power via `pow_le_pow_left₀` after extracting the max-norm term with `exists_norm_finsetSum_le_of_nonempty`. No genuinely new lemma is needed — the power-wrapped form is a 5–6 line inline composition (one case split + one `.trans`), and the field hypothesis is spurious.

  Mathlib building blocks:
  - `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` — `Mathlib/Analysis/Normed/Group/Ultra.lean:256` (additive twin via `to_additive`)
  - `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty` — `Mathlib/Analysis/Normed/Group/Ultra.lean:267` (additive twin; the argmax extractor)
  - `pow_le_pow_left₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:470`
  - `norm_nonneg`, `zero_pow`, `Nat.one_le_iff_ne_zero` (glue)

  Composition sketch (the inline form):
  ```lean
  -- replace `pow_norm_sum_le _ _ hm hC hbound` with:
  by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simpa [zero_pow (Nat.one_le_iff_ne_zero.mp hm)] using hC
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      exact (pow_le_pow_left₀ (norm_nonneg _) hle m).trans (hbound i hi)
  ```

  Call sites in our project (from Phase 6.0): **K = 1** — `PadicExp.lean:747` inside `norm_coeff_pow_le` (with `m := p − 1`, `C := (p:ℝ)^(k−n)`).

  Refactor plan: at the single call site (`PadicExp.lean:747`), inline the composition above in place of `pow_norm_sum_le (L := ℚ_[p]) _ _ … …`. Concretely: after the existing `rw [coeff_pow]`, do the empty/nonempty split, pull the max coefficient-tuple via `exists_norm_finsetSum_le_of_nonempty`, and finish with `(pow_le_pow_left₀ (norm_nonneg _) hle (p-1)).trans (norm_coeff_prod_le … l hi)`. The argument flow matches (the existing `fun l hl => norm_coeff_prod_le …` already supplies the per-term bound). Then delete `pow_norm_sum_le` from `PadicExp.lean`.

  Caveat / alternative (kept project-local): if the maintainer prefers to keep a one-call helper rather than inline a 6-line block at the one site, that is a legitimate *project-hygiene* choice — but the helper should then (a) be renamed/relocated as a clearly project-internal lemma and (b) weaken `[NormedField L]` to `[SeminormedAddCommGroup L] [IsUltrametricDist L]` to match the mathlib base lemma it wraps. Either way it does **not** belong in a mathlib PR.

  Next action: inline the composition at `PadicExp.lean:747` (or keep it project-local with the weakened typeclass), and delete `pow_norm_sum_le` from the mathlib-candidate set.

---

## Next step

Delete `pow_norm_sum_le` from the project's mathlib-candidate set; inline the 5–6 line composition (`exists_norm_finsetSum_le_of_nonempty` + `pow_le_pow_left₀`, with the empty-sum case via `zero_pow`) at its single call site `PadicExp.lean:747` inside `norm_coeff_pow_le`. The `m = 1` content is already in mathlib as `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` (at strictly greater generality), so no mathlib PR is warranted.
