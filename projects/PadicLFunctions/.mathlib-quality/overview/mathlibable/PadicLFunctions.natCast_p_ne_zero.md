# `/mathlibable` report — `PadicLFunctions.natCast_p_ne_zero`

**Final verdict: `NO-composable-from-mathlib`** (1–2 mathlib calls; also redundant with the project's own `PadicLFunctions.charZero_of_qpAlgebra`). Refactor: inline at the 4 call sites and delete.

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task instruction); **reasoned from source**
- decl `PadicLFunctions.natCast_p_ne_zero`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:294`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the extended (Iwasawa-branch) p-adic logarithm `extLog` — extends `padicLog` to rational-valuation elements `x` with `x^m = p^k·y`, `y` in the exponential ball.

Elaborated statement (with the file's `variable`/`omit` scope resolved):

```lean
variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]   -- IsUltrametricDist, CompleteSpace omitted here

theorem natCast_p_ne_zero : (p : L) ≠ 0 :=
  norm_ne_zero_iff.mp <| by
    rw [norm_natCast_p p]; have := hp.out.pos; positivity
```

Active hypotheses after `omit`: `p : ℕ`, `Fact p.Prime`, `NormedField L`, `NormedAlgebra ℚ_[p] L`.

---

### Statement (Phase 1)

`natCast_p_ne_zero` is a theorem stating the following:

> Let `p` be a prime and let `L` be a normed field that is a normed `ℚ_p`-algebra. Then the image of the natural number `p` under the canonical ring map `ℕ → L` is nonzero: `(p : L) ≠ 0`.

This is an instance of the elementary fact that, in a ring of **characteristic zero**, the cast of a nonzero natural number is nonzero. Here `L` inherits characteristic zero from `ℚ_p` (which is characteristic zero) via the injective algebra map `ℚ_p → L`. The supplied proof instead routes through the norm: `‖(p:L)‖ = p⁻¹ > 0`, hence `(p:L) ≠ 0`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; `Fact`-wrapped so `hp.out : p.Prime` gives `p.pos`, `p.ne_zero`, `p.one_lt`.
- `L : Type*`, `[NormedField L]` — the ambient normed field.
- `[NormedAlgebra ℚ_[p] L]` — makes `L` a `ℚ_p`-algebra, supplying `algebraMap ℚ_[p] L` and `norm_algebraMap'`.

Hypotheses (Lean side): none beyond the typeclasses.

Conclusion (math): `p ≠ 0` in `L`.

Conclusion (Lean): `(p : L) ≠ 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper lemma — the nonvanishing of `(p:L)`, used purely as a side condition (feeds `zpow_ne_zero` / `pow_ne_zero` / `smul_right_injective`). Not a named theorem, not a `Main results` entry, introduces no structure.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (a `norm_ne_zero_iff.mp` applied to a 1-line `by` block).
One-liner verdict: **n/a** — kind is `theorem`, not a `def`. The defeq/diamond/API-name exemptions (Phase 2b) apply only to definitions; a one-line *theorem* carries no definitional content, so the relevant signal is the composition check (Phase 6), not the def-exemption table.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "cast of nonzero natural number is nonzero in characteristic zero ring Nat.cast_ne_zero"       | yes  | `CharZero R ⟹ (n:R) ≠ 0` for `n ≠ 0`                  | Mathlib `CharZero.Defs`, Wikipedia *Characteristic (algebra)*, nLab *characteristic*. This IS the definition of characteristic zero. |
|  2 | WebSearch (general form)         | "algebra over field characteristic zero injective algebra map CharZero propagation"            | yes  | injective ring/algebra map from a char-0 ring transports char-0 | Standard: field extensions / algebra maps are injective and preserve characteristic zero. |
|  3 | WebSearch (named-after / aliases)| "norm of p in p-adic field equals 1/p nonzero, p-adic algebra natural number cast nonzero"     | yes  | `‖p‖_p = p⁻¹ = 1/p ≠ 0`; `q ≠ 0 ⟹ padicNorm p q ≠ 0`   | MathWorld *p-adic Norm*, mathlib `PadicNorm`. Confirms the norm route the proof uses. |
|  4 | ChatGPT MCP                      | (standard form + generality + historical evolution of "nonzero natCast in char 0")             | n/a  | —                                                      | ChatGPT MCP not configured in this environment (not in the available tool set). Recorded n/a; the fact is elementary and channels 1–3 + nLab already pin the standard form unambiguously. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`        | n/a  | (no references dir)                                    | Neither directory exists — recorded n/a. |
|  6 | nLab                             | "characteristic" / "characteristic zero"                                                       | yes  | char 0 ⇔ `ℤ ↪ R` (equivalently `ℕ`-cast injective)    | nLab *characteristic* (returned by query #1) gives the abstract statement: char 0 means the unique ring map `ℤ → R` is injective. |
|  7 | nCatLab (if categorical)         | —                                                                                              | n/a  | —                                                      | Not a categorical concept; "ring of characteristic zero" is 1-algebraic. n/a with reason. |
|  8 | Stacks Project (if alg geom)     | —                                                                                              | n/a  | —                                                      | Not an algebraic-geometry concept; elementary ring theory. n/a with reason. |
|  9 | MathOverflow / Math.StackExchange| "(p : K) ≠ 0 char zero" generality                                                             | n/a  | —                                                      | No research-level question needed; the fact is textbook. Covered by #1/#6. n/a with reason. |
| 10 | recent arXiv (last 5 years)      | (via #2) characteristic-zero / prime-field formalization                                       | yes/marginal | "From natural numbers to prime fields and finite fields" (arXiv 2209.01069) | Confirms the formalized treatment of `ℕ → field` casts; no novelty for this lemma. |

Protocol pass check:
- WebSearch ran 3 distinct queries at different generality levels (specific char-0 cast; general algebra-map char-0 propagation; the p-adic-norm specialization) ✓
- ChatGPT MCP: unavailable in this environment → recorded n/a with reason ✓ (the fact is elementary; not load-bearing)
- Local references: checked, absent → n/a ✓
- nLab: checked ✓
- Stacks / nCatLab / MathOverflow / arXiv: each checked, n/a-with-reason or hit ✓

### Literature summary (Phase 3)

Concept identified as: **"the cast of a nonzero natural number is nonzero in a characteristic-zero ring"** — i.e. `CharZero R ⟹ ∀ n ≠ 0, (n:R) ≠ 0`. Specialized to `n = p` prime and `R = L` a `ℚ_p`-algebra (which is char 0 because `ℚ_p` is and the algebra map is injective). Equivalent norm-theoretic phrasing: `‖(p:L)‖ = p⁻¹ ≠ 0`.

Sources agree on the standard form: **yes**. This is the *definition* of characteristic zero (nLab, Wikipedia) together with the textbook fact that `ℚ_p` has characteristic zero and that a ring map out of a field is injective.

Most general standard form: in any `AddMonoidWithOne R` with `[CharZero R]`, for any `n : ℕ` with `n ≠ 0`, `(n : R) ≠ 0`. (This is precisely `Nat.cast_ne_zero`.)

Generality dimensions where the literature varies:
- **The ring**: from a specific field (`ℚ`, `ℚ_p`) up to any `AddMonoidWithOne` with `CharZero`. The maximally general carrier is `[AddMonoidWithOne R] [CharZero R]`.
- **The element**: from the specific prime `p` up to any nonzero natural number.

Disagreement with the literature: none. The user's statement is a doubly-specialized instance (carrier fixed to a `ℚ_p`-algebra field; element fixed to `p`) of a maximally general, definitional fact mathlib already states.

---

### Generality analysis — `PadicLFunctions.natCast_p_ne_zero`

Literature-standard form (from Phase 3): `[AddMonoidWithOne R] [CharZero R] {n : ℕ} (hn : n ≠ 0) : (n : R) ≠ 0` — i.e. mathlib's `Nat.cast_ne_zero`.

| # | Parameter / hypothesis        | Current Lean form                | Literature-standard form                 | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|----------------------------------|-------------------------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]`             | normed field                     | `AddMonoidWithOne` (no norm, no field)    | **yes**             | The result needs only `CharZero L`. The `NormedField` structure is irrelevant to the *conclusion*; the project's proof uses the norm merely as a route, but the char-0 route avoids it entirely. |
| 2 | `[NormedAlgebra ℚ_[p] L]`     | normed `ℚ_p`-algebra             | (replaced by) `[CharZero L]`              | **yes**             | The only consequence used is `CharZero L`, which follows from this typeclass via `charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective` (the project's own `charZero_of_qpAlgebra`). The general statement just assumes `CharZero` directly. |
| 3 | element is the prime `p`      | fixed prime `p`                  | any `n : ℕ`, `n ≠ 0`                       | **yes**             | Nothing in the conclusion uses primality beyond `p ≠ 0` (`hp.out.ne_zero`). Generalizes to arbitrary nonzero `n`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (on all three axes).
Number of weakening opportunities found: 3.
Maximally general form: `Nat.cast_ne_zero` (which mathlib already has — see Phase 5). The fully-generalized restatement of this lemma *is literally a mathlib lemma*, so "generalise first" is moot: the general form already exists. This pushes the verdict toward a NO bucket, not `YES-but-generalise-first`.

Cost of restatement: n/a — the general form is already in mathlib.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                      | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                            | no       | —                      | Already fully typeclass-based. |
|  2 | sequences/metric → filters/topological?                                                       | no       | —                      | No limiting/topological content; it's an algebraic nonvanishing. |
|  3 | construct an object → universal-property class?                                               | no       | —                      | No object constructed. |
|  4 | set-with-closure-predicate → bundled substructure?                                            | no       | —                      | No substructure. |
|  5 | vector-space/metric/field-specific → weaken to module/pseudometric/(semi)ring?                | **yes**  | drop `NormedField`/`NormedAlgebra`, assume `[AddMonoidWithOne L] [CharZero L]` | This is exactly `Nat.cast_ne_zero`; mathlib already realizes the modern weakened-typeclass form. |
|  6 | 1-categorical → higher/∞-categorical?                                                          | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive groups/monoids?                                   | **yes**  | replace prime `p` by any `n : ℕ`, `n ≠ 0`         | Already done by `Nat.cast_ne_zero`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and mathlib already implements it** (`Nat.cast_ne_zero` over `[CharZero R]`). Because the modern, maximally-general form already exists in mathlib, the modern-idiom observation does **not** flip this to `YES-but-generalise-first`; it reinforces `NO` (the right form is already upstream, and our form is a 1–2 call composition of it).

---

### Diamond / defeq risk — `PadicLFunctions.natCast_p_ne_zero`

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `PadicLFunctions.natCast_p_ne_zero`

[A] Lean-Finder       n/a — MCP not configured in this environment; substituted grep over the mathlib source tree (method [D]).
[B] Loogle            `⊢ (↑?n : ?R) ≠ 0` / `CharZero _ → Nat.cast _ ≠ 0`   n/a as live MCP (not configured); resolved by source grep [D] → `Nat.cast_ne_zero`.
[C] LeanSearch        "natural number cast nonzero characteristic zero"     n/a as live MCP; resolved by [D].
[D] Grep mathlib src  `cast_ne_zero`, `charZero_of_injective_algebraMap`, `Algebra.charZero_of_charZero`, `Prime.ne_zero`, `norm_ne_zero_iff` over `.lake/packages/mathlib/Mathlib/`  →  **multiple hits** (see below)
[E] Name pattern      `natCast_p_ne_zero`, `natCast_ne_zero`, `cast_ne_zero` in project + mathlib  → project decl is the only `natCast_p_ne_zero`; mathlib has the general `Nat.cast_ne_zero`.

Searched for both:
- the user's current form (`(p:L) ≠ 0` for a `ℚ_p`-algebra) — **no dedicated mathlib lemma** under this exact narrow signature (expected: it is a 1-line specialization, not something mathlib would state).
- the literature-standard / general form (`(n:R) ≠ 0` for `CharZero R`, `n ≠ 0`) — **FOUND**.

Key mathlib hits (read in source, not just name-cited):

1. **`Nat.cast_ne_zero`** — `Mathlib/Algebra/CharZero/Defs.lean:74`:
   ```lean
   theorem Nat.cast_ne_zero {R} [AddMonoidWithOne R] [CharZero R] {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0
   ```
   This is the general form. `(p : L) ≠ 0` is `Nat.cast_ne_zero.mpr hp.out.ne_zero` once `CharZero L` is available.

2. **`charZero_of_injective_algebraMap`** — `Mathlib/Algebra/CharP/Algebra.lean:77`:
   ```lean
   theorem charZero_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
       (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A
   ```
   Supplies `CharZero L` from `CharZero ℚ_[p]` + injectivity of `algebraMap ℚ_[p] L` (injective because `ℚ_p` is a field → `RingHom.injective`). It is a *theorem*, not an instance — which is exactly why the project wrote a helper; see Phase 6.

3. **`PadicNumbers` `instance : CharZero ℚ_[p]`** — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:563`. The base char-0 fact for `ℚ_p`.

4. **`Nat.Prime.ne_zero`** — used across mathlib (e.g. `Bernoulli.lean:479,543`, `PadicNumbers.lean:106`): `hp.out.ne_zero : p ≠ 0`.

5. **Exact analog already in mathlib** — `Mathlib/NumberTheory/Bernoulli.lean:479`:
   ```lean
   have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
   ```
   This is `natCast_p_ne_zero` for `L = ℚ` — mathlib derives it *inline* as a one-liner rather than as a named lemma, which is the established mathlib practice for this fact.

6. **Project's own helper** — `PadicLFunctions.charZero_of_qpAlgebra` at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:114`:
   ```lean
   lemma charZero_of_qpAlgebra (q : ℕ) [Fact q.Prime] {M : Type*} [NormedField M]
       [NormedAlgebra ℚ_[q] M] : CharZero M :=
     charZero_of_injective_algebraMap (algebraMap ℚ_[q] M).injective
   ```
   The project *already* has the char-0 transport lemma in exactly `natCast_p_ne_zero`'s typeclass context.

Concluded: **"not in mathlib under the narrow `(p:L)`-form, but mathlib has the general form `Nat.cast_ne_zero` plus the char-0 transport `charZero_of_injective_algebraMap`; the narrow form is a ≤2-call composition. Mathlib itself derives the `L = ℚ` analog inline (Bernoulli.lean:479)."**

---

### Call sites — `PadicLFunctions.natCast_p_ne_zero`

Internal use count: **4** (within the project, excluding the declaring line `ExtLog.lean:294`)
External-to-file callers: **2 distinct files** (`ExtLog.lean` itself — 3 uses below its definition — and `ValuesAtOne.lean`)

| Caller file:line                     | Usage pattern (one-line excerpt) |
|--------------------------------------|-----------------------------------|
| `ExtLog.lean:325`                    | `mul_left_cancel₀ (zpow_ne_zero _ (natCast_p_ne_zero p)) (hexp ▸ ekey)` |
| `ExtLog.lean:361`                    | `have hpL : (p : L) ≠ 0 := natCast_p_ne_zero p` |
| `ExtLog.lean:390`                    | `have hpL : (p : L) ≠ 0 := natCast_p_ne_zero p` |
| `ValuesAtOne.lean:571`               | `smul_right_injective K (pow_ne_zero _ (natCast_p_ne_zero (L := K) p)) hkey` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `natCast_p_ne_zero`?):
- `ExtLog.lean` (`extLog_witness_smul_eq`, ~line 320) computes `(0:ℝ) < (p:ℝ)⁻¹` and `(p:ℝ)⁻¹ ≠ 1` directly via `hp.out.pos` / `hp.out.one_lt` — a parallel norm-based side computation, but for `(p:ℝ)`, not `(p:L)`; not a re-derivation of this exact lemma.
- No site re-derives `(p:L) ≠ 0` by hand; all four obtain it from this lemma.

Composability reading: **K = 4 internal uses, no inline re-derivation.** Per the Phase-6 table, K ≥ 3 with no bypass is a "real API" signal that *normally* leans YES. Here it is outweighed by the fact that each use is a trivial side-condition (`zpow_ne_zero`/`pow_ne_zero`/`smul_right_injective` argument) and the lemma itself is a ≤2-call mathlib composition (Phase 6) — i.e. the 4 uses establish that the *fact* is needed repeatedly, not that a *new lemma* is needed. The right resolution is a tiny project-local helper (which it already is) or inlining; it is not a mathlib contribution.

---

### Composition check (Phase 6)

Can `natCast_p_ne_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1 (char-zero route — works in the lemma's exact typeclass context):
```lean
theorem natCast_p_ne_zero : (p : L) ≠ 0 :=
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  Nat.cast_ne_zero.mpr hp.out.ne_zero
```
  - Mathlib decls used: `charZero_of_injective_algebraMap`, `RingHom.injective` (for `(algebraMap ℚ_[p] L).injective`, ℚ_p a field), `Nat.cast_ne_zero`, `Nat.Prime.ne_zero`.
  - Result: **succeeds** (this is exactly what the project's `charZero_of_qpAlgebra` + the mathlib `Bernoulli.lean:479` idiom give).
  - Notes: 2 substantive mathlib calls (`charZero_of_injective_algebraMap …` to get the instance, then `Nat.cast_ne_zero.mpr …`). The `algebraMap … |>.injective` is a projection, not a reasoning step.

Attempt 2 (norm route — the proof as written, also a short mathlib composition):
```lean
example : (p : L) ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_natCast_p p]; positivity)
```
  - Mathlib decls used: `norm_ne_zero_iff` (mathlib), `positivity`. Building block `norm_natCast_p` is *project-local* (ExtLog.lean:88), itself a 2-call composition (`map_natCast`, `norm_algebraMap'`, `Padic.norm_p`).
  - Result: **succeeds**, but routes through a project lemma, so the char-zero route (Attempt 1) is the cleaner pure-mathlib composition.

Conclusion: **COMPOSABLE** (≤2 mathlib calls via the char-zero route; the general fact `Nat.cast_ne_zero` plus the char-0 transport already in mathlib). Per the Phase-6 heuristics this is a genuine composition (a `.mpr` of an iff applied to a prime's `ne_zero`, after acquiring the `CharZero` instance from a one-call transport), not a proof in disguise.

---

## Verdict: `PadicLFunctions.natCast_p_ne_zero`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the fact is the *definition* of characteristic zero (`Nat.cast_ne_zero`); maximally general form is `[AddMonoidWithOne R][CharZero R], n ≠ 0 ⊢ (n:R) ≠ 0`. No novelty.
- Generality analysis (Phase 4): STRICTLY NARROWER on 3 axes — but the maximally general form already exists in mathlib, so generalising "first" is moot (it's `Nat.cast_ne_zero`).
- Mathlib search (Phase 5): general form `Nat.cast_ne_zero` (CharZero/Defs.lean:74) + char-0 transport `charZero_of_injective_algebraMap` (CharP/Algebra.lean:77) + `CharZero ℚ_[p]` (PadicNumbers.lean:563) + `Nat.Prime.ne_zero`. Mathlib derives the `L = ℚ` analog inline at `Bernoulli.lean:479`.
- Composition check (Phase 6): COMPOSABLE in ≤2 mathlib calls (char-zero route).

**Rationale:**

`natCast_p_ne_zero` asserts `(p : L) ≠ 0` for `p` prime and `L` a normed `ℚ_p`-algebra field. This is a doubly-specialized instance of the definitional fact "in a characteristic-zero ring, a nonzero natural casts to a nonzero element" — mathlib's `Nat.cast_ne_zero`. The only thing standing between the general lemma and the project's narrow statement is the `CharZero L` instance, and mathlib already supplies the transport (`charZero_of_injective_algebraMap`, using that `ℚ_p → L` is injective because `ℚ_p` is a field). The whole statement therefore composes from mathlib in two calls: acquire `CharZero L`, then `Nat.cast_ne_zero.mpr hp.out.ne_zero`. Mathlib itself treats this fact as a one-liner rather than a named lemma — `Bernoulli.lean:479` writes the `L = ℚ` version inline as `Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)`. There is no mathlib gap to fill: the general form is upstream and the specialization is mechanical.

Decisively, the *project itself* already contains the relevant building block: `PadicLFunctions.charZero_of_qpAlgebra` (Coefficients.lean:114) proves `CharZero M` from `[NormedField M] [NormedAlgebra ℚ_[q] M]` — exactly `natCast_p_ne_zero`'s context — with a docstring explaining it is deliberately not an instance ("`p` is not determined by the goal — cite per use site"). So `natCast_p_ne_zero` is redundant with an existing project helper composed with `Nat.cast_ne_zero`; it does not belong in mathlib. The norm-based proof actually shipped is a valid alternative composition but routes through the project-local `norm_natCast_p`, so it is not even the simplest pure-mathlib derivation.

This is not `YES-but-generalise-first`: the maximally general statement (Phase 4) is already a mathlib lemma, so there is nothing to upstream — generalising lands you exactly on `Nat.cast_ne_zero`. It is not `NO-mathlib-has-it` *in the strict ≤1-line sense*, because the narrow `(p:L)`-form is not present verbatim and needs the `CharZero L` instance acquisition first (a second call); hence `NO-composable-from-mathlib` is the precise bucket. (If one regards `charZero_of_qpAlgebra` as the de-facto "mathlib-equivalent" and counts the instance as ambient, it collapses to `NO-mathlib-has-it`; either way the action is identical: do not contribute, inline/delete.)

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the user's form is a 1–2 mathlib-call composition. The lemma duplicates, in narrow form, `Nat.cast_ne_zero` plus the char-0 transport that the project already wraps as `charZero_of_qpAlgebra`.

Mathlib building blocks:
- `Nat.cast_ne_zero` — `Mathlib/Algebra/CharZero/Defs.lean:74`
- `charZero_of_injective_algebraMap` — `Mathlib/Algebra/CharP/Algebra.lean:77`
- `CharZero ℚ_[p]` instance — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:563`
- `Nat.Prime.ne_zero` (via `hp.out.ne_zero`)
- (project-local equivalent already present) `PadicLFunctions.charZero_of_qpAlgebra` — `Coefficients.lean:114`

Composition sketch (≤2 mathlib calls; works in the lemma's exact context):
```lean
example : (p : L) ≠ 0 :=
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  Nat.cast_ne_zero.mpr hp.out.ne_zero
-- or, reusing the project helper: `have := charZero_of_qpAlgebra (M := L) p; exact Nat.cast_ne_zero.mpr hp.out.ne_zero`
```

Call sites in our project (from Phase 6.0): **K = 4** — `ExtLog.lean:325`, `ExtLog.lean:361`, `ExtLog.lean:390`, `ValuesAtOne.lean:571`.

Refactor plan: at each of the 4 sites, replace `natCast_p_ne_zero p` (or `natCast_p_ne_zero (L := K) p`) with the inline composition. Because the bare term `natCast_p_ne_zero p : (p:L) ≠ 0` is used as a positional argument inside `zpow_ne_zero _ (·)`, `pow_ne_zero _ (·)`, and a local `have`, the cleanest mechanical refactor is:
- **Option A (preferred, minimal churn):** keep one tiny project-local lemma but state it as the trivial composition and route through the existing `charZero_of_qpAlgebra` — i.e. *do not contribute to mathlib*; this is already what the project effectively wants. If the team prefers zero extra helpers:
- **Option B (full inline):** at `ExtLog.lean:361` and `:390`, replace `have hpL : (p : L) ≠ 0 := natCast_p_ne_zero p` with
  `have : CharZero L := charZero_of_qpAlgebra (M := L) p` followed by `have hpL : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero`. At `ExtLog.lean:325` and `ValuesAtOne.lean:571`, inline the same `(p:L) ≠ 0` term (note `ValuesAtOne.lean` already has `[CharZero K]` in its `variable` block at line 41, so there the body is simply `Nat.cast_ne_zero.mpr hp.out.ne_zero` — no transport call needed).

Next action: do **not** open a mathlib PR. Either keep the lemma strictly project-local (acceptable as a one-line convenience, like mathlib's own inline usage), or inline the ≤2-call composition at the 4 sites and delete `natCast_p_ne_zero` from `ExtLog.lean`. At the `ValuesAtOne.lean:571` site, `[CharZero K]` is already in scope, so the inline is a single `Nat.cast_ne_zero.mpr hp.out.ne_zero`.

---

## Next step

Do not open a mathlib PR. `natCast_p_ne_zero` is a ≤2-call composition of mathlib's `Nat.cast_ne_zero` with the char-0 transport `charZero_of_injective_algebraMap` (already wrapped project-locally as `charZero_of_qpAlgebra`), and mathlib derives the analogous fact inline rather than as a named lemma. Inline the composition at the 4 call sites (`ExtLog.lean:325/361/390`, `ValuesAtOne.lean:571` — the last already has `CharZero K` in scope) and delete the lemma; or, if a one-line convenience helper is wanted, keep it strictly project-local.
