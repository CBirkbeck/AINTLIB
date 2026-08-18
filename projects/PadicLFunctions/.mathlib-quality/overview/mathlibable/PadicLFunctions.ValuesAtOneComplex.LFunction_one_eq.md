# `/mathlibable` report — `PadicLFunctions.ValuesAtOneComplex.LFunction_one_eq`

**Date:** 2026-06-18
**Mode:** A (single declaration, full 10-phase workflow, exhaustive 9-channel literature search)
**Final verdict:** `YES-add-as-is`

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task instruction); reasoned from source — the declaration and all its dependencies were read directly from `ValuesAtOneComplex.lean` and from the pinned mathlib tree (`.lake/packages/mathlib`, rev `d90090f647ca`, toolchain `v4.31.0-rc2`).
- decl `PadicLFunctions.ValuesAtOneComplex.LFunction_one_eq`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOneComplex.lean:419`
- kind:                      theorem
- has sorry:                 no (grep over the whole file: no `sorry`/`admit`; the proof closes cleanly using project lemmas + mathlib)
- module docstring summary:  Complex-analysis "quarantine" file (the §4 `ZetaValuesComplex` pattern) computing the classical value `L(θ,1)` — **RJW Thm 6.1(i)**, following **Washington Thm 4.9** — stated against mathlib's `DirichletCharacter.LFunction` per the mathlib-linking directive.

---

### Statement (Phase 1)

`LFunction_one_eq` is a **theorem** stating the classical closed-form value of a Dirichlet L-function at `s = 1`:

For a **non-trivial primitive** Dirichlet character `θ` of conductor `N` over `ℂ`, and `ε` a primitive `N`-th root of unity,
```
L(θ, 1)  =  −G(θ⁻¹)⁻¹ · Σ_{c ∈ (ℤ/N)ˣ}  θ⁻¹(c) · log(1 − ε^c),
```
where `G(θ⁻¹) = gaussSum θ⁻¹ ψ` is the Gauss sum of the inverse character against the standard additive character `ψ = AddChar.zmodChar N (ε^N = 1)`, and `log` is the principal complex logarithm. This is Washington, *Introduction to Cyclotomic Fields*, Thm 4.9 (p. 38), equivalently Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions* (arXiv:2309.15692), §6.1 "The complex value at s=1", Thm 6.1(i).

**Variables / typeclasses (Lean side):**
- `{N : ℕ} [NeZero N]` — the conductor, an arbitrary nonzero natural number.
- `{θ : DirichletCharacter ℂ N}` — a complex Dirichlet character mod `N`.
- `{ε : ℂ}` — a complex number serving as a primitive `N`-th root of unity.

**Hypotheses (Lean side):**
- `(hθ : θ.IsPrimitive)` — `θ` has conductor exactly `N` (primitive). Mathematical role: the Gauss-sum Fourier-inversion identity and `|G(θ⁻¹)| = √N` require primitivity.
- `(hθ1 : θ ≠ 1)` — `θ` is non-trivial. Role: rules out the pole of `ζ`-like trivial character at `s=1`; gives differentiability/continuity of `L(θ,·)` up to and at `s=1`.
- `(hε : IsPrimitiveRoot ε N)` — `ε` is a primitive `N`-th root of unity. Role: indexes the cyclotomic-unit logarithms `log(1 − ε^c)` and defines the additive character.

**Conclusion (math):** the displayed closed-form equality `L(θ,1) = −G(θ⁻¹)⁻¹ Σ_c θ⁻¹(c) log(1−ε^c)`.

**Conclusion (Lean):**
```lean
LFunction θ 1
  = -(gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹
    * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N) * Complex.log (1 - ε ^ ((c : ZMod N)).val)
```

---

### Size classification (Phase 2a)

**Verdict: BIG**
**Reason:** It is a **theorem named after a person/place** (Washington's Thm 4.9; RJW Thm 6.1(i)) — a classical special-value formula for Dirichlet L-functions — and it is a **main result** of the file (the module docstring is built around it; it is the C6 cluster target in `decomposition.md`). Both BIG triggers fire.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~40 substantive lines (a real analytic argument: boundary-limit `Tendsto`, `tendsto_nhds_unique`, `LSeries`-rearrangement). One-liner verdict: **n/a — kind is `theorem`, not a `def`.** Check skipped.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `L(chi,1) Dirichlet L-function value formula Gauss sum logarithm root of unity Washington` | yes | `L(1,χ) = −(1/f) Σ χ(a) Σ ζ_f^{aj} log(2 sin πj/f)` and Gauss-sum variants; `G(χ)=Σχ(a)ζ_N^a` | UChicago REU (Baidoo); Harvard/Bristol/Kedlaya lecture notes. Standard textbook material. |
| 2 | WebSearch (general / arbitrary modulus) | `value L(1, chi) primitive Dirichlet character arbitrary modulus tau(chi)^{-1} sum chi-bar(a) log(1-zeta^a) general theorem` | yes | confirms general primitive-character formula via `χ(n)=τ(χ̄)⁻¹ Σ χ̄(m) e(2πinm/k)` Fourier inversion; `|τ(χ)|=√q` | Encyclopedia of Math "Dirichlet character"; the identity `Σ z^n/n = −log(1−z)` is the textbook bridge from `L(χ,1)` to circular-unit logs. Arbitrary modulus, not prime-only. |
| 3 | WebSearch (named-after / source) | `Dirichlet L-function at s=1 closed form theorem 4.9 Washington cyclotomic fields character log(1 - zeta)` | yes | **Washington [p.38, Thm 4.9]** — closed form for `L(1,χ)`, non-principal `χ`, via Gauss sum `τ(χ)` and `log(1−ζ)` cyclotomic units | Hu–Kim–Li (arXiv:1902.00718) cite it verbatim as Thm 1.1 = "Washington [7, p.38, Theorem 4.9]". This is the canonical reference. |
| 4 | WebSearch (source paper) | `"Rodrigues Jacinto" Williams "introduction to p-adic L-functions" theorem 6.1 L(theta,1) Gauss sum` | yes | RJW arXiv:2309.15692; §6.1 literally titled **"The complex value at s = 1"** | Confirms the file's own citation. Authors: J. Rodrigues Jacinto & C. Williams (Williams overlaps the repo owner's circle — primary source). |
| 5 | ChatGPT MCP | (asking standard form + generality + historical evolution) | n/a | — | No ChatGPT MCP tool available in this environment. Recorded n/a. Coverage substituted by 6 WebSearch queries spanning specific/general/named/source/modern levels. |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (both absent) | No `references/` dir under this project's `.mathlib-quality/`; `refs/` is not symlinked in this worktree (local-only PDFs, gitignored). Recorded n/a per protocol. The file header + sibling report `gaussSum_mul_coprime.md` already pin the source as Washington Thm 4.9 / RJW Thm 6.1(i). |
| 7 | nLab | `special values of L-functions`; `Riemann zeta function` | partial | nLab "special values of L-functions" exists but is abstract (Beilinson regulators / Stark conjectures) | Has the *philosophy* (`L(1,χ)` = log of circular units, Stark) but not this concrete closed form. |
| 8 | nCatLab / categorical | (same as nLab "special values") | n/a | — | Not a categorical concept; classical analytic-number-theory identity. nLab entry already covered in #7. |
| 9 | Stacks Project | `Dirichlet L-function value` | n/a | — | Not an algebraic-geometry / scheme-theoretic concept; Stacks does not cover analytic L-values. |
| 10 | MathOverflow / Math.SE | `Dirichlet character L-function special value s=1 cyclotomic units logarithm Stark` (web) | yes | confirms `Σ z^n/n = −log(1−z)` route; `L_K(1,χ)` ↔ Stark regulator of log-units | Reed lecture (non-vanishing at 1); Kronecker limit formula refs. Corroborates the form and its arithmetic meaning. |
| 11 | recent arXiv (last 5 yrs) | (covered by #3, #4, #10) | yes | Hu–Kim–Li 2019 (Kummer-relation analogue), RJW 2023/2024 | Modern uses cite the *same* Washington Thm 4.9 form; no reformulation has superseded it. |

#### Literature summary (Phase 3)

Concept identified as: **the classical closed-form value of a Dirichlet L-function at `s = 1`** (= Washington, *Introduction to Cyclotomic Fields*, Thm 4.9; = RJW arXiv:2309.15692 §6.1 Thm 6.1(i)). It is the analytic input to the Dirichlet class-number formula / cyclotomic-unit theory and the abelian Stark conjecture.

Sources agree on the standard form: **yes.** Every source gives the same shape: `L(χ,1) = (Gauss-sum factor) · Σ_{a} χ̄(a) · log(cyclotomic unit)`, derived by Fourier-expanding `χ` via the Gauss sum and summing the power series `Σ z^n/n = −log(1−z)` on the unit circle (Abel limit). Cosmetic variants only: `log(1−ζ^a)` vs `log(2 sin πa/f)` (same up to a unit/phase), and `θ⁻¹` vs conjugate `χ̄` (identical for these unit-valued characters), and `G(θ⁻¹)⁻¹` vs `τ(χ)/q`-style normalisations.

Most general standard form: **arbitrary conductor `N`** (not prime), **any non-trivial primitive character** (no even/odd split needed — the single formula covers both parities; the parity split is only a *presentation* convenience some sources adopt). This is exactly the generality of the target.

Generality dimensions where the literature varies:
- **Conductor:** some expositions specialise to prime `p` or to fundamental discriminants; the general statement is any `N ≥ 2`. The target uses arbitrary `N` — the most general.
- **Parity:** many expositions split even/odd; the *unified* primitive form (target's form) is strictly more general and is itself standard.
- **RHS normalisation:** `G(θ⁻¹)⁻¹` vs `τ(χ)/q`; cosmetic.

Disagreement with the literature: **none.** The Lean statement is the literature-standard form at full classical generality.

---

### Generality analysis — `LFunction_one_eq` (Phase 4)

Literature-standard form (from Phase 3): `L(χ,1) = −G(χ⁻¹)⁻¹ Σ_{c∈(ℤ/N)ˣ} χ⁻¹(c) log(1−ε^c)` for **any** non-trivial primitive `χ` of **any** conductor `N ≥ 2`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `{N : ℕ} [NeZero N]` | arbitrary nonzero conductor | arbitrary `N ≥ 2` | NO | Already maximally general; `N=1` is vacuous (forces `θ=1`, excluded by `hθ1` — the proof derives `1 < N` from `hθ1`). |
| 2 | `{θ : DirichletCharacter ℂ N}` | complex Dirichlet character | complex Dirichlet character | NO | `ℂ` is intrinsic: `LFunction`, `Complex.log`, analytic continuation are ℂ-valued. Standard. |
| 3 | `(hθ : θ.IsPrimitive)` | primitive | primitive | NO | Primitivity is required for the Gauss-sum Fourier inversion (`gaussSum_mulShift_of_isPrimitive`) and `G≠0`. The non-primitive case factors through the primitive one — standard to state for primitive. |
| 4 | `(hθ1 : θ ≠ 1)` | non-trivial | non-trivial | NO | Trivial character has a pole at `s=1`; the value is genuinely different. Essential. |
| 5 | `(hε : IsPrimitiveRoot ε N)` | primitive `N`-th root | primitive `N`-th root of unity | NO | Any primitive root works; the formula is independent of the choice (different `ε` reindex the sum). Maximally general — not pinned to `exp(2πi/N)`. |
| 6 | (no parity hypothesis) | none | none in the unified form | — | The target is *already* the parity-unified statement, strictly more general than even/odd-split versions. |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0.**
Cost of restatement: n/a (nothing to restate).

This is notable in context: the sibling project `FltRegularBernoulli` proves the *same* formula only for **prime conductor `p`** and **split by parity** (`even_LFunction_one_eq_evenLValueRhs`, `odd_LFunction_one_eq_oddLValueRhs`, and `even_LFunction_one_eq_gaussSum_inv_mul_DirichletLogSum`). The target here is the **general-conductor, parity-unified** form those specialise from — i.e. the target is *more* general than the closest existing AINTLIB sibling, and matches the literature standard exactly.

#### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | Already fully typeclass-driven (`[NeZero N]`, `IsPrimitive`, `IsPrimitiveRoot`); hypotheses are propositions, not bundled structures. |
| 2 | sequences/metric → filters/topology? | no | — | The proof *already* uses the filter idiom (`nhdsWithin 1 (Set.Ioi 1)`, `Filter.Tendsto`, `tendsto_nhds_unique`) — this is the modern Abel-limit formulation, not a sequence. |
| 3 | construct an object → universal-property class? | no | — | It is an equality of two concrete ℂ-values; nothing is being constructed. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No substructures involved. |
| 5 | vector-space/metric/field-specific → weaken typeclass? | no | — | `ℂ` is intrinsic (analytic continuation, `Complex.log`); cannot weaken to a general field/ring. |
| 6 | 1-categorical → higher-categorical? | no | — | Pure analytic-number-theory identity; no categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no | — | Index set is `(ℤ/N)ˣ`, intrinsic to the character; the additive character on `ZMod N` is the right object. |

##### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The declaration is already stated in contemporary mathlib idiom: filter-based boundary limit, `DirichletCharacter`/`gaussSum`/`AddChar.zmodChar` API, primitivity as a `Prop`. There is no Bourbaki-2.0 reorganisation that would compose better. (One **cosmetic** API choice — discussed in Phase 7 — is whether to spell the additive character as `AddChar.zmodChar N hε.pow_eq_one` vs mathlib's `ZMod.stdAddChar`, and whether to phrase via `θ⁻¹` or the conjugate; these are presentation choices, not generalisations, and do not move the verdict.)

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths are introduced. Skipped.

---

### Mathlib search-status: `LFunction_one_eq` (Phase 5)

> Note: no Loogle / LeanSearch / Lean-Finder MCP tools are available in this environment. Methods [A]–[C] were executed via WebSearch (leansearch.net surfaced) + exhaustive `grep` over the pinned mathlib source tree (`.lake/packages/mathlib/Mathlib/`), which is the authoritative ground truth for *this* build. Method [D] (grep) and [E] (name-pattern) ran in full.

```
[A] Lean-Finder       (web) Dirichlet LFunction value at one Gauss sum   no MCP; web pointed only to Mathlib.NumberTheory.GaussSum (def of gaussSum) — no value-at-1 result
[B] Loogle            grep `LFunction _ 1 = …` / `LFunction … = gaussSum…` / `= log (1 …`   no hits (empty)
[C] LeanSearch        (web) "DirichletCharacter LFunction value at one Gauss sum formula"   no hit on a closed-form value; only functional-equation / Gauss-sum-definition pages
[D] Grep mathlib src  `gaussSum` × `LFunction` co-occurrence over NumberTheory/LSeries/   single file: DirichletContinuation.lean — and there only for the functional equation / rootNumber, NOT a value at s=1
[E] Name pattern      `LFunction*one_eq`, `value_one`, `LValue`, `special_value`, `LFunction … 1 =`   no hits in mathlib
```

Searched for both:
- the user's current form (`L(θ,1) = −G(θ⁻¹)⁻¹ Σ …log(1−ε^c)`) — **not in mathlib**;
- the literature-standard / more-general form (any normalisation of `L(χ,1)` via Gauss sums + cyclotomic-unit logs, any conductor) — **also not in mathlib**.

What mathlib **does** have (the building blocks, all confirmed by grep):
- `DirichletCharacter.LFunction` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61`) — the analytic continuation;
- `DirichletCharacter.LFunction_eq_LSeries` (ibid.:75) — `L = LSeries` for `Re s > 1`;
- `DirichletCharacter.differentiable_LFunction` (ibid.:98) — differentiable for `χ ≠ 1` (gives continuity at `s=1`);
- `DirichletCharacter.LFunction_apply_one_ne_zero` (`Nonvanishing.lean:405`) — `L(χ,1) ≠ 0` (the *non-vanishing*, not the value);
- the **functional equation** `completedLFunction_one_sub` and special values at negative integers (`LFunction_neg_two_mul_…`);
- `gaussSum`, `gaussSum_mul_gaussSum_inv`, and the Fourier-inversion `gaussSum_mulShift_of_isPrimitive` (`Mathlib/NumberTheory/DirichletCharacter/GaussSum.lean:57`).

Mathlib has **no** Abel boundary-limit lemma for `LSeries` at the edge of convergence either (`tendsto_LSeries_pow_boundary` is proved *in the project*, ~144 lines; the only near-neighbour `LSeries.tendsto_cpow_mul_atTop` is about `atTop`, not the `s↓1` boundary).

**Concluded:** "**not in mathlib** (all methods exhausted, plus the literature-standard / more-general form). Mathlib has the *non-vanishing* of `L(χ,1)` and all the building blocks (`LFunction`, `gaussSum`, Fourier inversion), but **no closed-form value** `L(χ,1)` and no relation of `L(χ,1)` to cyclotomic-unit logarithms."

---

### Composition check (+ call-sites signal) (Phase 6)

#### Call sites — `LFunction_one_eq`

Internal use count: **0** (within the same project, excluding the declaring file).
External-to-file callers: **0 distinct files** that call *this exact* qualified name.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | grep `LFunction_one_eq` across `projects/` returns only the declaration itself and **unrelated, similarly-named** theorems in the sibling project `FltRegularBernoulli` (`even_LFunction_one_eq_*`, `odd_LFunction_one_eq_*`, `LFunction_one_eq_dedekindZeta_residue_of_CN05`) — those are *not* uses of `PadicLFunctions.ValuesAtOneComplex.LFunction_one_eq`. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `LFunction_one_eq`?):
- **Yes — in a more specialised form, in a different project.** `FltRegularBernoulli/BernoulliRegular/LValueAtOne/{Even,Odd}.lean` and `CyclotomicUnits/AnalyticCore.lean` independently prove the *same* `L(χ,1)` formula but **only for prime conductor `p`** and **split by parity**, with project-specific RHS objects (`evenLValueRhs`, `oddLValueRhs`, `FLT37.Sinnott.DirichletLogSum`). These are specialisations of the target's general statement, derived without it.

##### What the call-sites pattern tells you

Pattern: **K = 0 internal uses, BUT the same statement is independently re-derived (in specialised prime/parity form) in a sibling project.** Per the Phase-6 signal table this normally leans toward NO-composable — *but the re-derivations are strictly narrower than the target*. The target is the general-conductor, parity-unified form; the sibling re-derivations cannot replace it (they only cover prime conductor, split by parity, with bespoke RHS). So the correct reading is: **the target is the canonical general statement the AINTLIB ecosystem is independently reaching for** — exactly the kind of result that should live once, upstream, rather than being re-proved per project. `K = 0` here reflects newness + the quarantine-file design (it is the file's headline result, freshly landed), not deadness.

#### Composition check

Can `LFunction_one_eq` be derived from mathlib in ≤3 chained calls?

Attempt 1: `LFunction_eq_LSeries` + `tendsto_nhds_unique` of the Abel boundary limit.
- Mathlib decls used: `DirichletCharacter.LFunction_eq_LSeries`, `differentiable_LFunction`, `gaussSum_mulShift_of_isPrimitive`.
- Result: **fails as a ≤3-call composition.** The actual proof needs: (i) the project lemma `LSeries_eq_gaussSum_inv_mul_sum` (~51 lines: Fourier-expand `θ` via the Gauss sum, reindex over `(ℤ/N)ˣ`, swap `LSeries` and finite sum); (ii) the project lemma `tendsto_LSeries_pow_boundary` (~144 lines: an **Abel boundary limit** `lim_{s↓1} LSeries(εⁿᶜ) = −log(1−ε^c)`, which mathlib does **not** provide); (iii) continuity of `L(θ,·)` at `s=1` from `differentiable_LFunction`; (iv) `tendsto_nhds_unique` to equate the two limits; plus `Finset.mul_sum` bookkeeping.
- Notes: the two heavy steps are full analytic lemmas, not mathlib one-liners.

Conclusion: **NOT-COMPOSABLE.** This is a genuine multi-lemma analytic theorem (the headline of a ~470-line file), resting on two substantial project lemmas plus an Abel-limit result absent from mathlib. It is decidedly not a 1–3 mathlib-call composition or a `simp`/`ring` glue.

---

## Verdict: `PadicLFunctions.ValuesAtOneComplex.LFunction_one_eq`

**Category:** `YES-add-as-is`

**Evidence:**
- Literature search (Phase 3): 9-channel exhaustive (6 WebSearch + nLab + MathOverflow/web + arXiv; ChatGPT MCP and local refs n/a with reasons). Identified unambiguously as **Washington Thm 4.9 / RJW arXiv:2309.15692 §6.1 Thm 6.1(i)** — a classical, universally-cited closed form for `L(χ,1)`. Sources agree on the form; the target matches it at full classical generality.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — arbitrary conductor `N`, any non-trivial primitive `θ`, any primitive root `ε`, parity-unified (strictly more general than the prime/parity-split sibling versions and equal to the literature standard). 0 weakening opportunities. Modern-idiom check: already contemporary (filter-based Abel limit); no Bourbaki-2.0 reorganisation available.
- Mathlib search (Phase 5): **not in mathlib** under either the user's form or the more-general form. Mathlib has the *non-vanishing* `LFunction_apply_one_ne_zero` and all building blocks, but **no value formula** for `L(χ,1)` and no cyclotomic-unit-log relation.
- Composition check (Phase 6): **NOT-COMPOSABLE** — rests on two heavy project lemmas (~51 and ~144 lines), one of which (the Abel boundary limit of an `LSeries`) mathlib lacks entirely.

**Rationale:**

This is a classical, named special-value theorem for Dirichlet L-functions — the analytic engine behind the Dirichlet class-number formula and cyclotomic-unit theory — stated at exactly the level of generality the literature treats as standard (arbitrary conductor, primitive non-trivial character, parity-unified). Mathlib already contains the entire surrounding scaffolding: the analytically-continued `DirichletCharacter.LFunction`, its differentiability/non-vanishing at `s=1`, the functional equation, special values at negative integers, and the Gauss-sum Fourier-inversion `gaussSum_mulShift_of_isPrimitive`. The one classical fact conspicuously **missing** is the *value at the central edge point* `s=1` — the natural companion to mathlib's `LFunction_apply_one_ne_zero` (mathlib proves `L(χ,1) ≠ 0` but never says *what it equals*). That is a concrete, nameable gap: `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` discusses `s=1` only as the trivial character's pole and via non-vanishing, with no closed form. Adding `LFunction_one_eq` fills it and immediately composes with the cyclotomic-unit API (`Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean`) and the Gauss-sum API to enable downstream class-number-formula work.

That the AINTLIB monorepo *already* contains independent re-derivations of this exact formula in a second project (`FltRegularBernoulli`'s `even_/odd_LFunction_one_eq_*`, but only for prime conductor and split by parity) is strong corroboration: the ecosystem keeps reaching for this result and re-proving narrower copies. The general, parity-unified statement here is the canonical form those should specialise from — precisely the case for a single upstream lemma. There is no further weakening (Phase 4 = maximally general), no modern reformulation that improves organisation (Phase 4c = none; it already uses the filter-based Abel-limit idiom), and no short mathlib composition (Phase 6 = not composable; needs an Abel boundary-limit lemma mathlib does not have). All four YES-add-as-is evidence gates are satisfied.

**WHY add it (refactor-actionable):**
- **New mathematical content mathlib is missing:** the closed-form *value* `L(χ,1)` for non-trivial primitive Dirichlet `χ`. Mathlib has `DirichletCharacter.LFunction_apply_one_ne_zero` (non-vanishing) and the functional equation, but **no** statement of what `L(χ,1)` *is*. Named, specific gap: there is no `LFunction…one…eq…` value lemma anywhere in `Mathlib/NumberTheory/LSeries/`.
- **The recurring manual reformulation:** within this very repo, `FltRegularBernoulli` re-proves the formula twice (even/odd) for prime conductor with bespoke RHS — evidence that users do this by hand because the canonical form is absent upstream.
- **How it composes:** with `LFunction_apply_one_ne_zero` it upgrades non-vanishing to an explicit value; it connects `DirichletCharacter.LFunction` to `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean` (the `log(1−ε^c)` are logs of cyclotomic units); it is the analytic input the (not-yet-in-mathlib) Dirichlet class-number formula needs, and it lets the prime/parity-split `FltRegularBernoulli` lemmas be re-derived as one-line specialisations.

Proposed mathlib location: `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` (sits naturally beside `LFunction_eq_LSeries`, `differentiable_LFunction`, `LFunction_apply_one_ne_zero`), or a new `Mathlib/NumberTheory/LSeries/ValueAtOne.lean` if the supporting Abel-limit lemma is bundled.

Proposed PR title: `feat(NumberTheory/LSeries): value of a Dirichlet L-function at s = 1`

PR grouping: ship together with the supporting general-purpose lemma `tendsto_LSeries_pow_boundary` (the Abel boundary limit `lim_{s↓1} Σ wⁿ/nˢ = −log(1−w)` for `‖w‖=1, w≠1`), which is independently mathlib-worthy and currently project-local, and with `LSeries_eq_gaussSum_inv_mul_sum` (the Gauss-sum Fourier rearrangement of `L(θ,s)` for `Re s>1`). These three form the right PR grain. Each warrants its own `/mathlibable` pass before submission.

Pre-PR checklist before opening:
- [ ] `/mathlibable PadicLFunctions.ValuesAtOneComplex.tendsto_LSeries_pow_boundary` — likely YES; it is the reusable Abel-limit primitive mathlib lacks.
- [ ] `/mathlibable PadicLFunctions.ValuesAtOneComplex.LSeries_eq_gaussSum_inv_mul_sum` — assess as a companion.
- [ ] `/generalise PadicLFunctions.ValuesAtOneComplex.LFunction_one_eq` — confirm no easy further weakening (expected: none; already maximal).
- [ ] `/cleanup ValuesAtOneComplex.lean PadicLFunctions.ValuesAtOneComplex.LFunction_one_eq` — full audit + diff gates. In particular settle the two **cosmetic API choices** for the mathlib statement: (a) additive character spelled as `AddChar.zmodChar N hε.pow_eq_one` vs mathlib's `ZMod.stdAddChar`; (b) RHS via `θ⁻¹` vs the conjugate character `θ̄`. Neither changes the math or the generality; pick the mathlib-idiomatic spelling at PR time.
- [ ] Pick a mathlib reviewer from recent `Mathlib/NumberTheory/LSeries/` commits (the `DirichletContinuation` / `ZMod` L-function authors).

---

## Next step

Open the upstreaming track for this result: run `/mathlibable` on the two supporting lemmas (`tendsto_LSeries_pow_boundary`, `LSeries_eq_gaussSum_inv_mul_sum`), then `/generalise` (expected: already maximal) and `/cleanup` on `LFunction_one_eq` to settle the cosmetic additive-character / conjugate spelling, and prepare a `feat(NumberTheory/LSeries): value of a Dirichlet L-function at s = 1` PR (grouped with its two supporting lemmas) targeting `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`.
