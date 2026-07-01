# Decomposition: Option B — Inclusion-Exclusion via P_p Operators

**Date**: 2026-05-19
**Status**: planning (Phase 1e for the IE strategy)
**Strategy**: Bypass the broken (4.6.14) Fourier-vanishing chain by
constructing the same-level decomposition `f = ∑_p f_p` via
inclusion-exclusion using same-level projection operators `P_p`.

## CRITICAL FINDING — T124 OBSTRUCTION

The project's existing same-level operator `pSupportedProjection`
(`Eigenforms/AtkinLehnerProjection.lean:176`) is defined as
`traceGamma1 ∘ pSupportedRaise`. Its **q-expansion is NOT clean** —
the trace round-trip picks up contributions from non-∞-stabilizing
cosets that produce "other-cusp expansions at ∞" unrelated to the
input's q-expansion.

From the file docstring (T124, lines 49-145), VERBATIM:

> "**The naive p-supported coefficient formula**
>
>   `(qExpansion 1 (pSupportedProjection f)).coeff n
>     = [Γ₁(N) : Γ₁(p · N)] · (if p ∣ n then (qExpansion 1 f).coeff n else 0)`
>
> **is false**, and more importantly the trace/projection route cannot
> supply a clean p-supported coefficient statement usable by
> `qSupportedOnDvd_mem_cuspFormsOld_of_char`."

The file docstring identifies the obstruction precisely (lines 80-86):

> "For the inclusion `Γ₁(p · N) ≤ Γ₁(N)` with `p ∤ N` or `p ∣ N`, the
> stabilisers satisfy `Γ₁(N) ∩ Stab(∞) = Γ₁(p · N) ∩ Stab(∞) = ⟨T⟩`
> (the upper-unipotent subgroup), so the **only** `∞`-stabilising coset
> in `𝒬` is the identity coset. All other cosets contribute
> other-cusp expansions at `∞`, which are **not** p-supported merely
> because the input is p-supported at `∞`."

The docstring further says (line 145):

> "the `mainLemma` coefficient chain should not depend on a q-expansion
> formula for `pSupportedProjection`."

**Implication**: Option B as initially planned (using the existing
`pSupportedProjection`) **is not viable**. To make Option B work,
we need either:

- (B-a) Develop the T124 cusp correction (via `PartialTraceCorrection`
  / `TraceCorrectionPrime` machinery — a separate research project).
- (B-b) Define a NEW operator that avoids the trace round-trip
  (e.g., Atkin-Lehner-Li orthogonal projection via Petersson product).
- (B-c) Develop a Möbius-sieve identity at the q-expansion level
  (also currently OPEN per the file docstring).

## Goal (Option B refined)

Given the T124 obstruction, the practical refinement of Option B is:

**Goal**: Develop a same-level p-supported projection `P_p^*` whose
q-expansion **is** clean. This `P_p^*` is the missing piece that the
file docstring identifies as `cuspFormsOld_of_coprime_coeff_vanishing_via_Mobius`.

## Source's full proof structure

Per the expert review 2026-05-16 (`.mathlib-quality/expert-review/2026-05-16-SMO-obligations-plan/reply.md`):

> "For each prime $p \mid N$, define $P_p = V_p U_p$, whose $q$-expansion is
> $$P_p f = \sum_{p \mid n} a_n(f) q^n.$$
> The operators $P_p$ commute with each other at the coefficient level and
> preserve the character space if the project's bad-prime $U_p$ and
> same-level $V_p U_p$ diamond-commutation lemmas are available."

The expert ACKNOWLEDGES the same risk (their "Risks or missing facts" section):

> "The main risk is that the project's $P_p = V_p U_p$ operator may not
> literally be a same-level endomorphism in the needed form. If
> `heckeT_p_divN` and `modularFormLevelRaise` only compose through a
> lower-level or higher-level type, the ticket should first create a
> packaged same-level projection $P_p$ with a theorem about its
> $q$-expansion and character preservation. This is the correct local API
> boundary."

So the expert's plan requires building a NEW same-level `P_p` operator
WITH a clean q-expansion identity. The existing `pSupportedProjection`
doesn't satisfy the clean-q-expansion requirement (per T124).

## Plain-English proof (Miyake p. 158 + expert review)

For `f : CuspForm Γ_1(N) k` with `f ∈ cuspFormCharSpace χ` (where
`χ.toUnitHom` factors through every `N/p`), and `a_n(f) = 0` for
`Coprime n N`:

**Step A** — For each prime `p ∣ N`, define `P_p f` as the same-level
form at `Γ_1(N)` whose q-expansion is `Σ_{p|n} a_n(f) q^n`. **The
existence and well-definedness of `P_p f` at the same level is THE
KEY CONSTRUCTION**. Standard construction via `V_p ∘ U_p` doesn't
give same-level output; we need:
- (1) `U_p` same-level at `Γ_1(N)`: `heckeT_p_divN` ✓.
- (2) A NEW same-level `V_p` at `Γ_1(N)` (when `p ∣ N` and `χ` factors
  through `N/p`): the slash by `[[p, 0; 0, 1]]` with appropriate
  normalisation.

For χ-eigen `f` with χ factoring through `N/p`, the composition
`V_p U_p f` gives a form at level `Γ_1(p·N)` that descends back to
`Γ_1(N)` via the character argument (diamond commutation). **This
descent is the technical core**.

**Step B** — Inclusion-exclusion at q-expansion level: for `f` with
`a_n(f) = 0` at `Coprime n N`,

```
f = Σ_{∅ ≠ T ⊆ N.primeFactors} (-1)^{|T|+1} (∏_{p ∈ T} P_p) f
```

This is purely combinatorial Möbius inversion.

**Step C** — Upgrade to function identity at level `Γ_1(N)`:
both sides are forms at `Γ_1(N)` with the same q-expansion. By
`qExpansion_eq_zero_iff` applied to their difference at `Γ_1(N)`,
they're equal as functions on ℍ.

**Step D** — Reindex `f = ∑_T ... → f = ∑_p f_p`: each f_T is
supported on multiples of every prime in T, hence on multiples of any
specific `p ∈ T`. Assign each T to its smallest prime; define
`f_p := Σ_{T : min T = p} (-1)^{|T|+1} f_T`. Then `f = Σ_p f_p` and
each `f_p` is p-supported (since each contributing f_T has p ∈ T).

**Step E** — Apply consumer
`mainLemma_charSpace_of_finset_decomposition`
(`Eigenforms/AtkinLehnerProjection.lean:607`): gets `f ∈ cuspFormsOld N k`.

## Lemmas (in order)

### L1 (NEW — major API gap): Same-level V_p operator at Γ_1(N)

The KEY new infrastructure. Define `V_p_same : ModularForm Γ_1(N) → ModularForm Γ_1(N)`
for χ-eigen f with χ factoring through N/p, such that:

```lean
noncomputable def V_p_same {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    [NeZero (N / p)] (χ : (ZMod N)ˣ →* ℂˣ)
    (hχ_fact : ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
      χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k //
      f ∈ modFormCharSpace k χ} →
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k //
      f ∈ modFormCharSpace k χ} := sorry
```

- Definition: V_p_same f := slash by `[[p, 0; 0, 1]]` of `f` (scaled
  appropriately), descended to level Γ_1(N) via the diamond-character argument.
- LOC: 150-250 (requires diamond-commutation infrastructure).

**T124-style obstruction**: this same-level descent works only when χ
factors through N/p. For general χ, the operator doesn't land at level
Γ_1(N).

### L2 (NEW — same level): P_p := V_p_same ∘ U_p

```lean
noncomputable def P_p_same {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    [NeZero (N / p)] (χ : (ZMod N)ˣ →* ℂˣ)
    (hχ_fact : ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
      χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    ...
    := V_p_same · ∘ U_p (heckeT_p_divN)
```

- LOC: 30 (composition).

### L3 (NEW): q-expansion identity for P_p_same

```lean
theorem qExpansion_one_P_p_same_coeff
    ... (analogous setup) (n : ℕ) :
    (qExpansion 1 (P_p_same f)).coeff n =
      if p ∣ n then (qExpansion 1 f).coeff n else 0 := by sorry
```

- LOC: 100-150 (requires V_p_same's q-expansion + U_p's q-expansion +
  composition).

### L4 (NEW): P_p commutation

```lean
theorem P_p_same_comm {f} {p q : ℕ} ... :
    P_p_same · (P_q_same · f) = P_q_same · (P_p_same · f) := by sorry
```

- LOC: 50-80 (q-expansion level reasoning).

### L5 (NEW): Iterated projection P_d for squarefree d ∣ N

```lean
noncomputable def P_d_same {N : ℕ} [NeZero N] (k : ℤ) (d : ℕ)
    (hd : Squarefree d) (hdN : d ∣ N) ... := sorry
```

with `a_n(P_d_same f) = a_n(f) if d ∣ n else 0`.

- LOC: 80-120 (induction over d.primeFactors).

### L6 (NEW): Inclusion-exclusion identity

```lean
theorem inclusion_exclusion_decomposition_qExp
    {f : ModularForm Γ_1(N) k} (hfχ : f ∈ modFormCharSpace χ)
    (h_vanish : ∀ n, Coprime n N → a_n(f) = 0)
    (n : ℕ) :
    (qExpansion 1 f).coeff n =
      ∑ T ∈ (N.primeFactors.powerset \ {∅}),
        (-1)^(T.card + 1) * (qExpansion 1 (P_d_same · f)).coeff n := by sorry
```

- LOC: 100-150 (Möbius / IE bookkeeping).

### L7 (NEW): Function-identity upgrade

```lean
theorem inclusion_exclusion_decomposition
    ... :
    f = ∑ T ∈ N.primeFactors.powerset \ {∅},
        (-1)^(T.card + 1) • (P_d_same · f) := by sorry
```

via `qExpansion_eq_zero_iff` at level Γ_1(N).

- LOC: 60-100.

### L8 (NEW): Reindex to per-prime decomposition

```lean
theorem prime_decomposition_of_coprime_vanishing
    ... :
    ∃ f_p : ℕ → CuspForm Γ_1(N) k,
      f = ∑ p ∈ N.primeFactors, f_p p ∧
      (∀ p, f_p p ∈ qSupportedOnDvdSubmodule N k p) ∧
      (∀ p, f_p p ∈ cuspFormCharSpace χ) := by sorry
```

via "smallest prime in T" reindexing.

- LOC: 100-150 (sum rearrangement bookkeeping).

### L9 (project, leaf): Consumer

`mainLemma_charSpace_of_finset_decomposition` (existing,
`Eigenforms/AtkinLehnerProjection.lean:607`).

## Attacks attempted

### L1 attacks (CRITICAL — this is the main blocker)

- **[1] Counterexample search**: search for "same-level V_p" lemmas in
  project. `pSupportedProjection` exists but its q-expansion is NOT
  clean (T124 docstring). No clean same-level V_p found.
- **[2] Edge cases**: For p²∣N, the descend has no extra-rep, but the
  trace round-trip still picks up non-∞-stabilizing coset contributions.
  Per T124 docstring, even p²∣N case is not clean.
- **[3] Hypothesis test**: Requiring χ factors through N/p is essential
  (otherwise the diamond-character descent doesn't give same-level).
  Even with this, T124 shows the trace round-trip picks up unwanted
  contributions.
- **[4] Source-drift**: Expert review proposes "V_p U_p" but
  acknowledges (in "Risks") that the project may not have this as
  literally same-level. T124 docstring confirms this is NOT trivial.
- **[5] Discharge attack**: Cannot discharge L1 via existing project
  infrastructure. `pSupportedProjection` has the wrong q-expansion.
  modularFormLevelRaise outputs at WRONG LEVEL. There's NO operator
  in the project with the required clean same-level q-expansion.
- **Verdict**: L1 discharge FAILED — there's no path to constructing
  V_p_same with the clean q-expansion using existing project code.
  **This is a genuine API gap requiring substantial new infrastructure.**

### L3 attacks (q-expansion identity for P_p_same)

Depends on L1 succeeding. Since L1 has no discharge, L3 inherits the
same gap.

### L6, L7, L8 attacks (IE + reindexing)

Standard combinatorial reasoning; would survive attacks IF L1-L5 are
in place. Currently blocked on L1.

## Prior-B2 log consultation

No B2 log exists. The T124 obstruction was identified by the project
itself (file docstring) as a known structural issue, NOT a B2 failure.

## Confidence gate (Option B)

1. ❌ L1 discharge BLOCKED — no existing project infrastructure
   provides the required same-level clean-q-expansion V_p operator.
2. ✅ Skeleton compiles (would, if written as `:= sorry`).
3. ⏳ Source quotes available (expert review + T124 docstring).
4. ❌ Adversarial pass REJECTED L1's discharge.
5. ✅ Prior-B2 log clean.
6. ⏳ Tree structure mirrors expert's proposal but requires NEW infrastructure.

**Gate status**: BLOCKED on L1 (V_p_same same-level operator).

## Feasibility assessment

**Option B is feasible but requires substantial new mathematical
infrastructure (~500-1000 LOC)**, including:

1. A new same-level `V_p_same` operator (NOT the existing
   `pSupportedProjection` which has the T124 obstruction).
2. Its q-expansion identity (requiring diamond-commutation + careful
   cusp analysis).
3. The IE machinery on top.

The project's existing `pSupportedProjection` (T121-T123) has
unconditional character preservation but does NOT have the required
q-expansion identity (T124). The Petersson / Atkin-Lehner-Li route
(D-S 5.7) is the alternative but requires even more infrastructure.

**Honest assessment**: Option B is NOT a quick fix. It's a major
research project equivalent in scope to closing the (4.6.14) Miyake
sorry directly (Option A).

## Recommendation

Given:
- Option A (Miyake's 4.6.14 chain) requires the M7-sqfree + M6(2)
  level-mismatch resolution (~500-800 LOC).
- Option B (inclusion-exclusion) requires the V_p_same construction
  + IE machinery (~500-1000 LOC).
- Both involve substantial new infrastructure that the project lacks.

The user should consider:

**Option C (NEW)** — direct fix to Option A by exposing M7-sqfree's
internal V_q-preimage at the natural level. This is a LOCALIZED
refactor of the existing `miyake_4_6_7_squarefree_decomp` lemma
(~200-300 LOC) and avoids the larger new infrastructure of B.

The cleanest path may be Option C: modify M7-sqfree to expose F_q at
level `Γ_1((l'·N · l'²)/q) = Γ_1(l'³·N/q)`, then add M6(1) chain to
bridge from this level to our base level `Γ_1(l'·N)` using the
function's char space membership.

## Next step

Confirm with the user whether to:
- (B-pursue) Develop Option B's V_p_same infrastructure (large scope).
- (C-pursue) Pursue Option C — localized refactor of M7-sqfree
  to expose V_q-preimages.
- (D-pursue) Pursue a completely different approach (e.g., Petersson
  inner product / Atkin-Lehner-Li).

Each option has substantial scope. The decomposition for the chosen
option needs its own iteration.
