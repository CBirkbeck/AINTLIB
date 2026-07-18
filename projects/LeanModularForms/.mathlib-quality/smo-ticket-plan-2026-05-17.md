# SMO Closure — Ticket Plan (2026-05-17)

This document plans the discharge of the 9 remaining sorries in
`LeanModularForms/SMOObligations.lean`. Each ticket includes:

1. **Statement audit** — verbatim comparison with Miyake.
2. **Repo infrastructure** — what's already available.
3. **Need for further breakdown** — yes/no/maybe with justification.
4. **Estimated complexity** — line count + dependencies.
5. **Suggested approach** — concrete proof strategy.

The 9 leaves grouped by character:

- **Atomic, directly attackable**: T1.
- **Atomic, new mathematical content**: T5a, T5d, T6.
- **Atomic, mostly free from existing**: T5b, T5c.
- **Assembly given the above**: T5, T7, T8.

---

## T1 — `miyake_4_6_5_iterated_L`

### Statement
```lean
∀ N (NeZero N) χ (f : CuspForm Γ_1(N)) (hfχ : f ∈ cuspFormCharSpace χ)
  (L : ℕ) (hL_pos : 0 < L) (hL_sqfree : Squarefree L)
  (hL_dvd : ∀ p ∈ L.primeFactors, p ∈ N.primeFactors),
  ∃ g : CuspForm Γ_1(L·N),
    g ∈ cuspFormCharSpace (χ.comp (ZMod.unitsMap (N ∣ L·N))) ∧
    ∀ n, aₙ(g) = if Coprime n L then aₙ(f) else 0
```

### Miyake audit
- **Reference**: Miyake Lemma 4.6.5 (p. 157), restricted to squarefree
  `L | N` with all primes dividing `N`.
- **Original**: "Then `g(z) ∈ M_k(M, χ)` with
  `M = N · ∏_{p|L, p|N} p · ∏_{p|L, p∤N} p²`."
- **For our case**: all `p | L` divide `N`, so `M = N · ∏_{p|L} p = N · L`
  (since `L` is squarefree).
- **Verdict**: ✓ statement correctly restricts Miyake's general `L` to our use.

### Repo infrastructure
- `miyake_4_6_5_single_prime_dvd_N` (lines 319–438, **PROVEN**) — single-prime case.

### Need for further breakdown
- **Yes (1 sub-ticket)**: T1a — generalized induction helper allowing the
  level `N` and character `χ` to vary during induction.

### Estimated complexity
- T1a (helper): ~60 lines.
- T1 (main): ~40 lines wrapping T1a.
- **Total: ~100 lines.**

### Suggested approach
1. Define a private helper `miyake_4_6_5_iterated_helper` parameterised by
   `(M, χ_M)` that recurses on `L.primeFactors.card`.
2. Base case `L = 1`: `g := f` (trivial since `Coprime n 1` is always true).
3. Inductive step: pick `q ∈ L.primeFactors`, apply
   `miyake_4_6_5_single_prime_dvd_N` at level `M` with `q` to get `h` at
   level `q·M`. Recurse on `h` with `L / q` at the new level. Both
   sub-results combine via composition of the q-expansion filters.
4. T1 main = T1a at `(N, χ)` with full `L`.

---

## T5a — `miyake_hecke_descend_cosets`

### Statement
```lean
∀ N (NeZero N) p (NeZero p) (hp : p.Prime) (hpN : p ∣ N) (NeZero (N/p)),
  let d := if p² ∣ N then p-1 else p
  ∃ γ : Fin (d+1) → GL (Fin 2) ℝ,
    (∀ v, (γ v).det = p) ∧
    ∀ γ' : SL₂(ℤ), γ' ∈ Gamma1 (N/p) →
      ∃ σ : Equiv.Perm (Fin (d+1))
        (α : Fin (d+1) → SL₂(ℤ)),
        (∀ v, α v ∈ Gamma1 N) ∧
        ∀ v, γ v * mapGL ℝ γ' = mapGL ℝ (α v) * γ (σ v)
```

### Miyake audit
- **Reference**: Miyake p. 161 + Lemma 4.5.11.
- **Original**: "Take elements `γ_ν (0 ≤ ν ≤ d)` of `Γ_0(Nl'²/p)` so that
  `Γ_0(Nl'²)[1,0;0,p]Γ_0(Nl'²/p) = ⊔_{ν=0}^d Γ_0(Nl'²)[1,0;0,p]γ_ν`."
- **Verdict on M5a's statement**:
  - ⚠️ **Action property may be too strong**: my statement requires
    `α v ∈ Γ_1(N)`, but Miyake's coset decomposition gives `α v ∈ Γ_0(N)`.
    For the slash sum to be `Γ_1(N/p)`-invariant on `M_k(Γ_1(N))`, we
    actually need `α v ∈ Γ_1(N)` (so `f|_k α v = f` without character).
    Whether this is achievable depends on the explicit coset choice.
- **Required restatement** (TICKET T5a-pre): Restate to use `α v ∈ Γ_0(N)`
  AND add a "diamond compatibility" property: `α v` acts on `f ∈
  modFormCharSpace χ` by `χ(α v) = χ'(γ')` for `χ` factoring through `χ'`
  at level `N/p`. This is what makes the slash sum a `χ'`-eigenfunction
  at level `N/p`.

### Repo infrastructure
- **`heckeT_p_ut_orbit_comm_gamma0`** (`HeckeT_n.lean:865`): the
  Γ_0(N)-orbit analysis for the single-prime `[1,m;0,p]` slash sum. The
  technique generalises to Γ_0(N/p) but needs new divisibility lemmas
  (since for `γ' ∈ Γ_0(N/p)`, only `N/p | γ'₁₀`, not `N | γ'₁₀`).
- **`moebiusFin'`** (`HeckeT_n.lean:106`): the Möbius permutation
  `b ↦ (b·d - c)/(a + b·c) mod p` (where `[a,b;c,d] = γ'`). Reusable
  as-is for the permutation `σ` in the action.
- **`T_p_upper`, `T_p_lower`** (`HeckeT_p.lean:50, 56`): the explicit
  matrix definitions `[1,b;0,p]` and `[p,0;0,1]` as `GL₂(ℚ)`. Reusable
  for the explicit coset list (with adjustment to embed in `GL₂(ℝ)`).

### Need for further breakdown
- **Yes (3 sub-tickets after restatement)**:
  - T5a-1: explicit coset list (use `T_p_upper`/`T_p_lower` from existing).
  - T5a-2: each coset has det `p` (direct calc, uses `T_p_upper_det`).
  - T5a-3: action property at Γ_0(N/p) — the main combinatorial work.
    Adapt `orbit_upper_gamma0_divN` and `moebiusFin'` from Γ_0(N) to
    Γ_0(N/p). Key divisibility issue: when `γ' ∈ Γ_0(N/p)`, we have
    `N/p | γ'₁₀` (not `N | γ'₁₀`), so `p ∤ γ'₀₀` doesn't follow directly
    from det 1. New analysis needed for the action.

### Estimated complexity
- T5a-1 (coset list): ~20 lines.
- T5a-2 (det): ~10 lines.
- T5a-3 (action at Γ_0(N/p)): ~150-200 lines.
- T5a-pre (restatement): ~30 lines (statement fix).
- **Total: ~220 lines.**

### Risk: highest of all leaves
The action property at Γ_0(N/p) is the genuine new mathematical content.
The existing project work at Γ_0(N) gives the technique but not the lemma.

---

## T5b — `miyake_hecke_descend_qexp`

### Statement
```lean
∀ N p (hp : p.Prime) (hpN : p ∣ N),
  let d := if p² ∣ N then p-1 else p
  ∀ γ : Fin (d+1) → GL (Fin 2) ℝ,
    (∀ v, (γ v).det = p) →
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ f n, aₙ (c · Σ_v ⇑f ∣[k] γ v) = c · aₙ((qExp f).coeff (p·n))
```

### Miyake audit
- **Reference**: Miyake Eq. 4.6.13 + 4.6.12 at the coefficient level.
- **Original**: `f_p(z) = p(d+1)⁻¹ · (f|T(p))(z)` where the q-expansion of
  `f|T(p)` shifts coefficients by `p`.
- **Verdict**: ⚠️ **Statement is too weak (over-generic)**.
  - The q-shift identity holds only for SPECIFIC matrices (the
    `[1,m;0,p]` reps plus possibly `[p,0;0,1]`), not for any det-`p`
    matrix list.
  - **Required restatement** (TICKET T5b-pre): take additional hypothesis
    that `γ v` are the specific Miyake matrices (or equivalently, use
    T5a's matrices specifically).

### Repo infrastructure
- **`qExpansion_one_heckeT_p_divN_coeff`**
  (`Modularforms/QExpansionSlash.lean:817`, **PROVEN**):
  `(qExpansion 1 (heckeT_p_divN k p hp hpM f)).coeff m = (qExpansion 1 f).coeff (p * m)`.
  **Directly gives M5b for the `p² ∣ N` case with `c = 1`** (since the
  function-level slash sum is the same as `heckeT_p_ut`, and period-1
  q-expansion is level-independent).
- **`fourierCoeff_heckeT_p_period_one`**
  (`Modularforms/QExpansionSlash.lean:584`, **PROVEN**): the full
  Hecke `T_p` q-expansion `aₘ(T_p f) = a_{pm}(f) + p^{k-1}χ(p)·a_{m/p}(f)·[p|m]`.
  Gives the `p² ∤ N` case (the extra term from `[p,0;0,1]`).

### Need for further breakdown
- **No** after the restatement (T5b-pre). Just bridges existing project
  lemmas to our specific slash sum.

### Estimated complexity
- T5b-pre (restatement): ~20 lines.
- T5b (proof): ~40 lines (just invoke existing lemmas).
- **Total: ~60 lines.**

### Suggested approach
1. Restate to use M5a's matrices specifically.
2. For `p² ∣ N`: `c := 1`, use `qExpansion_one_heckeT_p_divN_coeff`.
3. For `p² ∤ N`: `c := (something accounting for the [p,0;0,1] term)`,
   use `fourierCoeff_heckeT_p_period_one`.
4. Bridge via function-level equality `heckeT_p_ut = Σ_b f ∣[k] [1,b;0,p]`.

---

## T5c — `miyake_hecke_descend_cusp`

### Statement
```lean
∀ N p (hp : p.Prime) (hpN : p ∣ N),
  let d := if p² ∣ N then p-1 else p
  ∀ γ : Fin (d+1) → GL (Fin 2) ℝ,
    (∀ v, (γ v).det = p) →
    ∀ f : CuspForm Γ_1(N), ∀ {c}, IsCusp c Γ_1(N/p) →
      c.IsZeroAt (fun z => Σ_v (⇑f ∣[k] γ v) z) k
```

### Miyake audit
- **Reference**: Miyake p. 160 closing remark: "If `f(z)` is a cusp form,
  all `g_p(z)` can be taken as cusp forms" (Lemma 4.6.7 conclusion).
- **Verdict**: ✓ Correct. Each slash preserves cuspidality; sums of
  zero-at-cusp functions are zero at cusps.

### Repo infrastructure
- **`heckeT_p_all_zero_at_cusps`** (`AdjointTheory.lean:158`,
  **PROVEN**): the technique for slash-sum cusp preservation. Reusable
  but stated for cusps of `Γ_1(N)`, not `Γ_1(N/p)`.
- **`Finset.sum_induction`** + `OnePoint.IsZeroAt.smul_iff` +
  `f.zero_at_cusps'`: the building blocks used in
  `heckeT_p_all_zero_at_cusps`. Same blocks work for `Γ_1(N/p)` cusps.

### Need for further breakdown
- **No**. Direct adaptation of `heckeT_p_all_zero_at_cusps`'s proof.

### Estimated complexity
- ~40 lines (almost a copy-paste of `heckeT_p_all_zero_at_cusps` with the
  level adjusted).

### Suggested approach
1. Mirror `heckeT_p_all_zero_at_cusps`'s proof:
   ```lean
   apply Finset.sum_induction _ (fun g => c.IsZeroAt g k)
     (fun _ _ ha hb => ha.add hb)
     ((0 : CuspForm Γ_1(N/p) k).zero_at_cusps' hc)
   ```
2. Use `OnePoint.IsZeroAt.smul_iff` and `f.zero_at_cusps'` for each
   slash by `γ v`.
3. The key lemma `f.zero_at_cusps' (IsCusp_glMap_smul' _ hc)` works for
   any cusp `c` (regardless of level), since `f`'s cuspidality is at
   level `Γ_1(N)` and lifts.

---

## T5d — `miyake_hecke_descend_char`

### Statement
```lean
∀ N p (hp : p.Prime) (hpN : p ∣ N),
  let d := if p² ∣ N then p-1 else p
  ∀ γ : Fin (d+1) → GL (Fin 2) ℝ,
    (∀ v, (γ v).det = p) →
    ∀ χ : (ZMod N)ˣ →* ℂˣ, ∀ χ' : (ZMod (N/p))ˣ →* ℂˣ,
    χ = χ'.comp (ZMod.unitsMap ...) →
    ∀ {f}, f ∈ modFormCharSpace χ →
    ∀ (γ_d_pair : { γ_d : SL₂(ℤ) // γ_d ∈ Gamma0 (N/p) }),
    (fun z => Σ_v ⇑f ∣[k] γ v z) ∣[k] mapGL ℝ γ_d_pair.val =
    (χ' (Gamma0MapUnits ⟨γ_d, γ_d_pair.property⟩) : ℂ) •
      (fun z => Σ_v ⇑f ∣[k] γ v z)
```

### Miyake audit
- **Reference**: Miyake p. 161 "Then `f_p(z) ∈ G_k(N/p, χ)`".
- **Verdict**: ⚠️ **Same over-generic issue as T5b** — the character
  preservation holds for SPECIFIC matrices (Miyake's), not arbitrary
  det-`p` matrices.
- **Required restatement** (TICKET T5d-pre): take the matrices from T5a
  with the action property as a parameter.

### Repo infrastructure
- **`heckeT_p_divN_preserves_modFormCharSpace`**
  (`Eigenforms/MainLemma.lean:910`, **PROVEN**): character preservation
  for `heckeT_p_divN` at level `Γ_1(N)`. Uses
  `heckeT_p_ut_orbit_comm_gamma0_fun` (the Γ_0(N)-orbit identity).
- **`Gamma0MapUnits`** (referenced in `Eigenforms/MainLemma.lean`): the
  map `Γ_0(N) → (ZMod N)ˣ` sending `γ → γ₁₁ mod N`. Reusable for level `N/p`.

### Need for further breakdown
- **Yes (1 sub-ticket)**: T5d-1: the Γ_0(N/p)-orbit identity for the
  slash sum (analogue of `heckeT_p_ut_orbit_comm_gamma0_fun`).

### Estimated complexity
- T5d-pre (restatement): ~20 lines.
- T5d-1 (Γ_0(N/p)-orbit identity): ~100 lines (mirrors
  `heckeT_p_ut_orbit_comm_gamma0` at the new level, using the new action
  from T5a-3).
- T5d (assembly): ~40 lines.
- **Total: ~160 lines.**

---

## T5 — `miyake_hecke_descend` (bundled)

### Statement
Existence of `Φ_p` with all 4 properties (cusp, char, q-shift, linearity).

### Miyake audit
- **Reference**: Miyake Eq. 4.6.13 + surrounding text (p. 161).
- **Verdict**: ✓ Correct as bundle.

### Repo infrastructure
- All from T5a–T5d once those are proven.
- **`cuspFormToModularForm`** (`Eigenforms/ConductorTheorem.lean:1419`)
  for cusp ↔ ModularForm conversion.

### Need for further breakdown
- **No**. Pure assembly of T5a, T5b, T5c, T5d.

### Estimated complexity
- ~80 lines (build `Φ_p` as a `ModularForm` using T5a's invariance + f's
  holo/bdd; bundle properties from T5b/T5c/T5d).

---

## T6 — `miyake_4_6_6_level_commute`

### Statement
```lean
∀ N l p (hp : p.Prime) (hpN : p ∣ N) (hpl : Coprime p l),
  ∀ Φ_N (q-shift at level N) f,
    ∀ Φ_M (q-shift at level l·N),
    ⇑(Φ_M (restrict f)) = ⇑(restrict (Φ_N f))  [function-level]
```

### Miyake audit
- **Reference**: Miyake Lemma 4.6.6(1) (p. 158).
- **Original**: commutative diagram between Hecke descent at level `pN → N`
  and at level `pM → M` (`M = lN`).
- **Verdict**: ✓ Statement is correct as conditional on both Φ's
  satisfying the q-shift property (this pins them down up to scalar via
  the q-expansion principle).

### Repo infrastructure
- **Mathlib's `Matrix.mul_assoc`, `SL₂(ℤ)` matrix algebra** — for the
  matrix conjugation identities.
- **`ModularForm.restrictSubgroup`** + `Gamma1_mapGL_le_of_dvd` for the
  level inclusions.
- The argument is via matrix identity, not requiring existing Hecke
  infrastructure beyond standard matrix algebra.

### Need for further breakdown
- **Yes (2 sub-tickets)**:
  - T6a: the coset reps from T5a at level `M = lN` agree with those at
    level `N` (as matrices). For `(l, p) = 1`, the explicit `[1,m;0,p]`
    reps work at both levels.
  - T6b: the function-level commutation follows from T6a + the
    distributivity of slash.

### Estimated complexity
- T6a (coset agreement): ~40 lines (mostly trivial since coset reps are
  the SAME matrices at both levels).
- T6b (function commutation): ~60 lines.
- **Total: ~100 lines.**

---

## T7 — `miyake_V_p_descend_identity` (assembly)

### Statement
Existence of `g_low` at `Γ_1(N/p)` such that `V_p g_low` at `Γ_1(N)`
matches `f` on `(p|n, Coprime n l')` indices.

### Miyake audit
- **Reference**: Miyake Eq. 4.6.12 (p. 161).
- **Verdict**: ✓ Correct.

### Repo infrastructure
- All from T1, T4 (proven), T5, T6.
- **`qSupportedOnDvd_eq_zero_or_exists_levelRaise_preimage_of_char`**
  (T4 in our chain, **PROVEN** in `Eigenforms/AtkinLehner.lean`).

### Need for further breakdown
- **No**. Pure assembly: apply T1 to get filter `g_filter` at level
  `l'·N`, apply T4 to descend, apply T5 to construct level-N `g_low`,
  apply T6 to match.

### Estimated complexity
- ~80-120 lines.

---

## T8 — `miyake_4_6_8_inductive_step` (assembly)

### Statement
Existence of `f_p ∈ qSupportedOnDvdSubmodule N k p ∩ cuspFormCharSpace`
such that `f - f_p` has reduced coprime-vanishing.

### Miyake audit
- **Reference**: Miyake p. 161, the closing assembly: "Let us show that
  `f(z) - f_p(pz)` satisfies the assumption of the theorem for `l'`."
- **Verdict**: ✓ Correct.

### Repo infrastructure
- All from T5, T7.
- **`levelRaise_mem_qSupportedOnDvdSubmodule`**
  (`Eigenforms/AtkinLehner.lean:263`, **PROVEN**) — to show `f_p` is
  q-supported.
- **`cuspForm_levelRaise_mem_cuspFormCharSpace`** (our local helper,
  **PROVEN** lines 229–260) for character preservation of `V_p`.

### Need for further breakdown
- **No**. Pure assembly:
  1. Get `g_low` from T7.
  2. Bundle `g_low` as a CuspForm using M5's cusp preservation (T5c).
  3. `f_p := V_p g_low` at level `Γ_1(N)`.
  4. Verify `f_p ∈ qSupportedOnDvdSubmodule` via
     `levelRaise_mem_qSupportedOnDvdSubmodule`.
  5. Verify `f_p ∈ cuspFormCharSpace` via
     `cuspForm_levelRaise_mem_cuspFormCharSpace`.
  6. Verify `f - f_p` has reduced coprime-vanishing using T7's q-identity.

### Estimated complexity
- ~50-80 lines.

---

## Final ticket table

| ID | Name | Type | Sub-tickets | LOC est. | Risk |
|---|---|---|---|---|---|
| T1 | iterated 4.6.5 | atomic | T1a (helper) | 100 | Low |
| T5a | coset action @ Γ_0(N/p) | atomic | T5a-pre, T5a-1, T5a-2, T5a-3 | 220 | **High** |
| T5b | q-expansion shift | mostly free | T5b-pre | 60 | Low |
| T5c | cusp preservation | mostly free | (none) | 40 | Low |
| T5d | character preservation | atomic | T5d-pre, T5d-1 | 160 | Medium |
| T5 | Hecke descent bundled | assembly | (none) | 80 | Low |
| T6 | level commutation | atomic | T6a, T6b | 100 | Medium |
| T7 | V_p descend identity | assembly | (none) | 100 | Low |
| T8 | inductive step | assembly | (none) | 60 | Low |

**Atomic obligations needing genuinely new mathematics**: T5a (high risk),
T5d (medium), T6 (medium). Combined ~480 LOC.

**Assembly + reuse**: T1, T5b, T5c, T5, T7, T8. Combined ~440 LOC.

**Grand total estimate**: ~920 LOC across 9 leaves + 7 sub-tickets.

---

## Pre-work: STATEMENT FIXES required

Before any proof attempt:

1. **T5a-pre**: Strengthen action property to specify
   `α v ∈ Γ_0(N)` (NOT Γ_1(N)) with a diamond-compatibility clause.
2. **T5b-pre**: Take T5a's specific matrices as a hypothesis (not arbitrary
   det-`p` matrices).
3. **T5d-pre**: Same as T5b-pre.

These restatements are needed for the lemmas to be **correctly stated**
(currently they're slightly over-generic; the q-shift and character
properties don't hold for arbitrary det-`p` matrix lists).

---

## Execution order recommendation

1. **First**: T5a-pre, T5b-pre, T5d-pre (statement fixes, ~70 lines).
2. **Second**: T1, T5b, T5c (the directly attackable / mostly-reusable).
3. **Third**: T5a, T5d, T6 (the genuinely new mathematical content).
4. **Fourth**: T5, T7, T8 (assemblies, near-mechanical once atoms are in).
