# Eigenforms + SMOObligations Structural Audit (2026-05-31)

**Scope:** ~15 700 LOC across 7 Eigenforms files and 9 SMOObligations files.

**Working dir:** `/Users/mcu22seu/Documents/GitHub/LeanModularForms-hecke`
**Branch:** `hecke-ring`

## Inventory at a Glance

| File | LOC | # decls | # private | Headline output |
|------|----:|--------:|---------:|-----------------|
| `Eigenforms/MainLemma.lean` | 1997 | 84 | 51 | `same_level_collapse_of_deep_oldform_image_of_projections_finset` |
| `Eigenforms/AtkinLehner.lean` | 1315 | 76 | 6 | `mainLemma_charSpace_of_sameLevelDivisorDecomposition` |
| `Eigenforms/ConductorTheorem.lean` | 1289 | 87 | 19 | `conductor_theorem_dichotomy_cuspForm_strong` |
| `Eigenforms/AtkinLehnerProjection.lean` | 1281 | 51 | 11 | `traceLevelRaiseCore_mem_cuspFormCharSpace` |
| `Eigenforms/HeckeLemma.lean` | 1172 | 48 | 5 | `qExpansion_vanish_of_T_p_eigenform_decomp` |
| `Eigenforms/TraceOperator.lean` | 352 | 16 | – | `traceGamma1_cuspForm` |
| `Eigenforms/MainLemma/CoprimeSieve.lean` | 194 | 12 | – | `sievedQExpansion_eq_coprime_radical` |
| `SMOObligations/SquarefreeDecomp.lean` | 1424 | 53 | 42 | `miyake_4_6_7_squarefree_decomp` |
| `SMOObligations/StrongMultiplicityOneFull.lean` | 1387 | 53 | 33 | `strongMultiplicityOne_constMul`, `…_unconditional` |
| `SMOObligations/DescentCosets.lean` | 1245 | 49 | 30 | `descendCosetList_action`, `miyake_4_6_4_dichotomy_strong` |
| `SMOObligations/Lemma4_6_14.lean` | 1084 | 33 | 29 | `Φ_qExp_coeff_eq_count_div_p_mul_g_low_coeff` |
| `SMOObligations/MiyakeDescend.lean` | 840 | 30 | – | `miyake_hecke_descend`, `miyake_hecke_descend_qexp` |
| `SMOObligations/Miyake465.lean` | 613 | 20 | – | `miyake_h_form_general`, `miyake_4_6_5_iterated_L` |
| `SMOObligations/LevelCommute.lean` | 596 | 18 | – | `miyake_4_6_6_level_commute`, `…_delta` |
| `SMOObligations/Lemma4_6_8.lean` | 451 | 14 | – | `miyake_4_6_8_inductive_step`, `…_subset_helper(_unconditional)` |
| `SMOObligations.lean` (umbrella) | 436 | – | – | `strongMultiplicityOne_axiom_clean`, `mainLemma_charSpace_routeB` |

**Total:** 15 676 LOC, 644 declarations, ~270 private. External downstream uses ~11 names from AtkinLehner.

---

## 1. Family Sprawl

### 1a. Miyake 4.6.5 family — TWO PARALLEL CHAINS (≈4 100 LOC)

`Miyake 4.6.5` ("coprime sieve") exists in **two independent developments**:

- `Eigenforms/MainLemma.lean` — **ModularForm-valued** chain (84 decls, 9 named `miyake_4_6_5_*`)
- `SMOObligations/Miyake465.lean` — **CuspForm-valued** chain (20 decls, 6 named `miyake_4_6_5_*`)

The MainLemma chain has eight near-identical Miyake 4.6.5 statements differentiating only on:
- period `1` vs period `N` (`_one` suffix)
- positive vs indicator form (`_indicator`)
- witness level `Γ₁(N)` vs `Γ₁(p·N)` (`_witness_at_pN`)
- concrete `heckeT_p_divN` witness (`_heckeT_p_divN`)
- generic `g` witness (no suffix)
- per-prime vs Finset (`_finset_sieve_*`) vs squarefree (`_squarefree_sieve_*`)

These are essentially 4 × 2 (8) variants of one identity over (ModularForm, prefactored sieve). All 8 should collapse to 1-2 generic statements + thin wrappers.

The CuspForm-valued chain in `Miyake465.lean` re-derives `miyake_4_6_5_coprime_filter_cuspForm`, `…_iterated_L`, and `…_iterated_L_general` (≈562 LOC) from scratch despite the ModularForm version already existing — using its own helper `cuspForm_restrictSubgroup_mem_cuspFormCharSpace`, `cuspForm_levelRaise_mem_cuspFormCharSpace`, etc. There is **no API bridge** between them.

### 1b. Miyake 4.6.8 family — TWO PARALLEL CHAINS

- `Eigenforms/MainLemma.lean`: `miyake_main_lemma_4_6_8_finset / _squarefree / _radical / _level_L / _level_L_witness_qExpansion_zero / _level_L_witness_eq_zero` (6 ModularForm-level variants, ≈210 LOC chain).
- `SMOObligations/Lemma4_6_8.lean`: `miyake_4_6_8_inductive_step / _subset_helper / _factor_dichotomy / _subset_helper_unconditional` (4 CuspForm-level variants, ≈451 LOC); plus 2 more façades `miyake_4_6_8_main_lemma_cuspForm(_unconditional)` in `SMOObligations.lean`.

The radical-level form, level-L form, level-L-witness-qExpansion-zero, level-L-witness-eq-zero variants are progressive specialisations of `_squarefree`. They could be inlined; only `_squarefree` and one downstream consumer have actual content.

### 1c. Conditional / unconditional doublets — pervasive

Almost every public theorem in SMOObligations.lean has a `_unconditional` twin produced by routing through `miyake_4_6_8_factor_dichotomy`:

- `coprimeSieve_admits_squarefree_decomposition_in_charSpace` / `…_unconditional`
- `mainLemma_charSpace_routeB` / `…_unconditional`
- `miyake_4_6_8_main_lemma_cuspForm` / `…_unconditional`
- `miyake_4_6_8_subset_helper` / `…_subset_helper_unconditional`
- `strongMultiplicityOne_axiom_clean` (with `h_chi_factor`) / `strongMultiplicityOne_axiom_clean_unconditional` (without)

This doubling is intentional — the conditional version is the "frozen" form, the unconditional is the newer derivative. Downstream only uses the unconditional forms (`strongMultiplicityOne_axiom_clean_unconditional`, `mainLemma_charSpace_routeB_unconditional`). The `_chi_factor`-bearing forms are dead code modulo the frozen public-axiom commitment.

### 1d. SameLevelDivisorProjections / TraceCorrectionPrime / PartialTraceCorrection — never instantiated

`AtkinLehner.lean` defines six structures and `AtkinLehnerProjection.lean` defines four more:

- `TraceDescent`, `SameLevelDivisorProjections`, `SameLevelDivisorProjectionsLocalField` (in `AtkinLehner`)
- `TraceCorrectionPrime`, with `.zero/.ofCore/.add/.neg/.smul/.sub/.toLocalField/...` API (in `AtkinLehner`, ≈250 LOC)
- `PartialTraceCorrection`, `TraceLevelRaiseCorrectionData`, `TraceLevelRaiseStableSaturationData`, `IsGammaStableCosetFinset`, `cuspFormOfGammaStableCosetSum(Linear)` (in `AtkinLehnerProjection`)

`grep` confirms **none of these structures are constructed anywhere outside the file that defines them.** The closest external touch-point is `SMOObligations.lean` calling `mainLemma_charSpace_of_sameLevelDivisorDecomposition` — which bypasses every one of these structures by taking the divisor decomposition directly. Roughly 800 LOC of AtkinLehner + 600 LOC of AtkinLehnerProjection are entirely scaffolding for an unused API.

### 1e. AtkinLehnerProjection — declared dead by its own docstring

The file's docstring (lines 49-150) explicitly states "**The naive p-supported coefficient formula is false** ... `pSupportedProjection` is **not** the right operator to feed into `qSupportedOnDvd_mem_cuspFormsOld_of_char` for a composite-`N` `mainLemma`" and lists the alternative routes (Atkin–Lehner–Li orthogonality, Petersson, Möbius sieve) that should be used instead. The file then lands 1100 LOC of `pSupportedProjection` API and `TraceLevelRaise*` machinery anyway, none of which is consumed downstream.

### 1f. ConductorTheorem case A / case B — symmetric duplication

- `conductorTheoremCaseA_modularForm` (584), `…_apply` (601), `…_mem_modFormCharSpace` (1201)
- `conductorTheoremCaseA_cuspForm` (702), `…_apply` (722), `…_mem_cuspFormCharSpace` (1223)
- `conductor_theorem_dichotomy` (1141), `_cuspForm` (1158), `_strong` (1247), `_cuspForm_strong` (1266)

Four variants of one statement. `_strong` only differs from non-strong by adding `[NeZero (N / l)]`. Only `conductor_theorem_dichotomy_cuspForm_strong` is used in `SMOObligations/Lemma4_6_8.lean` (one site each for the two case-B route helpers).

### 1g. HeckeLemma — proves an isolated lemma, no consumers

`HeckeLemma.lean` (1172 LOC, 48 decls) develops Miyake 4.6.3 plus the `Delta0_submonoid.intLift / intDet / IsPrimitiveDelta0` API, the `diagGL_Q` matrices, and `qExpansion_vanish_of_T_p_eigenform[_decomp]`. **No external code references `Delta0_submonoid`, `diagGL_Q`, `qExpansion_vanish_of_T_p_eigenform`, or any other HeckeLemma name outside the file itself.** The `Delta0_submonoid` used elsewhere is the separate definition in `HeckeRIngs/GLn/CongruenceHecke/Foundation.lean`.

---

## 2. Hypothesis Sprawl

### 2a. `h_chi_factor` — Miyake's "primes of `(l, N/m_χ)`" restriction

Threaded through every conditional form of Miyake 4.6.X:

```
h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
  haveI : NeZero (N / p) := neZero_div_of_mem_primeFactors hp_in
  ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
    χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))
```

Appears on **5 separate public theorems** in `SMOObligations.lean` (lines 76, 146, 268, 302, 428). All can be discharged unconditionally by routing through `miyake_4_6_8_factor_dichotomy` — exactly what the `_unconditional` variants already do. The `_chi_factor`-bearing variants exist only to preserve `strongMultiplicityOne_axiom_clean`'s frozen signature.

### 2b. `h_le_full` + `h_vanish` + `hf_χ` triplet

`Eigenforms/MainLemma.lean` has 6 public theorems all carrying the same trio:

```
(h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod → (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
(h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤ (Gamma1 M).map (mapGL ℝ))
```

The level inclusion `h_le_full` is recoverable from `L`-primes-dividing-`M` via `Gamma1_mapGL_le_of_dvd`; it should be derived inside the theorem, not threaded through callers.

### 2c. `NeZero` boilerplate

`MainLemma.lean` alone has 19 `haveI hM_prev_ne : NeZero (M * L'.prod) := …`-style instances, each spelling out `Nat.mul_ne_zero` and `List.prod_pos`. The `neZero_mul_list_prod_of_prime_dvd` private theorem (line 54) exists to abbreviate this but is used inconsistently.

### 2d. CuspForm/ModularForm membership doublet

Across SMO files, every `f : CuspForm` requires both `hfχ : f ∈ cuspFormCharSpace k χ` AND `hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ`, repeatedly converted via `cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace`. About 40 occurrences. A single hypothesis with one transport theorem would suffice.

---

## 3. Redundant Structures

| Structure | File | Used externally? | Comment |
|-----------|------|:----------------:|---------|
| `TraceDescent` | AtkinLehner.lean:701 | No | Constructed only by the file's own `ofSingleDivisor / ofPrimePower / ofSameLevelDivisorProjections` |
| `SameLevelDivisorProjections` | AtkinLehner.lean:808 | No | Only constructed by `ofLocalFields / ofZeroLocalFields / ofTraceCorrections` in same file |
| `SameLevelDivisorProjectionsLocalField` | AtkinLehner.lean:1035 | No | Only constructed by `.zero` and via `TraceCorrectionPrime.toLocalField` |
| `TraceCorrectionPrime` | AtkinLehner.lean:1105 | No | 250 LOC of `.zero/.ofCore/.add/.neg/.smul/.sub/...` instance API, no instances anywhere |
| `PartialTraceCorrection` | AtkinLehnerProjection.lean:574 | No | Only constructed via `.zero` and `ofTraceLevelRaiseCorrectionData` |
| `TraceLevelRaiseCorrectionData` | AtkinLehnerProjection.lean:916 | No | Only constructed via `ofStableSaturation` |
| `TraceLevelRaiseStableSaturationData` | AtkinLehnerProjection.lean:1129 | No | Pure definitional packaging, no consumers |
| `IsGammaStableCosetFinset` | AtkinLehnerProjection.lean:975 | No | Helper for `cuspFormOfGammaStableCosetSum`, also unused externally |
| `ModularFormSameLevelDivisorProjections` | MainLemma.lean:1696 | Yes — once (in AtkinLehner.lean:1019) | Has 1 use; itself wraps a single existential, could be a `Prop` or just a `∃` |
| `Miyake467Decomp` (private) | SquarefreeDecomp.lean:142 | (private) | Local helper bundled as a structure where a tuple would suffice |

**Net:** 8 of the 10 enumerated structures (≈700 LOC of definitional API) are scaffolding for an abandoned design path.

---

## 4. Duplicate Proof Bodies

### 4a. `one_mem_strictPeriods_Gamma1_map` — defined four times

The same six-line lemma appears as:

- `SMOObligations/Lemma4_6_8.lean:22` — `private lemma one_mem_strictPeriods_Gamma1_map`
- `SMOObligations/Lemma4_6_14.lean:499` — `private lemma one_mem_strictPeriods_Gamma1_map`
- `SMOObligations/SquarefreeDecomp.lean:120` — `private lemma m7_one_mem_strictPeriods_Gamma1_map`
- `SMOObligations/StrongMultiplicityOneFull.lean:68` — `private lemma one_mem_strictPeriods_Gamma1_map_local`
- `Eigenforms/AtkinLehner.lean:85` — `private lemma h1_period_Gamma1`

The body is always `rw [show … from rfl, strictPeriods_Gamma1]; exact ⟨1, by simp⟩`. Plus 8 more inline copies in Miyake465, MiyakeDescend, LevelCommute, DescentCosets that just inline the same body.

### 4b. `cuspForm_cast_coe` / `modularForm_cast_coe` / `qExpansion_one_cuspForm_cast_coeff` / `cuspFormCharSpace_mem_cast`

`SquarefreeDecomp.lean` defines `qExpansion_one_cuspForm_cast_coeff` and `cuspFormCharSpace_mem_cast` at lines 878, 886. `Lemma4_6_14.lean` redefines `cuspForm_cast_coe` and `modularForm_cast_coe` at lines 721, 726. All four are one-line `cases h; rfl` lemmas about transport along `A = B`. They should live in a shared helper file with `Gamma1`/`CuspForm`/`ModularForm` cast lemmas.

### 4c. Sieve-induction skeleton — twice in MainLemma + twice in Miyake465

- `MainLemma.lean:472-504` (`miyake_main_lemma_4_6_8_finset`, `Finset.induction_on`)
- `MainLemma.lean:278-300` (`miyake_4_6_5_finset_sieve_heckeT_p_divN_one`, `Finset.induction_on`)
- `Miyake465.lean:232-270` (`miyake_4_6_5_iterated_helper`, `Nat.induction`)
- `Miyake465.lean:489-535` (`miyake_4_6_5_iterated_helper_general`)

All four use the same induction pattern: empty case → `simp`; `insert p₀ S'` case → unpack IH, apply single-prime step, recombine. The single-prime step is the only varying piece. Could be one parametric `Finset.induction_on` helper with the step as an argument.

### 4d. `miyake_4_6_8_subset_helper` vs `miyake_4_6_8_subset_helper_unconditional`

Both prove the same conclusion by the same `Finset.card`-induction skeleton (Lemma4_6_8.lean:256-291 vs 394-449). The only difference is whether the per-prime χ-factorisation is supplied (`h_chi_factor`) or computed (`miyake_4_6_8_factor_dichotomy`). ~85 LOC of repeated `induction → zero / succ → obtain → refine` structure.

### 4e. `extend_primeFactors_to_divisor_decomposition` used 2× by parallel callers

`SMOObligations.lean:110` is the helper; called by both `coprimeSieve_admits_squarefree_decomposition_in_charSpace` (line 139) and its `_unconditional` (line 169). Fine — but those two callers are otherwise structurally identical 30-line proofs differing only by which `miyake_4_6_8_main_lemma_cuspForm{,_unconditional}` they call. Should be merged with the χ-factor witness as a parameter (`Option`).

---

## 5. Cross-File Redundancy

### 5a. `qSupportedOnDvdSubmodule`-membership theorems strewn across Atkin-Lehner

`AtkinLehner.lean` has:
- `qSupportedOnDvd_mem_cuspFormsOld_of_char` (186)
- `qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld` (546)
- `qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_of_dvd` (583)
- `iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld` (560)
- `iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_divisors` (598)
- `mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule[_divisors]` (571, 612)

All of these prove versions of the same fact "a `p`-supported cusp form in the χ-space is old". The downstream consumers (SMOObligations.lean:254, Downstream.lean:36/49) only use `mainLemma_charSpace_of_sameLevelDivisorDecomposition`. The iSup-flavored variants and the `_divisors` variants are interchangeable rewrappings.

### 5b. `mainLemma_charSpace_*` — 9+ near-identical wrappers

In `AtkinLehner.lean` alone:
- `mainLemma_charSpace_primePower` (441), `…_primePower_via_divisor_iSup` (686), `…_primePower_via_TraceDescent` (777)
- `mainLemma_charSpace_of_prime_decomposition` (469), `…_of_primeFactors_decomposition` (493)
- `mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule[_divisors]` (571, 612)
- `mainLemma_charSpace_of_TraceDescent` (723), `…_of_singleDivisorSupport` (791), `…_of_SameLevelDivisorProjections` (855)
- `mainLemma_charSpace_of_sameLevelDivisorDecomposition` (871) — the only one used
- `mainLemma_charSpace_of_modularFormSameLevelDivisorDecomposition` (967), `…_of_modularFormSameLevelDivisorProjections` (1009)
- `mainLemma_charSpace_of_traceCorrections` (1296)

Plus in `AtkinLehnerProjection.lean`:
- `mainLemma_charSpace_of_finset_decomposition` (532), `mainLemma_charSpace_of_partialTraceCorrections` (668)

That is **14 different formulations** of "the Main Lemma at level N from a decomposition". Real downstream usage: 3 of them.

### 5c. `restrictSubgroup_mem_modFormCharSpace` — three flavours

- `MainLemma.lean:332` — base ModularForm version
- `MainLemma.lean:423` — `_comp` variant adding character composition
- `Miyake465.lean:28` — `cuspForm_restrictSubgroup_mem_cuspFormCharSpace` (CuspForm reflection)

### 5d. `cuspForm_levelRaise_mem_cuspFormCharSpace` is `levelRaise_mem_cuspFormCharSpace`

`Miyake465.lean:44` and `AtkinLehnerProjection.lean:822` define the same lemma under different names. Both wrap `MainLemma.modularFormLevelRaise_mem_modFormCharSpace`.

### 5e. Module-level Miyake 4.6.X family split is artificial

The dependency chain is strictly linear:

```
SMOObligations.lean
  └→ Lemma4_6_8 → Lemma4_6_14 → SquarefreeDecomp → LevelCommute → MiyakeDescend → DescentCosets → Miyake465
                                                                                                   └→ Eigenforms.{AtkinLehner, ConductorTheorem, MainLemma}
```

i.e. each "Lemma N" file *just* imports the next and adds 1-3 theorems. There is no parallel structure across the family; the split is purely chronological (one section per file). All eight SMO-side files (~7 200 LOC) form a single straight-line chain that could equally well live as one or two files (Miyake §4.6 / SMO closure).

---

## 6. Mathlib-Redo (Reinvented Wheel)

### 6a. Helper lemmas that are mathlib-ready

`Eigenforms/MainLemma/CoprimeSieve.lean` defines `sievedQExpansion`, `primeCoeffSieve`, `finsetPrimeCoeffSieve`, `finsetPrimeSievedSeries`, `coprime_indicator_eq_sum_moebius`, `sievedQExpansion_eq_coprime_radical`. These are pure number theory / power series and would fit comfortably in `Mathlib.NumberTheory.ArithmeticFunction.Moebius` or a new `Mathlib.RingTheory.PowerSeries.CoprimeSieve`. The Möbius-indicator identity `coprime_indicator_eq_sum_moebius` is a direct consequence of `ArithmeticFunction.moebius_mul_coe_zeta`; the wrapper might already exist (worth a `loogle (Coprime ?n ?L) ↔ ∑ d ∈ (Nat.gcd ?n ?L).divisors, _`).

### 6b. `extend_primeFactors_to_divisor_decomposition`

`SMOObligations.lean:110` extends a Finset-indexed family from `N.primeFactors` to `N.divisors.filter (1 < ·)` by zero-padding. This is a general `Finset` operation:

```
Finset.sum_extend_by_zero : ∀ (s t : Finset α) (h : s ⊆ t) (f : α → M),
  ∑ x ∈ s, f x = ∑ x ∈ t, if x ∈ s then f x else 0
```

— exists in mathlib (`Finset.sum_subset` + `if_neg`). The 30-line proof should be a 2-line wrapper.

### 6c. `exists_prime_coprime_avoiding_finset`

`SMOObligations.lean:339` proves: "∃ prime q coprime to N, not in a given finite set S, with q² also avoiding S, etc." Pure number theory; should be near `Nat.exists_infinite_primes` in mathlib. The body is a single `obtain ⟨q, _, _⟩ := Nat.exists_infinite_primes (S.sup id + N + n.val + 2)` plus 6 `omega`-style bounds.

### 6d. `slash_inv_eq_smul_of_levelRaiseFun_eq` etc. — `slash` on `GL ℚ` matrices

`ConductorTheorem.lean:338` and ~30 sibling lemmas manipulate `‖ ∣[k] (g : GL (Fin 2) ℝ)` where `g` is constructed from an integer matrix via `levelRaiseMatrix`. The whole `Matrix.SpecialLinearGroup ℚ → GL ℝ` plumbing (`mapGL`, `glMap`, `diagGL_Q`, `levelRaiseMatrix`) is project-local; mathlib has `Matrix.SpecialLinearGroup.map` that should subsume most of it.

### 6e. `ZMod.unitsMap_comp` chain

Throughout `SMOObligations*` and `Eigenforms/MainLemma.lean`, the same calculation appears: given `N ∣ M ∣ K`, `(χ.comp (unitsMap h₁)).comp (unitsMap h₂) = χ.comp (unitsMap (h₁.trans h₂))`. Always proven by `rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]`. ~25 occurrences. Should be `@[simp]` if not already, and definitely a one-liner via `ZMod.unitsMap_comp`.

---

## 7. Bloat Diagnosis (≤500 words)

**The headline:** 5 of 16 files (`MainLemma`, `AtkinLehner`, `AtkinLehnerProjection`, `ConductorTheorem`, `HeckeLemma`; ≈7 100 LOC) contain the bulk of the bloat. The SMOObligations chain is straight-line and content-dense; the bloat is concentrated in the Eigenforms side.

**Root cause #1: failed-route scaffolding.** `AtkinLehnerProjection.lean` opens with 100 lines of docstring concluding "this is the wrong operator, do not use," then lands 1 100 LOC of API for that wrong operator anyway. Compounding this: the `SameLevelDivisorProjections / TraceCorrectionPrime / PartialTraceCorrection / TraceLevelRaiseCorrectionData / TraceLevelRaiseStableSaturationData / IsGammaStableCosetFinset` structures (10 in total, ≈1 500 LOC including their `.zero/.add/.neg/.smul/.ofCore/.toLocalField/…` instance APIs) were a tentative spectral-decomposition design that downstream never adopted. Downstream uses `mainLemma_charSpace_of_sameLevelDivisorDecomposition` — a direct decomposition consumer — bypassing every one of these structures.

**Root cause #2: ModularForm/CuspForm parallel chains.** Miyake 4.6.5 has 9 ModularForm-valued variants (`MainLemma.lean`) and 6 CuspForm-valued variants (`Miyake465.lean`) developed independently, with no bridge. The "ModularForm chain" was the original Phase-1 design; the "CuspForm chain" was retro-fitted in the SMO obligations push.

**Root cause #3: conditional/unconditional twinning.** Every Miyake 4.6.X result that touches χ has two flavours: with `h_chi_factor` (preserves frozen `strongMultiplicityOne_axiom_clean` signature) and without (Miyake 4.6.4 dichotomy discharges it). Downstream only consumes the unconditional twins, but the conditional twins remain because the frozen public theorem requires them.

**Root cause #4: micro-decomposition into one file per Miyake-section.** The 8 SMO files (DescentCosets → Miyake465 → MiyakeDescend → LevelCommute → SquarefreeDecomp → Lemma4_6_14 → Lemma4_6_8 → SMOObligations) form a linear chain where each file adds 1-3 named "main" theorems and 15-50 private helpers. The split is by Miyake section number, not by logical content — the whole chain could equally well be one ~5 000 LOC file. The result is 30 `private lemma` × 8 files where many are direct duplicates (e.g. `one_mem_strictPeriods_Gamma1_map`).

**Root cause #5: `ConductorTheorem` case-A / case-B / dichotomy / `_strong` quadrupling.** Miyake 4.6.4 lands as 4 variants of essentially one statement; only `_cuspForm_strong` is actually consumed.

**Root cause #6: `HeckeLemma` dead-ends.** 1 172 LOC develop a self-contained `Delta0_submonoid.intLift / IsPrimitiveDelta0 / diagGL_Q / qExpansion_vanish_of_T_p_eigenform` API that nothing outside the file imports — the project's `Delta0_submonoid` is the separate `HeckeRIngs/GLn/CongruenceHecke/Foundation` definition.

**Realistic reducible LOC:** ~6 500 of the 15 700 LOC are removable / collapsible without changing what downstream consumes. Headlines `strongMultiplicityOne_constMul` and `strongMultiplicityOne_axiom_clean` need only `mainLemma_charSpace_of_sameLevelDivisorDecomposition` + the 8-stage SMO descent chain — ≈9 000 LOC of essential content.

---

## 8. Reduction Plan (12 tickets)

### R1. Delete `AtkinLehnerProjection.lean` entirely (−1 281 LOC) [BIG]
After confirming none of `pSupportedProjection*`, `traceLevelRaiseCore*`, `PartialTraceCorrection*`, `TraceLevelRaiseCorrectionData*`, `IsGammaStableCosetFinset*`, `cuspFormOfGammaStableCosetSum*` is referenced externally (`grep` confirms zero hits outside the file). The five `traceGamma1_*` theorems that ARE useful (`traceGamma1_mem_modFormCharSpace`, `traceGamma1_diamondOpHom_commute`, `traceGamma1_slash_mapGL_commute`, `traceGamma1_cuspForm_mem_cuspFormCharSpace`, `levelRaise_mem_cuspFormCharSpace`) can move into `TraceOperator.lean` or `AtkinLehner.lean`. **Verify by running `lake build` after deletion.**

### R2. Delete `TraceCorrectionPrime`/`SameLevelDivisorProjections{,LocalField}`/`TraceDescent` structures from `AtkinLehner.lean` (−700 LOC) [BIG]
Replace all 14 `mainLemma_charSpace_*` wrappers with just two:
- `mainLemma_charSpace_primePower` (prime-power case, used by Downstream.lean)
- `mainLemma_charSpace_of_sameLevelDivisorDecomposition` (general decomposition, used by SMO)
And delete `_of_prime_decomposition`, `_of_primeFactors_decomposition`, `_of_TraceDescent`, `_of_singleDivisorSupport`, `_of_SameLevelDivisorProjections`, `_of_modularFormSameLevelDivisorDecomposition`, `_of_modularFormSameLevelDivisorProjections`, `_of_traceCorrections`, `_of_mem_iSup_qSupportedOnDvdSubmodule[_divisors]`, `_primePower_via_divisor_iSup`, `_primePower_via_TraceDescent`.

### R3. Delete `HeckeLemma.lean` (−1 172 LOC) [BIG]
Nothing imports `Delta0_submonoid.intLift`, `IsPrimitiveDelta0`, `diagGL_Q`, `slash_diagGL_Q_apply`, `qExpansion_vanish_of_T_p_eigenform`, or any other HeckeLemma name. The "Hecke recurrence on Fourier coefficients" content (`hecke_recurrence_of_T_p_eigenform`) duplicates `fourierCoeff_heckeT_p` from `QExpansionSlash.lean`. **Verify by `lake build`.**

### R4. Collapse Miyake 4.6.5 — 9→2 ModularForm-side, 6→2 CuspForm-side [BIG]
Keep `miyake_4_6_5_prime_sieve_from_no_diamond_one` (period-1 generic) and `miyake_4_6_5_finset_sieve_heckeT_p_divN_one` (Finset iteration). Delete the 4 period-N variants, the indicator variants, and the witness-at-pN variants (callers can `restrictSubgroup` themselves). For Miyake465: keep `miyake_4_6_5_coprime_filter_cuspForm` and `miyake_4_6_5_iterated_L`; delete `miyake_h_form_general`, `…_iterated_L_general` (their callers in SquarefreeDecomp can use the simpler variants).

### R5. Collapse Miyake 4.6.8 ModularForm chain (−180 LOC) [MED]
In `MainLemma.lean`, delete `miyake_main_lemma_4_6_8_finset / _squarefree / _radical / _level_L`. Keep only `_level_L_witness_qExpansion_zero` (used by `_level_L_witness_eq_zero`) and `_witness_eq_zero`. Even better: delete the entire ModularForm-side 4.6.8 chain; the SMO side (Lemma4_6_8.lean) is the consumer-facing version.

### R6. Delete one half of the conditional/unconditional twins (−400 LOC) [MED]
Drop the `_chi_factor`-bearing versions: `mainLemma_charSpace_routeB`, `coprimeSieve_admits_squarefree_decomposition_in_charSpace`, `miyake_4_6_8_main_lemma_cuspForm`, `miyake_4_6_8_subset_helper` (in Lemma4_6_8.lean), `newform_unique_routeB`. Keep the unconditional variants only. The frozen `strongMultiplicityOne_axiom_clean` signature can be kept by deriving it as a 3-line corollary of `…_axiom_clean_unconditional` (drop the unused `h_chi_factor` argument inside).

### R7. Merge the 4 ConductorTheorem variants (−400 LOC) [MED]
Keep only `conductor_theorem_dichotomy_cuspForm_strong` (the only one consumed). Delete `conductor_theorem_dichotomy`, `_cuspForm`, `_strong`, plus the parallel `conductorTheoremCaseA_modularForm` API (callers can use the `_cuspForm` version and lift). Estimate ≈400 LOC removable.

### R8. Extract `one_mem_strictPeriods_Gamma1_map` to `TraceOperator.lean` or `Modularforms/QExpansionSlash.lean` [SMALL]
Single definition replacing the 4 redefinitions + 8 inlinings. Make it `@[simp]` if possible.

### R9. Extract a shared `Modularforms/Cast.lean` for cast lemmas [SMALL]
Move `cuspForm_cast_coe`, `modularForm_cast_coe`, `qExpansion_one_cuspForm_cast_coeff`, `cuspFormCharSpace_mem_cast`, `cast_add_Gamma1`, `cast_sum_Gamma1`, `cast_mem_modFormCharSpace_Gamma1`, `cast_eq_zero_iff_Gamma1`, `restrictSubgroup_cast_eq_of_level_eq`, `restrictSubgroup_cast_nil_eq`, `qExpansion_coeff_cast_Gamma1` to one helper file. ≈150 LOC dedup.

### R10. Merge the 8 SMO files → 2 files (−500 LOC import boilerplate, structural) [BIG]
The chain `DescentCosets → Miyake465 → MiyakeDescend → LevelCommute → SquarefreeDecomp → Lemma4_6_14 → Lemma4_6_8 → SMOObligations` is purely linear; each file is one Miyake section. Merge into:
- `SMOObligations/Descent.lean` (DescentCosets + LevelCommute + MiyakeDescend, ≈2 600 LOC)
- `SMOObligations/MainLemma.lean` (Miyake465 + Lemma4_6_14 + SquarefreeDecomp + Lemma4_6_8 + SMOObligations.lean, ≈4 000 LOC)
- Keep `StrongMultiplicityOneFull.lean` separate.

Removes ~70 imports + 16 namespace/section markers + 8 file-header `variable` declarations. Each downstream `import LeanModularForms.SMOObligations.Foo` collapses to 2 imports.

### R11. Push `CoprimeSieve.lean` mathlib-ward (−194 LOC if accepted upstream) [MED]
`sievedQExpansion`, `primeCoeffSieve`, `finsetPrimeCoeffSieve`, `finsetPrimeSievedSeries`, `coprime_indicator_eq_sum_moebius` are pure number theory. Propose to `Mathlib.NumberTheory.ArithmeticFunction.Moebius` (or a new `Mathlib.RingTheory.PowerSeries.Sieve`). Until accepted, can stay as-is.

### R12. Drop unused MainLemma iterated-sieve combinator API (−300 LOC) [MED]
`MainLemma.lean` lines 672-1265 develop `iteratedSieveWitnessOnList`, `iteratedSieveCorrectionsOnList`, `iteratedSieveCorrectionPiecesOnList` plus 30+ private structural lemmas culminating in `restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish` and `IsOldformImageAtDeep`. The downstream-consumed result `same_level_collapse_of_deep_oldform_image_of_projections_finset` could be re-proven directly from `miyake_main_lemma_4_6_8_level_L_witness_eq_zero` (Möbius-style), avoiding the whole inductive piece-tracking machinery. ≈300 LOC reduction; needs Möbius-inversion bridge.

---

## Estimated Reduction

| Ticket | LOC saved (est.) |
|--------|------------------:|
| R1: delete AtkinLehnerProjection | −1 281 |
| R2: delete TraceCorrection structures | −700 |
| R3: delete HeckeLemma | −1 172 |
| R4: collapse 4.6.5 family | −600 |
| R5: collapse 4.6.8 ModularForm chain | −180 |
| R6: drop conditional twins | −400 |
| R7: merge ConductorTheorem variants | −400 |
| R8: dedup `one_mem_strictPeriods_Gamma1_map` | −60 |
| R9: shared cast lemma file | −100 |
| R10: merge SMO 8→2 files | −300 (overhead) |
| R11: mathlib push CoprimeSieve | −194 (conditional) |
| R12: simplify MainLemma iterated-sieve combinator | −300 |
| **TOTAL** | **−5 687** (≈36 %) |

Headlines (`strongMultiplicityOne_constMul`, `strongMultiplicityOne_axiom_clean`) keep working — they need only `mainLemma_charSpace_routeB_unconditional` → `mainLemma_charSpace_of_sameLevelDivisorDecomposition` → `qSupportedOnDvd_mem_cuspFormsOld_of_char`, and the full 8-stage SMO descent chain. None of the deleted scaffolding sits on that path.
