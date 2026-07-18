# Newforms subtree — structural overview (2026-05-31)

**Scope.** 12,099 LOC across 12 files (one root + 11 in `Newforms/`):

| File | LOC | Decls (top-level) | Private |
| ---- | --: | ----------------: | ------: |
| `Newforms.lean` (root) | 588 | 21 | 2 |
| `Newforms/Basic.lean` | 495 | 48 | 2 |
| `Newforms/MainLemma.lean` | 484 | 31 | 5 |
| `Newforms/LevelRaiseComm.lean` | 992 | 24 | 34 |
| `Newforms/FullEigenform.lean` | 219 | 3 | 8 (re: 3 private) |
| `Newforms/CoeffSeq.lean` | 1,197 | 61 | 3 |
| `Newforms/BadPrimeAdjoint.lean` | 1,265 | 68 | 10 |
| `Newforms/BadPrimeCosets.lean` | 1,235 | 53 | 12 |
| `Newforms/BadPrimeReduction.lean` | 1,560 | 41 | 19 |
| `Newforms/Fricke.lean` | 1,447 | 98 | 7 |
| `Newforms/FrickeTwist.lean` | 1,509 | 35 | 16 |
| `Newforms/MellinBridges.lean` | 1,608 | 52 | 5 |
| **Total** | **12,599** | **535** | **121** |

**Sorries:** 2 (both documented as blocked-on-external-input):
- `MainLemma.lean:410` — `mainLemma` (Atkin-Lehner Main Lemma DS 5.7.1). **Permitted per task brief.**
- `CoeffSeq.lean:1144` — `Newform.exists_nonzero_prime_eigenvalue`. Blocks classical `strongMultiplicityOne` (CoeffSeq.lean:1154).

**Build status:** Both `Newforms.lean` and downstream imports are green; the 4 protected headlines (`heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`, `strongMultiplicityOne_constMul`, `strongMultiplicityOne_axiom_clean`) all transitively pull this subtree via `FullEigenform.lean`.

---

## 1. Family Sprawl

This is the #1 driver of bloat. There are five major sprawl families.

### 1A. The 6×6 `Hecke-data × Dirichlet-data` consumer matrix (Fricke / FrickeTwist / MellinBridges)

For each pair of `(H_input, D_input)` the project ships **four** parallel
consumers: `HeckeEntireExtension_of_…`, `analyticContradiction_of_…`,
`exists_nonzero_prime_eigenvalue_of_…`, `strongMultiplicityOne_of_…_of_newformUnique`.

There are **6 Hecke-side inputs** ranked by abstractness:

| Hecke input | Lives in | Field count |
| ----------- | -------- | ----------: |
| `HeckeEntireExtension` (Prop) | Fricke:120 | 0 |
| `HeckeFEData` | Fricke:129 | 2 |
| `MellinPairData` | Fricke:181 | 10 |
| `ImAxisMellinData` | Fricke:276 | 8 |
| `FrickeTwistData` | FrickeTwist:70 | 6 |
| `FrickeSlashData` | MellinBridges:778 | 4 |
| `CompletedFrickeData` / `CompletedMellinData` | MellinBridges:1296/1211 | 9/8 |

And **6 Dirichlet-side inputs** (the same conceptual data at decreasing levels of unfolding):

| Dirichlet input | Lives in | LOC of signature |
| --------------- | -------- | ---------------: |
| `NoEntireExtensionUnderBadPrime` (Prop) | FrickeTwist:162 | 6 |
| `DirichletQuotientHasPoleUnderBadPrime` (Prop) | FrickeTwist:197 | 15 |
| `HasDirichletZeroCertificate` | FrickeTwist:615 | 22 |
| `dirichletZeroCertificate` (closure shape) | FrickeTwist:680 | 27 |
| `full_dirichletZeroCertificate` (~55 LOC unfolded ∃-clause shape) | FrickeTwist:1067, MellinBridges:884, root:307… | 55 LOC each |
| `PerNewformFullDirichletData` (bundled struct) | MellinBridges:46 | 8 fields |

The cross-product produces 32+ unique conversion theorems (`strongMultiplicityOne_of_*` alone has 19 distinct variants — see grep output of unique base-names below):

```
analyticContradiction
analyticContradiction_of_newformUnique
analyticContradiction_of_newSubspaceZeroCriterion
classicalInputs_of_full_dirichletZeroCertificate_of_newformUnique
CompletedFrickeData_of_PerNewformFullDirichletData_of_newformUnique
FrickeSlashData_of_classicalInputs_T111
FrickeSlashData_of_dirichletZero
FrickeSlashData_of_full_dirichletZeroCertificate
FrickeSlashData_of_PerNewformFullDirichletData
HeckeEntireExtension_of_dirichletZero
HeckeEntireExtension_of_dirichletZeroCertificate (×2)
HeckeEntireExtension_of_full_dirichletZeroCertificate
HeckeEntireExtension_of_HasDirichletZeroCertificate
HeckeFEData_of_classicalInputs_T111
HeckeFEData_of_dirichletZero
HeckeFEData_of_PerNewformFullDirichletData
ImAxisMellinData_of_PerNewformFullDirichletData
MellinPairData_of_PerNewformFullDirichletData
```

**The ~55-LOC inline ∃-clause is the biggest single offender.** It appears verbatim in **24 separate theorem signatures** (`grep "FullDirichletQuotientUniversalFClause f χ S T s₀" | wc -l` = 24) and references `Newform.dirichletLift χ * Newform.dirichletLift χ` **176 times** across the subtree. Each of the 55 lines is the same expression of the form

```
∃ (T : Finset Nat.Primes) (s₀ : ℂ),
  AnalyticAt ℂ (fun s ↦ DirichletCharacter.LFunction
    (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) * ∏ p ∈ T, …) s₀ ∧
  AnalyticAt ℂ (fun s ↦ …) s₀ ∧
  (… ≠ 0) ∧ (… = 0) ∧ meromorphicOrderAt … ≠ ⊤ ∧
  Newform.FullDirichletQuotientUniversalFClause f χ S T s₀
```

`PerNewformFullDirichletData` (MellinBridges:46) **already exists** as the bundled
form of this exact ∃-clause. **`full_pole_witness_data_of_PerNewformFullDirichletData`
(MellinBridges:100) packages the struct into the ∃-clause shape.**

**Canonical form / unification opportunity:** Drop the ∃-clause shape entirely
from public signatures. Every public theorem should take
`PerNewformFullDirichletData` (or the `classicalInputs_T111` reducer) and the
project should expose **one** consumer per *headline endpoint* (3 only:
`analyticContradiction`, `existsNonzeroPrimeEigenvalue`, `strongMultiplicityOne`).
The Hecke side is already fan-in (all the `*_of_HeckeFEData`,
`*_of_MellinPairData` etc. immediately call `_of_HeckeEntireExtension` —
they're 3-line forwarders). Hand callers a single `*_of_HeckeFEData_of_perNewform`
consumer per endpoint and let them upgrade via `HeckeFEData.ofMellinData`,
`HeckeFEData.ofImAxisData`, `HeckeFEData.ofFrickeSlashData` etc. (which already
exist).

**Sample sizes / LOC saved estimate:** Removing the 24 inline ∃-clauses cuts
~1,300 LOC just in signatures (24 × 55). Replacing 19 SMO variants with 3
canonical ones cuts another ~400 LOC of theorem bodies (each forwarder is ~10–15
LOC). **Total ~1,700 LOC** without touching mathematics, just bundling.

### 1B. Three sibling files: `BadPrimeAdjoint` / `BadPrimeCosets` / `BadPrimeReduction`

These three files (4,060 LOC total) form a tightly-coupled chain of variant
predicates for the same underlying object — the bad-prime Hecke ↔ Petersson
adjoint identity:

| Predicate | File:Line | LOC of unfolded ∀-body |
| --------- | --------: | ---------------------: |
| `HasBadPrimeFrickePetNAdjoint` | Adjoint:413 | 4 |
| `HasBadPrimeFrickePerCosetAggregateRes` | Cosets:967 | 13 |
| `HasBadPrimeFrickePerCosetBsumShiftedFD` | Cosets:1035 | 17 |
| `HasBadPrimeFrickePerCosetT152ShiftedFD` | Cosets:1099 | 26 |
| `HasBadPrimeFrickePerCosetSumTransport` | Cosets:1126 | 42 |
| `HasBadPrimePetN_T_p_FrickeAdjoint_BSum` | Reduction:705 | 10 |
| `HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine` | Reduction:796 | 7 |
| `HasBadPrimeAtkinLehnerDoubleCosetTileBridge` | Reduction:879 | 12 |
| `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded` | Reduction:941 | 18 |
| `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified` | Reduction:1188 | 22 |
| `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap` | Reduction:1359 | 22 |
| `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection` | Reduction:1497 | 22 |

Together with 12+ private intermediate `hasBadPrime…_of_…` reduction theorems
(see `Newforms.lean` root file lines 85–104), this is a **12-step linear chain**
between `qBBijection` (the actual residual input shape) and the consumer
`HasBadPrimeFrickePetNAdjoint`.

Each `_qB*` variant is a **rewording of the same identity in increasingly
expanded form** (M_b vs W_N · β_b coordinates, sum vs ∫, with vs without scalar
prefactor, etc.). The pattern matches exactly the `MInfty*`/`TpUpper*` /
`Alpha*` triplication seen in the AdjointTheory subtree audit.

**Canonical form:** A single `HasBadPrimeFrickePetNAdjoint` predicate and a
single `…_of_qBBijection` reduction. The intermediate `_qBExpanded`,
`_qBSimplified`, `_qBDomainSwap` variants are 3-step rewrites that could live as
private lemmas inside the proof of the single reduction. Today each is its own
file-spanning Prop with its own consumer chain.

**LOC saved estimate:** Eliminating 10 of the 12 chain predicates and inlining
their proofs saves roughly **800–1,000 LOC** in BadPrimeReduction alone
(predicates ~200 LOC + 10 forwarding theorems ~600 LOC + the
`T184_dependency_audit_after_T177` style `True := by trivial` declarations).

### 1C. `cuspFormsOld` ↔ `cuspFormsOldExtended` (and `New`/`NewExtended`)

This is the second-largest sprawl driver. Every concept comes in two flavours:

| Classical (Basic.lean) | Extended (LevelRaiseComm.lean / BadPrimeAdjoint.lean) | Difference |
| ---------------------- | ----------------------------------------------------- | ---------- |
| `cuspFormsOld` (Basic:158) | `cuspFormsOldExtended` (LevelRaiseComm:399) | adds trivial-inclusion generators |
| `cuspFormsNew` (Basic:201) | `cuspFormsNewExtended` (LevelRaiseComm:421) | dual orthogonal complement |
| `IsInNewSubspace` (Basic:195) | `IsInNewSubspaceExtended` (BadPrimeAdjoint:820) | dual orthogonality test |
| `Newform` (MainLemma:161) | `NewformExtended` (BadPrimeAdjoint:871) | extended-newspace membership |
| `IsNewform` (MainLemma:172) | `IsNewformExtended` (BadPrimeAdjoint:855) | dual predicate |

Every `Has…PreservesCuspFormsOld` Prop in BadPrimeAdjoint:100, 357 has
an `Extended` twin; each downstream theorem (`heckeT_n_cusp_preserves_*`,
`Newform.frickeBadAdjointCandidate_preserves_*`) appears in both flavours.
`grep -c "Extended"` returns **201 references** in the subtree — close to one
mention per 60 LOC.

**Canonical form:** The `Extended` versions are strictly stronger (proper
inclusion `cuspFormsOld_le_cuspFormsOldExtended`, LevelRaiseComm:404). The whole
chain works at the `Extended` level (it's how Miyake/DS handle the level-raise
proof of `newform_unique`). Restating everything classically is needed only at
the public-API boundary (`Newform.isNew : … ∈ cuspFormsNewExtended` — already
extended-level since 2026-05-28 per project memory). The classical
`cuspFormsOld`/`cuspFormsNew` defs can survive as `abbrev` wrappers, but the
duplicated preservation theorems can collapse 2:1.

**LOC saved estimate:** Roughly 25 paired preservation theorems × 25 LOC each =
**~600 LOC**, plus elimination of the parallel `HasFrickeSlashCuspFormPreservesCuspFormsOld(Extended?)` Prop family.

### 1D. The `Fricke*` slash variants in `Fricke.lean`

Six tightly-related slash operators differ only by the form-class they map:

```
frickeSlashSIF        : SlashInvariantForm  → SlashInvariantForm
frickeSlashSIFLin     : same, as ℂ-linear
frickeSlashModularForm: ModularForm         → ModularForm
frickeSlashCuspForm   : CuspForm            → CuspForm
```

Plus paired `_coe`, `_apply_apply`, `_comp_self`, `_petN_adjoint`,
`_petN_adjoint_of_isFundDomain`, `_petN_adjoint_unconditional` lemmas — yielding
~20 lemmas in `Fricke.lean` lines 657–1100 that say essentially the same thing
at four levels of the form-class hierarchy.

**Canonical form:** Define a `frickeSlash` typeclass-polymorphic operator (or
explicit slash on the unified `SlashInvariantForm` substrate) once, then derive
all four siblings as `MAP` images via the existing `cuspFormToModularFormLin`
linear injection (Basic.lean:217). The `_apply_apply` / `_comp_self`
involutive pair appears for both `CuspForm` and `ModularForm` variants —
proved twice (Fricke:870, 886 / 878, 895).

**LOC saved estimate:** ~250 LOC in Fricke.lean.

### 1E. The `frickeMatrix_*` lemma family (Fricke.lean)

20+ frickeMatrix-related lemmas across lines 439–1342 (frickeMatrix_coe, _det,
_det_pos, _σ, _num, _denom, _smul, _sq_matrix, _mul_self_val, _GLPos, _PSL_R,
_PSL_R_smul, _PSL_R_smul_set, _PSL_R_mul_self, _PSL_R_inv, _PSL_R_mul_*_eq,
_PSL_R_conj_mem_…, _PSL_R_mem_normalizer, etc.).

Many of these are mechanical group-theoretic transports (GL → PSL → SL) that
exist only because there is no unified slash-of-matrix abstraction the
project uses. **Mathlib already has a lot of this** for SL(2,ℤ) — see e.g.
`ModularGroup.S`, `Matrix.GeneralLinearGroup.coe_mul` — these could replace
~10 of the lemmas.

**LOC saved estimate:** Conservatively ~150 LOC of mathlib re-derivation.

---

## 2. Hypothesis sprawl

The same hypothesis tuples appear over and over in headline signatures:

### Tuple A — bad-prime context: `(p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)`

Appears in **31 theorem signatures** across BadPrime{Adjoint,Cosets,Reduction}. 4
hypotheses on every line.

### Tuple B — cusp-form pair: `(f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)`

**42 signatures**. 90+ char per line.

### Tuple C — newform + character + membership: `(f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)`

**46 signatures**. 3 lines per occurrence on average.

### Tuple D — coefficient-vanishing: `(S : Finset ℕ) (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N), q ∉ S → f.lCoeff q = 0)`

**44 signatures**.

### Tuple E — character non-triviality: `(h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1) (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)`

**46 signatures** — and the `Newform.dirichletLift χ * Newform.dirichletLift χ`
sub-expression appears **176 times** in the subtree.

### Tuple F — quantified-input tuples in 32 SMO consumers
```
(h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
  f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ → ∀ (S : Finset ℕ), …)
```

The quantified prefix `∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄` plus inner Newform+χ+hfχ+S
appears **20 times** as `h_data` and another ~10 times for the other inputs
(`h_FE`, `h_mellin`, `h_slash`, `h_hecke`, `h_fricke`…).

### Bundles already in scope (lightly used)

* `Newform.HeckeFEData` (Fricke:129) — bundles 2 of Tuple F's quantified clauses
* `Newform.MellinPairData` (Fricke:181) — bundles 10 analytic fields
* `Newform.FrickeSlashData` (MellinBridges:778) — bundles 4 Fricke fields
* `Newform.PerNewformFullDirichletData` (MellinBridges:46) — bundles 8 Dirichlet fields
* `Newform.CompletedFrickeData` (MellinBridges:1296) — bundles 9 final-assembly fields

### Proposed new bundles (used 5+ times each)

1. **`BadPrimeContext`** *(Tuple A)*: `(p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)` — reduces 31 signatures by 3 lines each.

2. **`NewformInChar`** *(Tuple C)*: a structure or `variable` bundle for `(f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) (hfχ : f ∈ modFormCharSpace k χ)`. The `variable` form is preferable since `f.toCuspForm.toModularForm' ∈ …` is a Prop and Lean already supports auto-binding via `variable` in sections.

3. **`HasBadCoefficientVanishing`** *(Tuple D)*: rename or bundle the 44-occurrence h_bad hypothesis.

4. **`ChiNonTrivialPair`** *(Tuple E)*: a `Prop` bundling the χ ≠ 1 and χ² ≠ 1 hypotheses; introduce a `DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ) z` shortcut (e.g., `Newform.L_chi_sq χ z`) to collapse 176 verbose copies.

5. **`HeckeAndDirichletInputs`** *(Tuple F outer prefix)*: a `section`/`variable` block (or one structure for the global SMO drivers).

LOC impact of these bundles: conservatively **~700 LOC** of signature reduction.

---

## 3. Redundant structures

**12 structures total** in the subtree (counting `Eigenform`, `Newform`,
`NewformExtended` only once each). Field-count breakdown:

| Structure | File:Line | Fields | Verdict |
| --------- | --------: | -----: | ------- |
| `Eigenform` | Basic:49 | 5 | Core. Keep. |
| `Newform` | MainLemma:161 | (extends Eigenform) + 2 | Core. Keep. |
| `IsNewform` | MainLemma:172 | 3 (Prop fields) | Redundant with `Newform.isNewform`. **Subsumed.** |
| `NewformExtended` | BadPrimeAdjoint:871 | (extends Eigenform) + 2 | Pure renaming of `Newform`; differs only in `isNew : … ∈ cuspFormsNewExtended` instead of `cuspFormsNew`. **As of 2026-05-28 (per project memory) `Newform.isNew` was rebound to `cuspFormsNewExtended` — so NewformExtended IS Newform, but the duplicate structure is still around. Mark for deletion.** |
| `IsNewformExtended` | BadPrimeAdjoint:855 | 3 | **Subsumed** by `IsNewform` after Newform.isNew rebinding. |
| `HeckeFEData` | Fricke:129 | 2 | Keep — minimal. |
| `MellinPairData` | Fricke:181 | 10 | Keep, but most fields auto-discharge via `MellinPairData.ofImAxis` (Fricke:244). Consider promoting `ImAxisMellinData` to canonical. |
| `ImAxisMellinData` | Fricke:276 | 8 | Keep. **The canonical bundle.** |
| `FrickeTwistData` | FrickeTwist:70 | 6 | Pure 6-field re-bundling of MellinPairData with `Newform.imAxis f` and `_root_.ModularForms.imAxis twist` baked in. **Subsumed** by `FrickeSlashData` (a cleaner 4-field version) — both exist! |
| `FrickeSlashData` | MellinBridges:778 | 4 | Keep — the canonical bundle. |
| `CompletedMellinData` | MellinBridges:1211 | 5 | Subsumed by `CompletedFrickeData`. |
| `CompletedFrickeData` | MellinBridges:1296 | 6 | Keep — the final-assembly bundle. |
| `PerNewformFullDirichletData` | MellinBridges:46 | 8 | Keep — the canonical Dirichlet-side bundle. |
| `EulerStrippingArithmeticInput` | MellinBridges:1502 | 5 | Used once (`hasEulerStrippingMultiplier_of_arithmeticInput`). Possibly subsumed. |
| `HasHeckeMultiplicativeStructure` | MellinBridges:1544 | 3 | Used once. Possibly subsumed. |
| `IsHeckeCoefficientSequence` | CoeffSeq:148 | 4 | Keep — used by external `Eigenforms/ConductorTheorem`. |

**Redundancy verdicts:**
- 5 structures are pure renamings / superseded (`IsNewform`, `NewformExtended`,
  `IsNewformExtended`, `FrickeTwistData`, `CompletedMellinData`).
- 2 are mid-level intermediates (`MellinPairData`, `CompletedMellinData`) where
  the more general form is the only one consumed.

**LOC saved estimate:** ~200 LOC for the redundant structures and their projection/conversion lemmas (each structure averages a 30-LOC declaration plus 10–20 LOC of `ext`/`of*` accessors).

---

## 4. Duplicate proof bodies

### 4A. `Submodule.span_induction` block (~25 LOC, appears 3× verbatim)

`hasFrickeSlashCuspFormPreservesCuspFormsOld_iff_on_generators` (BadPrimeAdjoint:130-148), `frickeSlashCuspForm_preserves_cuspFormsOldExtended_iff_on_generators` (BadPrimeAdjoint:160-180), `cuspFormsOld_coeff_eq_zero_of_coprime` (MainLemma:308-341). Each does the same induction:
```
refine Submodule.span_induction (p := …) ?_ ?_ ?_ ?_ hf
· … (generator case)
· rw [map_zero]; exact zero_mem ...    -- zero
· intro x y _ _ ihx ihy; rw [map_add]; exact add_mem ihx ihy   -- add
· intro c x _ ihx; rw [map_smul]; exact smul_mem c ihx          -- smul
```
**Could be a one-line `Submodule.span_induction'` wrapper.**

### 4B. Per-`q` AE-disjointness + null-measurability + integrability triple (BadPrimeReduction.lean)

Lines 124-307 (~180 LOC) prove three structurally identical theorems
(`aedisjoint_pairwise_T_p_upper_smul_qOut_inv_fd`,
`nullMeasurableSet_T_p_upper_smul_qOut_inv_fd`,
`peterssonInner_iUnion_T_p_upper_smul_qOut_inv_fd_eq_sum`), then **lines 240-345
repeat the same three theorems with `T_p_upper` replaced by `fricke_T_p_upper`**
(`aedisjoint_pairwise_fricke_T_p_upper_smul_qOut_inv_fd`,
`nullMeasurableSet_fricke_T_p_upper_smul_qOut_inv_fd`,
`peterssonInner_iUnion_fricke_T_p_upper_smul_qOut_inv_fd_eq_sum`).

These are **near-verbatim duplicates with the Fricke matrix conjugation
inserted** — could be a single `α : GL (Fin 2) ℝ`-parameterised triple plus two
instantiations. **LOC saved: ~150.**

### 4C. The `(q,b)`-aggregate reindex skeleton (BadPrimeReduction.lean)

Three theorems (`aggregate_q_b_shifted_eq_inv_c_petN_T_p_f_g` at 49-77,
`aggregate_q_b_W_N_β_b_shifted_eq_inv_c_petN_T_p_f_g` at 95-119,
`aggregate_q_b_collapsed_W_N_qOut_inv_fd_eq_inv_c_petN_T_p_f_g` at 406-435,
`aggregate_q_b_collapsed_W_N_qOut_inv_fd_eq_inv_c_petN_T_p_f_g_unconditional`
at 574-…) all do the same `Finset.sum_congr rfl fun q _ ↦ …` reindex of the
double sum. **LOC saved: ~120.**

### 4D. `hasBadPrimeFrickePetNAdjoint_of_intertwine` /
`hasBadPrimePetN_T_p_FrickeAdjoint_BSum_of_intertwine` /
`hasBadPrimePetN_T_p_FrickeAdjoint_Intertwine_of_doubleCosetTileBridge`
(BadPrimeReduction:809, 840, 897)

Each is a ~30-LOC `Finset.sum_congr` shuffle that recomposes the same `Σ_q Σ_b
peterssonInner k fd …` aggregate into different RHS forms. The body of each is
roughly:
```
intro f g
show … = …
rw [show petN … = Σ_q peterssonInner k fd … from rfl]
have h_lhs_q : ∀ q, peterssonInner … = Σ_b peterssonInner …
  intro q
  rw [Newform.peterssonInner_heckeT_n_cusp_at_divN_slash_qOut_inv_eq_bsum hp hpN f g q, SlashAction.sum_slash]
  ...
rw [Finset.sum_congr rfl fun q _ ↦ h_lhs_q q]
exact …
```
The `have h_int` block is identical across three theorems (lines 747-755,
859-867, 925-935). **LOC saved: ~100** via a shared helper.

### 4E. The mainLemma_of_… / strongMultiplicityOne_of_… consumer chain

In FrickeTwist.lean (lines 460-610) and MellinBridges.lean (lines 388-870):
each theorem is a near-trivial 5-15 line forwarder of the form `consumer_X
upstream_input` →  `consumer_Y (upstream_input.toHigherLevel) downstream_input`.
There are roughly 20 such forwarders that are functionally just type
isomorphisms. **LOC saved: ~300** via a shared structure-conversion machinery (or
by deleting the redundant `_of_X_of_Y_of_…` consumers in favour of canonical 3
endpoints).

### 4F. Three `T*_dependency_audit*` `True := by trivial` declarations

(`T179_dependency_audit_after_T177` BadPrimeAdjoint:1017,
`T180_dependency_audit_after_T179` BadPrimeAdjoint:1184,
`T184_qBDomainSwap_equivalent_to_petN_adjoint_audit` BadPrimeReduction:1383)

Each is a 6–15-line `let _ := @Foo` block that exists purely to provide a "this
identifier is reachable" check. These should be replaced by `#check` commands
(or deleted; the lake build already validates reachability). **LOC saved: ~40.**

---

## 5. Cross-file redundancy

### 5A. Identical Hecke-operator-on-cusp-forms machinery

`heckeT_n_cusp_add` / `heckeT_n_cusp_smul` / `heckeT_n_cusp_zero` (Basic:451,
462, 472) are mirrored by `diamondOp_cusp_add` / `_smul` / `_zero` (Basic:482,
486, 491). The `heckeT_n_cusp_lin` linearised version exists separately in
`BadPrimeAdjoint.lean:46` despite the `_add`/`_smul` lemmas being in Basic.
**Move `heckeT_n_cusp_lin` to Basic.lean alongside the three lemmas it
linearises** (saves an import).

### 5B. `mainLemma` consumer duplication in root file

`Newforms.lean` lines 540-586 (`strongMultiplicityOne_of_analyticContradiction_of_newSubspaceZeroCriterion`)
duplicates large portions of `Fricke.lean:74-115`
(`strongMultiplicityOne_of_analyticContradiction`). The two differ only in
which side of the Atkin-Lehner chain they use as the upstream input.

### 5C. `shiftSL` and its `_mem_Gamma1` lemma (LevelRaiseComm:45, 49)

Look like they should be in the upstream `LevelRaise.lean` (where the rest of
the shift matrix infrastructure lives). Cf. `mapGL`, `glMap` in
`Unified/NebentypusHeckeRingHom`.

### 5D. `BadPrimeReduction.lean` reprises `peterssonInner_*` from `BadPrimeCosets.lean`

`peterssonInner_iUnion_T_p_upper_smul_qOut_inv_fd_eq_sum` (BadPrimeReduction:209) and
`peterssonInner_iUnion_fricke_T_p_upper_smul_qOut_inv_fd_eq_sum` (BadPrimeReduction:307)
re-prove `peterssonInner` ↔ `Σ_b peterssonInner` reductions that are also done
inside `BadPrimeCosets.lean:774-816`
(`peterssonInner_alpha_p_doubleCoset_smul_*`). The two share the same
double-coset partition (Cosets:417, 463) but never merge.

### 5E. Twist file pair (FrickeTwist / Fricke)

Per task brief: Fricke/FrickeTwist. `FrickeTwist.lean` is **not** the
"single character vs twist" pair — it's actually the layer between
`FrickeData`-class structures and the Dirichlet-quotient chain. The two share
the `Newform.imAxis_*` / `Newform.frickeSlash*` infrastructure (Fricke:225-240,
657-995), but never directly cohabit lemmas.

The genuine duplication between them is structural: **`Newform.FrickeTwistData`
(FrickeTwist:70) is subsumed by `Newform.FrickeSlashData` (MellinBridges:778)**
plus the bridge constructor `Newform.ImAxisMellinData.ofFrickeTwistData`
(FrickeTwist:93) is a 5-line shadow of `Newform.ImAxisMellinData.ofSlashEq`
(FrickeTwist:120). Pick one.

---

## 6. Mathlib-redo

Spot-check candidates that look like generic abstractions on mathlib types:

| Project lemma | File:Line | Mathlib candidate / status |
| ------------- | --------: | -------------------------- |
| `cuspFormToModularFormLin` + `_injective` | Basic:217, 225 | This is the obvious `CuspForm.toModularForm` linear map — likely already exists in mathlib as `CuspForm.toModularForm'` (referenced widely in this file). The `cuspFormToModularFormLin` is built solely to invoke `FiniteDimensional.of_injective`. **Could be a one-liner via `LinearMap.mk` on the existing `toModularForm'`.** |
| `cuspForm_finiteDimensional` | Basic:234 | The argument `CuspForm ≤ ModularForm ∧ ModularForm is finite-dim` is generic; this proof transports finite-dimensionality through a linear injection. Mathlib's `FiniteDimensional.of_injective` is the engine. Likely a direct corollary if `CuspForm` has an explicit linear map to `ModularForm`. **One-liner.** |
| `petN_realBilin` (Basic:243) and its `_isRefl`, `_orthogonal_*_eq` | Basic:243-304 | Real-part bilinear form on a complex inner-product space — this exists in mathlib as `InnerProductSpace.Core.toRealInnerProductSpace` machinery (`re_inner_eq_re_inner`, `IsRefl`, etc.). The 60 LOC of project code could be ~10 LOC of `noncomputable instance + import`. |
| `levelRaiseMatrix_inv_smul_vadd_one_eq` (Newforms.lean root:458) | root:458-466 | Pure 8-LOC matrix shuffle — generic enough that it should be either in upstream `LevelRaise.lean` or composable from `Matrix.smul_apply` + `UpperHalfPlane.coe_vadd`. |
| `exp_two_pi_mul_I_div_natCast_pow_eq_one` (root:468) | root:468-472 | Probably exists as `Complex.exp_two_pi_mul_I.pow_root_of_unity` or similar — needs a `lean_loogle` search. |
| `Newform.lCoeff_zero` / `_one` | CoeffSeq:100, 112 | Pure `qExpansion_coeff_zero` / `isNorm` unfolding — could be `simp` lemmas tagged `@[simp]` (already are) but the proofs themselves are 5 LOC of inlined `h1_period_Gamma1_local` plumbing. |
| `IsHeckeCoefficientSequence.coeff_prime_pow_*_eq_of_a_p_zero` (CoeffSeq:168-218) | CoeffSeq:168-218 | These three theorems (odd-power vanishing, even-power closed form, combined) are abstract recurrence solving. Mathlib has `Polynomial.recurOn` / `LinearRecurrence` but the project unfolds it manually. Could be a generic `LinearRecurrence` instance with `a₀ = 1, a₁ = 0` plus characteristic polynomial. |
| `Submodule.span_induction` triple proofs (4A above) | various | `Submodule.span_induction'` already takes a 4-tuple; this is a closure-finding pattern that doesn't need extra lemmas. Just inline. |
| `Newform.frickeMatrix_PSL_R_*` lemmas (Fricke:1099-1325) | Fricke:1099-1325 | The 20+ PSL/GLPos transports of frickeMatrix; some have direct mathlib analogues for `ModularGroup.S` and `ModularGroup.T`. Specifically `frickeMatrix_PSL_R_mul_self`, `frickeMatrix_PSL_R_inv`, `frickeMatrix_PSL_R_mem_normalizer` are generic group-theory facts about elements of order 2 in `PSL(2,ℝ)`. |

**Verdict for mathlib upstream PR opportunities:**
- `petN_realBilin` machinery → potential PR to mathlib (real-bilinear-form-of-Hermitian-inner-product).
- `IsHeckeCoefficientSequence` recurrence-closed-form theorems → if generalised, potential mathlib PR.

---

## 7. The Bloat Diagnosis (≤500 words)

Ranked by LOC impact:

**(a) Hypothesis re-inlining in headline signatures — ~2,000 LOC.** The
~55-LOC inline `∃-clause` that defines `full_dirichletZeroCertificate` shape
appears verbatim in **24** theorem signatures across FrickeTwist (12),
MellinBridges (8), and the root `Newforms.lean` (4). Each occurrence is the
exact same nested `AnalyticAt + ≠ 0 + = 0 + meromorphicOrderAt ≠ ⊤ + clause`
structure — the bundled `PerNewformFullDirichletData` (MellinBridges:46) already
captures this exactly, and the conversion theorem
`full_pole_witness_data_of_PerNewformFullDirichletData` (MellinBridges:100)
already exists. The 24 signatures should refuse to accept the unfolded shape.

**(b) The 6×6 `Hecke-input × Dirichlet-input` consumer matrix — ~700 LOC.**
There are 19 distinct `strongMultiplicityOne_of_*` variants, 6+ each of
`HeckeEntireExtension_of_*` and `analyticContradiction_of_*`. Most are 5-15
line forwarders that compose two `ofX` constructors. Replacing this with 3
canonical SMO endpoints + the existing `ofX` constructors collapses the matrix.

**(c) Three-file bad-prime variant chain — ~1,000 LOC.** BadPrime{Adjoint,
Cosets, Reduction} hosts a 12-step linear reduction `qBBijection → … →
HasBadPrimeFrickePetNAdjoint`. Each step has its own `def Has…` predicate
(7+ variants) plus a `theorem hasFoo_of_hasBar` reducer. Most intermediate
predicates are one-step rewrites and could be inlined.

**(d) Extended-vs-classical doubling — ~600 LOC.** `cuspFormsOld(Extended)`,
`Newform(Extended)`, `IsNewform(Extended)`, and ~15 paired preservation theorems
exist in both flavours. The project memory note from 2026-05-28 indicates the
canonical bind is `cuspFormsNewExtended`. The classical names can survive as
abbreviations.

**(e) Sibling proof bodies — ~400 LOC.** The `(q,b)`-aggregate reindex (4C),
the AE-disjoint/null-measurable/integrable triple repeated for T_p_upper and
fricke·T_p_upper (4B), and the `Submodule.span_induction` triple (4A) each
have multiple near-verbatim copies.

**(f) Mathlib-restatement — ~250 LOC.** `cuspForm_finiteDimensional` (5 LOC of
inlined linear-map → 1-line use of FiniteDimensional.of_injective),
`petN_realBilin` machinery (60 LOC, ~10 if going through mathlib's
real-bilinear-form-of-Hermitian-inner-product), and various matrix shuffles
that could be `lean_loogle`-findable.

**Total reduction potential:** ~2,000 + 700 + 1,000 + 600 + 400 + 250 = **~4,950
LOC**, taking the 12,599 LOC subtree to **~7,600** — a **1.65× reduction**. To
hit the 4-5× target the project should also reconsider the 12-step bad-prime
chain (perhaps replacing 7 intermediate Props with `lemma`s in a single proof)
and aggressively use mathlib-side helpers for the `petN_realBilin` and
`IsHeckeCoefficientSequence` recurrence machinery.

---

## 8. The Reduction Plan

Each ticket is independent unless noted; risk is rated for cascade into the 4
protected headlines (`heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`,
`strongMultiplicityOne_constMul`, `strongMultiplicityOne_axiom_clean`).

### Ticket N1: Adopt `PerNewformFullDirichletData` in all public signatures
**Files:** Newforms.lean root, FrickeTwist.lean, MellinBridges.lean
**LOC saved:** ~1,300
**Risk:** LOW — bundling existing data into already-existing struct. Internal forwarders only.
**Deps:** none.
Replace 24 occurrences of the 55-LOC inline `∃-clause` with
`(h_data : ∀ f χ S, … → Newform.PerNewformFullDirichletData f χ S)`. All call
sites already construct the bundle via `PerNewformFullDirichletData_*_of_classicalInputs`.

### Ticket N2: Canonicalise to 3 SMO endpoints
**Files:** FrickeTwist.lean, MellinBridges.lean, Newforms.lean
**LOC saved:** ~400
**Risk:** MEDIUM — public API change. The 4 protected headlines use a specific endpoint chain (verify before deletion).
**Deps:** N1.
Delete 16 of the 19 `strongMultiplicityOne_of_*` variants; keep only:
`strongMultiplicityOne_of_HeckeFEData_of_PerNewformFullDirichletData_of_newformUnique`
(or its closest direct equivalent), plus its `analyticContradiction` and
`existsNonzeroPrimeEigenvalue` siblings. Callers compose `ofX` constructors.

### Ticket N3: Collapse bad-prime chain to single `qBBijection ↔ HasBadPrime…Adjoint`
**Files:** BadPrimeReduction.lean
**LOC saved:** ~800-1,000
**Risk:** MEDIUM — internal chain; uses extensive `Newforms.lean` root forwarders.
**Deps:** none.
Replace 10 of the 12 `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qB*` Props
with private lemmas inside the proof of a single bridging theorem
`HasBadPrimeFrickePetNAdjoint ↔ HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection`.

### Ticket N4: Delete `NewformExtended`, `IsNewformExtended`, `IsNewform`
**Files:** BadPrimeAdjoint.lean, MainLemma.lean, Basic.lean
**LOC saved:** ~150
**Risk:** HIGH — `Newform.isNew` was rebound to `cuspFormsNewExtended` in
2026-05-28 (per project memory), so `NewformExtended ≡ Newform` definitionally,
but check downstream `*_constMul` / `*_axiom_clean` for direct uses of
`NewformExtended`. If used, deprecate via `abbrev`.
**Deps:** none.

### Ticket N5: Delete `FrickeTwistData`, prefer `FrickeSlashData`
**Files:** FrickeTwist.lean, MellinBridges.lean
**LOC saved:** ~120
**Risk:** LOW — both bundles construct the same `ImAxisMellinData`; only the
`ImAxisMellinData.ofFrickeTwistData` (FrickeTwist:93) constructor is used.
**Deps:** none.

### Ticket N6: Unify the 4× `frickeSlash{SIF,SIFLin,ModularForm,CuspForm}` variants
**Files:** Fricke.lean
**LOC saved:** ~250
**Risk:** MEDIUM — `Newform.frickeSlashCuspForm` is heavily used downstream
(35+ refs in BadPrime*). Introduce a unified `frickeSlash` polymorphic via the
existing `cuspFormToModularFormLin` injection.
**Deps:** none.

### Ticket N7: Generic `α : GL (Fin 2) ℝ`-parameterised AE-disjoint/null-meas/integrable triple
**Files:** BadPrimeReduction.lean (lines 124-345)
**LOC saved:** ~150
**Risk:** LOW — purely refactor of three proofs; no headline impact.
**Deps:** none. Parallel to N3.

### Ticket N8: Submodule-span-induction wrapper / mathlib `span_induction'` usage
**Files:** BadPrimeAdjoint.lean (130-180), MainLemma.lean (308-341)
**LOC saved:** ~70
**Risk:** LOW.
**Deps:** none.

### Ticket N9: Replace `petN_realBilin` machinery with mathlib's `InnerProductSpace.Core` helpers
**Files:** Basic.lean (lines 240-330)
**LOC saved:** ~50–60
**Risk:** LOW — internal lemma chain only used to prove
`cuspFormsOld_isCompl_cuspFormsNew`.
**Deps:** none.

### Ticket N10: Move `shiftSL` and `levelRaise*` matrix shuffle lemmas to upstream `LevelRaise.lean`
**Files:** LevelRaiseComm.lean → LevelRaise.lean, Newforms.lean root
**LOC saved:** ~80
**Risk:** LOW — modular relocation.
**Deps:** none.

### Ticket N11: Delete `T*_dependency_audit_after_*` `True := by trivial` declarations
**Files:** BadPrimeAdjoint.lean (1017, 1184), BadPrimeReduction.lean (1383)
**LOC saved:** ~40
**Risk:** ZERO — these are status assertions, not load-bearing.
**Deps:** none.

### Ticket N12: Inline / delete the 5 `_of_FrickeSlashData_of_classicalInputs_T111` consumers
**Files:** MellinBridges.lean (lines 550-870)
**LOC saved:** ~250
**Risk:** LOW after N1/N2.
**Deps:** N1, N2.

### Ticket N13: Introduce `BadPrimeContext` / `NewformInChar` / `ChiNonTrivialPair` `variable` bundles
**Files:** all
**LOC saved:** ~400
**Risk:** LOW — purely sigil-level change inside `section`s.
**Deps:** none.

### Ticket N14: Replace `(q,b)`-aggregate reindex skeleton with shared helper
**Files:** BadPrimeReduction.lean (lines 49-77, 95-119, 406-435, 574-…)
**LOC saved:** ~120
**Risk:** LOW.
**Deps:** N7 (compatible).

### Ticket N15: Hot patch — Move `heckeT_n_cusp_lin` definition to `Basic.lean`
**Files:** BadPrimeAdjoint.lean → Basic.lean
**LOC saved:** ~20
**Risk:** ZERO.
**Deps:** none.

---

### Aggregate
- Tickets N1+N2+N12 alone yield **~1,950 LOC** of pure bundling (zero math change).
- Tickets N3+N4+N5+N6 yield **~1,250 LOC** by collapsing 4 sibling families.
- Tickets N7+N8+N14 yield **~340 LOC** by deduplicating proof skeletons.
- N9+N10+N15 yield **~150 LOC** of housekeeping.
- N11 yields **~40 LOC** of pure noise removal.
- N13 yields **~400 LOC** of signature cleanup.

**Total ~4,130 LOC** from the cataloged tickets, taking the subtree from 12,599
to **~8,400** (**~1.5×** reduction). To hit the 4-5× target, the project would
additionally need to: (i) replace the 6×6 Hecke-FE-input matrix with a single
`HeckeFEData`-only public API, (ii) collapse the BadPrime trio into one file
(combining the merger of N3 with topical splits), and (iii) factor `petN`
adjoint properties through a generic mathlib bilinear-form framework. These are
each large efforts (200-500 LOC each more) that depend on architectural
acceptance of the bundling principle in N1.

### Sequencing
- **Wave 1** (low-risk bundling, blocks nothing): N1, N5, N10, N11, N13, N15.
- **Wave 2** (depends on Wave 1): N2, N12.
- **Wave 3** (refactors, can run in parallel): N3, N6, N7, N8, N9, N14.
- **Wave 4** (verified-only after Wave 1-3): N4 (requires audit of headline dependencies).
