# Ticket Board: Miyake Theorem 4.6.12 (Strong Multiplicity One, full constant-multiple form)

*`/develop` Phase 1g, 2026-05-26, branch `hecke-ring`. Supersedes the prior `tickets.md`
(backed up to `tickets-PRE-4612-backup-2026-05-26.md`). All work lands in the new file
`LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean` (skeleton already written,
elaborates with `lake env lean`). Plan: `.mathlib-quality/plan.md`. Decomposition + verbatim
source quotes + per-leaf adversarial logs: `.mathlib-quality/decomposition.md`.*

## Summary

- Total: 19 tickets — 13 proof/def, 6 cleanup.
- Open: 19 | In Progress: 0 | Done: 0.
- Parallel capacity at peak: ~4 (T001, T003, T011 independent; T005 independent of those).
- **RISKIEST: T012** (decomposition codisjointness for the χ-refined old space — gap #4
  structural form; side-steppable via Mitigation B in T013).
- Never modify `strongMultiplicityOne_axiom_clean` or `miyake_4_6_14_delta_slash_sum_coeff_zero`.
- Never use `native_decide` / `sorry`-as-answer / custom `axiom` / `set_option maxHeartbeats`.

## Dependency order (proof/def tickets)

```
T001 ─┬─ T002 ─┬─ T004 ── (→ T013)
      │        └─ T010 ── (→ T013)
T003 ─┘  T005 ─┬─ T006 ─┐
T011 ────┐     ├─ T007  ├─→ T010
         │     ├─ T008 ─┤
         └─────┴─ T009 ─┘
                              T012 (RISK; optional via Mitigation B)
                              T013 (milestone)
```

---

### [T001] Lemma 4.5.15(1), un-normalised: `Eigenform.coeff_eq_coeff_one_mul_eigenvalue`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: none
- **Parallel**: yes (with T003, T005, T011)
- **Type**: lemma (BUILD — assembly)

#### Statement
```lean
theorem Eigenform.coeff_eq_coeff_one_mul_eigenvalue
    (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (n : ℕ+) (hn : Nat.Coprime n.val N) :
    (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff n.val =
      (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 * g.eigenvalue n := by
  sorry
```

#### Proof sketch (Miyake §4.5 Lemma 4.5.15(1), p. 149: `aₙ = a₁ λₙ`)
1. `haveI : NeZero n.val := ⟨n.pos.ne'⟩`.
2. From `Eigenform.isEigen g n hn`: `heckeT_n_cusp k n.val g.toCuspForm = g.eigenvalue n • g.toCuspForm`.
   Take period-1 q-expansion coeff at 1 of both sides; RHS via
   `qExpansion_one_coeff_one_smul_of_norm`-style (`coeff 1 (c • g) = c * coeff 1 g`) gives
   `a₁(Tₙ g) = (g.eigenvalue n) * a₁(g)`. (Model: `qExpansion_one_coeff_one_smul_of_norm`,
   `MainLemma.lean:221`, but without `a₁=1`; use `qExpansion_smul` + `PowerSeries.coeff_smul`.)
3. Apply `fourierCoeff_heckeT_n_period_one k n.val hn χ hgχ 1`: the gcd-sum over
   `(Nat.gcd 1 n.val).divisors = {1}` collapses (model the simp block in
   `Newform.eigenvalue_eq_coeff`, `MainLemma.lean:243-249`) to `a₁(Tₙ g) = aₙ(g)`.
4. Combine 2+3: `aₙ(g) = a₁(g) * g.eigenvalue n`. Bridging: `mul_comm` to match orientation.

Off-script bridging: the `f.toCuspForm` vs `f.toCuspForm.toModularForm'` coercion juggling
(`show … from rfl` rewrites, as in `MainLemma.lean:264-267`).

#### Mathlib/project lemmas needed
- `Eigenform.isEigen` (`Newforms/Basic.lean:76`) — `Tₙ g = (eigenvalue n) • g` (verified sorry-free).
- `fourierCoeff_heckeT_n_period_one` (`FourierHecke.lean:864`) — building block (verified sorry-free).
- `qExpansion_smul`, `PowerSeries.coeff_smul` (mathlib).
- Pattern model: `eigenvalue_eq_fourierCoeff_one` (`FourierHecke.lean:912`),
  `Newform.eigenvalue_eq_coeff` (`MainLemma.lean:256`).

#### Sources
- [Miy] §4.5 Lemma 4.5.15(1), p. 149. (Verbatim quote in `decomposition.md` L1.)

#### Generality decision
- `Eigenform N k` (un-normalised), χ as `(ZMod N)ˣ →* ℂˣ`, `n : ℕ+`, `(n,N)=1`.
  No `a₁=1` assumption (that is the `Newform` specialisation already in the project).

---

### [T003] Lemma 4.6.2 (eigenvalue corollary): `heckeT_n_levelRaise_eigen`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: none
- **Parallel**: yes (with T001, T005, T011)
- **Type**: lemma (BUILD — corollary of existing commutation)

#### Statement
```lean
theorem heckeT_n_levelRaise_eigen
    {M : ℕ} [NeZero M] {l : ℕ} [NeZero l] (heq : l * M = N)
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (lam : ℂ)
    (h_eig : haveI : NeZero n := ⟨(NeZero.ne n)⟩
      heckeT_n_cusp k n h = lam • h) :
    heckeT_n_cusp k n (heq ▸ levelRaise M l k h) = lam • (heq ▸ levelRaise M l k h) := by
  sorry
```

#### Proof sketch (Miyake §4.6 Lemma 4.6.2, p. 157)
1. `subst heq` (eliminate the transport).
2. `rw [heckeT_n_levelRaise_comm n hn M l rfl h]` ⟹ goal `levelRaise M l k (Tₙ h) = lam • levelRaise M l k h`.
3. `rw [h_eig, map_smul]` (levelRaise is `→ₗ[ℂ]`) ⟹ `lam • levelRaise … h = lam • levelRaise … h`, `rfl`.

#### Mathlib/project lemmas needed
- `heckeT_n_levelRaise_comm` (`Newforms/LevelRaiseComm.lean:883`) — verified sorry-free.
- `LinearMap.map_smul` / `map_smul` (mathlib; `levelRaise` is a `→ₗ[ℂ]`, `LevelRaise.lean:231`).

#### Sources
- [Miy] §4.6 Lemma 4.6.2, p. 157. (Verbatim quote in `decomposition.md` L3.)

#### Generality decision
- General `M, l` with `l*M = N`, `(n,N)=1`, arbitrary scalar `lam`. No eigenform structure
  needed — stated for a bare cusp form with an eigen-equation.

---

### [T011] Public orthogonality: `petN_eq_zero_of_ne_eigenvalues`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
  (+ 1-line edit to `LeanModularForms/HeckeRIngs/GL2/AdjointTheoryPetersson.lean`)
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma (BUILD — public wrapper / de-privatise)

#### Statement
```lean
theorem petN_eq_zero_of_ne_eigenvalues
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ cuspFormCharSpace k χ) (hg_char : g ∈ cuspFormCharSpace k χ)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {n : ℕ} [NeZero n] (hn : Nat.Coprime n N) {a b : ℂ}
    (hf_eig : heckeT_n_cusp k n f = a • f)
    (hg_eig : heckeT_n_cusp k n g = b • g)
    (h_diff_ab : a ≠ b) :
    petN f g = 0 := by
  sorry
```

#### Proof sketch (Miyake p. 164, "distinct eigenvalues ⟹ linearly independent")
- The target is **definitionally** the existing private lemma
  `eigenforms_orthogonal_of_ne_eigenvalues` (`AdjointTheoryPetersson.lean:810`, sorry-free,
  same signature). Two options:
  1. **(recommended)** Drop the `private` modifier on `AdjointTheoryPetersson.lean:810`
     (1-line change, no logic touched), then `exact eigenforms_orthogonal_of_ne_eigenvalues
     χ hf_char hg_char hf_ne hg_ne hn hf_eig hg_eig h_diff_ab`.
  2. If de-privatising is undesirable, re-prove via the public `heckeT_n_adjoint_on_charSpace`
     + `petN_conj_smul_left'` + `petN_smul_right` + `petN_definite` (copy the 8-line body).

#### Mathlib/project lemmas needed
- `eigenforms_orthogonal_of_ne_eigenvalues` (`AdjointTheoryPetersson.lean:810`, private,
  sorry-free) OR its ingredients `heckeT_n_adjoint_on_charSpace`, `petN_definite`.

#### Sources
- [Miy] p. 164. (Verbatim in `decomposition.md` L_indep.)

#### Generality decision
- Stated identically to the private original; public so the new file (downstream) can use it.

---

### [T002] Lemma 4.6.11: `coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T001
- **Parallel**: no (needs T001)
- **Type**: lemma (BUILD — assembly)

#### Statement
```lean
theorem coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen
    (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hg_new : g.toCuspForm ∈ cuspFormsNew N k)
    (hg_ne : g.toCuspForm ≠ 0)
    (L : ℕ) (hNL : N ∣ L)
    (h_chi_factor : …) :   -- as in skeleton (route-B character-conductor restriction)
    (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 ≠ 0 := by
  sorry
```

#### Proof sketch (Miyake §4.6 Lemma 4.6.11, p. 163)
1. By contradiction: assume `a₁(g) = 0`.
2. For every `(n,N)=1`: by **T001** (`coeff_eq_coeff_one_mul_eigenvalue`),
   `aₙ(g) = a₁(g) * λₙ = 0`. (Don't even need `N ∣ L`; coprime-to-N suffices since route-B
   4.6.8 wants vanishing on coprime-to-N. `hNL`/`L` retained to mirror Miyake's "(n,L)=1".)
3. Bridge `hgχ` (modFormCharSpace) to `cuspFormCharSpace` via
   `cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace` (used in
   `newform_unique_routeB`, `SMOObligations.lean:301`).
4. Apply `mainLemma_charSpace_routeB χ g.toCuspForm (cuspFormCharSpace mem) h_vanish h_chi_factor`
   ⟹ `g.toCuspForm ∈ cuspFormsOld N k`.
5. `Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _ (old) (new) = 0` (or
   `hg_new g.toCuspForm (old) = petN g g = 0` then `petN_definite`) ⟹ `g.toCuspForm = 0`,
   contradicting `hg_ne`.

#### Mathlib/project lemmas needed
- `Eigenform.coeff_eq_coeff_one_mul_eigenvalue` (T001).
- `mainLemma_charSpace_routeB` (`SMOObligations.lean:232`, verified sorry-free).
- `cuspFormsOld_disjoint_cuspFormsNew` (`Newforms/Basic.lean:196`), `petN_definite`.
- `cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace` (charSpace bridge).

#### Sources
- [Miy] §4.6 Lemma 4.6.11, p. 163. (Verbatim in `decomposition.md` L2.)

#### Generality decision
- `Eigenform` in `cuspFormsNew ∩ modFormCharSpace χ`, nonzero. `h_chi_factor` mandatory
  (route-B 4.6.8; the bare `mainLemma` is sorry'd). `N ∣ L` retained for Miyake-fidelity.

---

### [CLEANUP-1] Run /cleanup on StrongMultiplicityOneFull.lean (after T001, T003, T011)
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T001, T003, T011 (the first 3 proof tickets)
- **Parallel**: no
- **Type**: cleanup
- **Description**: Cadence cleanup after the first 3 proof tickets. Golf the 4.5.15/4.6.2/
  orthogonality lemmas, fix naming, ensure docstrings cite Miyake (no proof strategy in
  docstrings per project style). Blocks T002 from building on un-cleaned code only loosely
  (T002 may proceed; this is the cadence checkpoint).

---

### [T005] Def: `cuspFormsOldChar` + basic span API (Miyake's S_k^♭(N,χ))
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: none (def); but `m_χ`-refinement caveat (T006a) interacts
- **Parallel**: yes
- **Type**: def + API (BUILD — gap #4 core)
- **Mathlib check**: not in mathlib/project; the χ-refined old space is new. Closest is the
  project's character-agnostic `cuspFormsOld` (`Newforms/Basic.lean:131`) and the placeholder
  `validSourceLevels`/`lowerLevelPairs` (`LevelEmbed.lean:85,93`).

#### Statement
```lean
def cuspFormsOldChar (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ
    {f | ∃ (M : ℕ) (l : ℕ) (_ : NeZero M) (_ : NeZero l)
        (_hcond : m_χ ∣ M) (_hML : M ≠ N) (heq : l * M = N)
        (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
      g ∈ cuspFormsNew M k ∧ heq ▸ levelRaise M l k g = f}
-- + API lemmas (BUILD): `mem_cuspFormsOldChar` (unfold the generator), and a generator
--   constructor `levelRaise_mem_cuspFormsOldChar` mirroring `Submodule.subset_span`.
```

#### Proof sketch
- Def: copy from skeleton (already elaborates). API lemmas: `mem` is `Submodule.mem_span`-style;
  generator membership is `Submodule.subset_span ⟨M, l, …, ⟨hg_new, rfl⟩⟩`.
- **T006a (sub-task, MEDIUM risk):** decide whether `g ∈ cuspFormsNew M k` must be refined to
  `g ∈ cuspFormsNew M k ∩ cuspFormCharSpace_M (χ mod M)` for faithfulness to Miyake's
  `S_k^♯(M,χ)`. The conductor-descent `χ = (χ mod M) ∘ ZMod.unitsMap` is available via
  `DirichletCharacter.conductor` + `ZMod.unitsMap` (used in `h_chi_factor`). If the downstream
  proofs (T008, T010) only need the new-ness + same-eigenvalue, the χ-refinement may be
  deferrable; record the decision in the def's docstring.

#### Mathlib/project lemmas needed
- `Submodule.span`, `Submodule.subset_span`, `Submodule.mem_span` (mathlib).
- `cuspFormsNew` (`Newforms/Basic.lean:180`), `levelRaise` (`LevelRaise.lean:231`).
- (T006a) `DirichletCharacter.conductor`, `ZMod.unitsMap`.

#### Sources
- [Miy] §4.6, p. 162 (definition of S_k^♭). (Verbatim in `decomposition.md` L4 / 4.6.9 quote.)

#### Generality decision
- Explicit `m_χ : ℕ` argument (caller-controlled). Span over the Miyake generator set verbatim.

---

### [T006] Lemma 4.6.9(2): `levelRaise_cuspFormsNew_le_cuspFormsOldChar`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T005
- **Parallel**: yes (with T007, T009 after T005)
- **Type**: lemma (BUILD)

#### Statement
```lean
theorem levelRaise_cuspFormsNew_le_cuspFormsOldChar
    (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    {M : ℕ} [NeZero M] {l : ℕ} [NeZero l]
    (hcond : m_χ ∣ M) (hML : M ≠ N) (heq : l * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (hg_new : g ∈ cuspFormsNew M k) :
    (heq ▸ levelRaise M l k g) ∈ cuspFormsOldChar N k χ m_χ := by
  sorry
```

#### Proof sketch (Miyake §4.6 Lemma 4.6.9(2), p. 162)
1. `exact Submodule.subset_span ⟨M, l, ‹NeZero M›, ‹NeZero l›, hcond, hML, heq, g, hg_new, rfl⟩`.
   (Direct membership in the generator set.)

#### Mathlib/project lemmas needed
- `Submodule.subset_span` (mathlib); T005's def.

#### Sources
- [Miy] §4.6 Lemma 4.6.9(2), p. 162.

#### Generality decision — inherits T005.

---

### [T007] Lemma 4.6.9(1): `cuspFormsOldChar_eq_bot_of_conductor_eq`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T005
- **Parallel**: yes (with T006, T009)
- **Type**: lemma (BUILD)

#### Statement
```lean
theorem cuspFormsOldChar_eq_bot_of_conductor_eq
    (χ : DirichletCharacter ℂ N) (hcond : χ.conductor = N) :
    cuspFormsOldChar N k χ.toUnitHom χ.conductor = ⊥ := by
  sorry
```

#### Proof sketch (Miyake §4.6 Lemma 4.6.9(1), p. 162)
- `rw [hcond]`. Now `m_χ = N`. Show the generator set is **empty**: any generator needs
  `M` with `N ∣ M` (`m_χ = N ∣ M`) and `M ∣ N` and `M ≠ N`; but `N ∣ M ∧ M ∣ N ⟹ M = N`
  (`Nat.dvd_antisymm`), contradicting `M ≠ N`.
1. `rw [hcond, cuspFormsOldChar]`.
2. `convert Submodule.span_empty using 2` (or `rw [show {f | …} = ∅ from …]`); prove the set
   is empty: `Set.eq_empty_iff_forall_not_mem.mpr`, then `rintro f ⟨M,l,_,_,hMdvd,hMne,heq,…⟩`,
   derive `M = N` from `Nat.dvd_antisymm hMdvd (⟨l, by rw [← heq, mul_comm]⟩ : M ∣ N)`,
   `exact hMne this`.
3. `Submodule.span_empty` ⟹ `⊥`.

#### Mathlib/project lemmas needed
- `Nat.dvd_antisymm`, `Submodule.span_empty`, `Set.eq_empty_iff_forall_not_mem` (mathlib).

#### Sources
- [Miy] §4.6 Lemma 4.6.9(1), p. 162. NOTE (see `decomposition.md` L4.2 / Risk #1): under
  the span-definition this is the *empty-index-set* triviality, NOT the deep orthocomplement
  statement — the depth is in `cuspFormsOldChar = cuspFormsOld` (T012), which 4.6.12 avoids.

#### Generality decision — `χ : DirichletCharacter ℂ N`; binds `m_χ := χ.conductor`.

---

### [T008] Lemma 4.6.9(3) + eigen-refinement: `exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T005, T003, T011
- **Parallel**: no (internal, multi-step)
- **Type**: lemma (BUILD — internal node, ~120 LOC)

#### Statement
```lean
theorem exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar
    (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsOldChar N k χ m_χ) :
    ∃ (ι : Type) (_ : Fintype ι) (M : ι → ℕ) (l : ι → ℕ)
      (_ : ∀ i, NeZero (M i)) (_ : ∀ i, NeZero (l i))
      (_ : ∀ i, m_χ ∣ M i) (_ : ∀ i, M i ≠ N) (heq : ∀ i, l i * M i = N)
      (h : ∀ i, CuspForm ((Gamma1 (M i)).map (mapGL ℝ)) k),
      (∀ i, h i ∈ cuspFormsNew (M i) k) ∧ (∀ i, IsEigenform (h i)) ∧
      f = ∑ i, (heq i ▸ levelRaise (M i) (l i) k (h i)) := by
  sorry
```

#### Proof sketch (Miyake §4.6 Lemma 4.6.9(3), p. 162 + step (i), p. 164)
1. **Generation (4.6.9(3)):** `Submodule.span_induction` on `hf`. Generators give a single
   `V_l g`, `g ∈ cuspFormsNew M k`; sums/smuls accumulate finite index sets (use
   `Finset`/`Sigma` indexing or `ι := Σ generator-data`).
2. **Eigen-refinement (step (i)):** each `g ∈ cuspFormsNew M k` is, by
   `exists_simultaneous_eigenform_basis` (`AdjointTheoryPetersson.lean:880`, sorry-free),
   a finite ℂ-combination of common eigenforms in `cuspFormCharSpace M χ_M`; intersect with
   `cuspFormsNew M k` (stable under `Tₙ` by `heckeT_n_preserves_cuspFormsNew`,
   `LevelRaiseComm.lean:966`) to get **new** eigen-components. Each component is an
   `IsEigenform` (predicate, `Newforms/Basic.lean:94`).
3. Re-index the double sum (generators × eigenbasis) into one `Fintype ι`.
4. Each eigen-component pushes through `V_l` keeping eigen-ness by **T003** (4.6.2). (Used by
   the *caller* T010; here we only need `IsEigenform (h i)` at level `M i`, before raising.)

Off-script: `FiniteDimensional ℂ (cuspFormCharSpace k χ)` instance — discharged by
`cuspForm_finiteDimensional` (`Newforms/Basic.lean:221`) restricted to the eigenspace; the
project already supplies the instance wherever `exists_simultaneous_eigenform_basis` is used.

**Sizing:** Miyake's 4.6.9(3) + (i) is ~12 source lines (p. 162 + p. 164); ~120 LOC in Lean
(span-induction + eigenbasis re-indexing is heavy). If over heartbeat budget, split into
`…_generation` (4.6.9(3)) and `…_eigen_refine` (step (i)) helper lemmas — NO `maxHeartbeats`.

#### Mathlib/project lemmas needed
- `Submodule.span_induction` (mathlib); T005 def.
- `exists_simultaneous_eigenform_basis` (`AdjointTheoryPetersson.lean:880`, sorry-free).
- `heckeT_n_preserves_cuspFormsNew` (`LevelRaiseComm.lean:966`, sorry-free).
- `IsEigenform` (`Newforms/Basic.lean:94`); `cuspForm_finiteDimensional` (`Newforms/Basic.lean:221`).

#### Sources
- [Miy] §4.6 Lemma 4.6.9(3) p. 162; step (i) p. 164. (Verbatim in `decomposition.md` L4.3.)

#### Generality decision
- Output indexed by an abstract `Fintype ι` (cleanest for the caller's "drop wrong-eigenvalue
  summands" step). `IsEigenform` predicate (not bundled `Eigenform`) to avoid χ-threading here.

---

### [CLEANUP-2] Run /cleanup on StrongMultiplicityOneFull.lean (after T008)
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T008 (and T002, T005, T006, T007 done by now → 3+ since CLEANUP-1)
- **Parallel**: no
- **Type**: cleanup
- **Description**: Cadence cleanup after the gap-#4 forward leaves (T002, T005, T006, T007,
  T008). Golf the span-induction in T008; ensure `cuspFormsOldChar` API is mathlib-quality
  before T010 builds on it. Consider split-file if the file exceeds ~1500 lines.

---

### [T009] Gap-#4 bridge (easy direction): `cuspFormsOldChar_le_cuspFormsOld`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T005
- **Parallel**: yes (with T006, T007)
- **Type**: lemma (BUILD)

#### Statement
```lean
theorem cuspFormsOldChar_le_cuspFormsOld
    (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ) :
    cuspFormsOldChar N k χ m_χ ≤ cuspFormsOld N k := by
  sorry
```

#### Proof sketch (gap-#4 bridge, easy inclusion)
1. `rw [cuspFormsOldChar]; refine Submodule.span_le.mpr ?_; rintro f ⟨M,l,_,_,_,hMne,heq,g,_,rfl⟩`.
2. Show `(heq ▸ levelRaise M l k g) ∈ cuspFormsOld N k = Submodule.subset_span ⟨M, l, …, 1<l, heq, g, rfl⟩`
   (the project's `IsOldformGenerator` needs `1 < l`).
3. Discharge `1 < l`: from `heq : l*M = N`, `hMne : M ≠ N`, `NeZero N`: `l ≠ 0` (else `N=0`);
   `l ≠ 1` (else `M = N`). So `1 < l` by `omega`/`Nat` lemmas.

#### Mathlib/project lemmas needed
- `Submodule.span_le`, `Submodule.subset_span` (mathlib); `cuspFormsOld`/`IsOldformGenerator`
  (`Newforms/Basic.lean:122,131`).

#### Sources
- [Miy] §4.6 (S_k^♭ ⊆ "lower-level cusp forms"); the project's `cuspFormsOld` is the latter.
  (See `decomposition.md` L4.4.)

#### Generality decision — `χ`, `m_χ` general (χ unused in conclusion; documents intent).

---

### [T004] 4.6.12 new part: `newPart_eq_smul_of_shared_eigenvalues`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T001, T002
- **Parallel**: yes (with T010 after deps)
- **Type**: lemma (BUILD — internal, template = `newform_unique_routeB`)

#### Statement
```lean
theorem newPart_eq_smul_of_shared_eigenvalues
    (f : Newform N k) (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hg_new : g_new.toCuspForm ∈ cuspFormsNew N k)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S → f.eigenvalue n = g_new.eigenvalue n)
    (h_chi_factor : …) :
    g_new.toCuspForm =
      (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 • f.toCuspForm := by
  sorry
```

#### Proof sketch (Miyake 4.6.12 new part, p. 163)
1. Set `b₁ := (qExpansion 1 g_new).coeff 1`, `h := g_new.toCuspForm - b₁ • f.toCuspForm`.
2. `h ∈ cuspFormsNew N k` (`sub_mem` + `smul_mem` of `hg_new`, `f.isNew`).
3. Upgrade `h_eig` (off `S`) to all coprime via `eigenvalues_eq_all_coprime_of_eq_off_finite`
   (`SMOObligations.lean:362`, sorry-free) — wraps `f g_new`... NOTE this is stated for two
   `Newform`s; for an `Eigenform g_new` reuse its prime-cofactor argument or restate. If
   `g_new` is not a `Newform`, prove the coprime-coefficient vanishing directly:
   `cₙ = aₙ(g_new) - b₁·aₙ(f)`. By **T001**, `aₙ(g_new) = b₁·λₙ(g_new)`; by
   `Newform.eigenvalue_eq_coeff` (`MainLemma.lean:256`), `aₙ(f) = λₙ(f)`; and `h_eig`
   gives `λₙ(f) = λₙ(g_new)` off `S` (extend to all coprime via the prime-cofactor trick
   `eigenvalues_eq_all_coprime_of_eq_off_finite` adapted). ⟹ `cₙ = 0` for `(n,N)=1`.
4. Apply `mainLemma_charSpace_routeB χ h (charSpace mem) (vanish) h_chi_factor` ⟹ `h ∈ cuspFormsOld`.
5. `cuspFormsOld_disjoint_cuspFormsNew` on `h` (old ∧ new) ⟹ `h = 0` ⟹ `g_new = b₁ • f`.

Template: `newform_unique_routeB` (`SMOObligations.lean:258`) is the `b₁=1` shadow — copy its
`h_vanish` block (lines 276–298) with the `b₁` scalar inserted.

#### Mathlib/project lemmas needed
- T001; `Newform.eigenvalue_eq_coeff` (`MainLemma.lean:256`); `mainLemma_charSpace_routeB`;
  `cuspFormsOld_disjoint_cuspFormsNew`; `eigenvalues_eq_all_coprime_of_eq_off_finite`
  (`SMOObligations.lean:362`); `qExpansion_sub`, `PowerSeries.coeff` lemmas (mathlib).

#### Sources
- [Miy] 4.6.12 new part, p. 163. (Verbatim in `decomposition.md` L5.)

#### Generality decision
- `g_new : Eigenform` (not `Newform` — its `a₁ = b₁` is the unknown scalar). `S : Finset`
  generalises "L". `h_chi_factor` mandatory.

---

### [T010] 4.6.12 old part = 0: `oldPart_eq_zero_of_shared_eigenvalues`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T008, T001, T002, T006, T009, T011
- **Parallel**: no (internal, ~150 LOC, consumes gaps #3,#4)
- **Type**: lemma (BUILD — internal node)

#### Statement
```lean
theorem oldPart_eq_zero_of_shared_eigenvalues
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (g_old : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_old : g_old ∈ cuspFormsOldChar N k χ m_χ)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      ∀ lam : ℂ, (haveI : NeZero n.val := ⟨n.pos.ne'⟩
        heckeT_n_cusp k n.val g_old = lam • g_old) → f.eigenvalue n = lam)
    (h_chi_factor : …) :
    g_old = 0 := by
  sorry
```

#### Proof sketch (Miyake 4.6.12 steps (i)+(ii), p. 164)
1. By contradiction: `g_old ≠ 0`.
2. **(i)** `exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar` (**T008**) ⟹
   `g_old = ∑ i, V_{l i}(h i)`, `h i ∈ cuspFormsNew (M i) k`, `IsEigenform (h i)`. Since
   `g_old ≠ 0`, some summand `V_{l i₀}(h i₀) ≠ 0`, so `h i₀ ≠ 0`. By **T003** (4.6.2),
   `V_{l i₀}(h i₀)` is a `Tₙ`-eigenform at level `N` with `h i₀`'s eigenvalue. Drop summands
   whose eigenvalue `≠ aₙ` using **T011** (`petN_eq_zero_of_ne_eigenvalues`) /
   linear-independence; the surviving `h := h i₀` has eigenvalue `aₙ = f.eigenvalue n` off `S`.
3. **(ii)** `h ≠ 0` new eigenform at proper divisor `M := M i₀` ⟹ by **T002** (4.6.11 at
   level M), `c₁' := a₁(h) ≠ 0`. Form `h - c₁' • (V?-pullback of f)`… — more precisely work at
   level N: let `H := V_{l i₀}(h)`; `H - c₁' • f` has vanishing coprime coeffs (T001 for `h`'s
   coeffs via 4.6.2 coefficient relation + `eigenvalue_eq_coeff` for f). Apply route-B 4.6.8
   ⟹ `H - c₁' • f ∈ cuspFormsOld N k`. Also `H ∈ cuspFormsOld N k`: by **T006** (4.6.9(2),
   `h ∈ cuspFormsNew M k` ⟹ `H ∈ cuspFormsOldChar N k`) then **T009** (bridge) ⟹
   `H ∈ cuspFormsOld N k`.
4. `f = c₁'⁻¹ • H - c₁'⁻¹ • (H - c₁' • f) ∈ cuspFormsOld N k` (submodule closed under
   sub/smul). But `f ∈ cuspFormsNew N k` (`f.isNew`) and `f ≠ 0`
   (`newform_toModularForm_ne_zero` ⟹ `f.toCuspForm ≠ 0`); `cuspFormsOld_disjoint_cuspFormsNew`
   ⟹ `f.toCuspForm = 0`, contradiction. Hence `g_old = 0`.

**Sizing:** Miyake (i)+(ii) ≈ 22 source lines; ~150 LOC. If over budget, split:
`…_extract_lowlevel_eigenform` (step (i) → produces `h`, `M`, `c₁'≠0`) and
`…_contradiction` (step (ii)). NO `maxHeartbeats`.

#### Mathlib/project lemmas needed
- T008, T003, T011, T002, T001, T006, T009; `mainLemma_charSpace_routeB`;
  `Newform.eigenvalue_eq_coeff`; `cuspFormsOld_disjoint_cuspFormsNew`;
  `newform_toModularForm_ne_zero` (`SMOObligations.lean:165`).

#### Sources
- [Miy] 4.6.12 (i)+(ii), p. 164. (Verbatim in `decomposition.md` L6.)

#### Generality decision
- `g_old ∈ cuspFormsOldChar` (NOT just `cuspFormsOld`) — necessary for T008's descent. This
  is the honest gap-#4 dependency (forward direction only).

---

### [CLEANUP-3] Run /cleanup on StrongMultiplicityOneFull.lean (after T004, T010)
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T004, T010 (+ T009 done → 3 since CLEANUP-2)
- **Parallel**: no
- **Type**: cleanup
- **Description**: Cadence cleanup after the two big internal nodes (T004, T009, T010). Golf
  T010's descent; verify helper-lemma split kept everything under default heartbeats.

---

### [T012] Decomposition codisjointness for the χ-refined old space (RISKIEST — gap #4 structural)
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
  (or a new `SMOObligations/Lemma4_6_9.lean`)
- **Depends on**: T005, T006, T007, T008, T009
- **Parallel**: no
- **Type**: theorem (BUILD — **OPEN/HARD; optional via Mitigation B in T013**)

#### Statement (target — Option A)
```lean
theorem cuspFormsOldChar_isCompl_cuspFormsNew
    (χ : DirichletCharacter ℂ N) :
    IsCompl (cuspFormsOldChar N k χ.toUnitHom χ.conductor) (cuspFormsNew N k) := by
  sorry
```

#### Proof approach + RISK
- Mirrors `cuspFormsOld_isCompl_cuspFormsNew` (`Newforms/Basic.lean:309`), which uses
  `cuspFormsNew = (cuspFormsOld)⊥`. To get the same for `cuspFormsOldChar`, need
  `cuspFormsNew = (cuspFormsOldChar)⊥`, i.e. `(cuspFormsOldChar)⊥ = (cuspFormsOld)⊥`.
  In a finite-dim nondegenerate inner-product space this is `cuspFormsOldChar` and
  `cuspFormsOld` having the **same span-saturation**, morally `cuspFormsOldChar = cuspFormsOld`.
- **This is the formal content of the master-plan identification
  (`docs/plans/strong-multiplicity-one.md:617`) that `cuspFormsOld` "is" Miyake's S_k^♭.**
  It is genuinely nontrivial and **may be open-ended** (it asserts that the full-space,
  all-divisors oldform span coincides with the χ-refined new-space-based span — a real
  newform-theory theorem, essentially Atkin–Lehner–Li new/old at this level).
- **Feasibility: MEDIUM-LOW.** Recommend NOT gating the milestone on this.

#### Mitigation B (RECOMMENDED, bounded — see T013)
- Skip T012. State 4.6.12 (T013) with `g.toCuspForm ∈ cuspFormsOldChar N k χ m_χ ⊔ cuspFormsNew N k`
  as a hypothesis (matching the master plan's `hg1` and Miyake's `g ∈ S_k(N,χ) = S_k^♭ ⊕ S_k^♯`).
  This yields a complete, honest 4.6.12 without the structural equivalence.

#### Sources
- [Miy] §4.6 p. 162 (S_k^♯ = (S_k^♭)⊥, the decomposition); [DS] §5.7 (new/old).

#### Generality decision — `DirichletCharacter ℂ N`; `m_χ := χ.conductor`.

---

### [CLEANUP-ALL-1] Run /cleanup-all on the project so far (before milestone T013)
- **Status**: open
- **File**: (project-wide, scoped to the new file + the 1-line AdjointTheoryPetersson edit)
- **Depends on**: every open proof ticket on the critical path (T004, T010, T006, T007, T009;
  T012 if pursued)
- **Parallel**: no
- **Type**: cleanup (pre-milestone)
- **Description**: Project-wide cleanup before assembling the milestone. Per cadence rule §1g.3.

---

### [T013] Theorem 4.6.12 (MILESTONE): `strongMultiplicityOne_constMul`
- **Status**: open
- **File**: `LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean`
- **Depends on**: T004, T010, CLEANUP-ALL-1 (and either T012 OR Mitigation B)
- **Parallel**: no (milestone)
- **Type**: theorem (BUILD — assembly)

#### Statement (Option A, if T012 done — as in skeleton)
```lean
theorem strongMultiplicityOne_constMul
    (f : Newform N k) (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S → f.eigenvalue n = g.eigenvalue n)
    (h_chi_factor : …) :
    ∃ c : ℂ, g.toCuspForm = c • f.toCuspForm := by
  sorry
```
#### Statement (Option B, RECOMMENDED — add the direct-sum membership hypothesis)
```lean
-- add hypothesis:
--   (hg_decomp : g.toCuspForm ∈ cuspFormsOldChar N k χ χ.conductor' ⊔ cuspFormsNew N k)
-- then no T012 needed.
```

#### Proof sketch (Miyake 4.6.12 assembly, pp. 163–164)
- **Option A:** use `cuspFormsOldChar_isCompl_cuspFormsNew` (T012) to decompose
  `g.toCuspForm = g_old + g_new` with `g_old ∈ cuspFormsOldChar`, `g_new ∈ cuspFormsNew`.
- **Option B:** `obtain` `g_old, g_new` from `Submodule.mem_sup.mp hg_decomp`.
- Then in both cases:
  1. By 4.6.10 (`heckeT_n_preserves_cuspFormsOld/New` — but for `cuspFormsOldChar` use
     stability of the span under `Tₙ`, which follows from `heckeT_n_levelRaise_comm` +
     `heckeT_n_preserves_cuspFormsNew` on each generator; small helper or fold into T008),
     `g_old`, `g_new` are common eigenfunctions with `g`'s eigenvalues.
  2. **T010** ⟹ `g_old = 0`. **T004** ⟹ `g_new = b₁ • f` where `b₁ = a₁(g_new) = a₁(g)`.
  3. `g.toCuspForm = g_old + g_new = 0 + b₁ • f = b₁ • f`. `exact ⟨b₁, by simp [...]⟩`.

#### Mathlib/project lemmas needed
- T004, T010; (Option A) T012; (Option B) `Submodule.mem_sup`; `oldPart_add_newPart`-analogue;
  4.6.10 stability; `Eigenform.eigenvalue` matching of `g_old`/`g_new` with `g`.

#### Sources
- [Miy] Theorem 4.6.12, statement p. 163, proof pp. 163–164. (Full verbatim transcription
  in `decomposition.md` top-level.)

#### Generality decision
- `f : Newform`, `g : Eigenform`, `S : Finset`, `h_chi_factor` (route-B). Conclusion
  `∃ c, g = c • f` (Miyake's "constant multiple"); `c = a₁(g)`. **DEPENDS ON
  `strongMultiplicityOne_axiom_clean`** (via T004's route-B machinery) and never modifies it.
- **Ship Option B first** (bounded, complete, faithful); upgrade to Option A iff T012 lands.

---

### [CLEANUP-FINAL] Run /cleanup-all on the whole project
- **Status**: open
- **File**: (whole project)
- **Depends on**: T013 (and all other tickets)
- **Parallel**: no
- **Type**: cleanup (final)
- **Description**: Final mathlib-quality pass. Then `/pre-submit`: `lake build` clean, no
  `sorry` in the new file, `#print axioms strongMultiplicityOne_constMul` shows only
  `propext, Classical.choice, Quot.sound` (NO `sorryAx`), and confirm the new theorem depends
  on `strongMultiplicityOne_axiom_clean` without having modified it.

---

## Cleanup-cadence verification

13 proof/def tickets in one file (`StrongMultiplicityOneFull.lean`). Required:
`⌈13/3⌉ = 5` cadence + final-per-file cleanups; plus pre-milestone CLEANUP-ALL + final.
Inserted: CLEANUP-1 (after T001/T003/T011), CLEANUP-2 (after T002/T005/T006/T007/T008),
CLEANUP-3 (after T009/T004/T010), CLEANUP-ALL-1 (pre-milestone), CLEANUP-FINAL (final) — and
the final-per-file pass is folded into CLEANUP-3/CLEANUP-ALL-1 (same single file). 6 cleanup
tickets total. ✅

---

### [T010-A] `levelInclude_cusp` lands in the lifted character space (diamond commutation)
- **Status**: done (DONE 2026-05-27: `levelInclude_cusp_mem_cuspFormCharSpace_comp` + `diamondOpCusp_levelInclude_cusp_eq` proven, build green)
- **File**: LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean
- **Depends on**: (none new)
- **Parent**: T010 (oldPart_eq_zero_of_shared_eigenvalues)
- **Type**: lemma
- **Statement**:
  ```
  private theorem levelInclude_cusp_mem_cuspFormCharSpace_comp
      {M : ℕ} [NeZero M] {N : ℕ} [NeZero N] {k : ℤ} (hMN : M ∣ N) (ψ : (ZMod M)ˣ →* ℂˣ)
      {g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hg : g ∈ cuspFormCharSpace k ψ) :
      levelInclude_cusp hMN k g ∈ cuspFormCharSpace k (ψ.comp (ZMod.unitsMap hMN))
  ```
- **Proof Sketch**:
  1. `mem_cuspFormCharSpace_iff`; intro `a : (ZMod N)ˣ`.
  2. `diamondOpCusp k a (levelInclude_cusp hMN g)` slashes `⇑g` by `mapGL ℝ (g_N : SL(2,ℤ))`,
     where `g_N ∈ Γ₀(N)` represents `a` (`diamondOpCusp_eq` + `diamondOpCuspAux`); the
     underlying function is unchanged because `levelInclude_cusp_coe : ⇑(levelInclude_cusp..) = ⇑g`.
  3. Take a representative `g_N ∈ Γ₀(N)` of `a` (`Gamma0MapUnits_surjective`); then
     `g_N ∈ Γ₀(M)` via `Gamma0_le_of_dvd hMN`, and at level M it represents `unitsMap a`
     (`Gamma0MapUnits_unitsMap_of_Gamma0_mul` / `Gamma0MapUnits_val`).
  4. `levelInclude_cusp (diamondOpCusp k (unitsMap a) g)` slashes `⇑g` by the SAME
     `mapGL ℝ g_N`; conclude `diamondOpCusp k a (levelInclude_cusp g) =
     levelInclude_cusp (diamondOpCusp k (unitsMap a) g)`.
  5. `diamondOpCusp_apply_charSpace k ψ (unitsMap a) hg` rewrites to `ψ(unitsMap a) • g`;
     push through `levelInclude_cusp` (linear, `map_smul`).
- **Mathlib Lemmas**: `diamondOpCusp_eq`, `levelInclude_cusp_coe`, `Gamma0MapUnits_surjective`,
  `Gamma0_le_of_dvd`, `Gamma0MapUnits_unitsMap_of_Gamma0_mul`, `diamondOpCusp_apply_charSpace`.
- **Sources**: Miyake Lemma 4.6.9(2) (the trivial inclusion preserves Nebentypus).
- **Generality**: minimal — match the T010 use site (M ∣ N, level-N character pullback).

---

### [T010-B] `h_chi_factor` descends along a character pullback (`χ = ψ∘unitsMap`, `M ∣ N`)
- **Status**: blocked/INVALID — h_chi_factor provably does NOT descend (valuation counterexample N=p², M=p, conductor p). See T010-C.
- **File**: LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean
- **Depends on**: (none new)
- **Parent**: T010 (oldPart_eq_zero_of_shared_eigenvalues)
- **Type**: lemma
- **Statement** (informal): if `χ = ψ.comp (ZMod.unitsMap hMN)` (`hMN : M ∣ N`) and `χ`
  satisfies the level-`N` h_chi_factor (∀ prime `p ∣ N`, χ factors through `N/p`), then `ψ`
  satisfies the level-`M` h_chi_factor (∀ prime `q ∣ M`, ψ factors through `M/q`).
- **Proof Sketch** (conductor route):
  1. `h_chi_factor` at `N` for χ ⟺ `(dirichletLift χ).conductor` is coprime to `N`
     (a number dividing `N/p` for **every** prime `p ∣ N` is coprime to `N`, and conversely).
  2. `dirichletLift χ = changeLevel hMN (dirichletLift ψ)` (since `χ = ψ∘unitsMap`,
     `changeLevel_def`/`MulChar.ofUnitHom`).
  3. `conductor (changeLevel hMN ρ) = conductor ρ` — both share `primitiveCharacter ρ`
     (changeLevel preserves the primitive character: `changeLevel_trans` +
     `changeLevel_primitiveCharacter` + `primitiveCharacter_isPrimitive`).
  4. So `(dirichletLift ψ).conductor = (dirichletLift χ).conductor`, coprime to `N`, hence
     coprime to `M` (`M ∣ N`), hence `∣ M/q` for each prime `q ∣ M`.
  5. `ψ.conductor ∣ M/q` + `factorsThrough_iff_ker_unitsMap` ⟹ the `χ'` witness for ψ at `M/q`.
- **Mathlib Lemmas**: `DirichletCharacter.changeLevel_def`, `changeLevel_trans`,
  `changeLevel_primitiveCharacter`, `primitiveCharacter_isPrimitive`, `conductor_dvd_level`,
  `factorsThrough_iff_ker_unitsMap`, `conductor_dvd_of_mem_conductorSet`,
  `Nat.Coprime.coprime_dvd_right`, `Nat.coprime_of_dvd` style.
- **Sources**: Miyake p.160 (the "(l, N/m_χ)" prime restriction is a conductor-coprimality).
- **Generality**: minimal — match the T010 step (ii) use site.

---

### [T010-C] Unconditional Main Lemma (DS 5.7.1 / Miyake 4.6.8) — the genuine blocker for T010 step (ii)
- **Status**: blocked (B3 — project's central sorried theorem; published-theorem scale)
- **File**: LeanModularForms/HeckeRIngs/GL2/Newforms/MainLemma.lean (`Newforms.mainLemma`, line ~445, `:= by sorry`)
- **Parent**: T010 (oldPart_eq_zero_of_shared_eigenvalues)
- **Type**: theorem (zero-criterion / unconditional 4.6.8)
- **Precise missing lemma**: the **zero-criterion** `∀ g ∈ cuspFormsNew N k, (∀ n coprime N,
  aₙ(g)=0) → g = 0` (equivalently `Newforms.mainLemma` unconditional), with NO `h_chi_factor`.
  Reduces (`mainLemma_of_newSubspace_coprime_vanishing_zero`, PROVEN) to showing a new eigenform
  with vanishing coprime coeffs is Petersson-orthogonal to itself — i.e. `petN g (eigf) = 0` for
  an eigenform `eigf` and a vanishing-coprime `g`. This is the Rankin–Selberg/unfolding content
  of DS 5.7.1, NOT present in the project (confirmed: 3 `exact?`/decomposition attempts fail; no
  lemma relates `petN` to q-coefficients).
- **Why T010 needs it (and route-B 4.6.8 does NOT suffice)**: step (ii) extracts a nonzero new
  eigenform `h` at a proper divisor level `M` (char ψ, conductor `m_χ`) and needs `a₁(h) ≠ 0`
  (4.6.11). 4.6.11's proof needs 4.6.8-at-`M`. The PROVEN 4.6.8 (`mainLemma_charSpace_routeB`)
  requires `ψ`'s level-`M` `h_chi_factor`, which provably FAILS for the matching summand:
  with `N = p²`, χ of conductor `p` (χ's level-N h_chi_factor holds: `p ∣ N/p = p`), the old
  space `S_k^♭(p²,χ)` is spanned by `B_p(S_k^♯(p, χ_p))` with `χ_p` the conductor-`p` (primitive)
  character mod `p`; the matching summand sits at `M = p` with `ψ = χ_p`, and `ψ`'s level-`p`
  h_chi_factor needs `p ∣ p/p = 1`, FALSE. So the unconditional 4.6.8 is unavoidable here.
- **Available inputs** (per MEMORY: adjoint/spectral frontier CLOSED): `heckeT_n_adjoint`,
  `exists_simultaneous_eigenform_basis`, `exists_eigenform_decomposition_of_invariant`,
  `qSupportedOnDvd_mem_cuspFormsOld_of_char`, `mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule`
  are all proven. The MISSING analytic bridge is `petN`↔`q`-coefficients (Rankin–Selberg), which
  no current lemma supplies — this is the multi-week development by mathlib standards.
