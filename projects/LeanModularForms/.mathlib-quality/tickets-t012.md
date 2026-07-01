# Ticket board — T012 (reverse old-space inclusion → unconditional Miyake 4.6.12)

*`/develop --decompose` ADVERSARIAL planning-only, 2026-05-27, branch `hecke-ring`. NEW file
(does not touch the `-adjoint` artifacts). Plan: `plan-t012.md`. Leaf logs + verbatim source
quotes + ≥3 attacks/leaf: `decomposition-t012.md`. No `lake build` run; LSP unavailable. All
`:= by sorry` skeletons are type-check deferred to execution.*

## Summary

- T012 decomposed into 6 leaves (L1-L6) + 1 induction workhorse + 1 public wrapper + 2 new
  infrastructure lemmas (L2 associativity) + 1 assembly-side helper (oldPart-diamond).
- **Verdict: BOUNDED, ~276 LOC** (floor ~195). Conductor fact (Miyake 4.6.4) already proven;
  only genuinely-new piece is `levelRaise` associativity.
- Minimal target = **Option B** `cuspFormsOld ⊓ charSpace ≤ cuspFormsOldChar` (not the stronger,
  circular-prone Option A IsCompl).
- Never modify `strongMultiplicityOne_axiom_clean` / `miyake_4_6_14_*` / any protected statement.
- Never use `native_decide` / `sorry`-as-answer / custom `axiom` / `set_option maxHeartbeats`.

## Dependency order

```
T012-L2  (levelRaise assoc, LevelRaise.lean)  ───────────┐
T012-L4  (linearity split — trivial)                     │
T012-L3  (new piece → cuspFormsOldChar, conductor fact)  ├─→ T012-AUX (induction workhorse) ─→ T012 (public target)
T012-L1  (generator expansion)                           │                                      │
T012-L5  (old piece via IH + χ-descent)  ◄── L2 ─────────┘                                      │
T012-L6  (sum assembly — trivial)                                                               ▼
                                                          T013-ASSEMBLY (drop Mitigation B from strongMultiplicityOne_constMul)
                                                            ◄── T012, T012-OLDPART, existing oldPart_eq_zero_of_shared_eigenvalues
```

Parallel capacity: L2, L4, L1 independent; L3 and L5 depend on the proven infrastructure (and L5 on
L2). AUX consumes all of L1-L6. T012 wraps AUX.

---

### [T012-L2] `levelRaise` associativity (NEW infrastructure)
- **Status**: open | **Type**: lemma (BUILD — new leaf, grep-confirmed absent)
- **File**: `LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean` (near :231)
- **Depends on**: none
- **LOC**: ~50

```lean
lemma levelRaiseMatrix_mul (d d' : ℕ) [NeZero d] [NeZero d'] :
    levelRaiseMatrix d * levelRaiseMatrix d' = levelRaiseMatrix (d * d') := by
  sorry  -- diag(d,1)·diag(d',1)=diag(dd',1): GL ext + Matrix.det_fin_two. deferred.

lemma levelRaise_levelRaise
    (M : ℕ) [NeZero M] (d d' : ℕ) [NeZero d] [NeZero d'] (k : ℤ)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (show d * (d' * M) = (d * d') * M by ring) ▸
        levelRaise (d' * M) d k (levelRaise M d' k g) = levelRaise M (d * d') k g := by
  sorry  -- function-level via levelRaiseFun_apply + α_d•(α_d'•τ)=α_dd'•τ, re-bundle. deferred.
```

- **Proof sketch:** matrix lemma by `GeneralLinearGroup` ext + `det_fin_two`. Bundle lemma:
  **dodge the `heq ▸` transport** — prove `levelRaiseFun d k (levelRaiseFun d' k f) =
  levelRaiseFun (d*d') k f` pointwise (`levelRaiseFun_apply` `LevelRaise.lean:315` gives `f(α_l•τ)`;
  `α_d•(α_{d'}•τ)=(α_d·α_{d'})•τ=α_{dd'}•τ` via `levelRaiseMatrix_mul` + `mul_smul`; rescale
  `(d^{1-k})(d'^{1-k})=(dd')^{1-k}` via `mul_zpow`+`Nat.cast_mul`), then re-bundle with
  `CuspForm.ext`/`qExpansion_ext2` (pattern: `MainLemma.lean:288-295`).
- **Lemmas:** `levelRaiseFun_apply` (`LevelRaise.lean:315`), `levelRaiseMatrix_mul_mapGL`
  (`LevelRaise.lean:140`, analogue), `mul_smul`, `mul_zpow`, `Nat.cast_mul`, `CuspForm.ext`.
- **Source:** [DS] §5.6 Exercise 5.6.2 (divisor-composition of i_d maps); [Miy] 4.6.8 induction engine.
- **Attacks:** [1] transport hell → function-level dodge (proven pattern). [2] rescaling is `zpow`
  not `cpow` → `mul_zpow` closes. [3] `restrictSubgroup` composition → dodged by function-level route.
  **SURVIVES.**

---

### [T012-L1] finite generator expansion of `cuspFormsOld`
- **Status**: open | **Type**: lemma (BUILD — span_induction, project pattern)
- **File**: `LeanModularForms/SMOObligations/Lemma4_6_9.lean`
- **Depends on**: none (consumed by AUX) | **LOC**: ~30
- **Proof sketch:** `Submodule.span_induction` on the `cuspFormsOld` membership (pattern:
  `cuspFormsOld_coeff_eq_zero_of_coprime` `MainLemma.lean:310-352`, 42-LOC analogue). Carry NOT the
  charSpace into the motive (not generator-preserved) — slice via `exists_finsupp_charSpace_of_cuspFormsOld`
  (`MainLemma.lean:92`) to the χ-isotypic part first, then expand generators.
- **Attacks:** [1] charSpace not preserved per generator → χ-slice first (proven finsupp decomp).
  [2] motive must be submodule-closed → `∈ cuspFormsOldChar` is. [3] generators carry `1<d` ⇒ `M≠N`.
  **SURVIVES.**

---

### [T012-L4] `levelRaise` of an old/new split (linearity)
- **Status**: open | **Type**: lemma (BUILD — trivial `map_add`)
- **File**: `Lemma4_6_9.lean` | **Depends on**: none | **LOC**: ~6
- **Proof sketch:** `cuspFormsOld_isCompl_cuspFormsNew` (`Basic.lean:309`) + `oldPart_add_newPart`
  (`Basic.lean:383`); `levelRaise` is `→ₗ[ℂ]` (`LevelRaise.lean:231`) ⇒ `map_add` distributes.
- **Attacks:** [1] noncomputable proj → still LinearMap. [2] `heq ▸` over `+` → `subst heq` first.
  [3] no char issue. **SURVIVES.**

---

### [T012-L3] new piece → `cuspFormsOldChar` (conductor-fact application) ⚠ HARDEST
- **Status**: open | **Type**: lemma (BUILD — compose conductor fact + 4.6.9(2) + isotypic)
- **File**: `Lemma4_6_9.lean`
- **Depends on**: none directly (uses proven infra); interleaves with L1/L6 for global isotypic
- **LOC**: ~110 (the bulk; includes the global χ-isotypic-vanishing bookkeeping)

```lean
lemma levelRaise_newPart_mem_cuspFormsOldChar
    (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N)
    {M d : ℕ} [NeZero M] [NeZero d] (hd : 1 < d) (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hg_new : g ∈ cuspFormsNew M k)
    (h_raise_char : (heq ▸ levelRaise M d k g) ∈ cuspFormCharSpace k χ.toUnitHom) :
    (heq ▸ levelRaise M d k g) ∈ cuspFormsOldChar N k χ.toUnitHom χ.conductor := by
  sorry  -- conductor_theorem_dichotomy_cuspForm_strong ⇒ m_χ ∣ M (nonzero branch); then 4.6.9(2). deferred.
```

- **Proof sketch:** conductor fact `conductor_theorem_dichotomy_cuspForm_strong` on the raised
  χ-form ⇒ either `χ.FactorsThrough (N/d) = M` (⇒ `χ.conductor ∣ M`) or the raised function is 0
  (⇒ `zero_mem`). In the nonzero branch, `levelRaise_cuspFormsNew_le_cuspFormsOldChar`
  (`…Full.lean:227`) with `m_χ ∣ M`, `M ≠ N` (`1<d`, `d M=N`), `g ∈ cuspFormsNew M k`. The
  ψ-selection (which character the new piece carries) is done GLOBALLY in AUX via
  `cuspFormsOld_iSupIndep_inf_charSpace` (`MainLemma.lean:77`) + `exists_finsupp_charSpace_of_cuspFormsNew`
  (`MainLemma.lean:104`); this lemma takes the already-character-pinned generator.
- **Lemmas:** `conductor_theorem_dichotomy_cuspForm_strong` (`ConductorTheorem.lean`, sorry-free),
  `levelRaise_cuspFormsNew_le_cuspFormsOldChar` (`…Full.lean:227`), `levelRaise_mem_cuspFormCharSpace`
  (`ConductorTheorem.lean:1001`), `DirichletCharacter.FactorsThrough` ⇒ conductor-dvd (mathlib).
- **Source:** [Miy] 4.6.9(2) p.162; 4.6.4 conductor theorem (the m_χ∣M fact).
- **Attacks (ATTACK-χ, the crux):** [a] new piece carries single ψ ✓ (finsupp decomp). [b] ψ forced
  χ-compatible — GLOBAL `iSupIndep` argument (bad-ψ pieces vanish in the sum); this is why L1+L3+L6
  are one combined argument, the LOC bulk; **resolvable from proven infra** (the prior pass's
  unresolved "open hard part"). [c] char-agnostic `cuspFormsNew M k` suffices for 4.6.9(2) ✓ (it
  TAKES agnostic-new) — the agnostic def is a feature. [1] m_χ∣M from `FactorsThrough` ✓ (mathlib).
  [2] `hf_period` (f∣T=f) from `T∈Gamma1` + cusp-form slash-invariance, ~3-line have ✓. [3] zero
  branch → `zero_mem` ✓. **SURVIVES.**

---

### [T012-L5] old piece via induction hypothesis + χ-descent
- **Status**: open | **Type**: lemma (BUILD — IH + conductor Case A bundle + L2)
- **File**: `Lemma4_6_9.lean`
- **Depends on**: T012-L2 (associativity); consumed by AUX (the IH is AUX itself at `M_j < N`)
- **LOC**: ~45 (incl. ~5 for the bundled `levelRaise_injective` wrapper)
- **Proof sketch:** `oldPart g_j ∈ cuspFormsOld M_j k`. χ-descend `g_j` to `charSpace_{M_j} χ_{M_j}`
  via `conductorTheoremCaseA_cuspForm` + `_mem_cuspFormCharSpace` (`ConductorTheorem.lean:767,1375`);
  bridge bundle-to-`oldPart g_j` via `levelRaise` injectivity (bundle-wrap of `levelRaiseFun_injective`
  `LevelRaise.lean:367`, ~5 LOC). Apply the IH (AUX at `M_j < N`):
  `oldPart g_j ∈ cuspFormsOld M_j k ⊓ charSpace_{M_j} ≤ cuspFormsOldChar M_j k χ_{M_j} m_χ`. Then
  `oldPart g_j = Σ_i V_{e_i}(h_i)`; apply `V_{d_j}` and fold via **L2**:
  `V_{d_j}(V_{e_i} h_i) = V_{d_j e_i}(h_i)` ⇒ generators of `cuspFormsOldChar N k χ m_χ`
  (`m_χ ∣ M'_i`, `M'_i ≤ M_j < N` ⇒ `M'_i ≠ N`, `(d_j e_i) M'_i = N`).
- **Lemmas:** AUX (IH), `conductorTheoremCaseA_cuspForm(_mem_cuspFormCharSpace)`
  (`ConductorTheorem.lean`), `levelRaiseFun_injective` (`LevelRaise.lean:367`), T012-L2,
  `DirichletCharacter.conductor` invariance under `FactorsThrough`-lowering (mathlib).
- **Source:** [Miy] 4.6.8 induction step p.162 ("by the induction assumption … Σ_q f_M(q)(l_q z)").
- **Attacks:** [1] bundle `⇑F=f` ≅ algebraic `oldPart g_j` → `levelRaise` injective (EXISTS at fun
  level) ✓. [2] IH applies at `M_j=N/d_j<N` ✓; `m_{χ_{M_j}}=m_χ` (conductor invariance) ✓. [3]
  `M'_i ≠ N` from `M'_i ≤ M_j < N` ✓. **SURVIVES.**

---

### [T012-L6] sum assembly
- **Status**: open | **Type**: lemma (BUILD — mathlib `sum_mem`)
- **File**: `Lemma4_6_9.lean` | **Depends on**: L3, L5 | **LOC**: ~10 (interleaved w/ L1, L3)
- **Proof sketch:** `Submodule.sum_mem` / `Finset.sum_mem` + `smul_mem` over `cuspFormsOldChar`.
- **Attacks:** [1] mix new+old generators → both `cuspFormsOldChar`, `add_mem`. [2] span scalars →
  `smul_mem`. [3] empty sum → `zero_mem`. **SURVIVES.**

---

### [T012-AUX] the induction workhorse
- **Status**: open | **Type**: theorem (BUILD — strong induction on N)
- **File**: `Lemma4_6_9.lean`
- **Depends on**: L1, L2, L3, L4, L5, L6 | **LOC**: ~25 (scaffold + IH plumbing)

```lean
theorem cuspFormsOld_inf_charSpace_le_cuspFormsOldChar_aux
    (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOldChar N k χ.toUnitHom χ.conductor := by
  sorry  -- Nat.strong_induction_on N; base bot_le; step = L1∘(L4,L3,L5)∘L6. deferred.
```

- **Proof sketch:** `Nat.strong_induction_on N`. Base: `cuspFormsOld = ⊥` ⇒ `bot_le`. Step: L1
  expands `f`; per generator L4 splits, L3 handles new piece (with global isotypic via the proven
  `iSupIndep`), L5 handles old piece (IH at `M_j<N` + L2); L6 sums.
- **Attacks:** [1] strong induction well-founded on `<` ✓ (`M_j=N/d_j<N`). [2] `[NeZero N]` instance
  threads through `M_j` (`NeZero (N/d_j)`) — supply explicitly as in `coeff_one_ne_zero_…`'s
  `h_chi_factor` block (`StrongMultiplicityOneFull.lean:154-158`). [3] heartbeats: split into L1-L6
  (already separate) — no `maxHeartbeats`. **SURVIVES.**

---

### [T012] public target (Option B)
- **Status**: open | **Type**: theorem (BUILD — thin wrapper of AUX)
- **File**: `Lemma4_6_9.lean` | **Depends on**: T012-AUX | **LOC**: ~3

```lean
theorem cuspFormsOld_inf_charSpace_le_cuspFormsOldChar
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOldChar N k χ.toUnitHom χ.conductor :=
  cuspFormsOld_inf_charSpace_le_cuspFormsOldChar_aux N k χ
```

- **Generality:** `χ : DirichletCharacter ℂ N` (binds `m_χ := χ.conductor`, matching
  `cuspFormsOldChar_eq_bot_of_conductor_eq`). Implicit `{N}{k}` for ergonomic application.

---

### [T012-OLDPART] (assembly-side helper, T013 ticket) `oldPart` commutes with diamond / charSpace
- **Status**: open | **Type**: lemma (BUILD — `linearProjOfIsCompl` uniqueness)
- **File**: `StrongMultiplicityOneFull.lean` (assembly side) | **Depends on**: none | **LOC**: ~10

```lean
lemma oldPart_mem_cuspFormCharSpace_of_mem
    {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    oldPart f ∈ cuspFormCharSpace k χ := by
  sorry  -- diamond-equivariance of linearProjOfIsCompl (both summands diamond-stable). deferred.
```

- **Proof sketch:** `cuspFormsOldProjection = linearProjOfIsCompl` of two diamond-stable submodules
  (`diamondOp_preserves_cuspFormsOld/New`), so it commutes with each `diamondOpCusp d`; then
  `f ∈ charSpace χ ⟺ ∀d, ⟨d⟩f = χ(d) f` transfers to `oldPart f`.
- **NOTE:** This is part of the **T013 assembly** (dropping Mitigation B), not T012's target. Listed
  for completeness so the unconditional `strongMultiplicityOne_constMul` is fully scoped.

---

## Verdict (binding)

**BOUNDED — ~276 LOC** (floor ~195), distributed: ~50 into `LevelRaise.lean` (L2), ~226 into new
`SMOObligations/Lemma4_6_9.lean` (L1,L3,L4,L5,L6,AUX,target) + ~10 assembly-side (T012-OLDPART). The
conductor fact (Miyake 4.6.4) is ALREADY PROVEN; `levelRaiseFun_injective` exists; only `levelRaise`
associativity is genuinely new and it is elementary. The intricate piece (global χ-isotypic
vanishing) is fully backed by proven `iSupIndep`/finsupp infrastructure. **No leaf hides an unproven
mathematical theorem.** This converts the prior pass's "side-step via Mitigation B" into a
dischargeable, bounded path to an **unconditional** Miyake 4.6.12.
