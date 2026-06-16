# Dev ticket — `mainLemma` (DS 5.7.1 / Atkin–Lehner Main Lemma)

**File:** `LeanModularForms/HeckeRIngs/GL2/Newforms/MainLemma.lean`
**Status (2026-06-16):** opaque headline `sorry` → **route-B skeleton, build green** (commit `da70820`). Reduced to 2 precise sub-`sorry`s.

## What's proven (sorry-free)
The `mainLemma` body itself: Nebentypus char-decomposition `f = ∑_χ g_χ`
(`exists_finsupp_charSpace_of_diamondOpCuspHom_invariant` at `⊤`) → per-component oldness → `Submodule.sum_mem`. Plus `qExpansion_one_coeff_finset_sum` (q-coeff additivity over Finset sums, via new `qExpansionOneCuspAddHom`).

## Remaining sub-sorries
1. **`qExpansion_charComponent_coprime_eq_zero`** (~:206) — *coefficient inheritance*: the χ-component `g_χ` of a coprime-coefficient-vanishing `f` is itself coprime-coefficient-vanishing. **The one genuine math gap.** Needs the diamond operators' action on individual period-1 Fourier coefficients *without* a single-character hypothesis (equivalently: the Nebentypus projector commutes with the coprime-index coefficient functionals). The codebase only computes `⟨d⟩`/`T_n` on q-coefficients *inside* one char space (`fourierCoeff_heckeT_n_period_one`); no `qExpansion ∘ diamondOp` lemma exists in the monorepo or mathlib. Either prove that, OR replace the char-decomposition route by a **character-free** sieve (the Miyake 4.6.8 engine is currently χ-indexed — `miyake_4_6_8_inductive_step χ …`).

2. **`mainLemma_charSpace`** (~:222) — per-character Main Lemma. **NOT open**: it is verbatim `HeckeRing.GL2.mainLemma_charSpace_routeB` (`SMOObligations.lean:209`), proven sorry-free (it's used by the axiom-clean `StrongMultiplicityOneFull`). `routeB` is just the 2-line composition
   `coprimeSieve_admits_squarefree_decomposition_in_charSpace` (SMOObligations:111) `; cuspFormsOld_of_sameLevel_decomposition` (SMOObligations:189).
   **Blocked only by an import cycle:** both ingredients sit in `SMOObligations.lean`, which transitively imports `…GL2.Newforms → Newforms.MainLemma` (where the `Newform` structure is defined). Fix = **file split**: extract the `Newform` structure (+ `Newform.conductor`, `Newform.eigenvalue_eq_coeff`, the char-decomposition lemmas that `Newforms.CoeffSeq` and downstream need) into a low `Newforms/Defs.lean`; move the `mainLemma` theorem + its 2 sub-lemmas into a high file that imports `SMOObligations`. Then `mainLemma_charSpace := mainLemma_charSpace_routeB` and sub-sorry 2 closes. (Pure file-org; no statement change.)

## Available inputs (all proven)
`heckeT_n_adjoint`, `exists_simultaneous_eigenform_basis`, `cuspFormsOld_isCompl_cuspFormsNew` + projections, full `petN` algebra (`petN_definite` etc.), `ConductorTheorem`/`conductor_theorem_dichotomy_cuspForm_strong` (already imported), the Miyake 4.6.8 sieve (`SMOObligations/Lemma4_6_8.lean`, importable). Alternative spectral route A exists but its crux (linear independence of distinct eigensystems) risks circularity and needs `petN`-spanning of the eigenbasis (not exposed).

## Next steps
- [ ] Close sub-sorry 2 via the `Newform`-structure file split (low-risk file-org refactor; touches the LeanModularForms aggregator + `Newforms.lean`/`CoeffSeq` imports — verify with `lake build LeanModularForms`).
- [ ] Close sub-sorry 1: prove `qExpansion ∘ diamondOp` coefficient inheritance, or refactor Miyake 4.6.8 to a character-free sieve so no decomposition/inheritance is needed.
