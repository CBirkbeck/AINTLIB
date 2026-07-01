# GLn Operator-Combinatorics Subtree: Structural Audit

**Scope.** 24 `.lean` files, **~15,950 LOC** across:

* `AbstractHeckeRing/` (7 files, ~3085 LOC) — abstract Hecke pair, double cosets, multiplication, module, associativity, ring, degree, commutativity.
* `GLn/` root (14 files, ~6128 LOC) — concrete `GL_pair n`, diagonal SNF, transvections, projection (Shimura 3.20 induction), congruence-Hecke umbrella.
* `GLn/BlockBijection/` (7 files, ~5904 LOC) — Shimura Lemma 3.19 dim-`(k+1) ↔ (k+2)` Hecke-multiplicity bijection.
* `GLn/CongruenceHecke/` (6 files, ~4911 LOC) — `(Γ₀(N), Δ₀(N))` Hecke pair, Atkin–Lehner anti-involution, polynomial presentation, Shimura Thm 3.35 surjection.
* `GL2/HeckeT_n.lean` (2024 LOC) — the analytic Hecke operator on `M_k(Γ₁(N))`.

**Branch.** `hecke-ring`. **Sorry inventory.** 5 declarations: 2 in `Projection.lean` (`hecke_coeff_compat_gen`, `evalHom_lift_injective`, `evalHom_surj_and_inj`) and 1 in `BlockBijection/FiberPreimageJ.lean` (`fiber_has_block_form_preimages`), plus 2 `sorry`s in `PolynomialRing.lean` (`R_p_isPolynomialRing`'s general-`n` branch) — **all gated behind the general-`n` Shimura 3.20** development and **not on the path** to Thm 3.35 at `n = 2`, the four protected headlines, or `[propext, Classical.choice, Quot.sound]` cleanliness.

## 1. Family Sprawl

Four overlapping family hierarchies are all alive simultaneously:

| Family | Sample carriers | Where defined | Active? |
|---|---|---|---|
| Abstract `(H, Δ)` | `HeckePair`, `𝕋 P Z`, `decompQuot` | `AbstractHeckeRing/Basic.lean` | Yes — foundation |
| `(SL_n(ℤ), Δ_n)` for `n ≥ 1` | `GL_pair n`, `T_diag a` | `GLn/Basic.lean`, `GLn/DiagonalCosets.lean` | Yes |
| `(Γ₀(N), Δ₀(N))` (level only at `n=2`) | `Gamma0_pair N` | `GLn/CongruenceHecke/Foundation.lean` | Yes — Thm 3.35 |
| `(Γ₁(N), Δ₁(N))` (level only at `n=2`) | `Gamma1_pair N` | `GL2/Gamma1Pair.lean` (!!) | Yes |
| `Γ(N)` slash | `CongruenceSubgroup.Gamma N` (mathlib) | imports only | Sparse |
| Prime vs prime-power vs general `n` | `heckeT_p_all`, `heckeT_ppow`, `heckeT_n` | `GL2/HeckeT_n.lean` | All three live, used by recurrence step |
| Coprime vs `p | N` (bad prime) | `diamondOp_ext`, `diamondOp_n`, `heckeT_p_divN` | `GL2/HeckeT_n.lean` | Live, force `if h : Nat.Coprime p N` dichotomy everywhere |
| Block-embedded `(k+1) → (k+2)` vs non-block | `diagMat_delta (Fin.cons 1 a)` vs `diagMat_delta a` | `BlockBijection/` (entire subtree) | Live, but isolated (see §6) |

**Most painful sprawl:**

* `Gamma0_pair N` is in `HeckeRIngs/GLn/CongruenceHecke/` while `Gamma1_pair N` is in `HeckeRIngs/GL2/Gamma1Pair.lean` — **same shape, different namespace, different parent directory**. There is no reason `Gamma1Pair.lean` couldn't be `GLn/CongruenceHecke/Gamma1_pair.lean`.
* The `GLn/` and `GL2/` split is fictional: every consumer of `GLn/CongruenceHecke/*` is at `n = 2`. The "GLn" name only refers to `GL_pair n` from `GLn/Basic.lean`; the `CongruenceHecke/` subtree is pinned to `Fin 2`.
* Block-embedded vs non-block: `(Fin.cons 1 a)` appears **639 times** across `GLn/`, almost entirely in `BlockBijection/` which is gating dim-induction nobody currently needs.

## 2. Hypothesis Sprawl

The recurring **8-hypothesis stanza** appears across `CoprimeMul.lean`, `DiagonalCosets.lean`, `BlockBijection/*.lean`, `BlockBijection/SLReduction.lean`:

```
(a b c : Fin (k+1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
(hda : DivChain (k+1) a) (hdb : DivChain (k+1) b) (hdc : DivChain (k+1) c)
```

Sample count in `BlockBijection.lean` alone: this 8-tuple recurs in `heckeMultiplicity_block_embed_le_diagMat`, `..._target_mulMap`, `..._ge_diagMat`, `..._target_mulMap_sandwich`, `..._via_iFunctional`, `..._direct`, `..._sorryFree`, `..._sandwich_sorryFree` — **eight variants** of the same statement.

Other sprawl signatures:
* `(p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)` triplet ubiquitous in `HeckeT_n.lean`, `HeckeT_p.lean`, `HeckeT_p_Gamma0.lean`, `HeckeT_p_Gamma1.lean`.
* `[NeZero N] [NeZero n] [NeZero m]` instances per-lemma rather than per-namespace.
* `(σ : SpecialLinearGroup (Fin n) ℤ)` is restated in every BlockBijection lemma rather than `variable`-ed.

**Sandwich-hypothesis explosion in BlockBijection.lean.** `heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sandwich_sorryFree`'s **eight-character version-suffix wart** (`_target_mulMap`, `_sorryFree`, `_sandwich`, `_via_iFunctional`, `_direct`, `_corrected_j`, `_canonical_j`) is documenting the workflow of "I split this in half because the original proof was blocked"; it is not load-bearing math.

## 3. Redundant Structures

* **Two `heckeMultiplicity` definitions.** `heckeMultiplicity P g₁ g₂ d` (set-form, rep-dependent: `{i.out g₁}·{j.out g₂}·H = {d}·H`) and `heckeMultiplicityMulMap P g₁ g₂ d` (rep-invariant: `mulMap (i,j) = ⟦d⟧`). Their equivalence is `heckeMultiplicity_le_heckeMultiplicityMulMap` — they are equal in value but the **set form is what `m` (the multiplication finsupp) is defined from, while every Block-bijection downstream argument prefers the mulMap form**. Result: 20 references to `heckeMultiplicityMulMap` in `BlockBijection.lean` that exist only to bridge.
* **Two `slSuccEmbed` definitions.** `private noncomputable def slSuccEmbed` lives at `DiagonalCosets.lean:743` **and** `BlockBijection/BlockEmbed.lean:28` (the latter is public; the former is private within `DiagonalCosets.lean` but its private status is the only thing keeping it from conflicting). Same statement, same type.
* **Three `private lemma mapGL_injective`.** `GLn/Basic.lean:114`, `GLn/Degree.lean:114`, `BlockBijection/BlockEmbed.lean:78` — each a 2-line wrapper around mathlib's `SpecialLinearGroup.mapGL_injective`.
* **Two `private lemma smulOrbit_map_injective` ≈ `smulOrbit_map_inj`.** `AbstractHeckeRing/Associativity.lean:35` and `AbstractHeckeRing/Degree.lean:66`. Both abstract HeckeRing files, **literally adjacent**, redefining the same private lemma.
* **Two `conjAct_mem_of_subgroupOf` / `conjAct_inv_mem_of_subgroupOf`.** Abstract `AbstractHeckeRing/Associativity.lean` (140, 149) and `Commutativity.lean:153` (as `conj_mem_of_stabilizer`); then re-stated for `GL (Fin n) ℚ` in `BlockBijection/HeckeMultBridge.lean:25, 33`. Four total copies of one fact.
* **Two `mk_out_coe_eq_mul` ≈ `decompQuot_out_coe_eq_mul`.** Same lemma, abstract form `AbstractHeckeRing/Associativity.lean:156`, concrete form `BlockBijection/HeckeMultBridge.lean:89`.
* **Misnamespaced file:** `BlockBijection/AbstractHeckePair.lean` opens `namespace HeckeRing` (no `.GLn`), but lives in the `HeckeRIngs/GLn/BlockBijection/` directory. It belongs in `AbstractHeckeRing/`.
* **Two `T_sum_mul`-shaped divisor identities.** `GL2/MultiplicationTable.lean:T_sum_mul` (formal ring identity) and `GL2/HeckeT_n.lean:heckeT_n_mul` (analytic operator identity). They have the same divisor-sum shape with the same `∑_{d|gcd m n} d^{k-1} · ⟨d⟩ · T_{mn/d²}` formula, but one lives in the abstract Hecke ring (`T_ad d d * T_sum_nat ...`) and one is a slash-action operator on `ModularForm`. The unification path — applying `shimura_thm_3_35`-style surjections to descend — exists but is unused; the second identity is reproved from scratch with prime-power induction.

## 4. Duplicate Proof Bodies

* **`heckeT_ppow_mul` (HeckeT_n.lean:1526) ↔ `T_sum_ppow_mul` (MultiplicationTable.lean:812).** Both are the prime-power identity `T_{p^r}·T_{p^s} = Σ_{i=0}^{min} p^i · ⟨p⟩^i · T_{p^{r+s−2i}}` for `r ≤ s`. The combinatorics of the sum decomposition is **the same** (`Finset.sum_range`, `heckeT_ppow_mul_summand_eq`, `heckeT_ppow_mul_boundary_eq`, `heckeT_ppow_mul_step` mirror `T_sum_ppow_mul_summand_split`, `T_sum_ppow_mul_lhs1_distrib`, `T_sum_ppow_mul_step`). Each chain takes ~100 LOC.
* **`heckeT_n_mul` (HeckeT_n.lean:1963) ↔ `T_sum_mul` (MultiplicationTable.lean:1101).** Both prove `T_m T_n = Σ_{d|gcd} ...`. The reduction-by-minFac strong-induction is duplicated almost word-for-word.
* **`heckeT_p_all_comm_distinct` (HeckeT_n.lean:966) ↔ `T_ad_mul_of_coprime` (MultiplicationTable.lean:839).** Both encode coprime-multiplicativity at primes.
* **`gcd_factor_prime_pow` / `gcd_eq_gcd_ordCompl_mul_pow_min`.** Combinatorial lemma about `gcd m n = g' · p^(min)`: present in `MultiplicationTable.lean:963` and again as `gcd_eq_gcd_ordCompl_mul_pow_min` in `HeckeT_n.lean:1845`.
* **`mulMap_T_one_eq` (Multiplication.lean:227) and `mulMap_one_T_eq` (Multiplication.lean:344).** The lemmas asserting that the identity coset acts as identity on the right (227) and on the left (344) **share their proof skeleton**: both call `HeckeCoset.eq_iff`, `mul_assoc`, `doset_mul_left_eq_self`/`doset_mul_right`. The latter is just the former with sides swapped.
* **Right/left versions of `nonempty_mul_one_witness_of_dcRel` and `nonempty_one_mul_witness_of_dcRel`** (Multiplication.lean:285, 501). 22 LOC each, mirror-image structure.
* **`heckeMultiplicity_mul_one` and `heckeMultiplicity_one_mul`** (Multiplication.lean:313, 550). Both `⟦g₁⟧ = ⟦d⟧ ↔ heckeMultiplicity P g₁ T_one d = 1`. Same proof, sides swapped.
* **Right/left versions of `heckeMultiplicity_mul_one_eq_zero` / `_one_mul_eq_zero` / `m_mul_one_eq_single` / `m_one_mul_eq_single`** (Multiplication.lean:662–712).
* **`conjugate_congruent_mem_SLnZ` (CoprimeMul.lean:428) and `inv_conjugate_congruent_mem_SLnZ` (CoprimeMul.lean:470).** 42 LOC each; identical except the conjugation goes `A⁻¹·γ·A` versus `A·γ·A⁻¹`. Already mirrors `conj_ker_mem_SLnZ` / `conj_ker_mem_SLnZ_inv` from `Basic.lean:205, 276` — a **two-by-two mirror grid** of the same fact.
* **`conj_dvd_reverse`, `conj_mat_det_one_reverse`, `int_mul_eq_reverse` in `GLn/Basic.lean:233–272`** are reverse copies of `adjugate_conj_dvd`, `conj_mat_det_one`, `int_mul_eq` from the same file. All six are private; the "reverse" half exists only to give the `g_GL · (γ_GL) · g_GL⁻¹` form needed in `conj_ker_mem_SLnZ_inv`.

## 5. Cross-File Redundancy

* **`Foundation.lean` reproves `mapGL`-image commensurability** (`Gamma0_map_commensurable_SLnZ:96`) duplicating the structure of `posDetInt_le_commensurator` in `Basic.lean:351`. The whole Shimura-Lemma-3.10 ker-decomposition pattern is repeated.
* **`HeckeT_p_Gamma0_Bridge.lean`** consists almost entirely of one-line wrappers passing `HeckePairAction.adjugate_mem_H` and `Gamma0_pair N`.H membership through chained `mul_mem` — this is generic Hecke-pair plumbing that should live in `AbstractHeckeRing/`.
* **`HeckeT_p_GLpair.lean`** rebuilds the same coset-counting argument that `D_p_Gamma0` (GLn) and `D_p_Gamma1` (GL2) each get separately. Three near-identical `decompQuot` cardinality proofs.
* **`heckeT_p_ut_orbit_comm_gamma0` (HeckeT_n.lean:729) and `orbit_upper_gamma0` (HeckeT_p.lean:402)** both compute the Möbius-style action of `Γ₀(N)` on `T_p_upper b`. The structure (case-split on `b ∈ Fin p`, `moebiusFin` reindexing, `dvd_topLeft_add_canonicalIndex`) is shared.
* **`SLnZ_to_GLnQ_det` / `SLnZ_to_GLnQ_val` (MultiplicationTable.lean:37, 45)** are noted in their docstring as "replaces removed lemmas" — they're literally restoring deleted mathlib helpers that should live in `GLn/Basic.lean`.

## 6. Mathlib-Redo Opportunities

* **`HeckePair` and `𝕋 P ℤ`**: the structure `HeckePair` (`H ≤ Δ ≤ commensurator H`), the double-coset quotient, the multiplication via decomposition quotients, the degree map, and the proof that `𝕋 P ℤ` is a non-unital semiring — **none of this is `GL`-specific**. This is general arithmetic-group Hecke theory and belongs in `Mathlib.GroupTheory.DoubleCoset` / a new `Mathlib.GroupTheory.HeckeRing` file. The development is ~3085 LOC and very modular.
* **`AntiInvolution` / commutativity via fixed double cosets.** Shimura Prop 3.8 (`Commutativity.lean`, 449 LOC) is pure group theory. Belongs in mathlib alongside `HeckePair`.
* **`set_eq_iUnion_leftCosets`** (Basic.lean:238) and **`DoubleCoset.doubleCoset_eq_iUnion_leftCosets`** (Basic.lean:286) are not yet in `Mathlib.GroupTheory.DoubleCoset`. They should be PR'd up.
* **`SL2_reduction_surjective`** (GLn/SL2Surjection.lean:174) — strong approximation for `SL₂(ℤ) → SL₂(ℤ/dℤ)` — is a mathlib gap. Should be `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` upstream.
* **`slTransvecG` / `IsTransvec`** (SLnTransvection.lean) reimplements `Matrix.transvection` from mathlib (`Mathlib.LinearAlgebra.Matrix.Transvection`). The mathlib `TransvectionStruct` exists, `transvection_mul_transvection_same` exists, etc. — but the project's `slTransvecG` is at the `SpecialLinearGroup` level rather than the `Matrix` level. The wrapper is justified; the **internal lemmas** (`slTransvecG_mul`, `slTransvecG_inv`, `slTransvecG_zero`, etc.) duplicate `Matrix.transvection_*` results.
* **`exists_diagonal_of_posdet` / `exists_divchain_diagonal_of_posdet`** (DiagonalCosets.lean:349, 865) is **Smith Normal Form for integer matrices with positive determinant**. Mathlib has `Submodule.exists_smith_normal_form_of_le` for PID modules but not in elementary-matrix form. This 500-LOC custom-rolled SNF (with all the `fin1Sum`, `finEquivSum`, `genEquiv` `Fin (k+2) ≃ Fin 2 ⊕ Fin k` reindexings) should be replaced by mathlib's PID SNF + matrix↔module bridge.
* **`Chinese Remainder for SL_n(ℤ)`** (`SLnZ_CRT_decomposition`, CoprimeMul.lean:409) is mathlib-worthy.
* **`HeckeRing.AbstractHeckePair`** (BlockBijection/AbstractHeckePair.lean) — already lives in the wrong namespace (`namespace HeckeRing` not `.GLn`); this is just a sign the file belongs in `AbstractHeckeRing/`. Or, ideally, mathlib.

## 7. Bloat Diagnosis (≤500 words)

**HeckeT_n.lean is 2024 LOC because it bridges three independent recurrences.** First, the **slash-action layer** (lines 60–550): `heckeT_p_all`, `heckeT_ppow`, `heckeT_n_aux`, `heckeT_n` are defined as concrete `f ↦ Σ_b f|γ_b` on `ModularForm ((Gamma1 N).map (mapGL ℝ)) k`, with full holomorphy/`bdd_at_cusps` packaging at each level. Each definition reproves slash-invariance from scratch (`heckeT_p_ut_slash_invariant_divN`, `orbit_upper_divN`, etc.). The bad-prime / coprime-prime dichotomy forces `if h : Nat.Coprime p N then ... else ...` everywhere — `heckeT_p_all_not_coprime_apply` and `heckeT_p_all_coprime_apply` are wrappers around this `dif`. This layer alone is ~600 LOC.

Second, the **divisor-sum manipulation layer** (lines 1500–1950): `heckeT_n_mul` is the operator-level Shimura-3.24(3) identity `T_m·T_n = Σ_{d|gcd} d^{k−1}·⟨d⟩·T_{mn/d²}`. The proof goes by strong induction on `gcd m n`, peeling minimum-prime factors and using `heckeT_n_mul_aux_divisor_sum` (line 1747, 75 LOC), which is itself a `Finset.sum_bij'` between `range(c+1) ×ˢ g'.divisors.attach` and `(g'·p^c).divisors.attach`. The forward map sends `(j, d')` to `p^j · d'`; the backward map is `d ↦ (d.factorization p, d / p^…)`. Both `pow_mul_mem_gcd_divisors` (line 1725) and `ordCompl_mem_divisors_of_dvd_mul_pow` (line 1736) are pure `Nat.factorization` plumbing. Add `factorization_coprime_mul_pow_self`, `factorization_pow_mul_self`, `gcd_eq_gcd_ordCompl_mul_pow_min`, `heckeT_n_aux_mn_div_pjd_eq`, `heckeT_n_mul_aux_divisor_sum_summand` — this is **~300 LOC of `Nat.factorization`/`Nat.divisors` combinatorics** that has nothing to do with Hecke operators per se.

Third, the **sigma-algebra / character-space plumbing layer**: `diamondOp_ext` (the extended diamond that is zero when `p|N`), `diamondOp_n` (general `n`), `diamondOp_ext_comm_diamondOp` (line 1556), `diamondOp_n_pow_mul_eq` (line 1590), `heckeT_ppow_comm_diamondOp` (line 1565), `heckeT_ppow_comm_diamondOp_n` (line 1622), `heckeT_n_aux_comm_diamondOp` (line 1973), `heckeT_n_comm_diamondOp` (line 2002), `heckeT_n_preserves_charSpace` (line 2011). Every operator commutes with every diamond, and each commutation is reproved at the right level. This is ~400 LOC.

The remaining ~700 LOC is the **inductive coprime decomposition** (`heckeT_n_aux`, `heckeT_n_aux_mul_coprime`, `heckeT_n_aux_mul_coprime_minFacL`/`_minFacR`, the cross-multiplication step) — a strong induction on `n`'s minimum prime factor. Each step needs both the slash-action commutativity and the divisor-sum identity, so the three layers are interleaved rather than separable. **The file is not bloated by accident**: it sits on top of three independent recurrences and each one needs its own divisor-sum / coprime-decomposition apparatus repeated at the operator level. The same recurrence proved abstractly in `MultiplicationTable.lean:T_sum_mul` (1144 LOC) is then **redone** here as `heckeT_n_mul` because no Hecke-pair-level → slash-action surjection has been built.

## 8. Reduction Plan (8–15 tickets)

Each ticket preserves `[propext, Classical.choice, Quot.sound]` and the four protected headlines (which all transit `Thm 3.35` at `n=2`, so the `BlockBijection`/`Projection` subtree is downstream-safe to delete or quarantine).

| # | Ticket | Est. LOC saved | Risk |
|---|---|---:|---|
| 1 | **Quarantine `Projection.lean` and `BlockBijection/`** behind a `general-n` namespace. Nothing in the four-headline path consumes them; their sorries (`fiber_has_block_form_preimages`, `hecke_coeff_compat_gen`, `evalHom_lift_injective`, `evalHom_surj_and_inj`) are all for Shimura 3.20 at general `n`. Move under `LeanModularForms/HeckeRIngs/GLn/_GeneralN/` (mirrors `_Sandbox` precedent) and exclude from `lakefile.lean` default target. | ~6300 | Low |
| 2 | **Move `AbstractHeckeRing/` to mathlib track.** Create `Mathlib.GroupTheory.HeckeRing.{Basic,Multiplication,Module,Associativity,Ring,Degree,Commutativity}` and PR. Project re-imports from mathlib. The seven files are written in mathlib style already (private helpers, `variable` blocks, `open scoped`). | ~3085 | Medium (PR review timeline) |
| 3 | **De-duplicate `heckeMultiplicity` / `heckeMultiplicityMulMap`.** Pick the mulMap form as primary (it's rep-invariant and what all downstream lemmas want). Rename the existing `heckeMultiplicity` to `heckeMultiplicitySetForm` (or delete after retargeting `m` to use mulMap). Eliminate the `≤`/`≥` bridge spam. | ~150 | Medium |
| 4 | **Delete `BlockBijection/AbstractHeckePair.lean` after moving its contents to `AbstractHeckeRing/Multiplication.lean`** (it's already in the abstract namespace). | ~50 | Low |
| 5 | **Unify the three `mapGL_injective` private wrappers + two `slSuccEmbed` definitions + two `smulOrbit_map_inj` copies.** Make one canonical version in `AbstractHeckeRing/Basic.lean` (for `smulOrbit_map_inj`) and `GLn/Basic.lean` (for `mapGL_injective`, `slSuccEmbed`). Single file edit affects 8 callers. | ~120 | Low |
| 6 | **Unify the four conjAct-stabilizer-membership lemma copies.** `conjAct_mem_of_subgroupOf` (Associativity), `conj_mem_of_stabilizer` (Commutativity), and two concrete copies in `BlockBijection/HeckeMultBridge.lean`. One abstract version in `AbstractHeckeRing/Basic.lean`, delete three. | ~80 | Low |
| 7 | **Collapse Right/Left mirror duplicates in `AbstractHeckeRing/Multiplication.lean`.** `mulMap_T_one_eq`/`mulMap_one_T_eq`, `nonempty_*_witness_of_dcRel`, `heckeMultiplicity_mul_one_*`/`_one_mul_*`, `m_mul_one`/`m_one_mul`. Introduce a single lemma parameterized by side, derive both. | ~250 | Medium |
| 8 | **Collapse the `conj_*_reverse` mirror sextet in `GLn/Basic.lean`.** `adjugate_conj_dvd` / `conj_dvd_reverse`, `conj_mat_det_one` / `_reverse`, `int_mul_eq` / `_reverse`, `conj_ker_mem_SLnZ` / `_inv`. Lemmas come in pairs (`A⁻¹·γ·A` vs `A·γ·A⁻¹`); parameterize by side. | ~150 | Medium |
| 9 | **Collapse `conjugate_congruent_mem_SLnZ` / `inv_conjugate_congruent_mem_SLnZ` in `CoprimeMul.lean`.** Same mirror pattern. | ~70 | Medium |
| 10 | **Bridge `T_sum_mul` (formal) ↔ `heckeT_n_mul` (analytic) via a slash-action ring homomorphism.** Build `𝕋 (GL_pair 2) ℤ →* Module.End ℂ (ModularForm …)`; derive `heckeT_n_mul` as the image of `T_sum_mul` under it. **~700 LOC saved** from `HeckeT_n.lean`. | ~700 | High (need to design the bridge, possibly part of new mathlib API) |
| 11 | **Replace `exists_diagonal_of_posdet` / `exists_divchain_diagonal_of_posdet` with mathlib SNF.** Replace the ~500-LOC custom SNF (with `fin1Sum`/`finEquivSum`/`genEquiv` Fin-reindexing forest) by `Submodule.smithNormalFormOfRankEq` + matrix-↔-module bridge in mathlib. | ~500 | High (need a clean matrix↔PID-basis bridge in mathlib) |
| 12 | **Move `Gamma1_pair N` from `GL2/Gamma1Pair.lean` into `GLn/CongruenceHecke/Gamma1_pair.lean`.** Restore namespace symmetry with `Gamma0_pair`. Atomic file rename + import fix-up. | ~0 (organization) | Low |
| 13 | **Pull `set_eq_iUnion_leftCosets`, `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`, and `SL2_reduction_surjective` into mathlib PRs.** Three clean mathlib gaps with no downstream churn locally. | ~250 (after mathlib lands) | Low |
| 14 | **Simplify the `diamondOp_ext` dichotomy.** The `if h : Nat.Coprime p N then diamondOp k (ZMod.unitOfCoprime p h) else 0` pattern forces a `dif_pos`/`dif_neg` everywhere. Replace `diamondOp_ext k p` with `diamondOp_n k p` (already defined!); kill the duplicate. The `diamondOp_n` / `diamondOp_ext` split exists only because the file is paranoid about `n : ℕ` vs `p : ℕ` parameter naming. | ~150 | Low |
| 15 | **Consolidate `HeckeT_p_Gamma0_Bridge.lean`** into `HeckeT_p_GLpair.lean`. The Bridge file is one-line wrappers; merge. | ~150 | Low |

**Net reduction (excluding mathlib upstreaming):** ~2100 LOC purely from de-duplication and quarantining; an additional ~3085 LOC migrates to mathlib (still counted in the project until the PR lands). Including the BlockBijection quarantine: **~8400 LOC removed from the active build path** while keeping every protected headline green.

---

## Top 3 Findings (200 words)

1. **The `BlockBijection/` + `Projection/` subtree (≈6300 LOC) is dead code on the path to the four headlines.** Nothing outside `Projection.lean` itself consumes its exports, and `Projection.lean` is only used by `CongruenceHecke/Foundation.lean` for `T_scalar_not_zero_divisor` (which has no callers anywhere). The four sorries (`fiber_has_block_form_preimages`, `hecke_coeff_compat_gen`, `evalHom_lift_injective`, `evalHom_surj_and_inj`) and the two in `PolynomialRing.lean` are all guarding general-`n` Shimura 3.20 that the n=2 surjection `shimura_thm_3_35` does not need. Quarantining this subtree is the single biggest LOC win and removes every project sorry from the default build target.

2. **`HeckeT_n.lean` is 2024 LOC because it reproves at the slash-action level what `MultiplicationTable.lean` already proves at the formal Hecke ring level.** The prime-power recurrence `heckeT_ppow_mul`, the divisor identity `heckeT_n_mul`, and the coprime decomposition `heckeT_n_mul_coprime` are mirror images of `T_sum_ppow_mul`, `T_sum_mul`, and `T_sum_mul_coprime` in `MultiplicationTable.lean`. The missing piece is a slash-action ring homomorphism `𝕋 (GL_pair 2) ℤ →* Module.End ℂ (ModularForm …)`; building it would let `heckeT_n_mul` follow from the abstract identity, saving ~700 LOC.

3. **`AbstractHeckeRing/` (≈3085 LOC) is mathlib-worthy infrastructure that currently lives in this repo.** `HeckePair`, `HeckeCoset`, `𝕋 P Z`, `decompQuot`, the degree ring homomorphism, the `IsScalarTower` proof of associativity, and the `AntiInvolution`-based commutativity criterion are all pure-group-theory facts. Upstream as `Mathlib.GroupTheory.HeckeRing.*` and the entire subdirectory becomes a stub.

**File path:** `/Users/mcu22seu/Documents/GitHub/LeanModularForms-hecke/.mathlib-quality/gln-overview-2026-05-31.md`
