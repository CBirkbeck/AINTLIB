# Project Overview: Chebotarev

**Generated:** 2026-06-17
**Project:** `projects/Chebotarev/` (`CebotarevDensity`) in `CBirkbeck/AINTLIB`
**Sources:** synthesized from the Stage-1 per-file inventories (`overview/inventory/*.md`, 14 files) and the Stage-2 analyses (`overview/analysis/04`–`07`). This is a consolidation document; no re-analysis was performed.

## Executive Summary

This project gives a complete, `sorry`-free Lean formalisation of the **Chebotarev density theorem** for a finite Galois extension `L/K` of number fields. The headline result, `Chebotarev.chebotarev_density` (`Main.lean`), states that the set of primes `𝔭` of `𝓞 K` unramified in `L` whose Frobenius conjugacy class equals a fixed class `C` has Dirichlet density `|C| / |Gal(L/K)|` (Sharifi *Algebraic Number Theory* §7.1–7.2). Two corollaries are also proved at the top level: `density_split_completely` — the primes that split completely have density `1/[L:K]` — and `dirichlet_primes_in_AP` — Dirichlet's theorem on primes in arithmetic progressions (`K = ℚ`, `L = ℚ(μ_n)`) as the density refinement `1/φ(n)`. The proof is CFT-free: it routes the conjugacy-class statement through the cyclic case (a fixed-field subextension `E = L^⟨σ⟩`), the abelian case (a cyclotomic-crossing / pigeonhole argument), and the cyclotomic case (Artin L-series of characters `Gal(L/K) →* ℂˣ`, their Dirichlet-density asymptotics, and a self-contained geometry-of-numbers ideal-count). The analytic backbone is the Dedekind-zeta Euler product and the asymptotic `Σ_𝔭 N𝔭^{-s} ~ log(1/(s-1))` as `s ↓ 1`.

The project is in excellent shape for cleanup. Across **15 files (one a pure aggregator) and 441 declarations there are 0 `sorry` and 0 `set_option`**; the entire dependency chain down to the cyclotomic-crossing and Carmichael-function number-theory leaves is discharged. Five of the files form a deliberate `ForMathlib/` upstreaming surface (133 declarations, root-namespaced, author-earmarked for mathlib).

The top consolidation findings: (1) **34 proofs exceed 50 lines** and want a re-`/decompose-proof` pass — they cluster in the two giant geometry-of-numbers / Euler-product files (`IdealCongruenceCount` 11, `ZetaProduct` 9). (2) **Strong de-duplication opportunities**: the `≥120`-line log-asymptotic "Dirichlet ratio → 1 when the complement is finite" squeeze is replicated across three decls; `2 ≤ N𝔭` exists in 3 copies + 2 inlinings; the Frobenius-descent pair and the cyclotomic coprime-norm⇒unramified lemma are each explicit `_repl`/replica copies (the producer made them private, then re-derived them). (3) A clear split among the `ForMathlib/` decls between **genuinely-new mathlib contribution candidates** (character orthogonality over `HasEnoughRootsOfUnity`; the effective lattice-point count; the Dirichlet-density predicates; several `Ideal.absNorm`/`ZLattice` bridges) and **delete-and-use-mathlib** decls that are thin composites of existing API (`charEval`, `lipschitzWith_exp_ofReal_mul_I`, `map_span_int_linearEquiv`, the `IsEquivalent` squeeze).

The per-declaration `/mathlibable` (Step 9) pass was intentionally **not run** — it is deferred pending a retune of the `/mathlibable` skill. Stage 2 nonetheless flagged a ready worklist of genuinely-new vs. generalise-first candidates (see Part 8).

## Statistics

| Metric | Value |
|---|---|
| Files | 15 (1 pure aggregator: `CebotarevDensity.lean`) |
| Declarations | 441 |
| `sorry` | **0** |
| `set_option` | **0** |
| Proofs > 50 lines (decompose-needed) | **34** |
| `ForMathlib/` files / decls | 5 files / 133 decls (root-namespaced, upstream surface) |
| Moral duplications (Stage 5) | ~31 pairs/groups examined; 4 within-project UNIFY families + 1 dead-code + 4 DUP-of-mathlib + ~7 BORDERLINE-mathlib |
| Generalisation opportunities (Stage 6) | 11 actionable (5 Low / 5 Med / 1 High) + 4 assessed no-action |
| API improvements (Stage 7) | 10 (4 HIGH extractions, 2 MED relocations, 1 instance group, 3 completeness) |
| Junk / removable (Stage 7/8) | **7 genuine** (REMOVE/REPLACE/INLINE); **~30+** "unused-but-public" → KEEP (terminal exports) |
| Mathlibable (Step 9) | **DEFERRED** — `/mathlibable` skill retune pending (see Part 8) |

## Part 1: Declaration Inventory

Compact per-file summary. "Key API" = the most-reused in-file declaration(s) (used by ≥ 3, else the project-central object). "Unused" counts decls with no in-file consumer — for this project these are almost all intentional terminal/cross-file exports, not dead code. Full per-declaration detail (statement, proof sketch, uses, line ranges) lives in `inventory/<file>.md`.

| File | Decls | Key API | Unused (terminal exports) | Proofs > 50 |
|---|---|---|---|---|
| `CebotarevDensity.lean` (aggregator) | 0 | — (15 `public import`s + module docstring) | 0 | 0 |
| `Density.lean` | 30 | `primeIdealZetaSum`, `primeIdealZetaSum_def`, `HasDirichletDensity` | 10 (the `HasDirichletDensity.*` API surface) | 0 |
| `Frobenius.lean` | 22 | `UnramifiedIn` (def, 11 uses), `UnramifiedIn.finite_quotient` | 4 (`card_primesAbove_mul_orderOf_eq`, `finite_ramifiedIn`, `finite_badPrimes`, the private instance) | 0 |
| `NumberFieldEulerProduct.lean` | 36 | `NonzeroIdeal`, `idealNormMultiplicity` | 7 (`dedekindZeta_eq_tprod_primeIdeal`, `…re_pos…`, `hasSum_nonzeroIdeal_absNorm_cpow`, …) | 3 |
| `ZetaProduct.lean` | 84 | `galoisCharacter`, `galoisCharacterOnIdeal`, `frobeniusIdeal`, `artinDirichletSeries` | `artinLSeries_one_ne_zero` + headline exports | 9 |
| `CyclotomicNormResidue.lean` | 14 | `unramifiedIn_intermediateField`, `finrank_residue_fixedField_eq_one` | `autToPow_frobeniusClass_out`, `subgroup_eq_top_of_forall_frobenius_mem` | 1 |
| `Cyclotomic.lean` | 27 | `twistedPrimeSum` (def, 6 uses), `unramifiedPrime_toPrimeNeBot_injective` | `chebotarev_cyclotomic_lowerDensity_ge`, `log_artinLSeries_asymp_character_sum` | 2 |
| `FixedFieldDensity.lean` | 26 | (deep linear chain; most-reused used by 2) | `density_lift_through_fixedField` | 2 |
| `Abelian.lean` | 46 | `cyclotomicField_finrank_eq` (3 uses) | `chebotarev_abelian`, `cyclic_subgroup_meets_G_times_one_trivially`, `H_n_over_H_tends_to_one` | 4 |
| `Main.lean` | 23 | `chebotarev_density` (3 uses) | `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, `density_split_completely`, `dirichlet_primes_in_AP` | 0 |
| `ForMathlib/CharacterOrthogonality.lean` | 5 | `sum_eq_zero_of_mulLeft_mul_const_aux` (private engine) | `sum_char_self_eq_zero_of_ne_one`, `eq_of_sum_char_mul_eq_zero` | 0 |
| `ForMathlib/IdealCongruenceCount.lean` | 85 | `cardNormLeResidueClass` (11), `cardNormLeResidueClassDvd` (8), `map_span_int_linearEquiv` (≥5) | 4 public terminals (workhorse + 3 residue-count exports) | 11 |
| `ForMathlib/LatticePointCount.lean` | 9 | `setFinite_index_image_of_isBounded` (3 uses) | `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` | 2 |
| `ForMathlib/LogOneDivSubOne.lean` | 3 | (3 decls; each used once) | `tendsto_ratio_one_of_log_pm_bounded` | 0 |
| `ForMathlib/NormLeOneLipschitz.lean` | 31 | `clampUnit`, `faceMapZero`/`faceMapSide`, `frontierCoverFamily`, `liftToMixed` | `normLeOne_frontier_lipschitz_cover`, `…_index` | 0 |
| **Total** | **441** | | | **34** |

(Per-file decl counts sum to 441; the aggregator contributes 0. The 5 `ForMathlib/` files = 133 decls = `5 + 85 + 9 + 3 + 31`.)

## Part 2: Cross-File Dependencies

The dependency spine, reconstructed from the inventories' "Uses from project" / "Used by" fields. The umbrella file re-exports everything; the mathematics flows bottom-up from the `ForMathlib/` helpers and the analytic/algebraic infrastructure into the three case-files and finally `Main`.

**Umbrella (re-export only):**
`CebotarevDensity.lean` — 15 `public import`s of all submodules; declares nothing. The headline theorem lives in `Main`.

**`ForMathlib/` foundations (root-namespaced, no project deps among most):**
- `LogOneDivSubOne` → provides `tendsto_log_one_div_sub_one_atTop`, `tendsto_ratio_one_of_log_pm_bounded` (the `s ↓ 1` log squeeze) → consumed by `Density`.
- `CharacterOrthogonality` → `sum_char_apply_eq_zero_of_ne_one` (column), `sum_char_self_eq_zero_of_ne_one` (row), Fourier inversion `eq_of_sum_char_mul_eq_zero` → consumed by `Cyclotomic` (orthogonality) and `IdealCongruenceCount` (the `hF`/uniformity step).
- `LatticePointCount` → effective boundary-cell count `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` → consumed by `IdealCongruenceCount`.
- `NormLeOneLipschitz` → frontier Lipschitz-cover `normLeOne_frontier_lipschitz_cover_index` → consumed by `IdealCongruenceCount`.
- `IdealCongruenceCount` (the 3437-line geometry-of-numbers engine) → consumes `LatticePointCount` + `NormLeOneLipschitz` + `CharacterOrthogonality`; exports the workhorse `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` and the residue-count results `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le[_uniform]`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` → consumed by `ZetaProduct` (the κ-uniform transfer).

**Analytic / algebraic infrastructure:**
- `NumberFieldEulerProduct` → `dedekindZeta_eq_tprod_primeIdeal`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_re_pos_of_one_lt`, `NonzeroIdeal`, `idealNormMultiplicity` → consumed by `Density` and `ZetaProduct`.
- `Density` → defines `primeIdealZetaSum` + the three density predicates; proves `primeIdealZetaSum_univ_tendsto_log` (Sharifi 7.1.12), the finite-set density-0 engine, and the `HasDirichletDensity.*` API → consumed by every case-file.
- `Frobenius` → defines `UnramifiedIn`, `frobeniusClass`; proves `orderOf_eq_finrank_of_isArithFrobAt` (flagged API gap), the count×degree identities, `finite_ramifiedIn`, `finite_badPrimes` → the project-wide arithmetic vocabulary, pervasive.
- `ZetaProduct` → Artin L-series machinery: `galoisCharacter`, `galoisCharacterOnIdeal`, `frobeniusIdeal`, `artinDirichletSeries`, the abelian Euler product, the analytic extension `artinLSeries_analytic_extension` (LF4) and non-vanishing `artinLSeries_one_ne_zero` (LF5), and the L2/geometry-of-numbers κ-uniformity → consumed by `Cyclotomic`.

**Case chain (the three reductions):**
- `CyclotomicNormResidue` → cyclotomic Frobenius = norm residue (`autToPow_frobeniusClass_out`), "Frobenii generate" (`subgroup_eq_top_of_forall_frobenius_mem`) → consumed by `ZetaProduct`/`Cyclotomic`.
- `Cyclotomic` → `chebotarev_cyclotomic` (density `1/|G|` on a Frobenius fibre for `L = K(μ_m)`), built on the Artin L-series asymptotics + character orthogonality + `primeIdealZetaSum_univ_tendsto_log` → consumed by `Main` (Dirichlet AP) and `Abelian`.
- `FixedFieldDensity` → `density_lift_through_fixedField` (cyclic Step 1: lift the `1/|Gal(L/E)|` fibre density over `E = L^⟨σ⟩` to `|C|/|G|` over `K`) → consumed by `Main`/`Abelian`.
- `Abelian` → `chebotarev_abelian` (Step 2: cyclotomic-crossing C1–C5 + an `H_n`/Carmichael pigeonhole) → consumed by `Main`.
- `Main` → `chebotarev_density` = reduce class form to cyclic via `density_lift_through_fixedField` + `chebotarev_abelian`; then `density_split_completely`, `infinite_setOf_frobenius_class`, `dirichlet_primes_in_AP`.

## Part 3: Mathlib API Audit

(From `analysis/04-mathlib-api-audit.md`. Scope: every `def`/`abbrev` plus the project's core concepts and the 5 `ForMathlib/` files. Verdict legend: REPLACE / GENERALISE / USE-MATHLIB-API / KEEP / RENAME.)

**Definitions to REPLACE with mathlib (thin wrappers — delete/inline):**
- `charEval` (`ZetaProduct:248`) — body **is literally** `(CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ`, the canonical Pontryagin evaluation map already in mathlib (`Mathlib.GroupTheory.FiniteAbelian.Duality`, already imported). Delete `charEval`/`charEval_apply`; only `charEval_ker_card` is worth keeping, restated about the evaluation hom.
- `lipschitzWith_exp_ofReal_mul_I` (`NormLeOneLipschitz:369`) — it is `circleMap 0 1`; mathlib `lipschitzWith_circleMap 0 1` gives it. Replace call sites (one-line `simp [circleMap]`); do not upstream.
- `map_span_int_linearEquiv` (`IdealCongruenceCount:646`) — `Submodule.map_span (f.restrictScalars ℤ)` + `congrArg coe`. Replace the ~5 call sites; too trivial to upstream.
- `dist_mul_le_norm_mul_dist` (`NormLeOneLipschitz:360`) — generic normed-field product-distance; 3-line proof from `norm_add_le` + `norm_mul`. USE-MATHLIB-API / inline at its single transitive call site, or upstream to `Normed/Field/Basic` if no near-duplicate found.

**API-poor → API-rich abstraction (the highest-impact findings):**
- **Character orthogonality (`ForMathlib/CharacterOrthogonality.lean`) → mathlib `AddChar`.** The four public theorems are textbook finite-abelian orthogonality/Fourier inversion stated for the multiplicative dual `G →* ℂˣ`. `sum_char_self_eq_zero_of_ne_one` **is** `AddChar.sum_eq_zero_of_ne_one` (REPLACE after the `MonoidHom ↔ AddChar` translation). The column lemma is the double-dual instance via `CommGroup.monoidHomMonoidHomEquiv` (GENERALISE/derive). The Fourier-inversion pair should be rebuilt on the `AddChar` orthogonality lemmas (USE-MATHLIB-API). This is the single biggest dedup win.
- `tendsto_ratio_one_of_div_atTop_pm_bounded` (`LogOneDivSubOne:60`) → `Asymptotics.IsEquivalent` (`isEquivalent_iff_tendsto_one`). The file's own docstring already cites the `IsLittleO`/`IsEquivalent` API; the proof should route through it.
- `clampUnit` + `lipschitzWith_clampUnit` (`NormLeOneLipschitz:86`) → `LipschitzWith.projIcc` + `LipschitzWith.pi` (prove the pi-Lipschitz directly, drop the bespoke `lipschitzWith_one_of_edist_apply_le`).
- `lipschitzWith_one_of_edist_apply_le` (private) → `LipschitzWith.pi` / `.eval` (likely deletable; fills a confirmed mathlib gap if kept and generalised — see Part 5 #6).

**KEEP (genuinely new), verify-only / contribute beside existing API:**
- `realizedResidues` (`ZetaProduct`) — genuine `Subgroup (ZMod m)ˣ`; verify it is not more cleanly `MonoidHom.range`/`Subgroup.closure` of the norm-residue hom, else KEEP.
- Density predicates `HasDirichletDensity`/`Upper`/`Lower` (`Density:60`) — correctly use `Tendsto`/`limsup`/`liminf`; mathlib has no Dirichlet-density-of-primes notion, so genuinely new (Sharifi 7.1.13) and good verbatim upstream candidates.
- `Set.Finite`/`Nat.card` counts in the geometry-of-numbers files — modern mathlib idiom; **no blanket `Set.Finite → Finset` change warranted**. The `unitPartition.index`-image refinements belong beside mathlib's existing `index` API.
- `tendsto_div_atTop_of_sub_mul_rpow_le`, `exists_sub_mul_rpow_le_of_div` (`IdealCongruenceCount`) — purely analytic "`|f N − κN| ≤ C·N^{1−1/d}` ⇒ ratio limit / floor transfer"; candidates for `Mathlib.Analysis`.
- The ideal-norm / lattice bridges (`relIndex_*_eq_absNorm`, `absNorm_coprime_of_isCoprime_span`, `covolume_image_basisFun_eq_abs_det`, `exists_mk0_eq_absNorm_coprime`, `crt_single_coset`, `natCast_algebraNorm_add_nsmul_mul`, `norm_eq_prod_real_emb_mul_prod_complex`) — search-then-KEEP, contribute beside `Ideal.absNorm`/`ZLattice.covolume`/`ClassGroup` with the `Chebotarev` namespace stripped.
- The Artin L-series defs (`galoisCharacterOnIdeal`, `frobeniusIdeal`, `galoisCharacterCoeff`, `artinDirichletSeries`), NT predicates (`UnramifiedIn`, `frobeniusClass`), and the `expMapBasis`/`mixedEmbedding`-specific frontier-cover machinery (`faceMap*`, `cubeRelabel`, `frontierCoverFamily`, `mixedCubeEquiv`, `liftToMixed`) are project-specific and the real contribution.

**RENAME:** `Nat.le_iff_le_mul_div_of_dvd` (`IdealCongruenceCount:2112`) — generic `Nat` floor/dvd lemma declared **in the `Nat.` namespace** (clobber risk for a ForMathlib decl); rename out of `Nat.` regardless of dup status.

**Top-5 highest-impact (orchestrator view):** (1) `charEval → CommGroup.monoidHomMonoidHomEquiv`; (2) `CharacterOrthogonality.lean → AddChar` (rebase all four + drop the private aux); (3) `tendsto_ratio_one_of_div_atTop_pm_bounded → IsEquivalent`; (4) `clampUnit`/Lipschitz-pi → `LipschitzWith.projIcc` + `.pi`, and `lipschitzWith_exp_ofReal_mul_I → lipschitzWith_circleMap`; (5) `map_span_int_linearEquiv → Submodule.map_span`, inline `measureReal_biUnion_box`/`dist_mul_le_norm_mul_dist`, RENAME `Nat.le_iff_le_mul_div_of_dvd`.

## Part 4: Moral Duplications

(From `analysis/05-duplications.md`. `𝓞K`, `N𝔭 = Ideal.absNorm 𝔭`, `Gal(L/K) = L ≃ₐ[K] L`.)

### Pairwise comparison table

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `Density.two_le_absNorm_of_prime` | `Cyclotomic.two_le_absNorm_prime` | Yes (A casts to ℝ) | Yes (`lia`) | UNIFY |
| `Cyclotomic.two_le_absNorm_prime` | `ZetaProduct.two_le_absNorm` | B generalises (any Dedekind, free+finite/ℤ) | Yes | special-case → keep B |
| `Density.two_le_absNorm_of_prime` | `ZetaProduct.two_le_absNorm` | B generalises; A is ℝ-cast `𝓞K` case | Yes | special-case → keep B |
| `NumberFieldEulerProduct.norm_absNorm_cpow_neg_lt_one` (inlined `2≤N𝔭`) | `ZetaProduct.two_le_absNorm` | sub-fact re-derived inline | Yes | UNIFY (factor out) |
| `FixedFieldDensity.absNorm_rpow_neg_le_under_sq` (inlined `2≤N𝔭`) | `ZetaProduct.two_le_absNorm` | sub-fact inlined | Yes | UNIFY (factor out) |
| `Density.absNorm_rpow_neg_lt_one` | `NumberFieldEulerProduct.norm_absNorm_cpow_neg_lt_one` | same idea (ℝ vs ℂ) | same | keep-both (real vs complex) |
| `Main.unramifiedIn_cyclotomic_of_coprime` | `ZetaProduct.unramifiedIn_of_coprime_absNorm` | **Identical** | **Identical** (docstring: "Replica") | UNIFY (delete replica) |
| `Abelian.smul_algebraMap_eq_repl` | `CyclotomicNormResidue.smul_algebraMap_eq` | same fact (tower vs intermediate field) | same (`_repl`) | UNIFY (tower form generalises) |
| `Abelian.isArithFrobAt_restrictNormal_repl` | `CyclotomicNormResidue.isArithFrobAt_restrictNormal` | same fact (tower vs intermediate field) | same (replica) | UNIFY (tower form generalises) |
| `Cyclotomic.primeIdealZetaSum_unramified_div_log_tendsto_one` | `CyclotomicNormResidue.primeIdealZetaSum_unramified_coprime_div_log_tendsto_one` | differ only in the "good" set | **Same 4-step proof** | UNIFY → one `…_of_finite_compl` lemma |
| `Cyclotomic.sum_galoisCharacter_eq_card_or_zero` | `CharacterOrthogonality.sum_char_apply_eq_zero_of_ne_one` | A = if-packaged superset | A *calls* B | keep-both |
| `Cyclotomic.sum_charTwist_eq`/`_ne` | `Cyclotomic.character_orthogonality_cyclotomic_eq`/`_ne` | `_charTwist` is `_orthogonality` reindexed by `Equiv.inv` | `_charTwist` *calls* `_orthogonality` | keep-both (thin adapters) |
| `Density.two_le_absNorm_of_prime` | mathlib `Ideal.one_lt_absNorm`/… | mathlib has ≠0/≠1, not packaged `2≤` | composes from mathlib | DUP-of-mathlib-composable |
| `LogOneDivSubOne.tendsto_ratio_one_of_div_atTop_pm_bounded` | mathlib `Asymptotics.IsEquivalent` | generic ratio→1 | builds on `tendsto_bdd_div_atTop_nhds_zero` | BORDERLINE-mathlib (verify `IsEquivalent`) |
| `IdealCongruenceCount.tendsto_div_atTop_of_sub_mul_rpow_le` | `IdealCongruenceCount.exists_sub_mul_rpow_le_of_div` | both pure-analytic asymptotic↔ratio/floor | distinct conclusions | keep-both |
| `IdealCongruenceCount.exists_card_cell_sub_mul_rpow_le` | `…_explicit` | implicit- vs explicit-constant | `_` re-binds `_explicit` | **DEAD-CODE** (`_` unused) → delete `_` |
| `IdealCongruenceCount.exists_card_residue_fibre_sub_mul_rpow_le` | `…_explicit` | implicit- vs explicit-constant | `_` re-binds `_explicit` | keep-both (`_` IS used) |
| `IdealCongruenceCount.cardNormLeResidueClassDvd_div_density` | `…_div_density_routeA` | **same conclusion**, two routes | independent proofs | keep-both **by design** (uniqueness-of-limits cancellation) |
| `IdealCongruenceCount.mem_span_int_basisFun_iff` | mathlib `Pi.basisFun`/`Basis.mem_span_iff_repr_mem` | "ℤ-lattice ↔ integer coords" | composes | DUP-of-mathlib-composable (verify) |
| `IdealCongruenceCount.map_span_int_linearEquiv` | mathlib `Submodule.map_span` | `f''(span ℤ S)=span ℤ (f''S)` | `map_span`+`restrictScalars` | DUP-of-mathlib-composable |
| `IdealCongruenceCount.prod_eq_neg_one_pow_card_mul_prod_abs` | mathlib `Finset.prod_*` sign API | generic `∏ = (−1)^#neg·∏\|·\|` | `prod_mul_prod_compl` | BORDERLINE-mathlib (likely *add*) |
| `IdealCongruenceCount.Nat.le_iff_le_mul_div_of_dvd` | mathlib `Nat` div API | generic floor/dvd | `Nat.le_div_iff_mul_le` | BORDERLINE + **`Nat.` clobber risk** |
| `NormLeOneLipschitz.dist_mul_le_norm_mul_dist` | mathlib `dist`/`norm` API | generic normed-field | `norm_add_le`+`dist_eq_norm` | DUP-of-mathlib-composable (verify) |
| `NormLeOneLipschitz.lipschitzWith_one_of_edist_apply_le` | mathlib `LipschitzWith.pi`/`.eval` | coordinatewise edist ⇒ 1-Lip into pi | `of_edist_le`+`edist_pi_def` | BORDERLINE-mathlib |
| `NormLeOneLipschitz.lipschitzWith_exp_ofReal_mul_I` | mathlib `lipschitzWith_circleMap` | literally `circleMap 0 1` | mathlib lemma | DUP-of-mathlib (≈1 line) |
| `CharacterOrthogonality.sum_char_apply_eq_zero_of_ne_one` (+`_self_`) | mathlib `AddChar`/`MonoidHom` orthogonality | standard row/column orthogonality | translation trick | BORDERLINE-mathlib (verify `AddChar.sum_*`) |
| `Frobenius.UnramifiedIn` | mathlib `Algebra.IsUnramifiedAt` | project bundles `≠⊥ ∧ ∀𝔓, IsUnramifiedAt` | — | keep (project bundle) |
| `NumberFieldEulerProduct.dedekindZeta_eq_tprod_primeIdeal` | mathlib `NumberField` Euler product? | Sharifi 7.1.12 | — | keep (not in mathlib at audit) |
| `Density.HasDirichletDensity` | mathlib density API | Dirichlet density via ratio | — | keep (no mathlib def) |

### Within-project UNIFY families (do now)

- **A1. `2 ≤ N𝔭` — 5 occurrences collapse to 1.** Keep the most-general `ZetaProduct.two_le_absNorm` (any number-ring Dedekind domain, ℕ-valued; sits in an `@[expose] public` module, so just drop `private` and relocate to `Common/` or leave-and-import); delete `Cyclotomic.two_le_absNorm_prime` and `Density.two_le_absNorm_of_prime`; replace the two inlinings (in `NumberFieldEulerProduct`, `FixedFieldDensity`) with a call. Density's ℝ-cast call adds `mod_cast`.
- **A2. `unramifiedIn` replica.** `Main.unramifiedIn_cyclotomic_of_coprime` is a verbatim replica (per its docstring) of private `ZetaProduct.unramifiedIn_of_coprime_absNorm`. Make the ZetaProduct one public, delete the Main copy (~48 dup lines), import.
- **A3. Frobenius-descent `_repl` pair.** `Abelian.smul_algebraMap_eq_repl` / `Abelian.isArithFrobAt_restrictNormal_repl` are explicit replicas of `CyclotomicNormResidue.smul_algebraMap_eq` / `.isArithFrobAt_restrictNormal`. Lift the **tower form** (strictly more general: an intermediate field is such a tower) to a shared spot, make public, delete the two `_repl` decls (~40 dup lines).
- **A4. log-squeeze.** `Cyclotomic.primeIdealZetaSum_unramified_div_log_tendsto_one` and `CyclotomicNormResidue.primeIdealZetaSum_unramified_coprime_div_log_tendsto_one` run the identical 4-step argument over a different finite "bad" set (~84 lines total). Add one parametrised lemma in `Density.lean` (`primeIdealZetaSum_div_log_tendsto_one_of_finite_compl`) and derive both call sites in one line each. (See API-4 — `Abelian.ratioSum_frobeniusFibres_tendsto_one` shares the skeleton too; this is the single biggest dedup, ~120 lines across 3 decls.)

The enabling move for A1–A3 is **making the private originals public** (they live in `@[expose] public` modules) so the replicas can be deleted and imported. Also **delete dead code** `IdealCongruenceCount.exists_card_cell_sub_mul_rpow_le` (only the `_explicit` form is consumed).

## Part 5: Generalisation Opportunities

(From `analysis/06-generalization.md`. Difficulty: Low / Med / High. The 5 `ForMathlib/` files were the priority; the real wins are in `CharacterOrthogonality` (A) and `NormLeOneLipschitz`/metric helpers (B).)

**A. `ForMathlib/CharacterOrthogonality.lean` — hard-wired `ℂ`, only needs `HasEnoughRootsOfUnity` (headline).** All four public results are textbook finite-abelian orthogonality/Fourier inversion but fix the target ring to `ℂ`; `ℂ` enters *only* as a source of `HasEnoughRootsOfUnity` (via `IsAlgClosed`). Confirmed: no orthogonality-sum lemma exists upstream, so these are genuinely new and should be added general.
1. `sum_char_apply_eq_zero_of_ne_one` (column) — generalise to `[CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent G)]`. The proof already calls the general `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`. **Med.**
2. `sum_char_self_eq_zero_of_ne_one` (row) — even weaker: any `[Semiring R] [IsRightCancelMulZero R]` (row orthogonality needs no roots of unity). Verbatim proof. **Low.**
3. `card_mul_eq_sum_of_sum_char_mul_eq_zero` (Fourier inversion) — same `ℂ→R` hypotheses as #1. **Med.**
4. `eq_of_sum_char_mul_eq_zero` (vanishing ⇒ constant) — `ℂ→R` with an explicit `(#dual : R) ≠ 0` side-condition for the maximally-general (non-`CharZero`) form. **Med.**
5. `sum_eq_zero_of_mulLeft_mul_const_aux` (private engine) — **already maximally general** (`Group` + `Semiring`+`IsRightCancelMulZero`); the reference for how general #1–#4 should be. No action.

**B. `ForMathlib/NormLeOneLipschitz.lean` — four over-specialised metric helpers (the bulk is correctly number-field-specific).**
6. `lipschitzWith_one_of_edist_apply_le` → generalise `1 → K` and name it **`LipschitzWith.pi`** (a map *into* a finite pi). **Verified mathlib gap**: only `LipschitzWith.eval` (the projection-from direction) exists. **Low.**
7. `dist_mul_le_norm_mul_dist` — already general but relax `NormedField → NormedDivisionRing` (the `≤`-form generalises to `NormedRing`). Verified: no two-variable product-distance bound in `Normed/Field/Basic`. **Low.**
8. `lipschitzWith_exp_ofReal_mul_I` — **not** a generalisation; it is dedup against `lipschitzWith_circleMap` (route to the dedup lane). No action.
9. `clampUnit` / `lipschitzWith_clampUnit` — hard-wired unit cube `[0,1]`; generalise to a box `projPiIcc a b` (mathlib has scalar `LipschitzWith.projIcc` but no pi/box version). **Low.**
10. `exists_phase_mem_Icc_mul_exp` — keep; the `[0,1]` interval-normalisation is the project-specific part (core is mathlib `Complex.norm_mul_exp_arg_mul_I`). No action.

**C. `LatticePointCount`:** decls are already at `Fintype ι` / sup-metric `ι → ℝ`. (11) The standard lattice `span ℤ (range (Pi.basisFun ℝ ι))` → abstract `ZLattice` is **High** (a change-of-variables layer; better as a separate wrapper than a restatement — `IdealCongruenceCount` already does exactly this conjugation). (12) Ceiling-scalar `n:ℕ → t≥0` is Low but low-value (keep/inline). The other `LatticePointCount` decls need only namespace-stripping.

**D. `LogOneDivSubOne`:** (13) `tendsto_ratio_one_of_div_atTop_pm_bounded` — a generality axis exists but the value is low; this is primarily a dedup question vs `IsEquivalent` (the file docstring already explains the deliberate elementary `∃C,∀ᶠ` form). (14) The two thin composites stay specific. Not generalisation work.

**E. `IdealCongruenceCount`:** no high-value generalisation beyond `Fintype`/namespace hygiene — the ~73 private helpers are either already maximally general for their role (`crt_single_coset`, `frontier_signOrthant_subset`, the `span_image_basisFun_*` family) or are dedup/mathlibable questions (the `Algebra.norm`/`Ideal.absNorm` identities).

**Top-5 (all ForMathlib): #1, #2, #6, #3+#4, #7+#9.** The character-orthogonality block (A) is the single highest-value target: four new-to-mathlib theorems currently pinned to `ℂ` that the proofs show need only `HasEnoughRootsOfUnity`.

## Part 6: API Improvements

(From `analysis/07-api-and-junk.md`, Part A. 10 suggestions.)

**A.1 Extract repeated patterns (new project lemmas):**
- **API-1 (HIGH)** — Shared `two_le_absNorm` (nonzero prime ⇒ N ≥ 2): 3 copies + 1 inline (see A1 above). Also a strong mathlib candidate; verify mathlib `Ideal.absNorm` lacks `Ideal.one_lt_absNorm`/`two_le_absNorm`.
- **API-2 (HIGH)** — Shared `smul_algebraMap_eq` + `isArithFrobAt_restrictNormal` (Frobenius descent): keep ONE tower-form `(K L M)` version in `Common/` (subsumes the `IntermediateField` case), delete the `_repl` copies. Both mathlib candidates (verify near `AlgEquiv.restrictNormal_commutes` / `Mathlib.RingTheory.Frobenius`).
- **API-3 (HIGH)** — Shared "cyclotomic coprime-norm ⇒ unramified" different-ideal lemma: the Main replica + the ZetaProduct original are the SAME theorem; keep one in `Common/`, delete the Main copy, import. The whole "ramification in `K(μ_m)` detected via `conductor_mul_differentIdeal`" argument is mathlib-worthy (the general-base coprime-norm criterion looks new — verify, then upstream).
- **API-4 (HIGH)** — General "Dirichlet ratio → 1 when complement is finite" lemma in `Density.lean` (`primeIdealZetaSum_div_log_tendsto_one_of_finite_primeCompl`): collapses each of 3 structurally-identical proofs (`Cyclotomic`, `CyclotomicNormResidue`, `Abelian.ratioSum_frobeniusFibres_tendsto_one`) to a one-line application. **The single highest-value extraction (~120 lines of near-duplicate squeeze).**
- **API-5 (MED)** — Relocate `Main.primeIdealZetaSum_eq_add_sub_sdiff` and `hasDirichletDensity_of_finite_symmDiff` from `Main` (where they sit `private`/orphaned) to `Density.lean` next to `HasDirichletDensity`, made public — generally-useful Dirichlet-density facts.
- **API-6 (MED)** — Consolidate the 3 fibre-counting `tsum` helpers in `FixedFieldDensity` (`tsum_comp_eq_card_fibre_smul`, `tsum_comp_le_card_fibre_mul`, `tsum_real_comp_le_card_fibre_mul`) into one `Common/` file; check mathlib `HasSum.tsum_fiberwise`/`tsum_fiberwise` for a constant-fibre form.

**A.2 Instances / coercions:**
- **API-7 (MED)** — Duplicated/ad-hoc `Fintype`/`Finite` instances: `instFintypeSym` (verify mathlib `Sym.instFintype`); promote the local `galoisCharacter.instFintype` (or a `Common/` one) to non-local so `Cyclotomic`'s lemmas can drop their `[Fintype (galoisCharacter K L)]` binders; `NumberFieldEulerProduct.instFiniteAbsNormFiber` ↔ `ZetaProduct.finite_nonzeroIdeal_absNorm_eq` are the SAME fact (one instance, one theorem) — keep the instance, delete the theorem.

**A.3 Completeness (`@[simp]` / equation companions):**
- **API-8 (LOW)** — `ZetaProduct.galoisCharacterOnIdeal_apply_prime` is not `@[simp]` though the parallel `frobeniusIdeal_apply_prime` is; consider marking it (conditional simp; same `h𝔭 : 𝔭 ≠ ⊥` shape).
- **API-9 (LOW)** — `frobeniusIdeal`/`galoisCharacterOnIdeal` lack `_pow` companions; several proofs re-derive `w(𝔭^k)=(w𝔭)^k` by inline induction. Marginal.
- **API-10 (NOTE)** — `Frobenius.orderOf_eq_finrank_of_isArithFrobAt` is a documented mathlib API gap ("Frobenius generates the decomposition group `D_𝔓`"). Record for `/mathlibable`; no project action.

## Part 7: Junk / Removable

(From `analysis/07-api-and-junk.md`, Part B. **The distinction matters:** the vast majority of "unused in file" decls are terminal public exports consumed by sibling files — they are KEEP, not junk. Only duplicates and one superseded decl are genuine removables.)

### B.1 / B.2 — Genuine removables (7)

| # | Decl | Verdict | Reason |
|---|------|---------|--------|
| J-1 | `Density.two_le_absNorm_of_prime`, `Cyclotomic.two_le_absNorm_prime` | **REPLACE** → `ZetaProduct.two_le_absNorm` (relocate to `Common/`) | 3 verbatim copies (API-1); keep most-general |
| J-2 | `Abelian.smul_algebraMap_eq_repl` | **REMOVE** (shared tower-form lemma) | verbatim replica per docstring (API-2) |
| J-3 | `Abelian.isArithFrobAt_restrictNormal_repl` | **REMOVE** (shared lemma) | verbatim replica (API-2) |
| J-4 | `Main.unramifiedIn_cyclotomic_of_coprime` | **REMOVE** (import ZetaProduct original, relocated to `Common/`) | docstring: "self-contained replica"; ~48 dup lines (API-3) |
| J-5 | `NumberFieldEulerProduct.instFiniteAbsNormFiber` **or** `ZetaProduct.finite_nonzeroIdeal_absNorm_eq` | **REMOVE one** (keep the `instance`) | same fact stated twice (API-7) |
| J-6 | `Abelian.H_n_over_H_tends_to_one` (public, ~60 lines) | **REMOVE** | superseded by `ratio_card_dvd_orderOf_tendsto_one`; no consumer in-file or cross-file (verify before deleting). ~60 dead lines |
| J-7 | `Abelian.cyclic_subgroup_meets_G_times_one_trivially` (public) | **REMOVE or privatise** | the concrete `zpowers_inf_fixingSubgroup_eq_bot_aux` re-derives it; abstract `G × H` version never applied |

### B.3 — INLINE candidates (LOW; both borderline, evaluated-and-kept)

| # | Decl | Verdict | Reason |
|---|------|---------|--------|
| J-8 | `NumberFieldEulerProduct.instFintypeSym` | **REPLACE** if mathlib has `Sym.instFintype` | one-line `Fintype.ofFinite`; verify, else keep |
| J-9 | `LatticePointCount.measureReal_biUnion_box` | **KEEP** | bundles disjointness + finite-measure side-conditions; inlining would bloat a 72-line proof |
| J-10 | `Frobenius.UnramifiedIn.ne_bot` | **KEEP** | canonical accessor used by ~6 sites; idiomatic, reads better than `.1` |

The project has very few gratuitous wrappers — most short decls are legitimate named projections or equation lemmas that earn their names.

### B.4 — "Unused in file" but PUBLIC API (~30+ — KEEP, do not remove)

These are intentional cross-file/upstream exports flagged "unused in file" only because no *other decl in the same file* calls them. Confirmed via the inventories' "Used by" notes and module docstrings:
- **`ForMathlib/` upstream exports:** `LogOneDivSubOne.tendsto_ratio_one_of_log_pm_bounded`; `CharacterOrthogonality.{sum_char_self_eq_zero_of_ne_one, eq_of_sum_char_mul_eq_zero}`; `LatticePointCount.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`; `NormLeOneLipschitz.{normLeOne_frontier_lipschitz_cover, …_index}`; `IdealCongruenceCount`'s 4 public terminals.
- **Cross-file Chebotarev spine:** `Frobenius.{card_primesAbove_mul_orderOf_eq, finite_ramifiedIn, finite_badPrimes}`; `CyclotomicNormResidue.{autToPow_frobeniusClass_out, subgroup_eq_top_of_forall_frobenius_mem}`; `Cyclotomic.chebotarev_cyclotomic_lowerDensity_ge`; `FixedFieldDensity.density_lift_through_fixedField`; `Abelian.chebotarev_abelian`; `ZetaProduct.artinLSeries_one_ne_zero`; the `Density.HasDirichletDensity.*` surface (10 decls); `NumberFieldEulerProduct.{dedekindZeta_eq_tprod_primeIdeal, dedekindZeta_re_pos_of_one_lt, hasSum_nonzeroIdeal_absNorm_cpow}`.
- **Top-level deliverables:** `Main.{chebotarev_density, chebotarev_density_of_comm, infinite_setOf_frobenius_class, density_split_completely, dirichlet_primes_in_AP}`.
- **Typeclass-resolved instances:** `Frobenius.faithfulSMul_galois`, `ZetaProduct.{finite_L2, finite_ramifiedAbove, galoisCharacter.instFintype}`, `NumberFieldEulerProduct.{instFintypeSym, instFiniteAbsNormFiber}`.

**Top duplication root causes:** (1) the log-asymptotic squeeze [API-4, ~120 dup lines — biggest win]; (2) `two_le_absNorm` [J-1]; (3) the Frobenius-descent `_repl` pair [J-2/J-3]; (4) the cyclotomic coprime-norm⇒unramified replica [J-4].

## Part 8: Mathlibable Assessment

**Status: DEFERRED.** The per-declaration `/mathlibable` pass (Step 9 of `/overview`) was **intentionally not run** for this project. It is parked pending a retune of the `/mathlibable` skill (its literature-search gating is being revised so it does not short-circuit the WebSearch/ChatGPT/nLab sweep that is the whole value of the step). When resumed, Step 9 should be run once-per-declaration over the candidate list below — these are exactly the decls Stage 2 flagged as either genuinely-new-to-mathlib or generalise-first, so the list is a ready-made worklist.

**Candidate decls flagged genuinely-new (YES-add / contribute-beside, verify upstream first):**
- `ForMathlib/CharacterOrthogonality.lean`: the four orthogonality/Fourier-inversion theorems (in their generalised `HasEnoughRootsOfUnity` form — Part 5 #1–#4) + the private engine `sum_eq_zero_of_mulLeft_mul_const_aux` (already maximally general; plausibly standalone-worthy). No orthogonality-sum lemma exists upstream.
- `ForMathlib/LatticePointCount.lean`: `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` / `abs_card_inter_sub_volume_mul_pow_le` — the *effective* (`O(n^{d−1})`-error) strengthening of mathlib's rate-free `tendsto_card_div_pow_atTop_volume`, beside the `BoxIntegral.unitPartition.index` API; plus the diameter-counting refinements (`setFinite_index_image_of_isBounded`, `ncard_index_image_*`).
- `ForMathlib/NormLeOneLipschitz.lean`: `LipschitzWith.pi` (the into-pi direction, a confirmed gap — Part 5 #6); `projPiIcc`/box-clamp (Part 5 #9); the `expMapBasis`/`mixedEmbedding` frontier-cover machinery (`faceMap*`, `frontierCoverFamily`, `liftToMixed`, `mixedCubeEquiv`, the three `normLeOne_frontier_lipschitz_cover*`) — the real number-field contribution.
- `ForMathlib/IdealCongruenceCount.lean`: the workhorse `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`; the residue-count exports; and the `Ideal.absNorm`/`ZLattice`/`ClassGroup` bridges to verify-then-KEEP (`relIndex_*_eq_absNorm`, `absNorm_coprime_of_isCoprime_span`, `covolume_image_basisFun_eq_abs_det`, `exists_mk0_eq_absNorm_coprime`, `crt_single_coset`, `natCast_algebraNorm_add_nsmul_mul`, `norm_eq_prod_real_emb_mul_prod_complex`, `prod_eq_neg_one_pow_card_mul_prod_abs`); the analytic `tendsto_div_atTop_of_sub_mul_rpow_le` / `exists_sub_mul_rpow_le_of_div`.
- `Density.lean`: `HasDirichletDensity`/`Upper`/`Lower` + the `primeIdealZetaSum_univ_tendsto_log` (7.1.12) family — no Dirichlet-density-of-primes notion in mathlib.
- `Frobenius.lean`: `orderOf_eq_finrank_of_isArithFrobAt` — a documented API gap ("Frobenius generates `D_𝔓`").
- `NumberFieldEulerProduct.lean` / `ZetaProduct.lean`: `dedekindZeta_eq_tprod_primeIdeal` (7.1.12), the weighted Euler product (7.1.18), the abelian Artin Euler product (7.1.18).

**Candidate decls flagged generalise-first (YES-but-generalise):** the same `CharacterOrthogonality` four (`ℂ → HasEnoughRootsOfUnity` ring), `dist_mul_le_norm_mul_dist` (`NormedField → NormedDivisionRing`), `clampUnit`→`projPiIcc` (unit cube → box) — see Part 5.

**Decls that `/mathlibable` should return NO/composable for** (delete-and-use-mathlib, from Part 3/4): `charEval`, `lipschitzWith_exp_ofReal_mul_I`, `map_span_int_linearEquiv`, `mem_span_int_basisFun_iff`, `tendsto_ratio_one_of_div_atTop_pm_bounded` (likely `IsEquivalent`), and the `2 ≤ N𝔭` family (composable from `Ideal.absNorm` API).

## Recommended Action Plan

### Priority 1 — Quick wins (mechanical, statement-preserving)
- **Drop `private` + import dedup (A1–A4 / J-1..J-4):** make `ZetaProduct.two_le_absNorm`, `ZetaProduct.unramifiedIn_of_coprime_absNorm`, and the tower-form Frobenius-descent lemmas public (they sit in `@[expose] public` modules), relocate to `Common/`, delete the 2 `two_le_absNorm` copies + 2 inlinings, the `Main` replica, and the two `Abelian._repl` decls; import.
- **Delete-and-use-mathlib (Part 3):** `charEval → CommGroup.monoidHomMonoidHomEquiv`; `lipschitzWith_exp_ofReal_mul_I → lipschitzWith_circleMap`; `map_span_int_linearEquiv → Submodule.map_span`; inline `dist_mul_le_norm_mul_dist` and `measureReal_biUnion_box`; (verify) `mem_span_int_basisFun_iff → Pi.basisFun`.
- **Dead-code removal:** `IdealCongruenceCount.exists_card_cell_sub_mul_rpow_le` (J — `_explicit` only is used); `Abelian.H_n_over_H_tends_to_one` (J-6, superseded — verify no cross-file consumer); `Abelian.cyclic_subgroup_meets_G_times_one_trivially` (J-7); one of the `instFiniteAbsNormFiber`/`finite_nonzeroIdeal_absNorm_eq` pair (J-5).
- **`Nat.`-namespace rename:** `IdealCongruenceCount.Nat.le_iff_le_mul_div_of_dvd` → out of `Nat.` (clobber risk).

### Priority 2 — Extract shared API
- **API-4 (highest value):** add `primeIdealZetaSum_div_log_tendsto_one_of_finite_primeCompl` to `Density.lean`; collapse the 3 log-squeeze proofs (`Cyclotomic`, `CyclotomicNormResidue`, `Abelian.ratioSum_frobeniusFibres_tendsto_one`) to one-liners (~120 lines saved).
- **API-5/6:** relocate `primeIdealZetaSum_eq_add_sub_sdiff` + `hasDirichletDensity_of_finite_symmDiff` into `Density.lean` (public); consolidate the 3 `FixedFieldDensity` fibre-`tsum` helpers into `Common/`.
- **API-7/8/9:** promote `galoisCharacter.instFintype` non-local (lets `Cyclotomic` drop `[Fintype …]` binders); add the `@[simp]`/`_pow` companions if the inline inductions recur.

### Priority 3 — Generalisations (statement changes → `lane:generalise`, coordinator-merged)
- **Character orthogonality ℂ → ring (the headline):** generalise the four `CharacterOrthogonality` theorems to `[CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent G)]` (row lemma even weaker: `[Semiring R] [IsRightCancelMulZero R]`); proofs unchanged (Part 5 #1–#4).
- **Metric helpers (Low):** `lipschitzWith_one_of_edist_apply_le → LipschitzWith.pi` (`1 → K`); `dist_mul_le_norm_mul_dist` (`NormedField → NormedDivisionRing`); `clampUnit → projPiIcc` (unit cube → box).

### Priority 4 — Re-decompose the 34 proofs > 50 lines (`lane:decompose`)
Statement-unchanged helper extraction. Grouped by file with line counts (suggested helpers noted in the inventories):

- **`ForMathlib/IdealCongruenceCount.lean` (11):** `exists_card_fibre_dvd_eq_card_cell` (~97), `abs_cardR_translate_sub_volume_le` (~80), `ncard_index1_image_smul_chart_le` (~78), `exists_card_fibre_dvd_residue_sub_mul_rpow_le` (~64), `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` (~59), `exists_card_residue_fibre_sub_mul_rpow_le_explicit` (~58), `exists_mk0_eq_absNorm_coprime` (~57), `card_isPrincipal_dvd_norm_le_residue` (~55), `crt_single_coset` (~53), `mem_smul_cell_iff_norm_le_and_filter_eq` (~52), `cardNormLeResidueClassDvd_div_density_routeA` (~52).
- **`ZetaProduct.lean` (9):** `card_fibre_bound_two_le` (~127 — highest-priority target), `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` (~65), `prod_galoisCharacter_one_sub` (~63), `sum_rpow_le_euler_prod` (~62), `tprod_unramified_eq_prod_artinDirichletSeries` (~57), `unramifiedIn_of_coprime_absNorm` (~55), `card_fibre_eq_card_good_fibre` (~55), `ciSup_sum_inv_absNorm_sub_le` (~55), `coprime_absNorm_of_unramified_of_finrank_eq_one` (~53).
- **`Abelian.lean` (4):** `liminf_ratio_ge_inv_card_G` (~63), `H_n_over_H_tends_to_one` (~60 — but J-6 deletes this), `ratioSum_frobeniusFibres_tendsto_one` (~57 — but API-4 collapses this), `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` (~55).
- **`NumberFieldEulerProduct.lean` (3):** `weighted_eulerProduct_eq_tsum` (~60), `idealNormMultiplicity_mul` (~58 — extract the `fwd`/`bwd`/`h_equiv` block), `finsetGeometricProd_summable_and_hasSum` (~55 — empty/insert branches).
- **`FixedFieldDensity.lean` (2):** `density_lift_through_fixedField` (~88), `primeIdealZetaSum_fibre_eq_smul` (LEAF A, ~82).
- **`Cyclotomic.lean` (2):** `differentiableAt_logSum_of_two_le` (~103), `log_artinLSeries_asymp_character_sum` (~61).
- **`ForMathlib/LatticePointCount.lean` (2):** `abs_card_inter_sub_volume_mul_pow_le` (~72), `ncard_index_image_chart_le` (~56).
- **`CyclotomicNormResidue.lean` (1):** `primeIdealZetaSum_under_eq_finrank_mul` (~50 — extract the fibre `Equiv` + constancy facts).

(Note: 2 of the 34 — `Abelian.H_n_over_H_tends_to_one` and `…ratioSum_frobeniusFibres_tendsto_one` — are slated for removal/collapse under Priority 1/2, which would reduce the decompose backlog to 32.)

### Priority 5 — Mathlib contributions
**DEFERRED to Stage 3.** Gated on the `/mathlibable` retune (Part 8). When resumed, run `/mathlibable` per-declaration over the Part 8 candidate list, then PR the genuinely-new decls (character orthogonality, effective lattice count, Dirichlet-density predicates, the verified `Ideal.absNorm`/`ZLattice` bridges, `LipschitzWith.pi`) to mathlib with the `Chebotarev` namespace stripped — after the generality and dedup work in Priorities 1–3 lands.
