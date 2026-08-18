# Step 5 — Moral Duplication Detection: Chebotarev project

Scope: 14 files, 441 declarations across `projects/Chebotarev/CebotarevDensity/`.
Goal: find decls that are **morally the same** — (a) within the project (same fact stated
differently / special cases / same proof structure over different objects) and (b) decls that
**duplicate mathlib** and should be deleted in favour of the upstream name.

Method: read all 14 inventory `.md` files; cross-checked exact statements/proof bodies in the
`.lean` sources for every flagged pair; ran `WebSearch "mathlib4 <concept>"` for the
mathlib-overlap candidates flagged by the inventories' ForMathlib audits.

`𝓞K`, `N𝔭 = Ideal.absNorm 𝔭`, `Gal(L/K) = L ≃ₐ[K] L`, `Φ` = `(stdBasis K).equivFunL`.

---

## Pairwise comparison table

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `Density.two_le_absNorm_of_prime` | `Cyclotomic.two_le_absNorm_prime` | Yes (A casts to ℝ; both `2 ≤ N𝔭`) | Yes (≠0,≠1,`lia`) | UNIFY |
| `Cyclotomic.two_le_absNorm_prime` | `ZetaProduct.two_le_absNorm` | B generalises (any `IsDedekindDomain`, free+finite/ℤ) | Yes (identical body) | one-is-special-case → keep B |
| `Density.two_le_absNorm_of_prime` | `ZetaProduct.two_le_absNorm` | B generalises; A is the ℝ-cast `𝓞K` case | Yes | one-is-special-case → keep B |
| `NumberFieldEulerProduct.norm_absNorm_cpow_neg_lt_one` (inlined `2≤N𝔭`) | `ZetaProduct.two_le_absNorm` | Sub-fact: `2≤N𝔭` is re-derived inline | Yes (same 2 lines) | UNIFY (factor out) |
| `FixedFieldDensity.absNorm_rpow_neg_le_under_sq` (inlined `2≤N𝔭`) | `ZetaProduct.two_le_absNorm` | Sub-fact inlined | Yes | UNIFY (factor out) |
| `Density.absNorm_rpow_neg_lt_one` | `NumberFieldEulerProduct.norm_absNorm_cpow_neg_lt_one` | Same idea (ℝ vs ℂ `N𝔭^{-s}<1`) | Same (`two_le` ⇒ `rpow_lt_one_of_one_lt_of_neg`) | keep-both (real vs complex) |
| `Main.unramifiedIn_cyclotomic_of_coprime` | `ZetaProduct.unramifiedIn_of_coprime_absNorm` | **Identical** (same binders/concl) | **Identical** (docstring says "Replica") | UNIFY (delete replica) |
| `Abelian.smul_algebraMap_eq_repl` | `CyclotomicNormResidue.smul_algebraMap_eq` | Same fact; B uses `IntermediateField F`, A uses tower `K⊆L⊆M` | Same (docstring says "replicated `_repl`") | UNIFY (tower form generalises) |
| `Abelian.isArithFrobAt_restrictNormal_repl` | `CyclotomicNormResidue.isArithFrobAt_restrictNormal` | Same fact; tower vs intermediate-field | Same (replica) | UNIFY (tower form generalises) |
| `Cyclotomic.primeIdealZetaSum_unramified_div_log_tendsto_one` | `CyclotomicNormResidue.primeIdealZetaSum_unramified_coprime_div_log_tendsto_one` | Differ only in the "good" set (unram vs unram∧coprime) | **Same 4-step proof** (finite bad set, `_le_card_of_finite`, `squeeze_zero_norm'`, subtract `univ_tendsto_log`) | UNIFY → one `…_of_finite_compl` lemma |
| `Cyclotomic.two_le_absNorm_prime` | `Density.two_le_absNorm_of_prime` | (see row 1) | | (covered) |
| `Cyclotomic.sum_galoisCharacter_eq_card_or_zero` | `ForMathlib.CharacterOrthogonality.sum_char_apply_eq_zero_of_ne_one` | A = `if g=1 then |G| else 0`; B is the `g≠1` half | A *calls* B for one branch | keep-both (A is a packaged superset) |
| `Cyclotomic.sum_charTwist_eq` / `_ne` | `Cyclotomic.character_orthogonality_cyclotomic_eq` / `_ne` | `_charTwist` is `_orthogonality` reindexed by `Equiv.inv` | `_charTwist` *calls* `_orthogonality` | keep-both (thin adapters) |
| `Density.primeIdealZetaSum_le_card_of_finite` | (mathlib) | — | — | keep (project def `primeIdealZetaSum`) |
| `Density.two_le_absNorm_of_prime` | mathlib `Ideal.one_lt_absNorm` / `Ideal.absNorm_...` | mathlib has the ≠0/≠1 facts, not a packaged `2≤` | composes from mathlib | DUP-OF-MATHLIB-composable (see below) |
| `ForMathlib.LogOneDivSubOne.tendsto_ratio_one_of_div_atTop_pm_bounded` | mathlib `Asymptotics.IsEquivalent` API | Generic additive-perturbation ratio→1 | builds on `tendsto_bdd_div_atTop_nhds_zero` | BORDERLINE-mathlib (verify `IsEquivalent`) |
| `ForMathlib.IdealCongruenceCount.tendsto_div_atTop_of_sub_mul_rpow_le` | `ForMathlib.IdealCongruenceCount.exists_sub_mul_rpow_le_of_div` | Both pure-analytic asymptotic↔ratio/floor lemmas | Distinct (limit vs floor-shift) | keep-both (different conclusions) |
| `ForMathlib.IdealCongruenceCount.exists_card_cell_sub_mul_rpow_le` | `…_explicit` | Implicit- vs explicit-constant form | `_` re-binds `_explicit`'s constant | DEAD-CODE (`_` is UNUSED) → delete `_` |
| `ForMathlib.IdealCongruenceCount.exists_card_residue_fibre_sub_mul_rpow_le` | `…_explicit` | Implicit- vs explicit-constant form | `_` re-binds `_explicit` | keep-both (`_` IS used by `…_residue_le`) |
| `ForMathlib.IdealCongruenceCount.cardNormLeResidueClassDvd_div_density` | `…_div_density_routeA` | **Same conclusion** (same density `κfull/N𝔟`), two routes | Independent proofs (geometric vs Route A) | keep-both **by design** (uniqueness-of-limits cancellation) |
| `ForMathlib.IdealCongruenceCount.mem_span_int_basisFun_iff` | mathlib `Pi.basisFun`/`Basis.mem_span_iff_repr_mem` | "in ℤ-lattice ↔ integer coords" | composes from mathlib | DUP-OF-MATHLIB-composable (verify) |
| `ForMathlib.IdealCongruenceCount.map_span_int_linearEquiv` | mathlib `Submodule.map_span` | `f''(span ℤ S)=span ℤ (f''S)` | `Submodule.map_span` + `restrictScalars` | DUP-OF-MATHLIB-composable |
| `ForMathlib.IdealCongruenceCount.prod_eq_neg_one_pow_card_mul_prod_abs` | mathlib `Finset.prod_*` sign API | Generic `∏ = (−1)^#neg · ∏\|·\|` | `Finset.prod_mul_prod_compl` | BORDERLINE-mathlib (likely addable, not present verbatim) |
| `ForMathlib.IdealCongruenceCount.Nat.le_iff_le_mul_div_of_dvd` | mathlib `Nat` div API | Generic `a≤N ↔ a≤m⌊N/m⌋` for `m∣a` | `Nat.le_div_iff_mul_le` | BORDERLINE-mathlib + **`Nat.` namespace clobber risk** |
| `ForMathlib.NormLeOneLipschitz.dist_mul_le_norm_mul_dist` | mathlib `dist`/`norm` API | Generic normed-field product-distance | `norm_add_le`+`dist_eq_norm` | DUP-OF-MATHLIB-composable (verify) |
| `ForMathlib.NormLeOneLipschitz.lipschitzWith_one_of_edist_apply_le` | mathlib `LipschitzWith.pi` / `.eval` | Coordinatewise edist ⇒ 1-Lip into pi | `of_edist_le`+`edist_pi_def` | BORDERLINE-mathlib (check pi-Lipschitz API) |
| `ForMathlib.NormLeOneLipschitz.lipschitzWith_exp_ofReal_mul_I` | mathlib `lipschitzWith_circleMap` | `t↦exp(t·i)` is 1-Lip = `circleMap 0 1` | literally `circleMap`+mathlib lemma | DUP-OF-MATHLIB (≈1 line) |
| `ForMathlib.CharacterOrthogonality.sum_char_apply_eq_zero_of_ne_one` (+ `_self_`) | mathlib `AddChar`/`MonoidHom` orthogonality | Standard column/row orthogonality for `G→*ℂˣ` | translation trick | BORDERLINE-mathlib (verify `AddChar.sum_apply_eq_zero`) |
| `Frobenius.UnramifiedIn` (def) | mathlib `Algebra.IsUnramifiedAt` | Project bundles `≠⊥ ∧ ∀𝔓 over 𝔭, IsUnramifiedAt` | — | keep (project-specific bundle, not in mathlib) |
| `NumberFieldEulerProduct.dedekindZeta_eq_tprod_primeIdeal` | mathlib `NumberField` Euler-product? | Sharifi Thm 7.1.12 | weighted euler product | keep (not in mathlib at audit time) |
| `Density.HasDirichletDensity` (def) | mathlib density API | Dirichlet density via `primeIdealZetaSum` ratio | — | keep (no mathlib Dirichlet-density def) |

(31 pairs/groups examined above; the full per-family reasoning follows.)

---

## Prose action list

### A. WITHIN-PROJECT — clear UNIFY (highest value)

**A1. `2 ≤ N𝔭` — three identical copies + two inlinings. UNIFY to one.**
- `ZetaProduct.two_le_absNorm` `{R} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
  [Module.Finite ℤ R] {𝔭} (hp : 𝔭.IsPrime) (hb : 𝔭 ≠ ⊥) : 2 ≤ Ideal.absNorm 𝔭` is the
  **most general** form (works for any number-ring Dedekind domain, ℕ-valued).
- `Cyclotomic.two_le_absNorm_prime` (`𝓞K`, ℕ-valued) and `Density.two_le_absNorm_of_prime`
  (`𝓞K`, ℝ-cast) are special cases with byte-identical `lia` proofs.
- The same `≠0 ∧ ≠1 ⇒ 2≤` two-liner is **inlined** inside
  `NumberFieldEulerProduct.norm_absNorm_cpow_neg_lt_one` and
  `FixedFieldDensity.absNorm_rpow_neg_le_under_sq`.
- **Action**: keep `ZetaProduct.two_le_absNorm`, make it **public** (it sits in an `@[expose]
  public` module so just drop `private`), relocate it to a `Common/`-style shared spot (or leave
  in ZetaProduct and import), delete `two_le_absNorm_prime` and `two_le_absNorm_of_prime`, and
  replace the two inlinings with a call. Density's ℝ-cast call site adds `Nat.cast_le.mpr`/
  `mod_cast`. **5 occurrences collapse to 1.**

**A2. `unramifiedIn_cyclotomic_of_coprime` (Main) = `unramifiedIn_of_coprime_absNorm`
(ZetaProduct). UNIFY — delete the replica.**
- Statements are **identical** up to `{K}` implicit vs explicit; proofs are **identical** (the
  Main docstring literally says *"Replica of the private `unramifiedIn_of_coprime_absNorm` in
  `ZetaProduct.lean`, which is not importable here"*). ~48–55 duplicated proof lines.
- Note: a third, *weaker* sibling `Main.unramifiedIn_cyclotomic_of_coprime` is also semantically
  matched by `CyclotomicNormResidue.cyclotomic_frobenius_acts_as_norm_power`'s prerequisites — but
  the exact replica is the ZetaProduct one.
- **Action**: make `ZetaProduct.unramifiedIn_of_coprime_absNorm` **public**, delete
  `Main.unramifiedIn_cyclotomic_of_coprime`, import. (Both modules are already in the build.)

**A3. `smul_algebraMap_eq` / `isArithFrobAt_restrictNormal` — CNR vs Abelian `_repl`. UNIFY.**
- `Abelian.smul_algebraMap_eq_repl` and `Abelian.isArithFrobAt_restrictNormal_repl` are explicit
  replicas (docstrings: *"The CNR original is `private`, hence unreachable here; replicated
  `_repl`"*) of `CyclotomicNormResidue.smul_algebraMap_eq` / `.isArithFrobAt_restrictNormal`.
- **Generality**: CNR states them for an `IntermediateField F` of `L/K`; Abelian for a 3-field
  tower `K ⊆ L ⊆ M` with `[IsScalarTower K L M]`. These are the *same fact* (an intermediate
  field is exactly such a tower), and the **tower form subsumes the intermediate-field form**
  (instantiate `M := L`, `L := ↥F`). ~40 duplicated proof lines across the two pairs.
- **Action**: lift one copy (prefer the **tower form**, it is strictly more general) to a shared
  location and make it public; derive the intermediate-field CNR call sites from it (or just keep
  the tower form and adjust CNR's two call sites). Delete the two `_repl` decls.

**A4. `primeIdealZetaSum_..._div_log_tendsto_one` — same proof over a different finite "bad" set.
UNIFY to one parametrised lemma.**
- `Cyclotomic.primeIdealZetaSum_unramified_div_log_tendsto_one`: ratio over
  `{unramified primes}` → 1; bad set = ramified primes (`finite_ramifiedIn`).
- `CyclotomicNormResidue.primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`: ratio over
  `{unramified ∧ coprime-norm primes}` → 1; bad set = `finite_ramifiedIn ∪ finite_badPrimes`.
- Both run the **identical 4-step argument** (lines 690–732 vs 353–402): split univ = good ⊔ bad,
  bad finite so `primeIdealZetaSum_le_card_of_finite` bounds its sum, `squeeze_zero_norm'` +
  `Tendsto.div_atTop` kills the bad ratio, subtract from `primeIdealZetaSum_univ_tendsto_log`,
  reassemble with `primeIdealZetaSum_union_of_disjoint` /
  `primeIdealZetaSum_eq_univ_of_forall_prime_mem`. ~42 lines each, ~84 total.
- **Action**: add one lemma in `Density.lean` next to the existing engine
  `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`:
  `primeIdealZetaSum_div_log_tendsto_one_of_finite_compl (S : Set …) (hcofin : {nonzero primes} \ S
  finite) : Tendsto (Σ_S / log(1/(s−1))) (𝓝[>]1) (𝓝 1)`, then derive both call sites in one line
  each. (`FixedFieldDensity.univ_ratio_E_K_tendsto_one` is a *different* fact — E-vs-K ratio of
  two `univ` sums — so it stays.)

### B. WITHIN-PROJECT — keep-both / one-is-special-case (do NOT merge)

- **`Cyclotomic.sum_galoisCharacter_eq_card_or_zero`** packages
  `ForMathlib…sum_char_apply_eq_zero_of_ne_one` (the `g≠1` branch) together with the `g=1`
  branch into one `if`. It *uses* the orthogonality lemma; it is a convenience superset, not a
  duplicate. **keep-both.**
- **`Cyclotomic.sum_charTwist_eq`/`_ne`** are `character_orthogonality_cyclotomic_eq`/`_ne`
  reindexed by `Equiv.inv`; thin adapters that *call* the originals. **keep-both** (could be
  inlined but it is not a correctness-level dup).
- **`Density.absNorm_rpow_neg_lt_one`** (ℝ) vs **`NumberFieldEulerProduct.norm_absNorm_cpow_neg_lt_one`**
  (ℂ): genuinely different ambient field/conclusion shape; both should call the unified `2≤N𝔭`
  (A1) but otherwise **keep-both**.
- **`IdealCongruenceCount.cardNormLeResidueClassDvd_div_density` vs `…_routeA`**: deliberately two
  independent proofs of the *same* density value so that uniqueness of limits cancels the `N𝔟`
  and torsion factors in `tendsto_cardNormLeResidueClass_div_transfer`. **keep-both by design.**
- **`…_explicit`/non-explicit pairs** (`exists_card_cell_…`, `exists_card_residue_fibre_…`): the
  implicit-constant wrapper just re-binds the explicit constant. Not a moral dup —
  `exists_card_residue_fibre_sub_mul_rpow_le` *is* used. But
  **`exists_card_cell_sub_mul_rpow_le` is UNUSED** (inventory-confirmed) → **delete as dead code.**

### C. DUP-OF-MATHLIB — delete + replace (verify the exact upstream name at PR time)

These are flagged because they are `ForMathlib`-namespaced (author-earmarked) yet either exist
upstream or compose trivially from mathlib primitives. WebSearch confirms the underlying mathlib
API exists in each case; the project lemma is a thin composite.

- **`NormLeOneLipschitz.lipschitzWith_exp_ofReal_mul_I`** → it is literally `circleMap 0 1`, and
  mathlib has `lipschitzWith_circleMap`. Replace with the one-line mathlib form. **DUP-OF-MATHLIB.**
- **`NormLeOneLipschitz.dist_mul_le_norm_mul_dist`** → generic `NormedField` product-distance,
  derivable from `dist_eq_norm` + `norm_add_le` + `norm_mul`; search for an existing
  `dist_mul_le`/`norm_mul_sub_mul_le`-style lemma before keeping. **DUP-OF-MATHLIB-composable.**
- **`IdealCongruenceCount.map_span_int_linearEquiv`** → `Submodule.map_span` of
  `f.restrictScalars ℤ`; replace the call sites with `Submodule.map_span` (+ `congrArg coe`).
  **DUP-OF-MATHLIB-composable.**
- **`IdealCongruenceCount.mem_span_int_basisFun_iff`** → `(Pi.basisFun ℝ ι).mem_span_iff_repr_mem`
  + `Pi.basisFun_repr`. **DUP-OF-MATHLIB-composable.**

### D. BORDERLINE-mathlib — verify before deleting (do not auto-delete)

Plausibly already in mathlib or worth upstreaming-as-is; needs a human/PR-time check (the five-
method mathlib search), not a mechanical delete:

- `LogOneDivSubOne.tendsto_ratio_one_of_div_atTop_pm_bounded` — generic additive-perturbation
  `f/g→1`; very likely subsumed by `Asymptotics.IsEquivalent`/`isEquivalent_iff_tendsto_one`. The
  module docstring itself cites these. **Strong DUP candidate — verify.**
  (Its specialisation `tendsto_ratio_one_of_log_pm_bounded` would never be added separately.)
- `CharacterOrthogonality.sum_char_apply_eq_zero_of_ne_one` / `sum_char_self_eq_zero_of_ne_one`
  — textbook finite-abelian column/row orthogonality for `G →* ℂˣ`; mathlib has `AddChar`-flavoured
  orthogonality. Check `AddChar.sum_apply_eq_zero` / `MonoidHom.sum_apply_eq_zero` before
  upstreaming; the private engine `sum_eq_zero_of_mulLeft_mul_const_aux` is itself clean and
  mathlib-worthy.
- `IdealCongruenceCount.prod_eq_neg_one_pow_card_mul_prod_abs` — generic `Finset.prod` sign
  identity; belongs in `Mathlib.Algebra.BigOperators` if absent. Likely *add*, not delete.
- `IdealCongruenceCount.Nat.le_iff_le_mul_div_of_dvd` — generic `Nat` floor/dvd lemma **declared
  in the `Nat.` namespace** → clobber risk; rename/relocate regardless of dup status.
- `IdealCongruenceCount.natCast_eq_iff_mul_natCast_eq`, `covolume_image_basisFun_eq_abs_det`,
  `relIndex_mul_ideal_eq_absNorm`, `absNorm_coprime_of_isCoprime_span`, `crt_single_coset`,
  `exists_mk0_eq_absNorm_coprime`, `tendsto_div_atTop_of_sub_mul_rpow_le`,
  `exists_sub_mul_rpow_le_of_div`, `natCast_algebraNorm_add_nsmul_mul`,
  `norm_eq_prod_real_emb_mul_prod_complex` — all generic (ZMod/ZLattice/Ideal/analysis/Algebra.norm
  level), flagged by the inventory's ForMathlib audit. None are within-project dups; each needs a
  standalone mathlibable check. Not actioned here beyond noting them.
- `NormLeOneLipschitz.lipschitzWith_one_of_edist_apply_le` — generic 1-Lipschitz-into-pi; check
  `LipschitzWith.pi`/`.eval` family.

### Summary of recommended edits

- **UNIFY (within-project, do now)**: A1 (`2≤N𝔭`, 5→1), A2 (`unramifiedIn` replica), A3 (`smul`/
  `isArithFrobAt` `_repl` ×2), A4 (`…_div_log_tendsto_one`, 2→1 parametrised). The enabling move
  for A1–A3 is **making the originals `public`** (they are private but live in `@[expose] public`
  modules) so the replicas can be deleted and imported.
- **DELETE dead code**: `IdealCongruenceCount.exists_card_cell_sub_mul_rpow_le` (unused).
- **DUP-OF-MATHLIB (delete + replace, verify name)**: `lipschitzWith_exp_ofReal_mul_I`,
  `dist_mul_le_norm_mul_dist`, `map_span_int_linearEquiv`, `mem_span_int_basisFun_iff`.
- **KEEP-BOTH**: character-orthogonality adapters, the two density "routes", explicit/implicit
  residue-fibre pair, ℝ-vs-ℂ `N𝔭^{-s}<1`.
