# Inventory: ./HasseWeil/FormalGroup/Differential.lean

File: `HasseWeil/FormalGroup/Differential.lean`
Total lines: 1410
Module: Invariant Differential for Formal Groups (Silverman IV.4)

---

## Public Declarations

---

### `noncomputable def FormalGroup.dX_at_zero`

- **Type**: `(F : FormalGroup R) : PowerSeries R`
- **What**: Defines `F_X(0, T)`, the formal partial derivative of the formal group series `F(X, Y)` with respect to `X`, evaluated at `X = 0`. Concretely, the `n`-th coefficient is the coefficient of `X¹Yⁿ` in `F(X, Y)`.
- **How**: Direct construction via `PowerSeries.mk` with coefficient function reading `MvPowerSeries.coeff (single 0 1 + single 1 n) F.toSeries`.
- **Hypotheses**: `R` a commutative ring, `F` a formal group over `R`.
- **Uses from project**: `FormalGroup.toSeries`
- **Used by**: `dX_at_zero_constantCoeff`, `dX_at_zero_isUnit`, `dX_at_zero_mul_invariantDiff`, `invariantDiff_mul_dX_at_zero`, `coeff_10_rhs`, `coeff_10_FG_pow`, `coeff_10_lhs`, `dX_at_zero_chain`, `invariantDiff_chain`, `subst_zero_X0_pderiv0`, `subst_zero_F_pderiv0_eq`, `dX_at_zero_translation`, `invariantDiff_translation`; also used in `FormalGroup/Logarithm.lean` (direct coefficient access)
- **Visibility**: public
- **Lines**: 47–50 (definition, 3 lines)
- **Notes**: none

---

### `theorem FormalGroup.dX_at_zero_constantCoeff`

- **Type**: `(F : FormalGroup R) : PowerSeries.constantCoeff F.dX_at_zero = 1`
- **What**: The constant term of `F_X(0, T)` is 1, reflecting that `F(X, 0) = X` implies the `X¹`-coefficient of `F` at `Y = 0` equals 1.
- **How**: Applies `F.lunit` (left unit axiom `F(X, 0) = X`), extracts the coefficient via `MvPowerSeries.coeff_subst` with `hasSubst_of_constantCoeff_zero`, uses `finsum_eq_single` to isolate the surviving term, and handles all other multi-indices by case splitting on whether the `Y`-exponent is zero.
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `FormalGroup.dX_at_zero`, `FormalGroup.lunit`
- **Used by**: `dX_at_zero_isUnit`, `dX_at_zero_mul_invariantDiff`, `invariantDiff_mul_dX_at_zero`
- **Visibility**: public
- **Lines**: 56–95 (proof ~38 lines)
- **Notes**: Long proof (≈38 lines); handles the multivariate finsum carefully.

---

### `theorem FormalGroup.dX_at_zero_isUnit`

- **Type**: `(F : FormalGroup R) : IsUnit F.dX_at_zero`
- **What**: States that `F_X(0, T)` is a unit in `R⟦T⟧`.
- **How**: Reduces via `PowerSeries.isUnit_iff_constantCoeff` to checking the constant coefficient equals a unit, which follows from `dX_at_zero_constantCoeff` and `isUnit_one`.
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `FormalGroup.dX_at_zero_constantCoeff`
- **Used by**: `invariantDiff_chain`
- **Visibility**: public
- **Lines**: 98–101 (proof 2 lines)
- **Notes**: none

---

### `noncomputable def FormalGroup.invariantDiff`

- **Type**: `(F : FormalGroup R) : PowerSeries R`
- **What**: Defines the normalized invariant differential `ω_F = F_X(0, T)⁻¹ ∈ R⟦T⟧` using `PowerSeries.invOfUnit`.
- **How**: Wraps `PowerSeries.invOfUnit F.dX_at_zero 1`, which is well-defined because the constant coefficient of `F.dX_at_zero` is 1 (a unit).
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `FormalGroup.dX_at_zero`
- **Used by**: `dX_at_zero_mul_invariantDiff`, `invariantDiff_mul_dX_at_zero`, `invariantDiff_constantCoeff`, `invariantDiff_chain`, `dX_at_zero_translation`, `invariantDiff_translation`; also `FormalGroup/InvariantDiff.lean`, `FormalGroup/Logarithm.lean`
- **Visibility**: public
- **Lines**: 116–117 (definition, 1 line)
- **Notes**: none

---

### `@[simp] theorem FormalGroup.dX_at_zero_mul_invariantDiff`

- **Type**: `(F : FormalGroup R) : F.dX_at_zero * F.invariantDiff = 1`
- **What**: The product `F_X(0, T) · ω_F = 1` in `R⟦T⟧`.
- **How**: Direct application of `PowerSeries.mul_invOfUnit` with the unit-witness from `dX_at_zero_constantCoeff`.
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `FormalGroup.invariantDiff`, `FormalGroup.dX_at_zero_constantCoeff`
- **Used by**: `invariantDiff_chain`, `dX_at_zero_translation` (indirectly via `invariantDiff_translation`)
- **Visibility**: public (simp lemma)
- **Lines**: 121–124 (proof 3 lines)
- **Notes**: none

---

### `@[simp] theorem FormalGroup.invariantDiff_mul_dX_at_zero`

- **Type**: `(F : FormalGroup R) : F.invariantDiff * F.dX_at_zero = 1`
- **What**: The symmetric version: `ω_F · F_X(0, T) = 1`.
- **How**: `PowerSeries.invOfUnit_mul` with the unit-witness.
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `FormalGroup.dX_at_zero_constantCoeff`
- **Used by**: `invariantDiff_chain`, `invariantDiff_translation`
- **Visibility**: public (simp lemma)
- **Lines**: 128–131 (proof 3 lines)
- **Notes**: none

---

### `@[simp] theorem FormalGroup.invariantDiff_constantCoeff`

- **Type**: `(F : FormalGroup R) : PowerSeries.constantCoeff F.invariantDiff = 1`
- **What**: The constant coefficient of the invariant differential is 1 (normalization condition).
- **How**: Unfolds `invariantDiff` and applies `PowerSeries.constantCoeff_invOfUnit`.
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `FormalGroup.invariantDiff`
- **Used by**: unused in file (used in `FormalGroup/InvariantDiff.lean`, `FormalGroup/CharP.lean`)
- **Visibility**: public (simp lemma)
- **Lines**: 135–137 (proof 2 lines)
- **Notes**: none

---

### `theorem FormalGroupHom.hasSubst`

- **Type**: `(f : FormalGroupHom F G) : PowerSeries.HasSubst (S := R) f.toSeries`
- **What**: States that a formal group homomorphism series has zero constant coefficient, making it a valid substitution argument.
- **How**: Applies `PowerSeries.HasSubst.of_constantCoeff_zero'` with `f.zero_const`.
- **Hypotheses**: `F G : FormalGroup R` formal groups, `f` a homomorphism between them.
- **Uses from project**: `FormalGroupHom.zero_const`
- **Used by**: `coeff_10_rhs` (lines 468, 482), `invariantDiff_chain` (line 851); used externally in `FormalGroup/Hom.lean` (via `hasSubst_pair_lift`, related name)
- **Visibility**: public
- **Lines**: 153–155 (proof 1 line)
- **Notes**: none

---

### `theorem FormalGroup.dX_at_zero_chain`

- **Type**: `(f : FormalGroupHom F G) : (PowerSeries.derivative R f.toSeries) * F.dX_at_zero = PowerSeries.C (PowerSeries.coeff 1 f.toSeries) * PowerSeries.subst f.toSeries G.dX_at_zero`
- **What**: The intermediate chain rule identity: `f'(T) · F_X(0,T) = c₁ · G_X(0, f(T))` where `c₁` is the linear coefficient of `f`. This is the coefficient-level content of Silverman IV.4 Prop. 4.2.
- **How**: For each `n`, applies `f.preserves_add` (functoriality of `f` under `F`), extracts the coefficient at multi-index `(1, n)` of both sides, uses `coeff_10_lhs` (LHS) and `coeff_10_rhs` (RHS) to simplify, and concludes by `PowerSeries.coeff_C_mul`.
- **Hypotheses**: `F G : FormalGroup R`, `f : FormalGroupHom F G`.
- **Uses from project**: `coeff_10_lhs`, `coeff_10_rhs`, `FormalGroupHom.preserves_add`, `FormalGroup.dX_at_zero`
- **Used by**: `invariantDiff_chain` (line 846)
- **Visibility**: public
- **Lines**: 807–819 (proof 12 lines)
- **Notes**: none

---

### `theorem FormalGroup.invariantDiff_chain`

- **Type**: `(f : FormalGroupHom F G) : PowerSeries.subst f.toSeries G.invariantDiff * PowerSeries.derivative R f.toSeries = PowerSeries.C (PowerSeries.coeff 1 f.toSeries) * F.invariantDiff`
- **What**: **Corollary IV.4.3**: the pullback of ω_G along f satisfies `ω_G(f(T)) · f'(T) = c₁ · ω_F(T)`. This is the formal-group analogue of `φ*(ω) = a_φ · ω`.
- **How**: Uses `dX_at_zero_chain` as the key intermediate step, then cancels the unit `dX_at_zero F` from both sides (using `dX_at_zero_isUnit.mul_right_cancel`) via a calculation chain: computes `ωG' * f' * dF = c₁` and `c₁ * ωF * dF = c₁` using `invariantDiff_mul_dX_at_zero` and `dX_at_zero_mul_invariantDiff`. Substitution homomorphism `substAlgHom` is used to prove `ωG' * dG' = 1`.
- **Hypotheses**: `F G : FormalGroup R`, `f : FormalGroupHom F G`.
- **Uses from project**: `FormalGroup.dX_at_zero_chain`, `FormalGroup.dX_at_zero_isUnit`, `FormalGroup.invariantDiff_mul_dX_at_zero`, `FormalGroup.dX_at_zero_mul_invariantDiff`, `FormalGroupHom.hasSubst`
- **Used by**: unused in file (used in `FormalGroup/InvariantDiff.lean`, referenced in `GapQfKernel.lean` comments)
- **Visibility**: public
- **Lines**: 833–874 (proof ~41 lines)
- **Notes**: Long proof (≈41 lines); key external output of the first half of the file.

---

### `theorem dX_at_zero_translation`

- **Type**: `(F : FormalGroup R) : PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.dX_at_zero * MvPowerSeries.pderiv 0 F.toSeries = PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.dX_at_zero`
- **What**: The translation identity for `dX_at_zero`: `F_X(0, T) · F_X(T, S) = F_X(0, F(T, S))` in `MvPowerSeries (Fin 2) R`, expressing that `F_X(0, -)` is translation-invariant.
- **How**: Differentiates the associativity identity `F(F(X,Y),Z) = F(X,F(Y,Z))` with respect to `X` (via `pderiv_assoc_identity`), then specializes to `X = 0` by applying the `shift3to2` substitution `(0 ↦ 0, 1 ↦ X 0, 2 ↦ X 1)` (using `MvPowerSeries.subst_comp_subst_apply` and the composition lemmas `shift3to2_comp_pairXY/assocL/assocR`), and finally identifies `F_X(0, -)` with `dX_at_zero` via `subst_zero_X0_pderiv0` and `subst_zero_F_pderiv0_eq`.
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `pderiv_assoc_identity`, `shift3to2_comp_pairXY`, `shift3to2_comp_assocL`, `shift3to2_comp_assocR`, `subst_zero_X0_pderiv0`, `subst_zero_F_pderiv0_eq`, `hasSubst_pairXY`, `hasSubst_assocL`, `hasSubst_assocR`, `hasSubst_shift3to2`
- **Used by**: `invariantDiff_translation` (line 1383)
- **Visibility**: public
- **Lines**: 1334–1352 (proof ~18 lines)
- **Notes**: none

---

### `theorem invariantDiff_translation`

- **Type**: `(F : FormalGroup R) : PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.invariantDiff * MvPowerSeries.pderiv 0 F.toSeries = PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) F.invariantDiff`
- **What**: **Silverman IV.4.2**: the invariant differential is translation-invariant: `ω_F(F(T,S)) · F_X(T,S) = ω_F(T)` in `MvPowerSeries (Fin 2) R`.
- **How**: Sets `A = dX_at_zero(X 0)`, `B = pderiv 0 F`, `C = dX_at_zero(F)`, `α = ω_F(X 0)`, `γ = ω_F(F)`. Uses `dX_at_zero_translation` for `A * B = C`, proves `A * α = 1` and `C * γ = 1` via `substAlgHom.map_one` and `dX_at_zero_mul_invariantDiff`, then establishes `γ * B = α` by a calculation chain using associativity and commutativity.
- **Hypotheses**: `R` a commutative ring, `F` a formal group.
- **Uses from project**: `FormalGroup.dX_at_zero_mul_invariantDiff`, `dX_at_zero_translation`, `FG.constantCoeff_FG_toSeries`
- **Used by**: unused in file (used in `FormalGroup/Logarithm.lean` line 1280)
- **Visibility**: public (inside `namespace FormalGroup`)
- **Lines**: 1365–1406 (proof ~41 lines)
- **Notes**: Long proof (≈41 lines); note that `dX_at_zero_translation` is proved *before* the namespace block and is technically `FormalGroup.dX_at_zero_translation` (or just `dX_at_zero_translation` as named).

---

## Private Declarations

---

### `private theorem coeff_subst_runit_eq`

- **Type**: `(n : ℕ) (phi : MvPowerSeries (Fin 2) R) : MvPowerSeries.coeff (single 1 n) (subst ![0, X 1] phi) = MvPowerSeries.coeff (single 1 n) phi`
- **What**: Substituting `X₀ ↦ 0, X₁ ↦ X₁` preserves coefficients supported on `{X₁}`.
- **How**: Expands via `coeff_subst`, applies `finsum_eq_single` to isolate the unique surviving summand `d = single 1 n`, handles off-diagonal terms by zero-power-kills argument.
- **Hypotheses**: none beyond `R` a commutative ring.
- **Uses from project**: none
- **Used by**: `coeff_single1_F`, `coeff_runit_pow`
- **Visibility**: private
- **Lines**: 169–196 (proof ~26 lines)
- **Notes**: none

---

### `private theorem coeff_single1_F`

- **Type**: `(F : FormalGroup R) (m : ℕ) : MvPowerSeries.coeff (single 1 m) F.toSeries = if m = 1 then 1 else 0`
- **What**: The coefficient of `Y^m` (no `X`) in `F(X, Y)` is 1 if `m = 1` and 0 otherwise, reflecting `F(0, Y) = Y`.
- **How**: Uses `coeff_subst_runit_eq` to commute substitution through, then applies `F.runit` and `coeff_X_pow`.
- **Hypotheses**: `F` a formal group.
- **Uses from project**: `coeff_subst_runit_eq`, `FormalGroup.runit`
- **Used by**: `antidiag_term_vanish`, `coeff_10_FG_pow`
- **Visibility**: private
- **Lines**: 199–208 (proof ~8 lines)
- **Notes**: none

---

### `private theorem coeff_runit_pow`

- **Type**: `(F : FormalGroup R) (k n : ℕ) : MvPowerSeries.coeff (single 1 n) (F.toSeries ^ k) = if n = k then 1 else 0`
- **What**: The coefficient of `Y^n` in `F(0, Y)^k` is `[n = k]`, since `F(0, Y) = Y` gives `F(0, Y)^k = Y^k`.
- **How**: Uses `coeff_subst_runit_eq` then `MvPowerSeries.subst_pow` and `F.runit` to reduce to `coeff_X_pow`.
- **Hypotheses**: `F` a formal group.
- **Uses from project**: `coeff_subst_runit_eq`, `FormalGroup.runit`
- **Used by**: `antidiag_term_vanish`, `coeff_10_FG_pow`
- **Visibility**: private
- **Lines**: 212–221 (proof ~9 lines)
- **Notes**: none

---

### `private theorem coeff_one_pow_eq_zero`

- **Type**: `{f : PowerSeries R} (hf : constantCoeff f = 0) {d : ℕ} (hd : 2 ≤ d) : PowerSeries.coeff 1 (f ^ d) = 0`
- **What**: For a power series with zero constant coefficient and exponent `d ≥ 2`, the coefficient of `T¹` in `f^d` is zero.
- **How**: Shows `X^d ∣ f^d` via `pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) d`, then applies `X_pow_dvd_iff`.
- **Hypotheses**: `f` a power series with `constantCoeff f = 0`, `d ≥ 2`.
- **Uses from project**: none
- **Used by**: `coeff_one_pow`
- **Visibility**: private
- **Lines**: 224–229 (proof ~5 lines)
- **Notes**: none

---

### `private theorem coeff_one_pow`

- **Type**: `{f : PowerSeries R} (hf : constantCoeff f = 0) (d : ℕ) : PowerSeries.coeff 1 (f ^ d) = if d = 1 then PowerSeries.coeff 1 f else 0`
- **What**: The coefficient of `T¹` in `f^d` is `coeff_1 f` if `d = 1` and 0 otherwise (for series with zero constant term).
- **How**: Case splits on `d = 1`, `d = 0` (gives `coeff_1 1 = 0`), and `d ≥ 2` (uses `coeff_one_pow_eq_zero`).
- **Hypotheses**: `constantCoeff f = 0`.
- **Uses from project**: `coeff_one_pow_eq_zero`
- **Used by**: `coeff_10_rhs`
- **Visibility**: private
- **Lines**: 232–243 (proof ~11 lines)
- **Notes**: none

---

### `private theorem coeff_subst_X0`

- **Type**: `(g : PowerSeries R) (a b : ℕ) : MvPowerSeries.coeff (single 0 a + single 1 b) (PowerSeries.subst (X 0) g) = if b = 0 then PowerSeries.coeff a g else 0`
- **What**: The coefficient at multi-index `(a, b)` of `g(X₀)` (univariate `g` substituted into variable `X₀`) equals `coeff_a g` if `b = 0` and 0 otherwise.
- **How**: Applies `PowerSeries.coeff_subst`, uses `finsum_eq_single` for the `b = 0` case, and `finsum_eq_zero_of_forall_eq_zero` for the `b ≠ 0` case.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: none
- **Used by**: `coeff_10_prod_orthogonal`
- **Visibility**: private
- **Lines**: 247–272 (proof ~24 lines)
- **Notes**: none

---

### `private theorem coeff_subst_X1`

- **Type**: `(g : PowerSeries R) (a b : ℕ) : MvPowerSeries.coeff (single 0 a + single 1 b) (PowerSeries.subst (X 1) g) = if a = 0 then PowerSeries.coeff b g else 0`
- **What**: The symmetric version of `coeff_subst_X0` for substitution into variable `X₁`.
- **How**: Same structure as `coeff_subst_X0` with roles of `a` and `b` swapped.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: none
- **Used by**: `coeff_10_prod_orthogonal`
- **Visibility**: private
- **Lines**: 274–299 (proof ~24 lines)
- **Notes**: none

---

### `private lemma finsupp_fin2_decompose`

- **Type**: `(e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1)`
- **What**: Every `Fin 2`-indexed finitely-supported function decomposes as a sum of two singletons.
- **How**: `ext i; fin_cases i` then `simp`.
- **Hypotheses**: none.
- **Uses from project**: none
- **Used by**: `coeff_10_prod_orthogonal`
- **Visibility**: private
- **Lines**: 302–304 (proof 2 lines)
- **Notes**: none

---

### `private theorem coeff_10_prod_orthogonal` *(set_option maxHeartbeats 800000)*

- **Type**: `(g : PowerSeries R) (d0 d1 n : ℕ) : MvPowerSeries.coeff (single 0 1 + single 1 n) (g(X₀)^d0 * g(X₁)^d1) = PowerSeries.coeff 1 (g^d0) * PowerSeries.coeff n (g^d1)`
- **What**: An orthogonality lemma: the `(1, n)`-coefficient of the product `g(X₀)^d0 * g(X₁)^d1` factors as the product of a univariate coefficient on each factor.
- **How**: Rewrites powers using `subst_pow`, expands the product via `coeff_mul` over the antidiagonal, uses `finsupp_fin2_decompose`, `coeff_subst_X0`, `coeff_subst_X1` to identify the unique surviving summand, and proves all other antidiagonal terms vanish.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: `coeff_subst_X0`, `coeff_subst_X1`, `finsupp_fin2_decompose`
- **Used by**: `coeff_10_rhs`
- **Visibility**: private
- **Lines**: 307–365 (proof ~57 lines)
- **Notes**: Long proof (≈57 lines); `set_option maxHeartbeats 800000` with NO-COMMENT.

---

### `private lemma prod_subst_vec`

- **Type**: `(f : FormalGroupHom F G) (d : Fin 2 →₀ ℕ) : d.prod (fun s e => (![subst (X 0) f, subst (X 1) f] s)^e) = (subst (X 0) f)^(d 0) * (subst (X 1) f)^(d 1)`
- **What**: Expands the Finsupp.prod over `{0, 1}` into an explicit product of two terms.
- **How**: `Finsupp.prod_fintype` + `Fin.prod_univ_two` + `simp`.
- **Hypotheses**: `f : FormalGroupHom F G`.
- **Uses from project**: none
- **Used by**: `coeff_10_rhs`
- **Visibility**: private
- **Lines**: 368–375 (proof ~6 lines)
- **Notes**: none

---

### `private lemma hasSubst_subst_vec`

- **Type**: `(f : FormalGroupHom F G) : MvPowerSeries.HasSubst ![subst (X 0) f, subst (X 1) f]`
- **What**: The substitution vector `[f(X₀), f(X₁)]` satisfies `HasSubst` (constant coefficients are zero).
- **How**: Applies `hasSubst_of_constantCoeff_zero`; for each slot, computes `constantCoeff (subst (X i) f) = 0` via `PowerSeries.constantCoeff_subst` and `finsum_eq_zero_of_forall_eq_zero`.
- **Hypotheses**: `f : FormalGroupHom F G`.
- **Uses from project**: `FormalGroupHom.zero_const`
- **Used by**: `coeff_10_rhs`
- **Visibility**: private
- **Lines**: 378–391 (proof ~13 lines)
- **Notes**: none

---

### `private lemma finsum_fin2_reduce_full`

- **Type**: `(p : (Fin 2 →₀ ℕ) → R) : (∑ᶠ d, if d 0 = 1 then p d else 0) = ∑ᶠ k, p (single 0 1 + single 1 k)`
- **What**: Reindexes a finsum over `Fin 2 →₀ ℕ` with the indicator `{d | d 0 = 1}` to a finsum over `ℕ`, mapping `k ↦ single 0 1 + single 1 k`.
- **How**: Constructs the injection `ι : ℕ → Fin 2 →₀ ℕ`, uses `Set.indicator`, `finsum_subtype_eq_finsum_cond`, and `finsum_comp_equiv` with `Equiv.ofInjective`.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: none
- **Used by**: `coeff_10_rhs`
- **Visibility**: private
- **Lines**: 395–421 (proof ~26 lines)
- **Notes**: none

---

### `private lemma mul_finsum_of_support_subset`

- **Type**: `{α : Type*} (c : R) (f : α → R) {s : Finset α} (hs : support f ⊆ ↑s) : c * (∑ᶠ a, f a) = ∑ᶠ a, c * f a`
- **What**: Scalar multiplication distributes over a finsum when the support is finite.
- **How**: Converts both finsums to finset sums using `finsum_eq_finset_sum_of_support_subset`, then applies `Finset.mul_sum`.
- **Hypotheses**: `support f ⊆ ↑s` for some finite `s`.
- **Uses from project**: none
- **Used by**: `coeff_10_rhs`
- **Visibility**: private
- **Lines**: 424–431 (proof ~7 lines)
- **Notes**: none

---

### `private theorem coeff_10_rhs` *(set_option maxHeartbeats 3200000)*

- **Type**: `(F G : FormalGroup R) (f : FormalGroupHom F G) (n : ℕ) : MvPowerSeries.coeff (single 0 1 + single 1 n) (subst ![subst (X 0) f, subst (X 1) f] G.toSeries) = coeff 1 f.toSeries * coeff n (subst f G.dX_at_zero)`
- **What**: Computes the `(1, n)`-coefficient of `G(f(X₀), f(X₁))` as `c₁ · [G_X(0, f)]_n`, where `c₁` is the linear coefficient of `f`. This is the RHS of the chain rule identity.
- **How**: Expands via `coeff_subst`, applies `prod_subst_vec`, `coeff_10_prod_orthogonal`, and `coeff_one_pow`; reindexes via `finsum_fin2_reduce_full`; expands the RHS via `PowerSeries.coeff_subst'`; factors out `c₁` using `mul_finsum_of_support_subset`.
- **Hypotheses**: `F G : FormalGroup R`, `f : FormalGroupHom F G`.
- **Uses from project**: `hasSubst_subst_vec`, `prod_subst_vec`, `coeff_10_prod_orthogonal`, `coeff_one_pow`, `finsum_fin2_reduce_full`, `mul_finsum_of_support_subset`, `FormalGroup.dX_at_zero`, `FormalGroupHom.hasSubst`
- **Used by**: `dX_at_zero_chain`
- **Visibility**: private
- **Lines**: 435–485 (proof ~49 lines)
- **Notes**: Long proof (≈49 lines); `set_option maxHeartbeats 3200000` with NO-COMMENT.

---

### `private theorem antidiag_term_vanish` *(set_option maxHeartbeats 1600000)*

- **Type**: `(F : FormalGroup R) (d n : ℕ) (e1 e2 : Fin 2 →₀ ℕ) (hsum : e1 + e2 = single 0 1 + single 1 n) (hA : ¬(e1 0 = 0 ∧ e1 1 = 1)) (hB : ¬(e1 0 = 1 ∧ e2 1 = d)) : coeff e1 F.toSeries * coeff e2 (F^d) = 0`
- **What**: In the antidiagonal sum for `coeff_{(1,n)}(F^(d+1))`, all summands that are neither "pair A" nor "pair B" (the two survivors) vanish.
- **How**: Case splits on `e1 0 = 0` (uses `coeff_single1_F`) vs. `e1 0 ≥ 1` (implies `e2 0 = 0`, uses `coeff_runit_pow`).
- **Hypotheses**: Antidiagonal constraint + negations of the two survival conditions.
- **Uses from project**: `coeff_single1_F`, `coeff_runit_pow`
- **Used by**: `coeff_10_FG_pow`
- **Visibility**: private
- **Lines**: 489–511 (proof ~21 lines)
- **Notes**: `set_option maxHeartbeats 1600000` with NO-COMMENT.

---

### `private theorem coeff_10_FG_pow` *(set_option maxHeartbeats 6400000)*

- **Type**: `(F : FormalGroup R) (d n : ℕ) : MvPowerSeries.coeff (single 0 1 + single 1 n) (F.toSeries ^ d) = if d ≤ n + 1 then (d : R) * coeff (n + 1 - d) F.dX_at_zero else 0`
- **What**: Computes the `(1, n)`-coefficient of `F^d` as `d · [dX_at_zero F]_{n+1-d}` when `d ≤ n+1`, and 0 otherwise.
- **How**: Induction on `d`. Base: `F^0 = 1`, coefficient is 0 (not the identity multi-index). Step: `F^(d+1) = F · F^d`; expands `coeff_mul`, isolates the two surviving antidiagonal pairs A and B using `antidiag_term_vanish`, computes their values using `coeff_single1_F` and `coeff_runit_pow`, and combines via the induction hypothesis. For `d + 1 > n + 1`, uses `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`.
- **Hypotheses**: `F` a formal group.
- **Uses from project**: `coeff_single1_F`, `coeff_runit_pow`, `antidiag_term_vanish`, `FormalGroup.dX_at_zero`, `FG.constantCoeff_FG_toSeries`
- **Used by**: `coeff_10_lhs`
- **Visibility**: private
- **Lines**: 514–724 (proof ~209 lines)
- **Notes**: Very long proof (≈209 lines); `set_option maxHeartbeats 6400000` with NO-COMMENT. The inductive structure handles both the `n = 0` and `n ≥ 1` sub-cases separately.

---

### `private theorem coeff_10_lhs` *(set_option maxHeartbeats 6400000)*

- **Type**: `(F G : FormalGroup R) (f : FormalGroupHom F G) (n : ℕ) : MvPowerSeries.coeff (single 0 1 + single 1 n) (PowerSeries.subst F.toSeries f.toSeries) = PowerSeries.coeff n (derivative R f.toSeries * F.dX_at_zero)`
- **What**: Computes the `(1, n)`-coefficient of `f(F(X, Y))` as `[f' · dX_at_zero F]_n`. This is the LHS of the chain rule identity.
- **How**: Expands via `PowerSeries.coeff_subst`, applies `coeff_10_FG_pow`, expands the RHS via `coeff_mul` and `coeff_derivative`, converts the finsum to a Finset.sum over `range (n+2)`, peels off the `d = 0` term, simplifies `if` branches, and matches via `Finset.sum_nbij'`.
- **Hypotheses**: `F G : FormalGroup R`, `f : FormalGroupHom F G`.
- **Uses from project**: `coeff_10_FG_pow`, `FormalGroup.dX_at_zero`, `FG.constantCoeff_FG_toSeries`
- **Used by**: `dX_at_zero_chain`
- **Visibility**: private
- **Lines**: 728–805 (proof ~77 lines)
- **Notes**: Long proof (≈77 lines); `set_option maxHeartbeats 6400000` with NO-COMMENT.

---

### `private noncomputable def pairXY`

- **Type**: `(R : Type*) [CommRing R] : Fin 2 → MvPowerSeries (Fin 3) R`
- **What**: The substitution vector `![X 0, X 1]` for the `(X, Y)` slot in Silverman's associativity argument.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: none
- **Used by**: `assocL`, `hasSubst_pairXY`, `pderiv_subst_assocL`, `shift3to2_comp_pairXY`, `shift3to2_comp_assocL`
- **Visibility**: private
- **Lines**: 892–894 (definition, 2 lines)
- **Notes**: none

---

### `private noncomputable def pairYZ`

- **Type**: `(R : Type*) [CommRing R] : Fin 2 → MvPowerSeries (Fin 3) R`
- **What**: The substitution vector `![X 1, X 2]` for the `(Y, Z)` slot.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: none
- **Used by**: `assocR`, `hasSubst_pairYZ`, `pderiv_subst_assocR`, `shift3to2_comp_pairYZ`, `shift3to2_comp_assocR`
- **Visibility**: private
- **Lines**: 898–900 (definition, 2 lines)
- **Notes**: none

---

### `private noncomputable def assocL`

- **Type**: `(F : FormalGroup R) : Fin 2 → MvPowerSeries (Fin 3) R`
- **What**: The "left" outer substitution `![F(X, Y), Z]` for the LHS of associativity.
- **Hypotheses**: `F` a formal group.
- **Uses from project**: `pairXY`, `FormalGroup.toSeries`
- **Used by**: `hasSubst_assocL`, `pderiv_subst_assocL`, `pderiv_assoc_identity`, `shift3to2_comp_assocL`
- **Visibility**: private
- **Lines**: 903–906 (definition, 3 lines)
- **Notes**: none

---

### `private noncomputable def assocR`

- **Type**: `(F : FormalGroup R) : Fin 2 → MvPowerSeries (Fin 3) R`
- **What**: The "right" outer substitution `![X, F(Y, Z)]` for the RHS of associativity.
- **Hypotheses**: `F` a formal group.
- **Uses from project**: `pairYZ`, `FormalGroup.toSeries`
- **Used by**: `hasSubst_assocR`, `pderiv_subst_assocR`, `pderiv_assoc_identity`, `shift3to2_comp_assocR`
- **Visibility**: private
- **Lines**: 909–912 (definition, 3 lines)
- **Notes**: none

---

### `private noncomputable def shift3to2`

- **Type**: `(R : Type*) [CommRing R] : Fin 3 → MvPowerSeries (Fin 2) R`
- **What**: The evaluation map `![0, X 0, X 1]` that specializes `X = 0` and relabels `(Y, Z) ↦ (X 0, X 1)`.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: none
- **Used by**: `hasSubst_shift3to2`, `shift3to2_comp_pairXY`, `shift3to2_comp_pairYZ`, `shift3to2_comp_assocL`, `shift3to2_comp_assocR`, `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 917–919 (definition, 2 lines)
- **Notes**: none

---

### `private lemma hasSubst_pairXY`

- **Type**: `MvPowerSeries.HasSubst (pairXY R : Fin 2 → MvPowerSeries (Fin 3) R)`
- **What**: `pairXY` satisfies the `HasSubst` condition (each component has zero constant coefficient).
- **How**: `hasSubst_of_constantCoeff_zero` + `fin_cases`.
- **Uses from project**: `pairXY`
- **Used by**: `hasSubst_assocL`, `pderiv_subst_assocL`, `pderiv_assoc_identity` (implicit), `shift3to2_comp_assocL`, `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 921–924 (proof 3 lines)
- **Notes**: none

---

### `private lemma hasSubst_pairYZ`

- **Type**: `MvPowerSeries.HasSubst (pairYZ R : Fin 2 → MvPowerSeries (Fin 3) R)`
- **What**: `pairYZ` satisfies `HasSubst`.
- **How**: `hasSubst_of_constantCoeff_zero` + `fin_cases`.
- **Uses from project**: `pairYZ`
- **Used by**: `hasSubst_assocR`, `pderiv_subst_assocR`, `shift3to2_comp_assocR`, `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 926–929 (proof 3 lines)
- **Notes**: none

---

### `private lemma hasSubst_assocL`

- **Type**: `(F : FormalGroup R) : MvPowerSeries.HasSubst (assocL F)`
- **What**: `assocL F = ![F(X,Y), Z]` satisfies `HasSubst`.
- **How**: `hasSubst_of_constantCoeff_zero`; component 0 uses `MvPowerSeries.constantCoeff_subst_eq_zero` with `hasSubst_pairXY` and `FG.constantCoeff_FG_toSeries`; component 1 is `X 2` which is trivially zero at constant.
- **Uses from project**: `assocL`, `hasSubst_pairXY`, `pairXY`, `FG.constantCoeff_FG_toSeries`
- **Used by**: `pderiv_subst_assocL`, `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 931–943 (proof ~12 lines)
- **Notes**: none

---

### `private lemma hasSubst_assocR`

- **Type**: `(F : FormalGroup R) : MvPowerSeries.HasSubst (assocR F)`
- **What**: `assocR F = ![X, F(Y,Z)]` satisfies `HasSubst`.
- **How**: Symmetric to `hasSubst_assocL` using `hasSubst_pairYZ`.
- **Uses from project**: `assocR`, `hasSubst_pairYZ`, `pairYZ`, `FG.constantCoeff_FG_toSeries`
- **Used by**: `pderiv_subst_assocR`, `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 945–957 (proof ~12 lines)
- **Notes**: none

---

### `private lemma hasSubst_shift3to2`

- **Type**: `MvPowerSeries.HasSubst (shift3to2 R : Fin 3 → MvPowerSeries (Fin 2) R)`
- **What**: `shift3to2` satisfies `HasSubst`.
- **How**: `hasSubst_of_constantCoeff_zero` + `fin_cases` + `simp [shift3to2]`.
- **Uses from project**: `shift3to2`
- **Used by**: `shift3to2_comp_pairXY`, `shift3to2_comp_pairYZ`, `shift3to2_comp_assocL`, `shift3to2_comp_assocR`, `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 959–962 (proof 3 lines)
- **Notes**: none

---

### `private lemma pderiv_subst_assocL`

- **Type**: `(F : FormalGroup R) : pderiv 0 (subst (assocL F) F) = subst (pairXY R) (pderiv 0 F) * subst (assocL F) (pderiv 0 F)`
- **What**: The partial derivative of `F(F(X,Y), Z)` with respect to the first variable factors as `F_X(X, Y) · F_X(F(X,Y), Z)` by the chain rule.
- **How**: Applies `MvPowerSeries.pderiv_subst_fin2`, computes `pderiv 0` of `assocL F 0` (using `pderiv_subst_fin2` for the inner substitution and `pderiv_X_self`) and `pderiv 0` of `assocL F 1 = X 2` (gives 0 via `pderiv_X_of_ne`), then simplifies.
- **Uses from project**: `assocL`, `hasSubst_assocL`, `hasSubst_pairXY`, `pairXY`
- **Used by**: `pderiv_assoc_identity`
- **Visibility**: private
- **Lines**: 968–997 (proof ~29 lines)
- **Notes**: none

---

### `private lemma pderiv_subst_assocR`

- **Type**: `(F : FormalGroup R) : pderiv 0 (subst (assocR F) F) = subst (assocR F) (pderiv 0 F)`
- **What**: The partial derivative of `F(X, F(Y, Z))` with respect to `X` is simply `F_X(X, F(Y,Z))`, since the inner `F(Y,Z)` does not depend on `X`.
- **How**: `pderiv_subst_fin2` on `assocR F`; `pderiv 0 (assocR F 0) = pderiv 0 (X 0) = 1`; `pderiv 0 (assocR F 1) = 0` via `pderiv_subst_fin2` on `pairYZ` (both components are `X 1`, `X 2`).
- **Uses from project**: `assocR`, `hasSubst_assocR`, `hasSubst_pairYZ`, `pairYZ`
- **Used by**: `pderiv_assoc_identity`
- **Visibility**: private
- **Lines**: 1000–1025 (proof ~25 lines)
- **Notes**: none

---

### `private lemma pderiv_assoc_identity`

- **Type**: `(F : FormalGroup R) : subst (pairXY R) (pderiv 0 F) * subst (assocL F) (pderiv 0 F) = subst (assocR F) (pderiv 0 F)`
- **What**: The identity obtained by differentiating `F.assoc` with respect to the first variable: `F_X(X,Y) · F_X(F(X,Y), Z) = F_X(X, F(Y,Z))`.
- **How**: Applies `pderiv` to both sides of `F.assoc`, uses definitional unfolding to match `assocL/assocR`, then substitutes the results of `pderiv_subst_assocL` and `pderiv_subst_assocR`.
- **Uses from project**: `assocL`, `assocR`, `pairXY`, `pairYZ`, `pderiv_subst_assocL`, `pderiv_subst_assocR`, `FormalGroup.assoc`
- **Used by**: `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 1029–1053 (proof ~24 lines)
- **Notes**: none

---

### `private lemma shift3to2_comp_pairXY`

- **Type**: `(fun s => subst (shift3to2 R) (pairXY R s)) = ![0, X 0]`
- **What**: The composition `shift3to2 ∘ pairXY` evaluates to `![0, X 0]`.
- **How**: `funext s; fin_cases s`, `subst_X hasSubst_shift3to2`.
- **Uses from project**: `shift3to2`, `pairXY`, `hasSubst_shift3to2`
- **Used by**: `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 1058–1070 (proof ~12 lines)
- **Notes**: none

---

### `private lemma shift3to2_comp_pairYZ`

- **Type**: `(fun s => subst (shift3to2 R) (pairYZ R s)) = ![X 0, X 1]`
- **What**: The composition `shift3to2 ∘ pairYZ` evaluates to `![X 0, X 1]` (the identity substitution).
- **How**: `funext s; fin_cases s`, `subst_X hasSubst_shift3to2`.
- **Uses from project**: `shift3to2`, `pairYZ`, `hasSubst_shift3to2`
- **Used by**: `shift3to2_comp_assocR`
- **Visibility**: private
- **Lines**: 1073–1086 (proof ~13 lines)
- **Notes**: none

---

### `private lemma runit_at_X0`

- **Type**: `(F : FormalGroup R) : subst ![0, X 0] F.toSeries = X 0`
- **What**: The right unit property `F(0, T) = T` specialized to variable `X 0` (a variant of `F.runit` for the `Fin 2`-indexed bivariate setting).
- **How**: Applies `subst_X` and `subst_comp_subst_apply` to `F.runit` after composing with the substitution `![X 0, X 0]`.
- **Uses from project**: `FormalGroup.runit`
- **Used by**: `shift3to2_comp_assocL`
- **Visibility**: private
- **Lines**: 1090–1131 (proof ~41 lines)
- **Notes**: Long proof (≈41 lines).

---

### `private lemma shift3to2_comp_assocL`

- **Type**: `(F : FormalGroup R) : (fun s => subst (shift3to2 R) (assocL F s)) = ![X 0, X 1]`
- **What**: After specializing `X = 0` via `shift3to2`, the `assocL F` substitution reduces to the identity `![X 0, X 1]`, using `F(0, X 0) = X 0`.
- **How**: Component 0: `subst_comp_subst_apply` + `shift3to2_comp_pairXY` + `runit_at_X0`. Component 1: `subst_X`.
- **Uses from project**: `assocL`, `hasSubst_pairXY`, `hasSubst_shift3to2`, `shift3to2_comp_pairXY`, `runit_at_X0`
- **Used by**: `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 1134–1148 (proof ~14 lines)
- **Notes**: none

---

### `private lemma shift3to2_comp_assocR`

- **Type**: `(F : FormalGroup R) : (fun s => subst (shift3to2 R) (assocR F s)) = ![0, F.toSeries]`
- **What**: After `shift3to2`, `assocR F` becomes `![0, F(X 0, X 1)]`.
- **How**: Component 0: `subst_X`. Component 1: `subst_comp_subst_apply` + `shift3to2_comp_pairYZ` + `subst_self`.
- **Uses from project**: `assocR`, `hasSubst_pairYZ`, `hasSubst_shift3to2`, `shift3to2_comp_pairYZ`
- **Used by**: `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 1151–1167 (proof ~16 lines)
- **Notes**: none

---

### `private lemma coeff_prod_subst_vec_zero_X0`

- **Type**: `(d e : Fin 2 →₀ ℕ) : MvPowerSeries.coeff e (d.prod (fun s n => (![0, X 0] s)^n)) = if d 0 = 0 then coeff e ((X 0)^(d 1)) else 0`
- **What**: Computes a coefficient in the product from the `![0, X 0]` substitution vector: it is zero when `d 0 ≠ 0` (the `0^(d 0)` factor kills the product) and equals the corresponding `(X 0)^(d 1)` coefficient when `d 0 = 0`.
- **How**: `Finsupp.prod_fintype` + `Fin.prod_univ_two` + `zero_pow` case split.
- **Uses from project**: none
- **Used by**: `subst_zero_X0_pderiv0`
- **Visibility**: private
- **Lines**: 1173–1184 (proof ~11 lines)
- **Notes**: none

---

### `private lemma subst_zero_X0_pderiv0`

- **Type**: `(F : FormalGroup R) : subst ![0, X 0] (pderiv 0 F.toSeries) = PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) F.dX_at_zero`
- **What**: Identifies `F_X(0, T)` (partial derivative at zero) with `dX_at_zero F` viewed as a univariate series in `X 0`.
- **How**: Expands both sides via `coeff_subst`, applies `coeff_prod_subst_vec_zero_X0`, reindexes the finsum via `Equiv.ofInjective` using the injection `n ↦ single 1 n`, and uses `MvPowerSeries.coeff_pderiv` to match with the `dX_at_zero` formula.
- **Uses from project**: `coeff_prod_subst_vec_zero_X0`, `FormalGroup.dX_at_zero`
- **Used by**: `subst_zero_F_pderiv0_eq`, `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 1187–1273 (proof ~86 lines)
- **Notes**: Long proof (≈86 lines); the reindexing argument is the key technical step.

---

### `private lemma subst_zero_F_pderiv0_eq`

- **Type**: `(F : FormalGroup R) : subst ![0, F.toSeries] (pderiv 0 F.toSeries) = PowerSeries.subst (F.toSeries : MvPowerSeries (Fin 2) R) F.dX_at_zero`
- **What**: The partial derivative `F_X(0, -)` substituted with `F` equals `dX_at_zero F` substituted with `F`.
- **How**: Applies `subst_comp_subst_apply` twice to express `subst ![0, F] (pderiv 0 F)` as `subst ![F, F] (subst ![0, X 0] (pderiv 0 F))`, then uses `subst_zero_X0_pderiv0` on the inner substitution and `subst_comp_subst_apply` for the `PowerSeries.subst (X 0)` on the RHS.
- **Uses from project**: `subst_zero_X0_pderiv0`, `FG.constantCoeff_FG_toSeries`
- **Used by**: `dX_at_zero_translation`
- **Visibility**: private
- **Lines**: 1279–1328 (proof ~49 lines)
- **Notes**: Long proof (≈49 lines).

---

## Summary of Key API

The primary exported results (used by ≥3 other declarations within this file or heavily used externally) are:

- `FormalGroup.dX_at_zero`: used throughout (10+ uses in file)
- `FormalGroup.dX_at_zero_constantCoeff`: used by `dX_at_zero_isUnit`, `dX_at_zero_mul_invariantDiff`, `invariantDiff_mul_dX_at_zero` (3 in file)
- `FormalGroup.dX_at_zero_mul_invariantDiff`: used by `invariantDiff_chain`, `invariantDiff_translation` (2 in file; also `InvariantDiff.lean`, `Logarithm.lean`)
- `FormalGroupHom.hasSubst`: used by `coeff_10_rhs` ×2 and `invariantDiff_chain` (3 in file)
