# Inventory: PadicLFunctions/Coleman/NormOperator.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Coleman/NormOperator.lean`
Namespace: `PadicLFunctions.Coleman`. Builds the norm operator `𝒩` on `ℤ_p⟦T⟧` (relative norm of the degree-`p` φ-extension), its mod-`p^k` congruence theory (T908), and compactness inputs (T909). Variable `(p : ℕ) [hp : Fact p.Prime]` throughout.

---

### def padicIntEquivIntegerRing
- Type: `(p : ℕ) [Fact p.Prime] → ℤ_[p] ≃+* integerRing ℚ_[p]`
- What: The ring isomorphism between `ℤ_[p]` and the norm-unit ball `integerRing ℚ_[p]`, both being `{x : ℚ_[p] // ‖x‖ ≤ 1}`.
- How: `RingEquiv.ofBijective` of the algebra map; injectivity via `PadicInt.ext` on the underlying `ℚ_[p]` value, surjectivity by exhibiting the obvious preimage `⟨(y : ℚ_[p]), y.2⟩`.
- Hypotheses: `p` prime (for `ℤ_[p]`); none beyond.
- Uses from project: []
- Used by: `existsUnique_digits_padicInt`
- Visibility: public
- Lines: 71–79 (def body ~9 lines)
- Notes: none

### theorem existsUnique_digits_padicInt
- Type: `(F : PowerSeries ℤ_[p]) → ∃! G : Fin p → PowerSeries ℤ_[p], IsDigitDecomp p F G`
- What: Every power series over `ℤ_[p]` has a unique digit decomposition `F = Σ_{i<p} (1+X)^i · φ(G i)`.
- How: Transports `FormalPsi.existsUnique_digits` (over `integerRing ℚ_[p]`) along `PowerSeries.map padicIntEquivIntegerRing`; key step is the round-trip `me' ∘ me = id` (`RingEquiv.symm_apply_apply`) and `isDigitDecomp_map` to move the decomposition predicate through the coefficient maps in both directions.
- Hypotheses: none beyond `p` prime.
- Uses from project: `padicIntEquivIntegerRing`, `existsUnique_digits`, `isDigitDecomp_map`, `IsDigitDecomp`
- Used by: `psiSeries_eq_of_isDigitDecomp_padicInt`, `psiSeries_add_padicInt`, `psiSeries_C_mul_padicInt`, `digitBasis`, `digitBasis_repr_eq`, `trace_digitMatrix`, `digit_modEq_of_sum_modEq`
- Visibility: public
- Lines: 84–106 (proof ~22 lines)
- Notes: long(30-50)? No — ~22 lines.

### theorem psiSeries_eq_of_isDigitDecomp_padicInt
- Type: `{F} {G} (hG : IsDigitDecomp p F G) → psiSeries p F = G 0`
- What: Over `ℤ_[p]`, `ψ` equals the 0-th digit of any digit decomposition.
- How: Direct application of `psiSeries_eq_of_unique` using the uniqueness from `existsUnique_digits_padicInt`.
- Hypotheses: `hG` is a digit decomposition of `F`.
- Uses from project: `IsDigitDecomp`, `psiSeries`, `psiSeries_eq_of_unique`, `existsUnique_digits_padicInt`
- Used by: `psiSeries_phi_padicInt`, `psiSeries_add_padicInt`, `psiSeries_C_mul_padicInt`, `trace_digitMatrix`
- Visibility: public
- Lines: 120–123 (proof 1 line)
- Notes: none

### theorem psiSeries_phi_padicInt
- Type: `(G : PowerSeries ℤ_[p]) → psiSeries p (phiSeries p G) = G`
- What: `ψ ∘ φ = id` over `ℤ_[p]` (the retraction property).
- How: The digit family of `φ(G)` is `(G, 0, …, 0)`; `Finset.sum_eq_single 0` collapses the digit sum, with off-diagonal terms killed by `phiSeries_zero`.
- Hypotheses: none.
- Uses from project: `psiSeries`, `phiSeries`, `psiSeries_eq_of_isDigitDecomp_padicInt`, `phiSeries_zero`
- Used by: `phi_injective_mod`
- Visibility: public
- Lines: 127–136 (proof ~9 lines)
- Notes: none

### theorem psiSeries_add_padicInt
- Type: `(F G : PowerSeries ℤ_[p]) → psiSeries p (F + G) = psiSeries p F + psiSeries p G`
- What: `ψ` is additive over `ℤ_[p]`.
- How: Take digit decompositions of `F` and `G`; their sum-family `i ↦ GF i + GG i` decomposes `F+G` (using `PowerSeries.subst_add` on `phiSeries` and `Finset.sum_add_distrib`); conclude via `psiSeries_eq_of_isDigitDecomp_padicInt`.
- Hypotheses: none.
- Uses from project: `psiSeries`, `existsUnique_digits_padicInt`, `psiSeries_eq_of_isDigitDecomp_padicInt`, `phiSeries`, `hasSubst_one_add_X_pow_sub_one`, `IsDigitDecomp`
- Used by: unused in file
- Visibility: public
- Lines: 139–149 (proof ~10 lines)
- Notes: none

### theorem psiSeries_C_mul_padicInt
- Type: `(a : ℤ_[p]) (F : PowerSeries ℤ_[p]) → psiSeries p (C a * F) = C a * psiSeries p F`
- What: `ψ(C a · F) = C a · ψ(F)` — `ℤ_[p]`-linearity of `ψ` on constants.
- How: Digit decomposition of `F`, scale by `C a` (family `i ↦ C a * GF i`), using `PowerSeries.subst_mul` and `PowerSeries.subst_C` to pull `C a` through `phiSeries`; finish via `psiSeries_eq_of_isDigitDecomp_padicInt`.
- Hypotheses: none.
- Uses from project: `psiSeries`, `existsUnique_digits_padicInt`, `psiSeries_eq_of_isDigitDecomp_padicInt`, `phiSeries`, `hasSubst_one_add_X_pow_sub_one`
- Used by: `phi_injective_mod`
- Visibility: public
- Lines: 153–166 (proof ~13 lines)
- Notes: none

### def phiHom
- Type: `(p : ℕ) [Fact p.Prime] → PowerSeries ℤ_[p] →+* PowerSeries ℤ_[p]`
- What: The Frobenius substitution `φ : F ↦ F((1+X)^p − 1)` packaged as a ring homomorphism.
- How: `substAlgHom (hasSubst_one_add_X_pow_sub_one p)` coerced via `.toRingHom`.
- Hypotheses: none.
- Uses from project: `hasSubst_one_add_X_pow_sub_one`
- Used by: `phiHom_apply`, `PhiAlg` Algebra instance, `phiSeries_sub`, `phiSeries_one_padicInt`, `phiSeries_one_add_X_pow`, `digit_modEq_of_sum_modEq`
- Visibility: public
- Lines: 181–182 (def body 2 lines)
- Notes: none

### theorem phiHom_apply
- Type: `(F) → phiHom p F = phiSeries p F`
- What: `phiHom` agrees with `phiSeries`.
- How: Unfold `phiSeries` and `PowerSeries.coe_substAlgHom`.
- Hypotheses: none.
- Uses from project: `phiHom`, `phiSeries`
- Used by: `PhiAlg.toPS_algebraMap`, `phiSeries_sub`, `phiSeries_one_padicInt`, `phiSeries_one_add_X_pow`, `digitMatrix_C`, `digit_modEq_of_sum_modEq`
- Visibility: public (`@[simp]`)
- Lines: 184–188 (proof ~3 lines)
- Notes: none

### def PhiAlg
- Type: `(p : ℕ) [Fact p.Prime] → Type`
- What: Type synonym for `PowerSeries ℤ_[p]` carrying the `φ`-algebra structure over `A = φ(ℤ_p⟦T⟧)`, so the structure does not leak onto bare `PowerSeries ℤ_[p]`.
- How: Definitionally `:= PowerSeries ℤ_[p]`.
- Hypotheses: none.
- Uses from project: []
- Used by: pervasive — `PhiAlg.toPS`, `digitBasis`, `normOp`, `digitMatrix`, `trace_digitBasis`, etc.
- Visibility: public
- Lines: 194
- Notes: none

### instance PhiAlg.instCommRing (anonymous)
- Type: `CommRing (PhiAlg p)`
- What: `PhiAlg p` is a commutative ring (inherited from `PowerSeries ℤ_[p]`).
- How: `inferInstanceAs (CommRing (PowerSeries ℤ_[p]))`.
- Hypotheses: none.
- Uses from project: `PhiAlg`
- Used by: implicitly by all `PhiAlg` algebra/module structure
- Visibility: public (instance)
- Lines: 198–199
- Notes: none

### instance PhiAlg.instAlgebra (anonymous)
- Type: `Algebra (PowerSeries ℤ_[p]) (PhiAlg p)`
- What: The `φ`-algebra structure: `ℤ_p⟦T⟧` acts on `PhiAlg p` through `φ`.
- How: `RingHom.toAlgebra (phiHom p)`.
- Hypotheses: none.
- Uses from project: `phiHom`, `PhiAlg`
- Used by: `digitBasis`, `normOp`, `trace_digitBasis`, `digitMatrix_C`, `trace_digitMatrix`
- Visibility: public (instance)
- Lines: 202–203
- Notes: none

### def PhiAlg.toPS
- Type: `(p : ℕ) [Fact p.Prime] → PhiAlg p ≃+* PowerSeries ℤ_[p]`
- What: Identity repackaging `PhiAlg p ≃+* PowerSeries ℤ_[p]` to move between module language and `IsDigitDecomp`.
- How: `RingEquiv.refl _` (same carrier and `CommRing`).
- Hypotheses: none.
- Uses from project: `PhiAlg`
- Used by: `toPS_apply`, `toPS_symm_apply`, `toPS_algebraMap`, `smul_def`, `sum_smul_one_add_X_pow_eq`, `digitBasis`, `normOp`, `digitMatrix`, `digitBasis_repr_eq`, `trace_digitMatrix`, `digitMatrix_C`, `digitMatrix_col_isDigitDecomp`, `normOp_modEq_self`
- Visibility: public
- Lines: 207
- Notes: none

### theorem PhiAlg.toPS_apply
- Type: `(x : PhiAlg p) → toPS p x = x`
- What: `toPS` is the identity on elements.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: `PhiAlg.toPS`
- Used by: `sum_smul_one_add_X_pow_eq`, `digitBasis`, `digitMatrix_col_isDigitDecomp`
- Visibility: public (`@[simp]`)
- Lines: 211–212
- Notes: none

### theorem PhiAlg.toPS_symm_apply
- Type: `(F : PowerSeries ℤ_[p]) → (toPS p).symm F = F`
- What: The inverse of `toPS` is also the identity on elements.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: `PhiAlg.toPS`
- Used by: unused in file (convenience simp lemma)
- Visibility: public (`@[simp]`)
- Lines: 214–215
- Notes: none

### theorem PhiAlg.toPS_algebraMap
- Type: `(c) → toPS p (algebraMap (PowerSeries ℤ_[p]) (PhiAlg p) c) = phiSeries p c`
- What: The image of the `φ`-algebra map under `toPS` is `φ(c)`.
- How: `RingHom.algebraMap_toAlgebra` then `phiHom_apply`.
- Hypotheses: none.
- Uses from project: `PhiAlg.toPS`, `PhiAlg` Algebra instance, `phiSeries`, `phiHom_apply`
- Used by: `PhiAlg.smul_def`, `digitMatrix_C`
- Visibility: public
- Lines: 218–221 (proof ~3 lines)
- Notes: none

### theorem PhiAlg.smul_def
- Type: `(c) (x : PhiAlg p) → toPS p (c • x) = phiSeries p c * toPS p x`
- What: The `φ`-scalar action on `PhiAlg p` is multiplication by the `φ`-image.
- How: `Algebra.smul_def`, `map_mul`, `toPS_algebraMap`.
- Hypotheses: none.
- Uses from project: `PhiAlg.toPS`, `phiSeries`, `PhiAlg.toPS_algebraMap`
- Used by: `sum_smul_one_add_X_pow_eq`
- Visibility: public
- Lines: 224–226 (proof ~2 lines)
- Notes: none

### theorem sum_smul_one_add_X_pow_eq
- Type: `(c : Fin p → PowerSeries ℤ_[p]) → toPS p (Σ i, c i • (1+X)^i) = Σ i, (1+X)^i * φ(c i)`
- What: Bridges the `φ`-linear combination `Σ c i • (1+X)^i` (module language) with the digit expression `Σ (1+X)^i · φ(c i)` (predicate language).
- How: `map_sum` then per-term `PhiAlg.smul_def` + `mul_comm`.
- Hypotheses: none.
- Uses from project: `PhiAlg.toPS`, `phiSeries`, `PhiAlg.smul_def`, `PhiAlg.toPS_apply`
- Used by: `digitBasis`, `digitBasis_repr_eq`, `digitMatrix_col_isDigitDecomp`
- Visibility: public
- Lines: 235–241 (proof ~5 lines)
- Notes: none

### def digitBasis
- Type: `(p : ℕ) [Fact p.Prime] → Module.Basis (Fin p) (PowerSeries ℤ_[p]) (PhiAlg p)`
- What: The digit basis `1, (1+X), …, (1+X)^{p−1}` exhibiting `ℤ_p⟦T⟧` as a free rank-`p` module over `A = φ(ℤ_p⟦T⟧)`.
- How: `Module.Basis.mk`; linear independence from uniqueness half of `existsUnique_digits_padicInt` (via `Fintype.linearIndependent_iffₛ` + `sum_smul_one_add_X_pow_eq` recognizing both sides as digit decomps); spanning from the existence half (via `Submodule.top_le_span_range_iff_forall_exists_fun` + `toPS.injective`).
- Hypotheses: none beyond `p` prime.
- Uses from project: `PhiAlg`, `IsDigitDecomp`, `sum_smul_one_add_X_pow_eq`, `PhiAlg.toPS`, `existsUnique_digits_padicInt`
- Used by: `digitBasis_apply`, Free/Finite instances, `digitMatrix`, `trace_digitBasis`, `digitBasis_repr_eq`, `trace_digitMatrix`, `digitMatrix_col_isDigitDecomp`
- Visibility: public
- Lines: 250–268 (def body ~18 lines)
- Notes: none

### theorem digitBasis_apply
- Type: `(i : Fin p) → digitBasis p i = ((1+X)^i : PhiAlg p)`
- What: The `i`-th basis vector is `(1+X)^i`.
- How: `Module.Basis.mk_apply`.
- Hypotheses: none.
- Uses from project: `digitBasis`, `PhiAlg`
- Used by: `trace_digitBasis`, `digitBasis_repr_eq`, `digitMatrix_col_isDigitDecomp`
- Visibility: public (`@[simp]`)
- Lines: 270–273
- Notes: none

### instance Module.Free (anonymous)
- Type: `Module.Free (PowerSeries ℤ_[p]) (PhiAlg p)`
- What: `PhiAlg p` is a free `A`-module.
- How: `Module.Free.of_basis (digitBasis p)`.
- Hypotheses: none.
- Uses from project: `digitBasis`, `PhiAlg`
- Used by: implicitly by `Algebra.norm` / `Algebra.trace` machinery
- Visibility: public (instance)
- Lines: 276–277
- Notes: none

### instance Module.Finite (anonymous)
- Type: `Module.Finite (PowerSeries ℤ_[p]) (PhiAlg p)`
- What: `PhiAlg p` is module-finite (rank `p`) over `A`.
- How: `Module.Finite.of_basis (digitBasis p)`.
- Hypotheses: none.
- Uses from project: `digitBasis`, `PhiAlg`
- Used by: implicitly by `Algebra.norm` / `Algebra.trace`
- Visibility: public (instance)
- Lines: 280–281
- Notes: none

### def normOp
- Type: `{p} → (f : PowerSeries ℤ_[p]) → PowerSeries ℤ_[p]`
- What: The norm operator `𝒩 = N_{B/A}`, the relative norm of the free rank-`p` φ-algebra `B = ℤ_p⟦T⟧` over `A = φ(ℤ_p⟦T⟧)`.
- How: `Algebra.norm (PowerSeries ℤ_[p]) ((toPS p).symm f)`.
- Hypotheses: none.
- Uses from project: `PhiAlg.toPS`
- Used by: `normOp_mul`, `normOp_one`, `normOp_isUnit`, `normOp_eq_det`, `normOpHom`, `normOp_modEq_one`, `normOp_modEq_self`, plus all iterate lemmas
- Visibility: public
- Lines: 295–296 (def body 1 line)
- Notes: none

### theorem normOp_mul
- Type: `(f g) → normOp (f * g) = normOp f * normOp g`
- What: `𝒩` is multiplicative.
- How: `simp [normOp, map_mul]` (the relative norm is a monoid hom).
- Hypotheses: none.
- Uses from project: `normOp`
- Used by: `normOpHom`, `normOp_iterate_mul`
- Visibility: public
- Lines: 299–301 (proof 1 line)
- Notes: none

### theorem normOp_one
- Type: `normOp (1 : PowerSeries ℤ_[p]) = 1`
- What: `𝒩 1 = 1`.
- How: `map_one` twice.
- Hypotheses: none.
- Uses from project: `normOp`
- Used by: `normOpHom`, `normOp_iterate_modEq` (`Function.iterate_fixed`)
- Visibility: public (`@[simp]`)
- Lines: 304–306 (proof ~1 line)
- Notes: none

### theorem normOp_isUnit
- Type: `{f} (hf : IsUnit f) → IsUnit (normOp f)`
- What: `𝒩` sends units to units.
- How: Push `IsUnit` through `(toPS).symm` then through `Algebra.norm` (both monoid homs).
- Hypotheses: `f` a unit.
- Uses from project: `PhiAlg.toPS`
- Used by: `normOp_iterate_isUnit`
- Visibility: public
- Lines: 309–310 (proof 1 line)
- Notes: none

### def digitMatrix
- Type: `{p} → (f : PowerSeries ℤ_[p]) → Matrix (Fin p) (Fin p) (PowerSeries ℤ_[p])`
- What: The matrix of multiplication-by-`f` in the digit basis (entries in `A ≅ ℤ_p⟦T⟧`); its determinant is `𝒩 f`.
- How: `Algebra.leftMulMatrix (digitBasis p) ((toPS p).symm f)`.
- Hypotheses: none.
- Uses from project: `digitBasis`, `PhiAlg.toPS`
- Used by: `normOp_eq_det`, `digitMatrix_add/mul/one/C/pow`, `trace_digitMatrix`, `digitMatrix_col_isDigitDecomp`, `digitMatrix_one_add_C_mul`, `normOp_modEq_one`, `digitMatrix_pow_p_modEq_diagonal`, `normOp_modEq_self`
- Visibility: public
- Lines: 316–318 (def body 1 line)
- Notes: none

### theorem normOp_eq_det
- Type: `(f) → normOp f = Matrix.det (digitMatrix f)`
- What: The determinant characterisation: `𝒩 f` is the determinant of the multiplication matrix in the digit basis (replan R10.4 — the `μ_p`-product form is not a formal identity).
- How: `Algebra.norm_eq_matrix_det (digitBasis p)`.
- Hypotheses: none.
- Uses from project: `normOp`, `digitMatrix`, `digitBasis`
- Used by: `normOp_modEq_one`, `normOp_modEq_self`
- Visibility: public
- Lines: 325–328 (proof ~2 lines)
- Notes: none

### def ModEqPow
- Type: `(p : ℕ) [Fact p.Prime] → (k : ℕ) → (f g : PowerSeries ℤ_[p]) → Prop`
- What: `f ≡ g mod p^k` for power series — every coefficient of `f − g` is divisible by `p^k`.
- How: `∀ m, (p : ℤ_[p])^k ∣ coeff m (f - g)`.
- Hypotheses: none.
- Uses from project: []
- Used by: `ModEqPow.refl/symm/trans/.mul_right/.mul/.pow/.of_le`, `modEqPow_iff_exists_C_mul`, `phi_injective_mod`, `normOp_modEq_one/self`, `modEqPow_one_iff_map_toZMod`, `pow_p_modEq_phiSeries`, `digit_modEq_of_sum_modEq`, `digitMatrix_pow_p_modEq_diagonal`, all iterate `modEq` lemmas
- Visibility: public
- Lines: 343–344
- Notes: none

### theorem ModEqPow.refl
- Type: `(k) (f) → ModEqPow p k f f`
- What: Reflexivity of `≡ mod p^k`.
- How: `sub_self`, `map_zero`, `dvd_zero`.
- Hypotheses: none.
- Uses from project: `ModEqPow`
- Used by: `ModEqPow.pow`, `normOp_iterate_modEq_self`
- Visibility: public (`@[refl]`)
- Lines: 348–350 (proof ~1 line)
- Notes: none

### theorem ModEqPow.symm
- Type: `{k} {f g} (h : ModEqPow p k f g) → ModEqPow p k g f`
- What: Symmetry of `≡ mod p^k`.
- How: `g - f = -(f - g)` via `neg_sub`, then `dvd.neg_right`.
- Hypotheses: `h`.
- Uses from project: `ModEqPow`
- Used by: unused in file
- Visibility: public
- Lines: 352–354 (proof ~2 lines)
- Notes: none

### theorem ModEqPow.trans
- Type: `{k} {f g h} (hfg) (hgh) → ModEqPow p k f h`
- What: Transitivity of `≡ mod p^k`.
- How: `f - h = (f-g)+(g-h)`, then `dvd_add`.
- Hypotheses: `hfg`, `hgh`.
- Uses from project: `ModEqPow`
- Used by: `ModEqPow.mul`, `normOp_iterate_modEq_self`
- Visibility: public
- Lines: 356–359 (proof ~3 lines)
- Notes: none

### theorem modEqPow_iff_exists_C_mul
- Type: `{k} {f g} → ModEqPow p k f g ↔ ∃ h, f - g = C ((p:ℤ_[p])^k) * h`
- What: The `C`-factor form of the congruence: `f ≡ g mod p^k` iff `f − g = C(p^k)·h`.
- How: Forward: `choose` the per-coefficient quotient and assemble via `PowerSeries.mk` (`coeff_C_mul`, `coeff_mk`). Backward: `coeff_C_mul` + `Dvd.intro`.
- Hypotheses: none.
- Uses from project: `ModEqPow`
- Used by: `ModEqPow.mul_right`, `phi_injective_mod`, `normOp_modEq_one`, `digit_modEq_of_sum_modEq`
- Visibility: public
- Lines: 364–374 (proof ~10 lines)
- Notes: none

### theorem ModEqPow.mul_right
- Type: `{k} {f g} (h) (c) → ModEqPow p k (f * c) (g * c)`
- What: Right-multiplication by a common factor preserves `≡ mod p^k`.
- How: Use `modEqPow_iff_exists_C_mul`: from `f−g = C(p^k)·q` get `(f-g)·c = C(p^k)·(q·c)` via `sub_mul` and `mul_assoc`.
- Hypotheses: `h`.
- Uses from project: `ModEqPow`, `modEqPow_iff_exists_C_mul`
- Used by: `ModEqPow.mul`, `digitMatrix_pow_p_modEq_diagonal`, `normOp_iterate_modEq`
- Visibility: public
- Lines: 378–381 (proof ~2 lines)
- Notes: none

### theorem ModEqPow.mul
- Type: `{k} {f₁ g₁ f₂ g₂} (h₁) (h₂) → ModEqPow p k (f₁*f₂) (g₁*g₂)`
- What: Two-sided multiplicative compatibility.
- How: Chain `(h₁.mul_right f₂).trans (h₂.mul_right g₁)` after rewriting with `mul_comm`.
- Hypotheses: `h₁`, `h₂`.
- Uses from project: `ModEqPow`, `ModEqPow.mul_right`, `ModEqPow.trans`
- Used by: `ModEqPow.pow`, `normOp_iterate_isUnit` (via `.mul` on `IsUnit`? no — uses `IsUnit.mul`); used by `normOp_iterate_modEq`? No. Used by `ModEqPow.pow`.
- Visibility: public
- Lines: 384–389 (proof ~3 lines)
- Notes: none

### theorem ModEqPow.pow
- Type: `{k} {f g} (h) → ∀ n, ModEqPow p k (f^n) (g^n)`
- What: Powers respect `≡ mod p^k`.
- How: Induction on `n`; base `n=0` via `ModEqPow.refl`, step via `pow_succ` + `ModEqPow.mul`.
- Hypotheses: `h`.
- Uses from project: `ModEqPow`, `ModEqPow.refl`, `ModEqPow.mul`
- Used by: unused in file
- Visibility: public
- Lines: 392–395 (proof ~3 lines)
- Notes: none

### theorem phiSeries_sub
- Type: `(f g) → phiSeries p (f - g) = phiSeries p f - phiSeries p g`
- What: `φ` respects subtraction (it is the ring hom `phiHom`).
- How: Rewrite all `phiSeries` as `phiHom`, then `map_sub`.
- Hypotheses: none.
- Uses from project: `phiHom_apply`, `phiSeries`
- Used by: `phi_injective_mod`
- Visibility: public
- Lines: 407–409 (proof ~2 lines)
- Notes: none

### theorem phiSeries_one_padicInt
- Type: `phiSeries p (1 : PowerSeries ℤ_[p]) = 1`
- What: `φ(1) = 1`.
- How: `phiHom_apply` then `map_one`.
- Hypotheses: none.
- Uses from project: `phiHom_apply`, `phiSeries`
- Used by: `phi_injective_mod`
- Visibility: public
- Lines: 411–412 (proof ~1 line)
- Notes: none

### theorem phi_injective_mod
- Type: `{k} {f} (h : ModEqPow p k (phiSeries p f) 1) → ModEqPow p k f 1`
- What: T908 (i): `φ` is injective mod `p^k` — `φ(f) ≡ 1` implies `f ≡ 1`.
- How: Write `φ(f−1) = φf − 1 = C(p^k)·q` (`phiSeries_sub`, `phiSeries_one_padicInt`); apply `ψ` and use `psiSeries_phi_padicInt` (cancels `φ`) and `psiSeries_C_mul_padicInt` (carries `C(p^k)` through), giving `f − 1 = C(p^k)·ψ(q)`.
- Hypotheses: `h : φ(f) ≡ 1 mod p^k`.
- Uses from project: `ModEqPow`, `phiSeries`, `modEqPow_iff_exists_C_mul`, `phiSeries_sub`, `phiSeries_one_padicInt`, `psiSeries`, `psiSeries_phi_padicInt`, `psiSeries_C_mul_padicInt`
- Used by: unused in file
- Visibility: public
- Lines: 418–426 (proof ~8 lines)
- Notes: none

### theorem digitMatrix_add
- Type: `(f g) → digitMatrix (f + g) = digitMatrix f + digitMatrix g`
- What: `digitMatrix` is additive.
- How: `simp [digitMatrix, map_add]`.
- Hypotheses: none.
- Uses from project: `digitMatrix`
- Used by: `digitMatrix_one_add_C_mul`
- Visibility: public
- Lines: 439–441 (proof 1 line)
- Notes: none

### theorem digitMatrix_mul
- Type: `(f g) → digitMatrix (f * g) = digitMatrix f * digitMatrix g`
- What: `digitMatrix` is multiplicative.
- How: `simp [digitMatrix, map_mul]`.
- Hypotheses: none.
- Uses from project: `digitMatrix`
- Used by: `digitMatrix_pow`, `digitMatrix_one_add_C_mul`
- Visibility: public
- Lines: 444–446 (proof 1 line)
- Notes: none

### theorem digitMatrix_one
- Type: `digitMatrix (1 : PowerSeries ℤ_[p]) = 1`
- What: `digitMatrix 1 = 1`.
- How: `map_one` twice.
- Hypotheses: none.
- Uses from project: `digitMatrix`
- Used by: `digitMatrix_pow`, `digitMatrix_one_add_C_mul`
- Visibility: public (`@[simp]`)
- Lines: 449–451 (proof 1 line)
- Notes: none

### theorem digitMatrix_C
- Type: `(a : ℤ_[p]) → digitMatrix (C a) = C a • (1 : Matrix (Fin p) (Fin p) (PowerSeries ℤ_[p]))`
- What: `digitMatrix (C a)` is the scalar matrix `C a • 1` (since `φ` fixes constants).
- How: Show `(toPS).symm (C a) = algebraMap (C a)` using `toPS_algebraMap` + `PowerSeries.subst_C`; then `AlgHom.commutes` and `Algebra.algebraMap_eq_smul_one`.
- Hypotheses: none.
- Uses from project: `digitMatrix`, `PhiAlg.toPS`, `PhiAlg` Algebra instance, `PhiAlg.toPS_algebraMap`, `phiSeries`
- Used by: `digitMatrix_one_add_C_mul`
- Visibility: public
- Lines: 456–466 (proof ~10 lines)
- Notes: none

### theorem phiSeries_one_add_X_pow
- Type: `(q : ℕ) → phiSeries p ((1+X)^q) = ((1+X)^p)^q`
- What: `φ((1+X)^q) = ((1+X)^p)^q` (since `φ(1+X) = (1+X)^p`).
- How: Compute `phiHom (1+X) = 1 + ((1+X)^p − 1) = (1+X)^p` using `subst_X`, then `map_pow`.
- Hypotheses: none.
- Uses from project: `phiSeries`, `phiHom_apply`, `phiHom`, `hasSubst_one_add_X_pow_sub_one`
- Used by: `isDigitDecomp_one_add_X_pow`
- Visibility: public
- Lines: 469–477 (proof ~8 lines)
- Notes: none

### theorem isDigitDecomp_one_add_X_pow
- Type: `(m : ℕ) → IsDigitDecomp p ((1+X)^m) (fun i => if i = m%p then (1+X)^(m/p) else 0)`
- What: The digit decomposition of `(1+X)^m`: writing `m = p·(m/p)+m%p`, the digit family has `(1+X)^{m/p}` in slot `m%p` and `0` elsewhere.
- How: `Finset.sum_eq_single ⟨m%p, …⟩`; the surviving term uses `phiSeries_one_add_X_pow` and `pow_mul`/`pow_add` with `Nat.mod_add_div`; off-diagonal terms killed by `phiSeries_zero`.
- Hypotheses: `p` prime (for `Nat.mod_lt`).
- Uses from project: `IsDigitDecomp`, `phiSeries_one_add_X_pow`, `phiSeries_zero`
- Used by: `trace_digitBasis`
- Visibility: public
- Lines: 482–493 (proof ~11 lines)
- Notes: none

### theorem digitBasis_repr_eq
- Type: `(x : PhiAlg p) (G) (hG : IsDigitDecomp p (toPS p x) G) (i) → (digitBasis p).repr x i = G i`
- What: The basis `repr` coordinates of `x` are exactly the digit family of `toPS x`.
- How: Show the repr coordinates themselves form a digit decomposition (via `Basis.sum_repr` + `sum_smul_one_add_X_pow_eq` + `digitBasis_apply`), then apply uniqueness from `existsUnique_digits_padicInt`.
- Hypotheses: `hG` a digit decomposition.
- Uses from project: `PhiAlg`, `IsDigitDecomp`, `PhiAlg.toPS`, `digitBasis`, `sum_smul_one_add_X_pow_eq`, `digitBasis_apply`, `existsUnique_digits_padicInt`
- Used by: `trace_digitBasis`, `trace_digitMatrix`
- Visibility: public
- Lines: 497–505 (proof ~8 lines)
- Notes: none

### theorem trace_digitBasis
- Type: `(l : Fin p) → Algebra.trace (PowerSeries ℤ_[p]) (PhiAlg p) (digitBasis p l) = if (l:ℕ)=0 then (p:PowerSeries ℤ_[p]) else 0`
- What: The algebra trace of basis element `(1+X)^l` is `p` if `l = 0` else `0` (diagonal of `leftMulMatrix` vanishes off `l ≡ 0 mod p`).
- How: `Algebra.trace_eq_matrix_trace` + `Matrix.trace`; compute each diagonal entry as the `j`-th digit of `(1+X)^{l+j}` via `digitBasis_repr_eq` + `isDigitDecomp_one_add_X_pow`, then a Nat-arithmetic case split (`omega`, divisibility) shows it is `1` iff `l=0`; finally `Finset.sum_const` gives `p` or `0`.
- Hypotheses: `p` prime.
- Uses from project: `PhiAlg`, `digitBasis`, `digitBasis_apply`, `digitBasis_repr_eq`, `isDigitDecomp_one_add_X_pow`
- Used by: `trace_digitMatrix`
- Visibility: public
- Lines: 511–548 (proof ~37 lines)
- Notes: long(30-50) — proof ~37 lines; uses `omega` / `Nat.div_add_mod`.

### theorem trace_digitMatrix
- Type: `(h : PowerSeries ℤ_[p]) → Matrix.trace (digitMatrix h) = (p:PowerSeries ℤ_[p]) * psiSeries p h`
- What: The trace identity (RJW TeX 2670, abstract-base form `trace = p·ψ`): `trace (digitMatrix h) = p · ψ(h)`.
- How: Convert to `Algebra.trace`; expand `(toPS).symm h` in `digitBasis` (`Basis.sum_repr` + `map_sum`), apply linearity + `trace_digitBasis` so only `l=0` survives; identify `repr_0 = ψ h` via `digitBasis_repr_eq` and `psiSeries_eq_of_isDigitDecomp_padicInt`.
- Hypotheses: none.
- Uses from project: `digitMatrix`, `digitBasis`, `PhiAlg.toPS`, `trace_digitBasis`, `psiSeries`, `existsUnique_digits_padicInt`, `psiSeries_eq_of_isDigitDecomp_padicInt`, `digitBasis_repr_eq`
- Used by: `normOp_modEq_one`
- Visibility: public
- Lines: 554–571 (proof ~17 lines)
- Notes: none

### theorem modEqPow_one_iff_map_toZMod
- Type: `{f g} → ModEqPow p 1 f g ↔ map toZMod f = map toZMod g`
- What: `f ≡ g mod p` iff their reductions over `ZMod p` (via `PadicInt.toZMod`) agree.
- How: `PowerSeries.ext_iff` + `forall_congr'`; per-coefficient, `p ∣ x ↔ toZMod x = 0` via `RingHom.mem_ker`, `PadicInt.ker_toZMod`, `maximalIdeal_eq_span_p`, `Ideal.mem_span_singleton`.
- Hypotheses: none.
- Uses from project: `ModEqPow`
- Used by: `pow_p_modEq_phiSeries`, `digitMatrix_pow_p_modEq_diagonal`, `normOp_modEq_self`
- Visibility: public
- Lines: 577–585 (proof ~5 lines)
- Notes: none

### theorem phiSeries_eq_pow_zmod
- Type: `(g : PowerSeries (ZMod p)) → phiSeries p g = g ^ p`
- What: The Frobenius identity over `𝔽_p⟦T⟧`: `φ(ḡ) = ḡ^p` (engine for part (ii)).
- How: Over char `p`, `(1+X)^p − 1 = X^p` (`add_pow_char`, freshman's dream), so `φ = subst(X^p) = expand`; then `expand g = g^p` via `MvPowerSeries.map_frobenius_expand` and `ZMod.frobenius_zmod` + `PowerSeries.map_id`.
- Hypotheses: `p` prime (CharP instance).
- Uses from project: `phiSeries`
- Used by: `pow_p_modEq_phiSeries`
- Visibility: public
- Lines: 591–605 (proof ~14 lines)
- Notes: none

### theorem map_toZMod_phiSeries
- Type: `(f) → map toZMod (phiSeries p f) = phiSeries p (map toZMod f)`
- What: `map toZMod` commutes with `φ`.
- How: Direct from `map_phiSeries` (the coefficient-map naturality of `subst`).
- Hypotheses: none.
- Uses from project: `phiSeries`, `map_phiSeries`
- Used by: `pow_p_modEq_phiSeries`
- Visibility: public
- Lines: 609–612 (proof 1 line)
- Notes: none

### theorem pow_p_modEq_phiSeries
- Type: `(f) → ModEqPow p 1 (f^p) (phiSeries p f)`
- What: Frobenius identity over `ℤ_[p]` (reduced form): `f^p ≡ φ(f) mod p`.
- How: Reduce mod `p` via `modEqPow_one_iff_map_toZMod`, then `map_pow`, `map_toZMod_phiSeries`, `phiSeries_eq_pow_zmod`.
- Hypotheses: none.
- Uses from project: `ModEqPow`, `phiSeries`, `modEqPow_one_iff_map_toZMod`, `map_toZMod_phiSeries`, `phiSeries_eq_pow_zmod`
- Used by: `digitMatrix_pow_p_modEq_diagonal`
- Visibility: public
- Lines: 616–618 (proof 1 line)
- Notes: none

### theorem isDigitDecomp_C_mul
- Type: `(a : ℤ_[p]) {F} {G} (hG : IsDigitDecomp p F G) → IsDigitDecomp p (C a * F) (fun i => C a * G i)`
- What: The digit family of `C a · F` is `a ·` the digit family of `F`.
- How: Unfold `IsDigitDecomp`, distribute `C a` over the sum (`Finset.mul_sum`), per-term use `phiSeries_C_mul` + `ring`.
- Hypotheses: `hG`.
- Uses from project: `IsDigitDecomp`, `phiSeries`, `phiSeries_C_mul`
- Used by: `digit_modEq_of_sum_modEq`
- Visibility: public
- Lines: 622–627 (proof ~5 lines)
- Notes: none

### theorem digit_modEq_of_sum_modEq
- Type: `{k} {c d : Fin p → PowerSeries ℤ_[p]} (h : ModEqPow p k (Σ (1+X)^i φ(c i)) (Σ (1+X)^i φ(d i))) (i) → ModEqPow p k (c i) (d i)`
- What: Digit uniqueness mod `p^k`: if the two digit sums are congruent mod `p^k` then the digits are congruent component-wise.
- How: Write difference `= C(p^k)·R`, take digit decomp `GR` of `R`; show `c` and `i ↦ d i + C(p^k)·GR i` are both digit decomps of the same series (using `isDigitDecomp_C_mul`, `phiHom`/`map_add`), apply `ℤ_[p]`-digit uniqueness, then `c i − d i = C(p^k)·GR i`.
- Hypotheses: `h`.
- Uses from project: `ModEqPow`, `phiSeries`, `modEqPow_iff_exists_C_mul`, `existsUnique_digits_padicInt`, `IsDigitDecomp`, `isDigitDecomp_C_mul`, `phiHom_apply`, `phiHom`
- Used by: `digitMatrix_pow_p_modEq_diagonal`
- Visibility: public
- Lines: 632–659 (proof ~27 lines)
- Notes: none

### theorem digitMatrix_pow
- Type: `(f) (n : ℕ) → digitMatrix (f^n) = (digitMatrix f)^n`
- What: `digitMatrix` respects powers.
- How: Induction on `n`; base via `digitMatrix_one`, step via `pow_succ` + `digitMatrix_mul`.
- Hypotheses: none.
- Uses from project: `digitMatrix`, `digitMatrix_one`, `digitMatrix_mul`
- Used by: `normOp_modEq_self`
- Visibility: public
- Lines: 662–666 (proof ~4 lines)
- Notes: none

### theorem digitMatrix_col_isDigitDecomp
- Type: `(f) (j : Fin p) → f * (1+X)^j = Σ i, (1+X)^i * φ((digitMatrix f) i j)`
- What: The `j`-th column of `digitMatrix f` is the digit family of `f·(1+X)^j`.
- How: Expand `(toPS).symm f * digitBasis j` via `Basis.sum_repr` + `leftMulMatrix_eq_repr_mul` + `digitBasis_apply`, apply `toPS` and `sum_smul_one_add_X_pow_eq`.
- Hypotheses: none.
- Uses from project: `digitMatrix`, `phiSeries`, `PhiAlg.toPS`, `digitBasis`, `digitBasis_apply`, `PhiAlg.toPS_apply`, `sum_smul_one_add_X_pow_eq`
- Used by: `digitMatrix_pow_p_modEq_diagonal`
- Visibility: public
- Lines: 671–681 (proof ~10 lines)
- Notes: none

### theorem digitMatrix_one_add_C_mul
- Type: `(a : ℤ_[p]) (h) → digitMatrix (1 + C a * h) = 1 + C a • digitMatrix h`
- What: `digitMatrix (1 + C a · h) = 1 + C a • digitMatrix h`.
- How: `digitMatrix_add`, `digitMatrix_one`, `digitMatrix_mul`, `digitMatrix_C`, `smul_mul_assoc`.
- Hypotheses: none.
- Uses from project: `digitMatrix`, `digitMatrix_add`, `digitMatrix_one`, `digitMatrix_mul`, `digitMatrix_C`
- Used by: `normOp_modEq_one`
- Visibility: public
- Lines: 685–689 (proof ~2 lines)
- Notes: none

### theorem normOp_modEq_one
- Type: `{k} (hk : 1 ≤ k) {f} (_hf : IsUnit f) (h : ModEqPow p k f 1) → ModEqPow p (k+1) (normOp f) 1`
- What: T908 (iii): for a unit `f ≡ 1 mod p^k` (`k ≥ 1`), `𝒩 f ≡ 1 mod p^{k+1}`.
- How: Write `f = 1 + C(p^k)·g`; via `normOp_eq_det` + `digitMatrix_one_add_C_mul` + `Matrix.det_one_add_smul`, get the Taylor expansion `𝒩 f = 1 + trace(digitMatrix g)·C(p^k) + Rev·C(p^k)²`; linear term is `C(p)·ψ(g)·C(p^k)` (`trace_digitMatrix`, `map_natCast`), factor `p^k = p^{k-1}·p` (omega), assemble the `C(p^{k+1})` witness and close by `ring`.
- Hypotheses: `1 ≤ k`; `f` a unit (unused — recorded to match source); `h : f ≡ 1 mod p^k`.
- Uses from project: `ModEqPow`, `normOp`, `modEqPow_iff_exists_C_mul`, `digitMatrix`, `normOp_eq_det`, `digitMatrix_one_add_C_mul`, `trace_digitMatrix`, `psiSeries`
- Used by: `normOp_iterate_modEq_one`
- Visibility: public
- Lines: 699–725 (proof ~24 lines)
- Notes: `_hf` unit hypothesis unused (deliberately, per docstring); uses `omega`.

### theorem digitMatrix_pow_p_modEq_diagonal
- Type: `(f) (i j : Fin p) → ModEqPow p 1 ((digitMatrix (f^p)) i j) (if i = j then f else 0)`
- What: `digitMatrix (f^p) ≡ diagonal f mod p` entrywise (key to part (ii)).
- How: Apply `digit_modEq_of_sum_modEq` with `c = column j of digitMatrix(f^p)`, `d = δ_{·j}·f`; the LHS sum is `f^p·(1+X)^j` (`digitMatrix_col_isDigitDecomp`), the RHS collapses (`Finset.sum_eq_single j`) to `φ(f)·(1+X)^j`, and `f^p ≡ φ(f) mod p` (`pow_p_modEq_phiSeries`) via `.mul_right`.
- Hypotheses: none.
- Uses from project: `ModEqPow`, `digitMatrix`, `digit_modEq_of_sum_modEq`, `digitMatrix_col_isDigitDecomp`, `phiSeries`, `phiSeries_zero`, `pow_p_modEq_phiSeries`, `ModEqPow.mul_right`
- Used by: `normOp_modEq_self`
- Visibility: public
- Lines: 732–742 (proof ~10 lines)
- Notes: none

### theorem normOp_modEq_self
- Type: `(f) → ModEqPow p 1 (normOp f) f`
- What: T908 (ii): `𝒩 f ≡ f mod p`.
- How: Reduce `𝒩 f = det(digitMatrix f)` mod `p` to `det M̄` (`RingHom.map_det`); show `M̄^p = diagonal(map ρ f)` from `digitMatrix_pow_p_modEq_diagonal` (+ `digitMatrix_pow`); then `(det M̄)^p = f̄^p` (`Matrix.det_pow`, `det_diagonal`), and Frobenius injectivity on `𝔽_p⟦T⟧` (`frobenius_inj`, CharP instance) gives `det M̄ = f̄`.
- Hypotheses: none.
- Uses from project: `ModEqPow`, `normOp`, `digitMatrix`, `normOp_eq_det`, `digitMatrix_pow`, `digitMatrix_pow_p_modEq_diagonal`, `modEqPow_one_iff_map_toZMod`
- Used by: `normOp_iterate_modEq_self`
- Visibility: public
- Lines: 755–782 (proof ~27 lines)
- Notes: `set_option synthInstance.maxHeartbeats 400000 in` (lines 744–746) precedes this decl; uses `charP_of_injective_algebraMap'`, `frobenius_inj`.

### theorem ModEqPow.of_le
- Type: `{a b} (hab : b ≤ a) {f g} (h : ModEqPow p a f g) → ModEqPow p b f g`
- What: `≡ mod p^a` downgrades to `≡ mod p^b` for `b ≤ a`.
- How: `dvd_trans (pow_dvd_pow _ hab) (h m)`.
- Hypotheses: `b ≤ a`, `h`.
- Uses from project: `ModEqPow`
- Used by: unused in file
- Visibility: public
- Lines: 787–789 (proof ~2 lines)
- Notes: none

### def normOpHom
- Type: `{p} → PowerSeries ℤ_[p] →* PowerSeries ℤ_[p]`
- What: `𝒩` bundled as a monoid homomorphism.
- How: Structure literal with `toFun := normOp`, `map_one' := normOp_one`, `map_mul' := normOp_mul`.
- Hypotheses: none.
- Uses from project: `normOp`, `normOp_one`, `normOp_mul`
- Used by: `normOpHom_apply`
- Visibility: public
- Lines: 792–795
- Notes: none

### theorem normOpHom_apply
- Type: `(f) → normOpHom f = normOp f`
- What: `normOpHom` evaluates to `normOp`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: `normOpHom`, `normOp`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 797–798
- Notes: none

### theorem normOp_iterate_mul
- Type: `(n) (f g) → normOp^[n] (f * g) = normOp^[n] f * normOp^[n] g`
- What: The `n`-fold iterate `𝒩^{[n]}` is multiplicative.
- How: Induction on `n`; step uses `Function.iterate_succ_apply` and `normOp_mul`.
- Hypotheses: none.
- Uses from project: `normOp`, `normOp_mul`
- Used by: `normOp_iterate_modEq`
- Visibility: public
- Lines: 801–807 (proof ~6 lines)
- Notes: none

### theorem normOp_iterate_isUnit
- Type: `{f} (hf : IsUnit f) (n) → IsUnit (normOp^[n] f)`
- What: `𝒩^{[n]}` preserves units.
- How: Induction on `n`; step via `Function.iterate_succ_apply'` + `normOp_isUnit`.
- Hypotheses: `f` a unit.
- Uses from project: `normOp`, `normOp_isUnit`
- Used by: `normOp_iterate_modEq_one`, `normOp_iterate_modEq`
- Visibility: public
- Lines: 810–814 (proof ~4 lines)
- Notes: none

### theorem normOp_iterate_modEq_self
- Type: `(f) (n) → ModEqPow p 1 (normOp^[n] f) f`
- What: `𝒩^{[n]} f ≡ f mod p`.
- How: Induction on `n`; step chains `normOp_modEq_self (normOp^[m] f)` with the inductive hypothesis via `ModEqPow.trans`.
- Hypotheses: none.
- Uses from project: `ModEqPow`, `normOp`, `ModEqPow.refl`, `normOp_modEq_self`, `ModEqPow.trans`
- Used by: `normOp_iterate_modEq`
- Visibility: public
- Lines: 817–823 (proof ~6 lines)
- Notes: none

### theorem normOp_iterate_modEq_one
- Type: `{g} (hg : IsUnit g) (h : ModEqPow p 1 g 1) (n) → ModEqPow p (n+1) (normOp^[n] g) 1`
- What: Iterating part (iii): a unit `g ≡ 1 mod p` gives `𝒩^{[n]} g ≡ 1 mod p^{n+1}`.
- How: Induction on `n`; step via `Function.iterate_succ_apply'` + `normOp_modEq_one` (with `normOp_iterate_isUnit`).
- Hypotheses: `g` a unit; `g ≡ 1 mod p`.
- Uses from project: `ModEqPow`, `normOp`, `normOp_modEq_one`, `normOp_iterate_isUnit`
- Used by: `normOp_iterate_modEq`
- Visibility: public
- Lines: 827–834 (proof ~7 lines)
- Notes: none

### theorem normOp_iterate_modEq
- Type: `{k₁ k₂} (h : k₁ ≤ k₂) {f} (hf : IsUnit f) → ModEqPow p (k₁+1) (normOp^[k₂] f) (normOp^[k₁] f)`
- What: T908 (iv): for a unit `f` and `k₁ ≤ k₂`, `𝒩^{[k₂]} f ≡ 𝒩^{[k₁]} f mod p^{k₁+1}`.
- How: Set `g := 𝒩^{[k₂−k₁]} f · f⁻¹`, a unit `≡ 1 mod p` (`normOp_iterate_modEq_self` + `.mul_right`); apply `normOp_iterate_modEq_one` `k₁` times; unfold `𝒩^{[k₁]} g = 𝒩^{[k₂]} f · 𝒩^{[k₁]} f⁻¹` (`normOp_iterate_mul`, `Function.iterate_add_apply`), multiply by `𝒩^{[k₁]} f` and cancel.
- Hypotheses: `k₁ ≤ k₂`; `f` a unit.
- Uses from project: `ModEqPow`, `normOp`, `normOp_iterate_isUnit`, `normOp_iterate_modEq_self`, `ModEqPow.mul_right`, `normOp_iterate_modEq_one`, `normOp_iterate_mul`, `normOp_one`
- Used by: unused in file
- Visibility: public
- Lines: 841–865 (proof ~24 lines)
- Notes: uses `omega`.

### instance instCompactSpace
- Type: `(p) → CompactSpace (PowerSeries ℤ_[p])`
- What: `ℤ_p⟦T⟧` is compact for the coefficientwise (Pi) topology.
- How: `inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → ℤ_[p]))` (Tychonoff; `ℤ_[p]` compact).
- Hypotheses: none.
- Uses from project: []
- Used by: implicitly by `instSeqCompactSpace`? No (independent); supports T910 externally
- Visibility: public (instance); within `section Compactness`, `open scoped PowerSeries.WithPiTopology`
- Lines: 884–885
- Notes: none

### instance instSeqCompactSpace
- Type: `(p) → SeqCompactSpace (PowerSeries ℤ_[p])`
- What: `ℤ_p⟦T⟧` is sequentially compact (countable product of metric spaces ⇒ metrizable + first-countable, with compactness).
- How: `inferInstanceAs (SeqCompactSpace ((Unit →₀ ℕ) → ℤ_[p]))`.
- Hypotheses: none.
- Uses from project: []
- Used by: `exists_subseq_tendsto`
- Visibility: public (instance)
- Lines: 890–891
- Notes: none

### theorem exists_subseq_tendsto
- Type: `(g : ℕ → PowerSeries ℤ_[p]) → ∃ f φ, StrictMono φ ∧ Tendsto (g ∘ φ) atTop (nhds f)`
- What: T909: every sequence in `ℤ_p⟦T⟧` has a coefficientwise-convergent subsequence (feeds T910's diagonal argument).
- How: `SeqCompactSpace.tendsto_subseq` applied via `instSeqCompactSpace`.
- Hypotheses: none.
- Uses from project: `instSeqCompactSpace`
- Used by: unused in file
- Visibility: public
- Lines: 897–900 (proof 1 line)
- Notes: none

### theorem tendsto_coeff
- Type: `{g} {f} (hg : Tendsto g atTop (nhds f)) (n) → Tendsto (fun m => coeff n (g m)) atTop (nhds (coeff n f))`
- What: T909: coefficientwise convergence `gₘ → f` gives `coeff n gₘ → coeff n f` (projection continuity).
- How: `(WithPiTopology.continuous_coeff ℤ_[p] n).tendsto f |>.comp hg`.
- Hypotheses: `hg` convergence.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 906–910 (proof 1 line)
- Notes: none

### theorem isClosed_isUnit
- Type: `IsClosed {f : PowerSeries ℤ_[p] | IsUnit f}`
- What: T909: the units of `ℤ_p⟦T⟧` form a closed subset (limits of units along convergent subsequences are units).
- How: Rewrite the unit set as the preimage `(f ↦ ‖constantCoeff f‖)⁻¹' {1}` (`PowerSeries.isUnit_iff_constantCoeff` + `PadicInt.isUnit_iff`), then `isClosed_singleton.preimage` of the continuous norm-of-constant-coeff map (`WithPiTopology.continuous_constantCoeff`).
- Hypotheses: none.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 918–927 (proof ~9 lines)
- Notes: none

---

## File Summary

- Total declarations: 55
  - defs: 7 (`padicIntEquivIntegerRing`, `phiHom`, `PhiAlg`, `PhiAlg.toPS`, `digitBasis`, `normOp`, `digitMatrix`, `ModEqPow`, `normOpHom` — note `ModEqPow` and `PhiAlg` are def-like; counting all `def`: `padicIntEquivIntegerRing`, `phiHom`, `PhiAlg`, `PhiAlg.toPS`, `digitBasis`, `normOp`, `digitMatrix`, `ModEqPow`, `normOpHom` = 9 defs)
  - lemmas/theorems: 40
  - instances: 6 (`PhiAlg` CommRing, `PhiAlg` Algebra, `Module.Free`, `Module.Finite`, `instCompactSpace`, `instSeqCompactSpace`)
  - (Recount: 9 defs + 40 theorems + 6 instances = 55.)

- Key API (used by ≥3 in-file):
  - `PhiAlg.toPS` — used by ~13 decls.
  - `digitMatrix` — used by ~11 decls.
  - `ModEqPow` — the relation underlying the entire T908 congruence layer (used by ~15+ decls).
  - `existsUnique_digits_padicInt` — used by 7 decls (the foundational digit uniqueness).
  - `digitBasis` — used by ~8 decls.
  - `normOp` — used by ~8 decls.
  - `psiSeries_eq_of_isDigitDecomp_padicInt` — used by 4 decls.
  - `modEqPow_iff_exists_C_mul` — used by 4 decls.
  - `ModEqPow.mul_right` — used by 3 decls.

- Unused in file (terminal/exported API — likely consumed by Theorem.lean / T907 / T910):
  `psiSeries_add_padicInt`, `phi_injective_mod`, `ModEqPow.symm`, `ModEqPow.pow`, `ModEqPow.of_le`, `normOp_iterate_modEq`, `normOpHom_apply`, `exists_subseq_tendsto`, `tendsto_coeff`, `isClosed_isUnit`, `PhiAlg.toPS_symm_apply`.

- Declarations with `sorry`: NONE.

- `set_option`: one — `set_option synthInstance.maxHeartbeats 400000 in` on `normOp_modEq_self` (lines 744–746); raised because the `RingHom.map_det`/`Matrix.map` chain over `PowerSeries (ZMod p)` matrices drives nested instance synthesis past the default budget.

- Proofs >50 lines (OVER-50, need /decompose-proof): NONE.

- Proofs 30–50 lines (long): 1
  - `trace_digitBasis` (lines 511–548, ~37 lines).

- Borderline 27-line proofs (near the long threshold, candidates to watch): `digit_modEq_of_sum_modEq` (~27), `normOp_modEq_self` (~27).
