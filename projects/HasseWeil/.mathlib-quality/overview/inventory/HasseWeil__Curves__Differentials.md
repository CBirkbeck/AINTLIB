# Inventory: ./HasseWeil/Curves/Differentials.lean

**File**: `HasseWeil/Curves/Differentials.lean`  
**Ticket**: T-II-4-001 (Differentials), T-II-4-004 (separability iff ω-coeff ≠ 0)  
**Reference**: Silverman, *The Arithmetic of Elliptic Curves*, II.4  
**Total lines**: 1218  
**No `sorry` in any proof body. No `set_option maxHeartbeats`.**

---

## Section 1: Differentials on a smooth plane curve (`HasseWeil.Curves`)

### `noncomputable abbrev Differentials`
- **Type**: `(C : SmoothPlaneCurve F) : Type _` = `Ω[C.FunctionField⁄F]`
- **What**: The space of (meromorphic) differentials on a smooth plane curve, defined as the module of Kähler differentials of the function field over the base field.
- **How**: Pure abbreviation; no proof.
- **Hypotheses**: `F` is a field.
- **Uses from project**: `SmoothPlaneCurve`, `C.FunctionField`
- **Used by**: `Differentials.d`, all `d_*` lemmas
- **Visibility**: public
- **Lines**: 35–36, 0 lines proof

---

### `noncomputable abbrev Differentials.d`
- **Type**: `{C : SmoothPlaneCurve F} → (f : C.FunctionField) → Differentials C` = `KaehlerDifferential.D F C.FunctionField f`
- **What**: The differential `df` of a function `f` on a smooth curve.
- **How**: Pure abbreviation.
- **Hypotheses**: None beyond `F` field.
- **Uses from project**: `Differentials`
- **Used by**: `d_add`, `d_mul`, `d_algebraMap`, `d_zero`, `d_one`, `d_neg`, `d_sub`, `d_pow`, `d_inv`, `d_zpow`, `d_smul`
- **Visibility**: public
- **Lines**: 40–43, 0 lines proof

---

### `theorem d_add` (simp)
- **Type**: `d (f + g) = d f + d g`
- **What**: Additivity of the differential map.
- **How**: `KaehlerDifferential.D.map_add`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 48–50, 1 line

---

### `theorem d_mul` (simp)
- **Type**: `d (f * g) = f • d g + g • d f`
- **What**: Leibniz rule for the differential.
- **How**: `KaehlerDifferential.D.leibniz`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 52–54, 1 line

---

### `theorem d_algebraMap` (simp)
- **Type**: `d (algebraMap F C.FunctionField a) = 0`
- **What**: The differential of a constant (scalar from `F`) vanishes.
- **How**: `KaehlerDifferential.D.map_algebraMap`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 56–58, 1 line

---

### `theorem d_zero` (simp)
- **Type**: `d (0 : C.FunctionField) = 0`
- **What**: The differential of zero vanishes.
- **How**: `KaehlerDifferential.D.map_zero`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 60–61, 1 line

---

### `theorem d_one` (simp)
- **Type**: `d (1 : C.FunctionField) = 0`
- **What**: The differential of the unit is zero.
- **How**: `KaehlerDifferential.D.map_one_eq_zero`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 63–64, 1 line

---

### `theorem d_neg` (simp)
- **Type**: `d (-f) = -d f`
- **What**: The differential negates with negation.
- **How**: `KaehlerDifferential.D.map_neg`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66–68, 1 line

---

### `theorem d_sub` (simp)
- **Type**: `d (f - g) = d f - d g`
- **What**: The differential is additive over subtraction.
- **How**: `KaehlerDifferential.D.map_sub`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 70–72, 1 line

---

### `theorem d_pow`
- **Type**: `d (f ^ n) = n • f ^ (n - 1) • d f`
- **What**: Power rule for the differential.
- **How**: `KaehlerDifferential.D.leibniz_pow`.
- **Hypotheses**: `n : ℕ`.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 74–76, 1 line

---

### `theorem d_inv`
- **Type**: `d f⁻¹ = -f⁻¹ ^ 2 • d f`
- **What**: Inverse rule for the differential.
- **How**: `KaehlerDifferential.D.leibniz_inv`.
- **Hypotheses**: None.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 78–80, 1 line

---

### `theorem d_zpow`
- **Type**: `d (f ^ n) = n • f ^ (n - 1) • d f` for `n : ℤ`
- **What**: Integer power rule for the differential.
- **How**: `KaehlerDifferential.D.leibniz_zpow`.
- **Hypotheses**: `n : ℤ`.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 82–84, 1 line

---

### `theorem d_smul` (simp)
- **Type**: `d (a • f) = a • d f`
- **What**: The differential is `F`-linear.
- **How**: `KaehlerDifferential.D.map_smul`.
- **Hypotheses**: `a : F`.
- **Uses from project**: `Differentials.d`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 86–88, 1 line

---

## Section 2: T-II-4-004 — Separability iff ω-pullback-coeff ≠ 0 (`HasseWeil`)

---

### `theorem omegaPullbackCoeff_ne_zero_of_pullbackKaehler_injective`
- **Type**: `(α : Isogeny W W) → Function.Injective α.pullbackKaehler → omegaPullbackCoeff W α ≠ 0`
- **What**: If the Kähler differential pullback is injective on `Ω[K(E)/F]`, then the omega-pullback coefficient is nonzero.
- **How**: Contrapositive: coeff = 0 forces `pullbackKaehler ω = 0` via `Isogeny.pullbackKaehler_invariantDifferential`, and injectivity then gives `ω = 0`, contradicting `invariantDifferential_ne_zero`.
- **Hypotheses**: Injectivity of the differential pullback map.
- **Uses from project**: `Isogeny.pullbackKaehler_invariantDifferential`, `invariantDifferential_ne_zero`, `omegaPullbackCoeff`
- **Used by**: `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`
- **Visibility**: public
- **Lines**: 141–152, 10 lines

---

### `theorem pullbackKaehler_injective_of_omegaPullbackCoeff_ne_zero`
- **Type**: `(α : Isogeny W W) → omegaPullbackCoeff W α ≠ 0 → Function.Injective α.pullbackKaehler`
- **What**: If the omega-pullback coefficient is nonzero, then the differential pullback on `Ω[K(E)/F]` is injective.
- **How**: Uses 1-dim of `Ω` via `exists_smul_eq_of_finrank_eq_one` (from `kaehler_rank_one`) to write any `η = a • ω`, then analyzes `α.pullbackKaehler(a • ω) = 0` via `pullbackKaehler_smul_KE` + `pullbackKaehler_invariantDifferential`; the product `α.pullback a · coeff = 0` with coeff ≠ 0 forces `a = 0` via `α.pullback_injective`.
- **Hypotheses**: `omegaPullbackCoeff W α ≠ 0`.
- **Uses from project**: `kaehler_rank_one`, `invariantDifferential_ne_zero`, `exists_smul_eq_of_finrank_eq_one`, `Isogeny.pullbackKaehler_smul_KE`, `Isogeny.pullbackKaehler_invariantDifferential`, `omegaPullbackCoeff`, `α.pullback_injective`
- **Used by**: `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`
- **Visibility**: public
- **Lines**: 165–197, 31 lines
- **Notes**: Long proof (31 lines), 1 line over threshold.

---

### `theorem pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`
- **Type**: `(α : Isogeny W W) : Function.Injective α.pullbackKaehler ↔ omegaPullbackCoeff W α ≠ 0`
- **What**: The differential pullback on `Ω[K(E)/F]` is injective if and only if the omega-pullback coefficient is nonzero.
- **How**: Combines both directions via `⟨..., ...⟩`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_ne_zero_of_pullbackKaehler_injective`, `pullbackKaehler_injective_of_omegaPullbackCoeff_ne_zero`
- **Used by**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler`, `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses`, `isogeny_isSeparable_of_pullbackKaehler_injective`, `isSeparable_iff_pullbackKaehler_injective`
- **Visibility**: public
- **Lines**: 206–210, 3 lines

---

### `theorem isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler`
- **Type**: `(α : Isogeny W W) → (h_alg : α.IsSeparable ↔ Function.Injective α.pullbackKaehler) → (α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0)`
- **What**: Composes the algebra-Kähler half with the scalar half to give the full T-II-4-004 iff, assuming the algebra-Kähler half as a hypothesis.
- **How**: `h_alg.trans pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`.
- **Hypotheses**: The algebra-Kähler iff `α.IsSeparable ↔ pullbackKaehler injective` as a witness.
- **Uses from project**: `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`
- **Used by**: `isSeparable_iff_omegaPullbackCoeff_ne_zero` (the final deliverable)
- **Visibility**: public
- **Lines**: 256–260, 3 lines

---

### `theorem isogeny_formallyUnramified_of_isSeparable`
- **Type**: `(α : Isogeny W W) → α.IsSeparable → @Algebra.FormallyUnramified K(E) K(E) _ _ α.toAlgebra`
- **What**: Separability of `α` implies the algebra `K(E)/K(E)_α` is formally unramified.
- **How**: `Algebra.FormallyUnramified.of_isSeparable` directly, after promoting the isogeny's `IsSeparable` to a typeclass instance via `letI`/`haveI`.
- **Hypotheses**: `α.IsSeparable`.
- **Uses from project**: `α.toAlgebra`, `Isogeny.IsSeparable`
- **Used by**: `isogeny_subsingleton_kaehler_of_isSeparable`
- **Visibility**: public
- **Lines**: 278–285, 6 lines

---

### `theorem isogeny_subsingleton_kaehler_of_isSeparable`
- **Type**: `(α : Isogeny W W) → α.IsSeparable → @Subsingleton (Ω[K(E)⁄K(E) via α.toAlgebra])`
- **What**: Separability of `α` implies the relative Kähler module `Ω[K(E)/K(E)_α]` is trivial.
- **How**: Chains through `isogeny_formallyUnramified_of_isSeparable` and then `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`.
- **Hypotheses**: `α.IsSeparable`.
- **Uses from project**: `isogeny_formallyUnramified_of_isSeparable`, `α.toAlgebra`
- **Used by**: `isSeparable_iff_subsingleton_kaehler_of_finiteDimensional`, `isogeny_omegaCoeff_ne_zero_of_isSeparable`
- **Visibility**: public
- **Lines**: 294–301, 7 lines

---

### `theorem mapBaseChange_surjective_of_subsingleton_relativeKaehler`
- **Type**: `(R A B : Type*) [algebra tower] → [Subsingleton Ω[B⁄A]] → Function.Surjective (KaehlerDifferential.mapBaseChange R A B)`
- **What**: Abstract cotangent-sequence result: if the relative Kähler `Ω[B/A]` is trivial, then the base-change map `B ⊗[A] Ω[A/R] → Ω[B/R]` is surjective.
- **How**: Uses exactness of the cotangent sequence (`KaehlerDifferential.exact_mapBaseChange_map`) and Subsingleton to show every element of `Ω[B/R]` is in the kernel of the rightmost map, hence in the image of `mapBaseChange`.
- **Hypotheses**: Commutative algebra tower `R → A → B` with `IsScalarTower`, `Subsingleton (Ω[B⁄A])`.
- **Uses from project**: []
- **Used by**: `isogeny_omegaCoeff_ne_zero_of_isSeparable`
- **Visibility**: public
- **Lines**: 321–328, 7 lines

---

### `theorem subsingleton_relativeKaehler_of_mapBaseChange_surjective`
- **Type**: `(R A B : Type*) [algebra tower] → Function.Surjective (KaehlerDifferential.mapBaseChange R A B) → Subsingleton (Ω[B⁄A])`
- **What**: Converse of the above: surjectivity of the base-change map forces the relative Kähler to be trivial.
- **How**: Exactness gives `map = 0` (from surjectivity of `mapBaseChange`); then `KaehlerDifferential.map_surjective_of_surjective` gives surjectivity of `map : Ω[B/R] → Ω[B/A]`; combining yields `Ω[B/A]` is trivial.
- **Hypotheses**: Commutative algebra tower `R → A → B` with `IsScalarTower`, surjectivity of `mapBaseChange`.
- **Uses from project**: []
- **Used by**: `isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero`
- **Visibility**: public
- **Lines**: 342–360, 18 lines

---

### `theorem isogeny_smul_assoc_identity`
- **Type**: `(α : Isogeny W W) → (a : F) (b c : K(E)) → α.pullback (algebraMap F K(E) a * b) * c = algebraMap F K(E) a * (α.pullback b * c)`
- **What**: The `smul_assoc` identity for the algebra tower `F → K(E) → K(E)` where the inner step is `α.pullback`-twisted.
- **How**: `map_mul` + `AlgHom.commutes` + `mul_assoc`.
- **Hypotheses**: None.
- **Uses from project**: `α.pullback`
- **Used by**: unused in file (the adjacent `isogeny_isScalarTower` uses `commutes` directly)
- **Visibility**: public
- **Lines**: 391–396, 4 lines

---

### `theorem isogeny_isScalarTower`
- **Type**: `(α : Isogeny W W) → @IsScalarTower F K(E) K(E) _ α.toAlgebra.toSMul _`
- **What**: The algebra tower `F → K(E)_α → K(E)` (with `α.toAlgebra` for the middle step) satisfies the scalar tower condition.
- **How**: `IsScalarTower.of_algebraMap_eq` applied to `(α.pullback.commutes x).symm`.
- **Hypotheses**: None.
- **Uses from project**: `α.toAlgebra`, `α.pullback`
- **Used by**: `IsogenyAlgebraSource.isScalarTower` (the synonym instance)
- **Visibility**: public
- **Lines**: 411–416, 5 lines

---

### `theorem isogeny_essFiniteType_of_finiteDimensional`
- **Type**: `(α : Isogeny W W) → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule → @Algebra.EssFiniteType K(E) K(E) _ _ α.toAlgebra`
- **What**: If `K(E)` is finite-dimensional over `K(E)_α`, then it is essentially of finite type over `K(E)_α`.
- **How**: `Module.Finite.finiteType` then `EssFiniteType.of_finiteType`, both with explicit `@`-algebra instance pinning.
- **Hypotheses**: `@FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule`.
- **Uses from project**: `α.toAlgebra`
- **Used by**: `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`
- **Visibility**: public
- **Lines**: 455–466, 10 lines

---

### `theorem isogeny_finiteDimensional_of_isAlgebraic_essFiniteType`
- **Type**: `(α : Isogeny W W) → @IsAlgebraic K(E) K(E) _ _ α.toAlgebra → @EssFiniteType K(E) K(E) _ _ α.toAlgebra → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule`
- **What**: From algebraicity and essential finite type of the extension `K(E)/K(E)_α`, deduce that `K(E)` is finite-dimensional over `K(E)_α`.
- **How**: `Algebra.finite_of_essFiniteType_of_isAlgebraic` directly, after lifting hypotheses into typeclasses.
- **Hypotheses**: `IsAlgebraic` and `EssFiniteType` over `α.toAlgebra`.
- **Uses from project**: `α.toAlgebra`
- **Used by**: unused in file (superseded by synonym-based version)
- **Visibility**: public
- **Lines**: 491–502, 11 lines

---

### `theorem isogeny_isAlgebraic_of_finite_intermediate`
- **Type**: `(α : Isogeny W W) → (L : Type*) [Field L] [Algebra L K(E)] [Module.Finite L K(E)] → (h_tower : @IsScalarTower L K(E) K(E) _ α.toAlgebra.toSMul _) → @IsAlgebraic K(E) K(E) _ _ α.toAlgebra`
- **What**: If `K(E)` is finite over some intermediate field `L` (with the right tower), then `K(E)` is algebraic over `K(E)_α`.
- **How**: `Algebra.IsAlgebraic.of_finite` for `L → K(E)`, then `Algebra.IsAlgebraic.tower_top` to lift to `K(E)_α`.
- **Hypotheses**: A finite intermediate field `L` below `K(E)_α`.
- **Uses from project**: `α.toAlgebra`
- **Used by**: unused in file (superseded by transcendence-degree approach)
- **Visibility**: public
- **Lines**: 523–537, 14 lines

---

### `theorem isogeny_isSeparable_of_kaehler_witnesses`
- **Type**: `(α : Isogeny W W) → @Subsingleton (Ω[K(E)⁄K(E)_α]) → @EssFiniteType K(E) K(E) _ _ α.toAlgebra → α.IsSeparable`
- **What**: The reverse direction of T-II-4-004 (witness-parametric): trivial relative Kähler plus essentially-finite-type implies separability.
- **How**: Promotes `Subsingleton` to `FormallyUnramified` via `⟨h_sub⟩`, then applies `Algebra.FormallyUnramified.iff_isSeparable.mp inferInstance`.
- **Hypotheses**: `Subsingleton Ω[K(E)/K(E)_α]`, `EssFiniteType K(E) K(E)` over `α.toAlgebra`.
- **Uses from project**: `α.toAlgebra`, `Isogeny.IsSeparable`
- **Used by**: `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`
- **Visibility**: public
- **Lines**: 569–581, 12 lines

---

### `theorem isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`
- **Type**: `(α : Isogeny W W) → @Subsingleton (Ω[K(E)⁄K(E)_α]) → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule → α.IsSeparable`
- **What**: Reverse direction of T-II-4-004: trivial relative Kähler plus Witness #2 (FiniteDimensional) implies separability.
- **How**: Composes `isogeny_essFiniteType_of_finiteDimensional` and `isogeny_isSeparable_of_kaehler_witnesses`.
- **Hypotheses**: `Subsingleton` relative Kähler, `FiniteDimensional` witness.
- **Uses from project**: `isogeny_isSeparable_of_kaehler_witnesses`, `isogeny_essFiniteType_of_finiteDimensional`
- **Used by**: `isSeparable_iff_subsingleton_kaehler_of_finiteDimensional`, `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim`, `isogeny_isSeparable_of_pullbackKaehler_injective_witnesses`
- **Visibility**: public
- **Lines**: 593–601, 3 lines

---

### `theorem isSeparable_iff_subsingleton_kaehler_of_finiteDimensional`
- **Type**: `(α : Isogeny W W) → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule → (α.IsSeparable ↔ @Subsingleton (Ω[K(E)⁄K(E)_α]))`
- **What**: Full algebra-Kähler iff: separability is equivalent to triviality of the relative Kähler module, given Witness #2.
- **How**: Pairs `isogeny_subsingleton_kaehler_of_isSeparable` (forward) and `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional` (reverse).
- **Hypotheses**: `FiniteDimensional` witness.
- **Uses from project**: `isogeny_subsingleton_kaehler_of_isSeparable`, `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`
- **Used by**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses`
- **Visibility**: public
- **Lines**: 617–626, 8 lines

---

### `theorem isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses`
- **Type**: `(α : Isogeny W W) → @FiniteDimensional... → (Subsingleton ... ↔ Injective α.pullbackKaehler) → (α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0)`
- **What**: Full T-II-4-004 iff, parametric on Witness #2 (FiniteDimensional) and a bridge witness.
- **How**: Chains `isSeparable_iff_subsingleton_kaehler_of_finiteDimensional.trans(h_bridge.trans(pullbackKaehler_injective_iff...))`.
- **Hypotheses**: FiniteDimensional witness and a Subsingleton↔Injective bridge hypothesis.
- **Uses from project**: `isSeparable_iff_subsingleton_kaehler_of_finiteDimensional`, `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 653–662, 4 lines

---

### `theorem isSeparable_iff_pullbackKaehler_injective_of_witnesses`
- **Type**: `(α : Isogeny W W) → (h_fwd : α.IsSeparable → Injective α.pullbackKaehler) → (h_rev : Injective α.pullbackKaehler → α.IsSeparable) → (α.IsSeparable ↔ Injective α.pullbackKaehler)`
- **What**: Utility combinator: assembles the full algebra-Kähler iff from separately supplied forward and reverse directions.
- **How**: Plain `⟨h_fwd, h_rev⟩`.
- **Hypotheses**: Both directions as explicit hypotheses.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 680–685, 2 lines

---

### `def IsogenyAlgebraSource`
- **Type**: `(_ : Isogeny W.toAffine W.toAffine) : Type _` = `W.toAffine.FunctionField`
- **What**: A type synonym for `K(E)` on the source side of an isogeny's algebra structure, carrying `α.toAlgebra` as the unique `Algebra` instance (eliminates the `OreLocalization.instSMul` vs `α.toAlgebra.toSMul` defeq ambiguity).
- **How**: Pure `def` alias (no proof content).
- **Hypotheses**: None.
- **Uses from project**: `Isogeny`, `FunctionField`
- **Used by**: all `IsogenyAlgebraSource.*` instances, and many theorems below using the synonym
- **Visibility**: public
- **Lines**: 703–704, 0 lines proof

---

### `noncomputable instance IsogenyAlgebraSource.commRing`
- **Type**: `CommRing (IsogenyAlgebraSource W α)`
- **What**: The type synonym inherits the `CommRing` structure from `K(E)`.
- **How**: `inferInstanceAs (CommRing W.toAffine.FunctionField)`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`
- **Used by**: downstream instances in the namespace
- **Visibility**: public
- **Lines**: 711–712, 1 line

---

### `noncomputable instance IsogenyAlgebraSource.field`
- **Type**: `Field (IsogenyAlgebraSource W α)`
- **What**: The type synonym inherits the `Field` structure from `K(E)`.
- **How**: `inferInstanceAs (Field W.toAffine.FunctionField)`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`
- **Used by**: downstream instances
- **Visibility**: public
- **Lines**: 715–716, 1 line

---

### `noncomputable instance IsogenyAlgebraSource.algebraF`
- **Type**: `Algebra F (IsogenyAlgebraSource W α)`
- **What**: The type synonym inherits the `F`-algebra structure from `K(E)`.
- **How**: `inferInstanceAs (Algebra F W.toAffine.FunctionField)`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`
- **Used by**: `IsogenyAlgebraSource.isScalarTower`, `isogenyAlgebraSource_isAlgebraic`, `functionField_essFiniteType_F`
- **Visibility**: public
- **Lines**: 720–721, 1 line

---

### `noncomputable instance IsogenyAlgebraSource.algebra`
- **Type**: `Algebra (IsogenyAlgebraSource W α) K(E)`
- **What**: The type synonym carries `α.toAlgebra` as its unique `Algebra` instance on the target side.
- **How**: Direct assignment `α.toAlgebra`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`, `α.toAlgebra`
- **Used by**: all callers of the synonym-based API
- **Visibility**: public
- **Lines**: 727–729, 1 line

---

### `noncomputable instance IsogenyAlgebraSource.isScalarTower`
- **Type**: `IsScalarTower F (IsogenyAlgebraSource W α) K(E)`
- **What**: The synonym provides the scalar tower `F → K(E)_α → K(E)`.
- **How**: `IsScalarTower.of_algebraMap_eq (fun x => (α.pullback.commutes x).symm)`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`, `α.pullback`
- **Used by**: `isogenyAlgebraSource_essFiniteType`, `isogenyAlgebraSource_isAlgebraic` (transitively), `isogeny_mapBaseChange_one_tmul_D`, `isogeny_mapBaseChange_surjective_of_omegaCoeff_ne_zero`, `isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero`, `isogeny_omegaCoeff_ne_zero_of_isSeparable`
- **Visibility**: public
- **Lines**: 733–735, 2 lines

---

### `theorem weierstrass_functionField_trdeg_eq_one`
- **Type**: `Algebra.trdeg F W.toAffine.FunctionField = 1`
- **What**: The transcendence degree of `K(E)` over `F` is 1, for any Weierstrass curve.
- **How**: Packages `W.toAffine` into a `SmoothPlaneCurve` and applies `functionField_trdeg_eq_one`.
- **Hypotheses**: `W` elliptic.
- **Uses from project**: `SmoothPlaneCurve`, `functionField_trdeg_eq_one`
- **Used by**: `isogenyAlgebraSource_isAlgebraic` (used twice)
- **Visibility**: public
- **Lines**: 749–752, 3 lines

---

### `theorem isogeny_finiteDimensional_of_isAlgebraic_synonym`
- **Type**: `(α : Isogeny W W) → [IsAlgebraic (IsogenyAlgebraSource W α) K(E)] → [EssFiniteType (IsogenyAlgebraSource W α) K(E)] → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule`
- **What**: Discharges Witness #2 (FiniteDimensional) from the synonym-based IsAlgebraic and EssFiniteType instances.
- **How**: `@Algebra.finite_of_essFiniteType_of_isAlgebraic (IsogenyAlgebraSource W α) ...`.
- **Hypotheses**: Both instances carried as typeclass arguments via `[]`.
- **Uses from project**: `IsogenyAlgebraSource`, `α.toAlgebra`
- **Used by**: `isogeny_finiteDimensional`
- **Visibility**: public
- **Lines**: 769–776, 7 lines

---

### `instance functionField_essFiniteType_F`
- **Type**: `Algebra.EssFiniteType F W.toAffine.FunctionField`
- **What**: `K(E)` is essentially of finite type over `F`. Relies on `CoordinateRing` being `FiniteType` over `F` and localization preserving `EssFiniteType`.
- **How**: Chains `EssFiniteType.of_finiteType`, `EssFiniteType.of_isLocalization`, and `EssFiniteType.comp`.
- **Hypotheses**: `W.toAffine.IsElliptic`.
- **Uses from project**: `W.toAffine.CoordinateRing`, `W.toAffine.FunctionField`
- **Used by**: `isogenyAlgebraSource_essFiniteType`
- **Visibility**: public
- **Lines**: 789–799, 10 lines

---

### `instance isogenyAlgebraSource_essFiniteType`
- **Type**: `(α : Isogeny W W) → Algebra.EssFiniteType (IsogenyAlgebraSource W α) K(E)`
- **What**: The synonym type `IsogenyAlgebraSource W α` makes `K(E)` essentially of finite type, by lifting from `F` via `of_comp`.
- **How**: `Algebra.EssFiniteType.of_comp F (IsogenyAlgebraSource W α) K(E)`, using the scalar tower and `functionField_essFiniteType_F`.
- **Hypotheses**: None (uses `functionField_essFiniteType_F` and `IsogenyAlgebraSource.isScalarTower`).
- **Uses from project**: `IsogenyAlgebraSource`, `functionField_essFiniteType_F`
- **Used by**: `isogenyAlgebraSource_isAlgebraic` (implicitly, via `isogeny_finiteDimensional_of_isAlgebraic_synonym`)
- **Visibility**: public
- **Lines**: 804–807, 3 lines

---

### `instance isogenyAlgebraSource_faithfulSMul_F`
- **Type**: `(α : Isogeny W W) → FaithfulSMul F (IsogenyAlgebraSource W α)`
- **What**: The `F`-action on the synonym is faithful (algebra map `F → K(E)` is injective).
- **How**: `faithfulSMul_iff_algebraMap_injective` + injectivity of ring hom from a field.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`
- **Used by**: `isogenyAlgebraSource_isAlgebraic` (needed for `trdeg_add_eq`)
- **Visibility**: public
- **Lines**: 830–834, 4 lines

---

### `instance isogenyAlgebraSource_faithfulSMul_KE`
- **Type**: `(α : Isogeny W W) → FaithfulSMul (IsogenyAlgebraSource W α) K(E)`
- **What**: The `K(E)_α`-action on `K(E)` is faithful (algebra map is `α.pullback`, which is injective).
- **How**: `faithfulSMul_iff_algebraMap_injective` + `α.pullback_injective`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`, `α.pullback_injective`
- **Used by**: `isogenyAlgebraSource_isAlgebraic` (needed for `trdeg_add_eq`)
- **Visibility**: public
- **Lines**: 838–842, 4 lines

---

### `instance isogenyAlgebraSource_isAlgebraic`
- **Type**: `(α : Isogeny W W) → Algebra.IsAlgebraic (IsogenyAlgebraSource W α) K(E)`
- **What**: `K(E)` is algebraic over `K(E)_α`. Proof uses that both have transcendence degree 1 over `F`, so the relative transcendence degree is 0, hence algebraic.
- **How**: `trdeg_eq_zero_iff` + `trdeg_add_eq F (IsogenyAlgebraSource W α) K(E)` + `weierstrass_functionField_trdeg_eq_one` (twice) + arithmetic on `Cardinal`.
- **Hypotheses**: `isogenyAlgebraSource_faithfulSMul_F`, `isogenyAlgebraSource_faithfulSMul_KE`, `IsogenyAlgebraSource.isScalarTower` (implicit).
- **Uses from project**: `IsogenyAlgebraSource`, `weierstrass_functionField_trdeg_eq_one`, `trdeg_add_eq`, `trdeg_eq_zero_iff`
- **Used by**: `isogeny_finiteDimensional_of_isAlgebraic_synonym` (via instance search)
- **Visibility**: public
- **Lines**: 848–866, 17 lines

---

### `theorem isogeny_finiteDimensional`
- **Type**: `(α : Isogeny W W) → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule`
- **What**: Witness #2: the function field `K(E)` is finite-dimensional over `K(E)_α` for any isogeny. Unconditional.
- **How**: Applies `isogeny_finiteDimensional_of_isAlgebraic_synonym`, which fires from the synonym instances `isogenyAlgebraSource_isAlgebraic` and `isogenyAlgebraSource_essFiniteType`.
- **Hypotheses**: None.
- **Uses from project**: `isogeny_finiteDimensional_of_isAlgebraic_synonym`
- **Used by**: `isogeny_degree_pos`, `isogeny_isSeparable_of_pullbackKaehler_injective`
- **Visibility**: public
- **Lines**: 874–878, 3 lines

---

### `theorem isogeny_degree_pos`
- **Type**: `(α : Isogeny W W) → 0 < α.degree`
- **What**: Isogeny degrees are positive: the finrank of `K(E)` as a `K(E)_α`-module is at least 1.
- **How**: Unfolds `Isogeny.degree`, then applies `@Module.finrank_pos` with `isogeny_finiteDimensional` and `Nontrivial K(E)`.
- **Hypotheses**: None.
- **Uses from project**: `isogeny_finiteDimensional`, `α.degree`, `α.toAlgebra`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 889–896, 7 lines

---

### `theorem isogeny_mapBaseChange_one_tmul_D`
- **Type**: `(α : Isogeny W W) (x : K(E)) → KaehlerDifferential.mapBaseChange F (IsogenyAlgebraSource W α) K(E) (1 ⊗ₜ D x) = D (α.pullback x)`
- **What**: The cotangent base-change map sends `1 ⊗ₜ D x` (on the synonym side) to `D(α.pullback x)` (on the target side).
- **How**: `KaehlerDifferential.mapBaseChange_tmul`, `one_smul`, `KaehlerDifferential.map_D`, and a `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`, `α.pullback`
- **Used by**: unused in file (the surjectivity proof below uses a different element)
- **Visibility**: public
- **Lines**: 907–916, 8 lines

---

### `theorem isogeny_mapBaseChange_surjective_of_omegaCoeff_ne_zero`
- **Type**: `(α : Isogeny W W) → omegaPullbackCoeff W α ≠ 0 → Function.Surjective (KaehlerDifferential.mapBaseChange F (IsogenyAlgebraSource W α) K(E))`
- **What**: If `omegaPullbackCoeff ≠ 0`, the cotangent base-change map is surjective; this is the forward cotangent bridge.
- **How**: Given any `y = a • ω`, constructs explicit preimage using `omegaPullbackCoeff_spec` to express `ω` as `(alpha_star_u · c)⁻¹ • D(α.pullback x_gen)`, then algebraic calculation closes with `field_simp`.
- **Hypotheses**: `omegaPullbackCoeff W α ≠ 0`.
- **Uses from project**: `IsogenyAlgebraSource`, `invariantDifferential_ne_zero`, `kaehler_rank_one`, `exists_smul_eq_of_finrank_eq_one`, `omegaPullbackCoeff_spec`, `alpha_star_u_eq`, `u_gen_ne_zero`, `omegaPullbackCoeff`
- **Used by**: `isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero`
- **Visibility**: public
- **Lines**: 923–969, 46 lines
- **Notes**: Long proof (46 lines); explicit preimage construction with `field_simp` cancellation.

---

### `theorem isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero`
- **Type**: `(α : Isogeny W W) → omegaPullbackCoeff W α ≠ 0 → Subsingleton (Ω[K(E)⁄IsogenyAlgebraSource W α])`
- **What**: If the omega-pullback coefficient is nonzero, the relative Kähler module (synonym form) is trivial.
- **How**: `subsingleton_relativeKaehler_of_mapBaseChange_surjective` applied to `isogeny_mapBaseChange_surjective_of_omegaCoeff_ne_zero`.
- **Hypotheses**: `omegaPullbackCoeff W α ≠ 0`.
- **Uses from project**: `IsogenyAlgebraSource`, `subsingleton_relativeKaehler_of_mapBaseChange_surjective`, `isogeny_mapBaseChange_surjective_of_omegaCoeff_ne_zero`
- **Used by**: `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim`
- **Visibility**: public
- **Lines**: 974–980, 6 lines

---

### `theorem isogeny_subsingleton_via_synonym_eq`
- **Type**: `(α : Isogeny W W) → Subsingleton (Ω[K(E)⁄IsogenyAlgebraSource W α]) ↔ @Subsingleton (Ω[K(E)⁄K(E) via α.toAlgebra])`
- **What**: The relative Kähler module in synonym form equals the one in `@`-pinned form; these are definitionally equal.
- **How**: `Iff.rfl`.
- **Hypotheses**: None.
- **Uses from project**: `IsogenyAlgebraSource`, `α.toAlgebra`
- **Used by**: `isogeny_omegaCoeff_ne_zero_of_isSeparable`, `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim`
- **Visibility**: public
- **Lines**: 986–991, 1 line

---

### `theorem isogeny_omegaCoeff_ne_zero_of_isSeparable`
- **Type**: `(α : Isogeny W W) → α.IsSeparable → omegaPullbackCoeff W α ≠ 0`
- **What**: The forward direction of T-II-4-004: separability implies the omega-pullback coefficient is nonzero.
- **How**: Contrapositive: assume coeff = 0, derive that `pullbackKaehler` is identically zero (from 1-dim of Ω), then show `mapBaseChange = 0` (since `map D` = 0), contradicting that `ω` is in the image of `mapBaseChange` (from `mapBaseChange_surjective_of_subsingleton_relativeKaehler` applied to `isogeny_subsingleton_kaehler_of_isSeparable`). Uses `KaehlerDifferential.exact_mapBaseChange_map` implicitly.
- **Hypotheses**: `α.IsSeparable`.
- **Uses from project**: `invariantDifferential_ne_zero`, `kaehler_rank_one`, `exists_smul_eq_of_finrank_eq_one`, `Isogeny.pullbackKaehler_invariantDifferential`, `Isogeny.pullbackKaehler_smul_KE`, `Isogeny.pullbackKaehler_D`, `IsogenyAlgebraSource`, `isogeny_subsingleton_via_synonym_eq`, `isogeny_subsingleton_kaehler_of_isSeparable`, `mapBaseChange_surjective_of_subsingleton_relativeKaehler`, `u_gen`
- **Used by**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`, `isSeparable_iff_pullbackKaehler_injective`
- **Visibility**: public
- **Lines**: 1001–1100, 99 lines
- **Notes**: Long proof (99 lines); the most involved proof in the file, with an elaborate argument showing `mapBaseChange = 0` via `Subsingleton.elim` on a different relative Kähler than the one in scope.

---

### `theorem isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim`
- **Type**: `(α : Isogeny W W) → omegaPullbackCoeff W α ≠ 0 → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule → α.IsSeparable`
- **What**: Reverse direction of T-II-4-004 (FiniteDim only, no bridge needed): nonzero coeff + Witness #2 implies separability.
- **How**: `isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero` → `isogeny_subsingleton_via_synonym_eq.mp` → `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`.
- **Hypotheses**: `omegaPullbackCoeff W α ≠ 0`, `FiniteDimensional`.
- **Uses from project**: `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`, `isogeny_subsingleton_via_synonym_eq`, `isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero`
- **Used by**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`, `isogeny_isSeparable_of_pullbackKaehler_injective`
- **Visibility**: public
- **Lines**: 1110–1119, 9 lines

---

### `theorem isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`
- **Type**: `(α : Isogeny W W) → @FiniteDimensional K(E) K(E) _ _ α.toAlgebra.toModule → (α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0)`
- **What**: Full T-II-4-004 iff parametric on Witness #2 only (no bridge witness needed).
- **How**: Pairs `isogeny_omegaCoeff_ne_zero_of_isSeparable` and `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim`.
- **Hypotheses**: `FiniteDimensional` witness.
- **Uses from project**: `isogeny_omegaCoeff_ne_zero_of_isSeparable`, `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim`
- **Used by**: unused in file (superseded by the unconditional form)
- **Visibility**: public
- **Lines**: 1129–1135, 5 lines

---

### `theorem isogeny_isSeparable_of_pullbackKaehler_injective_witnesses`
- **Type**: `(α : Isogeny W W) → Injective α.pullbackKaehler → @FiniteDimensional ... → (Subsingleton ... ↔ Injective α.pullbackKaehler) → α.IsSeparable`
- **What**: Witness-parametric reverse direction (pullbackKaehler form), combining the bridge with Subsingleton+FiniteDim → IsSeparable.
- **How**: `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional` after `h_bridge.mpr h_inj`.
- **Hypotheses**: Injectivity, FiniteDimensional, and a bridge hypothesis.
- **Uses from project**: `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1152–1162, 9 lines

---

### `theorem isogeny_isSeparable_of_pullbackKaehler_injective`
- **Type**: `(α : Isogeny W W) → Function.Injective α.pullbackKaehler → α.IsSeparable`
- **What**: Unconditional reverse of T-II-4-004 (pullbackKaehler form): injectivity of differential pullback implies separability.
- **How**: `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero.mp h_inj` then `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim` with `isogeny_finiteDimensional`.
- **Hypotheses**: Injectivity of `α.pullbackKaehler`.
- **Uses from project**: `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`, `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim`, `isogeny_finiteDimensional`
- **Used by**: `isSeparable_iff_pullbackKaehler_injective`
- **Visibility**: public
- **Lines**: 1183–1189, 6 lines

---

### `theorem isSeparable_iff_pullbackKaehler_injective`
- **Type**: `(α : Isogeny W W) : α.IsSeparable ↔ Function.Injective α.pullbackKaehler`
- **What**: The algebra-Kähler half of T-II-4-004 (Silverman II.4.2(c)): separability is equivalent to injectivity of the differential pullback. Unconditional.
- **How**: Forward via `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero.mpr` + `isogeny_omegaCoeff_ne_zero_of_isSeparable`; reverse via `isogeny_isSeparable_of_pullbackKaehler_injective`.
- **Hypotheses**: None.
- **Uses from project**: `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`, `isogeny_omegaCoeff_ne_zero_of_isSeparable`, `isogeny_isSeparable_of_pullbackKaehler_injective`
- **Used by**: `isSeparable_iff_omegaPullbackCoeff_ne_zero`
- **Visibility**: public
- **Lines**: 1199–1204, 5 lines

---

### `theorem isSeparable_iff_omegaPullbackCoeff_ne_zero`
- **Type**: `(α : Isogeny W W) : α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0`
- **What**: **T-II-4-004 (deliverable target)**: separability of an isogeny is equivalent to nonvanishing of the omega-pullback coefficient. Silverman II.4.2(c). Unconditional.
- **How**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler` applied to `isSeparable_iff_pullbackKaehler_injective`.
- **Hypotheses**: None.
- **Uses from project**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler`, `isSeparable_iff_pullbackKaehler_injective`
- **Used by**: unused in file (this is the final export)
- **Visibility**: public
- **Lines**: 1212–1216, 4 lines
