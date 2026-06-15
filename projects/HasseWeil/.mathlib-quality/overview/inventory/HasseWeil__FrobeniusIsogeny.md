# Inventory: ./HasseWeil/FrobeniusIsogeny.lean

**File**: `HasseWeil/FrobeniusIsogeny.lean`
**Total declarations**: 26
**Defs**: 3 (frobeniusIsogeny, frobeniusRangeEquiv, frobFracRange)
**Lemmas/Theorems**: 13
**Instances**: 10
**Sorries**: none (the word "sorry" appears only in a doc-comment on line 83)
**Lines**: 538

---

## Variable context (top of file)

```
variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
```

---

## Declarations

### `noncomputable def frobeniusIsogeny`
- **Type**: `PullbackIsogeny K W.toAffine W.toAffine`
- **What**: The q-th power Frobenius endomorphism as a `PullbackIsogeny`, whose pullback on `K(E)` is the algebra map `f ↦ f^q` (i.e., `frobeniusAlgHom K W.toAffine.FunctionField`).
- **How**: Direct `where` construction; no nontrivial proof required beyond providing the pullback field.
- **Hypotheses**: `K` finite field, `W` elliptic Weierstrass curve over `K`.
- **Uses from project**: `frobeniusAlgHom` (from `Auxiliary.Universal`).
- **Used by**: `frobeniusIsogeny_pullback_apply`, `frobeniusIsogeny_degree`, `frobeniusIsogeny_pow_mem_fieldRange`, `frobeniusIsogeny_pullback_range` (all in this file); also used by `IsogenyAG.lean` (via `frobenius_finrank_functionField`), `Frobenius.lean`.
- **Visibility**: public
- **Lines**: 46–48 (2 lines proof body)
- **Notes**: Main definition of file; no heartbeat issues.

---

### `theorem frobeniusIsogeny_pullback_apply`
- **Type**: `(frobeniusIsogeny K W).pullback f = f ^ Fintype.card K`
- **What**: The Frobenius isogeny's pullback sends `f` to `f^q` where `q = #K`.
- **How**: Unfolds the definition to `frobeniusAlgHom`, then applies `coe_frobeniusAlgHom` (from `Auxiliary.Universal`).
- **Hypotheses**: Omits `[DecidableEq K]`. `f : W.toAffine.FunctionField`.
- **Uses from project**: `frobeniusIsogeny`, `coe_frobeniusAlgHom`.
- **Used by**: `frobeniusIsogeny_pullback_range`.
- **Visibility**: public
- **Lines**: 51–55 (5 lines)
- **Notes**: Short; `omit [DecidableEq K]` annotation is notable.

---

### `private noncomputable def frobeniusRangeEquiv`
- **Type**: `W.toAffine.FunctionField ≃+* (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange`
- **What**: The Frobenius algebra map restricts to a ring equivalence from `K(E)` onto its image `K(E)^q`, using injectivity of algebra maps from fields.
- **How**: `AlgEquiv.ofInjective` applied to the injective `frobeniusAlgHom`, then `.toRingEquiv`.
- **Hypotheses**: Injectivity of `frobeniusAlgHom` (any algHom from a field is injective).
- **Uses from project**: `frobeniusAlgHom`.
- **Used by**: `frobenius_finrank_eq_fieldRange_finrank`, `finrank_over_frobenius_image` (for `h_intermediate`).
- **Visibility**: private
- **Lines**: 86–91 (6 lines)
- **Notes**: Auxiliary ring equivalence used in two separate sub-arguments of the degree proof.

---

### `private theorem frobenius_finrank_eq_fieldRange_finrank`
- **Type**: `@Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _ (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.toAlgebra.toModule = Module.finrank (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange W.toAffine.FunctionField`
- **What**: The finrank of `K(E)` as a module over itself via the Frobenius scalar action equals the finrank of the extension `K(E)/K(E)^q` (i.e., the Frobenius-twisted module rank equals the genuine field extension degree).
- **How**: `Algebra.finrank_eq_of_equiv_equiv` with `frobeniusRangeEquiv` as the scalar-field equivalence and `RingEquiv.refl` as the module equivalence; compatibility is verified by `AlgEquiv.ofInjective_apply` and `simp`.
- **Hypotheses**: Standard field/fintype hypotheses.
- **Uses from project**: `frobeniusRangeEquiv`.
- **Used by**: `frobenius_finrank_functionField`.
- **Visibility**: private
- **Lines**: 105–128 (24 lines)
- **Notes**: Careful algebra-instance juggling with explicit `@`; uses `Algebra.finrank_eq_of_equiv_equiv` from mathlib.

---

### `noncomputable instance coordinateRing_module`
- **Type**: `Module K[X] W.toAffine.CoordinateRing`
- **What**: Gives `K[X]` an explicit module action on `W.toAffine.CoordinateRing` via the algebra structure (needed to make typeclass inference deterministic).
- **How**: `@Algebra.toModule` applied to the inferred algebra instance.
- **Hypotheses**: Standard.
- **Uses from project**: none (standard mathlib instances).
- **Used by**: `coordinateRing_finite`, `finrank_coordinateRing_eq_two` (implicitly).
- **Visibility**: public
- **Lines**: 130–132 (3 lines)
- **Notes**: Explicit instance to guide synthesis; redundant with mathlib's general construction but needed for transparency.

---

### `instance coordinateRing_finite`
- **Type**: `Module.Finite K[X] W.toAffine.CoordinateRing`
- **What**: The coordinate ring is a finitely generated `K[X]`-module, witnessed by the `{1, y}` basis.
- **How**: `Module.Finite.of_basis` applied to `Affine.CoordinateRing.basis W.toAffine`.
- **Hypotheses**: Elliptic curve (`IsElliptic`).
- **Uses from project**: `Affine.CoordinateRing.basis` (from mathlib or project).
- **Used by**: Implicitly by `finrank_coordinateRing_eq_two` and downstream.
- **Visibility**: public
- **Lines**: 134–135 (2 lines)
- **Notes**: None.

---

### `theorem finrank_coordinateRing_eq_two`
- **Type**: `Module.finrank K[X] W.toAffine.CoordinateRing = 2`
- **What**: The coordinate ring `K[X,Y]/(W)` is a free `K[X]`-module of rank 2 (with basis `{1, y}`).
- **How**: `Module.finrank_eq_card_basis` applied to `Affine.CoordinateRing.basis`, then `Fintype.card_fin 2`.
- **Hypotheses**: Standard; needs `coordinateRing_module` and `coordinateRing_finite`.
- **Uses from project**: `Affine.CoordinateRing.basis`.
- **Used by**: `finrank_functionField_eq_two` (via `isBaseChange_coordToFunc`); also used by `Basic.lean` (as a pattern for `mulByInt_finrank_coordinateRing_eq_two`).
- **Visibility**: public
- **Lines**: 139–142 (4 lines)
- **Notes**: Key API used externally in `L6Witnesses.lean`, `GapSpines.lean` (and mirrors in `Basic.lean`).

---

### `noncomputable instance : FaithfulSMul K[X] W.toAffine.FunctionField`
- **Type**: `FaithfulSMul K[X] W.toAffine.FunctionField`
- **What**: The action of `K[X]` on the function field `K(E)` is faithful (the algebra map `K[X] → K(E)` is injective).
- **How**: Injectivity follows from composing `IsFractionRing.injective` (CoordinateRing → FunctionField) with `Affine.CoordinateRing.algebraMap_poly_injective` (K[X] → CoordinateRing).
- **Hypotheses**: Needs `set_option synthInstance.maxHeartbeats 40000`.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective`.
- **Used by**: `IsLocalization` private instance (line 171), `FaithfulSMul K[X] CoordinateRing` (line 166) uses the same pattern.
- **Visibility**: public (anonymous instance)
- **Lines**: 146–151 (6 lines)
- **Notes**: `set_option synthInstance.maxHeartbeats 40000` — NO justifying comment.

---

### `noncomputable instance : Algebra (FractionRing K[X]) W.toAffine.FunctionField`
- **Type**: `Algebra (FractionRing K[X]) W.toAffine.FunctionField`
- **What**: Makes `FractionRing K[X] = K(x)` into a `K(E)`-algebra via the universal property of localization (`FractionRing.liftAlgebra`).
- **How**: Direct term `FractionRing.liftAlgebra K[X] W.toAffine.FunctionField`.
- **Hypotheses**: `FaithfulSMul K[X] W.toAffine.FunctionField`.
- **Uses from project**: none beyond mathlib.
- **Used by**: `IsScalarTower K[X] (FractionRing K[X]) FunctionField`, `isBaseChange_coordToFunc`, `finrank_functionField_eq_two`, `finrank_over_frobenius_image`.
- **Visibility**: public (anonymous instance)
- **Lines**: 154–155 (2 lines)
- **Notes**: None.

---

### `noncomputable instance : IsScalarTower K[X] (FractionRing K[X]) W.toAffine.FunctionField`
- **Type**: `IsScalarTower K[X] (FractionRing K[X]) W.toAffine.FunctionField`
- **What**: The scalar towers `K[X] → K(x) → K(E)` are compatible (i.e., `FractionRing.isScalarTower_liftAlgebra`).
- **How**: Direct term `FractionRing.isScalarTower_liftAlgebra K[X] W.toAffine.FunctionField`.
- **Hypotheses**: Preceding algebra instances.
- **Uses from project**: none.
- **Used by**: `isBaseChange_coordToFunc`, `finrank_functionField_eq_two`, `finrank_over_frobenius_image`.
- **Visibility**: public (anonymous instance)
- **Lines**: 157–158 (2 lines)
- **Notes**: None.

---

### `noncomputable instance : Algebra.IsIntegral K[X] W.toAffine.CoordinateRing`
- **Type**: `Algebra.IsIntegral K[X] W.toAffine.CoordinateRing`
- **What**: The coordinate ring is integral over `K[X]` (follows from finite generation as a module).
- **How**: `Algebra.IsIntegral.of_finite K[X] W.toAffine.CoordinateRing` (uses `coordinateRing_finite`).
- **Hypotheses**: `coordinateRing_finite`.
- **Uses from project**: `coordinateRing_finite` (implicitly).
- **Used by**: `IsLocalization` private instance (line 171).
- **Visibility**: public (anonymous instance)
- **Lines**: 163–164 (2 lines)
- **Notes**: Doc-comment explains this replicates an unexported mathlib result.

---

### `noncomputable instance : FaithfulSMul K[X] W.toAffine.CoordinateRing`
- **Type**: `FaithfulSMul K[X] W.toAffine.CoordinateRing`
- **What**: The action of `K[X]` on the coordinate ring is faithful (algebra map is injective).
- **How**: `Affine.CoordinateRing.algebraMap_poly_injective` directly gives the desired injectivity.
- **Hypotheses**: Standard.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective`.
- **Used by**: `IsLocalization` private instance (line 171).
- **Visibility**: public (anonymous instance)
- **Lines**: 166–169 (4 lines)
- **Notes**: None.

---

### `private noncomputable instance : IsLocalization (...) W.toAffine.FunctionField`
- **Type**: `IsLocalization (Algebra.algebraMapSubmonoid W.toAffine.CoordinateRing (nonZeroDivisors K[X])) W.toAffine.FunctionField`
- **What**: The function field is a localization of the coordinate ring at the image of the non-zero-divisors of `K[X]`.
- **How**: Uses `Algebra.IsAlgebraic.isAlgebraic` (from `Algebra.IsIntegral.isAlgebraic`), `FaithfulSMul.algebraMap_injective` to get `NoZeroDivisors`, then `IsLocalization.iff_of_le_of_exists_dvd` together with `Algebra.IsAlgebraic.isAlgebraic.exists_nonzero_dvd`.
- **Hypotheses**: `Algebra.IsIntegral K[X] CoordinateRing` and `FaithfulSMul K[X] CoordinateRing`.
- **Uses from project**: `Algebra.IsIntegral K[X] W.toAffine.CoordinateRing`, `FaithfulSMul K[X] W.toAffine.CoordinateRing`.
- **Used by**: `IsLocalizedModule` private instance (line 185).
- **Visibility**: private
- **Lines**: 171–182 (12 lines)
- **Notes**: Uses `IsLocalization.iff_of_le_of_exists_dvd` — non-trivial mathlib machinery.

---

### `private noncomputable instance : IsLocalizedModule (nonZeroDivisors K[X]) ...`
- **Type**: `IsLocalizedModule (nonZeroDivisors K[X]) (IsScalarTower.toAlgHom K[X] W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap`
- **What**: The linear map CoordinateRing → FunctionField is a localization-of-modules at the non-zero-divisors of `K[X]`.
- **How**: `isLocalizedModule_iff_isLocalization.mpr inferInstance`.
- **Hypotheses**: `IsLocalization` instance above.
- **Uses from project**: Private `IsLocalization` instance.
- **Used by**: `isBaseChange_coordToFunc`.
- **Visibility**: private
- **Lines**: 185–187 (3 lines)
- **Notes**: Thin adapter; depends on the private `IsLocalization` above.

---

### `private theorem isBaseChange_coordToFunc`
- **Type**: `IsBaseChange (FractionRing K[X]) (IsScalarTower.toAlgHom K[X] W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap`
- **What**: The natural map CoordinateRing → FunctionField presents FunctionField as the base change `FractionRing(K[X]) ⊗[K[X]] CoordinateRing`.
- **How**: `(isLocalizedModule_iff_isBaseChange (nonZeroDivisors K[X]) ..).mp inferInstance`.
- **Hypotheses**: `IsLocalizedModule` instance.
- **Uses from project**: Private `IsLocalizedModule` instance.
- **Used by**: `finrank_functionField_eq_two`.
- **Visibility**: private
- **Lines**: 191–194 (4 lines)
- **Notes**: Key bridge lemma enabling the finrank computation.

---

### `theorem finrank_functionField_eq_two`
- **Type**: `Module.finrank (FractionRing K[X]) W.toAffine.FunctionField = 2`
- **What**: The function field `K(E)` has degree 2 over the rational function field `K(x) = FractionRing K[X]`.
- **How**: `isBaseChange_coordToFunc.finrank_eq` reduces to `finrank_coordinateRing_eq_two`.
- **Hypotheses**: Standard.
- **Uses from project**: `isBaseChange_coordToFunc`, `finrank_coordinateRing_eq_two`.
- **Used by**: `finrank_over_frobenius_image` (3 times); also used externally in `L6Witnesses.lean`, `GapSpines.lean`, `Basic.lean`, etc.
- **Visibility**: public
- **Lines**: 196–198 (3 lines)
- **Notes**: Key API — used by 3+ other declarations in this file and by many external files.

---

### `private noncomputable def frobFracRange`
- **Type**: `IntermediateField K W.toAffine.FunctionField`
- **What**: The intermediate field `K(x^q)` inside `K(E)`, defined as the image of `K(x) = FractionRing K[X]` under the Frobenius (concretely: `(Frob_K(x)).fieldRange` mapped into `K(E)` by the algebra map).
- **How**: Composition of `(frobeniusAlgHom K (FractionRing K[X])).fieldRange` with `IntermediateField.map` along `IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField`.
- **Hypotheses**: Standard.
- **Uses from project**: `frobeniusAlgHom`.
- **Used by**: `frobFracRange_le_frobRange`, `finrank_over_frobenius_image` (extensively).
- **Visibility**: private
- **Lines**: 203–205 (3 lines)
- **Notes**: Auxiliary intermediate field; not exposed publicly.

---

### `private theorem frobeniusAlgHom_comp_comm`
- **Type**: `(IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField).comp (frobeniusAlgHom K (FractionRing K[X])) = (frobeniusAlgHom K W.toAffine.FunctionField).comp (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField)`
- **What**: The Frobenius commutes with the algebra map `K(x) → K(E)`: `alg ∘ Frob_K(x) = Frob_K(E) ∘ alg`.
- **How**: Both sides map `a` to `(algebraMap a)^q`; proved by `AlgHom.ext` and `map_pow`.
- **Hypotheses**: `set_option maxHeartbeats 1600000`.
- **Uses from project**: `frobeniusAlgHom`.
- **Used by**: `frobFracRange_le_frobRange`, `finrank_over_frobenius_image` (h_intermediate sub-proof).
- **Visibility**: private
- **Lines**: 209–218 (9 lines, declared with `set_option maxHeartbeats 1600000`)
- **Notes**: `set_option maxHeartbeats 1600000` — NO justifying comment. The proof is conceptually trivial (`map_pow`) but synthesis is slow.

---

### `private theorem frobFracRange_le_frobRange`
- **Type**: `frobFracRange K W ≤ (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange`
- **What**: The intermediate field `K(x^q)` is contained in the full Frobenius image `K(E)^q`.
- **How**: Rewrites via `AlgHom.map_fieldRange` and `frobeniusAlgHom_comp_comm`, then does a straightforward membership argument.
- **Hypotheses**: Standard.
- **Uses from project**: `frobFracRange`, `frobeniusAlgHom_comp_comm`.
- **Used by**: `finrank_over_frobenius_image`.
- **Visibility**: private
- **Lines**: 223–234 (12 lines)
- **Notes**: None.

---

### `private theorem frobenius_fieldRange_ratFunc`
- **Type**: `(frobeniusAlgHom K (RatFunc K)).fieldRange = IntermediateField.adjoin K ({(RatFunc.X (K := K)) ^ Fintype.card K} : Set (RatFunc K))`
- **What**: The image of the Frobenius on `RatFunc K = K(X)` is exactly `K⟮X^q⟯`.
- **How**: Two-direction inclusion. Forward: write `g = p/r` and use `Polynomial.expand_card` + `Polynomial.expand_aeval` to show `g^q = (expand p)(X^q)/(expand r)(X^q) ∈ K⟮X^q⟯`. Backward: `X^q = Frob(X) ∈ fieldRange`.
- **Hypotheses**: Omits `[DecidableEq K]`. Uses `FiniteField.expand_card`.
- **Uses from project**: `frobeniusAlgHom`, `coe_frobeniusAlgHom`.
- **Used by**: `finrank_ratFunc_frobenius`.
- **Visibility**: private
- **Lines**: 240–282 (43 lines)
- **Notes**: **Proof >30 lines (43 lines).** Polynomial induction on `g.num` and `g.denom`; uses `Polynomial.aeval_mem_adjoin_singleton`.

---

### `private theorem finrank_ratFunc_frobenius`
- **Type**: `Module.finrank (frobeniusAlgHom K (RatFunc K)).fieldRange (RatFunc K) = Fintype.card K`
- **What**: The degree `[K(X) : K(X^q)] = q`, i.e., the Frobenius on rational functions has degree equal to the field cardinality.
- **How**: Rewrites `fieldRange` to `K⟮X^q⟯` via `frobenius_fieldRange_ratFunc`, then uses `RatFunc.finrank_eq_max_natDegree` and `Polynomial.natDegree_X_pow`.
- **Hypotheses**: Omits `[DecidableEq K]`.
- **Uses from project**: `frobenius_fieldRange_ratFunc`.
- **Used by**: `finrank_over_frobenius_image`.
- **Visibility**: private
- **Lines**: 288–299 (12 lines)
- **Notes**: None.

---

### `private theorem finrank_over_frobenius_image`
- **Type**: `Module.finrank (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange W.toAffine.FunctionField = Fintype.card K`
- **What**: The field extension degree `[K(E) : K(E)^q] = q`, the core fact needed for the degree of the Frobenius isogeny.
- **How**: Tower-law argument with three sub-computations:
  1. `h_total`: `[K(E) : K(x^q)] = 2 * q` via double application of the tower law through `frobFracRange ≤ algebraMap.fieldRange`, using `finrank_functionField_eq_two` (for `[K(E):K(x)]=2`) and `finrank_ratFunc_frobenius` (for `[K(x):K(x^q)]=q`) transferred via `Algebra.finrank_eq_of_equiv_equiv`.
  2. `h_intermediate`: `[K(E)^q : K(x^q)] = 2` via `finrank_functionField_eq_two` transferred through `frobeniusRangeEquiv` + `frobeniusAlgHom_comp_comm`.
  3. Combined via `Module.finrank_mul_finrank` and `linarith`.
- **Hypotheses**: `set_option backward.isDefEq.respectTransparency false` and `set_option maxHeartbeats 800000`. Uses all preceding private declarations.
- **Uses from project**: `frobFracRange_le_frobRange`, `frobFracRange`, `frobeniusRangeEquiv`, `finrank_functionField_eq_two`, `finrank_ratFunc_frobenius`, `frobeniusAlgHom_comp_comm`.
- **Used by**: `frobenius_finrank_functionField`.
- **Visibility**: private
- **Lines**: 308–460 (153 lines)
- **Notes**: **Proof >30 lines (153 lines).** `set_option backward.isDefEq.respectTransparency false` (line 305) — NO justifying comment. `set_option maxHeartbeats 800000` (line 307) — NO justifying comment. Three nested `have` sub-lemmas; extensive use of `Algebra.finrank_eq_of_equiv_equiv` to transfer finranks across ring equivalences.

---

### `theorem frobenius_finrank_functionField`
- **Type**: `@Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _ (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.toAlgebra.toModule = Fintype.card K`
- **What**: The finrank of `K(E)` over itself via the Frobenius twisted algebra structure equals `q = #K`; this is the clean public statement of `[K(E) : K(E)^q] = q`.
- **How**: `frobenius_finrank_eq_fieldRange_finrank` (to untwist the module to a genuine field extension) followed by `finrank_over_frobenius_image`.
- **Hypotheses**: Standard.
- **Uses from project**: `frobenius_finrank_eq_fieldRange_finrank`, `finrank_over_frobenius_image`.
- **Used by**: `frobeniusIsogeny_degree`; also used externally by `Frobenius.lean` and `IsogenyAG.lean`.
- **Visibility**: public
- **Lines**: 470–475 (6 lines)
- **Notes**: Key API externally referenced.

---

### `theorem frobeniusIsogeny_degree`
- **Type**: `(frobeniusIsogeny K W).degree = Fintype.card K`
- **What**: The Frobenius isogeny has degree `q = #K` (reference: Silverman III.4.6 + II.2.11(a)).
- **How**: Unfolds `PullbackIsogeny.degree` to the Frobenius-twisted finrank, then applies `frobenius_finrank_functionField`.
- **Hypotheses**: Standard.
- **Uses from project**: `frobeniusIsogeny`, `frobenius_finrank_functionField`.
- **Used by**: unused in this file (main advertised result; used by importers).
- **Visibility**: public
- **Lines**: 484–488 (5 lines)
- **Notes**: The main theorem of the file.

---

### `theorem frobeniusIsogeny_pow_mem_fieldRange`
- **Type**: `∀ x : W.toAffine.FunctionField, ∃ n : ℕ, x ^ (Nat.minFac (Fintype.card K)) ^ n ∈ (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange`
- **What**: Every element `x ∈ K(E)` has some power lying in the Frobenius image `K(E)^q`; specifically `x^(p^n) ∈ K(E)^q` where `p = char K` and `q = p^n`. This is the power-membership form of Silverman II.2.11(b) (pure inseparability).
- **How**: `FiniteField.card'` gives `q = p^m`; `Nat.Prime.pow_minFac` shows `Nat.minFac q = p`; take `n = m` and witness `x^(p^m) = x^q = Frob(x) ∈ fieldRange` via `coe_frobeniusAlgHom`.
- **Hypotheses**: Standard finite-field hypotheses; `x : W.toAffine.FunctionField`.
- **Uses from project**: `frobeniusAlgHom`, `coe_frobeniusAlgHom`.
- **Used by**: unused in this file (referenced in doc-comment of `Verschiebung/FieldTower.lean`).
- **Visibility**: public
- **Lines**: 506–517 (12 lines)
- **Notes**: Sidesteps `IsPurelyInseparable` typeclass issues; only weakly referenced externally (mention in comments).

---

### `theorem frobeniusIsogeny_pullback_range`
- **Type**: `Set.range (frobeniusIsogeny K W).pullback = Set.range ((· ^ Fintype.card K) : W.toAffine.FunctionField → W.toAffine.FunctionField)`
- **What**: The image of the Frobenius isogeny's pullback is exactly the set of `q`-th powers in `K(E)`.
- **How**: Direct `rintro`/`exact` using `frobeniusIsogeny_pullback_apply`.
- **Hypotheses**: Standard.
- **Uses from project**: `frobeniusIsogeny`, `frobeniusIsogeny_pullback_apply`.
- **Used by**: unused in this file.
- **Visibility**: public
- **Lines**: 527–537 (11 lines)
- **Notes**: Appears to be unused externally as well (no grep hits outside this file).

---

## Summary statistics

| Category | Count |
|---|---|
| Total declarations | 26 |
| defs (noncomputable) | 3 |
| Lemmas/theorems | 13 |
| Instances | 10 |
| Sorries (in body) | 0 |
| Long proofs (>30 lines) | 2: `frobenius_fieldRange_ratFunc` (43 lines), `finrank_over_frobenius_image` (153 lines) |

## set_option heartbeats

| Location | Value | Comment |
|---|---|---|
| Line 144 (before FaithfulSMul instance) | `synthInstance.maxHeartbeats 40000` | NO-COMMENT |
| Line 209 (before `frobeniusAlgHom_comp_comm`) | `maxHeartbeats 1600000` | NO-COMMENT |
| Lines 305–307 (before `finrank_over_frobenius_image`) | `backward.isDefEq.respectTransparency false` + `maxHeartbeats 800000` | NO-COMMENT |

## Key API (used by 3+ declarations in this file)

- `finrank_functionField_eq_two`: used in `finrank_over_frobenius_image` (3 times: `h_top`, `h_mid` sub-proof, `h_intermediate`)
- `frobFracRange`: used in `frobFracRange_le_frobRange`, `finrank_over_frobenius_image` (multiple sub-goals)
- `frobeniusRangeEquiv`: used in `frobenius_finrank_eq_fieldRange_finrank`, `finrank_over_frobenius_image`

## Unused in file (dead-code candidates)

- `frobeniusIsogeny_degree`: advertised main result, not called within file
- `frobeniusIsogeny_pow_mem_fieldRange`: not called within file
- `frobeniusIsogeny_pullback_range`: not called within file (and appears not used externally)

## Notes

The file proves `[K(E):K(E)^q]=q` (degree of Frobenius) by a careful tower-law argument through the intermediate field `K(x^q)`, using `Algebra.finrank_eq_of_equiv_equiv` to transfer finranks across ring equivalences — a pattern that `Basic.lean` copies for `mulByInt`. The 153-line central proof `finrank_over_frobenius_image` is the most complex, requiring three nested sub-computations and two `set_option` overrides with no justifying comments. No sorries anywhere in the file.
