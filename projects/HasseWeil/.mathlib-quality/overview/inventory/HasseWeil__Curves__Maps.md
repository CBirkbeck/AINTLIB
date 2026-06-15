# Inventory: ./HasseWeil/Curves/Maps.lean

**File purpose**: T-II-2-016 (Silverman II.2.12 specialised to `[p]`): constructs the relative
p-Frobenius isogeny `F_{E/k} : E → E^{(p)}` in all technical layers (coefficient twist, coordinate
ring homomorphism, function-field pullback, point map, packaged Isogeny structure, purely-inseparable
membership lemmas), and lays out stub theorems for the `[p] = ψ ∘ F` factorisation.

**Imports**: `HasseWeil.Basic`, `HasseWeil.EC.IsogenyKernel`, `Mathlib.Algebra.CharP.Lemmas`

**Total declarations**: 33

---

## Declarations

### `noncomputable def WeierstrassCurve.frobeniusTwist`
- **Type**: `(E : WeierstrassCurve k) → WeierstrassCurve k` (takes `p` implicit via `[ExpChar k p]`)
- **What**: Defines the Frobenius twist `E^{(p)}` by applying the `p`-th power Frobenius ring hom to the coefficients of the Weierstrass equation; equivalently `E.map (frobenius k p)`.
- **How**: One-liner: `E.map (frobenius k p)`. `@[simps!]` unfolds coefficient projections automatically.
- **Hypotheses**: `[CommRing k]`, `[ExpChar k p]`.
- **Uses from project**: none (only Mathlib's `frobenius`).
- **Used by**: nearly every subsequent declaration in the file (used 62 times total).
- **Visibility**: public (lives in `_root_`).
- **Lines**: 69–72, proof/body 1 line.
- **Notes**: Key API entry point; `@[simps!]` attribute.

---

### `noncomputable def WeierstrassCurve.iterateFrobeniusTwist`
- **Type**: `(E : WeierstrassCurve k) → (e : ℕ) → WeierstrassCurve k`
- **What**: Defines the iterated Frobenius twist `E^{(p^e)}` as `E.map (iterateFrobenius k p e)`.
- **How**: Direct: `E.map (iterateFrobenius k p e)`.
- **Hypotheses**: `[CommRing k]`, `[ExpChar k p]`.
- **Uses from project**: none.
- **Used by**: unused in file (count = 1, which is the definition line itself; referenced only in a docstring comment mentioning `frobeniusIsog_relative_iterate`).
- **Visibility**: public (lives in `_root_`).
- **Lines**: 77–79, body 1 line.
- **Notes**: Declared but not referenced by any other declaration within this file (dead-code candidate for this file; intended for a downstream `frobeniusIsog_relative_iterate` not yet defined here). `@[simps!]` attribute.

---

### `instance instExpChar_FunctionField`
- **Type**: `ExpChar KE p` where `KE = E.toAffine.FunctionField`
- **What**: Propagates the `ExpChar k p` typeclass from the base field `k` to the function field `K(E)` via the injective algebraMap.
- **How**: `expChar_of_injective_algebraMap` applied to the injection `k → K(E)`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: none directly (uses Mathlib's `expChar_of_injective_algebraMap`).
- **Used by**: implicitly by subsequent declarations that need `ExpChar KE p` (used by type inference); explicit name referenced only at its definition line.
- **Visibility**: public (unnamed instance).
- **Lines**: 102–104, body 1 line.
- **Notes**: Enables Frobenius and related machinery on `K(E)`.

---

### `theorem frobeniusTwist_baseChange_KE_eq_W_KE_map_frobenius`
- **Type**: `(E.frobeniusTwist p).map (algebraMap k KE) = (W_KE E).map (frobenius KE p)`
- **What**: Shows that base-changing the Frobenius twist `E^{(p)}` to `K(E)` equals applying the absolute Frobenius of `K(E)` to the coefficients of `W_KE E`. This is the key commutativity of algebraMap with Frobenius.
- **How**: `WeierstrassCurve.map_map` twice plus `RingHom.frobenius_comm (algebraMap k KE) p` (algebraMap commutes with Frobenius on a characteristic-p ring).
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `WeierstrassCurve.frobeniusTwist` (def), `W_KE`.
- **Used by**: `frobeniusTwist_generic_equation`.
- **Visibility**: public.
- **Lines**: 109–114, proof 4 lines.
- **Notes**: None.

---

### `theorem frobeniusTwist_generic_equation`
- **Type**: `((E.frobeniusTwist p).map (algebraMap k KE)).toAffine.Equation (x_gen E ^ p) (y_gen E ^ p)`
- **What**: The Weierstrass equation of `E^{(p)}` (base-changed to `K(E)`) is satisfied by the p-th-power images `(x_gen^p, y_gen^p)` of the generic point.
- **How**: Applies `Affine.Equation.map` with `frobenius KE p` to the known `generic_equation E`, then rewrites via `frobeniusTwist_baseChange_KE_eq_W_KE_map_frobenius`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusTwist_baseChange_KE_eq_W_KE_map_frobenius`, `generic_equation`.
- **Used by**: `frobeniusTwist_polynomial_eval₂_zero`.
- **Visibility**: public.
- **Lines**: 120–127, proof 6 lines.
- **Notes**: None.

---

### `noncomputable def frobeniusRelativeBaseHom`
- **Type**: `Polynomial k →+* KE`, sending `X ↦ x_gen E ^ p`
- **What**: The base ring hom `Polynomial k → K(E)` that evaluates polynomials at `x_gen^p`; serves as the coefficient piece for constructing the coord-ring hom via `AdjoinRoot.lift`.
- **How**: `Polynomial.eval₂RingHom (algebraMap k KE) (x_gen E ^ p)`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `x_gen` (via `KE`).
- **Used by**: `frobeniusTwist_polynomial_eval₂_zero`, `frobeniusRelativeCoordRingHom`, `frobeniusRelativeCoordAlgHom` (commutes'), `frobeniusRelativeCoordAlgHom_x`, `frobeniusRelativeCoordAlgHom_y`, `frobeniusRelativeBaseHom_injective`, `frobeniusRelativeCoordRingHom_injective` (×several times).
- **Visibility**: public.
- **Lines**: 136–137, body 1 line.
- **Notes**: Referenced 22 times in file; central low-level ingredient.

---

### `theorem frobeniusTwist_polynomial_eval₂_zero`
- **Type**: `(E.frobeniusTwist p).toAffine.polynomial.eval₂ (frobeniusRelativeBaseHom p E) (y_gen E ^ p) = 0`
- **What**: The Weierstrass polynomial of `E^{(p)}` evaluates to zero when X is specialised to `x_gen^p` and Y to `y_gen^p`; this is the `eval₂ = 0` witness needed to apply `AdjoinRoot.lift`.
- **How**: Rewrites via `Polynomial.eval₂_eval₂RingHom_apply` and `Affine.map_polynomial`, then applies `frobeniusTwist_generic_equation`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeBaseHom`, `frobeniusTwist_generic_equation`.
- **Used by**: `frobeniusRelativeCoordRingHom`, `frobeniusRelativeCoordAlgHom_x`, `frobeniusRelativeCoordAlgHom_y`.
- **Visibility**: public.
- **Lines**: 141–146, proof 4 lines.
- **Notes**: None.

---

### `noncomputable def frobeniusRelativeCoordRingHom`
- **Type**: `(E.frobeniusTwist p).toAffine.CoordinateRing →+* KE`
- **What**: The relative Frobenius pullback as a ring hom on the coordinate ring, sending `X ↦ x_gen^p` and `Y (root) ↦ y_gen^p`; constructed via `AdjoinRoot.lift`.
- **How**: `AdjoinRoot.lift (frobeniusRelativeBaseHom p E) (y_gen E ^ p) (frobeniusTwist_polynomial_eval₂_zero p E)`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeBaseHom`, `frobeniusTwist_polynomial_eval₂_zero`.
- **Used by**: `frobeniusRelativeCoordAlgHom`, `frobeniusRelativeCoordRingHom_injective`, `frobeniusRelativeCoordRingHom_comp_map`, `frobeniusRelative_compose_eq_pow`, `algebraMap_CR_KE_pow_p_mem_fieldRange`.
- **Visibility**: public.
- **Lines**: 152–155, body 2 lines.
- **Notes**: Referenced 24 times in file; major structural piece.

---

### `noncomputable def frobeniusRelativeCoordAlgHom`
- **Type**: `(E.frobeniusTwist p).toAffine.CoordinateRing →ₐ[k] KE`
- **What**: Upgrades `frobeniusRelativeCoordRingHom` to a k-AlgHom by verifying that it commutes with the k-algebra structure (`algebraMap k → CoordinateRing → KE`).
- **How**: Sets `toRingHom := frobeniusRelativeCoordRingHom p E`; proves `commutes'` by unfolding through `AdjoinRoot.lift_mk` and `Polynomial.eval₂_C`, using `simp [frobeniusRelativeBaseHom, Polynomial.eval₂_C]`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordRingHom`, `frobeniusRelativeBaseHom`.
- **Used by**: `frobeniusRelativeCoordAlgHom_x`, `frobeniusRelativeCoordAlgHom_y`, `frobeniusRelativeCoordAlgHom_injective`.
- **Visibility**: public.
- **Lines**: 160–172, proof/commutes' 10 lines.
- **Notes**: None.

---

### `theorem frobeniusRelativeCoordAlgHom_x`
- **Type**: `frobeniusRelativeCoordAlgHom p E (algebraMap (Polynomial k) (E.frobeniusTwist p).toAffine.CoordinateRing Polynomial.X) = x_gen E ^ p`
- **What**: The AlgHom sends the X-coordinate generator of `CoordinateRing(E^{(p)})` to `x_gen^p`.
- **How**: Unfolds to an `AdjoinRoot.lift_mk` computation with `Polynomial.eval₂_X` via `simp [frobeniusRelativeBaseHom]`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordAlgHom`, `frobeniusRelativeBaseHom`, `frobeniusTwist_polynomial_eval₂_zero`.
- **Used by**: `frobeniusIsog_relative_pullback_x_gen`.
- **Visibility**: public.
- **Lines**: 176–185, proof 8 lines.
- **Notes**: Referenced 3 times (definition + 2 callers).

---

### `theorem frobeniusRelativeCoordAlgHom_y`
- **Type**: `frobeniusRelativeCoordAlgHom p E (AdjoinRoot.root (E.frobeniusTwist p).toAffine.polynomial) = y_gen E ^ p`
- **What**: The AlgHom sends the Y-coordinate generator (AdjoinRoot.root) of `CoordinateRing(E^{(p)})` to `y_gen^p`.
- **How**: Exactly `AdjoinRoot.lift_root`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordAlgHom`, `frobeniusTwist_polynomial_eval₂_zero`.
- **Used by**: `frobeniusIsog_relative_pullback_y_gen`, `frobeniusRelativeCoordRingHom_comp_map`.
- **Visibility**: public.
- **Lines**: 190–197, proof 6 lines.
- **Notes**: Referenced 4 times.

---

### `lemma x_gen_pow_p_transcendental`
- **Type**: `Transcendental k (x_gen E ^ p)`
- **What**: Shows `x_gen^p` is transcendental over `k`; key for injectivity of the base polynomial hom.
- **How**: `(x_gen_transcendental E).pow (expChar_pos k p)` — transcendental raised to a positive power is transcendental.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `x_gen_transcendental` (from `HasseWeil.Basic`).
- **Used by**: `frobeniusRelativeBaseHom_injective`.
- **Visibility**: public.
- **Lines**: 210–211, proof 1 line.
- **Notes**: Referenced only twice (definition + one caller); could be inlined.

---

### `lemma frobeniusRelativeBaseHom_injective`
- **Type**: `Function.Injective (frobeniusRelativeBaseHom p E)`
- **What**: The polynomial ring hom `Polynomial k → K(E)` evaluating at `x_gen^p` is injective, because `x_gen^p` is transcendental over `k`.
- **How**: Shows `frobeniusRelativeBaseHom` equals `(Polynomial.aeval (x_gen E ^ p)).toRingHom`, then applies `transcendental_iff_injective.mp` (Mathlib) to `x_gen_pow_p_transcendental`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeBaseHom`, `x_gen_pow_p_transcendental`.
- **Used by**: `frobeniusRelativeCoordRingHom_injective` (×2 uses inside proof).
- **Visibility**: public.
- **Lines**: 216–222, proof 5 lines.
- **Notes**: Referenced 3 times total.

---

### `theorem frobeniusRelativeCoordRingHom_injective`
- **Type**: `Function.Injective (frobeniusRelativeCoordRingHom p E)`
- **What**: The coord-ring ring hom `CoordinateRing(E^{(p)}) → K(E)` is injective. This is the key injectivity needed to extend to the function field.
- **How**: Follows the same pattern as `mulByInt_coordHom_injective`: for any `r` with image 0, decompose `r = a•1 + b•Y` via `Affine.CoordinateRing.exists_smul_basis_eq`, express the image as `baseHom(a) + baseHom(b)·y_gen^p`, then split on `b=0` (use `frobeniusRelativeBaseHom_injective`) or `b≠0` (derive contradiction via `Affine.CoordinateRing.degree_norm_smul_basis` showing the norm has degree ≥ 3, so cannot be zero unless `b=0`).
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordRingHom`, `frobeniusRelativeBaseHom`, `frobeniusRelativeBaseHom_injective`.
- **Used by**: `frobeniusRelativeCoordAlgHom_injective`.
- **Visibility**: public.
- **Lines**: 234–313, **proof 79 lines**.
- **Notes**: Longest proof in file (79 lines). Uses `Affine.CoordinateRing.degree_norm_smul_basis` from `HasseWeil.Basic` (Mathlib pattern). Proof is mechanically correct but verbose; could potentially be shortened.

---

### `lemma frobeniusRelativeCoordAlgHom_injective`
- **Type**: `Function.Injective (frobeniusRelativeCoordAlgHom p E)`
- **What**: The coord-ring AlgHom version of injectivity; trivially derived from the ring-hom injectivity.
- **How**: Direct: `frobeniusRelativeCoordRingHom_injective p E`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordRingHom_injective`.
- **Used by**: `frobeniusRelativePullback`.
- **Visibility**: public.
- **Lines**: 317–319, proof 1 line.
- **Notes**: Thin wrapper; exists to expose AlgHom form for `IsFractionRing.liftAlgHom`.

---

### `noncomputable def frobeniusRelativePullback`
- **Type**: `(E.frobeniusTwist p).toAffine.FunctionField →ₐ[k] KE`
- **What**: Extends `frobeniusRelativeCoordAlgHom` to the function fields via `IsFractionRing.liftAlgHom`; this is the pullback of the relative Frobenius isogeny `F : E → E^{(p)}` at the function-field level, sending `x_gen ↦ x_gen^p`, `y_gen ↦ y_gen^p`.
- **How**: `IsFractionRing.liftAlgHom (frobeniusRelativeCoordAlgHom_injective p E)`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordAlgHom_injective`.
- **Used by**: `frobeniusIsog_relative` (pullback field), `frobeniusIsog_relative_pullback_x_gen`, `frobeniusIsog_relative_pullback_y_gen`, `algebraMap_CR_KE_pow_p_mem_fieldRange`.
- **Visibility**: public.
- **Lines**: 330–332, body 1 line.
- **Notes**: Referenced 12 times; key structural object.

---

### `noncomputable def frobeniusRelativePointFun`
- **Type**: `E.toAffine.Point → (E.frobeniusTwist p).toAffine.Point`
- **What**: The point-level map of the relative Frobenius: sends `zero ↦ zero` and `(x, y) ↦ (x^p, y^p)` with nonsingularity inherited via `Affine.map_nonsingular`.
- **How**: Pattern match; the `.some` case uses `(WeierstrassCurve.Affine.map_nonsingular ... (RingHom.injective (frobenius k p))).mpr h`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusTwist` (codomain).
- **Used by**: `frobeniusRelativePointFun_add`, `frobeniusRelativePointMap`.
- **Visibility**: public.
- **Lines**: 342–347, body 4 lines.
- **Notes**: Referenced 10 times in file.

---

### `theorem frobeniusRelativePointFun_add`
- **Type**: `∀ P₁ P₂ : E.toAffine.Point, frobeniusRelativePointFun p E (P₁ + P₂) = frobeniusRelativePointFun p E P₁ + frobeniusRelativePointFun p E P₂`
- **What**: The function `frobeniusRelativePointFun` is a group hom; i.e., the relative Frobenius preserves the elliptic curve group law.
- **How**: Case analysis on both points; the negation case uses `Affine.Point.add_of_Y_eq` plus `Affine.map_negY`; the generic case uses `simpa` with `Affine.Point.add_some`, `Affine.map_addX`, `Affine.map_addY`, `Affine.map_slope`, `Affine.map_negY` (Mathlib map lemmas for the group law), relying on `RingHom.injective (frobenius k p)` to pull back the non-degeneracy condition.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativePointFun`.
- **Used by**: `frobeniusRelativePointMap` (map_add').
- **Visibility**: public.
- **Lines**: 353–379, **proof 26 lines**.
- **Notes**: Proof is 26 lines; just below the 30-line threshold. Pattern parallel to Mathlib's `Affine.Point.map.map_add'`.

---

### `noncomputable def frobeniusRelativePointMap`
- **Type**: `E.toAffine.Point →+ (E.frobeniusTwist p).toAffine.Point`
- **What**: Packages `frobeniusRelativePointFun` as an `AddMonoidHom`, supplying `map_zero' := rfl` and `map_add' := frobeniusRelativePointFun_add`.
- **How**: Record literal.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativePointFun`, `frobeniusRelativePointFun_add`.
- **Used by**: `frobeniusIsog_relative` (toAddMonoidHom field).
- **Visibility**: public.
- **Lines**: 382–386, body 4 lines.
- **Notes**: None.

---

### `instance : (E.frobeniusTwist p).toAffine.IsElliptic`
- **Type**: `(E.frobeniusTwist p).toAffine.IsElliptic`
- **What**: States that the Frobenius twist of an elliptic curve is itself elliptic; derived from Mathlib's `(W.map f).IsElliptic` instance.
- **How**: `show (E.map (frobenius k p)).IsElliptic from inferInstance`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusTwist` (unfolds to `E.map (frobenius k p)`).
- **Used by**: `frobeniusIsog_relative` (for IsElliptic synthesis on codomain), `frobeniusTwist_isElliptic`.
- **Visibility**: public (anonymous instance).
- **Lines**: 397–398, body 1 line.
- **Notes**: Unnamed instance.

---

### `theorem WeierstrassCurve.frobeniusTwist_isElliptic`
- **Type**: `(E.frobeniusTwist p).toAffine.IsElliptic`
- **What**: Explicit named theorem version of the `IsElliptic` instance above, for ticket-tracking purposes (T07 of R27).
- **How**: `inferInstance` (delegates to the unnamed instance).
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusTwist`.
- **Used by**: unused in file (count = 1, the definition itself).
- **Visibility**: public (lives in `_root_`).
- **Lines**: 407–408, body 1 line.
- **Notes**: Only purpose is as a named alias for ticket T07/R27; dead-code candidate in this file.

---

### `noncomputable def frobeniusIsog_relative`
- **Type**: `Isogeny E.toAffine (E.frobeniusTwist p).toAffine`
- **What**: The full relative Frobenius isogeny `F_{E/k} : E → E^{(p)}` packaged as an `Isogeny` structure, combining the function-field pullback and the point-level AddMonoidHom.
- **How**: Record literal with `pullback := frobeniusRelativePullback p E` and `toAddMonoidHom := frobeniusRelativePointMap p E`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativePullback`, `frobeniusRelativePointMap`.
- **Used by**: `frobeniusIsog_relative_pullback_x_gen`, `frobeniusIsog_relative_pullback_y_gen`, `frobeniusIsog_relative_apply_some`, `frobeniusIsog_relative_apply_zero`, `x_gen_pow_p_mem_fieldRange`, `y_gen_pow_p_mem_fieldRange`, `algebraMap_k_mem_fieldRange`, `algebraMap_CR_KE_pow_p_mem_fieldRange`, `frobeniusIsog_relative_pow_p_mem_fieldRange`, `Conditional` theorems.
- **Visibility**: public.
- **Lines**: 415–418, body 3 lines.
- **Notes**: Referenced 32 times; the main deliverable of the file.

---

### `theorem frobeniusIsog_relative_pullback_x_gen`
- **Type**: `(frobeniusIsog_relative p E).pullback (x_gen (E.frobeniusTwist p)) = x_gen E ^ p`
- **What**: The relative Frobenius pullback sends `x_gen(E^{(p)})` to `(x_gen E)^p`.
- **How**: Unfolds `frobeniusRelativePullback`, applies `IsFractionRing.liftAlgHom_apply` + `IsFractionRing.lift_algebraMap`, then closes with `frobeniusRelativeCoordAlgHom_x`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`, `frobeniusRelativePullback`, `frobeniusRelativeCoordAlgHom_x`.
- **Used by**: `x_gen_pow_p_mem_fieldRange`.
- **Visibility**: public.
- **Lines**: 428–436, proof 7 lines.
- **Notes**: Referenced 3 times total (definition + 2 callers).

---

### `theorem frobeniusIsog_relative_pullback_y_gen`
- **Type**: `(frobeniusIsog_relative p E).pullback (y_gen (E.frobeniusTwist p)) = y_gen E ^ p`
- **What**: The relative Frobenius pullback sends `y_gen(E^{(p)})` to `(y_gen E)^p`.
- **How**: Analogous to `frobeniusIsog_relative_pullback_x_gen`, using `frobeniusRelativeCoordAlgHom_y`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`, `frobeniusRelativePullback`, `frobeniusRelativeCoordAlgHom_y`.
- **Used by**: `y_gen_pow_p_mem_fieldRange`.
- **Visibility**: public.
- **Lines**: 440–448, proof 7 lines.
- **Notes**: Referenced 3 times total.

---

### `theorem frobeniusIsog_relative_apply_some`
- **Type**: `(frobeniusIsog_relative p E).toAddMonoidHom (.some x y h) = .some ((frobenius k p) x) ((frobenius k p) y) (...)`
- **What**: Evaluation of the relative Frobenius point map on an affine point: sends `(x,y)` to `(x^p, y^p)`.
- **How**: `rfl` — definitionally true by construction of `frobeniusRelativePointFun`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`, `h : E.toAffine.Nonsingular x y`.
- **Uses from project**: `frobeniusIsog_relative`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 451–457, proof 1 line (`rfl`).
- **Notes**: Dead-code candidate in this file (referenced only at definition).

---

### `@[simp] theorem frobeniusIsog_relative_apply_zero`
- **Type**: `(frobeniusIsog_relative p E).toAddMonoidHom 0 = 0`
- **What**: The relative Frobenius point map sends the identity point to the identity.
- **How**: `rfl`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`.
- **Used by**: unused in file.
- **Visibility**: public (`@[simp]`).
- **Lines**: 460–461, proof 1 line.
- **Notes**: Dead-code candidate in this file; `@[simp]` makes it available globally.

---

### `theorem x_gen_pow_p_mem_fieldRange`
- **Type**: `x_gen E ^ p ∈ (frobeniusIsog_relative p E).pullback.fieldRange`
- **What**: `x_gen^p` lies in the image of `(frobeniusIsog_relative p E).pullback`; part of the purely-inseparable membership package.
- **How**: Explicit witness: `⟨x_gen (E.frobeniusTwist p), frobeniusIsog_relative_pullback_x_gen p E⟩`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`, `frobeniusIsog_relative_pullback_x_gen`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 471–473, proof 1 line.
- **Notes**: Dead-code candidate in this file.

---

### `theorem y_gen_pow_p_mem_fieldRange`
- **Type**: `y_gen E ^ p ∈ (frobeniusIsog_relative p E).pullback.fieldRange`
- **What**: `y_gen^p` lies in the image of `(frobeniusIsog_relative p E).pullback`.
- **How**: Explicit witness via `frobeniusIsog_relative_pullback_y_gen`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`, `frobeniusIsog_relative_pullback_y_gen`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 477–479, proof 1 line.
- **Notes**: Dead-code candidate in this file.

---

### `theorem algebraMap_k_mem_fieldRange`
- **Type**: `∀ c : k, algebraMap k KE c ∈ (frobeniusIsog_relative p E).pullback.fieldRange`
- **What**: Constants from the base field `k` (mapped to `K(E)`) lie in the pullback image field range; this follows from the k-AlgHom property.
- **How**: `⟨algebraMap k _ c, AlgHom.commutes _ c⟩`.
- **Hypotheses**: `[Field k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 483–485, proof 1 line.
- **Notes**: Dead-code candidate in this file.

---

### `lemma algebraMap_CR_KE_of_eq_eval₂`
- **Type**: `algebraMap E.toAffine.CoordinateRing KE (AdjoinRoot.of E.toAffine.polynomial q) = q.eval₂ (algebraMap k KE) (x_gen E)`
- **What**: The natural algebra map from `CoordinateRing(E)` to `K(E)`, applied to elements of `Polynomial k` (embedded via `AdjoinRoot.of`), equals polynomial evaluation at `x_gen E`.
- **How**: Polynomial induction via `Polynomial.induction_on'`: handles `+` by `map_add`+`eval₂_add`, and monomials `c·X^n` using `map_mul`, `map_pow`, `eval₂_C`, `eval₂_X_pow`, and the `IsScalarTower` identification that `algebraMap Polynomial.X` maps to `x_gen`.
- **Hypotheses**: `[Field k]`, `[DecidableEq k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `x_gen` (from `HasseWeil.Basic`).
- **Used by**: `frobeniusRelativeCoordRingHom_comp_map`.
- **Visibility**: public.
- **Lines**: 503–518, proof 14 lines.
- **Notes**: Referenced twice in file (definition + one caller).

---

### `theorem frobeniusRelativeCoordRingHom_comp_map`
- **Type**: `(frobeniusRelativeCoordRingHom p E).comp (Affine.CoordinateRing.map E.toAffine (frobenius k p)) = (frobenius KE p).comp (algebraMap E.toAffine.CoordinateRing KE)`
- **What**: Compositional identity at the coordinate ring level: the relative Frobenius pullback, composed with the coordinate-ring map under `frobenius k p`, equals the absolute Frobenius `(·^p)` on the algebraMap image. This is the key purely-inseparable algebraic identity.
- **How**: `AdjoinRoot.ringHom_ext` reduces to two goals: (a) on `AdjoinRoot.of q` for polynomials, using `Polynomial.eval₂_map`, `RingHom.frobenius_comm`, `Polynomial.hom_eval₂`, and `algebraMap_CR_KE_of_eq_eval₂`; (b) on the root (`y_gen`), using `AdjoinRoot.lift_root` and `frobeniusRelativeCoordAlgHom_y`.
- **Hypotheses**: `[Field k]`, `[DecidableEq k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordRingHom`, `frobeniusRelativeCoordAlgHom_y`, `algebraMap_CR_KE_of_eq_eval₂`.
- **Used by**: `frobeniusRelative_compose_eq_pow`.
- **Visibility**: public.
- **Lines**: 523–572, **proof 49 lines**.
- **Notes**: Proof 49 lines. Uses `RingHom.frobenius_comm` as key Mathlib lemma.

---

### `theorem frobeniusRelative_compose_eq_pow`
- **Type**: `∀ r : E.toAffine.CoordinateRing, frobeniusRelativeCoordRingHom p E (Affine.CoordinateRing.map E.toAffine (frobenius k p) r) = (algebraMap E.toAffine.CoordinateRing KE r) ^ p`
- **What**: Pointwise form of the compositional identity: the relative Frobenius pullback of the Frobenius-mapped coordinate element equals the `p`-th power of its image in `K(E)`.
- **How**: `RingHom.congr_fun (frobeniusRelativeCoordRingHom_comp_map p E) r`.
- **Hypotheses**: `[Field k]`, `[DecidableEq k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusRelativeCoordRingHom`, `frobeniusRelativeCoordRingHom_comp_map`.
- **Used by**: `algebraMap_CR_KE_pow_p_mem_fieldRange`.
- **Visibility**: public.
- **Lines**: 577–581, proof 1 line.
- **Notes**: None.

---

### `theorem algebraMap_CR_KE_pow_p_mem_fieldRange`
- **Type**: `∀ r : E.toAffine.CoordinateRing, (algebraMap E.toAffine.CoordinateRing KE r) ^ p ∈ (frobeniusIsog_relative p E).pullback.fieldRange`
- **What**: The `p`-th power of any algebraMap-image from `CoordinateRing(E)` lies in the pullback image field range; the coordinate-ring piece of the purely-inseparable membership statement.
- **How**: Provides explicit preimage `algebraMap CR(E^{(p)}) FF(E^{(p)}) (CoordRingMap (frobenius k p) r)`, then uses `IsFractionRing.liftAlgHom_apply` + `IsFractionRing.lift_algebraMap` + `frobeniusRelative_compose_eq_pow`.
- **Hypotheses**: `[Field k]`, `[DecidableEq k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`, `frobeniusRelativePullback`, `frobeniusRelativeCoordRingHom`, `frobeniusRelative_compose_eq_pow`.
- **Used by**: `frobeniusIsog_relative_pow_p_mem_fieldRange` (×2).
- **Visibility**: public.
- **Lines**: 597–607, proof 9 lines.
- **Notes**: Referenced 3 times total.

---

### `theorem frobeniusIsog_relative_pow_p_mem_fieldRange`
- **Type**: `∀ f : KE, f ^ p ∈ (frobeniusIsog_relative p E).pullback.fieldRange`
- **What**: Every element of `K(E)` has its p-th power in the pullback image of the relative Frobenius; the purely-inseparable membership statement for the full function field.
- **How**: Uses `IsFractionRing.div_surjective` to write `f = algMap(a) / algMap(b)`, applies `div_pow`, then `IntermediateField.div_mem` with `algebraMap_CR_KE_pow_p_mem_fieldRange` for numerator and denominator.
- **Hypotheses**: `[Field k]`, `[DecidableEq k]`, `[ExpChar k p]`, `E.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog_relative`, `algebraMap_CR_KE_pow_p_mem_fieldRange`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 613–620, proof 7 lines.
- **Notes**: The main T-II-2-016b deliverable; referenced only at its definition within the file.

---

### `theorem Conditional.mulByNat_p_factors_through_frobenius_of_silvermanII212`
- **Type**: Given `h_factor : ∃ ψ : Isogeny (E.frobeniusTwist p).toAffine E.toAffine, ψ.IsSeparable ∧ ψ.comp (frobeniusIsog_relative p E) = mulByInt E.toAffine (p : ℤ)`, concludes the same.
- **What**: Conditional placeholder for Silverman II.2.12 specialised to `[p]`: given a separable factor ψ such that `ψ ∘ F_{E/k} = [p]`, packages this as the named result. The theorem body is the identity `h_factor`.
- **How**: `h_factor` (identity).
- **Hypotheses**: Full hypothesis is the existence of the separable factor (upstream content, marked `Conditional`).
- **Uses from project**: `frobeniusIsog_relative`, `mulByInt`.
- **Used by**: unused in file.
- **Visibility**: public (scoped to `Conditional` namespace).
- **Lines**: 649–656, proof 1 line.
- **Notes**: Stub/placeholder; body is `h_factor`. The `Conditional` namespace marks it explicitly as requiring upstream discharge.

---

### `theorem Conditional.mulByNat_p_factors_through_frobenius_of_witnesses`
- **Type**: Given `_h_p_insep : ¬ (mulByInt E.toAffine (p : ℤ)).IsSeparable` and `h_factor : ∀ φ, ¬ φ.IsSeparable → ∃ ψ, ψ.IsSeparable ∧ ψ.comp (frobeniusIsog_relative p E) = φ`, concludes the same factorisation for `[p]`.
- **What**: Refined conditional form: factors the hypotheses into `[p]` being inseparable (T-FROB-INSEP) plus the general Silverman II.2.12 statement.
- **How**: `h_factor _ _h_p_insep` (function application).
- **Hypotheses**: As above.
- **Uses from project**: `frobeniusIsog_relative`, `mulByInt`.
- **Used by**: unused in file.
- **Visibility**: public (scoped to `Conditional`).
- **Lines**: 662–670, proof 1 line.
- **Notes**: Stub/placeholder; also `Conditional` namespace.

---

## Summary statistics

| Category | Count |
|---|---|
| Total declarations | 33 |
| `noncomputable def` | 9 |
| `theorem` | 17 |
| `lemma` | 4 |
| `instance` | 3 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Proofs > 30 lines | 2 (`frobeniusRelativeCoordRingHom_injective`: 79 lines, `frobeniusRelativeCoordRingHom_comp_map`: 49 lines) |

## Key API (used by 3+ other declarations in this file)

- `frobeniusRelativeBaseHom` — 22 references
- `frobeniusRelativeCoordRingHom` — 24 references
- `WeierstrassCurve.frobeniusTwist` — 62 references
- `frobeniusIsog_relative` — 32 references (excluding comment text)
- `frobeniusTwist_polynomial_eval₂_zero` — 4 references (used by 3 distinct theorems)
- `frobeniusRelativeCoordAlgHom_y` — 4 references (used by 2 theorems + 1 in comp proof)
- `frobeniusRelativeBaseHom_injective` — used by `frobeniusRelativeCoordRingHom_injective` (×2 internal uses)
- `frobeniusIsog_relative_pullback_x_gen` / `frobeniusIsog_relative_pullback_y_gen` — 3 references each
- `algebraMap_CR_KE_pow_p_mem_fieldRange` — 3 references

## Unused in file (dead-code candidates)

- `iterateFrobeniusTwist` — only mentioned in a docstring comment
- `frobeniusTwist_isElliptic` — named alias for inference, not called by any declaration
- `frobeniusIsog_relative_apply_some` — terminal evaluation lemma, no in-file caller
- `frobeniusIsog_relative_apply_zero` — `@[simp]` leaf, no in-file caller
- `x_gen_pow_p_mem_fieldRange` — no in-file caller
- `y_gen_pow_p_mem_fieldRange` — no in-file caller
- `algebraMap_k_mem_fieldRange` — no in-file caller
- `frobeniusIsog_relative_pow_p_mem_fieldRange` — no in-file caller
- `Conditional.mulByNat_p_factors_through_frobenius_of_silvermanII212` — stub, no in-file caller
- `Conditional.mulByNat_p_factors_through_frobenius_of_witnesses` — stub, no in-file caller
