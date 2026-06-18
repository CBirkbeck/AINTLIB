# Inventory: ./HasseWeil/EC/SeparableKernelTorsor.lean

**File summary:** 376 lines. Formalises Silverman III.4.10c — the kernel-torsor / Galois-correspondence proof that `#ker φ = deg φ` for a separable endomorphism φ of an elliptic curve over K̄. The structure is: (1) abstract Galois packaging (3 theorems), (2) the concrete forward witness `kernelTranslateForwardAut`, (3) Phase-1 helper lemmas about the translation action on the generic point, (4) the concrete inverse witness via a descent hypothesis `hdesc`, and (5) the master concrete theorem `card_kernel_eq_degree_of_separable_concrete`.

**Imports:** `HasseWeil.EC.IsogenyKernel`, `HasseWeil.Curves.Differentials`, `HasseWeil.EC.TranslationOrd`.

No `set_option maxHeartbeats`. No `sorry`. No `private` declarations.

---

### `theorem card_kernel_eq_degree_of_separable_isogeny`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → φ.IsSeparable → Normal K(E) K(E) [w.r.t. φ.toAlgebra] → (#ker φ = #Aut(K(E)/φ*K(E))) → #ker φ = φ.degree`
- **What**: The master abstract theorem: for a separable endomorphism, the kernel cardinality equals the degree, given normality of the function-field extension and a bijection witness between the kernel and the automorphism group.
- **How**: Rewrites `#ker φ = #Aut` via `h_card`, then applies `Isogeny.card_aut_eq_degree_of_isGalois` (using `isogeny_finiteDimensional` to get finite-dimensionality, and `Isogeny.isGalois_of_isSeparable_and_normal` to package separability + normality into `IsGalois`).
- **Hypotheses**: φ separable; function-field extension `K(E)/φ*K(E)` is normal; `#ker φ = #Aut(K(E)/φ*K(E))`.
- **Uses from project**: `isogeny_finiteDimensional` (Differentials.lean), `Isogeny.card_aut_eq_degree_of_isGalois` (IsogenyKernel.lean), `Isogeny.isGalois_of_isSeparable_and_normal` (IsogenyKernel.lean).
- **Used by**: `card_kernel_eq_degree_of_separable_of_witnesses` (line 91), `card_kernel_eq_degree_of_separable_concrete` (line 373).
- **Visibility**: public
- **Lines**: 44–54; proof ~3 lines.
- **Notes**: None.

---

### `theorem card_kernel_eq_card_aut_of_inverse_witnesses`

- **Type**: Given `forward : ker φ → Aut(K(E)/φ*K(E))` and `inverse : Aut → ker φ` that are mutual inverses (LeftInverse + RightInverse), then `#ker φ = #Aut(K(E)/φ*K(E))`.
- **What**: Packages a forward/inverse pair into a `Nat.card` bijection. This discharges the `h_card` hypothesis of `card_kernel_eq_degree_of_separable_isogeny`.
- **How**: Pure `Nat.card_congr` applied to the `Equiv` built from the four witness data.
- **Hypotheses**: Explicit forward and inverse functions that are mutual inverses.
- **Uses from project**: None (pure mathlib `Nat.card_congr`).
- **Used by**: `card_kernel_eq_degree_of_separable_of_witnesses` (line 91).
- **Visibility**: public
- **Lines**: 63–74; proof 1 line (term-mode).
- **Notes**: None.

---

### `theorem card_kernel_eq_degree_of_separable_of_witnesses`

- **Type**: Same as `card_kernel_eq_degree_of_separable_isogeny` but takes explicit `forward`/`inverse` mutual-inverse witnesses instead of the abstract `h_card`.
- **What**: Combines the two abstract lemmas above: given separability, normality, and explicit forward/inverse translation witnesses, concludes `#ker φ = φ.degree`.
- **How**: Composes `card_kernel_eq_card_aut_of_inverse_witnesses` to produce `h_card`, then applies `card_kernel_eq_degree_of_separable_isogeny`.
- **Hypotheses**: φ separable; normal extension; explicit forward/inverse functions with mutual-inverse proofs.
- **Uses from project**: `card_kernel_eq_degree_of_separable_isogeny` (this file, line 44), `card_kernel_eq_card_aut_of_inverse_witnesses` (this file, line 63).
- **Used by**: `card_kernel_eq_degree_of_separable_concrete` (line 373).
- **Visibility**: public
- **Lines**: 80–92; proof 2 lines (term-mode).
- **Notes**: None.

---

### `noncomputable def kernelTranslateForwardAut`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → (hcov : ∀ k ∈ ker φ, ∀ z, τ_k(φ*z) = φ*z) → ker φ → Aut(K(E)/φ*K(E))`
- **What**: Constructs the forward map of the kernel-torsor: sends a kernel point `k` to the translation automorphism `τ_k`, recast as a `φ*K(E)`-algebra automorphism of `K(E)` using the covariance hypothesis that `τ_k` fixes the pullback range.
- **How**: Uses `AlgEquiv.ofRingEquiv` to upgrade `translateAlgEquivOfPoint W k.val` (an `F`-AlgEquiv of `K(E)`) to an element of `Aut(K(E)/φ*K(E))` by supplying `hcov k` as the commutes-with-algebra-map proof.
- **Hypotheses**: Covariance `hcov`: translation by any kernel point fixes every element of `φ*K(E)`.
- **Uses from project**: `translateAlgEquivOfPoint` (TranslationOrd.lean).
- **Used by**: `kernelTranslateForwardAut_injective` (line 116), `genericPointAct_kernelTranslateForwardAut` (line 293), `card_kernel_eq_degree_of_separable_concrete` (line 338).
- **Visibility**: public
- **Lines**: 100–109; 4-line body (term-mode def).
- **Notes**: None.

---

### `theorem kernelTranslateForwardAut_injective`

- **Type**: `Function.Injective (kernelTranslateForwardAut W φ hcov)`
- **What**: The forward kernel-translation map is injective: if two kernel points give the same automorphism of `K(E)/φ*K(E)`, they are equal.
- **How**: From equal `Aut`-elements, extracts equal underlying functions via `AlgEquiv.ext`/`congrFun`, then deduces `τ_{k1} = τ_{k2}` as ring maps, and concludes `k1 = k2` by `translateAlgEquivOfPoint_injective` (distinct points give distinct translations).
- **Hypotheses**: Same `hcov` as `kernelTranslateForwardAut`.
- **Uses from project**: `kernelTranslateForwardAut` (this file, line 100), `translateAlgEquivOfPoint_injective` (TranslationOrd.lean).
- **Used by**: `finite_kernel_of_hcov` (line 142).
- **Visibility**: public
- **Lines**: 116–129; proof ~13 lines.
- **Notes**: None.

---

### `theorem finite_kernel_of_hcov`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → (hcov : ∀ k ∈ ker φ, ∀ z, τ_k(φ*z) = φ*z) → Finite φ.kernel`
- **What**: Kernel finiteness from covariance alone (no Verschiebung or characteristic polynomial): the function-field extension `K(E)/φ*K(E)` is finite-dimensional, so `Aut(K(E)/φ*K(E))` is a `Fintype`, and the injective forward map embeds `ker φ` into this finite type.
- **How**: `isogeny_finiteDimensional` gives `FiniteDimensional`; `Finite.of_fintype _` gives `Finite Aut`; then `Finite.of_injective _ (kernelTranslateForwardAut_injective ...)`.
- **Hypotheses**: Same `hcov` as above.
- **Uses from project**: `isogeny_finiteDimensional` (Differentials.lean), `kernelTranslateForwardAut_injective` (this file, line 116).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 142–152; proof ~10 lines.
- **Notes**: Likely exported to downstream files for `[ℓ]` kernel finiteness. Trace-free/dual-free route is explicitly noted in the docstring.

---

### `theorem translateAlgEquivOfPoint_apply_x_gen_of_some`

- **Type**: `(xk yk : F) → (h_ns : Nonsingular xk yk) → translateAlgEquivOfPoint W (.some xk yk h_ns) (x_gen W) = translateX_xy W xk yk`
- **What**: Computes the action of the translation automorphism on the x-generator: `τ_k(x_gen) = translateX_xy W xk yk`, by case split on 2-torsion status of `k`.
- **How**: Case splits on `yk = negY xk yk` (2-torsion): in each branch, unfolds the relevant `AlgEquiv` constructor (`translateAlgEquiv_of_2tor` or `translateAlgEquiv`), reduces via `AlgEquiv.ofAlgHom_apply`, and applies the shipped generator-evaluation lemma (`translateAlgHom_of_2tor_apply_x_gen` or `translateAlgHom_apply_x_gen`).
- **Hypotheses**: `k = .some xk yk h_ns` (affine kernel point).
- **Uses from project**: `translateAlgEquivOfPoint_some_2tor` (TranslationOrd.lean), `translateAlgEquiv_of_2tor` (TranslationOrd.lean), `translateAlgHom_of_2tor_apply_x_gen` (TranslationOrd.lean), `translateAlgEquivOfPoint_some_nonTor` (TranslationOrd.lean), `translateAlgEquiv` (TranslationOrd.lean), `translateAlgHom_apply_x_gen` (TranslationOrd.lean), `x_gen` (MulByIntPullback.lean), `translateX_xy` (TranslationOrd.lean).
- **Used by**: `translateAlgEquivOfPoint_map_genericPoint` (line 203).
- **Visibility**: public
- **Lines**: 165–178; proof ~12 lines.
- **Notes**: None.

---

### `theorem translateAlgEquivOfPoint_apply_y_gen_of_some`

- **Type**: `(xk yk : F) → (h_ns : Nonsingular xk yk) → translateAlgEquivOfPoint W (.some xk yk h_ns) (y_gen W) = translateY_xy W xk yk`
- **What**: Same structure as the x_gen lemma: computes the action of `τ_k` on the y-generator.
- **How**: Case splits on 2-torsion; applies `translateAlgHom_of_2tor_apply_y_gen` or `translateAlgHom_apply_y_gen`.
- **Hypotheses**: `k = .some xk yk h_ns`.
- **Uses from project**: `translateAlgEquivOfPoint_some_2tor`, `translateAlgEquiv_of_2tor`, `translateAlgHom_of_2tor_apply_y_gen`, `translateAlgEquivOfPoint_some_nonTor`, `translateAlgEquiv`, `translateAlgHom_apply_y_gen`, `y_gen` (MulByIntPullback.lean), `translateY_xy` (TranslationOrd.lean).
- **Used by**: `translateAlgEquivOfPoint_map_genericPoint` (line 203).
- **Visibility**: public
- **Lines**: 182–195; proof ~12 lines.
- **Notes**: Structural twin of the x_gen version.

---

### `theorem translateAlgEquivOfPoint_map_genericPoint`

- **Type**: `∀ k : W.toAffine.Point, Point.map (translateAlgEquivOfPoint W k).toAlgHom (genericPoint W) = genericPoint W + liftPointToKE W k`
- **What**: The Phase-1 master lemma: the function-field translation `τ_k`, lifted to `(W_KE).Point`, sends the generic point to `P_gen + (k lifted to K(E))`. Covers both `k = 0` and `k = .some xk yk h_ns`.
- **How**: Case splits on `k`. At `k = 0`: uses `translateAlgEquivOfPoint_zero_toAlgHom` to see the map is identity, then `WeierstrassCurve.Affine.Point.map_id` and `add_zero`. At `k = .some`: unfolds via `liftPointToKE_some` and `genericPoint_add_liftSomePoint`, then matches coordinates using `WeierstrassCurve.Affine.Point.map_some` and the two generator lemmas above.
- **Hypotheses**: None beyond the file's variable hypotheses.
- **Uses from project**: `translateAlgEquivOfPoint_zero_toAlgHom` (TranslationOrd.lean), `liftPointToKE` (TranslationOrd.lean), `genericPoint` (GenericPoint.lean), `liftPointToKE_some` (TranslationOrd.lean), `genericPoint_add_liftSomePoint` (TranslationOrd.lean), `genericPoint_xOf_some` (GenericPoint.lean), `generic_nonsingular` (GenericPoint.lean), `translateAlgEquivOfPoint_apply_x_gen_of_some` (this file, line 165), `translateAlgEquivOfPoint_apply_y_gen_of_some` (this file, line 182).
- **Used by**: `genericPointAct_kernelTranslateForwardAut` (line 293), indirectly by `card_kernel_eq_degree_of_separable_concrete` (via `genericPointAct_kernelTranslateForwardAut`).
- **Visibility**: public
- **Lines**: 203–222; proof ~19 lines.
- **Notes**: Axiom-clean per docstring. This is the single geometric fact behind both mutual-inverse identities.

---

### `noncomputable def genericPointAct`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → Aut(K(E)/φ*K(E)) → (W_KE W).toAffine.Point`
- **What**: The action of an automorphism `σ ∈ Aut(K(E)/φ*K(E))` on the generic point `P_gen`, computed via `Affine.Point.map` of the `F`-algebra restriction of `σ`.
- **How**: Direct definition: `Point.map (σ.toAlgHom.restrictScalars F) (genericPoint W)`.
- **Hypotheses**: None (besides the `letI := φ.toAlgebra` instance).
- **Uses from project**: `genericPoint` (GenericPoint.lean), `W_KE` (MulByIntPullback.lean).
- **Used by**: `genericPointAct_eq_some` (line 245), `genericPointAct_mem_ker_g` (line 270), `genericPointAct_kernelTranslateForwardAut` (line 293), `card_kernel_eq_degree_of_separable_concrete` (line 323).
- **Visibility**: public
- **Lines**: 236–241; 2-line body.
- **Notes**: None.

---

### `theorem genericPointAct_eq_some`

- **Type**: `genericPointAct W φ σ = Affine.Point.some (σ (x_gen W)) (σ (y_gen W)) (baseChange_nonsingular ... (generic_nonsingular W))`
- **What**: Expresses the σ-action on the generic point in coordinates: the result is `(σ x_gen, σ y_gen)`.
- **How**: Unfolds `genericPointAct`, rewrites via `genericPoint_xOf_some`, then applies `WeierstrassCurve.Affine.Point.map_some`.
- **Hypotheses**: None.
- **Uses from project**: `genericPointAct` (this file, line 236), `genericPoint_xOf_some` (GenericPoint.lean), `generic_nonsingular` (GenericPoint.lean), `x_gen`, `y_gen` (MulByIntPullback.lean).
- **Used by**: `card_kernel_eq_degree_of_separable_concrete` (line 364–365).
- **Visibility**: public
- **Lines**: 245–257; proof ~7 lines.
- **Notes**: None.

---

### `theorem genericPointAct_mem_ker_g`

- **Type**: Given a group endomorphism `g` of `(W_KE).Point` with `g(P_gen) = (X, Y)` where `X = φ*x_gen`, `Y = φ*y_gen`, and `σ`-equivariance of `g`, concludes `g(σ(P_gen)) = g(P_gen)`.
- **What**: The kernel-membership half of Silverman III.4.10c: since `σ` fixes the pullback range `φ*K(E)`, and `g(P_gen)` has coordinates in that range, σ-equivariance forces `g(σ(P_gen)) = g(P_gen)`, i.e., `σ(P_gen) − P_gen ∈ ker g`.
- **How**: Rewrites `hequiv`, then applies `WeierstrassCurve.Affine.Point.map_some` and uses `σ.commutes` (σ fixes `φ*x_gen` and `φ*y_gen`) to close both coordinate goals via `Point.some.injEq`.
- **Hypotheses**: `g(P_gen) = some X Y hns`; `X = φ*x_gen`, `Y = φ*y_gen`; σ-equivariance of `g`.
- **Uses from project**: `genericPointAct` (this file, line 236).
- **Used by**: unused in file (exported utility for downstream).
- **Visibility**: public
- **Lines**: 270–287; proof ~15 lines.
- **Notes**: φ-agnostic generalisation of `GapSpines.emb_le_card_kernel`; the descent to `F`-rational kernel point is NOT done here (left to `hdesc` in the concrete theorem).

---

### `theorem genericPointAct_kernelTranslateForwardAut`

- **Type**: `genericPointAct W φ (kernelTranslateForwardAut W φ hcov k) = genericPoint W + liftPointToKE W k.val`
- **What**: The forward map's action on the generic point: `τ_k(P_gen) = P_gen + lift(k)`, linking `genericPointAct` for the forward witness to the Phase-1 master lemma.
- **How**: Unfolds both `genericPointAct` and `kernelTranslateForwardAut`; shows the underlying `AlgHom` equals `(translateAlgEquivOfPoint W k.val).toAlgHom` via `AlgHom.ext`+`rfl`; then applies `translateAlgEquivOfPoint_map_genericPoint`.
- **Hypotheses**: `hcov` covariance.
- **Uses from project**: `genericPointAct` (this file, line 236), `kernelTranslateForwardAut` (this file, line 100), `translateAlgEquivOfPoint_map_genericPoint` (this file, line 203), `liftPointToKE` (TranslationOrd.lean), `genericPoint` (GenericPoint.lean).
- **Used by**: `card_kernel_eq_degree_of_separable_concrete` (lines 352, 361).
- **Visibility**: public
- **Lines**: 293–306; proof ~13 lines.
- **Notes**: None.

---

### `theorem card_kernel_eq_degree_of_separable_concrete`

- **Type**: `(φ : Isogeny ...) → φ.IsSeparable → hcov → h_normal → hdesc → Nat.card φ.kernel = φ.degree`
  where `hdesc : ∀ σ, ∃ k ∈ ker φ, liftPointToKE W k = genericPointAct W φ σ − genericPoint W`
- **What**: The master concrete theorem (Silverman III.4.10c): for a separable endomorphism, `#ker φ = deg φ`, reduced to three genuine-isogeny hypotheses (`hcov`, `h_normal`, `hdesc`). The forward witness is `kernelTranslateForwardAut`; the inverse witness is `σ ↦ σ(P_gen) − P_gen` via `hdesc`; both mutual-inverse identities are discharged inline.
- **How**: 
  * Defines `inverse σ := ⟨(hdesc σ).choose, ...⟩` and sets `forward := kernelTranslateForwardAut`.
  * Proves `h_left` (inverse ∘ forward = id): `liftPointToKE (inverse (forward k)) = forward_k(P_gen) − P_gen = (P_gen + lift k) − P_gen = lift k` using `genericPointAct_kernelTranslateForwardAut`; concludes by injectivity of `liftPointToKE` (`WeierstrassCurve.Affine.Point.map_injective`).
  * Proves `h_right` (forward ∘ inverse = id): shows `genericPointAct (forward (inverse σ)) = genericPointAct σ` (both equal `σ(P_gen)`), reads off coordinate equality via `genericPointAct_eq_some` + `Point.some.injEq`, and extends to full `AlgEquiv` equality by `algHom_ext_x_y_gen`.
  * Concludes by `card_kernel_eq_degree_of_separable_of_witnesses`.
- **Hypotheses**: φ separable; `hcov` (kernel-translation covariance); `h_normal` (normal extension); `hdesc` (generic-point torsor descent).
- **Uses from project**: `kernelTranslateForwardAut` (this file, line 100), `genericPointAct` (this file, line 236), `genericPointAct_kernelTranslateForwardAut` (this file, line 293), `genericPointAct_eq_some` (this file, line 245), `liftPointToKE` (TranslationOrd.lean), `algHom_ext_x_y_gen` (TranslationOrd.lean), `card_kernel_eq_degree_of_separable_of_witnesses` (this file, line 80).
- **Used by**: unused in file (the main exported result).
- **Visibility**: public
- **Lines**: 323–375; proof ~51 lines.
- **Notes**: Proof is 51 lines — the longest in the file. No sorry, no maxHeartbeats. The `hdesc` hypothesis packages the two deep geometric steps (equivariance over K̄ and descent to F-rational points) that are discharged downstream for `φ = [ℓ]`.
