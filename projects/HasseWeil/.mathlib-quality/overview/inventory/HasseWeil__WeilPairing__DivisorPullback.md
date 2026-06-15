# Inventory: ./HasseWeil/WeilPairing/DivisorPullback.lean

**Total declarations**: 30 (6 defs, 24 theorems, 0 instances)
**Sorries**: none
**`set_option maxHeartbeats`**: none

---

## Summary

This file proves divisor-pullback functoriality for the separable multiplication-by-`ℓ` isogeny on an elliptic curve over an algebraically closed field `F`. The main theorem is `projectiveDivisorOf_pullback_eq_pullbackDivisor`: under the per-place unramified order-transport predicate `ProjOrdTransport φ`, the projective divisor of `φ.pullback h` equals the fibre-pullback `pullbackDivisor φ (div h)`. The file also provides `ProjOrdTransport` for `mulByInt W ℓ` (`projOrdTransport_mulByInt`), and three pairing-facing corollaries. The file imports `MulByIntSamePlace`, `MulByIntUnramified`, `SigmaBridge`, `TranslateOrdInfty`.

---

### `noncomputable def projOrdAt`
- **Type**: `(f : KE) → (Q : W.Point) → ℤ`
- **What**: The coefficient of `projectiveDivisorOf f` at the projective place corresponding to the `Affine.Point` `Q` — i.e., `ord_Q f` for finite points and `ordAtInfty f` for the zero point.
- **How**: Single-line definition via `(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f Q.toProjectiveSmoothPoint`.
- **Hypotheses**: `W` an elliptic Weierstrass curve over a field `F`.
- **Uses from project**: none (uses `SmoothPlaneCurve.projectiveDivisorOf`, `Affine.Point.toProjectiveSmoothPoint`)
- **Used by**: `projOrdAt_some`, `projOrdAt_zero`, `OrdTransport`, `coeff_affine_pullback_eq`, `ProjOrdTransport`, `projOrdTransport_of_affine_of_infinity`, `ordTransport_affine_mulByInt` (7 uses in file)
- **Visibility**: public
- **Lines**: 77–79 (1-line body, no proof block)
- **Notes**: None

---

### `theorem projOrdAt_some`
- **Type**: `projOrdAt f (Affine.Point.some x y h) = ((⟨W⟩ : SmoothPlaneCurve F).ord_P ⟨x, y, h⟩ f).untopD 0`
- **What**: Unfolds `projOrdAt` at an affine smooth point: it is the affine order `ord_P` with `⊤` mapped to `0`.
- **How**: Rewrite via `Affine.Point.toProjectiveSmoothPoint_some` and `projectiveDivisorOf_apply_affine`.
- **Hypotheses**: `W.Nonsingular x y`.
- **Uses from project**: none (uses `SmoothPlaneCurve.projectiveDivisorOf_apply_affine`)
- **Used by**: `ordTransport_affine_mulByInt`
- **Visibility**: public
- **Lines**: 80–86 (3-line proof)
- **Notes**: None

---

### `theorem projOrdAt_zero`
- **Type**: `projOrdAt f (0 : W.Point) = ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f).untopD 0`
- **What**: Unfolds `projOrdAt` at the zero point (point at infinity): it is `ordAtInfty f` with `⊤` mapped to `0`.
- **How**: Rewrite via `Affine.Point.toProjectiveSmoothPoint_zero` and `projectiveDivisorOf_apply_infinity`.
- **Hypotheses**: None beyond curve setup.
- **Uses from project**: none (uses `SmoothPlaneCurve.projectiveDivisorOf_apply_infinity`)
- **Used by**: `projOrdTransport_of_affine_of_infinity`, `ordTransport_affine_mulByInt`
- **Visibility**: public
- **Lines**: 87–91 (2-line proof)
- **Notes**: None

---

### `def OrdTransport`
- **Type**: `(φ : Isogeny W W) → (P : SmoothPoint) → Prop`
- **What**: The per-place unramified order-transport predicate for isogeny `φ` at smooth point `P`: for every `h ∈ K(E)`, `ord_P(φ.pullback h) = projOrdAt h (φ(P))`. This is the geometric unramifiedness of `φ` at `P` (no ramification factor `e_P > 1`).
- **How**: Pure Prop-valued definition; no proof.
- **Hypotheses**: None (predicate).
- **Uses from project**: `projOrdAt`
- **Used by**: `coeff_affine_pullback_eq`, `projOrdTransport_of_affine_of_infinity`, `ordTransport_affine_mulByInt`, `ordTransport_mulByInt`
- **Visibility**: public
- **Lines**: 108–112 (4-line body)
- **Notes**: None

---

### `theorem coeff_affine_pullback_eq`
- **Type**: Under `OrdTransport φ P`, for any `h`, the coefficient of `projectiveDivisorOf (φ.pullback h)` at the affine place `P` equals `projOrdAt h (φ(P.toAffinePoint))`.
- **What**: Lifts `OrdTransport` from the `ord_P`-level to the `projectiveDivisorOf`-coefficient level at affine places, using `projectiveDivisorOf_apply_affine`.
- **How**: Single `rw` using `projectiveDivisorOf_apply_affine` then `exact hP h`.
- **Hypotheses**: `OrdTransport φ P`.
- **Uses from project**: `projOrdAt`, `OrdTransport`
- **Used by**: `projOrdTransport_of_affine_of_infinity`
- **Visibility**: public
- **Lines**: 116–124 (3-line proof)
- **Notes**: None

---

### `noncomputable def pullbackDivisor`
- **Type**: `(f : W.Point →+ W.Point) → (hf : Finite f.ker) → ProjectiveDivisor → ProjectiveDivisor`
- **What**: The fibre-pullback of a projective divisor `D` under `f`: `φ*(D) = Σ_v D(v) · pullbackDiv f hf v.toAffinePoint`, extending `pullbackDiv` (from `Pullback.lean`) ℤ-linearly over all places.
- **How**: `D.sum fun v n => n • pullbackDiv f hf v.toAffinePoint` — a `Finsupp.sum`.
- **Hypotheses**: Finite kernel of `f`.
- **Uses from project**: `pullbackDiv` (from `WeilPairing/Pullback.lean`)
- **Used by**: `pullbackDivisor_zero`, `pullbackDivisor_single`, `pullbackDivisor_add`, `pullbackDivisorHom`, `pullbackDivisor_apply`, `projectiveDivisorOf_pullback_eq_pullbackDivisor`, `pullback_divisorOf_eq_of_divisorOf_eq`, `pullbackDivisor_weilDivisor`, `pullbackDivisor_bilinDivisor` (9 uses)
- **Visibility**: public
- **Lines**: 135–139 (4-line body)
- **Notes**: Key API definition — used by 9+ other declarations in the file.

---

### `@[simp] theorem pullbackDivisor_zero`
- **Type**: `pullbackDivisor f hf 0 = 0`
- **What**: The fibre-pullback of the zero divisor is zero.
- **How**: `simp [pullbackDivisor]` using `Finsupp.sum` on the zero finsupp.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisor`
- **Used by**: `pullbackDivisorHom`
- **Visibility**: public
- **Lines**: 140–143 (2-line proof)
- **Notes**: None

---

### `@[simp] theorem pullbackDivisor_single`
- **Type**: `pullbackDivisor f hf (Finsupp.single v n) = n • pullbackDiv f hf v.toAffinePoint`
- **What**: The fibre-pullback of a single-place divisor `n · (v)` is `n` times the multiplicity-free fibre at `v`.
- **How**: `Finsupp.sum_single_index` + `zero_smul`.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisor`, `pullbackDiv`
- **Used by**: `pullbackDivisorHom` (implicitly via `map_add'`/`toFun`), `pullbackDivisor_weilDivisor`, `pullbackDivisor_bilinDivisor`
- **Visibility**: public
- **Lines**: 144–149 (4-line proof)
- **Notes**: None

---

### `@[simp] theorem pullbackDivisor_add`
- **Type**: `pullbackDivisor f hf (D₁ + D₂) = pullbackDivisor f hf D₁ + pullbackDivisor f hf D₂`
- **What**: The fibre-pullback is additive in the divisor argument.
- **How**: `Finsupp.sum_add_index'` with `zero_smul` and `add_smul`.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisor`
- **Used by**: `pullbackDivisorHom`
- **Visibility**: public
- **Lines**: 150–156 (5-line proof)
- **Notes**: None

---

### `noncomputable def pullbackDivisorHom`
- **Type**: `ProjectiveDivisor →+ ProjectiveDivisor` (additive group homomorphism)
- **What**: Packages `pullbackDivisor f hf` as an additive homomorphism, using `pullbackDivisor_zero` and `pullbackDivisor_add` as the group-hom axioms.
- **How**: Direct structure construction using the simp lemmas.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisor`, `pullbackDivisor_zero`, `pullbackDivisor_add`
- **Used by**: `pullbackDivisorHom_apply`, `pullbackDivisor_weilDivisor`, `pullbackDivisor_bilinDivisor`
- **Visibility**: public
- **Lines**: 158–164 (6-line body)
- **Notes**: None

---

### `@[simp] theorem pullbackDivisorHom_apply`
- **Type**: `pullbackDivisorHom f hf D = pullbackDivisor f hf D`
- **What**: Unfolding lemma: the hom-bundled version equals the plain function.
- **How**: `rfl`.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisorHom`, `pullbackDivisor`
- **Used by**: `pullbackDivisor_weilDivisor`, `pullbackDivisor_bilinDivisor`
- **Visibility**: public
- **Lines**: 165–167 (1-line proof)
- **Notes**: None

---

### `theorem pullbackDiv_apply_affine`
- **Type**: `pullbackDiv f hf Q (ProjectiveSmoothPoint.affine P) = if f P.toAffinePoint = Q then 1 else 0`
- **What**: The coefficient of the fibre divisor `pullbackDiv f hf Q` at an affine place `P` is `1` if `f(P) = Q` and `0` otherwise — the étale fibre structure.
- **How**: Case-splits on `f P.toAffinePoint = Q`. In the positive case, identifies the unique contributing summand `R = ⟨P, hPQ⟩` using `Finset.sum_eq_single`; in the negative case shows no summand contributes via `Finsupp.single_eq_of_ne`. Uses `fiber_finite` to get `Fintype`.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDiv`, `fiber_finite` (from `Pullback.lean`)
- **Used by**: `pullbackDivisor_apply` (via `pullbackDiv_apply`)
- **Visibility**: public
- **Lines**: 177–220 (43-line proof)
- **Notes**: Proof >30 lines. The `pullbackDiv_apply` below supersedes this with a uniform statement; `pullbackDiv_apply_affine` appears to not be called directly except in the proof of `pullbackDiv_apply` (which handles both cases uniformly).

---

### `theorem pullbackDiv_apply`
- **Type**: `pullbackDiv f hf Q w = if f w.toAffinePoint = Q then 1 else 0`
- **What**: The uniform version of `pullbackDiv_apply_affine`, valid at any projective place `w` (affine or `∞`): the coefficient is `1` iff `f(w.toAffinePoint) = Q`.
- **How**: Same case-split as `pullbackDiv_apply_affine`, now using `Affine.Point.toAffinePoint_toProjectiveSmoothPoint` for the round-trip. Uses `fiber_finite` for the `Fintype` instance.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDiv`, `fiber_finite` (from `Pullback.lean`)
- **Used by**: `pullbackDivisor_apply`
- **Visibility**: public
- **Lines**: 226–263 (37-line proof)
- **Notes**: Proof >30 lines. Largely parallel to `pullbackDiv_apply_affine` but uniform over all projective places.

---

### `theorem pullbackDivisor_apply`
- **Type**: `pullbackDivisor f hf D w = D (f w.toAffinePoint).toProjectiveSmoothPoint`
- **What**: The coefficient of the fibre-pullback divisor at any place `w` equals the coefficient of `D` at the image place `f(w)` — the key "coefficient transport" identity.
- **How**: Rewrites as a sum over `D.support`, uses `pullbackDiv_apply` to evaluate each summand as an indicator, then uses `Finset.sum_ite_eq` for the final coefficient extraction. Handles the `mem / notMem support` case split.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisor`, `pullbackDiv_apply`
- **Used by**: `projectiveDivisorOf_pullback_eq_pullbackDivisor`
- **Visibility**: public
- **Lines**: 267–293 (26-line proof)
- **Notes**: None

---

### `def ProjOrdTransport`
- **Type**: `(φ : Isogeny W W) → Prop`
- **What**: The uniform projective order-transport predicate for `φ`: for every `h ∈ K(E)` and every projective place `w`, the coefficient of `projectiveDivisorOf (φ.pullback h)` at `w` equals `projOrdAt h (φ(w.toAffinePoint))`.
- **How**: Pure Prop-valued definition.
- **Hypotheses**: None (predicate).
- **Uses from project**: `projOrdAt`
- **Used by**: `projectiveDivisorOf_pullback_eq_pullbackDivisor`, `projOrdTransport_of_affine_of_infinity`, `projOrdTransport_mulByInt`, `pullback_divisorOf_eq_of_divisorOf_eq`, `projectiveDivisorOf_pullback_weilFunction`, `projectiveDivisorOf_pullback_bilinFunction` (6 uses)
- **Visibility**: public
- **Lines**: 308–313 (4-line body)
- **Notes**: Key API — used by 6+ other declarations. Also used by at least 5 files outside this file (IsogenySurjective, ProjOrdTransportLocal, HfactLemma, PairingNondeg, PairingProps).

---

### `theorem projectiveDivisorOf_pullback_eq_pullbackDivisor`
- **Type**: Under `ProjOrdTransport φ` and `[Finite φ.toAddMonoidHom.ker]`, `projectiveDivisorOf (φ.pullback h) = pullbackDivisor φ.toAddMonoidHom inferInstance (projectiveDivisorOf h)`.
- **What**: The main divisor-pullback functoriality theorem: `div(φ*h) = φ*(div h)`. This is Silverman III.4.10c / III.8 in divisor language.
- **How**: Extensionality via `Finsupp.ext`; at each place `w`, rewrites the LHS using `ProjOrdTransport` and the RHS using `pullbackDivisor_apply`, then checks they agree by `rfl` (both equal `projOrdAt h (φ(w))`).
- **Hypotheses**: `ProjOrdTransport φ`, `Finite φ.toAddMonoidHom.ker`.
- **Uses from project**: `ProjOrdTransport`, `pullbackDivisor`, `pullbackDivisor_apply`
- **Used by**: `pullback_divisorOf_eq_of_divisorOf_eq`
- **Visibility**: public
- **Lines**: 321–332 (11-line proof)
- **Notes**: None

---

### `def InftyOrdTransport`
- **Type**: `(φ : Isogeny W W) → Prop`
- **What**: The infinity order-transport predicate for `φ`: `(ordAtInfty (φ.pullback h)).untopD 0 = (ordAtInfty h).untopD 0` for every `h`. Since `φ(O) = O` (group hom), this is `ord_∞(φ*h) = ord_∞ h`.
- **How**: Pure Prop-valued definition.
- **Hypotheses**: None (predicate).
- **Uses from project**: none directly
- **Used by**: `projOrdTransport_of_affine_of_infinity`, `inftyOrdTransport_mulByInt`, `ordTransport_mulByInt`
- **Visibility**: public
- **Lines**: 342–346 (4-line body)
- **Notes**: Also used externally by `OneSubInftyResidues`, `PencilComapWitnesses`.

---

### `theorem projOrdTransport_of_affine_of_infinity`
- **Type**: If `OrdTransport φ P` holds for every affine smooth point `P`, and `InftyOrdTransport φ`, then `ProjOrdTransport φ`.
- **What**: Assembles the uniform `ProjOrdTransport` predicate from its two halves: the affine per-place core and the infinity transport. A projective place is either affine or `∞`.
- **How**: Case-splits on the projective place (`affine P` vs `infinity`). For affine: uses `coeff_affine_pullback_eq` + `rfl`. For `∞`: uses `projectiveDivisorOf_apply_infinity` and `hinf` with `map_zero` (`φ(O) = O`), then `projOrdAt_zero`.
- **Hypotheses**: `OrdTransport φ P` for all `P`, `InftyOrdTransport φ`.
- **Uses from project**: `OrdTransport`, `InftyOrdTransport`, `ProjOrdTransport`, `coeff_affine_pullback_eq`, `projOrdAt_zero`
- **Used by**: `projOrdTransport_mulByInt`
- **Visibility**: public
- **Lines**: 352–365 (13-line proof)
- **Notes**: None

---

### `theorem inftyOrdTransport_mulByInt`
- **Type**: Under `ℓ ≠ 0` and `(ℓ : F) ≠ 0`, `InftyOrdTransport (mulByInt W ℓ)`.
- **What**: The infinity order-transport for `[ℓ]`: `ord_∞([ℓ]*h) = ord_∞ h` for all `h ∈ K(E)`.
- **How**: Constructs the comap valuation `w = ordAtInftyValuation ∘ [ℓ].pullback` and proves it equals `ordAtInftyValuation` via the master lemma `eq_ordAtInftyValuation_of_x_y` (from `TranslateOrdInfty`). The base values are: `w(x_gen) = exp 2` (using `mulByInt_pullback_x`, `mulByInt_x_ne_zero`, `ordAtInfty_mulByInt_x`) and `w(y_gen) = exp 3` (using `ordAtInfty_mulByInt_y_eq_neg_three_general`). After establishing the valuation identity, reads off the additive order via the `exp`-bridge `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` and `WithZero.exp_inj`.
- **Hypotheses**: `ℓ ≠ 0`, `(ℓ : F) ≠ 0` (separability).
- **Uses from project**: `InftyOrdTransport`, `mulByInt_pullback_x`, `mulByInt_pullback_y` (from `MulByIntPullback`), `mulByInt_x_ne_zero`, `ordAtInfty_mulByInt_x`, `ordAtInfty_mulByInt_y_eq_neg_three_general` (from `MulByIntSamePlace`), `eq_ordAtInftyValuation_of_x_y` (from `TranslateOrdInfty`)
- **Used by**: `ordTransport_mulByInt`
- **Visibility**: public
- **Lines**: 378–439 (61-line proof)
- **Notes**: Proof >30 lines (61 lines). No `set_option maxHeartbeats`.

---

### `theorem comap_pointValuation_mulByInt_eq_affine`
- **Type**: Under `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, smooth point `P`, and `(mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns`, we have `(pointValuation P).comap [ℓ].pullback.toRingHom = pointValuation ⟨x, y, h_ns⟩`.
- **What**: The comap-valuation identity for `[ℓ]` at an affine image: the DVR `pointValuation P` pulled back along `[ℓ]` equals `pointValuation` at the image point `Q = (x, y)`.
- **How**: Case-splits on whether `Q` is 2-torsion (`y = W.negY x y`) or not. In each case, finds a uniformizer `t` at `Q` (either `y_gen − y_Q` or `x_gen − x_Q`), uses the corresponding `ord_P_mulByInt_y_sub_const_eq_one` or `ord_P_mulByInt_x_sub_const_eq_one` (from `MulByIntUnramified`) for the `e = 1` datum, and calls `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` (from `IsogenyOrdTransport`) with `mulByInt_comap_pointValuation_isEquiv_affine` (from `MulByIntSamePlace`) for same-place content.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `mulByInt W ℓ` maps `P` to the affine point `(x, y)`.
- **Uses from project**: `mulByInt_pullback_x`, `mulByInt_pullback_y`, `ord_P_mulByInt_y_sub_const_eq_one`, `ord_P_mulByInt_x_sub_const_eq_one` (from `MulByIntUnramified`), `mulByInt_comap_pointValuation_isEquiv_affine` (from `MulByIntSamePlace`), `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` (from `IsogenyOrdTransport`), `pointValuation_surjective'`
- **Used by**: `ord_P_mulByInt_pullback_eq_affine`, `ordTransport_affine_mulByInt`
- **Visibility**: public
- **Lines**: 511–542 (31-line proof)
- **Notes**: Proof >30 lines (31 lines). This is an assembly lemma that glues the same-place content (isEquiv) with the unramifiedness content (e=1 datum).

---

### `theorem ord_P_mulByInt_pullback_eq_affine`
- **Type**: Under `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, and `[ℓ](P) = some x y h_ns`, for nonzero `f`: `ord_P P ([ℓ].pullback f) = ord_P ⟨x, y, h_ns⟩ f`.
- **What**: The additive per-place order-transport for `[ℓ]` at an affine image: the order of the pulled-back function at `P` equals the order of `f` at the image `[ℓ](P)`.
- **How**: Extracts integer orders `m, n` from the nonzero conditions using `WithTop.ne_top_iff_exists`, reads off the comap identity `comap_pointValuation_mulByInt_eq_affine` at `f` via `DFunLike.coe`, then uses the `exp`-bridge `pointValuation_eq_exp_neg_of_ord_P_eq` + `WithZero.exp_inj` to conclude `m = n`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, affine image, `f ≠ 0`.
- **Uses from project**: `comap_pointValuation_mulByInt_eq_affine`, `pointValuation_eq_exp_neg_of_ord_P_eq` (from `OrdAtPoint` or similar)
- **Used by**: not directly referenced within this file (used externally)
- **Visibility**: public
- **Lines**: 557–587 (30-line proof)
- **Notes**: None. Note `pullback_injective` is used to show `[ℓ].pullback f ≠ 0`.

---

### `theorem ord_P_mulByInt_pullback_eq_infty`
- **Type**: Under `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, and `[ℓ](P) = 0` (P is ℓ-torsion), for nonzero `f`: `ord_P P ([ℓ].pullback f) = ordAtInfty f`.
- **What**: The additive order-transport for `[ℓ]` at an ℓ-torsion point: the order of the pulled-back function at `P` equals `ord_∞ f`.
- **How**: Uses `comap_pointValuation_mulByInt_eq_infty` (from `MulByIntSamePlace`) to get the valuation equality, extracts integer orders, uses `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` + `WithZero.exp_inj` for the conclusion.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `P` is ℓ-torsion, `f ≠ 0`.
- **Uses from project**: `comap_pointValuation_mulByInt_eq_infty` (from `MulByIntSamePlace`), `pointValuation_eq_exp_neg_of_ord_P_eq`, `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`
- **Used by**: not directly referenced within this file
- **Visibility**: public
- **Lines**: 593–617 (24-line proof)
- **Notes**: None.

---

### `theorem ordTransport_affine_mulByInt`
- **Type**: Under `[IsAlgClosed F]` and `(ℓ : F) ≠ 0`, `OrdTransport (mulByInt W ℓ) P` for any affine smooth point `P`.
- **What**: The affine per-place order-transport for `[ℓ]`: for every `h ∈ K(E)`, `ord_P P ([ℓ].pullback h) = projOrdAt h ([ℓ](P))`. This is the core of Silverman III.4.10c.
- **How**: Handles `h = 0` separately (both sides vanish). For `h ≠ 0`, extracts integer order `m`, computes `pointValuation P (τ h) = WithZero.exp(−m)`. Case-splits on whether the image `[ℓ](P)` is `O` or a finite point `(x, y)`. In each case, reads off the appropriate comap identity (`comap_pointValuation_mulByInt_eq_infty` or `comap_pointValuation_mulByInt_eq_affine`) and compares via the `exp`-bridge + `projOrdAt_zero` or `projOrdAt_some`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`.
- **Uses from project**: `OrdTransport`, `projOrdAt`, `projOrdAt_zero`, `projOrdAt_some`, `comap_pointValuation_mulByInt_eq_infty` (from `MulByIntSamePlace`), `comap_pointValuation_mulByInt_eq_affine`, `pointValuation_eq_exp_neg_of_ord_P_eq`, `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`
- **Used by**: `ordTransport_mulByInt`
- **Visibility**: public
- **Lines**: 629–683 (54-line proof)
- **Notes**: Proof >30 lines (54 lines). This is the main affine unramifiedness proof; it relies on both comap-valuation residuals.

---

### `theorem ordTransport_mulByInt`
- **Type**: Under `[IsAlgClosed F]` and `(ℓ : F) ≠ 0`, the conjunction `(∀ P, OrdTransport (mulByInt W ℓ) P) ∧ InftyOrdTransport (mulByInt W ℓ)`.
- **What**: Packages the affine and infinity transport for `[ℓ]` into a single conjunction.
- **How**: `exact ⟨ordTransport_affine_mulByInt ℓ hℓ, inftyOrdTransport_mulByInt ℓ hℓ0 hℓ⟩`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`.
- **Uses from project**: `OrdTransport`, `InftyOrdTransport`, `ordTransport_affine_mulByInt`, `inftyOrdTransport_mulByInt`
- **Used by**: `projOrdTransport_mulByInt`
- **Visibility**: public
- **Lines**: 687–692 (4-line proof)
- **Notes**: None.

---

### `theorem projOrdTransport_mulByInt`
- **Type**: Under `[IsAlgClosed F]` and `(ℓ : F) ≠ 0`, `ProjOrdTransport (mulByInt W ℓ)`.
- **What**: The uniform projective order-transport for the separable multiplication-by-`ℓ` isogeny. Assembles the affine and infinity halves.
- **How**: `projOrdTransport_of_affine_of_infinity` applied to the two components of `ordTransport_mulByInt`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`.
- **Uses from project**: `ProjOrdTransport`, `projOrdTransport_of_affine_of_infinity`, `ordTransport_mulByInt`
- **Used by**: Not referenced within this file (used externally by `ProjOrdTransportLocal`, pairing files).
- **Visibility**: public
- **Lines**: 695–699 (4-line proof)
- **Notes**: None.

---

### `theorem pullback_divisorOf_eq_of_divisorOf_eq`
- **Type**: Under `ProjOrdTransport φ`, `Finite φ.toAddMonoidHom.ker`, and `projectiveDivisorOf k = D`: `projectiveDivisorOf (φ.pullback k) = pullbackDivisor φ.toAddMonoidHom inferInstance D`.
- **What**: The pairing-facing divisor functoriality: if `k` has projective divisor `D`, then `φ.pullback k` has divisor the fibre-pullback `φ*(D)`.
- **How**: Chain `projectiveDivisorOf_pullback_eq_pullbackDivisor hcore k` then substitute `hk`.
- **Hypotheses**: `ProjOrdTransport φ`, `Finite φ.toAddMonoidHom.ker`.
- **Uses from project**: `ProjOrdTransport`, `pullbackDivisor`, `projectiveDivisorOf_pullback_eq_pullbackDivisor`
- **Used by**: `projectiveDivisorOf_pullback_weilFunction`, `projectiveDivisorOf_pullback_bilinFunction`
- **Visibility**: public
- **Lines**: 709–717 (7-line proof)
- **Notes**: None.

---

### `theorem pullbackDivisor_weilDivisor`
- **Type**: `pullbackDivisor f hf (ℓ • (T) − ℓ • (O)) = ℓ • (pullbackDiv f hf T − pullbackDiv f hf 0)` (divisors as Finsupp).
- **What**: Pure-algebra identity (no core needed): the fibre-pullback of the Weil divisor `ℓ((T) − (O))` equals `ℓ` times the fibre-difference divisor `φ*(T) − φ*(O)`. The divisor-level form of `f_T ∘ φ = c · g_T^ℓ`.
- **How**: Rewrites via `pullbackDivisorHom_apply`, `map_sub`, `pullbackDivisor_single`, and `toAffinePoint_toProjectiveSmoothPoint`.
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisor`, `pullbackDivisorHom`, `pullbackDivisorHom_apply`, `pullbackDivisor_single`, `pullbackDiv`
- **Used by**: `projectiveDivisorOf_pullback_weilFunction`
- **Visibility**: public
- **Lines**: 723–733 (10-line proof)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_pullback_weilFunction`
- **Type**: Under `ProjOrdTransport (mulByInt W ℓ)`, `[Finite (mulByInt W ℓ).toAddMonoidHom.ker]`, and `fT` having divisor `ℓ((T) − (O))`: `projectiveDivisorOf ([ℓ].pullback fT) = ℓ • (pullbackDiv ... T − pullbackDiv ... 0)`.
- **What**: The III.8.1 divisor identity for `[ℓ]`: `[ℓ].pullback f_T` (where `f_T` has Weil divisor) has divisor `ℓ · (fibre-diff)`. Pairing nondegeneracy consumes this.
- **How**: Chain `pullback_divisorOf_eq_of_divisorOf_eq hcore hfT` then `pullbackDivisor_weilDivisor`.
- **Hypotheses**: `ProjOrdTransport (mulByInt W ℓ)`, `Finite` kernel, Weil divisor hypothesis on `fT`.
- **Uses from project**: `ProjOrdTransport`, `pullbackDivisor`, `pullbackDiv`, `pullback_divisorOf_eq_of_divisorOf_eq`, `pullbackDivisor_weilDivisor`
- **Used by**: Not referenced within this file.
- **Visibility**: public
- **Lines**: 743–754 (11-line proof)
- **Notes**: None.

---

### `theorem pullbackDivisor_bilinDivisor`
- **Type**: `pullbackDivisor f hf ((T₁+T₂) − T₁ − T₂ + O) = pullbackDiv f hf (T₁+T₂) − pullbackDiv f hf T₁ − pullbackDiv f hf T₂ + pullbackDiv f hf 0` (with divisors as Finsupp).
- **What**: Pure-algebra identity: the fibre-pullback of the bilinearity-in-`T` divisor `(T₁+T₂)−(T₁)−(T₂)+(O)` distributes over the four fibre terms.
- **How**: Rewrites via `pullbackDivisorHom_apply`, `map_add`, `map_sub`, `pullbackDivisor_single` (four times), `one_smul` (four times), and `toAffinePoint_toProjectiveSmoothPoint` (four times).
- **Hypotheses**: Finite kernel.
- **Uses from project**: `pullbackDivisor`, `pullbackDivisorHom`, `pullbackDivisorHom_apply`, `pullbackDivisor_single`, `pullbackDiv`
- **Used by**: `projectiveDivisorOf_pullback_bilinFunction`
- **Visibility**: public
- **Lines**: 760–777 (17-line proof)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_pullback_bilinFunction`
- **Type**: Under `ProjOrdTransport (mulByInt W ℓ)`, `[Finite ...]`, and `k` having the bilinearity divisor: `projectiveDivisorOf ([ℓ].pullback k) = pullbackDiv ... (T₁+T₂) − pullbackDiv ... T₁ − pullbackDiv ... T₂ + pullbackDiv ... 0`.
- **What**: The bilinearity-in-`T` divisor identity: pulling back a function `k` with the Abel–Jacobi divisor gives the pullback of the four fibre-divisors. The divisor identity behind bilinearity in the second slot (Silverman III.8.1b).
- **How**: Chain `pullback_divisorOf_eq_of_divisorOf_eq hcore hk` then `pullbackDivisor_bilinDivisor`.
- **Hypotheses**: `ProjOrdTransport (mulByInt W ℓ)`, `Finite` kernel, bilinearity divisor hypothesis on `k`.
- **Uses from project**: `ProjOrdTransport`, `pullbackDivisor`, `pullbackDiv`, `pullback_divisorOf_eq_of_divisorOf_eq`, `pullbackDivisor_bilinDivisor`
- **Used by**: Not referenced within this file (used by `PairingProps`).
- **Visibility**: public
- **Lines**: 788–803 (15-line proof)
- **Notes**: None.
