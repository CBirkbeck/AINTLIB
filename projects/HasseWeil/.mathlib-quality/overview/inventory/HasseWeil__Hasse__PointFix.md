# Inventory: ./HasseWeil/Hasse/PointFix.lean

**File purpose**: Formalises Silverman V.1's opening observation `E(F_q) = ker(1 − π)` at
the point level, and builds a cascading chain of witness-parametric helpers that reduce
the Hasse-bound fibre-witness requirement (HOLE D) to progressively more basic inputs:
`isogTrace`, separability, Galois-correspondence data, and the Artin fixed-field theorem
(`FixedPoints.finrank_eq_card`).

**Total declarations**: 47
**Lines**: 1121

---

## Declarations

---

### `@[simp] theorem frobeniusIsog_apply`
- **Type**: `(P : W.toAffine.Point) : (frobeniusIsog W).toAddMonoidHom P = P`
- **What**: The Frobenius isogeny acts as the identity on K-rational points; proved by `rfl` since the definition encodes it.
- **How**: Pure definitional equality; the point-map of `frobeniusIsog` is `AddMonoidHom.id` by construction.
- **Hypotheses**: `W` is a Weierstrass curve over a finite field `K`, elliptic.
- **Uses from project**: `frobeniusIsog`
- **Used by**: `kernel_eq_top_of_hom_eq_id_sub_frobenius` (line 72)
- **Visibility**: public
- **Lines**: 40–41, proof length 1
- **Notes**: Single-line `rfl` proof.

---

### `theorem kernel_eq_top_of_hom_eq_id_sub_frobenius`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) (h_hom : β.toAddMonoidHom = (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom) : β.kernel = ⊤`
- **What**: Any isogeny whose point-map equals `id − π` has trivial kernel in the sense that every rational point is in the kernel (kernel equals the whole group).
- **How**: Rewrites via `h_hom` and `frobeniusIsog_apply` to reduce the goal `β(P) = 0` to `P − P = 0`, closed by `sub_self`.
- **Hypotheses**: `β` is a self-isogeny of `W.toAffine`; its AddMonoidHom equals `id − Frobenius`.
- **Uses from project**: `frobeniusIsog_apply`, `frobeniusIsog`, `Isogeny.mem_kernel_iff`
- **Used by**: `degree_eq_pointCount_of_witness` (line 90), `hole_d_of_hom_and_sepDegree` (line 188), `isogOneSub_kernel_eq_top_of_hom` (line 212)
- **Visibility**: public
- **Lines**: 63–73, proof length 10
- **Notes**: None.

---

### `theorem degree_eq_pointCount_of_witness`
- **Type**: `[Fintype W.toAffine.Point] (β : Isogeny W.toAffine W.toAffine) (h_hom : ...) (h_ker_deg : Nat.card β.kernel = β.degree) : (β.degree : ℤ) = pointCount W.toAffine`
- **What**: If a self-isogeny `β` with point-map `id − π` satisfies `#ker β = deg β`, then `deg β = #E(F_q)` as integers. This is the T-V-1-003 content.
- **How**: Calls `kernel_eq_top_of_hom_eq_id_sub_frobenius` to get `β.kernel = ⊤`, then uses `AddSubgroup.card_top` and `Nat.card_eq_fintype_card` to identify `#ker β` with `pointCount`, then rewrites via `h_ker_deg`.
- **Hypotheses**: `W.toAffine.Point` is finite; `β` has point-map `id − π`; `Nat.card β.kernel = β.degree`.
- **Uses from project**: `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `pointCount`
- **Used by**: `pointCount_eq_of_hom_kernel_witness` (line 148)
- **Visibility**: public
- **Lines**: 83–94, proof length 11
- **Notes**: None.

---

### `theorem omegaPullbackCoeff_of_pullback_eq_id`
- **Type**: `{F : Type*} ... (α : Isogeny W.toAffine W.toAffine) (hα : α.pullback = AlgHom.id F W.toAffine.FunctionField) : omegaPullbackCoeff W α = 1`
- **What**: If an isogeny's function-field pullback is the identity AlgHom, its ω-pullback coefficient (the unique `c` with `α^* ω = c ω`) equals 1.
- **How**: Applies `omegaPullbackCoeff_unique`, then rewrites with `omegaPullbackCoeff_spec`, `alpha_star_u_eq`, and `hα`, finishing with `simp` + `rfl` after observing `AlgHom.id` acts as identity and `one_smul`.
- **Hypotheses**: `F` is a field, `W` elliptic over `F`, `α` is a self-isogeny whose pullback is the identity.
- **Uses from project**: `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec`, `alpha_star_u_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 113–122, proof length 9
- **Notes**: Variable shadowing: introduces a fresh `{F}` and `(W : WeierstrassCurve F)` at broader scope than the file-level `K`, `W`. Unused in file — dead-code candidate.

---

### `theorem pointCount_eq_of_hom_kernel_witness`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_hom : ...) (h_ker_deg : Nat.card β.kernel = β.degree) : (pointCount W.toAffine : ℤ) = Fintype.card K + 1 - isogTrace (frobeniusIsog W) β`
- **What**: Composed V.1 witness: under `id − π` point-map and `#ker = deg`, the point count equals `q + 1 − isogTrace π β`. This is the classical Silverman V.1 equation.
- **How**: One-liner composition of `degree_eq_pointCount_of_witness` with `pointCount_eq_of_witness` (from `Frobenius.lean`).
- **Hypotheses**: `W.toAffine.Point` finite; `β.toAddMonoidHom = id − π`; `Nat.card β.kernel = β.degree`.
- **Uses from project**: `degree_eq_pointCount_of_witness`, `pointCount_eq_of_witness`, `frobeniusIsog`, `isogTrace`, `pointCount`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 140–148, proof length 8
- **Notes**: Unused in file — dead-code candidate.

---

### `theorem hole_d_of_hom_and_sepDegree`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_hom : ...) (h_sepDeg : β.sepDegree = pointCount W.toAffine) : ∃ P₀, Nat.card {P // β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree`
- **What**: Produces the fibre-witness (HOLE D requirement) for any β with point-map `id − π` and `sepDegree = pointCount`. The fibre over any point has cardinality `β.sepDegree`.
- **How**: Applies `Isogeny.fiber_witness_of_ker_card_eq_sepDegree`, then rewrites using `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `AddSubgroup.card_top`, `Nat.card_eq_fintype_card`, and `h_sepDeg`.
- **Hypotheses**: `W.toAffine.Point` finite; `β.toAddMonoidHom = id − π`; `β.sepDegree = pointCount`.
- **Uses from project**: `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `pointCount`, `Isogeny.fiber_witness_of_ker_card_eq_sepDegree`
- **Used by**: `fiber_witness_of_separable_and_degree_eq_pointCount` (line 248)
- **Visibility**: public
- **Lines**: 178–190, proof length 12
- **Notes**: None.

---

### `theorem isogOneSub_kernel_eq_top_of_hom`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) (h_hom : ...) : β.kernel = ⊤`
- **What**: Sub-helper III-4-015-S1: trivial alias of `kernel_eq_top_of_hom_eq_id_sub_frobenius`.
- **How**: Term-mode direct application of `kernel_eq_top_of_hom_eq_id_sub_frobenius`.
- **Hypotheses**: Same as `kernel_eq_top_of_hom_eq_id_sub_frobenius`.
- **Uses from project**: `kernel_eq_top_of_hom_eq_id_sub_frobenius`
- **Used by**: `degree_eq_pointCount_of_card_kernel_eq_degree` (line 265–266)
- **Visibility**: public
- **Lines**: 207–212, proof length 5
- **Notes**: Thin wrapper; may be redundant given `kernel_eq_top_of_hom_eq_id_sub_frobenius` exists.

---

### `theorem card_kernel_eq_pointCount_of_kernel_eq_top`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_top : β.kernel = ⊤) : Nat.card β.kernel = pointCount W.toAffine`
- **What**: Sub-helper III-4-015-S2: from `β.kernel = ⊤`, the cardinality of the kernel is `pointCount`.
- **How**: Rewrites via `h_top`, `AddSubgroup.card_top`, `Nat.card_eq_fintype_card`, finished by `rfl`.
- **Hypotheses**: `W.toAffine.Point` finite; `β.kernel = ⊤`.
- **Uses from project**: `pointCount`
- **Used by**: `degree_eq_pointCount_of_card_kernel_eq_degree` (line 265)
- **Visibility**: public
- **Lines**: 217–223, proof length 6
- **Notes**: None.

---

### `theorem fiber_witness_of_separable_and_degree_eq_pointCount`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_hom : ...) (h_sep : β.IsSeparable) (h_fin : @FiniteDimensional ...) (h_deg : β.degree = pointCount W.toAffine) : ∃ P₀, Nat.card {P // β.toAddMonoidHom P = β.toAddMonoidHom P₀} = β.sepDegree`
- **What**: Sub-helper III-4-015-S3: fibre witness from separability + `deg β = #E(F_q)`. Uses `isSeparable_iff_sepDegree_eq_degree` to convert then delegates to `hole_d_of_hom_and_sepDegree`.
- **How**: Derives `β.sepDegree = pointCount` from `h_sep` via `Isogeny.isSeparable_iff_sepDegree_eq_degree`, then applies `hole_d_of_hom_and_sepDegree`.
- **Hypotheses**: `W.toAffine.Point` finite; `β.toAddMonoidHom = id − π`; `β` separable with finite-dimensional algebra; `β.degree = pointCount`.
- **Uses from project**: `hole_d_of_hom_and_sepDegree`, `Isogeny.isSeparable_iff_sepDegree_eq_degree`, `pointCount`
- **Used by**: `fiber_witness_of_separable_via_card_kernel_eq_degree` (line 285)
- **Visibility**: public
- **Lines**: 234–248, proof length 14
- **Notes**: None.

---

### `theorem degree_eq_pointCount_of_card_kernel_eq_degree`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_hom : ...) (h_card_eq : Nat.card β.kernel = β.degree) : β.degree = pointCount W.toAffine`
- **What**: Sub-helper III-4-015-S4: from `#ker β = deg β` and `β.toAddMonoidHom = id − π`, derives `deg β = #E(F_q)`.
- **How**: Uses `card_kernel_eq_pointCount_of_kernel_eq_top` (structural, from kernel = ⊤) and `isogOneSub_kernel_eq_top_of_hom`.
- **Hypotheses**: `W.toAffine.Point` finite; `β.toAddMonoidHom = id − π`; `Nat.card β.kernel = β.degree`.
- **Uses from project**: `card_kernel_eq_pointCount_of_kernel_eq_top`, `isogOneSub_kernel_eq_top_of_hom`
- **Used by**: `fiber_witness_of_separable_via_card_kernel_eq_degree` (line 286)
- **Visibility**: public
- **Lines**: 257–266, proof length 9
- **Notes**: None.

---

### `theorem fiber_witness_of_separable_via_card_kernel_eq_degree`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_hom : ...) (h_sep : β.IsSeparable) (h_fin : @FiniteDimensional ...) (h_card_eq : Nat.card β.kernel = β.degree) : ∃ P₀, ...`
- **What**: Sub-helper III-4-015-S5: full fibre-witness from `#ker = deg` directly (no-circular-dependency version). Chains S4 + S3.
- **How**: Term-mode composition: calls `fiber_witness_of_separable_and_degree_eq_pointCount` with `degree_eq_pointCount_of_card_kernel_eq_degree`.
- **Hypotheses**: `W.toAffine.Point` finite; `β.toAddMonoidHom = id − π`; `β` separable with finite algebra; `Nat.card β.kernel = β.degree`.
- **Uses from project**: `fiber_witness_of_separable_and_degree_eq_pointCount`, `degree_eq_pointCount_of_card_kernel_eq_degree`
- **Used by**: `fiber_witness_via_galois_witnesses` (line 338)
- **Visibility**: public
- **Lines**: 273–286, proof length 13
- **Notes**: None.

---

### `theorem card_kernel_eq_degree_of_galois_witness`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) (Aut : Type*) (h_aut_card : Nat.card Aut = β.degree) (h_iso : Nonempty (Equiv Aut β.kernel)) : Nat.card β.kernel = β.degree`
- **What**: Sub-helper III-4-015-S6: derives `#ker β = deg β` from an abstract Galois-style bijection `Aut ≃ β.kernel` and `#Aut = deg β`.
- **How**: Destructures `h_iso` to get the equivalence, rewrites `Nat.card β.kernel` via `Nat.card_congr`.
- **Hypotheses**: An abstract type `Aut` with `Nat.card Aut = β.degree` and a nonempty equivalence to `β.kernel`.
- **Uses from project**: None (abstract witness-parametric).
- **Used by**: `fiber_witness_via_galois_witnesses` (line 339)
- **Visibility**: public
- **Lines**: 311–319, proof length 8
- **Notes**: None.

---

### `theorem fiber_witness_via_galois_witnesses`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_hom : ...) (h_sep : ...) (h_fin : ...) (Aut : Type*) (h_aut_card : ...) (h_iso : ...) : ∃ P₀, ...`
- **What**: Sub-helper III-4-015-S7: chains S6 into S5 to get the fibre witness from two named Galois-correspondence witnesses.
- **How**: Term-mode composition of `fiber_witness_of_separable_via_card_kernel_eq_degree` with `card_kernel_eq_degree_of_galois_witness`.
- **Hypotheses**: Same as S5, plus Galois witnesses `Aut`, `h_aut_card`, `h_iso`.
- **Uses from project**: `fiber_witness_of_separable_via_card_kernel_eq_degree`, `card_kernel_eq_degree_of_galois_witness`
- **Used by**: `fiber_witness_via_isGalois_and_bijection` (line 400)
- **Visibility**: public
- **Lines**: 324–339, proof length 15
- **Notes**: None.

---

### `theorem card_aut_eq_degree_of_isGalois`
- **Type**: `(β : ...) (hgal : letI := β.toAlgebra; IsGalois W.toAffine.FunctionField W.toAffine.FunctionField) (hfin : @FiniteDimensional ...) : Nat.card (@AlgEquiv ... β.toAlgebra β.toAlgebra) = β.degree`
- **What**: Sub-helper III-4-015-S8: discharges Galois Witness #1 (`#Aut = deg β`) via Mathlib's `IsGalois.card_aut_eq_finrank`.
- **How**: Introduces `letI`/`haveI` to set up the algebra instance, then applies `IsGalois.card_aut_eq_finrank` directly.
- **Hypotheses**: `β.toAlgebra` is Galois (`IsGalois`) and `FiniteDimensional`.
- **Uses from project**: None from project (mathlib `IsGalois.card_aut_eq_finrank`).
- **Used by**: `fiber_witness_via_isGalois_and_bijection` (line 403)
- **Visibility**: public
- **Lines**: 360–371, proof length 11
- **Notes**: None.

---

### `theorem fiber_witness_via_isGalois_and_bijection`
- **Type**: `[Fintype W.toAffine.Point] (β : ...) (h_hom : ...) (h_sep : ...) (h_fin : ...) (hgal : ...) (h_iso : Nonempty (Equiv (@AlgEquiv ...) β.kernel)) : ∃ P₀, ...`
- **What**: Sub-helper III-4-015-S9: final cascade from IsGalois + automorphism-kernel bijection to fibre witness.
- **How**: Calls `fiber_witness_via_galois_witnesses` with `Aut = AlgEquiv...` and `card_aut_eq_degree_of_isGalois` for the card witness.
- **Hypotheses**: All previous hypotheses; `IsGalois`; Nonempty `Equiv (AlgEquiv...) β.kernel`.
- **Uses from project**: `fiber_witness_via_galois_witnesses`, `card_aut_eq_degree_of_isGalois`
- **Used by**: `fiber_witness_via_inverse_witnesses` (line 462)
- **Visibility**: public
- **Lines**: 384–403, proof length 19
- **Notes**: None.

---

### `theorem aut_kernel_equiv_of_inverse_witnesses`
- **Type**: `(β : ...) (Aut : Type*) (forward : β.kernel → Aut) (inverse : Aut → β.kernel) (h_left_inv : Function.LeftInverse inverse forward) (h_right_inv : Function.RightInverse inverse forward) : Nonempty (Equiv Aut β.kernel)`
- **What**: Sub-helper III-4-015-S10: builds the required `Nonempty (Equiv Aut β.kernel)` from explicit forward/inverse maps and mutual-inverse identities.
- **How**: Constructs the `Equiv` record directly and wraps in `⟨...⟩`.
- **Hypotheses**: Forward, inverse, and mutual-inverse hypotheses.
- **Uses from project**: None.
- **Used by**: `fiber_witness_via_inverse_witnesses` (line 463)
- **Visibility**: public
- **Lines**: 426–437, proof length 11
- **Notes**: None.

---

### `theorem fiber_witness_via_inverse_witnesses`
- **Type**: Full cascade: `[Fintype W.toAffine.Point] (β : ...) (h_hom, h_sep, h_fin, hgal, forward, inverse, h_left_inv, h_right_inv) : ∃ P₀, ...`
- **What**: Sub-helper III-4-015-S11: combines S10 with S9 to obtain the fibre witness from concrete forward/inverse map witnesses.
- **How**: Term-mode call to `fiber_witness_via_isGalois_and_bijection` with `aut_kernel_equiv_of_inverse_witnesses`.
- **Hypotheses**: All previous plus concrete forward/inverse maps and mutual-inverse proofs.
- **Uses from project**: `fiber_witness_via_isGalois_and_bijection`, `aut_kernel_equiv_of_inverse_witnesses`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 442–464, proof length 22
- **Notes**: Unused in file — dead-code candidate at the file level.

---

### `noncomputable def aut_of_kernel_zero`
- **Type**: `{F : Type*} ... (W : WeierstrassCurve F) [W.toAffine.IsElliptic] : W.toAffine.FunctionField ≃ₐ[F] W.toAffine.FunctionField`
- **What**: The trivial case of the forward map (translation-by-0 = identity AlgEquiv); defined as `AlgEquiv.refl`.
- **How**: Direct definition; `AlgEquiv.refl`.
- **Hypotheses**: `F` field, `W` elliptic.
- **Uses from project**: None.
- **Used by**: `aut_of_kernel_zero_apply`
- **Visibility**: public
- **Lines**: 476–480, proof length 4
- **Notes**: Uses fresh variable `{F}` at a different scope. Trivial sanity-check def.

---

### `@[simp] theorem aut_of_kernel_zero_apply`
- **Type**: `... (f : W.toAffine.FunctionField) : aut_of_kernel_zero W f = f`
- **What**: States that `aut_of_kernel_zero` acts as the identity function.
- **How**: `rfl`.
- **Hypotheses**: Same as `aut_of_kernel_zero`.
- **Uses from project**: `aut_of_kernel_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 483–488, proof length 5
- **Notes**: Unused in file. Simp lemma.

---

### `noncomputable def aut_of_kernel_construction_witness`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) (translation_at : β.kernel → W.toAffine.FunctionField ≃ₐ[K] W.toAffine.FunctionField) : β.kernel → W.toAffine.FunctionField ≃ₐ[K] W.toAffine.FunctionField`
- **What**: Identity combinator: given a family of translation AlgEquivs parametrised by kernel elements, produces the forward map (= the input). A placeholder for the substantive construction.
- **How**: `fun k => translation_at k` (eta-expansion identity).
- **Hypotheses**: A translation map `translation_at`.
- **Uses from project**: None.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 505–511, proof length 6
- **Notes**: Trivial combinator; no mathematical content. Unused in file — experimental/scaffold.

---

### `noncomputable def kernelTranslateForward`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) : β.kernel → (W.toAffine.FunctionField ≃ₐ[F] W.toAffine.FunctionField)`
- **What**: Concrete forward map `β.kernel → AlgEquiv`: sends kernel element `k` to the translation AlgEquiv `translateAlgEquivOfPoint W k.val`.
- **How**: `fun k => translateAlgEquivOfPoint W k.val`.
- **Hypotheses**: `F` field, `W` elliptic, `β` self-isogeny.
- **Uses from project**: `translateAlgEquivOfPoint`
- **Used by**: `kernelTranslateForward_zero` (line 532 comment)
- **Visibility**: public
- **Lines**: 523–526, proof length 3
- **Notes**: This is the "F-AlgEquiv landing" version; see `kernelTranslateAsAut` for the `β.toAlgebra`-promoted version.

---

### `@[simp] theorem kernelTranslateForward_zero`
- **Type**: `(β : ...) (h_zero_mem : (0 : W.toAffine.Point) ∈ β.kernel) : kernelTranslateForward W β ⟨0, h_zero_mem⟩ = AlgEquiv.refl`
- **What**: At the zero kernel element, the forward map is the identity AlgEquiv.
- **How**: `rfl`.
- **Hypotheses**: Zero must be in `β.kernel`.
- **Uses from project**: `kernelTranslateForward`, `translateAlgEquivOfPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 529–532, proof length 3
- **Notes**: Unused in file.

---

### `noncomputable def kernelTranslateAsAut`
- **Type**: `(β : ...) (k : β.kernel) (h_invariance : ∀ z, translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z) : @AlgEquiv ... β.toAlgebra β.toAlgebra`
- **What**: Promotes the F-AlgEquiv `translateAlgEquivOfPoint W k.val` to a `β.toAlgebra`-AlgEquiv, given a covariance identity.
- **How**: `AlgEquiv.ofRingEquiv` with covariance given by `h_invariance`.
- **Hypotheses**: Kernel element `k`; covariance identity `τ_k ∘ β.pullback = β.pullback`.
- **Uses from project**: `translateAlgEquivOfPoint`
- **Used by**: `kernelTranslateForwardAsAut` (line 578), `kernelTranslateAsAut_zero` (line 588), `kernelTranslateAsAut_apply` (line 607), `kernelTranslateAsAut_of_xy_invariance` (line 696)
- **Visibility**: public
- **Lines**: 558–567, proof length 9
- **Notes**: Crucial Layer-2 bridge declaration.

---

### `noncomputable def kernelTranslateForwardAsAut`
- **Type**: `(β : ...) (h_invariance_family : ∀ k : β.kernel, ∀ z, translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z) : β.kernel → @AlgEquiv ... β.toAlgebra β.toAlgebra`
- **What**: Family version of `kernelTranslateAsAut`; produces the full forward-map family `β.kernel → Aut` given universal covariance.
- **How**: `fun k => kernelTranslateAsAut W β k (h_invariance_family k)`.
- **Hypotheses**: Universal covariance family.
- **Uses from project**: `kernelTranslateAsAut`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 572–578, proof length 6
- **Notes**: Unused in file.

---

### `@[simp] theorem kernelTranslateAsAut_zero`
- **Type**: `(β : ...) (h_zero_mem : ...) (h_invariance : ...) : kernelTranslateAsAut W β ⟨0, h_zero_mem⟩ h_invariance = @AlgEquiv.refl ... β.toAlgebra`
- **What**: At the zero kernel element, `kernelTranslateAsAut` is the identity AlgEquiv.
- **How**: `AlgEquiv.ext` + `rfl` (translation by 0 is identity).
- **Hypotheses**: Zero in `β.kernel`; covariance at 0 (trivially true).
- **Uses from project**: `kernelTranslateAsAut`, `translateAlgEquivOfPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 582–595, proof length 13
- **Notes**: Unused in file.

---

### `theorem kernelTranslateAsAut_apply`
- **Type**: `(β : ...) (k : β.kernel) (h_invariance : ...) (f : W.toAffine.FunctionField) : kernelTranslateAsAut W β k h_invariance f = translateAlgEquivOfPoint W k.val f`
- **What**: States that applying `kernelTranslateAsAut` on data equals applying the F-AlgEquiv `translateAlgEquivOfPoint`.
- **How**: `rfl`.
- **Hypotheses**: Same as `kernelTranslateAsAut`.
- **Uses from project**: `kernelTranslateAsAut`, `translateAlgEquivOfPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 601–608, proof length 7
- **Notes**: Unused in file. Confirms `kernelTranslateAsAut` is conservative.

---

### `noncomputable def algHomFieldEqualizer`
- **Type**: `(f g : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) : IntermediateField F W.toAffine.FunctionField`
- **What**: The IntermediateField of points where two F-AlgHoms `K(E) → K(E)` agree; obtained by adding `inv_mem'` to the Subalgebra `AlgHom.equalizer f g`.
- **How**: Constructs the `IntermediateField` record; `inv_mem'` uses `map_inv₀` on both sides plus `hx`.
- **Hypotheses**: `F` field, `W` elliptic over `F`.
- **Uses from project**: None (pure mathlib structure).
- **Used by**: `mem_algHomFieldEqualizer` (line 639), `algHom_ext_of_eq_on_xy` (line 652)
- **Visibility**: public
- **Lines**: 627–635, proof length 8
- **Notes**: Infrastructure definition for generator-extension argument.

---

### `@[simp] theorem mem_algHomFieldEqualizer`
- **Type**: `(f g : ...) (x : W.toAffine.FunctionField) : x ∈ algHomFieldEqualizer W f g ↔ f x = g x`
- **What**: Membership in `algHomFieldEqualizer` is definitionally equality of the two AlgHom values.
- **How**: `Iff.rfl`.
- **Hypotheses**: None beyond context.
- **Uses from project**: `algHomFieldEqualizer`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 636–639, proof length 3
- **Notes**: Unused in file (but needed conceptually).

---

### `theorem algHom_ext_of_eq_on_xy`
- **Type**: `[Fintype F] (f g : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) (h_x : f (x_gen W) = g (x_gen W)) (h_y : f (y_gen W) = g (y_gen W)) : f = g`
- **What**: Two F-AlgHoms `K(E) → K(E)` that agree on `x_gen` and `y_gen` are equal, since `K(E) = adjoin F {x_gen, y_gen}`.
- **How**: Builds `h_top : ⊤ ≤ algHomFieldEqualizer W f g` by rewriting with `functionField_eq_intermediateField_adjoin_xy` and `IntermediateField.adjoin_le_iff`; then applies `AlgHom.ext`.
- **Hypotheses**: `F` finite; F-AlgHoms agree on generators.
- **Uses from project**: `algHomFieldEqualizer`, `functionField_eq_intermediateField_adjoin_xy`, `x_gen`, `y_gen`
- **Used by**: `translateAlgEquivOfPoint_pullback_invariance_of_xy` (line 678)
- **Visibility**: public
- **Lines**: 646–660, proof length 14
- **Notes**: Key lemma reducing generator-level equality to global equality.

---

### `theorem translateAlgEquivOfPoint_pullback_invariance_of_xy`
- **Type**: `[Fintype F] (β : ...) (k : W.toAffine.Point) (h_x : translateAlgEquivOfPoint W k (β.pullback (x_gen W)) = β.pullback (x_gen W)) (h_y : ...) : ∀ z, translateAlgEquivOfPoint W k (β.pullback z) = β.pullback z`
- **What**: Generator-restricted covariance reducer: if τ_k commutes with β.pullback on `x_gen` and `y_gen`, it does so on all of K(E).
- **How**: Frames the two sides as F-AlgHom composition/identity, applies `algHom_ext_of_eq_on_xy` to get equality, then uses `congrFun`/`congrArg`.
- **Hypotheses**: `F` finite; two generator-level equalities.
- **Uses from project**: `algHom_ext_of_eq_on_xy`, `translateAlgEquivOfPoint`, `x_gen`, `y_gen`
- **Used by**: `kernelTranslateAsAut_of_xy_invariance` (line 697), `pullback_fieldRange_le_fixedField_of_xy_family` (line 856)
- **Visibility**: public
- **Lines**: 666–681, proof length 15
- **Notes**: None.

---

### `noncomputable def kernelTranslateAsAut_of_xy_invariance`
- **Type**: `[Fintype F] (β : ...) (k : β.kernel) (h_x : ...) (h_y : ...) : @AlgEquiv ... β.toAlgebra β.toAlgebra`
- **What**: Produces the `β.toAlgebra`-AlgEquiv from two generator-level invariance witnesses.
- **How**: Calls `kernelTranslateAsAut` with covariance obtained from `translateAlgEquivOfPoint_pullback_invariance_of_xy`.
- **Hypotheses**: `F` finite; kernel element `k`; x_gen and y_gen invariance.
- **Uses from project**: `kernelTranslateAsAut`, `translateAlgEquivOfPoint_pullback_invariance_of_xy`
- **Used by**: `kernelTranslateForwardAsAut_of_xy_family` (line 712)
- **Visibility**: public
- **Lines**: 687–697, proof length 10
- **Notes**: None.

---

### `noncomputable def kernelTranslateForwardAsAut_of_xy_family`
- **Type**: `[Fintype F] (β : ...) (h_xy_family : ∀ k : β.kernel, (...) ∧ (...)) : β.kernel → @AlgEquiv ... β.toAlgebra β.toAlgebra`
- **What**: Full forward-map family `β.kernel → Aut` from the xy-family invariance witnesses (requiring only two equalities per kernel element).
- **How**: `fun k => kernelTranslateAsAut_of_xy_invariance W β k (h_xy_family k).1 (h_xy_family k).2`.
- **Hypotheses**: `F` finite; xy-invariance family.
- **Uses from project**: `kernelTranslateAsAut_of_xy_invariance`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 702–713, proof length 11
- **Notes**: Unused in file.

---

### `theorem kernel_pullback_invariance_id`
- **Type**: `(k : (Isogeny.id W.toAffine).kernel) (z : W.toAffine.FunctionField) : translateAlgEquivOfPoint W k.val ((Isogeny.id W.toAffine).pullback z) = (Isogeny.id W.toAffine).pullback z`
- **What**: Concrete sanity check: for the identity isogeny (which has kernel = ⊥), the pullback-invariance holds trivially since the only kernel element is 0.
- **How**: Derives `k.val = 0` from `Isogeny.kernel_id` + `AddSubgroup.mem_bot`, then rewrites with `translateAlgEquivOfPoint_zero` and `rfl`.
- **Hypotheses**: `k` is in the kernel of `Isogeny.id`.
- **Uses from project**: `Isogeny.kernel_id`, `translateAlgEquivOfPoint_zero`, `translateAlgEquivOfPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 726–743, proof length 17
- **Notes**: Unused in file. Sanity check / framework-consumer example.

---

### `instance translateMulSemiringAction_smulCommClass`
- **Type**: `SMulCommClass (Multiplicative W.toAffine.Point) F W.toAffine.FunctionField`
- **What**: The translation action of `Multiplicative E.Point` on `K(E)` commutes with F-scalar multiplication (since each `translateAlgEquivOfPoint W k` is F-linear).
- **How**: Unfolds the smul and uses `Algebra.smul_def`, `map_mul`, and `AlgEquiv.commutes`.
- **Hypotheses**: `F` field, `W` elliptic.
- **Uses from project**: `translateAlgEquivOfPoint`
- **Used by**: `kernelMulSemiringAction_smulCommClass` (conceptually)
- **Visibility**: public (instance)
- **Lines**: 796–801, proof length 5
- **Notes**: None.

---

### `noncomputable instance kernelMulSemiringAction`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) : MulSemiringAction (Multiplicative β.kernel) W.toAffine.FunctionField`
- **What**: The restriction of the master translation action to `Multiplicative β.kernel`, giving a `MulSemiringAction` of the kernel on `K(E)`.
- **How**: `MulSemiringAction.compHom` along the inclusion `β.kernel → E.Point` (via `AddSubgroup.subtype` composed with `.toMultiplicative`).
- **Hypotheses**: `F` field, `W` elliptic, `β` self-isogeny.
- **Uses from project**: `translateMulSemiringAction_smulCommClass` (implicitly)
- **Used by**: `kernelMulSemiringAction_smulCommClass`, `kernelMulSemiringAction_smul`, `pullback_fieldRange_le_fixedField_of_xy_family`, `pullback_fieldRange_eq_fixedField_of_finrank_match`, `pullback_fieldRange_eq_fixedField_of_card_match`, `faithfulSMul_kernel_of_translate_inj`, `faithfulSMul_kernel`, `finrank_pullback_fieldRange_eq_degree` (via `Multiplicative β.kernel`), `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`
- **Visibility**: public (instance)
- **Lines**: 806–811, proof length 5
- **Notes**: Central infrastructure instance enabling Artin machinery.

---

### `instance kernelMulSemiringAction_smulCommClass`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) : SMulCommClass (Multiplicative β.kernel) F W.toAffine.FunctionField`
- **What**: The restricted kernel action commutes with F-scalars; inherits from the master action via the inclusion.
- **How**: Same argument as `translateMulSemiringAction_smulCommClass` but via `.val`.
- **Hypotheses**: Same as `kernelMulSemiringAction`.
- **Uses from project**: `translateAlgEquivOfPoint`
- **Used by**: unused in file (used via instance synthesis)
- **Visibility**: public (instance)
- **Lines**: 815–821, proof length 6
- **Notes**: None.

---

### `@[simp] theorem kernelMulSemiringAction_smul`
- **Type**: `(β : ...) (g : Multiplicative β.kernel) (f : W.toAffine.FunctionField) : g • f = translateAlgEquivOfPoint W (Multiplicative.toAdd g).val f`
- **What**: Reduces the restricted kernel action smul to `translateAlgEquivOfPoint`.
- **How**: `rfl`.
- **Hypotheses**: None beyond context.
- **Uses from project**: `kernelMulSemiringAction`, `translateAlgEquivOfPoint`
- **Used by**: `pullback_fieldRange_le_fixedField_of_xy_family` (line 854)
- **Visibility**: public
- **Lines**: 825–828, proof length 3
- **Notes**: None.

---

### `theorem pullback_fieldRange_le_fixedField_of_xy_family`
- **Type**: `[Fintype F] (β : ...) (h_xy_family : ...) : β.pullback.fieldRange ≤ FixedPoints.intermediateField (Multiplicative β.kernel)`
- **What**: Forward inclusion of the Galois fixed-field theorem: every element in the image of `β.pullback` is fixed by the kernel translation action, given the xy-invariance family.
- **How**: Unfolds membership, changes the smul via `kernelMulSemiringAction_smul`, then applies `translateAlgEquivOfPoint_pullback_invariance_of_xy`.
- **Hypotheses**: `F` finite; xy-invariance family.
- **Uses from project**: `kernelMulSemiringAction_smul`, `translateAlgEquivOfPoint_pullback_invariance_of_xy`, `kernelMulSemiringAction`
- **Used by**: `pullback_fieldRange_eq_fixedField_of_finrank_match` (line 920), `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic` (indirectly)
- **Visibility**: public
- **Lines**: 842–859, proof length 17
- **Notes**: None.

---

### `theorem xy_family_zero`
- **Type**: `(β : ...) (h_zero_mem : (0 : W.toAffine.Point) ∈ β.kernel) : (...x_gen invariance...) ∧ (...y_gen invariance...)`
- **What**: The xy-invariance family at the zero kernel element holds trivially since `τ_0 = refl`.
- **How**: `⟨rfl, rfl⟩`.
- **Hypotheses**: Zero in `β.kernel`.
- **Uses from project**: `translateAlgEquivOfPoint`, `x_gen`, `y_gen`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 875–882, proof length 7
- **Notes**: Unused in file. Trivial sanity check.

---

### `theorem pullback_fieldRange_eq_fixedField_of_finrank_match`
- **Type**: `[Fintype F] (β : ...) [hfindim : FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField] (h_xy_family : ...) (h_finrank_match : Module.finrank ↥β.pullback.fieldRange W.toAffine.FunctionField = Module.finrank ↥FixedPoints... W.toAffine.FunctionField) : β.pullback.fieldRange = FixedPoints.intermediateField (Multiplicative β.kernel)`
- **What**: Layer 2 closure: from the forward inclusion + finrank equality, the intermediate fields are equal.
- **How**: Direct application of `IntermediateField.eq_of_le_of_finrank_eq'` to `pullback_fieldRange_le_fixedField_of_xy_family`.
- **Hypotheses**: `F` finite; finite-dimensional; xy-invariance family; finrank equality.
- **Uses from project**: `pullback_fieldRange_le_fixedField_of_xy_family`
- **Used by**: `pullback_fieldRange_eq_fixedField_of_card_match` (line 948)
- **Visibility**: public
- **Lines**: 902–921, proof length 19
- **Notes**: None.

---

### `theorem pullback_fieldRange_eq_fixedField_of_card_match`
- **Type**: `[Fintype F] (β : ...) [hfin_ker : Fintype (Multiplicative β.kernel)] [hfaith : FaithfulSMul ...] [hfindim : FiniteDimensional ...] (h_xy_family : ...) (h_pullback_finrank : Module.finrank ↥β.pullback.fieldRange W.toAffine.FunctionField = Fintype.card (Multiplicative β.kernel)) : β.pullback.fieldRange = FixedPoints.intermediateField ...`
- **What**: Packaged Artin-route closure: uses Mathlib's `FixedPoints.finrank_eq_card` (faithful + finite action gives `[K(E) : FixedPoints] = |G|`) to convert from cardinality match to finrank match.
- **How**: Calls `pullback_fieldRange_eq_fixedField_of_finrank_match`; proves the finrank match by rewriting with `h_pullback_finrank` and applying `FixedPoints.finrank_eq_card` symmetrically.
- **Hypotheses**: `F` finite; faithful + finite kernel action; finite-dimensional; xy-invariance; finrank-of-pullback equals kernel card.
- **Uses from project**: `pullback_fieldRange_eq_fixedField_of_finrank_match`
- **Used by**: `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic` (line 1098)
- **Visibility**: public
- **Lines**: 932–955, proof length 23
- **Notes**: None.

---

### `theorem faithfulSMul_kernel_of_translate_inj`
- **Type**: `(β : ...) (h_inj : ∀ k₁ k₂ : β.kernel, (∀ f, translateAlgEquivOfPoint W k₁.val f = translateAlgEquivOfPoint W k₂.val f) → k₁ = k₂) : FaithfulSMul (Multiplicative β.kernel) W.toAffine.FunctionField`
- **What**: Bundles pointwise injectivity of translation into Mathlib's `FaithfulSMul` typeclass.
- **How**: Unfolds `eq_of_smul_eq_smul`, uses `h_inj` and `Multiplicative.toAdd.injective`.
- **Hypotheses**: Injectivity witness: pointwise-equal translations come from equal kernel elements.
- **Uses from project**: `translateAlgEquivOfPoint`, `kernelMulSemiringAction`
- **Used by**: `faithfulSMul_kernel` (line 1012)
- **Visibility**: public
- **Lines**: 985–998, proof length 13
- **Notes**: None.

---

### `instance faithfulSMul_kernel`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) : FaithfulSMul (Multiplicative β.kernel) W.toAffine.FunctionField`
- **What**: Unconditional `FaithfulSMul` instance for any isogeny kernel over a finite field, using `translateAlgEquivOfPoint_injective` from `EC/TranslationOrd`.
- **How**: Applies `faithfulSMul_kernel_of_translate_inj` and discharges the injectivity via `AlgEquiv.ext` + `translateAlgEquivOfPoint_injective` + `Subtype.ext`.
- **Hypotheses**: `F` finite, `W` elliptic; no additional substantive hypotheses — unconditional.
- **Uses from project**: `faithfulSMul_kernel_of_translate_inj`, `translateAlgEquivOfPoint_injective`, `translateAlgEquivOfPoint`
- **Used by**: Used by `pullback_fieldRange_eq_fixedField_of_card_match` via instance synthesis
- **Visibility**: public (instance)
- **Lines**: 1009–1019, proof length 10
- **Notes**: Key unconditional instance enabling Artin machinery.

---

### `theorem finrank_pullback_fieldRange_eq_degree`
- **Type**: `(β : Isogeny W.toAffine W.toAffine) : Module.finrank ↥β.pullback.fieldRange W.toAffine.FunctionField = β.degree`
- **What**: Intrinsic finrank relation: the degree of `K(E_cod)` over `β.pullback.fieldRange` (= image of β.pullback) equals β.degree. This is the "codimension of pullback image = degree" fact.
- **How**: Uses `AlgEquiv.ofInjective β.pullback β.pullback_injective` to get `K(E_cod) ≃ₐ β.pullback.range`, builds a bridge `RingEquiv` from `.range` to `.fieldRange` (definitional), forms the composed `RingEquiv i` and identity `j`, checks compatibility via `rfl`, and applies `Algebra.finrank_eq_of_equiv_equiv`.
- **Hypotheses**: `F` field, `W` elliptic, `β` self-isogeny.
- **Uses from project**: `Isogeny.degree`, `Isogeny.pullback_injective`
- **Used by**: `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic` (line 1099)
- **Visibility**: public
- **Lines**: 1046–1076, proof length 30
- **Notes**: Proof exactly 30 lines long (boundary case). Uses `Algebra.finrank_eq_of_equiv_equiv` from mathlib. Constructs a bridge `RingEquiv` manually.

---

### `theorem pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`
- **Type**: `[Fintype F] (β : ...) [hfin_ker : Fintype (Multiplicative β.kernel)] [hfindim : FiniteDimensional ...] (h_xy_family : ...) (h_card_eq_degree : Fintype.card (Multiplicative β.kernel) = β.degree) : β.pullback.fieldRange = FixedPoints.intermediateField ...`
- **What**: Layer 2 closure with the intrinsic finrank discharged: from xy-family + cardinality match `|ker β| = deg β`, the pullback field range equals the fixed field of the kernel action.
- **How**: Calls `pullback_fieldRange_eq_fixedField_of_card_match` with `finrank_pullback_fieldRange_eq_degree` inserted to rewrite the finrank hypothesis.
- **Hypotheses**: `F` finite; finite kernel; finite-dimensional; xy-family; `|ker β| = deg β`.
- **Uses from project**: `pullback_fieldRange_eq_fixedField_of_card_match`, `finrank_pullback_fieldRange_eq_degree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1085–1099, proof length 14
- **Notes**: Unused in file — main bundled result.

---

### `theorem isogeny_pullback_algebraMap_K`
- **Type**: `(β : Isogeny V.toAffine V.toAffine) (c : KK) : β.pullback (algebraMap KK V.toAffine.FunctionField c) = algebraMap KK V.toAffine.FunctionField c`
- **What**: Any K-AlgHom pullback fixes K-constants (elements in the image of `algebraMap K K(E)`).
- **How**: `β.pullback.commutes c` (directly applies `AlgHom.commutes`).
- **Hypotheses**: `KK` finite field, `V` elliptic over `KK`, `β` self-isogeny.
- **Uses from project**: None.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1113–1117, proof length 4
- **Notes**: Unused in file. In a separate `section FrobeniusKE` with fresh variables `KK`, `V`.

---

## Summary

- **Total declarations**: 47
  - `def`/`noncomputable def`: 12
  - `theorem`/`@[simp] theorem`: 31
  - `instance`/`noncomputable instance`: 4
- **Sorries**: none
- **`set_option maxHeartbeats`**: none
- **Long proofs (>30 lines)**: none (longest is `finrank_pullback_fieldRange_eq_degree` at 30 lines exactly)
- **Key API** (used by 3+ others in file): `kernel_eq_top_of_hom_eq_id_sub_frobenius` (used in 3+ proofs), `translateAlgEquivOfPoint` (used throughout), `kernelTranslateAsAut` (used in 4 defs/theorems), `pullback_fieldRange_le_fixedField_of_xy_family` (used in 2 closures), `fiber_witness_of_separable_and_degree_eq_pointCount` (used in chain)
- **Unused in file** (possible dead-code): `omegaPullbackCoeff_of_pullback_eq_id`, `pointCount_eq_of_hom_kernel_witness`, `aut_of_kernel_zero_apply`, `aut_of_kernel_construction_witness`, `kernelTranslateForwardAsAut`, `kernelTranslateForward_zero`, `kernelTranslateAsAut_zero`, `kernelTranslateAsAut_apply`, `mem_algHomFieldEqualizer`, `kernelTranslateForwardAsAut_of_xy_family`, `kernel_pullback_invariance_id`, `fiber_witness_via_inverse_witnesses`, `kernelMulSemiringAction_smulCommClass`, `xy_family_zero`, `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`, `isogeny_pullback_algebraMap_K`
