# Inventory: ./HasseWeil/EC/IsogenyKernel.lean

**File**: `HasseWeil/EC/IsogenyKernel.lean`
**Lines**: 643
**Imports**: `HasseWeil.Basic`, `Mathlib.FieldTheory.SeparableDegree`, `Mathlib.FieldTheory.Galois.Basic`
**Namespace**: `HasseWeil.Isogeny` (most decls), one decl in `_root_` (Finset.sum_eq_card_mul_of_constant)
**No `sorry`, no `set_option maxHeartbeats`.**

---

### `noncomputable def kernel`
- **Type**: `(φ : Isogeny W₁ W₂) : AddSubgroup W₁.Point`
- **What**: Defines the kernel of an isogeny as an `AddSubgroup` of `W₁.Point`, wrapping `φ.toAddMonoidHom.ker`.
- **How**: One-line delegation to `AddMonoidHom.ker`.
- **Hypotheses**: `W₁`, `W₂` elliptic curves over a field `F`.
- **Uses from project**: `Isogeny.toAddMonoidHom` (via `HasseWeil.Basic`)
- **Used by**: `zero_mem_kernel`, `kernel_comp_le`, `kernel_finite_of_fiber_finite`, `kernel_mulByInt_one/zero/le_mul/neg`, `mem_kernel_comp_of_mem_kernel`, `kernel_comp_of_kernel_eq_bot`, `kernel_finite_of_point_finite`, `kernel_card_le_point_card`, `kernel_card_dvd_point_card`, `kernel_inf_le_kernel_of_sum`, `kernel_eq_bot_iff_injective`, `kernel_comp_eq_comap`, `fiber_eq_coset`, `fiberEquivKernel`, `kernel_equiv_fiber_zero`, `fiber_card_eq_kernel_card`, `kernel_id`, nearly all theorems in the file
- **Visibility**: public
- **Lines**: 51–52, proof length: 1 line (term)
- **Notes**: none

---

### `@[simp] theorem mem_kernel_iff`
- **Type**: `(φ : Isogeny W₁ W₂) (P : W₁.Point) : P ∈ φ.kernel ↔ φ.toAddMonoidHom P = 0`
- **What**: The membership criterion for the kernel: `P ∈ ker φ` iff `φ(P) = 0`.
- **How**: One-line term proof via `AddMonoidHom.mem_ker`.
- **Hypotheses**: none beyond variables.
- **Uses from project**: `kernel`
- **Used by**: virtually every theorem in the file that reasons about kernel membership
- **Visibility**: public
- **Lines**: 54–56, proof length: 1 line (term)
- **Notes**: keyApi — referenced by 10+ declarations in file.

---

### `@[simp] theorem zero_mem_kernel`
- **Type**: `(φ : Isogeny W₁ W₂) : (0 : W₁.Point) ∈ φ.kernel`
- **What**: The identity point is always in the kernel.
- **How**: Direct from `φ.kernel.zero_mem` (subgroup axiom).
- **Hypotheses**: none.
- **Uses from project**: `kernel`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 58–59, proof length: 1 line (term)
- **Notes**: none

---

### `theorem kernel_comp_le`
- **Type**: `(ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) : φ.kernel ≤ (ψ.comp φ).kernel`
- **What**: The kernel of φ is contained in the kernel of ψ∘φ (since ψ(0)=0).
- **How**: `simp` on `mem_kernel_iff` + `comp_apply`, then `rw [hP, map_zero]`.
- **Hypotheses**: W₃ also elliptic.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `Isogeny.comp`, `comp_apply`
- **Used by**: `mem_kernel_comp_of_mem_kernel`
- **Visibility**: public
- **Lines**: 62–68, proof length: 5 lines

---

### `theorem kernel_finite_of_fiber_finite`
- **Type**: `(φ : Isogeny W₁ W₂) (h_fiber : Finite {P : W₁.Point // φ.toAddMonoidHom P = 0}) : Finite φ.kernel`
- **What**: If the fiber over 0 (as a subtype) is finite, then the kernel (as an AddSubgroup) is finite.
- **How**: Constructs an explicit `Equiv` between `φ.kernel` and the fiber subtype using `mem_kernel_iff`, then applies `Finite.of_equiv`.
- **Hypotheses**: Finiteness of the zero-fiber subtype.
- **Uses from project**: `kernel`, `mem_kernel_iff`
- **Used by**: unused in file (useful as a witness-parametric T-III-4-011 form for downstream consumers)
- **Visibility**: public
- **Lines**: 88–97, proof length: 8 lines

---

### `@[simp] theorem kernel_mulByInt_one`
- **Type**: `(mulByInt W.toAffine 1).kernel = ⊥`
- **What**: The kernel of the identity-multiplication isogeny `[1]` is trivial.
- **How**: `ext P` + `simp` using `mem_kernel_iff`, `mulByInt_apply`, `one_zsmul`.
- **Hypotheses**: W a Weierstrass curve with elliptic affine model.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `mulByInt`, `mulByInt_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 104–107, proof length: 3 lines

---

### `@[simp] theorem kernel_mulByInt_zero`
- **Type**: `(mulByInt W.toAffine 0).kernel = ⊤`
- **What**: The kernel of `[0]` is the entire point group.
- **How**: `ext P` + `simp` using `mem_kernel_iff`, `mulByInt_apply`, `zero_zsmul`.
- **Hypotheses**: W a Weierstrass curve with elliptic affine model.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `mulByInt`, `mulByInt_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 110–113, proof length: 3 lines

---

### `theorem kernel_mulByInt_le_mul`
- **Type**: `(m n : ℤ) : (mulByInt W.toAffine n).kernel ≤ (mulByInt W.toAffine (m * n)).kernel`
- **What**: Every n-torsion point is also mn-torsion: `ker [n] ≤ ker [mn]`.
- **How**: `simp` on `mem_kernel_iff`/`mulByInt_apply`, then `rw [mul_smul, hP, smul_zero]`.
- **Hypotheses**: W a Weierstrass curve with elliptic affine model.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `mulByInt`, `mulByInt_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 116–121, proof length: 5 lines

---

### `theorem kernel_mulByInt_neg`
- **Type**: `(m : ℤ) : (mulByInt W.toAffine (-m)).kernel = (mulByInt W.toAffine m).kernel`
- **What**: `ker [-m] = ker [m]` (negation doesn't change the kernel).
- **How**: `ext P` + `simp` using `neg_zsmul` and `neg_eq_zero`.
- **Hypotheses**: W a Weierstrass curve with elliptic affine model.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `mulByInt`, `mulByInt_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 124–128, proof length: 4 lines

---

### `theorem mem_kernel_comp_of_mem_kernel`
- **Type**: `(ψ : Isogeny W₂ W₃) {φ : Isogeny W₁ W₂} {P : W₁.Point} (hP : P ∈ φ.kernel) : P ∈ (ψ.comp φ).kernel`
- **What**: Reformulation of `kernel_comp_le` for membership: if `P ∈ ker φ` then `P ∈ ker(ψ∘φ)`.
- **How**: Direct application of `kernel_comp_le`.
- **Hypotheses**: W₃ elliptic; P in φ.kernel.
- **Uses from project**: `kernel`, `kernel_comp_le`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132–135, proof length: 1 line (term)

---

### `theorem kernel_comp_of_kernel_eq_bot`
- **Type**: `{ψ : Isogeny W₂ W₃} (hψ : ψ.kernel = ⊥) (φ : Isogeny W₁ W₂) : (ψ.comp φ).kernel = φ.kernel`
- **What**: If ψ is a monomorphism (trivial kernel), then `ker(ψ∘φ) = ker φ`.
- **How**: `ext P`, case split: forward direction uses `mem_kernel_iff ψ` + `hψ`, reverse uses `map_zero`.
- **Hypotheses**: ψ has trivial kernel; W₃ elliptic.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `Isogeny.comp`, `comp_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 139–150, proof length: 11 lines

---

### `instance kernel_finite_of_point_finite`
- **Type**: `[Finite W₁.Point] (φ : Isogeny W₁ W₂) : Finite φ.kernel`
- **What**: When the whole point group is finite (e.g. over a finite field), every kernel is automatically finite.
- **How**: `inferInstance` (subgroup of a finite type is finite by Mathlib).
- **Hypotheses**: `W₁.Point` finite.
- **Uses from project**: `kernel`
- **Used by**: `kernel_finite_of_point_finite_named`, `kernel_card_le_point_card`, `kernel_card_dvd_point_card`
- **Visibility**: public
- **Lines**: 155–157, proof length: 1 line (term)
- **Notes**: keyApi for finite-field downstream.

---

### `theorem kernel_finite_of_point_finite_named`
- **Type**: `[Finite W₁.Point] (φ : Isogeny W₁ W₂) : Finite φ.kernel`
- **What**: Named theorem form of `kernel_finite_of_point_finite`; same content.
- **How**: `inferInstance`.
- **Hypotheses**: `W₁.Point` finite.
- **Uses from project**: `kernel`, `kernel_finite_of_point_finite` (implicit)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 161–163, proof length: 1 line (term)
- **Notes**: Suspected near-duplicate of the instance above; may be dead code.

---

### `theorem kernel_card_le_point_card`
- **Type**: `[Finite W₁.Point] (φ : Isogeny W₁ W₂) : Nat.card φ.kernel ≤ Nat.card W₁.Point`
- **What**: Cardinality of the kernel is at most the cardinality of the point group.
- **How**: `Nat.card_le_card_of_injective` with `Subtype.val_injective`.
- **Hypotheses**: `W₁.Point` finite.
- **Uses from project**: `kernel`, `kernel_finite_of_point_finite`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 166–168, proof length: 1 line (term)

---

### `theorem kernel_card_dvd_point_card`
- **Type**: `[Finite W₁.Point] (φ : Isogeny W₁ W₂) : Nat.card φ.kernel ∣ Nat.card W₁.Point`
- **What**: Lagrange's theorem for the kernel: `#ker φ ∣ #W₁.Point`.
- **How**: Lifts to multiplicative setting via `AddSubgroup.toSubgroup` and applies `Subgroup.card_subgroup_dvd_card`, then transports cardinalities via `Nat.card_congr` with `Multiplicative.ofAdd`.
- **Hypotheses**: `W₁.Point` finite.
- **Uses from project**: `kernel`, `kernel_finite_of_point_finite`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 173–179, proof length: 5 lines

---

### `theorem kernel_inf_le_kernel_of_sum`
- **Type**: `(φ ψ σ : Isogeny W₁ W₂) (hσ : σ.toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom) : φ.kernel ⊓ ψ.kernel ≤ σ.kernel`
- **What**: If `σ(P) = φ(P) + ψ(P)` and `P` is in both `ker φ` and `ker ψ`, then `P ∈ ker σ`.
- **How**: `simp` on `AddSubgroup.mem_inf`/`mem_kernel_iff`, then rewrites through `hσ` and uses `hP.1, hP.2`.
- **Hypotheses**: The group-homomorphism identity `σ = φ + ψ` as an AddMonoidHom.
- **Uses from project**: `kernel`, `mem_kernel_iff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 184–193, proof length: 9 lines

---

### `theorem kernel_eq_bot_iff_injective`
- **Type**: `(φ : Isogeny W₁ W₂) : φ.kernel = ⊥ ↔ Function.Injective φ.toAddMonoidHom`
- **What**: Trivial kernel is equivalent to injectivity of the underlying AddMonoidHom.
- **How**: Direct application of `AddMonoidHom.ker_eq_bot_iff`.
- **Hypotheses**: none beyond variables.
- **Uses from project**: `kernel`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 196–198, proof length: 1 line (term)

---

### `theorem id_toAddMonoidHom_injective`
- **Type**: `Function.Injective (Isogeny.id W₁).toAddMonoidHom`
- **What**: The identity isogeny's AddMonoidHom is injective.
- **How**: `Function.injective_id`.
- **Hypotheses**: none.
- **Uses from project**: `Isogeny.id`
- **Used by**: `kernel_id` (implicitly via simp set)
- **Visibility**: public
- **Lines**: 201–203, proof length: 1 line (term)

---

### `theorem kernel_comp_eq_comap`
- **Type**: `(ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) : (ψ.comp φ).kernel = ψ.kernel.comap φ.toAddMonoidHom`
- **What**: The kernel of ψ∘φ is the preimage of `ker ψ` under φ (as AddSubgroups).
- **How**: `ext P` + `simp` on `mem_kernel_iff`/`comp_apply`/`AddSubgroup.mem_comap`.
- **Hypotheses**: W₃ elliptic.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `Isogeny.comp`, `comp_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 207–211, proof length: 3 lines

---

### `theorem fiber_eq_coset`
- **Type**: `(φ : Isogeny W₁ W₂) {P₀ Q} (hP₀ : φ P₀ = Q) : {P | φ P = Q} = {P | ∃ T ∈ φ.kernel, P = P₀ + T}`
- **What**: The fiber over Q equals the coset `P₀ + ker φ` (as sets).
- **How**: `ext P`, constructs `P - P₀ ∈ ker φ` using `map_sub`/`mem_kernel_iff`; back direction uses `map_add`.
- **Hypotheses**: A base point `P₀` with `φ(P₀) = Q`.
- **Uses from project**: `kernel`, `mem_kernel_iff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 216–228, proof length: 12 lines

---

### `theorem mem_fiber_iff_sub_mem_kernel`
- **Type**: `(φ : Isogeny W₁ W₂) {P₀ Q} (hP₀ : φ P₀ = Q) (P : W₁.Point) : φ P = Q ↔ P - P₀ ∈ φ.kernel`
- **What**: P is in the fiber over Q iff P - P₀ is in the kernel.
- **How**: `rw [mem_kernel_iff, map_sub, hP₀, sub_eq_zero]`.
- **Hypotheses**: A base point `P₀` with `φ(P₀) = Q`.
- **Uses from project**: `kernel`, `mem_kernel_iff`
- **Used by**: `fiberEquivKernel`
- **Visibility**: public
- **Lines**: 243–246, proof length: 2 lines

---

### `noncomputable def fiberEquivKernel`
- **Type**: `(φ : Isogeny W₁ W₂) {P₀ Q} (hP₀ : φ P₀ = Q) : {P // φ P = Q} ≃ φ.kernel`
- **What**: An explicit bijection between any nonempty fiber and the kernel (coset bijection).
- **How**: Explicit `Equiv` record: `toFun = P ↦ P - P₀`, `invFun = T ↦ P₀ + T`, with `left_inv`/`right_inv` by `simp`.
- **Hypotheses**: A base point `P₀` with `φ(P₀) = Q`.
- **Uses from project**: `kernel`, `mem_fiber_iff_sub_mem_kernel`, `mem_kernel_iff`
- **Used by**: `fiber_finite_of_kernel_finite`, `fiberEquivFiber`, `kernel_equiv_fiber_zero`, `fiber_card_eq_kernel_card`
- **Visibility**: public
- **Lines**: 252–259, proof length: 7 lines (structure literal)
- **Notes**: keyApi — used by 4 downstream declarations.

---

### `theorem fiber_finite_of_kernel_finite`
- **Type**: `(φ : Isogeny W₁ W₂) (h_ker : Finite φ.kernel) {Q : W₂.Point} : Finite {P // φ P = Q}`
- **What**: If the kernel is finite, every fiber is finite (empty fibers trivially, nonempty fibers via coset bijection).
- **How**: `Classical.em` on existence of a point in the fiber; nonempty case uses `Finite.of_equiv` via `fiberEquivKernel`; empty case constructs `IsEmpty` and applies `Finite.of_equiv Empty`.
- **Hypotheses**: `Finite φ.kernel`.
- **Uses from project**: `kernel`, `fiberEquivKernel`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 263–271, proof length: 9 lines

---

### `noncomputable def fiberEquivFiber`
- **Type**: `(φ : Isogeny W₁ W₂) {P₀ Q} (hP₀ : φ P₀ = Q) {P₁ Q'} (hP₁ : φ P₁ = Q') : {P // φ P = Q} ≃ {P // φ P = Q'}`
- **What**: Any two nonempty fibers of φ are in bijection (both are cosets of ker φ).
- **How**: Composition `(fiberEquivKernel φ hP₀).trans (fiberEquivKernel φ hP₁).symm`.
- **Hypotheses**: Base points in each fiber.
- **Uses from project**: `fiberEquivKernel`
- **Used by**: unused in file (documented as the T-III-4-012 tool, but not called)
- **Visibility**: public
- **Lines**: 275–280, proof length: 1 line (term)

---

### `noncomputable def kernel_equiv_fiber_zero`
- **Type**: `(φ : Isogeny W₁ W₂) : φ.kernel ≃ {P // φ P = 0}`
- **What**: The kernel is canonically isomorphic to the fiber over 0 (specialisation of `fiberEquivKernel` at `P₀ = 0`).
- **How**: `(fiberEquivKernel φ (by simp : φ 0 = 0)).symm`.
- **Hypotheses**: none beyond variables.
- **Uses from project**: `fiberEquivKernel`
- **Used by**: `kernel_card_eq_fiber_zero_card`
- **Visibility**: public
- **Lines**: 290–292, proof length: 1 line (term)

---

### `theorem kernel_card_eq_fiber_zero_card`
- **Type**: `(φ : Isogeny W₁ W₂) [Finite φ.kernel] : Nat.card φ.kernel = Nat.card {P // φ P = 0}`
- **What**: Cardinality of kernel equals cardinality of the zero-fiber.
- **How**: `Nat.card_eq_of_bijective _ (kernel_equiv_fiber_zero φ).bijective`.
- **Hypotheses**: `Finite φ.kernel`.
- **Uses from project**: `kernel`, `kernel_equiv_fiber_zero`
- **Used by**: `kernel_card_eq_sepDegree_of_fiber_zero_witness`
- **Visibility**: public
- **Lines**: 297–301, proof length: 1 line (term)

---

### `theorem fiber_card_eq_kernel_card`
- **Type**: `(φ : Isogeny W₁ W₂) [Finite φ.kernel] {P₀ Q} (hP₀ : φ P₀ = Q) : Nat.card {P // φ P = Q} = Nat.card φ.kernel`
- **What**: Every nonempty fiber has the same cardinality as the kernel.
- **How**: Uses `Finite.of_equiv` via `fiberEquivKernel`, then chains `Nat.card_eq_of_equiv_fin` twice.
- **Hypotheses**: `Finite φ.kernel`; a base point in the fiber.
- **Uses from project**: `kernel`, `fiberEquivKernel`
- **Used by**: `fiber_card_eq_sepDegree_of_witness`, `fiber_witness_of_ker_card_eq_sepDegree`, `card_kernel_eq_degree_of_separable_witness`
- **Visibility**: public
- **Lines**: 306–314, proof length: 7 lines
- **Notes**: keyApi — used by 3 downstream theorems.

---

### `@[simp] theorem kernel_id`
- **Type**: `(Isogeny.id W₁).kernel = ⊥`
- **What**: The kernel of the identity isogeny is trivial.
- **How**: `ext P` + `simp` using `mem_kernel_iff`, `id_toAddMonoidHom`, `AddMonoidHom.id_apply`, `AddSubgroup.mem_bot`.
- **Hypotheses**: none.
- **Uses from project**: `kernel`, `mem_kernel_iff`, `id_toAddMonoidHom_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 317–320, proof length: 3 lines

---

### `def IsSeparable`
- **Type**: `(φ : Isogeny W₁ W₂) : Prop`
- **What**: `φ.IsSeparable` is definitionally `Algebra.IsSeparable W₂.FunctionField W₁.FunctionField` via `φ.toAlgebra` — the function-field extension is separable.
- **How**: One-line `def` unfolding to `@Algebra.IsSeparable` with `φ.toAlgebra`.
- **Hypotheses**: none beyond variables.
- **Uses from project**: `Isogeny.toAlgebra`, `WeierstrassCurve.Affine.FunctionField`
- **Used by**: `isSeparable_iff_sepDegree_eq_degree`, `card_kernel_eq_degree_of_separable_witness`, `degree_eq_sepDegree_mul_inSepDegree_of_separable`, `card_kernel_eq_degree_of_sepDegree_eq_card_kernel`, `ramificationIndex_eq_one_of_separable_witnesses`, `isGalois_of_isSeparable_and_normal`
- **Visibility**: public
- **Lines**: 329–330, proof length: 1 line (def body)
- **Notes**: keyApi — referenced by 6 downstream theorems.

---

### `noncomputable def sepDegree`
- **Type**: `(φ : Isogeny W₁ W₂) : ℕ`
- **What**: The separable degree of φ, defined as `Field.finSepDegree W₂.FunctionField W₁.FunctionField` via `φ.toAlgebra`.
- **How**: One-line delegation to `@Field.finSepDegree`.
- **Hypotheses**: none beyond variables.
- **Uses from project**: `Isogeny.toAlgebra`, `WeierstrassCurve.Affine.FunctionField`
- **Used by**: `sepDegree_dvd_degree`, `isSeparable_iff_sepDegree_eq_degree`, `fiber_card_eq_sepDegree_of_witness`, `fiber_witness_of_ker_card_eq_sepDegree`, `kernel_card_eq_sepDegree_of_fiber_zero_witness`, `card_kernel_eq_degree_of_separable_witness`, `degree_eq_sepDegree_mul_inSepDegree_of_separable`, `sepDegree_eq_card_emb`, `card_kernel_eq_degree_of_sepDegree_eq_card_kernel`, `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`, `ramificationIndex_eq_insepDegree_of_witnesses`, `ramificationIndex_eq_one_of_separable_witnesses`
- **Visibility**: public
- **Lines**: 336–337, proof length: 1 line (def body)
- **Notes**: keyApi — the most widely used declaration in the file.

---

### `theorem sepDegree_dvd_degree`
- **Type**: `(φ : Isogeny W₁ W₂) : φ.sepDegree ∣ φ.degree`
- **What**: The separable degree divides the total degree of φ.
- **How**: Direct application of `Field.finSepDegree_dvd_finrank` via `φ.toAlgebra`.
- **Hypotheses**: none.
- **Uses from project**: `sepDegree`, `Isogeny.degree`, `Isogeny.toAlgebra`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 340–342, proof length: 1 line (term)

---

### `theorem isSeparable_iff_sepDegree_eq_degree`
- **Type**: `(φ : Isogeny W₁ W₂) (hfin : FiniteDimensional ...) : φ.IsSeparable ↔ φ.sepDegree = φ.degree`
- **What**: A field-extension criterion: φ is separable iff separable degree = total degree.
- **How**: Application of `Field.finSepDegree_eq_finrank_iff` via `φ.toAlgebra hfin`, with `.symm`.
- **Hypotheses**: The function-field extension is finite-dimensional.
- **Uses from project**: `IsSeparable`, `sepDegree`, `Isogeny.degree`, `Isogeny.toAlgebra`
- **Used by**: `card_kernel_eq_degree_of_separable_witness`, `degree_eq_sepDegree_mul_inSepDegree_of_separable`, `card_kernel_eq_degree_of_sepDegree_eq_card_kernel`, `ramificationIndex_eq_one_of_separable_witnesses`
- **Visibility**: public
- **Lines**: 346–351, proof length: 3 lines (term)
- **Notes**: keyApi — used by 4 downstream theorems.

---

### `theorem fiber_card_eq_sepDegree_of_witness`
- **Type**: `(φ : Isogeny W₁ W₂) [Finite φ.kernel] (h_witness : ∃ P₀, Nat.card {P // φ P = φ P₀} = φ.sepDegree) : ∀ {P₀ Q} (_ : φ P₀ = Q), Nat.card {P // φ P = Q} = φ.sepDegree`
- **What**: If one fiber has cardinality = sepDegree, every nonempty fiber does (T-III-4-012 witness form).
- **How**: Extracts the witness, rewrites fiber cardinality to kernel cardinality twice via `fiber_card_eq_kernel_card`, then concludes.
- **Hypotheses**: `Finite φ.kernel`; existential witness that one fiber has size = `sepDegree`.
- **Uses from project**: `sepDegree`, `fiber_card_eq_kernel_card`
- **Used by**: `card_kernel_eq_degree_of_separable_witness`
- **Visibility**: public
- **Lines**: 369–380, proof length: 9 lines

---

### `theorem fiber_witness_of_ker_card_eq_sepDegree`
- **Type**: `(φ : Isogeny W₁ W₂) [Finite φ.kernel] (h_ker_sep : Nat.card φ.kernel = φ.sepDegree) : ∃ P₀, Nat.card {P // φ P = φ P₀} = φ.sepDegree`
- **What**: If `#ker = sepDegree`, then the zero-fiber provides the existential fiber witness.
- **How**: Uses `P₀ = 0`, rewrites via `fiber_card_eq_kernel_card`, then `h_ker_sep`.
- **Hypotheses**: `Finite φ.kernel`; `Nat.card φ.kernel = φ.sepDegree`.
- **Uses from project**: `kernel`, `sepDegree`, `fiber_card_eq_kernel_card`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 391–399, proof length: 7 lines

---

### `theorem kernel_card_eq_sepDegree_of_fiber_zero_witness`
- **Type**: `(φ : Isogeny W₁ W₂) [Finite φ.kernel] (h_fiber_card_zero : Nat.card {P // φ P = 0} = φ.sepDegree) : Nat.card φ.kernel = φ.sepDegree`
- **What**: If the zero-fiber has cardinality = sepDegree, then so does the kernel.
- **How**: `rw [kernel_card_eq_fiber_zero_card φ, h_fiber_card_zero]`.
- **Hypotheses**: `Finite φ.kernel`; zero-fiber has size = sepDegree.
- **Uses from project**: `kernel`, `sepDegree`, `kernel_card_eq_fiber_zero_card`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 408–413, proof length: 3 lines

---

### `theorem card_kernel_eq_degree_of_separable_witness`
- **Type**: `(φ : Isogeny W₁ W₂) [Finite φ.kernel] (hsep : φ.IsSeparable) (hfin : FiniteDimensional ...) (h_witness : ∃ P₀, ...) : Nat.card φ.kernel = φ.degree`
- **What**: T-III-4-015 witness form: for a separable φ with a fiber witness, `#ker = deg`.
- **How**: Derives `#ker = sepDegree` via `fiber_card_eq_sepDegree_of_witness` + `fiber_card_eq_kernel_card`; then `isSeparable_iff_sepDegree_eq_degree`.
- **Hypotheses**: `Finite φ.kernel`, `φ.IsSeparable`, finite-dimensional extension, one fiber witness.
- **Uses from project**: `kernel`, `sepDegree`, `IsSeparable`, `fiber_card_eq_sepDegree_of_witness`, `fiber_card_eq_kernel_card`, `isSeparable_iff_sepDegree_eq_degree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 419–435, proof length: 15 lines

---

### `theorem degree_eq_sepDegree_mul_inSepDegree_of_separable`
- **Type**: `(φ : Isogeny W₁ W₂) (hsep : φ.IsSeparable) (hfin : FiniteDimensional ...) : φ.degree = φ.sepDegree`
- **What**: For a separable isogeny, total degree equals separable degree.
- **How**: `((isSeparable_iff_sepDegree_eq_degree φ hfin).mp hsep).symm`.
- **Hypotheses**: `φ.IsSeparable` and finite-dimensional extension.
- **Uses from project**: `IsSeparable`, `sepDegree`, `Isogeny.degree`, `isSeparable_iff_sepDegree_eq_degree`
- **Used by**: `ramificationIndex_eq_one_of_separable_witnesses`
- **Visibility**: public
- **Lines**: 442–447, proof length: 2 lines (term)

---

### `theorem sepDegree_eq_card_emb`
- **Type**: `(φ : Isogeny W₁ W₂) : φ.sepDegree = Nat.card (W₁.FunctionField →ₐ[W₂.FunctionField] AlgebraicClosure W₁.FunctionField)` (with `letI := φ.toAlgebra`)
- **What**: Unfolds the definition of `sepDegree` as the count of algebra embeddings — the Mathlib definition of `finSepDegree`.
- **How**: `rfl` (definitional equality).
- **Hypotheses**: none.
- **Uses from project**: `sepDegree`, `Isogeny.toAlgebra`, `WeierstrassCurve.Affine.FunctionField`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 469–474, proof length: 1 line (term)

---

### `theorem card_kernel_eq_degree_of_sepDegree_eq_card_kernel`
- **Type**: `(φ : Isogeny W₁ W₂) (hsep : φ.IsSeparable) (hfin : FiniteDimensional ...) (h_count : φ.sepDegree = Nat.card φ.kernel) : Nat.card φ.kernel = φ.degree`
- **What**: R2 reduction brick: given the embedding↔kernel bijection hypothesis, derive `#ker = deg`.
- **How**: `rw [← h_count]; exact (isSeparable_iff_sepDegree_eq_degree φ hfin).mp hsep`.
- **Hypotheses**: `φ.IsSeparable`, finite-dimensional extension, embedding count = kernel count.
- **Uses from project**: `kernel`, `sepDegree`, `IsSeparable`, `Isogeny.degree`, `isSeparable_iff_sepDegree_eq_degree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 486–493, proof length: 5 lines

---

### `theorem _root_.Finset.sum_eq_card_mul_of_constant`
- **Type**: `{α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ} (heq : ∀ P ∈ S, e P = c) : ∑ P ∈ S, e P = (S.card : ℤ) * c`
- **What**: A combinatorial helper: if `e` is constant `c` on `S`, then `∑_{P ∈ S} e(P) = #S * c`.
- **How**: `rw [Finset.sum_congr rfl heq, Finset.sum_const]; simp`.
- **Hypotheses**: Finset `S`, constant function `e = c` on `S`.
- **Uses from project**: none (pure Mathlib)
- **Used by**: `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`
- **Visibility**: public (`_root_` namespace)
- **Lines**: 499–504, proof length: 4 lines
- **Notes**: Mathlib duplication suspicion — `Finset.sum_const` + `Finset.sum_congr` is standard mathlib; this may already exist as a lemma.

---

### `theorem ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`
- **Type**: `(φ : Isogeny W₁ W₂) {α S e c} (h_uniform) (h_sum) (h_card : S.card = φ.sepDegree) : (φ.sepDegree : ℤ) * c = (φ.degree : ℤ)`
- **What**: Witness-parametric T-III-4-013: given uniform ramification index `c`, sum = deg, fiber size = sepDegree, derive `sepDegree * c = deg`.
- **How**: `rw [← h_card]`, then `(Finset.sum_eq_card_mul_of_constant h_uniform).symm.trans h_sum`.
- **Hypotheses**: Uniform ramification, sum witness, fiber size = sepDegree.
- **Uses from project**: `sepDegree`, `Isogeny.degree`, `Finset.sum_eq_card_mul_of_constant`
- **Used by**: `ramificationIndex_eq_insepDegree_of_witnesses`, `ramificationIndex_eq_one_of_separable_witnesses`
- **Visibility**: public
- **Lines**: 522–530, proof length: 5 lines

---

### `theorem ramificationIndex_eq_insepDegree_of_witnesses`
- **Type**: `(φ : Isogeny W₁ W₂) (hs : φ.sepDegree ≠ 0) {α S e c} (h_uniform) (h_sum) (h_card) : (c : ℚ) = (φ.degree : ℚ) / (φ.sepDegree : ℚ)`
- **What**: Under the same witnesses as `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`, the common ramification index equals `deg / sepDegree` in ℚ.
- **How**: Casts the integer product identity to ℚ via `exact_mod_cast`, then `field_simp` + `linarith`.
- **Hypotheses**: `sepDegree ≠ 0`, all three witness conditions.
- **Uses from project**: `sepDegree`, `Isogeny.degree`, `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 535–547, proof length: 12 lines

---

### `theorem ramificationIndex_eq_one_of_separable_witnesses`
- **Type**: `(φ : Isogeny W₁ W₂) (hsep : φ.IsSeparable) (hfin : FiniteDimensional ...) (hs : φ.sepDegree ≠ 0) {α S e c} (h_uniform) (h_sum) (h_card) : c = 1`
- **What**: For a separable isogeny with all combinatorial witnesses, every ramification index in the fiber equals 1 (the isogeny is unramified).
- **How**: Derives `sepDegree * c = degree` (via `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`), then `degree = sepDegree` (via `degree_eq_sepDegree_mul_inSepDegree_of_separable`), so `sepDegree * c = sepDegree * 1`; cancels via `mul_left_cancel₀`.
- **Hypotheses**: `φ.IsSeparable`, finite-dimensional extension, `sepDegree ≠ 0`, three witnesses.
- **Uses from project**: `sepDegree`, `IsSeparable`, `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`, `degree_eq_sepDegree_mul_inSepDegree_of_separable`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 561–580, proof length: 19 lines

---

### `theorem card_aut_eq_degree_of_isGalois`
- **Type**: `(φ : Isogeny W₁ W₂) (hfin : FiniteDimensional ...) (hgal : IsGalois ...) : Nat.card (AlgEquiv ...) = φ.degree`
- **What**: T-III-4-015 step 3: given IsGalois for the function-field tower, `#Aut = deg φ`.
- **How**: Sets up `letI`/`haveI` instances, then applies `IsGalois.card_aut_eq_finrank`.
- **Hypotheses**: `FiniteDimensional` and `IsGalois` for the function-field extension.
- **Uses from project**: `Isogeny.degree`, `Isogeny.toAlgebra`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 597–606, proof length: 7 lines

---

### `theorem isGalois_of_separable_and_normal`
- **Type**: `(φ : Isogeny W₁ W₂) (h_sep : Algebra.IsSeparable ...) (h_normal : Normal ...) : @IsGalois ...`
- **What**: Constructs a `IsGalois` instance from `Algebra.IsSeparable` + `Normal` for the function-field tower.
- **How**: Sets up instances, then `isGalois_iff.mpr ⟨h_sep, h_normal⟩`.
- **Hypotheses**: Separability and normality of the function-field extension.
- **Uses from project**: `Isogeny.toAlgebra`
- **Used by**: `isGalois_of_isSeparable_and_normal`
- **Visibility**: public
- **Lines**: 616–625, proof length: 8 lines

---

### `theorem isGalois_of_isSeparable_and_normal`
- **Type**: `(φ : Isogeny W₁ W₂) (h_sep : φ.IsSeparable) (h_normal : Normal ...) : @IsGalois ...`
- **What**: Same as `isGalois_of_separable_and_normal` but taking `φ.IsSeparable` (project-style) as the separability hypothesis.
- **How**: Direct delegation to `isGalois_of_separable_and_normal φ h_sep h_normal`.
- **Hypotheses**: `φ.IsSeparable`, normality of function-field extension.
- **Uses from project**: `IsSeparable`, `isGalois_of_separable_and_normal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 634–639, proof length: 2 lines (term)

---

## Summary

| Category | Count |
|----------|-------|
| `def` / `noncomputable def` | 6 |
| `theorem` (incl. `@[simp]`) | 39 |
| `instance` | 1 |
| **Total** | **46** |

**No `sorry` anywhere in the file.**
**No `set_option maxHeartbeats`.**
**No proofs exceeding 30 lines.**

### Key API declarations (referenced by 3+ others in the file)
- `mem_kernel_iff` — used by 10+ declarations
- `kernel` (the def) — used by nearly all declarations
- `fiberEquivKernel` — used by 4 declarations
- `fiber_card_eq_kernel_card` — used by 3 declarations
- `IsSeparable` — used by 6 declarations
- `sepDegree` — used by 12+ declarations
- `isSeparable_iff_sepDegree_eq_degree` — used by 4 declarations

### Dead-code candidates (unused within this file)
`zero_mem_kernel`, `kernel_mulByInt_one`, `kernel_mulByInt_zero`, `kernel_mulByInt_le_mul`, `kernel_mulByInt_neg`, `mem_kernel_comp_of_mem_kernel`, `kernel_comp_of_kernel_eq_bot`, `kernel_finite_of_point_finite_named`, `kernel_card_le_point_card`, `kernel_card_dvd_point_card`, `kernel_inf_le_kernel_of_sum`, `kernel_eq_bot_iff_injective`, `kernel_comp_eq_comap`, `fiber_eq_coset`, `fiber_finite_of_kernel_finite`, `fiberEquivFiber`, `kernel_id`, `sepDegree_dvd_degree`, `fiber_witness_of_ker_card_eq_sepDegree`, `kernel_card_eq_sepDegree_of_fiber_zero_witness`, `card_kernel_eq_degree_of_separable_witness`, `sepDegree_eq_card_emb`, `card_kernel_eq_degree_of_sepDegree_eq_card_kernel`, `ramificationIndex_eq_insepDegree_of_witnesses`, `ramificationIndex_eq_one_of_separable_witnesses`, `card_aut_eq_degree_of_isGalois`, `isGalois_of_isSeparable_and_normal` (these are API intended for downstream files).
