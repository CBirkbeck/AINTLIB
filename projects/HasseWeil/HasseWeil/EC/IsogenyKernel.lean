/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableDegree
import HasseWeil.Basic

/-!
# Kernel of an Isogeny

For an isogeny `φ : E₁ → E₂`, we collect the structural facts about `ker φ`
as an `AddSubgroup` of `E₁.Point`. These are foundational for the dual
isogeny construction (Silverman III.6) and the Hasse bound (V.1).

## Main definitions

* `Isogeny.kernel φ` — the kernel of `φ.toAddMonoidHom`, viewed as an
  `AddSubgroup` of `W₁.Point`. A thin wrapper around `AddMonoidHom.ker`.
* `Isogeny.IsSeparable φ` — separability of the induced field extension.

## Deep results (not yet proved)

The following correspond to tickets `T-III-4-011/012/015`; they require
substantial infrastructure (finiteness of fibers for finite morphisms of
smooth curves, and the Galois theory of `K(E₁)/φ*K(E₂)`) and are deferred.

* **Silverman III.4.10(a)** — nonzero isogeny has finite kernel.
* **Silverman III.4.10(b)** — `#ker φ ≤ deg_s φ ≤ deg φ`.
* **Silverman III.4.10(c)** — equality when `φ` is separable.

Once available, these unblock the dual isogeny chain (T-III-6-001 etc.).

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10.

-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

namespace Isogeny

/-- The kernel of an isogeny `φ`, as an `AddSubgroup` of `W₁.Point`. -/
noncomputable def kernel (φ : Isogeny W₁ W₂) : AddSubgroup W₁.Point :=
  φ.toAddMonoidHom.ker

@[simp] theorem mem_kernel_iff (φ : Isogeny W₁ W₂) (P : W₁.Point) :
    P ∈ φ.kernel ↔ φ.toAddMonoidHom P = 0 :=
  AddMonoidHom.mem_ker

@[simp] theorem zero_mem_kernel (φ : Isogeny W₁ W₂) : (0 : W₁.Point) ∈ φ.kernel :=
  (φ.kernel).zero_mem

/-- The kernel is preserved by composition (fiberwise): `ker φ ⊆ ker (ψ ∘ φ)`. -/
theorem kernel_comp_le {W₃ : Affine F} [W₃.IsElliptic] (ψ : Isogeny W₂ W₃)
    (φ : Isogeny W₁ W₂) : φ.kernel ≤ (ψ.comp φ).kernel := by
  intro P hP
  simp only [mem_kernel_iff, comp_apply] at hP ⊢
  rw [hP, map_zero]

/-- **T-III-4-011 witness form**: If the fiber `φ⁻¹({0})` (as a subtype
    of `W₁.Point`) is finite, then `φ.kernel` is a finite additive subgroup.

    The hypothesis `h_fiber` is a specific case of T-II-2-002 (finite fibers
    for nonconstant morphisms of smooth curves) applied to the fiber over `0`.
    Full unconditional version awaits that foundational curve-theory result. -/
theorem kernel_finite_of_fiber_finite (φ : Isogeny W₁ W₂)
    (h_fiber : Finite {P : W₁.Point // φ.toAddMonoidHom P = 0}) :
    Finite φ.kernel :=
  Finite.of_equiv _ (Equiv.subtypeEquivRight (mem_kernel_iff φ)).symm

/-- `ker [1] = ⊥` (trivial kernel, since [1] is the identity on points). -/
@[simp] theorem kernel_mulByInt_one {W : WeierstrassCurve F} [W.toAffine.IsElliptic] :
    (mulByInt W.toAffine 1).kernel = ⊥ := by
  ext P
  simp [mem_kernel_iff, mulByInt_apply]

/-- `ker [0] = ⊤` (everything, since [0] sends everything to 0). -/
@[simp] theorem kernel_mulByInt_zero {W : WeierstrassCurve F} [W.toAffine.IsElliptic] :
    (mulByInt W.toAffine 0).kernel = ⊤ := by
  ext P
  simp [mem_kernel_iff, mulByInt_apply]

/-- `ker [n] ≤ ker [m·n]`: every `n`-torsion point is also `m·n`-torsion. -/
theorem kernel_mulByInt_le_mul {W : WeierstrassCurve F} [W.toAffine.IsElliptic] (m n : ℤ) :
    (mulByInt W.toAffine n).kernel ≤ (mulByInt W.toAffine (m * n)).kernel := by
  intro P hP
  simp only [mem_kernel_iff, mulByInt_apply] at hP ⊢
  rw [mul_smul, hP, smul_zero]

/-- `ker [m]` and `ker [-m]` coincide: `P ∈ ker [m] ↔ P ∈ ker [-m]`. -/
theorem kernel_mulByInt_neg {W : WeierstrassCurve F} [W.toAffine.IsElliptic] (m : ℤ) :
    (mulByInt W.toAffine (-m)).kernel = (mulByInt W.toAffine m).kernel := by
  ext P
  simp [mem_kernel_iff, mulByInt_apply]

/-- `ker φ ≤ ker (ψ ∘ φ)` reformulated: every element of `ker φ` is in the
    preimage of `0` under `ψ ∘ φ` (trivial since `ψ(0) = 0`). -/
theorem mem_kernel_comp_of_mem_kernel {W₃ : Affine F} [W₃.IsElliptic]
    (ψ : Isogeny W₂ W₃) {φ : Isogeny W₁ W₂} {P : W₁.Point}
    (hP : P ∈ φ.kernel) : P ∈ (ψ.comp φ).kernel :=
  kernel_comp_le ψ φ hP

/-- If `ψ` has trivial kernel, `ker (ψ ∘ φ) = ker φ`: applying a "monomorphic"
    post-composition doesn't enlarge the kernel. -/
theorem kernel_comp_of_kernel_eq_bot {W₃ : Affine F} [W₃.IsElliptic]
    {ψ : Isogeny W₂ W₃} (hψ : ψ.kernel = ⊥) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).kernel = φ.kernel := by
  ext P
  simp only [mem_kernel_iff, comp_apply]
  constructor
  · intro h
    have : φ.toAddMonoidHom P ∈ ψ.kernel := (mem_kernel_iff ψ _).mpr h
    rw [hψ, AddSubgroup.mem_bot] at this
    exact this
  · intro h
    rw [h, map_zero]

/-- **Kernel finiteness over finite fields (unconditional)**: when `W₁.Point`
    is finite (e.g., for an elliptic curve over a finite field), every kernel
    is automatically finite. -/
instance kernel_finite_of_point_finite [Finite W₁.Point] (φ : Isogeny W₁ W₂) :
    Finite φ.kernel :=
  inferInstance

/-- **T-III-4-011 for finite fields**: over F with Finite Point structure,
    every isogeny's kernel is automatically finite (named theorem form). -/
theorem kernel_finite_of_point_finite_named [Finite W₁.Point]
    (φ : Isogeny W₁ W₂) : Finite φ.kernel :=
  inferInstance

/-- **Cardinality bound**: over a finite field, `#ker φ ≤ #W₁.Point`. -/
theorem kernel_card_le_point_card [Finite W₁.Point] (φ : Isogeny W₁ W₂) :
    Nat.card φ.kernel ≤ Nat.card W₁.Point :=
  Nat.card_le_card_of_injective _ (Subtype.val_injective)

/-- **Lagrange for kernel**: over a finite field, `#ker φ ∣ #W₁.Point`
    (subgroup cardinality divides group cardinality). Via
    `Subgroup.card_subgroup_dvd_card` applied in multiplicative form. -/
theorem kernel_card_dvd_point_card [Finite W₁.Point] (φ : Isogeny W₁ W₂) :
    Nat.card φ.kernel ∣ Nat.card W₁.Point := by
  have := @Subgroup.card_subgroup_dvd_card (Multiplicative W₁.Point) _
    (AddSubgroup.toSubgroup φ.kernel)
  rwa [Nat.card_congr (Multiplicative.ofAdd : W₁.Point ≃ _).symm,
    Nat.card_congr (Equiv.refl _)] at this

/-- **Kernel of sum** (for AddSubgroup inclusion): `ker φ ∩ ker ψ ≤ ker (φ + ψ)`,
    where `(φ + ψ)` is a hypothetical isogeny with summed action.
    (Purely algebraic: if φ(P) = 0 and ψ(P) = 0, then φ(P) + ψ(P) = 0.) -/
theorem kernel_inf_le_kernel_of_sum (φ ψ : Isogeny W₁ W₂)
    (σ : Isogeny W₁ W₂) (hσ : σ.toAddMonoidHom = φ.toAddMonoidHom + ψ.toAddMonoidHom) :
    φ.kernel ⊓ ψ.kernel ≤ σ.kernel := by
  intro P hP
  simp only [AddSubgroup.mem_inf, mem_kernel_iff] at hP
  simp only [mem_kernel_iff, hσ, AddMonoidHom.add_apply, hP.1, hP.2, add_zero]

/-- An isogeny has trivial kernel iff its toAddMonoidHom is injective. -/
theorem kernel_eq_bot_iff_injective (φ : Isogeny W₁ W₂) :
    φ.kernel = ⊥ ↔ Function.Injective φ.toAddMonoidHom :=
  AddMonoidHom.ker_eq_bot_iff φ.toAddMonoidHom

/-- The identity isogeny's toAddMonoidHom is injective (trivial). -/
theorem id_toAddMonoidHom_injective :
    Function.Injective (Isogeny.id W₁).toAddMonoidHom :=
  Function.injective_id

/-- `ker (ψ ∘ φ) = φ⁻¹(ker ψ)` (as an AddSubgroup): the kernel of a composition
    is the preimage of the outer kernel. -/
theorem kernel_comp_eq_comap {W₃ : Affine F} [W₃.IsElliptic]
    (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).kernel = ψ.kernel.comap φ.toAddMonoidHom := by
  ext P
  simp [mem_kernel_iff]

/-- For a nonzero isogeny with finite kernel, the action of the kernel on
    any nonempty fiber is transitive. I.e., `φ⁻¹(Q) = P₀ + ker φ` as sets
    (when `φ(P₀) = Q`). -/
theorem fiber_eq_coset (φ : Isogeny W₁ W₂)
    {P₀ : W₁.Point} {Q : W₂.Point} (hP₀ : φ.toAddMonoidHom P₀ = Q) :
    {P : W₁.Point | φ.toAddMonoidHom P = Q} =
      {P : W₁.Point | ∃ T ∈ φ.kernel, P = P₀ + T} := by
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hP
    refine ⟨P - P₀, ?_, by abel⟩
    exact (mem_kernel_iff φ _).mpr (by
      rw [map_sub, hP, hP₀, sub_self])
  · rintro ⟨T, hT, rfl⟩
    rw [map_add, hP₀, (mem_kernel_iff φ T).mp hT, add_zero]

/-- **Fiber as coset**: `P ∈ φ⁻¹(Q)` iff `P - P₀ ∈ ker φ`, given
    `P₀ ∈ φ⁻¹(Q)`. -/
theorem mem_fiber_iff_sub_mem_kernel (φ : Isogeny W₁ W₂)
    {P₀ : W₁.Point} {Q : W₂.Point} (hP₀ : φ.toAddMonoidHom P₀ = Q) (P : W₁.Point) :
    φ.toAddMonoidHom P = Q ↔ P - P₀ ∈ φ.kernel := by
  rw [mem_kernel_iff, map_sub, hP₀, sub_eq_zero]

/-- **Fiber cardinality = kernel cardinality** (via coset structure): the
    fiber `φ⁻¹(Q)` of a nonempty fiber (with `P₀ ∈ φ⁻¹(Q)`) has the same
    cardinality as `ker φ`. This is the group-theoretic content of the
    fiber-cardinality formula (before invoking any ramification theory). -/
noncomputable def fiberEquivKernel (φ : Isogeny W₁ W₂)
    {P₀ : W₁.Point} {Q : W₂.Point} (hP₀ : φ.toAddMonoidHom P₀ = Q) :
    {P : W₁.Point // φ.toAddMonoidHom P = Q} ≃ φ.kernel where
  toFun := fun ⟨P, hP⟩ ↦ ⟨P - P₀, (mem_fiber_iff_sub_mem_kernel φ hP₀ P).mp hP⟩
  invFun := fun ⟨T, hT⟩ ↦ ⟨P₀ + T, by
    rw [map_add, hP₀, (mem_kernel_iff φ T).mp hT, add_zero]⟩
  left_inv := fun ⟨P, hP⟩ ↦ by simp
  right_inv := fun ⟨T, hT⟩ ↦ by simp

/-- **Corollary**: if `ker φ` is finite, every fiber of `φ` is finite
    (with the same cardinality as `ker φ`). -/
theorem fiber_finite_of_kernel_finite (φ : Isogeny W₁ W₂)
    (h_ker : Finite φ.kernel) {Q : W₂.Point} :
    Finite {P : W₁.Point // φ.toAddMonoidHom P = Q} := by
  rcases Classical.em (∃ P₀, φ.toAddMonoidHom P₀ = Q) with ⟨P₀, hP₀⟩ | h_empty
  · exact Finite.of_equiv _ (fiberEquivKernel φ hP₀).symm
  · haveI : IsEmpty {P : W₁.Point // φ.toAddMonoidHom P = Q} :=
      ⟨fun ⟨P, hP⟩ ↦ h_empty ⟨P, hP⟩⟩
    exact Finite.of_equiv Empty (Equiv.equivEmpty _).symm

/-- **Bijection of nonempty fibers**: any two nonempty fibers of `φ` are in
    bijection. (They're both cosets of the kernel, hence have the same size.) -/
noncomputable def fiberEquivFiber (φ : Isogeny W₁ W₂)
    {P₀ : W₁.Point} {Q : W₂.Point} (hP₀ : φ.toAddMonoidHom P₀ = Q)
    {P₁ : W₁.Point} {Q' : W₂.Point} (hP₁ : φ.toAddMonoidHom P₁ = Q') :
    {P : W₁.Point // φ.toAddMonoidHom P = Q} ≃
      {P : W₁.Point // φ.toAddMonoidHom P = Q'} :=
  (fiberEquivKernel φ hP₀).trans (fiberEquivKernel φ hP₁).symm

/-- **T-III-4-015 step 1** (kernel-as-fiber-over-zero): the kernel of an
    isogeny is in canonical bijection with the fiber over the identity point.
    Direct specialization of `fiberEquivKernel` to `Q = 0` (image of `P₀ = 0`).

    This is the foundational set-theoretic identification: `φ.kernel ≃ φ⁻¹(0)`.
    Combined with `fiber_card_eq_kernel_card` (which generalizes to any `Q` in
    image), this gives the standard isogeny-fiber result that connects the
    kernel cardinality to the fiber structure. -/
noncomputable def kernel_equiv_fiber_zero (φ : Isogeny W₁ W₂) :
    φ.kernel ≃ {P : W₁.Point // φ.toAddMonoidHom P = 0} :=
  (fiberEquivKernel φ (by simp : φ.toAddMonoidHom 0 = 0)).symm

/-- **Corollary** (kernel-cardinality = fiber-zero-cardinality): when the kernel
    is finite, the cardinality of the fiber over zero equals the cardinality of
    the kernel. Direct from `kernel_equiv_fiber_zero`. -/
theorem kernel_card_eq_fiber_zero_card (φ : Isogeny W₁ W₂)
    [Finite φ.kernel] :
    Nat.card φ.kernel = Nat.card {P : W₁.Point // φ.toAddMonoidHom P = 0} :=
  Nat.card_eq_of_bijective _ (kernel_equiv_fiber_zero φ).bijective

/-- **Cardinality invariance**: `Nat.card {P // φ P = Q} = Nat.card ker φ`
    for any `Q` in the image of `φ`. -/
theorem fiber_card_eq_kernel_card (φ : Isogeny W₁ W₂)
    {P₀ : W₁.Point} {Q : W₂.Point} (hP₀ : φ.toAddMonoidHom P₀ = Q) :
    Nat.card {P : W₁.Point // φ.toAddMonoidHom P = Q} = Nat.card φ.kernel :=
  Nat.card_congr (fiberEquivKernel φ hP₀)

/-- The kernel of the identity isogeny is trivial. -/
@[simp] theorem kernel_id : (Isogeny.id W₁).kernel = ⊥ := by
  ext P
  simp [mem_kernel_iff, id_toAddMonoidHom]

/-- `φ.IsSeparable` holds when the function-field extension
`K(E₁) / φ*K(E₂)` is a separable algebraic extension.

In characteristic zero this is automatic; in characteristic `p` it is
equivalent to `p ∤ deg_i φ` (the inseparable part of the degree).

Reference: Silverman III.4.5 (separable/inseparable decomposition). -/
def IsSeparable (φ : Isogeny W₁ W₂) : Prop :=
  @Algebra.IsSeparable W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra

/-- The **separable degree** of an isogeny, `deg_s φ = #{F-algebra embeddings
    of K(E₂) into alg. closure of K(E₁)}`. By Silverman III.4, this equals the
    cardinality of a generic fiber: `#φ⁻¹(Q) = deg_s φ` for generic `Q ∈ E₂`
    (T-III-4-012). -/
noncomputable def sepDegree (φ : Isogeny W₁ W₂) : ℕ :=
  @Field.finSepDegree W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra

/-- The separable degree divides the total degree. -/
theorem sepDegree_dvd_degree (φ : Isogeny W₁ W₂) :
    φ.sepDegree ∣ φ.degree :=
  @Field.finSepDegree_dvd_finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra

/-- An isogeny is separable iff `sepDegree = degree` (the "no inseparable
    part" condition). -/
theorem isSeparable_iff_sepDegree_eq_degree (φ : Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toAlgebra.toModule) :
    φ.IsSeparable ↔ φ.sepDegree = φ.degree :=
  @Field.finSepDegree_eq_finrank_iff W₂.FunctionField W₁.FunctionField _ _
    φ.toAlgebra hfin |>.symm

/-- **T-III-4-012 witness form**: If at least ONE fiber has cardinality =
    `sepDegree`, then EVERY nonempty fiber has cardinality = `sepDegree`.

    The "at least one fiber" hypothesis is the content of T-II-2-009 (generic
    fiber size = sepDegree), applied to our curve-map. Our fiber-as-coset
    structure gives the "every fiber" conclusion for free. -/
theorem fiber_card_eq_sepDegree_of_witness (φ : Isogeny W₁ W₂)
    [Finite φ.kernel]
    (h_witness : ∃ P₀ : W₁.Point,
      Nat.card {P : W₁.Point // φ.toAddMonoidHom P = φ.toAddMonoidHom P₀} =
        φ.sepDegree) :
    ∀ {P₀ Q} (_ : φ.toAddMonoidHom P₀ = Q),
      Nat.card {P : W₁.Point // φ.toAddMonoidHom P = Q} = φ.sepDegree := by
  obtain ⟨P₀_wit, h_wit⟩ := h_witness
  intro P₀ Q hP₀
  rw [fiber_card_eq_kernel_card φ hP₀]
  rw [← fiber_card_eq_kernel_card φ rfl (P₀ := P₀_wit)]
  exact h_wit

/-- **Hasse-bound shortcut**: if `|ker φ| = φ.sepDegree` (a finite-field
    fact that can be proved directly without going through the generic
    II.2.6(b) fiber-size theorem), then the fiber over `φ(0)` (i.e. the
    kernel) provides the fiber witness used by the historical witness-parametric
    Hasse-bound route.

    Reduces T-II-2-009's "existential fiber-size = sepDegree" witness to the
    simpler `|ker| = sepDegree` fact, which is directly accessible for
    separable isogenies over finite fields via the V.1 chain. -/
theorem fiber_witness_of_ker_card_eq_sepDegree (φ : Isogeny W₁ W₂)
    [Finite φ.kernel]
    (h_ker_sep : Nat.card φ.kernel = φ.sepDegree) :
    ∃ P₀ : W₁.Point,
      Nat.card {P : W₁.Point //
          φ.toAddMonoidHom P = φ.toAddMonoidHom P₀} = φ.sepDegree := by
  refine ⟨0, ?_⟩
  rw [fiber_card_eq_kernel_card φ (P₀ := 0) (Q := φ.toAddMonoidHom 0) rfl,
    h_ker_sep]

/-- **T-III-4-015 step 2 closer** (witness-parametric): given a witness that
the fiber over zero has cardinality `φ.sepDegree`, the kernel cardinality
equals `φ.sepDegree`. Direct from `kernel_card_eq_fiber_zero_card`.

The witness `h_fiber_card_zero` is the SUBSTANTIVE content of Silverman
III.4.10/12 specialized to fiber over zero: for separable isogenies, every
fiber has cardinality = sepDegree. -/
theorem kernel_card_eq_sepDegree_of_fiber_zero_witness (φ : Isogeny W₁ W₂)
    [h_ker : Finite φ.kernel]
    (h_fiber_card_zero :
      Nat.card {P : W₁.Point // φ.toAddMonoidHom P = 0} = φ.sepDegree) :
    Nat.card φ.kernel = φ.sepDegree := by
  rw [kernel_card_eq_fiber_zero_card φ, h_fiber_card_zero]

/-- **T-III-4-015 witness form for separable isogenies**: If `φ` is
    separable and has a finite kernel, and at least one fiber has
    cardinality = `sepDegree`, then `#ker φ = deg φ`. -/
theorem card_kernel_eq_degree_of_separable_witness (φ : Isogeny W₁ W₂)
    [h_ker : Finite φ.kernel] (hsep : φ.IsSeparable)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toAlgebra.toModule)
    (h_witness : ∃ P₀ : W₁.Point,
      Nat.card {P : W₁.Point // φ.toAddMonoidHom P = φ.toAddMonoidHom P₀} =
        φ.sepDegree) :
    Nat.card φ.kernel = φ.degree := by
  have h_ker_eq : Nat.card φ.kernel = φ.sepDegree := by
    have := fiber_card_eq_sepDegree_of_witness φ h_witness
      (P₀ := 0) (Q := φ.toAddMonoidHom 0) rfl
    rw [← this]
    exact (fiber_card_eq_kernel_card φ (P₀ := 0) (Q := φ.toAddMonoidHom 0) rfl).symm
  rw [h_ker_eq]
  exact (isSeparable_iff_sepDegree_eq_degree φ hfin).mp hsep

/-- **T-III-4-015 corollary**: `deg φ = deg_s φ · [K(E₁) : K(E₂)]_i`
    (degree = separable × inseparable, tautologically via finrank_split).

    For separable φ, inseparable factor = 1, so `deg = sepDegree = #ker`
    (assuming the fiber witness for T-III-4-012). -/
theorem degree_eq_sepDegree_mul_inSepDegree_of_separable (φ : Isogeny W₁ W₂)
    (hsep : φ.IsSeparable)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toAlgebra.toModule) :
    φ.degree = φ.sepDegree :=
  ((isSeparable_iff_sepDegree_eq_degree φ hfin).mp hsep).symm

/-- **Embeddings interpretation of `sepDegree`** (definitional unfold of
`Field.finSepDegree`): the separable degree of `φ` is the number of
`φ*K(E₂)`-algebra embeddings of `K(E₁)` into `AlgebraicClosure K(E₁)`.

This is the count `#Hom_M(L, Ω)` of the R2 (embeddings-classification) route,
with `M = φ*K(E₂)`, `L = K(E₁)`, `Ω = AlgebraicClosure K(E₁)`. -/
theorem sepDegree_eq_card_emb (φ : Isogeny W₁ W₂) :
    letI := φ.toAlgebra
    φ.sepDegree =
      Nat.card (W₁.FunctionField →ₐ[W₂.FunctionField]
        AlgebraicClosure W₁.FunctionField) :=
  rfl

/-- **R2 reduction brick** (Silverman III.4.10c, embeddings half): for a
separable, finite-dimensional isogeny `φ`, if the **embedding count equals the
kernel count** — `φ.sepDegree = #ker φ`, i.e.
`#(K(E₁) →ₐ[φ*K(E₂)] Ω) = #ker φ` — then `#ker φ = deg φ`.

This is the clean compositional consumer for the embeddings-classification
route: `#ker φ = sepDegree φ` (hypothesis) `= deg φ` (separability, via
`isSeparable_iff_sepDegree_eq_degree`). The substantive content is delegated
to the hypothesis `h_count`, which is exactly the embedding↔kernel bijection
`Emb ≃ ker φ`. -/
theorem card_kernel_eq_degree_of_sepDegree_eq_card_kernel (φ : Isogeny W₁ W₂)
    (hsep : φ.IsSeparable)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toAlgebra.toModule)
    (h_count : φ.sepDegree = Nat.card φ.kernel) :
    Nat.card φ.kernel = φ.degree := by
  rw [← h_count]
  exact (isSeparable_iff_sepDegree_eq_degree φ hfin).mp hsep

/-- **Combinatorial helper**: if `e : α → ℤ` is uniformly `c` on a finset `S`,
then `∑ P ∈ S, e P = (#S) * c`. -/
theorem _root_.Finset.sum_eq_card_mul_of_constant
    {α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ}
    (heq : ∀ P ∈ S, e P = c) :
    ∑ P ∈ S, e P = (S.card : ℤ) * c := by
  rw [Finset.sum_congr rfl heq, Finset.sum_const]
  simp

/-- **Witness-parametric Silverman III.4.10(a) second half** (T-III-4-013):
given a finite fiber `S` with uniform ramification index `c` summing to
`deg φ`, and `#S = deg_s φ`, we recover the product identity
`deg_s φ · c = deg φ`, i.e., `c = deg_i φ = deg φ / deg_s φ`.

The hypotheses encode Silverman's three inputs:
* `h_uniform` — all fiber ramification indices coincide (equals a value `c`).
  Proof: translation symmetry on elliptic curves (Silverman III.4.10(a)
  setup).
* `h_sum` — Silverman II.2.6(a): `Σ e_φ(P) = deg φ` (witness).
* `h_card` — Silverman III.4.10(a) first half (T-III-4-012): `#fiber = deg_s φ`
  (witness).

The conclusion `(deg_s φ) * c = deg φ` is combinatorial; combined with
divisibility `deg_s ∣ deg` (which is structural, from the separable-
inseparable degree split), this gives `c = deg_i φ`. -/
theorem ramificationIndex_mul_sepDegree_eq_degree_of_witnesses
    (φ : Isogeny W₁ W₂)
    {α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ}
    (h_uniform : ∀ P ∈ S, e P = c)
    (h_sum : ∑ P ∈ S, e P = (φ.degree : ℤ))
    (h_card : S.card = φ.sepDegree) :
    (φ.sepDegree : ℤ) * c = (φ.degree : ℤ) := by
  rw [← h_card]
  exact (Finset.sum_eq_card_mul_of_constant h_uniform).symm.trans h_sum

/-- **Witness-parametric T-III-4-013** in ratio form: under the same hypotheses,
if `φ.sepDegree ≠ 0`, the common ramification index `c` equals
`deg φ / deg_s φ = deg_i φ`. Stated over `ℚ` for clean division. -/
theorem ramificationIndex_eq_insepDegree_of_witnesses
    (φ : Isogeny W₁ W₂) (hs : φ.sepDegree ≠ 0)
    {α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ}
    (h_uniform : ∀ P ∈ S, e P = c)
    (h_sum : ∑ P ∈ S, e P = (φ.degree : ℤ))
    (h_card : S.card = φ.sepDegree) :
    (c : ℚ) = (φ.degree : ℚ) / (φ.sepDegree : ℚ) := by
  have hprod : (φ.sepDegree : ℤ) * c = (φ.degree : ℤ) :=
    ramificationIndex_mul_sepDegree_eq_degree_of_witnesses φ h_uniform h_sum h_card
  have hsQ : (φ.sepDegree : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hs
  have hprod' : (φ.sepDegree : ℚ) * c = (φ.degree : ℚ) := by exact_mod_cast hprod
  field_simp
  linarith

/-- **Separable corollary of T-III-4-013**: for a separable isogeny with all
the witness inputs, every ramification index in the fiber equals `1`.

Witness inputs:
* `hsep` — `φ.IsSeparable` (Algebra-separable, from T-III-4-003/5-004).
* `hfin` — finite-dimensional extension (from algebra-finiteness of isogenies).
* `h_uniform`, `h_sum`, `h_card` — the three combinatorial witnesses of
  T-III-4-013.

The separability gives `deg φ = deg_s φ` (via
`degree_eq_sepDegree_mul_inSepDegree_of_separable`), so `deg_i φ = 1`,
so `c = 1` — i.e., the isogeny is unramified across the fiber. -/
theorem ramificationIndex_eq_one_of_separable_witnesses
    (φ : Isogeny W₁ W₂)
    (hsep : φ.IsSeparable)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toAlgebra.toModule)
    (hs : φ.sepDegree ≠ 0)
    {α : Type*} {S : Finset α} {e : α → ℤ} {c : ℤ}
    (h_uniform : ∀ P ∈ S, e P = c)
    (h_sum : ∑ P ∈ S, e P = (φ.degree : ℤ))
    (h_card : S.card = φ.sepDegree) :
    c = 1 := by
  have hprod : (φ.sepDegree : ℤ) * c = (φ.degree : ℤ) :=
    ramificationIndex_mul_sepDegree_eq_degree_of_witnesses φ h_uniform h_sum h_card
  have hdeg_eq : φ.degree = φ.sepDegree :=
    degree_eq_sepDegree_mul_inSepDegree_of_separable φ hsep hfin
  rw [hdeg_eq] at hprod
  have hsZ : (φ.sepDegree : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hs
  exact mul_left_cancel₀ hsZ (by rw [mul_one]; exact hprod)

/-- **T-III-4-015 step 3** (Galois card witness via IsGalois): given a
`FiniteDimensional` and `IsGalois` instance for the function-field tower
induced by `φ.toAlgebra`, derive `Nat.card Aut = φ.degree`.

Witness-parametric on the IsGalois instance. The IsGalois hypothesis is
the substantive III.4.10(a) content; with it, this consumer fires the
`Nat.card Aut = φ.degree` witness needed by S6, axiom-clean via Mathlib's
`IsGalois.card_aut_eq_finrank`. -/
theorem card_aut_eq_degree_of_isGalois (φ : Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toAlgebra.toModule)
    (hgal : @IsGalois W₂.FunctionField _ W₁.FunctionField _ φ.toAlgebra) :
    Nat.card (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      φ.toAlgebra φ.toAlgebra) = φ.degree := by
  letI := φ.toAlgebra
  haveI := hfin
  haveI := hgal
  exact IsGalois.card_aut_eq_finrank W₂.FunctionField W₁.FunctionField

/-- **T-III-4-015 step 4** (IsGalois from Separable + Normal): given the
two atomic conditions `IsSeparable` and `Normal` for the function-field
tower induced by `φ.toAlgebra`, derive `IsGalois`. Direct from Mathlib's
`isGalois_iff`.

Reduces the IsGalois instance to TWO atomic Mathlib-API gaps:
1. `Algebra.IsSeparable` — for separable isogenies (Witness #1's content).
2. `Normal` — the substantive III.4.10(a) Galois closure property. -/
theorem isGalois_of_separable_and_normal (φ : Isogeny W₁ W₂)
    (h_sep : letI := φ.toAlgebra
      Algebra.IsSeparable W₂.FunctionField W₁.FunctionField)
    (h_normal : letI := φ.toAlgebra
      Normal W₂.FunctionField W₁.FunctionField) :
    @IsGalois W₂.FunctionField _ W₁.FunctionField _ φ.toAlgebra := by
  letI := φ.toAlgebra
  exact isGalois_iff.mpr ⟨h_sep, h_normal⟩

/-- **T-III-4-015 step 4b** (IsGalois from Isogeny.IsSeparable + Normal):
since `φ.IsSeparable` is definitionally `Algebra.IsSeparable W₂.FunctionField
W₁.FunctionField` via `φ.toAlgebra`, we can take `φ.IsSeparable` directly
as the separability hypothesis. Cleaner consumer for Witness #1.

Reduces the IsGalois requirement to ONE substantive Mathlib gap beyond
Witness #1: `Normal β.toAlgebra` for the function-field tower. -/
theorem isGalois_of_isSeparable_and_normal (φ : Isogeny W₁ W₂)
    (h_sep : φ.IsSeparable)
    (h_normal : letI := φ.toAlgebra
      Normal W₂.FunctionField W₁.FunctionField) :
    @IsGalois W₂.FunctionField _ W₁.FunctionField _ φ.toAlgebra :=
  isGalois_of_separable_and_normal φ h_sep h_normal

end Isogeny

end HasseWeil
