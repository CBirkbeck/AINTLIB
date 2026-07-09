import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.GroupTheory.CosetCover

/-!
# Selecting a basis from a generating submodule over a semi-local ring

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-A4]`; Stacks
`algebra-lemma-semi-local-module-basis-in-submodule`, tag 03C1): let `R` be a local ring
with **infinite** residue field, `S` an `R`-algebra with finitely many maximal ideals, all
containing `m·S`, and `M` a finite free `S`-module. If an `R`-submodule `N ⊆ M` generates
`M` over `S`, then `N` contains an `S`-basis of `M`.

This is the basis-selection step of the semi-local heart of the finite-flat quotient
theorem (Stacks 03BM, our `[HG-B6]`): there it produces `x₁, …, x_r ∈ B` such that
`B ⊗[R] A = ⊕ᵢ ρ(B)·(xᵢ ⊗ 1)`, the input to the `[HG-B5]` descent bootstrap.

The proof follows 03C1 with two simplifications enabled by mathlib gadgets:
* the "product of fields" reduction is replaced by per-maximal fibre spaces
  `S⧸n ⊗[S] M` plus a finite-family Nakayama step
  (`Submodule.eq_bot_of_forall_le_smul_of_prod_le_jacobson`), so no CRT is needed;
* the general-position choice is `Subspace.exists_eq_top_of_iUnion_eq_univ`
  (a vector space over an infinite field is not a finite union of proper subspaces),
  applied over the residue field `κ = R⧸m` to the quotient `N⧸mN`;
* linear independence of the selected spanning family is automatic from the Orzech
  property of commutative rings (`basisOfSpanRangeEqTop`).
-/

open Submodule

section BasisOfSpan

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-- Over a commutative ring, `r` elements spanning a finite free module of rank `r` are
automatically a basis: the induced surjection `S^r → M ≅ S^r` is injective by the Orzech
property. This is the lift-to-a-basis half of Stacks 03C1. -/
noncomputable def basisOfSpanRangeEqTop [Nontrivial S] [Module.Free S M] [Module.Finite S M]
    {r : ℕ} (hr : Module.finrank S M = r) {y : Fin r → M}
    (hspan : Submodule.span S (Set.range y) = ⊤) : Module.Basis (Fin r) S M := by
  classical
  let φ : (Fin r → S) →ₗ[S] M := Fintype.linearCombination S y
  have hφsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  have hφinj : Function.Injective φ := by
    let b : Module.Basis (Fin r) S M := (Module.finBasis S M).reindex (finCongr hr)
    have hψ : Function.Surjective (b.equivFun.toLinearMap ∘ₗ φ) :=
      b.equivFun.surjective.comp hφsurj
    have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hψ
    intro a a' haa'
    exact hinj (by simp [LinearMap.comp_apply, haa'])
  exact (Pi.basisFun S (Fin r)).map (LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩)

@[simp]
theorem basisOfSpanRangeEqTop_apply [Nontrivial S] [Module.Free S M] [Module.Finite S M]
    {r : ℕ} (hr : Module.finrank S M = r) {y : Fin r → M}
    (hspan : Submodule.span S (Set.range y) = ⊤) (i : Fin r) :
    basisOfSpanRangeEqTop hr hspan i = y i := by
  classical
  simp [basisOfSpanRangeEqTop, Module.Basis.map_apply, LinearEquiv.ofBijective_apply,
    Fintype.linearCombination_apply, Pi.single_apply]

end BasisOfSpan

section Nakayama

variable {S M' : Type*} [CommRing S] [AddCommGroup M'] [Module S M']

/-- **Finite-family Nakayama**: if a finitely generated submodule `Q` satisfies
`Q ≤ nⱼ • Q` for each ideal in a finite family whose product lies in the Jacobson radical,
then `Q = ⊥`. Applied with the family of all maximal ideals of a semi-local ring, this
replaces Stacks 03C1's reduction to the product of residue fields. -/
theorem Submodule.eq_bot_of_forall_le_smul_of_prod_le_jacobson (Q : Submodule S M')
    (hfg : Q.FG) {s : ℕ} (n : Fin s → Ideal S) (hsmul : ∀ j, Q ≤ n j • Q)
    (hjac : (∏ j, n j) ≤ (⊥ : Ideal S).jacobson) : Q = ⊥ := by
  classical
  have hprod : ∀ t : Finset (Fin s), Q ≤ (∏ j ∈ t, n j) • Q := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      calc Q ≤ n a • Q := hsmul a
        _ ≤ n a • ((∏ j ∈ t, n j) • Q) := smul_mono_right _ ih
        _ = (∏ j ∈ insert a t, n j) • Q := by rw [Finset.prod_insert ha, smul_smul]
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (∏ j, n j) Q hfg
    (hprod Finset.univ) hjac

end Nakayama

section Avoidance

open IsLocalRing TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Every element of `κ ⊗[R] N'` for the residue field `κ` is a pure tensor `1 ⊗ z`:
residue-field scalars lift to `R` (`residue_surjective`), so they can be pushed across the
tensor. -/
theorem exists_one_tmul_eq_residueField {N' : Type*} [AddCommGroup N'] [Module R N']
    (x : ResidueField R ⊗[R] N') : ∃ z : N', (1 : ResidueField R) ⊗ₜ[R] z = x := by
  induction x with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul c z =>
    obtain ⟨r, rfl⟩ := residue_surjective (R := R) c
    exact ⟨r • z, by simp [TensorProduct.smul_tmul', Algebra.smul_def]⟩
  | add x y ihx ihy =>
    obtain ⟨zx, hzx⟩ := ihx
    obtain ⟨zy, hzy⟩ := ihy
    exact ⟨zx + zy, by rw [TensorProduct.tmul_add, hzx, hzy]⟩

/-- If the maximal ideal kills `T`, then `1 ⊗ t ≠ 0` in `κ ⊗[R] T` for `t ≠ 0`: under
`quotTensorEquivQuotSMul` the element `1 ⊗ t` is the class of `t` mod `m•T = ⊥`. -/
theorem one_tmul_ne_zero_of_smul_top_eq_bot {T : Type*} [AddCommGroup T] [Module R T]
    (hmT : maximalIdeal R • (⊤ : Submodule R T) = ⊥) {t : T} (ht : t ≠ 0) :
    (1 : ResidueField R) ⊗ₜ[R] t ≠ (0 : ResidueField R ⊗[R] T) := by
  intro h0
  have h1 : quotTensorEquivQuotSMul T (maximalIdeal R)
      ((Ideal.Quotient.mk (maximalIdeal R) 1) ⊗ₜ[R] t) = 0 := by
    rw [show (Ideal.Quotient.mk (maximalIdeal R) 1) = (1 : R ⧸ maximalIdeal R) from map_one _]
    exact h0 ▸ map_zero _
  rw [quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero, hmT] at h1
  exact ht h1

/-- **The simultaneous-escape step of Stacks 03C1**: over a local ring with infinite
residue field, given finitely many linear maps out of `N'` whose residue base changes are
all nonzero, some single element `1 ⊗ z` escapes every kernel — a vector space over an
infinite field is not a finite union of proper subspaces
(`Subspace.exists_eq_top_of_iUnion_eq_univ`), and every element of `κ ⊗ N'` is of the form
`1 ⊗ z` (`exists_one_tmul_eq_residueField`). -/
theorem exists_one_tmul_baseChange_ne_zero [Infinite (ResidueField R)]
    {N' : Type*} [AddCommGroup N'] [Module R N'] {s : ℕ}
    {T : Fin s → Type*} [∀ j, AddCommGroup (T j)] [∀ j, Module R (T j)]
    (h : ∀ j, N' →ₗ[R] T j)
    (hne : ∀ j, LinearMap.baseChange (ResidueField R) (h j) ≠ 0) :
    ∃ z : N', ∀ j,
      LinearMap.baseChange (ResidueField R) (h j) (1 ⊗ₜ[R] z) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hcover : ⋃ j, ((LinearMap.ker ((h j).baseChange (ResidueField R)) :
      Submodule (ResidueField R) (ResidueField R ⊗[R] N')) :
      Set (ResidueField R ⊗[R] N')) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨z, hz⟩ := exists_one_tmul_eq_residueField x
    obtain ⟨j, hj⟩ := hcon z
    exact Set.mem_iUnion.mpr ⟨j, by
      rw [SetLike.mem_coe, LinearMap.mem_ker, ← hz]
      exact hj⟩
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcover
  exact hne j (LinearMap.ker_eq_top.mp hj)

end Avoidance
