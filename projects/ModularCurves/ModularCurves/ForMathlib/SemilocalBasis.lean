import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Free
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
